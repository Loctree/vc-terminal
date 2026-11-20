use std::borrow::Cow;
use std::cmp::Reverse;
use std::collections::HashSet;
use std::iter;
use std::rc::Rc;

use ahash::RandomState;
use winit::keyboard::ModifiersState;

use alacritty_terminal::grid::{BidirectionalIterator, Dimensions};
use alacritty_terminal::index::{Boundary, Column, Direction, Line, Point};
use alacritty_terminal::term::cell::Hyperlink;
use alacritty_terminal::term::search::{Match, RegexIter, RegexSearch};
use alacritty_terminal::term::{Term, TermMode};

use crate::config::UiConfig;
use crate::config::ui_config::{Hint, HintAction, HintMouse};

/// Maximum number of linewraps followed outside of the viewport during search highlighting.
pub const MAX_SEARCH_LINES: usize = 100;

/// Percentage of characters in the hints alphabet used for the last character.
const HINT_SPLIT_PERCENTAGE: f32 = 0.5;

/// Keyboard regex hint state.
pub struct HintState {
    /// Hint currently in use.
    hint: Option<Rc<Hint>>,

    /// Alphabet for hint labels.
    alphabet: String,

    /// Visible matches.
    matches: Vec<Match>,

    /// Key label for each visible match.
    labels: Vec<Vec<char>>,

    /// Keys pressed for hint selection.
    keys: Vec<char>,
}

impl HintState {
    /// Initialize an inactive hint state.
    pub fn new<S: Into<String>>(alphabet: S) -> Self {
        Self {
            alphabet: alphabet.into(),
            hint: Default::default(),
            matches: Default::default(),
            labels: Default::default(),
            keys: Default::default(),
        }
    }

    /// Check if a hint selection is in progress.
    pub fn active(&self) -> bool {
        self.hint.is_some()
    }

    /// Start the hint selection process.
    pub fn start(&mut self, hint: Rc<Hint>) {
        self.hint = Some(hint);
    }

    /// Cancel the hint highlighting process.
    fn stop(&mut self) {
        self.matches.clear();
        self.labels.clear();
        self.keys.clear();
        self.hint = None;
    }

    /// Update the visible hint matches and key labels.
    pub fn update_matches<T>(&mut self, term: &Term<T>) {
        let hint = match self.hint.as_mut() {
            Some(hint) => hint,
            None => return,
        };

        // Clear current matches.
        self.matches.clear();

        // Add escape sequence hyperlinks.
        if hint.content.hyperlinks {
            self.matches.extend(visible_unique_hyperlinks_iter(term));
        }

        // Add visible regex matches.
        if let Some(regex) = hint.content.regex.as_ref() {
            regex.with_compiled(|regex| {
                let matches = visible_regex_match_iter(term, regex);

                // Apply post-processing and search for sub-matches if necessary.
                if hint.post_processing {
                    let mut matches = matches.collect::<Vec<_>>();
                    self.matches.extend(matches.drain(..).flat_map(|rm| {
                        HintPostProcessor::new(term, regex, rm).collect::<Vec<_>>()
                    }));
                } else {
                    self.matches.extend(matches);
                }
            });
        }

        // Cancel highlight with no visible matches.
        if self.matches.is_empty() {
            self.stop();
            return;
        }

        // Sort and dedup ranges. Currently overlapped but not exactly same ranges are kept.
        self.matches.sort_by_key(|bounds| (*bounds.start(), Reverse(*bounds.end())));
        self.matches.dedup_by_key(|bounds| *bounds.start());

        let mut generator = HintLabels::new(&self.alphabet, HINT_SPLIT_PERCENTAGE);
        let match_count = self.matches.len();
        let keys_len = self.keys.len();

        // Get the label for each match.
        self.labels.resize(match_count, Vec::new());
        for i in (0..match_count).rev() {
            let mut label = generator.next();
            if label.len() >= keys_len && label[..keys_len] == self.keys[..] {
                self.labels[i] = label.split_off(keys_len);
            } else {
                self.labels[i] = Vec::new();
            }
        }
    }

    /// Handle keyboard input during hint selection.
    pub fn keyboard_input<T>(&mut self, term: &Term<T>, c: char) -> Option<HintMatch> {
        match c {
            // Use backspace to remove the last character pressed.
            '\x08' | '\x1f' => {
                self.keys.pop();
            },
            // Cancel hint highlighting on ESC/Ctrl+c.
            '\x1b' | '\x03' => self.stop(),
            _ => (),
        }

        // Update the visible matches.
        self.update_matches(term);

        let hint = self.hint.as_ref()?;

        // Find the last label starting with the input character.
        let mut labels = self.labels.iter().enumerate().rev();
        let (index, label) = labels.find(|(_, label)| !label.is_empty() && label[0] == c)?;

        // Check if the selected label is fully matched.
        if label.len() == 1 {
            let bounds = self.matches[index].clone();
            let hint = hint.clone();

            // Exit hint mode unless it requires explicit dismissal.
            if hint.persist {
                self.keys.clear();
            } else {
                self.stop();
            }

            // Hyperlinks take precedence over regex matches.
            let hyperlink = term.grid()[*bounds.start()].hyperlink();
            Some(HintMatch { bounds, tail: Vec::new(), hyperlink, hint })
        } else {
            // Store character to preserve the selection.
            self.keys.push(c);

            None
        }
    }

    /// Hint key labels.
    pub fn labels(&self) -> &Vec<Vec<char>> {
        &self.labels
    }

    /// Visible hint regex matches.
    pub fn matches(&self) -> &[Match] {
        &self.matches
    }

    /// Update the alphabet used for hint labels.
    pub fn update_alphabet(&mut self, alphabet: &str) {
        if self.alphabet != alphabet {
            alphabet.clone_into(&mut self.alphabet);
            self.keys.clear();
        }
    }
}

/// Hint match which was selected by the user.
#[derive(PartialEq, Eq, Debug, Clone)]
pub struct HintMatch {
    /// Terminal range matching the hint.
    bounds: Match,

    /// Words continuing the match on the following rows, see [`WrappedMatch`].
    tail: Vec<Match>,

    /// OSC 8 hyperlink.
    hyperlink: Option<Hyperlink>,

    /// Hint which triggered this match.
    hint: Rc<Hint>,
}

impl HintMatch {
    #[inline]
    pub fn should_highlight(&self, point: Point, pointed_hyperlink: Option<&Hyperlink>) -> bool {
        self.hyperlink.as_ref() == pointed_hyperlink
            && (self.hyperlink.is_some()
                || self.bounds.contains(&point)
                || self.tail.iter().any(|word| word.contains(&point)))
    }

    #[inline]
    pub fn action(&self) -> &HintAction {
        &self.hint.action
    }

    #[inline]
    pub fn bounds(&self) -> &Match {
        &self.bounds
    }

    /// Terminal range from the start of the hint to the end of its last row.
    pub fn extent(&self) -> Match {
        *self.bounds.start()..=*self.tail.last().unwrap_or(&self.bounds).end()
    }

    pub fn hyperlink(&self) -> Option<&Hyperlink> {
        self.hyperlink.as_ref()
    }

    /// Get the text content of the hint match.
    ///
    /// This will always revalidate the hint text, to account for terminal content
    /// changes since the [`HintMatch`] was constructed. The text of the hint might
    /// be different from its original value, but it will **always** be a valid
    /// match for this hint.
    pub fn text<T>(&self, term: &Term<T>) -> Option<Cow<'_, str>> {
        // Revalidate hyperlink match.
        if let Some(hyperlink) = &self.hyperlink {
            let (validated, bounds) = hyperlink_at(term, *self.bounds.start())?;
            return (&validated == hyperlink && bounds == self.bounds)
                .then(|| hyperlink.uri().into());
        }

        // Revalidate regex match.
        let regex = self.hint.content.regex.as_ref()?;
        if self.tail.is_empty() {
            let bounds = regex.with_compiled(|regex| {
                regex_match_at(term, *self.bounds.start(), regex, self.hint.post_processing)
            })??;
            return (bounds == self.bounds)
                .then(|| term.bounds_to_string(*bounds.start(), *bounds.end()).into());
        }

        // Revalidate a match hard-wrapped onto the following rows.
        let wrapped = regex.with_compiled(|regex| {
            wrapped_regex_match_at(term, *self.bounds.start(), regex, self.hint.post_processing)
        })??;
        (wrapped.head == self.bounds && wrapped.tail == self.tail)
            .then(|| wrapped.text(term).into())
    }
}

/// Regex match that a program hard-wrapped at the edge of its text box.
///
/// Programs such as Claude Code break long lines with real newlines, and a
/// multiplexer such as vc-frame redraws its panes with cursor addressing, so
/// the grid never marks these rows as wrapped and the regex stops at the edge.
/// A match that fills its row up to the edge of its box continues with the
/// first word of the next row in the same box.
#[derive(PartialEq, Eq, Debug, Clone)]
struct WrappedMatch {
    /// Regex match the link starts with.
    head: Match,

    /// Continuation words, one per following row.
    tail: Vec<Match>,
}

impl WrappedMatch {
    /// The link text, without the indentation of its continuation rows.
    ///
    /// A segment reaching the last grid column of an unwrapped row reads back
    /// with a newline; the link continues on the next row instead.
    fn text<T>(&self, term: &Term<T>) -> String {
        iter::once(&self.head)
            .chain(&self.tail)
            .map(|segment| {
                let text = term.bounds_to_string(*segment.start(), *segment.end());
                text.trim_end_matches('\n').to_owned()
            })
            .collect()
    }
}

/// Retrieve the regex match at `point`, joined across rows hard-wrapped at the
/// edge of its text box.
fn wrapped_regex_match_at<T>(
    term: &Term<T>,
    point: Point,
    regex: &mut RegexSearch,
    post_processing: bool,
) -> Option<WrappedMatch> {
    let text_box = text_box(term, point);
    let right = text_box.1;

    // The match under the point, or the continuation word under it.
    let mut head = regex_match_at(term, point, regex, post_processing);
    let mut segment = match &head {
        Some(head) => head.clone(),
        None => leading_word(term, point.line, text_box).filter(|word| word.contains(&point))?,
    };

    // Walk up while the segment opens its row and a match fills the row above.
    while segment.start().line > term.topmost_line()
        && leading_word(term, segment.start().line, text_box)
            .is_some_and(|word| word.start() == segment.start())
    {
        let above = Point::new(Line(segment.start().line.0 - 1), right);
        let Some(previous) = regex_match_at(term, above, regex, post_processing)
            .filter(|previous| *previous.end() == above)
        else {
            break;
        };
        head = Some(previous.clone());
        segment = previous;
    }
    let head = head?;

    // Walk down while each segment fills its row up to the edge.
    let mut tail = Vec::new();
    let mut end = *head.end();
    while end.column == right && end.line < term.bottommost_line() {
        let Some(word) = leading_word(term, Line(end.line.0 + 1), text_box) else {
            break;
        };
        end = *word.end();
        tail.push(word);
    }
    trim_wrapped_tail(term, &head, &mut tail);

    let covered = head.contains(&point) || tail.iter().any(|word| word.contains(&point));
    covered.then_some(WrappedMatch { head, tail })
}

/// Drop the sentence punctuation that follows a wrapped link.
///
/// A closing bracket stays when the link itself opened it.
fn trim_wrapped_tail<T>(term: &Term<T>, head: &Match, tail: &mut Vec<Match>) {
    let Some(last) = tail.last() else {
        return;
    };
    let line = last.end().line;
    let first = last.start().column.0;
    let text = WrappedMatch { head: head.clone(), tail: tail.clone() }.text(term);
    let mut open_parens = text.matches('(').count() as isize - text.matches(')').count() as isize;
    let mut open_brackets = text.matches('[').count() as isize - text.matches(']').count() as isize;

    let row = &term.grid()[line];
    let mut end = last.end().column.0 + 1;
    while end > first {
        match row[Column(end - 1)].c {
            '.' | ',' | ':' | ';' | '?' | '!' | '\'' => (),
            ')' if open_parens < 0 => open_parens += 1,
            ']' if open_brackets < 0 => open_brackets += 1,
            _ => break,
        }
        end -= 1;
    }

    if end == first {
        tail.pop();
    } else if let Some(last) = tail.last_mut() {
        *last = *last.start()..=Point::new(line, Column(end - 1));
    }
}

/// Columns `[left, right]` of the text box holding `point`: between the
/// nearest pane rules on its row, or the grid edges.
fn text_box<T>(term: &Term<T>, point: Point) -> (Column, Column) {
    let row = &term.grid()[point.line];
    let last = term.last_column().0;
    let left = (0..point.column.0)
        .rev()
        .find(|&column| is_pane_rule(row[Column(column)].c))
        .map_or(0, |column| column + 1);
    let right = (point.column.0 + 1..=last)
        .find(|&column| is_pane_rule(row[Column(column)].c))
        .map_or(last, |column| column - 1);
    (Column(left), Column(right))
}

/// Vertical rules a multiplexer draws between panes.
fn is_pane_rule(c: char) -> bool {
    matches!(c, '│' | '┃' | '║' | '┆' | '┇' | '┊' | '┋')
}

/// Characters of a URL or a path: letters, digits and the RFC 3986 set.
fn is_link_char(c: char) -> bool {
    c.is_alphanumeric() || "-._~:/?#[]@!$&'()*+,;=%".contains(c)
}

/// The first word inside the box on `line`; blanks before it are indentation.
fn leading_word<T>(term: &Term<T>, line: Line, (left, right): (Column, Column)) -> Option<Match> {
    let row = &term.grid()[line];
    let start = (left.0..=right.0).find(|&column| !matches!(row[Column(column)].c, ' ' | '\t'))?;
    let end = (start..=right.0).take_while(|&column| is_link_char(row[Column(column)].c)).last()?;
    Some(Point::new(line, Column(start))..=Point::new(line, Column(end)))
}

/// Generator for creating new hint labels.
struct HintLabels {
    /// Full character set available.
    alphabet: Vec<char>,

    /// Alphabet indices for the next label.
    indices: Vec<usize>,

    /// Point separating the alphabet's head and tail characters.
    ///
    /// To make identification of the tail character easy, part of the alphabet cannot be used for
    /// any other position.
    ///
    /// All characters in the alphabet before this index will be used for the last character, while
    /// the rest will be used for everything else.
    split_point: usize,
}

impl HintLabels {
    /// Create a new label generator.
    ///
    /// The `split_ratio` should be a number between 0.0 and 1.0 representing the percentage of
    /// elements in the alphabet which are reserved for the tail of the hint label.
    fn new(alphabet: impl Into<String>, split_ratio: f32) -> Self {
        let alphabet: Vec<char> = alphabet.into().chars().collect();
        let split_point = ((alphabet.len() - 1) as f32 * split_ratio.min(1.)) as usize;

        Self { indices: vec![0], split_point, alphabet }
    }

    /// Get the characters for the next label.
    fn next(&mut self) -> Vec<char> {
        let characters = self.indices.iter().rev().map(|index| self.alphabet[*index]).collect();
        self.increment();
        characters
    }

    /// Increment the character sequence.
    fn increment(&mut self) {
        // Increment the last character; if it's not at the split point we're done.
        let tail = &mut self.indices[0];
        if *tail < self.split_point {
            *tail += 1;
            return;
        }
        *tail = 0;

        // Increment all other characters in reverse order.
        let alphabet_len = self.alphabet.len();
        for index in self.indices.iter_mut().skip(1) {
            if *index + 1 == alphabet_len {
                // Reset character and move to the next if it's already at the limit.
                *index = self.split_point + 1;
            } else {
                // If the character can be incremented, we're done.
                *index += 1;
                return;
            }
        }

        // Extend the sequence with another character when nothing could be incremented.
        self.indices.push(self.split_point + 1);
    }
}

/// Iterate over all visible regex matches.
pub fn visible_regex_match_iter<'a, T>(
    term: &'a Term<T>,
    regex: &'a mut RegexSearch,
) -> impl Iterator<Item = Match> + 'a {
    let viewport_start = Line(-(term.grid().display_offset() as i32));
    let viewport_end = viewport_start + term.bottommost_line();
    let mut start = term.line_search_left(Point::new(viewport_start, Column(0)));
    let mut end = term.line_search_right(Point::new(viewport_end, Column(0)));
    start.line = start.line.max(viewport_start - MAX_SEARCH_LINES);
    end.line = end.line.min(viewport_end + MAX_SEARCH_LINES);

    RegexIter::new(start, end, Direction::Right, term, regex)
        .skip_while(move |rm| rm.end().line < viewport_start)
        .take_while(move |rm| rm.start().line <= viewport_end)
}

/// Iterate over all visible hyperlinks, yanking only unique ones.
pub fn visible_unique_hyperlinks_iter<T>(term: &Term<T>) -> impl Iterator<Item = Match> + '_ {
    let mut display_iter = term.grid().display_iter().peekable();

    // Avoid creating hints for the same hyperlinks, but from a different places.
    let mut unique_hyperlinks = HashSet::<Hyperlink, RandomState>::default();

    iter::from_fn(move || {
        // Find the start of the next unique hyperlink.
        let (cell, hyperlink) = display_iter.find_map(|cell| {
            let hyperlink = cell.hyperlink()?;
            (!unique_hyperlinks.contains(&hyperlink)).then(|| {
                unique_hyperlinks.insert(hyperlink.clone());
                (cell, hyperlink)
            })
        })?;

        let start = cell.point;
        let mut end = start;

        // Find the end bound of just found unique hyperlink.
        while let Some(next_cell) = display_iter.peek() {
            // Cell at display iter doesn't match, yield the hyperlink and start over with
            // `find_map`.
            if next_cell.hyperlink().as_ref() != Some(&hyperlink) {
                break;
            }

            // Advance to the next cell.
            end = next_cell.point;
            let _ = display_iter.next();
        }

        Some(start..=end)
    })
}

/// Retrieve the match, if the specified point is inside the content matching the regex.
fn regex_match_at<T>(
    term: &Term<T>,
    point: Point,
    regex: &mut RegexSearch,
    post_processing: bool,
) -> Option<Match> {
    let regex_match = visible_regex_match_iter(term, regex).find(|rm| rm.contains(&point))?;

    // Apply post-processing and search for sub-matches if necessary.
    if post_processing {
        HintPostProcessor::new(term, regex, regex_match).find(|rm| rm.contains(&point))
    } else {
        Some(regex_match)
    }
}

/// Check if there is a hint highlighted at the specified point.
pub fn highlighted_at<T>(
    term: &Term<T>,
    config: &UiConfig,
    point: Point,
    mouse_mods: ModifiersState,
) -> Option<HintMatch> {
    let mouse_mode = term.mode().intersects(TermMode::MOUSE_MODE);

    config.hints.enabled.iter().find_map(|hint| {
        // Check if all required modifiers are pressed.
        let highlight =
            hint.mouse.is_some_and(|mouse| mouse_hint_enabled(mouse_mode, mouse, mouse_mods));
        if !highlight {
            return None;
        }

        if let Some((hyperlink, bounds)) =
            hint.content.hyperlinks.then(|| hyperlink_at(term, point)).flatten()
        {
            return Some(HintMatch {
                bounds,
                tail: Vec::new(),
                hyperlink: Some(hyperlink),
                hint: hint.clone(),
            });
        }

        let wrapped = hint.content.regex.as_ref().and_then(|regex| {
            regex.with_compiled(|regex| {
                wrapped_regex_match_at(term, point, regex, hint.post_processing)
            })
        });
        if let Some(WrappedMatch { head, tail }) = wrapped.flatten() {
            return Some(HintMatch { bounds: head, tail, hint: hint.clone(), hyperlink: None });
        }

        None
    })
}

/// Check whether a mouse hint owns the click at the host boundary.
///
/// Shift remains the generic escape hatch while an application reports mouse
/// events. A hint explicitly bound to Command/Super is already an unambiguous
/// host gesture, so it must not be forwarded to the terminal application.
fn mouse_hint_enabled(mouse_mode: bool, mouse: HintMouse, mouse_mods: ModifiersState) -> bool {
    mouse.enabled
        && mouse_mods.contains(mouse.mods.0)
        && (!mouse_mode
            || mouse_mods.contains(ModifiersState::SHIFT)
            || mouse.mods.0.contains(ModifiersState::SUPER))
}

/// Retrieve the hyperlink with its range, if there is one at the specified point.
///
/// This will only return contiguous cells, even if another hyperlink with the same ID exists.
fn hyperlink_at<T>(term: &Term<T>, point: Point) -> Option<(Hyperlink, Match)> {
    let hyperlink = term.grid()[point].hyperlink()?;

    let grid = term.grid();

    let mut match_end = point;
    for cell in grid.iter_from(point) {
        if cell.hyperlink().is_some_and(|link| link == hyperlink) {
            match_end = cell.point;
        } else {
            break;
        }
    }

    let mut match_start = point;
    let mut iter = grid.iter_from(point);
    while let Some(cell) = iter.prev() {
        if cell.hyperlink().is_some_and(|link| link == hyperlink) {
            match_start = cell.point;
        } else {
            break;
        }
    }

    Some((hyperlink, match_start..=match_end))
}

/// Iterator over all post-processed matches inside an existing hint match.
struct HintPostProcessor<'a, T> {
    /// Regex search DFAs.
    regex: &'a mut RegexSearch,

    /// Terminal reference.
    term: &'a Term<T>,

    /// Next hint match in the iterator.
    next_match: Option<Match>,

    /// Start point for the next search.
    start: Point,

    /// End point for the hint match iterator.
    end: Point,
}

impl<'a, T> HintPostProcessor<'a, T> {
    /// Create a new iterator for an unprocessed match.
    fn new(term: &'a Term<T>, regex: &'a mut RegexSearch, regex_match: Match) -> Self {
        let mut post_processor = Self {
            next_match: None,
            start: *regex_match.start(),
            end: *regex_match.end(),
            term,
            regex,
        };

        // Post-process the first hint match.
        post_processor.next_processed_match(regex_match);

        post_processor
    }

    /// Apply some hint post processing heuristics.
    ///
    /// This will check the end of the hint and make it shorter if certain characters are determined
    /// to be unlikely to be intentionally part of the hint.
    ///
    /// This is most useful for identifying URLs appropriately.
    fn hint_post_processing(&self, regex_match: &Match) -> Option<Match> {
        let mut iter = self.term.grid().iter_from(*regex_match.start());

        let mut c = iter.cell().c;

        // Truncate uneven number of brackets.
        let end = *regex_match.end();
        let mut open_parents = 0;
        let mut open_brackets = 0;
        loop {
            match c {
                '(' => open_parents += 1,
                '[' => open_brackets += 1,
                ')' => {
                    if open_parents == 0 {
                        iter.prev();
                        break;
                    } else {
                        open_parents -= 1;
                    }
                },
                ']' => {
                    if open_brackets == 0 {
                        iter.prev();
                        break;
                    } else {
                        open_brackets -= 1;
                    }
                },
                _ => (),
            }

            if iter.point() == end {
                break;
            }

            match iter.next() {
                Some(indexed) => c = indexed.cell.c,
                None => break,
            }
        }

        // Truncate trailing characters which are likely to be delimiters.
        let start = *regex_match.start();
        while iter.point() != start {
            if !matches!(c, '.' | ',' | ':' | ';' | '?' | '!' | '(' | '[' | '\'') {
                break;
            }

            match iter.prev() {
                Some(indexed) => c = indexed.cell.c,
                None => break,
            }
        }

        if start > iter.point() { None } else { Some(start..=iter.point()) }
    }

    /// Loop over submatches until a non-empty post-processed match is found.
    fn next_processed_match(&mut self, mut regex_match: Match) {
        self.next_match = loop {
            if let Some(next_match) = self.hint_post_processing(&regex_match) {
                self.start = next_match.end().add(self.term, Boundary::Grid, 1);
                break Some(next_match);
            }

            self.start = regex_match.start().add(self.term, Boundary::Grid, 1);
            if self.start > self.end {
                return;
            }

            match self.term.regex_search_right(self.regex, self.start, self.end) {
                Some(rm) => regex_match = rm,
                None => return,
            }
        };
    }
}

impl<T> Iterator for HintPostProcessor<'_, T> {
    type Item = Match;

    fn next(&mut self) -> Option<Self::Item> {
        let next_match = self.next_match.take()?;

        if self.start <= self.end {
            if let Some(rm) = self.term.regex_search_right(self.regex, self.start, self.end) {
                self.next_processed_match(rm);
            }
        }

        Some(next_match)
    }
}

#[cfg(test)]
mod tests {
    use alacritty_terminal::index::{Column, Line};
    use alacritty_terminal::term::test::mock_term;
    use alacritty_terminal::vte::ansi::Handler;

    use super::*;

    #[test]
    fn hint_label_generation() {
        let mut generator = HintLabels::new("0123", 0.5);

        assert_eq!(generator.next(), vec!['0']);
        assert_eq!(generator.next(), vec!['1']);

        assert_eq!(generator.next(), vec!['2', '0']);
        assert_eq!(generator.next(), vec!['2', '1']);
        assert_eq!(generator.next(), vec!['3', '0']);
        assert_eq!(generator.next(), vec!['3', '1']);

        assert_eq!(generator.next(), vec!['2', '2', '0']);
        assert_eq!(generator.next(), vec!['2', '2', '1']);
        assert_eq!(generator.next(), vec!['2', '3', '0']);
        assert_eq!(generator.next(), vec!['2', '3', '1']);
        assert_eq!(generator.next(), vec!['3', '2', '0']);
        assert_eq!(generator.next(), vec!['3', '2', '1']);
        assert_eq!(generator.next(), vec!['3', '3', '0']);
        assert_eq!(generator.next(), vec!['3', '3', '1']);

        assert_eq!(generator.next(), vec!['2', '2', '2', '0']);
        assert_eq!(generator.next(), vec!['2', '2', '2', '1']);
        assert_eq!(generator.next(), vec!['2', '2', '3', '0']);
        assert_eq!(generator.next(), vec!['2', '2', '3', '1']);
        assert_eq!(generator.next(), vec!['2', '3', '2', '0']);
        assert_eq!(generator.next(), vec!['2', '3', '2', '1']);
        assert_eq!(generator.next(), vec!['2', '3', '3', '0']);
        assert_eq!(generator.next(), vec!['2', '3', '3', '1']);
        assert_eq!(generator.next(), vec!['3', '2', '2', '0']);
        assert_eq!(generator.next(), vec!['3', '2', '2', '1']);
        assert_eq!(generator.next(), vec!['3', '2', '3', '0']);
        assert_eq!(generator.next(), vec!['3', '2', '3', '1']);
        assert_eq!(generator.next(), vec!['3', '3', '2', '0']);
        assert_eq!(generator.next(), vec!['3', '3', '2', '1']);
        assert_eq!(generator.next(), vec!['3', '3', '3', '0']);
        assert_eq!(generator.next(), vec!['3', '3', '3', '1']);
    }

    #[test]
    fn closed_bracket_does_not_result_in_infinite_iterator() {
        let term = mock_term(" ) ");

        let mut search = RegexSearch::new("[^/ ]").unwrap();

        let count = HintPostProcessor::new(
            &term,
            &mut search,
            Point::new(Line(0), Column(1))..=Point::new(Line(0), Column(1)),
        )
        .take(1)
        .count();

        assert_eq!(count, 0);
    }

    #[test]
    fn command_hint_owns_click_during_mouse_reporting() {
        let mut command_hint = HintMouse { enabled: true, ..Default::default() };
        command_hint.mods.0 = ModifiersState::SUPER;
        let plain_hint = HintMouse { enabled: true, ..Default::default() };

        assert!(mouse_hint_enabled(true, command_hint, ModifiersState::SUPER));
        assert!(!mouse_hint_enabled(true, plain_hint, ModifiersState::SUPER));
        assert!(mouse_hint_enabled(true, plain_hint, ModifiersState::SHIFT));
    }

    #[test]
    fn collect_unique_hyperlinks() {
        let mut term = mock_term("000\r\n111");
        term.goto(0, 0);

        let hyperlink_foo = Hyperlink::new(Some("1"), String::from("foo"));
        let hyperlink_bar = Hyperlink::new(Some("2"), String::from("bar"));

        // Create 2 hyperlinks on the first line.
        term.set_hyperlink(Some(hyperlink_foo.clone().into()));
        term.input('b');
        term.input('a');
        term.set_hyperlink(Some(hyperlink_bar.clone().into()));
        term.input('r');
        term.set_hyperlink(Some(hyperlink_foo.clone().into()));
        term.goto(1, 0);

        // Ditto for the second line.
        term.set_hyperlink(Some(hyperlink_foo.into()));
        term.input('b');
        term.input('a');
        term.set_hyperlink(Some(hyperlink_bar.into()));
        term.input('r');
        term.set_hyperlink(None);

        let mut unique_hyperlinks = visible_unique_hyperlinks_iter(&term);
        assert_eq!(
            Some(Match::new(Point::new(Line(0), Column(0)), Point::new(Line(0), Column(1)))),
            unique_hyperlinks.next()
        );
        assert_eq!(
            Some(Match::new(Point::new(Line(0), Column(2)), Point::new(Line(0), Column(2)))),
            unique_hyperlinks.next()
        );
        assert_eq!(None, unique_hyperlinks.next());
    }

    #[test]
    fn visible_regex_match_covers_entire_viewport() {
        let content = "I'm a match!\r\n".repeat(4096);
        // The Term returned from this call will have a viewport starting at 0 and ending at 4096.
        // That's good enough for this test, since it only cares about visible content.
        let term = mock_term(&content);
        let mut regex = RegexSearch::new("match!").unwrap();

        // The iterator should match everything in the viewport.
        assert_eq!(visible_regex_match_iter(&term, &mut regex).count(), 4096);
    }

    const PATH_REGEX: &str = "(/[A-Za-z0-9._-]+)+";

    fn wrapped_text(content: &str, regex: &str, point: Point) -> Option<String> {
        let term = mock_term(content);
        let mut regex = RegexSearch::new(regex).unwrap();
        wrapped_regex_match_at(&term, point, &mut regex, true).map(|wrapped| wrapped.text(&term))
    }

    #[test]
    fn path_hard_wrapped_at_a_pane_rule_continues_on_the_next_row() {
        // A vc-frame pane between two others; the program broke the path at
        // the pane edge and indented the rest.
        let content = "s│run /tmp/claude/wrap-│r\r\ns│  ped/report.log done│r";
        let joined = Some(String::from("/tmp/claude/wrap-ped/report.log"));

        // Pointing at either row opens the whole path.
        assert_eq!(wrapped_text(content, PATH_REGEX, Point::new(Line(0), Column(8))), joined);
        assert_eq!(wrapped_text(content, PATH_REGEX, Point::new(Line(1), Column(5))), joined);

        // The neighbouring pane and the indentation are not part of the link.
        let term = mock_term(content);
        let mut regex = RegexSearch::new(PATH_REGEX).unwrap();
        let wrapped =
            wrapped_regex_match_at(&term, Point::new(Line(1), Column(5)), &mut regex, true)
                .unwrap();
        assert_eq!(wrapped.head, Point::new(Line(0), Column(6))..=Point::new(Line(0), Column(22)));
        assert_eq!(wrapped.tail, vec![
            Point::new(Line(1), Column(4))..=Point::new(Line(1), Column(17))
        ]);

        // Text after the continuation word is not a link.
        assert_eq!(wrapped_text(content, PATH_REGEX, Point::new(Line(1), Column(20))), None);
    }

    #[test]
    fn url_hard_wrapped_at_the_window_edge_continues_on_the_next_row() {
        let content = "see https://example.com/a/very-lon\r\ng/path ok";
        let url = "https://[a-z./-]+";

        let joined = Some(String::from("https://example.com/a/very-long/path"));
        assert_eq!(wrapped_text(content, url, Point::new(Line(0), Column(10))), joined);
        assert_eq!(wrapped_text(content, url, Point::new(Line(1), Column(1))), joined);
    }

    #[test]
    fn match_ending_before_the_edge_stays_on_its_row() {
        // Word wrapping moved `next/thing` down; it does not continue the path.
        let content = "s│see /tmp/a.log    │r\r\ns│next/thing        │r";

        let text = wrapped_text(content, PATH_REGEX, Point::new(Line(0), Column(8)));
        assert_eq!(text, Some(String::from("/tmp/a.log")));
    }

    #[test]
    fn interface_glyphs_on_the_next_row_do_not_continue_the_link() {
        // Tool output marker and a pane frame below a path that fills its row.
        let marker = "s│run /tmp/claude/wrap-│r\r\ns│  ⎿ done            │r";
        let frame = "s│run /tmp/claude/wrap-│r\r\ns└────────────────────┘r";

        let path = Some(String::from("/tmp/claude/wrap-"));
        assert_eq!(wrapped_text(marker, PATH_REGEX, Point::new(Line(0), Column(8))), path);
        assert_eq!(wrapped_text(frame, PATH_REGEX, Point::new(Line(0), Column(8))), path);
    }

    #[test]
    fn sentence_punctuation_after_a_wrapped_link_is_dropped() {
        let content = "s│run /tmp/claude/wrap-│r\r\ns│  ped/report.log).  │r";

        let text = wrapped_text(content, PATH_REGEX, Point::new(Line(0), Column(8)));
        assert_eq!(text, Some(String::from("/tmp/claude/wrap-ped/report.log")));
    }
}
