#![doc = include_str!("../README.md")]

use std::borrow::Cow;

use asm_lexer::{Token, TopLevel};

fn comment_pos(lines: &[TopLevel]) -> usize {
    let mut max = 0;
    for line in lines {
        let line_width = line.width_no_comment() + 2; //  - line.comment().as_ref().map(|x| x.text.len()).unwrap_or(0) + 2;
        max = max.max(line_width);
        match line {
            TopLevel::Line { comment, .. } | TopLevel::Directive { comment, .. } => {
                max = max.max(comment.as_ref().map(|x| x.col - 1).unwrap_or(0))
            }
            TopLevel::Illegal { .. } => {}
        }
    }

    max
}

fn is_only_comment(t: &TopLevel) -> bool {
    match t {
        TopLevel::Line {
            label,
            instruction,
            operands,
            comment,
        } => label.is_none() && instruction.is_none() && operands.is_none() && comment.is_some(),
        _ => false,
    }
}

/// Aligns comments in `lines` by
/// a) the comment that begins the furthest to the right
/// b) the end of the longest line
///
/// if the line only contains a comment and nothing else and `shift_only_comments` is false
/// then moves the comment to the beginning of that line
pub fn align_comments(lines: &mut [TopLevel], shift_only_comments: bool) {
    let latest_comment_pos = comment_pos(lines);

    for line in lines {
        let just_comment = is_only_comment(line);
        match line {
            TopLevel::Line { comment, .. } | TopLevel::Directive { comment, .. } => {
                if let Some(comment) = comment {
                    if !shift_only_comments && just_comment {
                        comment.col = 2;
                    } else {
                        comment.col = latest_comment_pos;
                    }
                }
            }
            TopLevel::Illegal { .. } => {}
        }
    }
}

#[derive(Debug)]
pub struct AlignOperandsOpt {
    /// how far away the 'instruction column' should appear from the 'label column', in spaces
    pub min_spaces_after_label: u8,
    /// how far away the 'operands column' should appear from the 'instruction column', in spaces
    pub min_spaces_after_instr: u8,
}

impl Default for AlignOperandsOpt {
    fn default() -> Self {
        Self {
            min_spaces_after_label: 1,
            min_spaces_after_instr: 4,
        }
    }
}

/// Aligns the operands in `lines` under each label
/// calculates the best position to put the operand given
/// by the length of the instructions. After a new label, resets.
/// Local labels (labels starting with a .) do not reset the
/// shift amount
pub fn align_operands(lines: &mut [TopLevel], opts: AlignOperandsOpt) {
    let mut index = 0;

    fn has_label(t: &TopLevel) -> bool {
        match t {
            TopLevel::Line {
                label: Some(label), ..
            } => !label.text.starts_with('.'),
            _ => false,
        }
    }

    fn label_end(t: &TopLevel) -> usize {
        match t {
            TopLevel::Line {
                label: Some(label), ..
            } => label.col + label.text.len(),
            _ => 0,
        }
    }

    fn instr_end(t: &TopLevel) -> usize {
        match t {
            TopLevel::Line {
                instruction: Some(instr),
                ..
            } => instr.col + instr.text.len(),
            _ => 0,
        }
    }

    fn diff_signed(a: usize, b: usize) -> isize {
        if a >= b {
            (a - b) as isize
        } else {
            -((b - a) as isize)
        }
    }

    while index < lines.len() {
        let next_with_label = lines
            .iter()
            .enumerate()
            .skip(index)
            .find(|(_, line)| has_label(line))
            .map(|(i, _)| i)
            .unwrap_or(lines.len());
        let shifty_col = lines[index.saturating_sub(1)..next_with_label]
            .iter()
            .map(label_end)
            .max()
            .unwrap_or(0)
            + 1 // the ':' after the label
            + opts.min_spaces_after_label as usize;

        for line in &mut lines[index..next_with_label] {
            match line {
                TopLevel::Line {
                    label: _,
                    instruction: Some(instr),
                    operands,
                    comment,
                } => {
                    let shift_by = diff_signed(shifty_col, instr.col);
                    instr.col = shifty_col;
                    let mut last_col = shifty_col + instr.text.len();

                    for i in operands.iter_mut().flatten() {
                        i.shift_by(shift_by);
                    }
                    if let Some(last) = operands.iter().flatten().last() {
                        last_col = last.col() + last.width();
                    }
                    if let Some(comment) = comment {
                        if comment.col <= last_col {
                            comment.col = comment.col.wrapping_add_signed(shift_by);
                        }
                    }
                }
                TopLevel::Line {
                    label: _,
                    instruction: _,
                    operands: Some(ops),
                    comment,
                } if ops.get(0).map(|x| x.col() < shifty_col) == Some(true) => {
                    let shift_by = diff_signed(shifty_col, ops[0].col());

                    for i in ops.iter_mut() {
                        i.shift_by(shift_by)
                    }
                    let last_col = if let Some(last) = ops.iter().last() {
                        last.col() + last.width()
                    } else {
                        0
                    };
                    if let Some(comment) = comment {
                        if comment.col <= last_col {
                            comment.col = comment.col.wrapping_add_signed(shift_by);
                        }
                    }
                }
                _ => (),
            }
        }

        // do the same but for operands
        let shifty_col = lines[index.saturating_sub(1)..next_with_label]
            .iter()
            .map(instr_end)
            .max()
            .unwrap_or(0)
            + opts.min_spaces_after_instr as usize;

        for line in &mut lines[index..next_with_label] {
            match line {
                TopLevel::Line {
                    label: _,
                    instruction: _,
                    operands: Some(ops),
                    comment,
                } if !ops.is_empty() => {
                    let shift_by = diff_signed(shifty_col, ops[0].col());

                    for i in ops.iter_mut() {
                        i.shift_by(shift_by)
                    }
                    let last_col = if let Some(last) = ops.iter().last() {
                        last.col() + last.width()
                    } else {
                        0
                    };
                    if let Some(comment) = comment {
                        if comment.col <= last_col {
                            comment.col = comment.col.wrapping_add_signed(shift_by);
                        }
                    }
                }
                _ => {}
            }
        }

        index = next_with_label + 1;
    }
}

pub struct FixCase<I> {
    iter: I,
}

impl<I> FixCase<I> {
    pub fn new<'a>(iter: I) -> Self
    where
        I: Iterator<Item = TopLevel<'a>>,
    {
        Self { iter }
    }
}

impl<'a, I> Iterator for FixCase<I>
where
    I: Iterator<Item = TopLevel<'a>>,
{
    type Item = TopLevel<'a>;
    fn next(&mut self) -> Option<Self::Item> {
        fn fixup(tok: Token) -> Token {
            Token {
                text: Cow::Owned(tok.text.to_lowercase()),
                ..tok
            }
        }
        fn ofixup(tok: Option<Token>) -> Option<Token> {
            tok.map(fixup)
        }
        let out: Self::Item = self.iter.next()?.map(
            |label, instruction, operands, comment| TopLevel::Line {
                label: ofixup(label),
                instruction: ofixup(instruction),
                operands,
                comment,
            },
            |directive, args, brackets, comment| TopLevel::Directive {
                directive: fixup(directive),
                args,
                brackets,
                comment,
            },
            |tokens, remainder| TopLevel::Illegal { tokens, remainder },
        );
        Some(out)
    }
}

#[cfg(test)]
mod tests {
    use asm_lexer::{to_string, Lexer};

    use super::*;

    fn apply_global_fmt(s: &str, f: impl Fn(&mut [TopLevel])) -> String {
        let lexer = Lexer::new(s);
        let mut lines = lexer.collect::<Vec<_>>();
        f(&mut lines);
        to_string(lines.iter())
    }

    fn apply_local_fmt<'a, F, B>(s: &'a str, f: F) -> String
    where
        B: Iterator<Item = TopLevel<'a>>,
        F: FnOnce(Lexer<'a>) -> B,
    {
        let lexer = Lexer::new(s);
        let lines = f(lexer);
        to_string(lines)
    }

    macro_rules! snap_global {
        ($name:ident, $path:expr, $rule:expr) => {
            #[test]
            fn $name() {
                let contents = include_str!($path);
                let snapshot = apply_global_fmt(contents, $rule);
                let mut settings = insta::Settings::clone_current();
                settings.set_snapshot_path("../testdata/output/");
                settings.bind(|| {
                    insta::assert_snapshot!(snapshot);
                });
            }
        };
    }

    macro_rules! snap_local {
        ($name:ident, $path:expr, $cons:expr) => {
            #[test]
            fn $name() {
                let contents = include_str!($path);
                let snapshot = apply_local_fmt(contents, $cons);
                let mut settings = insta::Settings::clone_current();
                settings.set_snapshot_path("../testdata/output/");
                settings.bind(|| {
                    insta::assert_snapshot!(snapshot);
                });
            }
        };
    }

    snap_global!(align_comments_basic, "../testdata/basic.asm", |l| {
        align_comments(l, false)
    });
    snap_global!(align_comments_printf1, "../testdata/printf1.asm", |l| {
        align_comments(l, false)
    });
    snap_global!(align_labels_printf2, "../testdata/printf2.asm", |l| {
        align_operands(l, Default::default())
    });
    snap_local!(fix_case_printf1, "../testdata/printf1.asm", FixCase::new);
}
