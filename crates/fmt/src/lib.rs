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

fn has_label(t: &TopLevel) -> bool {
    matches!(t, TopLevel::Line { label: Some(_), .. })
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

/// Aligns the operands in `lines` under each label
/// calculates the best position to put the operand given
/// by the length of the instructions. After a new label, resets.
pub fn align_operands(_lines: &mut [TopLevel]) {
    let mut index = 0;
    todo!()
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

    macro_rules! snap {
        ($name:ident, $rule:expr) => {
            snap!(
                $name,
                concat!("../testdata/", stringify!($name), ".asm"),
                $rule
            );
        };
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

    snap!(basic, |l| align_comments(l, false));
    snap!(printf1, |l| align_comments(l, false));
}
