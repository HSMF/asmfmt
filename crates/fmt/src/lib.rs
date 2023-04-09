#![doc = include_str!("../README.md")]

use asm_lexer::TopLevel;

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
