#![doc = include_str!("../README.md")]

use std::borrow::Cow;

use asm_lexer::{Token, TokenKind, TopLevel};

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

#[cfg_attr(feature = "serde", derive(serde::Deserialize, serde::Serialize))]
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

fn diff_signed(a: usize, b: usize) -> isize {
    if a >= b {
        (a - b) as isize
    } else {
        -((b - a) as isize)
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

fn shift_tok(pos: &mut usize, tok: &mut Token) {
    tok.col = *pos;
    *pos += tok.text.len();
}

/// aligns pseudo instructions (such as DB,DW,..., and RESB,RESW,..., and EQU)
pub fn align_pseudo(lines: &mut [TopLevel], opts: AlignOperandsOpt) {
    let align_to = lines
        .iter()
        .filter_map(|tl| match tl {
            TopLevel::Line {
                label: Some(label),
                instruction:
                    Some(Token {
                        kind:
                            TokenKind::DeclareMemoryInit
                            | TokenKind::DeclareMemoryUninit
                            | TokenKind::Equ,
                        ..
                    }),
                ..
            } => Some(label),
            _ => None,
        })
        .map(|label| label.text.len())
        .max()
        .unwrap_or(0)
        + 1 // columns are 1-based
        + 1 // colon after label
        + opts.min_spaces_after_label as usize;

    for (label, tok) in lines.iter_mut().filter_map(|tl| match tl {
        TopLevel::Line {
            label,
            instruction:
                Some(
                    tok @ Token {
                        kind:
                            TokenKind::DeclareMemoryInit
                            | TokenKind::DeclareMemoryUninit
                            | TokenKind::Equ,
                        ..
                    },
                ),
            ..
        } => Some((label, tok)),
        _ => None,
    }) {
        if let Some(label) = label {
            label.col = 1;
        }

        tok.col = align_to;
    }

    let align_to_ops = lines
        .iter()
        .filter_map(|tl| match tl {
            TopLevel::Line {
                label: Some(_),
                instruction:
                    Some(Token {
                        kind:
                            TokenKind::DeclareMemoryInit
                            | TokenKind::DeclareMemoryUninit
                            | TokenKind::Equ,
                        col,
                        text,
                ..
                    }),
                ..
            } => Some(col + text.len()),
            _ => None,
        })
        .max()
        .unwrap_or(0)
        + 1 // columns are 1-based
        + opts.min_spaces_after_instr as usize;

    for (operands, comment) in
        lines.iter_mut().filter_map(|tl| match tl {
            TopLevel::Line {
                instruction:
                    Some(Token {
                        kind:
                            TokenKind::DeclareMemoryInit
                            | TokenKind::DeclareMemoryUninit
                            | TokenKind::Equ,
                        ..
                    }),
                operands,
                comment,
                ..
            } => Some((operands, comment)),
            _ => None,
        })
    {
        let mut pos = align_to_ops;
        if let Some(ops) = operands {
            if !ops.is_empty() {
                let shift_by = diff_signed(pos, ops[0].col());
                for i in operands.iter_mut().flatten() {
                    i.shift_by(shift_by);
                    pos = i.col() + i.width();
                }
            }
        }

        if let Some(comment) = comment {
            pos += 2;
            if comment.col < pos {
                shift_tok(&mut pos, comment);
            }
        }
    }
}

/// Converts the case of keywords to a consistent case (by default all lowercase)
///
/// use [FixCase::set_uppercase_tokens] to set which tokens to change to uppercase instead
///
/// Positions where the case is changed are
/// - instructions
/// - registers
/// - directive keywords
pub struct FixCase<I> {
    iter: I,
    uppercase_tokens: Vec<TokenKind>,
}

impl<I> FixCase<I> {
    /// Creates a new iterator that by default changes everything to lowercase
    pub fn new<'a>(iter: I) -> Self
    where
        I: Iterator<Item = TopLevel<'a>>,
    {
        Self {
            iter,
            uppercase_tokens: vec![],
        }
    }

    /// sets the tokens that are converted to uppercase instead of lowercase
    pub fn set_uppercase_tokens(mut self, uppercase_tokens: Vec<TokenKind>) -> Self {
        self.uppercase_tokens = uppercase_tokens;
        self
    }
}

impl<'a, I> Iterator for FixCase<I>
where
    I: Iterator<Item = TopLevel<'a>>,
{
    type Item = TopLevel<'a>;
    fn next(&mut self) -> Option<Self::Item> {
        let fixup = |tok: Token<'a>| -> Token<'a> {
            if self.uppercase_tokens.contains(&tok.kind) {
                Token {
                    text: Cow::Owned(tok.text.to_uppercase()),
                    ..tok
                }
            } else {
                Token {
                    text: Cow::Owned(tok.text.to_lowercase()),
                    ..tok
                }
            }
        };
        let ofixup = |tok: Option<_>| tok.map(fixup);
        let out: Self::Item = self.iter.next()?.map(
            |label, instruction, operands, comment| {
                let operands = operands.map(|operands| {
                    operands
                        .into_iter()
                        .map(|x| {
                            x.map_leaves(|tok| {
                                if let TokenKind::Register = tok.kind {
                                    fixup(tok)
                                } else {
                                    tok
                                }
                            })
                        })
                        .collect::<Vec<_>>()
                });

                TopLevel::Line {
                    // changing the case of a label is potentially not safe
                    label,
                    instruction: ofixup(instruction),
                    operands,
                    comment,
                }
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

/// Indents directives by `indent_by` spaces (by default 4).
/// Furthermore improves the spacing between directive and operands of that directive
///
/// Moves comments out of the way if needed, but do not use this to prettify comments
///
/// use [IndentDirectives::set_indent] to set the indentation amount
pub struct IndentDirectives<I> {
    iter: I,
    indent_by: usize,
}

impl<'a, I> IndentDirectives<I>
where
    I: Iterator<Item = TopLevel<'a>>,
{
    pub fn new(iter: I) -> Self {
        Self { iter, indent_by: 4 }
    }

    pub fn set_indent(mut self, indent_by: usize) -> Self {
        self.indent_by = indent_by;
        self
    }
}

impl<'a, I> Iterator for IndentDirectives<I>
where
    I: Iterator<Item = TopLevel<'a>>,
{
    type Item = TopLevel<'a>;
    fn next(&mut self) -> Option<Self::Item> {
        Some(match self.iter.next()? {
            TopLevel::Directive {
                mut directive,
                mut args,
                brackets,
                mut comment,
            } => {
                let (mut l, mut r) = brackets.unzip();
                let mut pos = self.indent_by;
                if let Some(l) = &mut l {
                    shift_tok(&mut pos, l);
                }
                shift_tok(&mut pos, &mut directive);
                let mut first = true;
                for arg in args.iter_mut() {
                    if first {
                        pos += 1; // space
                        first = false;
                    } else {
                        pos += 2; // comma and space
                    }
                    shift_tok(&mut pos, arg);
                }
                if let Some(r) = &mut r {
                    shift_tok(&mut pos, r);
                }

                if let Some(comment) = &mut comment {
                    pos += 2;
                    if comment.col < pos {
                        shift_tok(&mut pos, comment);
                    }
                }

                TopLevel::Directive {
                    directive,
                    args,
                    brackets: l.zip(r),
                    comment,
                }
            }
            x => x,
        })
    }
}

/// Moves labels to the beginning of the line.
pub struct DedentLabels<I> {
    iter: I,
}

impl<'a, I> DedentLabels<I>
where
    I: Iterator<Item = TopLevel<'a>>,
{
    pub fn new(iter: I) -> Self {
        Self { iter }
    }
}

impl<'a, I> Iterator for DedentLabels<I>
where
    I: Iterator<Item = TopLevel<'a>>,
{
    type Item = TopLevel<'a>;
    fn next(&mut self) -> Option<Self::Item> {
        let next = self.iter.next()?;

        Some(match next {
            TopLevel::Line {
                label: Some(mut label),
                instruction,
                operands,
                comment,
            } => {
                label.col = 1;
                TopLevel::Line {
                    label: Some(label),
                    instruction,
                    operands,
                    comment,
                }
            }
            x => x,
        })
    }
}

#[cfg(test)]
mod tests {
    use asm_lexer::{Document, Lexer};

    use super::*;

    fn apply_global_fmt(s: &str, f: impl Fn(&mut [TopLevel])) -> String {
        let lexer = Lexer::new(s);
        let mut lines = lexer.collect::<Vec<_>>();
        f(&mut lines);
        Document::new(&lines).to_string()
    }

    fn apply_local_fmt<'a, F, B>(s: &'a str, f: F) -> String
    where
        B: Iterator<Item = TopLevel<'a>>,
        F: FnOnce(Lexer<'a>) -> B,
    {
        let lexer = Lexer::new(s);
        let lines = f(lexer).collect::<Vec<_>>();
        Document::new(&lines).to_string()
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
    snap_global!(align_pseudo_pseudo, "../testdata/pseudo.asm", |l| {
        align_pseudo(l, Default::default())
    });
    snap_local!(fix_case_printf1, "../testdata/printf1.asm", FixCase::new);
    snap_local!(fix_case_printf2, "../testdata/printf2.asm", FixCase::new);
    snap_local!(
        indent_dir_directives,
        "../testdata/directives.asm",
        IndentDirectives::new
    );
    snap_local!(
        dedent_labels_labels,
        "../testdata/labels.asm",
        DedentLabels::new
    );
}
