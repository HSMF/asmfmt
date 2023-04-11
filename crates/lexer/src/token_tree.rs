use std::{collections::VecDeque, fmt::Display};

use crate::{RawToken, Token, TokenKind};

#[derive(Debug)]
pub enum RTopLevel<T> {
    Line {
        label: Option<T>,
        instruction: Option<T>,
        operands: Option<Vec<RTokenTree<T>>>,
        comment: Option<T>,
    },
    Directive {
        directive: T,
        args: Vec<T>,
        brackets: Option<(T, T)>,
        comment: Option<T>,
    },
    Illegal {
        tokens: Vec<T>,
        remainder: T,
    },
}

impl<T> RTopLevel<T> {
    pub fn is_line(&self) -> bool {
        matches!(self, Self::Line { .. })
    }
    pub fn is_directive(&self) -> bool {
        matches!(self, Self::Directive { .. })
    }
    pub fn is_illegal(&self) -> bool {
        matches!(self, Self::Illegal { .. })
    }
}

#[derive(Debug)]
pub enum RTokenTree<T> {
    Expression {
        operator: T,
        parenthesis: Option<(T, T)>,
        args: Vec<RTokenTree<T>>,
    },
    Single {
        id: T,
    },
    Annotated {
        note: T,
        actual: Box<RTokenTree<T>>,
    },
    EffectiveAddress {
        brackets: (T, T),
        size: Option<T>,
        arg: Box<RTokenTree<T>>,
        index: Option<Box<RTokenTree<T>>>,
    },
}

impl<T> RTokenTree<T> {
    /// applies the function F to every leaf of the token tree. Returns a newly constructed
    /// TokenTree.
    pub fn map_leaves<F, S>(self, mut f: F) -> RTokenTree<S>
    where
        F: FnMut(T) -> S,
    {
        /// A Partially initialized version of a RTokenTree<T>
        enum Kind<T> {
            Expression {
                parenthesis: Option<(T, T)>,
                operator: T,
                args: Vec<usize>,
            },
            Single {
                id: T,
            },
            Annotated {
                note: T,
                actual: usize,
            },
            EffectiveAddress {
                brackets: (T, T),
                size: Option<T>,
                arg: usize,
                index: Option<usize>,
            },
        }

        /// Wrapper Enum that signifies the initialization status of an element in `visited`
        // deriving Default to be able to use std::mem::take
        #[derive(Default)]
        enum InitStatus<T, S> {
            #[default]
            Uninit,
            Partial(Kind<T>),
            Full(RTokenTree<S>),
        }

        impl<T, S> InitStatus<T, S> {
            fn assert_partial(self) -> Kind<T> {
                match self {
                    Partial(k) => k,
                    _ => panic!("assertion failed. Field is not partially initialized"),
                }
            }

            fn assert_full(self) -> RTokenTree<S> {
                match self {
                    Full(k) => k,
                    _ => panic!("assertion failed. Field is not fully initialized"),
                }
            }
        }
        use InitStatus::*;

        // (index, subtree)
        let mut stack = vec![(0, self)];

        // could be done with MaybeUninit but I want to avoid unsafe for now
        let mut visited = vec![Uninit];

        fn make_new_visited<T, S>(
            visited: &mut Vec<InitStatus<T, S>>,
            stack: &mut Vec<(usize, RTokenTree<T>)>,
            arg: RTokenTree<T>,
        ) -> usize {
            let idx = visited.len();
            visited.push(Uninit); // add new uninit item
            stack.push((idx, arg));
            idx
        }

        // simple dfs
        while let Some((idx, top)) = stack.pop() {
            // no need to check for cycles since rusts ownership model does this for us

            let populated = match top {
                RTokenTree::Expression {
                    operator,
                    parenthesis,
                    args,
                } => {
                    let args = args
                        .into_iter()
                        .map(|arg| make_new_visited(&mut visited, &mut stack, arg))
                        .collect();
                    Kind::Expression {
                        parenthesis,
                        operator,
                        args,
                    }
                }
                RTokenTree::Single { id } => Kind::Single { id },
                RTokenTree::Annotated { note, actual } => {
                    let actual = make_new_visited(&mut visited, &mut stack, *actual);
                    Kind::Annotated { actual, note }
                }
                RTokenTree::EffectiveAddress {
                    brackets,
                    size,
                    arg,
                    index,
                } => {
                    let arg = make_new_visited(&mut visited, &mut stack, *arg);
                    let index =
                        index.map(|index| make_new_visited(&mut visited, &mut stack, *index));
                    Kind::EffectiveAddress {
                        brackets,
                        size,
                        arg,
                        index,
                    }
                }
            };

            visited[idx] = Partial(populated);
        }

        // since `visited` is topologically sorted, there should not be any conflicts when
        // traversing the reversed iterator. Furthermore, since DFS visits every node in the
        // connected graph (which a tree is), there are no uninitialized (`None`) nodes

        for i in (0..visited.len()).rev() {
            let v = &mut visited[i];
            let v = std::mem::take(v);
            let v = v.assert_partial();
            let full = match v {
                Kind::Expression {
                    parenthesis,
                    operator,
                    args,
                } => RTokenTree::Expression {
                    operator: f(operator),
                    parenthesis: parenthesis.map(|(l, r)| (f(l), f(r))),
                    args: args
                        .into_iter()
                        .map(|x| std::mem::take(&mut visited[x]).assert_full())
                        .collect(),
                },
                Kind::Single { id } => RTokenTree::Single { id: f(id) },
                Kind::Annotated { note, actual } => RTokenTree::Annotated {
                    note: f(note),
                    actual: Box::new(std::mem::take(&mut visited[actual]).assert_full()),
                },
                Kind::EffectiveAddress {
                    brackets: (l, r),
                    size,
                    arg,
                    index,
                } => RTokenTree::EffectiveAddress {
                    brackets: (f(l), f(r)),
                    size: size.map(&mut f),
                    arg: Box::new(std::mem::take(&mut visited[arg]).assert_full()),
                    index: index
                        .map(|idx| Box::new(std::mem::take(&mut visited[idx]).assert_full())),
                },
            };

            visited[i] = Full(full);
        }

        std::mem::take(&mut visited[0]).assert_full()
    }
}

pub(crate) fn single(id: RawToken) -> RTokenTree<RawToken> {
    RTokenTree::Single { id }
}

pub(crate) type RawTopLevel<'a> = RTopLevel<RawToken<'a>>;
pub(crate) type RawTokenTree<'a> = RTokenTree<RawToken<'a>>;
pub type TopLevel<'a> = RTopLevel<Token<'a>>;
pub type TokenTree<'a> = RTokenTree<Token<'a>>;

impl<'a> TopLevel<'a> {
    pub fn line(&self) -> u32 {
        match self {
            RTopLevel::Line {
                label,
                instruction,
                operands,
                comment,
            } => {
                if let Some(label) = label {
                    return label.line;
                }
                if let Some(instr) = instruction {
                    return instr.line;
                }
                if let Some(comment) = comment {
                    return comment.line;
                }
                if let Some(first) = operands.as_ref().and_then(|x| x.get(0)) {
                    return first.line();
                }

                unreachable!("there is an empty TopLevel::Line. This cannot happen");
            }
            RTopLevel::Directive { directive, .. } => directive.line,
            RTopLevel::Illegal { remainder, .. } => remainder.line,
        }
    }

    pub fn comment<'b>(&'b self) -> &'b Option<Token<'a>> {
        match self {
            RTopLevel::Line { comment, .. } | RTopLevel::Directive { comment, .. } => comment,
            RTopLevel::Illegal { .. } => &None,
        }
    }

    /// computes the number of characters spanned by the item
    pub fn width(&self) -> usize {
        match self {
            RTopLevel::Line {
                label,
                instruction,
                operands,
                comment,
            } => {
                if let Some(comment) = comment {
                    return comment.col + comment.text.len();
                }
                if let Some(operands) = operands.as_ref().and_then(|x| x.iter().last()) {
                    return operands.col() + operands.width();
                }
                if let Some(instr) = instruction {
                    return instr.col + instr.text.len();
                }
                if let Some(label) = label {
                    return label.col + label.text.len();
                }
                0
            }
            RTopLevel::Directive {
                directive,
                args,
                brackets,
                comment,
            } => {
                if let Some(comment) = comment {
                    return comment.col + comment.text.len();
                }

                if let Some((_, r)) = brackets {
                    return r.col + r.text.len();
                }

                if let Some(last) = args.iter().last() {
                    return last.col + last.text.len();
                }
                directive.col + directive.text.len()
            }
            // todo how to handle illegal tokens
            //RTopLevel::Illegal { remainder, .. } => remainder.col + remainder.text.len(),
            RTopLevel::Illegal { .. } => 0,
        }
    }

    pub fn width_no_comment(&self) -> usize {
        match self {
            RTopLevel::Line {
                label,
                instruction,
                operands,
                ..
            } => {
                if let Some(operands) = operands.as_ref().and_then(|x| x.iter().last()) {
                    return operands.col() + operands.width();
                }
                if let Some(instr) = instruction {
                    return instr.col + instr.text.len();
                }
                if let Some(label) = label {
                    return label.col + label.text.len();
                }
                0
            }
            RTopLevel::Directive {
                directive,
                args,
                brackets,
                ..
            } => {
                if let Some((_, r)) = brackets {
                    return r.col + r.text.len();
                }

                if let Some(last) = args.iter().last() {
                    return last.col + last.text.len();
                }
                directive.col + directive.text.len()
            }
            // todo how to handle illegal tokens
            //RTopLevel::Illegal { remainder, .. } => remainder.col + remainder.text.len(),
            RTopLevel::Illegal { .. } => 0,
        }
    }

    pub(crate) fn from_raw(raw: RawTopLevel, input: &'a str) -> TopLevel<'a> {
        let map = move |x: RawToken| Token::from_raw(x, input);
        match raw {
            RTopLevel::Line {
                label,
                instruction,
                operands,
                comment,
            } => RTopLevel::Line {
                label: label.map(map),
                instruction: instruction.map(map),
                operands: operands.map(|ops| {
                    ops.into_iter()
                        .map(|x| TokenTree::from_raw(x, input))
                        .collect()
                }),
                comment: comment.map(map),
            },
            RTopLevel::Directive {
                directive,
                args,
                comment,
                brackets,
            } => TopLevel::Directive {
                directive: map(directive),
                args: args.into_iter().map(map).collect(),
                comment: comment.map(map),
                brackets: brackets.map(|(a, b)| (map(a), map(b))),
            },
            RTopLevel::Illegal { tokens, remainder } => Self::Illegal {
                tokens: tokens.into_iter().map(map).collect(),
                remainder: map(remainder),
            },
        }
    }

    /// maps a top level item to some type `T`, according to the arguments
    pub fn map<L, D, I, T>(self, map_line: L, map_directive: D, map_illegal: I) -> T
    where
        L: FnOnce(
            Option<Token<'a>>,
            Option<Token<'a>>,
            Option<Vec<TokenTree<'a>>>,
            Option<Token<'a>>,
        ) -> T,
        D: FnOnce(
            Token<'a>,
            Vec<Token<'a>>,
            Option<(Token<'a>, Token<'a>)>,
            Option<Token<'a>>,
        ) -> T,
        I: FnOnce(Vec<Token<'a>>, Token<'a>) -> T,
    {
        match self {
            RTopLevel::Line {
                label,
                instruction,
                operands,
                comment,
            } => map_line(label, instruction, operands, comment),
            RTopLevel::Directive {
                directive,
                args,
                brackets,
                comment,
            } => map_directive(directive, args, brackets, comment),
            RTopLevel::Illegal { tokens, remainder } => map_illegal(tokens, remainder),
        }
    }
}

enum StackVal<'a> {
    TT(TokenTree<'a>),
    Op(Token<'a>),
    CloseParen(Token<'a>),
}

pub struct TokenTreeIter<'a> {
    stack: Vec<StackVal<'a>>,
}

pub enum TopLevelIter<'a> {
    Line {
        label: Option<Token<'a>>,
        instruction: Option<Token<'a>>,
        operands: VecDeque<TokenTreeIter<'a>>,
        comment: Option<Token<'a>>,
    },
    Directive {
        directive: Option<Token<'a>>,
        args: VecDeque<Token<'a>>,
        comment: Option<Token<'a>>,
        brackets: (Option<Token<'a>>, Option<Token<'a>>),
    },
    Illegal {
        tokens: VecDeque<Token<'a>>,
        remainder: Option<Token<'a>>,
    },
}

impl<'a> IntoIterator for TokenTree<'a> {
    type Item = Token<'a>;
    type IntoIter = TokenTreeIter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        TokenTreeIter {
            stack: vec![StackVal::TT(self)],
        }
    }
}

impl<'a> Iterator for TokenTreeIter<'a> {
    type Item = Token<'a>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let top = self.stack.pop()?;
        use StackVal::*;

        match top {
            CloseParen(p) => Some(p),
            Op(o) => Some(o),
            TT(RTokenTree::Expression {
                operator,
                args,
                parenthesis,
            }) => match args.len() {
                1 => {
                    let (open, close) = parenthesis.unzip();
                    if let Some(close) = close {
                        self.stack.push(CloseParen(close));
                    }
                    let first = args.into_iter().next().unwrap();
                    self.stack.push(TT(first));
                    if let Some(open) = open {
                        self.stack.push(Op(operator));
                        Some(open)
                    } else {
                        Some(operator)
                    }
                }
                2 => {
                    let (open, close) = parenthesis.unzip();
                    if let Some(close) = close {
                        self.stack.push(CloseParen(close));
                    }

                    let (first, second) = {
                        let mut iter = args.into_iter();
                        let first = iter.next().unwrap();
                        let second = iter.next().unwrap();
                        (first, second)
                    };

                    self.stack.push(TT(second));
                    self.stack.push(Op(operator));
                    self.stack.push(TT(first));
                    if let Some(open) = open {
                        Some(open)
                    } else {
                        self.next()
                    }
                }
                3 => todo!(),
                k => unreachable!("can't have {k}-ary operations."),
            },
            TT(RTokenTree::Single { id }) => Some(id),
            TT(RTokenTree::EffectiveAddress {
                brackets,
                size,
                arg,
                index,
            }) => {
                self.stack.push(CloseParen(brackets.1));
                if let Some(index) = index.map(|x| *x) {
                    self.stack.push(TT(index));
                }
                self.stack.push(TT(*arg));

                if let Some(size) = size {
                    self.stack.push(CloseParen(brackets.0));
                    Some(size)
                } else {
                    Some(brackets.0)
                }
            }
            TT(RTokenTree::Annotated { note, actual }) => {
                self.stack.push(TT(*actual));
                Some(note)
            }
        }
    }
}

impl<'a> TokenTree<'a> {
    pub fn col(&self) -> usize {
        match self {
            RTokenTree::Expression {
                operator,
                parenthesis,
                args,
            } => {
                if let Some((l, _)) = parenthesis {
                    return l.col;
                }
                if args.len() <= 1 {
                    return operator.col;
                }
                args[0].col()
            }
            RTokenTree::Single { id } => id.col,
            RTokenTree::Annotated { note, .. } => note.col,
            RTokenTree::EffectiveAddress { brackets, size, .. } => {
                if let Some(size) = size {
                    size.col
                } else {
                    brackets.0.col
                }
            }
        }
    }

    pub fn width(&self) -> usize {
        let col = self.col();
        match self {
            RTokenTree::Expression {
                parenthesis, args, ..
            } => {
                if let Some((_, r)) = parenthesis {
                    return r.col + r.text.len() - col;
                }

                let last = &args[args.len() - 1];
                last.col() + last.width() - col
            }
            RTokenTree::Single { id } => id.col + id.text.len() - col,
            RTokenTree::Annotated { actual, .. } => actual.col() + actual.width() - col,
            RTokenTree::EffectiveAddress { brackets, .. } => {
                brackets.1.col + brackets.1.text.len() - col
            }
        }
    }

    pub fn line(&self) -> u32 {
        match self {
            RTokenTree::Expression {
                operator,
                parenthesis,
                args,
            } => {
                if let Some((l, _)) = parenthesis {
                    return l.line;
                }
                if args.len() <= 1 {
                    return operator.line;
                }
                args[0].line()
            }
            RTokenTree::Single { id } => id.line,
            RTokenTree::Annotated { note, .. } => note.line,
            RTokenTree::EffectiveAddress { brackets, .. } => brackets.0.line,
        }
    }

    /// shifts the token tree by the given amount. A positive amount is to the right and a negative
    /// amount is to the left. panics if there is no space on the left to shift
    pub fn shift_by(&mut self, by: isize) {
        let shift = |x: &mut usize| *x = x.checked_add_signed(by).unwrap();
        match self {
            RTokenTree::Expression {
                operator,
                parenthesis,
                args,
            } => {
                shift(&mut operator.col);
                if let Some((l, r)) = parenthesis {
                    shift(&mut l.col);
                    shift(&mut r.col);
                }
                for arg in args {
                    arg.shift_by(by)
                }
            }
            RTokenTree::Single { id } => shift(&mut id.col),
            RTokenTree::Annotated { note, actual } => {
                shift(&mut note.col);
                actual.shift_by(by);
            }
            RTokenTree::EffectiveAddress {
                brackets,
                size,
                arg,
                index,
            } => {
                shift(&mut brackets.0.col);
                shift(&mut brackets.1.col);
                if let Some(size) = size {
                    shift(&mut size.col);
                }
                arg.shift_by(by);
                if let Some(idx) = index {
                    idx.shift_by(by)
                }
            }
        }
    }

    pub(crate) fn from_raw(raw: RawTokenTree, input: &'a str) -> TokenTree<'a> {
        let map = move |x: RawToken| Token::from_raw(x, input);
        raw.map_leaves(map)
    }
}

impl<'a> IntoIterator for TopLevel<'a> {
    type Item = Token<'a>;

    type IntoIter = TopLevelIter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        match self {
            RTopLevel::Line {
                label,
                instruction,
                operands,
                comment,
            } => TopLevelIter::Line {
                label,
                instruction,
                operands: operands
                    .map(|ops| ops.into_iter().map(IntoIterator::into_iter).collect())
                    .unwrap_or_else(VecDeque::new),
                comment,
            },
            RTopLevel::Directive {
                directive,
                args,
                comment,
                brackets,
            } => TopLevelIter::Directive {
                directive: Some(directive),
                args: args.into(),
                comment,
                brackets: brackets.unzip(),
            },
            RTopLevel::Illegal { tokens, remainder } => TopLevelIter::Illegal {
                tokens: tokens.into(),
                remainder: Some(remainder),
            },
        }
    }
}

impl<'a> Iterator for TopLevelIter<'a> {
    type Item = Token<'a>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match self {
            TopLevelIter::Line {
                label,
                instruction,
                operands,
                comment,
            } => {
                if let Some(label) = label.take() {
                    return Some(label);
                }
                if let Some(instr) = instruction.take() {
                    return Some(instr);
                }
                while let Some(front) = operands.front_mut() {
                    if let Some(first) = front.next() {
                        return Some(first);
                    }
                    // iterator was exhausted, remove and try again with next
                    operands.pop_front();
                }
                comment.take()
            }
            TopLevelIter::Directive {
                directive,
                args,
                comment,
                brackets,
            } => {
                if let Some(open) = brackets.0.take() {
                    return Some(open);
                }
                if let Some(dir) = directive.take() {
                    return Some(dir);
                }

                if let Some(arg) = args.pop_front() {
                    return Some(arg);
                }

                if let Some(close) = brackets.1.take() {
                    return Some(close);
                }

                comment.take()
            }
            TopLevelIter::Illegal { tokens, remainder } => {
                if let Some(first) = tokens.pop_front() {
                    return Some(first);
                }
                remainder.take()
            }
        }
    }
}

fn align_to(target: usize, col: &mut usize, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    write!(f, "{}", " ".repeat(target - *col))?;
    *col = target;
    Ok(())
}
fn write_token(
    token: &Token<'_>,
    col: &mut usize,
    f: &mut std::fmt::Formatter<'_>,
) -> std::fmt::Result {
    match token.kind {
        TokenKind::String => {
            align_to(token.col - 1, col, f)?;
            write!(f, "\"{}\"", token.text)?;
            *col = token.col + token.text.len() + 1;
        }
        TokenKind::Number(crate::Base::Hexadecimal) => {
            align_to(token.col - 2, col, f)?;
            write!(f, "0x{}", token.text)?;
            *col = token.col + token.text.len();
        }
        _ => {
            align_to(token.col, col, f)?;
            write!(f, "{}", token.text)?;
            *col = token.col + token.text.len();
        }
    }

    Ok(())
}

impl Display for TopLevel<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RTopLevel::Line {
                label,
                instruction,
                operands,
                comment,
            } => {
                let mut col = 1;
                if let Some(label) = label {
                    write_token(label, &mut col, f)?;
                    write!(f, ":")?;
                    col += 1;
                }
                if let Some(instruction) = instruction {
                    write_token(instruction, &mut col, f)?;
                }
                if let Some(operands) = operands {
                    let mut first = true;
                    for op in operands {
                        if !first {
                            write!(f, ",")?;
                            col += 1;
                        }
                        first = false;
                        TokenTreeWriter::new(op, &mut col).write(f)?;
                    }
                }
                if let Some(comment) = comment {
                    align_to(comment.col - 1, &mut col, f)?;
                    write!(f, ";")?;
                    col += 1;
                    write_token(comment, &mut col, f)?;
                }
                Ok(())
            }

            RTopLevel::Directive {
                directive,
                args,
                brackets,
                comment,
            } => {
                let mut col = 1;
                let (l, r) = if let Some((l, r)) = brackets {
                    (Some(l), Some(r))
                } else {
                    (None, None)
                };
                if let Some(l) = l {
                    write_token(l, &mut col, f)?;
                }

                write_token(directive, &mut col, f)?;

                let mut first = true;
                for arg in args {
                    if !first {
                        write!(f, ",")?;
                        col += 1;
                    }
                    first = false;
                    write_token(arg, &mut col, f)?;
                }

                if let Some(r) = r {
                    write_token(r, &mut col, f)?;
                }

                if let Some(comment) = comment {
                    align_to(comment.col - 1, &mut col, f)?;
                    write!(f, ";")?;
                    col += 1;
                    write_token(comment, &mut col, f)?;
                }

                Ok(())
            }
            RTopLevel::Illegal { tokens, remainder } => {
                let mut col = 1;
                for tok in tokens {
                    write_token(tok, &mut col, f)?;
                }
                write_token(remainder, &mut col, f)?;
                Ok(())
            }
        }
    }
}

struct TokenTreeWriter<'a> {
    tt: &'a TokenTree<'a>,
    col: &'a mut usize,
}

impl<'a> TokenTreeWriter<'a> {
    fn new(tt: &'a TokenTree<'a>, col: &'a mut usize) -> Self {
        Self { tt, col }
    }

    fn write(&mut self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.tt {
            RTokenTree::Expression {
                operator,
                parenthesis,
                args,
            } => {
                let (left, right) = if let Some((l, r)) = parenthesis {
                    (Some(l), Some(r))
                } else {
                    (None, None)
                };

                if args.len() <= 1 {
                    write_token(operator, self.col, f)?;
                    TokenTreeWriter::new(&args[0], self.col).write(f)?;
                } else {
                    debug_assert_eq!(args.len(), 2);
                    TokenTreeWriter::new(&args[0], self.col).write(f)?;
                    write_token(operator, self.col, f)?;
                    TokenTreeWriter::new(&args[1], self.col).write(f)?;
                }

                if let Some(l) = left {
                    write_token(l, self.col, f)?;
                }
                if let Some(r) = right {
                    write_token(r, self.col, f)?;
                }
            }
            RTokenTree::Single { id } => {
                write_token(id, self.col, f)?;
            }
            RTokenTree::Annotated { note, actual } => {
                write_token(note, self.col, f)?;
                TokenTreeWriter::new(actual, self.col).write(f)?;
            }
            RTokenTree::EffectiveAddress {
                brackets,
                size,
                arg,
                index,
            } => {
                // align_to(self.tt.col(), self.col, f)?;
                if let Some(size) = size {
                    write_token(size, self.col, f)?;
                }
                let (left, right) = brackets;
                write_token(left, self.col, f)?;
                TokenTreeWriter::new(arg, self.col).write(f)?;
                if let Some(index) = index {
                    write!(f, ",")?;
                    TokenTreeWriter::new(index, self.col).write(f)?;
                }
                write_token(right, self.col, f)?;
            }
        }

        Ok(())
    }
}

/// turns an iterator of [TopLevel] items into a string.
///
/// ```
/// # use asm_lexer::{Lexer, to_string};
/// let source = r#"
/// global main
/// main: mov eax, 15
///       add eax, 200
///       mov ecx, eax
/// "#;
/// // without any modifications to the token tree this just outputs the original
/// // program
/// assert_eq!(to_string(Lexer::new(source)), source);
/// ```
pub fn to_string<'a, I, T>(lines: I) -> String
where
    I: Iterator<Item = T>,
    T: std::borrow::Borrow<TopLevel<'a>>,
{
    let mut out = "".to_owned();
    let mut lnum = 1;
    for line in lines {
        let line = line.borrow();
        let got_lnum = line.line();
        while lnum < got_lnum {
            out.push('\n');
            lnum += 1;
        }
        out += &line.to_string();
        out.push('\n');
        lnum += 1;
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Lexer;
    use pretty_assertions::assert_eq;

    macro_rules! check_id {
        ($name:ident) => {
            #[test]
            fn $name() {
                let source = include_str!(concat!("../testdata/", stringify!($name), ".asm"));
                let parsed = Lexer::new(source).collect::<Vec<_>>();
                let reconstructed = to_string(parsed.iter());
                assert_eq!(source, &reconstructed);
            }
        };
        ($name:ident, $path:literal) => {
            #[test]
            fn $name() {
                let source = include_str!($path);
                let parsed = Lexer::new(source).collect();
                let reconstructed = reconstruct(parsed);
                assert_eq!(source, &reconstructed);
            }
        };
    }

    check_id!(hm);
    check_id!(printf1);
    check_id!(directives);
}
