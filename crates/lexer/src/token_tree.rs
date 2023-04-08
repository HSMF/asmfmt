use std::collections::VecDeque;

use crate::{RawToken, Token};

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

pub(crate) fn single(id: RawToken) -> RTokenTree<RawToken> {
    RTokenTree::Single { id }
}

pub(crate) type RawTopLevel<'a> = RTopLevel<RawToken<'a>>;
pub(crate) type RawTokenTree<'a> = RTokenTree<RawToken<'a>>;
pub type TopLevel<'a> = RTopLevel<Token<'a>>;
pub type TokenTree<'a> = RTokenTree<Token<'a>>;

impl<'a> TopLevel<'a> {
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
                dbg!(&note, &actual,);
                self.stack.push(TT(*actual));
                Some(note)
            }
        }
    }
}

impl<'a> TokenTree<'a> {
    pub(crate) fn from_raw(raw: RawTokenTree, input: &'a str) -> TokenTree<'a> {
        let map = move |x: RawToken| Token::from_raw(x, input);
        match raw {
            RTokenTree::Expression {
                operator,
                args,
                parenthesis,
            } => TokenTree::Expression {
                operator: map(operator),
                args: args
                    .into_iter()
                    .map(|x| TokenTree::from_raw(x, input))
                    .collect(),
                parenthesis: parenthesis.map(|(l, r)| (map(l), map(r))),
            },
            RTokenTree::Single { id } => Self::Single { id: map(id) },
            RTokenTree::EffectiveAddress {
                brackets,
                arg,
                index,
                size,
            } => Self::EffectiveAddress {
                brackets: (map(brackets.0), map(brackets.1)),
                arg: Box::new(TokenTree::from_raw(*arg, input)),
                index: index.map(|x| Box::new(TokenTree::from_raw(*x, input))),
                size: size.map(map),
            },
            RTokenTree::Annotated { note, actual } => Self::Annotated {
                note: map(note),
                actual: Box::new(TokenTree::from_raw(*actual, input)),
            },
        }
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
