use core::fmt;
use std::collections::VecDeque;

use crate::{RawToken, Token};

pub(crate) enum RTopLevel<T> {
    Line {
        label: Option<T>,
        instruction: Option<T>,
        operands: Option<Vec<RTokenTree<T>>>,
        comment: Option<T>,
    },
    Directive {
        directive: T,
        args: Vec<T>,
        comment: Option<T>,
    },
}

pub(crate) enum RTokenTree<T> {
    Expression {
        operator: T,
        args: Vec<RTokenTree<T>>,
    },
    Register {
        id: T,
    },
}

pub(crate) type RawTopLevel<'a> = RTopLevel<RawToken<'a>>;
pub(crate) type RawTokenTree<'a> = RTokenTree<RawToken<'a>>;
pub(crate) type TopLevel<'a> = RTopLevel<Token<'a>>;
pub(crate) type TokenTree<'a> = RTokenTree<Token<'a>>;

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
            } => TopLevel::Directive {
                directive: map(directive),
                args: args.into_iter().map(map).collect(),
                comment: comment.map(map),
            },
        }
    }
}

pub(crate) struct TokenTreeIter<'a> {
    stack: Vec<TokenTree<'a>>,
}

pub(crate) enum TopLevelIter<'a> {
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
    },
}

impl<'a> IntoIterator for TokenTree<'a> {
    type Item = Token<'a>;
    type IntoIter = TokenTreeIter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        TokenTreeIter { stack: vec![self] }
    }
}

impl<'a> Iterator for TokenTreeIter<'a> {
    type Item = Token<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        let top = self.stack.pop()?;

        match top {
            RTokenTree::Expression { operator, args } => {
                self.stack.extend(args.into_iter().rev());
                Some(operator)
            }
            RTokenTree::Register { id } => Some(id),
        }
    }
}

impl<'a> TokenTree<'a> {
    pub(crate) fn from_raw(raw: RawTokenTree, input: &'a str) -> TokenTree<'a> {
        let map = move |x: RawToken| Token::from_raw(x, input);
        match raw {
            RTokenTree::Expression { operator, args } => TokenTree::Expression {
                operator: map(operator),
                args: args
                    .into_iter()
                    .map(|x| TokenTree::from_raw(x, input))
                    .collect(),
            },
            RTokenTree::Register { id } => Self::Register { id: map(id) },
        }
    }
}

impl fmt::Debug for TokenTree<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Expression { operator, args } => f
                .debug_struct("Expression")
                .field("operator", operator)
                .field("args", args)
                .finish(),
            Self::Register { id } => f.debug_struct("Register").field("id", id).finish(),
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
            } => TopLevelIter::Directive {
                directive: Some(directive),
                args: args.into(),
                comment,
            },
        }
    }
}

impl<'a> Iterator for TopLevelIter<'a> {
    type Item = Token<'a>;

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
            } => {
                if let Some(dir) = directive.take() {
                    return Some(dir);
                }

                if let Some(arg) = args.pop_front() {
                    return Some(arg);
                }

                comment.take()
            }
        }
    }
}
