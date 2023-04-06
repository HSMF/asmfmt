/*!
* # A lexer for NASM-Style Assembly.
*
* ```
* #use asm_lexer::{Lexer, TokenKind};
* #let input = "mov eax, ecx";
* let lexer = Lexer::new(input);
* while let Ok(Some(token)) = lexer.next_token() {
*     if matches!(token.kind, TokenKind::Illegal(_)) {
*       // the input was illegal, handle this case accordingly.
*       // the lexer will continue producing tokens
*       // in case failure is not the end
*       return;
*     }
* }
* ```
*
* */

use std::{cell::RefCell, collections::VecDeque, fmt};

use lexer_state::LexerState;
mod lexer_state;

#[derive(Clone, PartialEq)]
pub struct Span {
    pub start_row: usize,
    pub start_col: usize,
    pub end_row: usize,
    pub end_col: usize,
}

impl Span {
    pub fn empty() -> Self {
        Self {
            start_row: 0,
            start_col: 0,
            end_row: 0,
            end_col: 0,
        }
    }
}

impl fmt::Debug for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "({},{})->({},{})",
            self.start_row, self.start_col, self.end_row, self.end_col
        )
    }
}

#[derive(Default, Clone, PartialEq)]
pub enum TokenText<'a> {
    Slice(&'a [char]),
    Owned(String),
    #[default]
    Empty,
}

impl<'a> From<TokenText<'a>> for String {
    fn from(val: TokenText<'a>) -> Self {
        match val {
            TokenText::Slice(s) => s.iter().collect(),
            TokenText::Owned(s) => s,
            TokenText::Empty => "".to_string(),
        }
    }
}

impl<'a> From<&TokenText<'a>> for String {
    fn from(val: &TokenText<'a>) -> Self {
        match val {
            TokenText::Slice(s) => s.iter().collect(),
            TokenText::Owned(s) => s.clone(),
            TokenText::Empty => "".to_string(),
        }
    }
}

impl<'a> fmt::Debug for TokenText<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TokenText::Slice(_) | TokenText::Owned(_) => {
                let s: String = self.into();

                write!(f, "{s:?}")
            }
            TokenText::Empty => write!(f, "<Empty>"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ErrorKind {
    TrailingComma,
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokenKind {
    Label,
    /// a end of line style comment, including the ;
    Comment,
    /// An instruction. Depending on the actual instruction there could be zero or more arguments
    /// but this is not checked by the lexer
    Instruction,
    /// could not handle this token.
    Illegal(ErrorKind),

    // operands
    /// a register
    Register,
    /// A literal number
    Number,

    // Operand: Effective Address
    /// Begins the Effective Address environment. Corresponds to a [
    OpenEffectiveAddress,
    /// Closes the Effective Address environment. Corresponds to a ]
    CloseEffectiveAddress,
    /// A Plus (+) operator
    Plus,
    /// A Minus (-) operator
    Minus,
    /// A Times (*) operator
    Times,
    Const,
}

#[derive(Clone, PartialEq)]
pub struct Token<'a> {
    pub kind: TokenKind,
    pub text: TokenText<'a>,
    pub span: Span,
}

impl fmt::Debug for Token<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Token")
            .field(&self.kind)
            .field(&self.text)
            .field(&self.span)
            .finish()
    }
}

fn make_span(start: usize, end: usize, lines: &[usize]) -> Span {
    assert!(
        start <= end,
        "start ({start}) must be less than end ({end})"
    );

    let start_row = lines
        .iter()
        .enumerate()
        .find_map(|(line, &ch)| (ch > start).then_some(line))
        .unwrap()
        - 1;

    let end_row = lines
        .iter()
        .enumerate()
        .skip(start_row)
        .find_map(|(line, &ch)| (ch > end).then_some(line))
        .unwrap()
        - 1;

    Span {
        start_row,
        start_col: start - lines[start_row],
        end_row,
        end_col: end - lines[end_row],
    }
}

impl<'a> Token<'a> {
    fn new(kind: TokenKind, range: (usize, usize), chars: &'a [char], lines: &[usize]) -> Self {
        let (start, end) = range;
        Self {
            kind,
            text: TokenText::Slice(&chars[start..end]),
            span: make_span(start, end, lines),
        }
    }
}


pub struct Lexer<'a> {
    chars: Vec<char>,
    state: RefCell<LexerState>,
    lines: Vec<usize>,
    buffered: RefCell<VecDeque<Token<'a>>>,
}

impl fmt::Debug for Lexer<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Lexer")
            .field("position", &self.position())
            .field("read_position", &self.state.borrow().read_position)
            .field("ch", &self.ch())
            .finish()
    }
}

fn is_whitespace(ch: char) -> bool {
    ch != '\n' && ch.is_ascii_whitespace()
}

fn is_word_start(ch: char) -> bool {
    ch.is_ascii_alphabetic()
}
fn is_word(ch: char) -> bool {
    is_word_start(ch) || ch.is_ascii_digit()
}

fn is_label_start(ch: char) -> bool {
    ch.is_alphabetic() || matches!(ch, '_' | '$' | '.' | '?')
}

fn is_label(ch: char) -> bool {
    is_label_start(ch) || ch.is_ascii_digit()
}

impl<'a> Lexer<'a> {
    fn ch(&self) -> Option<&char> {
        self.chars.get(self.position())
    }

    pub fn new(input: &str) -> Self {
        let chars = input.chars().collect();

        let lines = std::iter::once(0)
            .chain(
                input
                    .chars()
                    .enumerate()
                    .filter_map(|(idx, ch)| (ch == '\n').then_some(idx + 1)),
            )
            .collect();

        Self {
            chars,
            state: RefCell::new(LexerState {
                position: 0,
                read_position: 1,
            }),
            lines,
            buffered: Default::default(),
        }
    }

    fn rest_of_input(&self) -> TokenText {
        TokenText::Slice(&self.chars[self.state.borrow().position..])
    }

    fn position(&self) -> usize {
        self.state.borrow().position
    }

    fn read_label(&self) -> Option<Token> {
        let mut state = self.state.borrow().to_owned();
        state.read_while(&self.chars, is_whitespace);

        let (start, end) = state.wordy(&self.chars, is_label_start, is_label)?;

        let span = make_span(start, end, &self.lines);
        let text = TokenText::Slice(&self.chars[start..end]);

        state.read_while(&self.chars, is_whitespace);

        if state.ch(&self.chars)? == ':' {
            state.read_char(&self.chars);

            *self.state.borrow_mut() = state;
            Some(Token {
                kind: TokenKind::Label,
                text,
                span,
            })
        } else {
            None
        }
    }

    fn read_instruction(&self) -> Option<Token> {
        let mut state = self.state.borrow().to_owned();

        state.read_while(&self.chars, is_whitespace);
        let (start, end) = state.wordy(&self.chars, is_word_start, is_word)?;

        let span = make_span(start, end, &self.lines);
        let text = TokenText::Slice(&self.chars[start..end]);

        *self.state.borrow_mut() = state;
        Some(Token {
            kind: TokenKind::Instruction,
            text,
            span,
        })
    }

    fn read_register(&self) -> Option<Token> {
        let mut state = self.state.borrow().clone();

        let (start, end) = state.wordy(&self.chars, is_word_start, is_word)?;

        match state.ch(&self.chars) {
            None => {}
            Some(w) if w.is_ascii_whitespace() => {}
            Some(',') => {}
            _ => return None,
        }

        let span = make_span(start, end, &self.lines);
        let text = TokenText::Slice(&self.chars[start..end]);
        *self.state.borrow_mut() = state;

        Some(Token {
            kind: TokenKind::Register,
            text,
            span,
        })
    }

    fn read_number<'b>(
        state: &mut LexerState,
        chars: &'b [char],
        lines: &[usize],
    ) -> Option<Token<'b>> {
        // simple decimal
        state
            .cant_end_with(chars, |ch| ch.is_ascii_digit(), is_word)
            .map(|range| Token::new(TokenKind::Const, range, chars, lines))
    }

    fn read_effective_address(&'a self) -> Option<()> {
        let mut state = self.state.borrow().clone();
        let mut buf = vec![];
        state.read_while(&self.chars, is_whitespace);
        let start = state.position;
        let Some('[') = state.read_char(&self.chars) else {
            return None;
        };
        let end = state.position;
        buf.push(Token::new(
            TokenKind::OpenEffectiveAddress,
            (start, end),
            &self.chars,
            &self.lines,
        ));

        let tokens = state.delimited(
            &self.chars,
            |state, chars| {
                state.either(
                    chars,
                    |state, chars| {
                        state
                            .wordy(chars, is_label_start, is_label)
                            .map(|range| Token::new(TokenKind::Label, range, chars, &self.lines))
                    },
                    |state, chars| Lexer::read_number(state, chars, &self.lines),
                )
            },
            |state, chars| {
                state.either3(
                    chars,
                    |state, chars| {
                        state
                            .chr(chars, '+')
                            .map(|range| Token::new(TokenKind::Plus, range, chars, &self.lines))
                    },
                    |state: &mut LexerState, chars| {
                        state
                            .chr(chars, '-')
                            .map(|range| Token::new(TokenKind::Minus, range, chars, &self.lines))
                    },
                    |state: &mut LexerState, chars| {
                        state
                            .chr(chars, '*')
                            .map(|range| Token::new(TokenKind::Times, range, chars, &self.lines))
                    },
                )
            },
            is_whitespace,
        );

        buf.extend(tokens.into_iter());

        // we can
        // - have words (alphanum | ':' | '.' | '$' | '_')
        // - have consts
        // - do arithmetic (*,-,+)

        let start = state.position;
        let Some(']') = state.read_char(&self.chars) else {
            return None;
        };
        let end = state.position;
        buf.push(Token::new(
            TokenKind::CloseEffectiveAddress,
            (start, end),
            &self.chars,
            &self.lines,
        ));

        // commit
        *self.state.borrow_mut() = state;
        let mut buffer = self.buffered.borrow_mut();
        for v in buf {
            buffer.push_back(v);
        }
        Some(())
    }

    /// reads a single operand. If the operand consists of multiple tokens, consumes every token.
    /// pushes all the operands to the buffer
    fn read_operand(&'a self) -> Option<()> {
        // Instruction operands may take a number of forms: they can be registers,
        // described simply by the register name (e.g. ax, bp, ebx, cr0: NASM does not use
        // the gas–style syntax in which register names must be prefixed by a % sign), or
        // they can be effective addresses (see section 3.3), constants (section 3.4) or
        // expressions (section 3.5).

        if let Some(register) = self.read_register() {
            self.buffered.borrow_mut().push_back(register);
            return Some(());
        }
        if self.read_effective_address().is_some() {
            return Some(());
        }

        None
    }

    fn read_operands(&'a self) {
        self.state
            .borrow_mut()
            .read_while(&self.chars, is_whitespace);
        if self.read_operand().is_none() {
            return;
        }

        while let Some(',') = {
            // scope because state must be dropped. otherwise panics.
            let state = self.state.borrow();
            state.ch(&self.chars)
        } {
            self.state.borrow_mut().read_char(&self.chars);
            self.state
                .borrow_mut()
                .read_while(&self.chars, is_whitespace);
            if self.read_operand().is_none() {
                let (start, end) = self
                    .state
                    .borrow_mut()
                    .read_until(&self.chars, |ch| ch == '\n');

                self.buffered.borrow_mut().push_back(Token {
                    kind: TokenKind::Illegal(ErrorKind::TrailingComma),
                    text: TokenText::Slice(&self.chars[start..end]),
                    span: make_span(start, end, &self.lines),
                });
            }
        }
    }

    /// this does not yet handle macros or the like
    fn read_line(&'a self) {
        if let Some(label) = self.read_label() {
            self.buffered.borrow_mut().push_back(label);
        }

        if let Some(instr) = self.read_instruction() {
            self.buffered.borrow_mut().push_back(instr);
        }
        self.read_operands();
        // self.read_comment();

        eprintln!("read_line {:?}", self.rest_of_input());
        let ch = self.state.borrow_mut().read_char(&self.chars);
        dbg!(ch);
        match ch {
            None | Some('\n') => {}
            _ => {
                let (start, end) = self
                    .state
                    .borrow_mut()
                    .read_until(&self.chars, |ch| ch == '\n');

                self.buffered.borrow_mut().push_back(Token {
                    kind: TokenKind::Illegal(ErrorKind::Unknown),
                    text: TokenText::Slice(&self.chars[start..end]),
                    span: make_span(start, end, &self.lines),
                });
            }
        }
    }

    fn first_buffered(&self) -> Option<Token> {
        self.buffered.borrow_mut().pop_front()
    }

    /// Produces the next token in the program
    /// in case of failure, consumes the rest of the offending line and continues
    pub fn next_token(&'a self) -> Option<Token> {
        if let Some(first) = self.first_buffered() {
            return Some(first);
        }
        self.read_line();
        self.first_buffered()
    }
}

#[cfg(test)]
mod tests {
    use std::collections::VecDeque;

    use super::*;
    fn snapshot_lexing(input: &str) -> String {
        let lexer = Lexer::new(input);

        let mut tokens = VecDeque::new();
        while let Some(tok) = lexer.next_token() {
            // if matches!(tok.kind, TokenKind::Illegal(_)) {
            //     //     panic!("failure: {input:#?}");
            //     tokens.push_back(tok);
            //     break;
            // }

            tokens.push_back(tok);
        }

        let mut output = String::new();
        eprintln!("{tokens:?}");
        for (row, line) in input.lines().enumerate() {
            output += line;
            output += "\n";

            while let Some(tok) = tokens.pop_front() {
                if tok.span.start_row != tok.span.end_row {
                    panic!("We haven't handled this yet");
                }

                if tok.span.start_row != row {
                    tokens.push_front(tok);
                    break;
                }

                output += &" ".repeat(tok.span.start_col);
                output += &"^".repeat(tok.span.end_col - tok.span.start_col);
                output += &format!(" {tok:?}");
                output += "\n"
            }
        }

        output
    }

    macro_rules! snap {
        ($name:tt, $path:literal) => {
            #[test]
            fn $name() {
                let contents = include_str!($path);
                let snapshot = snapshot_lexing(contents);
                let mut settings = insta::Settings::clone_current();
                settings.set_snapshot_path("../testdata/output/");
                settings.bind(|| {
                    insta::assert_snapshot!(snapshot);
                });
            }
        };
    }

    snap!(hello, "../testdata/hello.asm");
    snap!(printf1, "../testdata/printf1.asm");
    snap!(hm, "../testdata/hm.asm");
}
