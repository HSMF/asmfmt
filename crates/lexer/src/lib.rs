/*!
* # A lexer for NASM-Style Assembly.
*
* ```
* # use asm_lexer::{parse};
* let input = "mov eax, ecx";
*
* for token in parse(input).unwrap() {
*   // do stuff
*   // in case of failure, the token will contain
*   // the rest of the line and continue normally
* }
* ```
*
* */

use nom::{
    branch::alt,
    bytes::complete::{
        tag, tag_no_case, take_until, take_until1, take_while, take_while1, take_while_m_n,
    },
    character::complete::{one_of, satisfy},
    combinator::{fail, map, not, opt},
    error::ParseError,
    multi::{many0, separated_list0, separated_list1},
    sequence::{delimited, preceded, terminated, tuple},
    IResult, Parser,
};
use nom_locate::{position, LocatedSpan};
use nom_supreme::error::ErrorTree;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
/// The base of a number.
pub enum Base {
    Binary,
    Octal,
    Decimal,
    Hexadecimal,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum TokenKind {
    /// A Label
    Label,

    #[default]
    Illegal,
    /// An instruction. Depending on the actual instruction there could be zero or more arguments
    /// but this is not checked by the lexer
    Instruction,
    /// A literal number, in the given base
    Number(Base),
    /// a end of line style comment, excluding the `;`
    Comment,

    // operands
    /// a register
    Register,

    OpenParen,
    CloseParen,

    Ident,
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
    /// A Split (,) operator
    Split,
    String,
    TernaryIf,
    TernaryElse,
    BoolOr,
    BoolXor,
    BoolAnd,
    Equals,
    NotEquals,
    LessThanEquals,
    GreaterThanEquals,
    GreaterThan,
    LessThan,
    BitOr,
    BitXor,
    BitAnd,
    ShiftRight,
    ShiftLeft,
    DivUnsigned,
    DivSigned,
    ModUnsigned,
    ModSigned,
    Negative,
    Positive,
    Segment,
    BoolNegation,
    BitNegation,
    SignedCmp,
    Wrt,
    /// A size modifier, such as DWORD
    Size,
    BitsDirective,
    Default,
    DefaultsValue,
    Section,
    SectionName,
    GlobalValue,
    Global,
    ExternValue,
    Extern,

    /// DB, DW, DD, DQ, DT, DO, DY and DZ.
    /// DT, DO, DY and DZ are currently unsupported
    DeclareMemoryInit,

    /// `equ`
    Equ,
}

#[derive(Debug, PartialEq, Eq)]
struct RawToken<'a> {
    kind: TokenKind,
    pos: Span<'a>,
    length: usize,
}

impl<'a> RawToken<'a> {
    fn from_span(kind: TokenKind, s: Span<'a>) -> Self {
        Self {
            kind,
            pos: s,
            length: s.len(),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Token<'a> {
    pub kind: TokenKind,
    pub line: u32,
    pub col: usize,
    pub text: &'a str,
}

impl<'a> Token<'a> {
    fn from_raw(raw: RawToken, input: &'a str) -> Self {
        Token {
            kind: raw.kind,
            line: raw.pos.location_line(),
            col: raw.pos.get_utf8_column(),
            text: &input[raw.pos.location_offset()..raw.pos.location_offset() + raw.length],
        }
    }
}

mod token_tree;

pub type Span<'a> = LocatedSpan<&'a str>;

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

fn is_ident_start(ch: char) -> bool {
    ch.is_alphabetic() || matches!(ch, '_' | '$' | '.' | '?')
}

fn is_ident(ch: char) -> bool {
    is_label_start(ch) || ch.is_ascii_digit() || ch == ':'
}

fn is_space(ch: char) -> bool {
    ch.is_ascii() && nom::character::is_space(ch as u8)
}

fn take_whitespace<'a, E: ParseError<Span<'a>>>(s: Span<'a>) -> IResult<Span<'a>, (), E> {
    // TODO: handle '\<newline', which is whitespace
    let (s, _) = take_while(is_space)(s)?;
    Ok((s, ()))
}

fn parse_wordy<'a, F1, F2, E: ParseError<Span<'a>>>(
    start: F1,
    rest: F2,
    kind: TokenKind,
) -> impl FnMut(Span<'a>) -> IResult<Span<'a>, RawToken<'a>, E>
where
    F1: Fn(char) -> bool,
    F2: Fn(char) -> bool,
{
    move |s| {
        let (s, _) = take_whitespace(s)?;
        let (s, pos) = position(s)?;
        let (s, prefix) = satisfy(&start)(s)?;
        let (s, word) = take_while(&rest)(s)?;
        let (s, _) = take_whitespace(s)?;
        Ok((
            s,
            RawToken {
                kind,
                pos,
                length: prefix.len_utf8() + word.len(),
            },
        ))
    }
}

fn parse_label<'a, E: ParseError<Span<'a>>>(s: Span<'a>) -> IResult<Span<'a>, RawToken<'a>, E> {
    terminated(
        parse_wordy(is_label_start, is_label, TokenKind::Label),
        tag(":"),
    )(s)
}

fn parse_instruction<'a, E: ParseError<Span<'a>>>(
    s: Span<'a>,
) -> IResult<Span<'a>, RawToken<'a>, E> {
    parse_wordy(is_word_start, is_word, TokenKind::Instruction)(s)
}

fn parse_expr<'a, E: ParseError<Span<'a>>>(s: Span<'a>) -> IResult<Span<'a>, Vec<RawToken<'a>>, E> {
    // boolean ? trueval : falseval
    let conditional_operator = |s: Span<'a>| -> IResult<Span<'a>, Vec<RawToken<'a>>, E> {
        let mut out = vec![];

        let (s, boolean) = if s.starts_with('(') {
            parse_expr(s)?
        } else {
            let (s, left) = take_until1("?")(s)?;
            let (remainder, a) = parse_expr(left)?;
            if !remainder.is_empty() {
                fail::<_, (), E>(s)?;
            }

            (s, a)
        };

        let (s, ternary_if) = tag("?")(s)?;
        let (s, trueval) = parse_expr(s)?;
        let (s, ternary_else) = tag(":")(s)?;
        let (s, falseval) = parse_expr(s)?;

        out.extend(boolean.into_iter());
        out.push(RawToken::from_span(TokenKind::TernaryIf, ternary_if));
        out.extend(trueval.into_iter());
        out.push(RawToken::from_span(TokenKind::TernaryElse, ternary_else));
        out.extend(falseval.into_iter());

        Ok((s, out))
    };

    let binop = move |operator: &'static str, kind| {
        move |s: Span<'a>| -> IResult<Span<'a>, Vec<RawToken<'a>>, E> {
            let mut out = vec![];

            let (s, a) = if s.starts_with('(') {
                parse_expr(s)?
            } else {
                let (s, left) = take_until1(operator)(s)?;
                let (remainder, a) = parse_expr(left)?;
                if !remainder.is_empty() {
                    fail::<_, (), E>(s)?;
                }

                (s, a)
            };

            let (s, op) = tag(operator)(s)?;
            let (s, b) = parse_expr(s)?;

            out.extend(a.into_iter());
            out.push(RawToken::from_span(kind, op));
            out.extend(b.into_iter());

            Ok((s, out))
        }
    };

    let unop = move |operator: &'static str, kind| {
        move |s| -> IResult<Span<'a>, Vec<RawToken<'a>>, E> {
            let mut out = vec![];
            let (s, bool_or) = tag(operator)(s)?;
            let (s, a) = parse_expr(s)?;

            out.push(RawToken::from_span(kind, bool_or));
            out.extend(a.into_iter());

            Ok((s, out))
        }
    };

    let boolean_or = binop("||", TokenKind::BoolOr);
    let boolean_xor = binop("^^", TokenKind::BoolXor);
    let boolean_and = binop("&&", TokenKind::BoolAnd);
    let eq = binop("=", TokenKind::Equals);
    let eq2 = binop("==", TokenKind::Equals);
    let neq = binop("!=", TokenKind::NotEquals);
    let neq2 = binop("<>", TokenKind::NotEquals);
    let lt = binop("<", TokenKind::LessThan);
    let lteq = binop("<=", TokenKind::LessThanEquals);
    let gt = binop(">", TokenKind::GreaterThan);
    let gteq = binop(">=", TokenKind::GreaterThanEquals);
    let signed_cmp = binop("<=>", TokenKind::SignedCmp);

    let bit_or = binop("|", TokenKind::BitOr);
    let bit_xor = binop("^", TokenKind::BitXor);
    let bit_and = binop("&", TokenKind::BitAnd);

    let shift_left = binop("<<", TokenKind::ShiftLeft);
    let shift_right = binop(">>", TokenKind::ShiftRight);

    let add = binop("+", TokenKind::Plus);
    let sub = binop("-", TokenKind::Minus);

    let wrt = binop("WRT", TokenKind::Wrt);

    let mul = binop("*", TokenKind::Times);
    let div_signed = binop("//", TokenKind::DivSigned);
    let div_unsigned = binop("/", TokenKind::DivUnsigned);
    let mod_signed = binop("%%", TokenKind::ModSigned);
    let mod_unsigned = binop("%", TokenKind::ModUnsigned);

    let negation = unop("-", TokenKind::Negative);
    let positive = unop("+", TokenKind::Positive);
    let bitneg = unop("~", TokenKind::BitNegation);
    let boolneg = unop("!", TokenKind::BoolNegation);

    let segment = unop("SEG", TokenKind::Segment);

    // TODO: implement https://www.nasm.us/doc/nasmdoc6.html#section-6.4

    let unops = alt((
        mul,
        div_signed,
        div_unsigned,
        mod_signed,
        mod_unsigned,
        negation,
        positive,
        bitneg,
        boolneg,
        segment,
    ));

    let binops = alt((
        boolean_or,
        boolean_xor,
        boolean_and,
        eq,
        eq2,
        neq,
        neq2,
        lt,
        lteq,
        gt,
        gteq,
        signed_cmp,
        bit_or,
        bit_xor,
        bit_and,
        shift_left,
        shift_right,
        add,
        sub,
        wrt,
    ));

    let mut out = vec![];
    let (s, _) = take_whitespace(s)?;
    let (s, open_paren) = opt(tag("("))(s)?;
    let (s, _) = take_whitespace(s)?;
    if let Some(paren) = open_paren {
        out.push(RawToken::from_span(TokenKind::OpenParen, paren));
    }
    let (s, expr) = alt((
        unops,
        binops,
        conditional_operator,
        parse_number.map(|x| vec![x]),
        parse_wordy(is_ident_start, is_ident, TokenKind::Ident).map(|x| vec![x]),
    ))(s)?;
    out.extend(expr.into_iter());

    let (s, _) = take_whitespace(s)?;
    let s = if open_paren.is_some() {
        let (s, close_paren) = tag(")")(s)?;
        out.push(RawToken::from_span(TokenKind::OpenParen, close_paren));
        s
    } else {
        s
    };
    let (s, _) = take_whitespace(s)?;

    Ok((s, out))
}

fn parse_str<'a, E: ParseError<Span<'a>>>(s: Span<'a>) -> IResult<Span<'a>, RawToken<'a>, E> {
    // A character string consists of up to eight characters enclosed in either single
    // quotes ('...'), double quotes ("...") or backquotes (`...`). Single or double
    // quotes are equivalent to NASM (except of course that surrounding the constant
    // with single quotes allows double quotes to appear within it and vice versa);
    // the contents of those are represented verbatim. Strings enclosed in backquotes
    // support C-style \–escapes for special characters.
    // \'          single quote (')
    // \"          double quote (")
    // \`          backquote (`)
    // \\          backslash (\)
    // \?          question mark (?)
    // \a          BEL (ASCII 7)
    // \b          BS  (ASCII 8)
    // \t          TAB (ASCII 9)
    // \n          LF  (ASCII 10)
    // \v          VT  (ASCII 11)
    // \f          FF  (ASCII 12)
    // \r          CR  (ASCII 13)
    // \e          ESC (ASCII 27)
    // \377        Up to 3 octal digits - literal byte
    // \xFF        Up to 2 hexadecimal digits - literal byte
    // \u1234      4 hexadecimal digits - Unicode character
    // \U12345678  8 hexadecimal digits - Unicode character

    let chr = move |quot: char| {
        alt((
            map(satisfy(move |ch: char| ch != '\\' && ch != quot), |_| ()),
            map(preceded(tag("\\"), one_of(r#"\\'"`?abtnvfre"#)), |_| ()),
            map(
                preceded(
                    tag("\\x"),
                    take_while_m_n(1, 2, |ch: char| ch.is_ascii_hexdigit()),
                ),
                |_| (),
            ),
            map(
                preceded(
                    tag("\\u"),
                    take_while_m_n(1, 4, |ch: char| ch.is_ascii_hexdigit()),
                ),
                |_| (),
            ),
            map(
                preceded(
                    tag("\\U"),
                    take_while_m_n(1, 8, |ch: char| ch.is_ascii_hexdigit()),
                ),
                |_| (),
            ),
            map(
                preceded(
                    tag("\\o"),
                    take_while_m_n(1, 2, |ch: char| ('0'..='7').contains(&ch)),
                ),
                |_| (),
            ),
        ))
    };

    let (s, _) = take_whitespace(s)?;
    // TODO: when to only take 8 bytes
    let (s, (start, _, end)) = alt((
        delimited(
            tag("\""),
            tuple((position, many0(chr('"')), position)),
            tag("\""),
        ),
        delimited(
            tag("'"),
            tuple((position, many0(chr('\'')), position)),
            tag("'"),
        ),
        delimited(
            tag("`"),
            tuple((position, many0(chr('`')), position)),
            tag("`"),
        ),
    ))(s)?;
    let (s, _) = take_whitespace(s)?;
    Ok((
        s,
        RawToken {
            kind: TokenKind::String,
            pos: start,
            length: end.location_offset() - start.location_offset(),
        },
    ))
}

fn parse_number<'a, E: ParseError<Span<'a>>>(s: Span<'a>) -> IResult<Span<'a>, RawToken<'a>, E> {
    // A numeric constant is simply a number. NASM allows you to specify numbers
    // in a variety of number bases, in a variety of ways: you can suffix H or X, D or
    // T, Q or O, and B or Y for hexadecimal, decimal, octal and binary respectively,
    //
    // or you can prefix 0x, for hexadecimal in the style of C, or you can prefix $
    // for hexadecimal in the style of Borland Pascal or Motorola Assemblers. Note,
    // though, that the $ prefix does double duty as a prefix on identifiers (see
    // section 3.1), so a hex number prefixed with a $ sign must have a digit after
    // the $ rather than a letter.
    // In addition, current versions of NASM accept the
    // prefix 0h for hexadecimal, 0d or 0t for decimal, 0o or 0q for octal, and 0b or
    // 0y for binary. Please note that unlike C, a 0 prefix by itself does not imply
    // an octal constant!

    fn map_number(base: Base) -> impl FnMut(Span) -> RawToken {
        move |span| RawToken {
            kind: TokenKind::Number(base),
            pos: span,
            length: span.len(),
        }
    }

    let hex_postfix = map(
        terminated(
            terminated(take_while1(|ch: char| ch.is_ascii_hexdigit()), one_of("HX")),
            not(satisfy(|ch: char| ch.is_ascii_alphanumeric())),
        ),
        map_number(Base::Hexadecimal),
    );

    let hex_prefix = map(
        preceded(
            alt((tag("0x"), tag("0h"), tag("$"))),
            take_while1(|ch: char| ch.is_ascii_hexdigit()),
        ),
        map_number(Base::Hexadecimal),
    );

    let bin_postfix = map(
        terminated(
            terminated(
                take_while1(|ch: char| ch == '0' || ch == '1'),
                one_of("BYby"),
            ),
            not(satisfy(|ch: char| ch.is_ascii_alphanumeric())),
        ),
        map_number(Base::Binary),
    );

    let bin_prefix = map(
        preceded(tag("0b"), take_while1(|ch: char| ch.is_ascii_hexdigit())),
        map_number(Base::Binary),
    );

    let oct_postfix = map(
        terminated(
            terminated(
                take_while1(|ch: char| ('0'..='7').contains(&ch)),
                one_of("OQoq"),
            ),
            not(satisfy(|ch: char| ch.is_ascii_alphanumeric())),
        ),
        map_number(Base::Octal),
    );

    let oct_prefix = map(
        preceded(
            alt((tag("0o"), tag("0q"))),
            take_while1(|ch: char| ch.is_ascii_hexdigit()),
        ),
        map_number(Base::Octal),
    );

    let dec_postfix = map(
        terminated(
            terminated(take_while1(|ch: char| ch.is_ascii_digit()), one_of("TDtd")),
            not(satisfy(|ch: char| ch.is_ascii_alphanumeric())),
        ),
        map_number(Base::Decimal),
    );

    let dec_prefix = map(
        preceded(tag("0d"), take_while(|ch: char| ch.is_ascii_digit())),
        map_number(Base::Decimal),
    );

    let dec_normal = map(
        take_while1(|ch: char| ch.is_ascii_digit()),
        map_number(Base::Decimal),
    );

    let (s, _) = take_whitespace(s)?;
    let (s, out) = terminated(
        alt((
            hex_postfix,
            hex_prefix,
            bin_postfix,
            bin_prefix,
            oct_postfix,
            oct_prefix,
            dec_postfix,
            dec_prefix,
            dec_normal,
        )),
        not(satisfy(|ch: char| ch.is_ascii_alphanumeric())),
    )(s)?;
    let (s, _) = take_whitespace(s)?;
    Ok((s, out))
}

fn parse_operands<'a, E: ParseError<Span<'a>>>(
    s: Span<'a>,
) -> IResult<Span<'a>, Vec<RawToken<'a>>, E> {
    let parse_effective_addr = |s| {
        let mut out = vec![];
        let (s, _) = take_whitespace(s)?;

        let (s, size) = opt(terminated(
            alt((
                tag_no_case("BYTE"),
                tag_no_case("WORD"),
                tag_no_case("DWORD"),
                tag_no_case("QWORD"),
                tag_no_case("TWORD"),
                tag_no_case("OWORD"),
                tag_no_case("YWORD"),
                tag_no_case("ZWORD"),
            )),
            take_whitespace,
        )
        .map(|s| RawToken::from_span(TokenKind::Size, s)))(s)?;
        if let Some(size) = size {
            out.push(size);
        }

        let (s, o) = tag("[")(s)?;
        // TODO: nosplit
        // TODO: rel
        out.push(RawToken::from_span(TokenKind::OpenEffectiveAddress, o));

        let (s, expr) = parse_expr(s)?;
        out.extend(expr.into_iter());
        let (s, expr) = opt(preceded(tag(","), parse_expr))(s)?;
        if let Some(expr) = expr {
            out.extend(expr.into_iter());
        }

        let (s, o) = tag("]")(s)?;
        out.push(RawToken::from_span(TokenKind::CloseEffectiveAddress, o));
        Ok((s, out))
    };

    fn size<'a, E: ParseError<Span<'a>>>(s: Span<'a>) -> IResult<Span<'a>, Span<'a>, E> {
        alt((
            tag_no_case("BYTE"),
            tag_no_case("WORD"),
            tag_no_case("DWORD"),
            tag_no_case("QWORD"),
            tag_no_case("TWORD"),
            tag_no_case("OWORD"),
            tag_no_case("YWORD"),
            tag_no_case("ZWORD"),
        ))(s)
    }
    let (s, x) = separated_list0::<_, _, _, E, _, _>(
        tag(","),
        alt((
            parse_effective_addr,
            parse_number.map(|x| vec![x]),
            tuple((
                not(size),
                parse_wordy(is_word_start, is_word, TokenKind::Register),
            ))
            .map(|(_, x)| vec![x]),
            tuple((
                opt(terminated(
                    size,
                    tuple((satisfy(is_space), take_whitespace)),
                )),
                parse_wordy(is_ident_start, is_ident, TokenKind::Ident),
            ))
            .map(|(a, b)| {
                let mut out = vec![];
                if let Some(a) = a {
                    out.push(RawToken::from_span(TokenKind::Size, a))
                }
                out.push(b);

                out
            }),
            parse_str.map(|x| vec![x]),
        )),
    )(s)?;

    Ok((s, x.into_iter().flatten().collect()))
}

fn parse_op<'a, E: ParseError<Span<'a>>>(s: Span<'a>) -> IResult<Span<'a>, Vec<RawToken<'a>>, E> {
    let mut output = vec![];
    let (s, instr) = parse_instruction(s)?;
    output.push(instr);

    let (s, operands) = parse_operands(s)?;
    output.extend(operands.into_iter());

    Ok((s, output))
}

fn parse_equ<'a, E: ParseError<Span<'a>>>(s: Span<'a>) -> IResult<Span<'a>, Vec<RawToken<'a>>, E> {
    let (s, _) = take_whitespace(s)?;

    let (s, equ) = tag_no_case("equ")(s)?;
    let (s, _) = take_whitespace(s)?;
    let (s, val) = parse_expr(s)?;
    let mut out = vec![RawToken::from_span(TokenKind::Equ, equ)];
    out.extend(val.into_iter());
    Ok((s, out))
}

fn parse_decl<'a, E: ParseError<Span<'a>>>(s: Span<'a>) -> IResult<Span<'a>, Vec<RawToken<'a>>, E> {
    let (s, _) = take_whitespace(s)?;

    let (s, declarer) = alt((
        tag_no_case("db"),
        tag_no_case("dw"),
        tag_no_case("dd"),
        tag_no_case("dq"),
        // the following are floating point
        // this is not yet supported
        // tag_no_case("DT"),
        // tag_no_case("DO"),
        // tag_no_case("DY"),
        // tag_no_case("DZ"),
    ))(s)?;

    let (s, value) = separated_list1(tag(","), alt((parse_number, parse_str)))(s)?;

    let mut out = vec![RawToken::from_span(TokenKind::DeclareMemoryInit, declarer)];
    out.extend(value.into_iter());

    Ok((s, out))
}

fn parse_comment<'a, E: ParseError<Span<'a>>>(s: Span<'a>) -> IResult<Span<'a>, RawToken<'a>, E> {
    let (s, _) = take_whitespace(s)?;

    let (s, comment) = preceded(tag(";"), take_until("\n"))(s)?;
    Ok((
        s,
        RawToken {
            kind: TokenKind::Comment,
            pos: comment,
            length: comment.len(),
        },
    ))
}

fn parse_directive<'a, E: ParseError<Span<'a>>>(
    s: Span<'a>,
) -> IResult<Span<'a>, Vec<RawToken<'a>>, E> {
    fn primitive_directive<'a, E: ParseError<Span<'a>>>(
        mut body: impl FnMut(Span<'a>) -> IResult<Span<'a>, Vec<RawToken<'a>>, E>,
    ) -> impl FnMut(Span<'a>) -> IResult<Span<'a>, Vec<RawToken<'a>>, E> {
        move |s| {
            let (s, _) = tag("[")(s)?;
            let (s, _) = take_whitespace(s)?;
            let (s, bd) = body(s)?;
            let (s, _) = take_whitespace(s)?;
            let (s, _) = tag("]")(s)?;
            Ok((s, bd))
        }
    }

    fn user_directive<'a, E: ParseError<Span<'a>>>(
        mut body: impl FnMut(Span<'a>) -> IResult<Span<'a>, Vec<RawToken<'a>>, E>,
    ) -> impl FnMut(Span<'a>) -> IResult<Span<'a>, Vec<RawToken<'a>>, E> {
        move |s| {
            let (s, _) = take_whitespace(s)?;
            let (s, bd) = body(s)?;
            let (s, _) = take_whitespace(s)?;
            Ok((s, bd))
        }
    }

    fn two_parter<'a, E: ParseError<Span<'a>>>(
        name: &'static str,
        mut argument: impl FnMut(Span<'a>) -> IResult<Span<'a>, Vec<RawToken<'a>>, E>,
        mapping: impl Fn(Span<'a>) -> RawToken<'a>,
    ) -> impl FnMut(Span<'a>) -> IResult<Span<'a>, Vec<RawToken<'a>>, E> {
        move |s| {
            let (s, name) = tag_no_case(name)(s)?;
            let (s, _) = satisfy(is_space)(s)?;
            let (s, _) = take_whitespace(s)?;
            let (s, args) = argument(s)?;
            let mut out = vec![mapping(name)];
            out.extend(args.into_iter());
            Ok((s, out))
        }
    }

    let bits = two_parter(
        "bits",
        map(alt((tag("64"), tag("32"), tag("16"))), |x| {
            vec![RawToken::from_span(TokenKind::Number(Base::Decimal), x)]
        }),
        |span| RawToken::from_span(TokenKind::BitsDirective, span),
    );

    let default = two_parter(
        "default",
        map(
            alt((tag("REL"), tag("ABS"), tag("BND"), tag("NOBND"))),
            |span| vec![RawToken::from_span(TokenKind::DefaultsValue, span)],
        ),
        |span| RawToken::from_span(TokenKind::Default, span),
    );

    let section = two_parter(
        "section",
        map(
            parse_wordy(is_label_start, is_label, TokenKind::SectionName),
            |s| vec![s],
        ),
        |span| RawToken::from_span(TokenKind::Section, span),
    );

    let segment = two_parter(
        "segment",
        map(
            parse_wordy(is_label_start, is_label, TokenKind::SectionName),
            |s| vec![s],
        ),
        |span| RawToken::from_span(TokenKind::Section, span),
    );

    let global = two_parter(
        "global",
        separated_list1(
            tag(","),
            parse_wordy(is_label_start, is_label, TokenKind::GlobalValue),
        ),
        |span| RawToken::from_span(TokenKind::Global, span),
    );

    // TODO: wrt
    let ext = two_parter(
        "extern",
        separated_list1(
            tag(","),
            parse_wordy(is_label_start, is_label, TokenKind::ExternValue),
        ),
        |span| RawToken::from_span(TokenKind::Extern, span),
    );

    let (s, (directive, comment)) = terminated(
        tuple((
            delimited(
                take_whitespace,
                alt((
                    primitive_directive(bits),
                    user_directive(default),
                    user_directive(section),
                    user_directive(segment),
                    user_directive(ext),
                    user_directive(global),
                )),
                take_whitespace,
            ),
            opt(parse_comment),
        )),
        tag("\n"),
    )(s)?;

    let mut out = directive;
    if let Some(comment) = comment {
        out.push(comment);
    }

    Ok((s, out))
}

fn parse_line<'a, E: ParseError<Span<'a>>>(s: Span<'a>) -> IResult<Span<'a>, Vec<RawToken<'a>>, E> {
    macro_rules! unwrap_or_return_illegal {
        ($e:expr, $output:expr, $s:expr) => {
            match $e {
                Ok(x) => x,
                Err(_) => {
                    let (rest, invalid) = terminated(take_until::<_, _, E>("\n"), tag("\n"))($s)
                        .unwrap_or((Span::new(""), $s));

                    $output.push(RawToken {
                        kind: TokenKind::Illegal,
                        pos: invalid,
                        length: invalid.len(),
                    });

                    return Ok((rest, $output));
                }
            }
        };
    }

    let mut output = vec![];
    let (s, label) = unwrap_or_return_illegal!(opt::<_, _, E, _>(parse_label)(s), output, s);
    if let Some(label) = label {
        output.push(label);
    }

    let (s, ops) = unwrap_or_return_illegal!(
        opt::<_, _, E, _>(alt((parse_equ, parse_decl, parse_op)))(s),
        output,
        s
    );
    if let Some(ops) = ops {
        output.extend(ops);
    }

    let (s, comment) = unwrap_or_return_illegal!(opt::<_, _, E, _>(parse_comment)(s), output, s);
    if let Some(comment) = comment {
        output.push(comment);
    }

    let (s, _) = unwrap_or_return_illegal!(tag::<_, _, E>("\n")(s), output, s);

    Ok((s, output))
}

fn parse_all<'a, E: ParseError<Span<'a>>>(
    mut input: Span<'a>,
) -> IResult<Span<'a>, Vec<RawToken<'a>>, E> {
    let mut output = vec![];
    while !input.is_empty() {
        let (rest, line) = alt((
            terminated(take_whitespace, tag("\n")).map(|_| vec![]),
            parse_directive,
            parse_line,
        ))(input)?;
        input = rest;
        output.extend(line.into_iter());
    }

    Ok((input, output))
}

// NOTE: this very much is *not* infallible
pub fn parse(input: &str) -> Result<impl Iterator<Item = Token>, std::convert::Infallible> {
    let span = Span::new(input);
    let (s, all) = parse_all::<ErrorTree<Span>>(span).expect("handle error");
    assert_eq!(s.fragment(), &"", "todo: handle incomplete match");

    Ok(all.into_iter().map(|x| Token::from_raw(x, input)))
}

#[cfg(test)]
mod tests {
    use std::collections::VecDeque;

    use super::*;
    fn snapshot_lexing(input: &str) -> String {
        let mut tokens = parse(input).unwrap().collect::<VecDeque<_>>();

        let mut output = String::new();
        // eprintln!("{tokens:?}");
        if let Some(x) = tokens.iter().find(|x| matches!(x.kind, TokenKind::Illegal)) {
            dbg!(x);
            panic!("ajksd");
        }
        for (row, line) in input.lines().enumerate() {
            output += line;
            output += "\n";

            while let Some(tok) = tokens.pop_front() {
                if tok.line as usize != row + 1 {
                    tokens.push_front(tok);
                    break;
                }

                output += &" ".repeat(tok.col - 1);
                output += &"^".repeat(tok.text.len());
                output += &format!(
                    " {:?} : ({}/{}) {:?}",
                    tok.kind, tok.line, tok.col, tok.text
                );
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
    snap!(directives, "../testdata/directives.asm");

    mod components {
        use super::*;
        mod label {
            use super::*;

            fn label(line: u32, col: usize, text: &str) -> Token {
                Token {
                    kind: crate::TokenKind::Label,
                    line,
                    col,
                    text,
                }
            }
            fn prs(s: &str) -> IResult<Span, RawToken, ErrorTree<Span>> {
                let s = Span::new(s);
                parse_label::<ErrorTree<Span>>(s)
            }

            #[test]
            fn works() {
                let inputs = "some_label: mov eax, ebx";
                let parsed = prs(inputs).expect("managed to parse");
                assert_eq!(parsed.0.fragment(), &" mov eax, ebx");
                assert_eq!(Token::from_raw(parsed.1, inputs), label(1, 1, "some_label"));
            }

            #[test]
            fn not_like_this() {
                let inputs = "some label: mov eax, ebx";
                prs(inputs).expect_err("failed to parse");
            }
        }
    }
}
