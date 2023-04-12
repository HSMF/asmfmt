use std::{
    io::{stdin, BufRead},
    path::PathBuf,
};

use asm_lexer::{Lexer, TokenKind};
use clap::Parser;
use fmt::{AlignOperandsOpt, FixCase, IndentDirectives};
use serde::{Deserialize, Serialize};

#[derive(Parser, Debug)]
#[clap(author, version, about)]
struct Arguments {
    /// The file to format. If no FILE is provided or FILE is -, then input is taken from stdin
    #[clap(value_name = "FILE")]
    file: Option<PathBuf>,

    /// which configuration to use
    #[clap(short, long, value_name = "CONFIG_FILE")]
    config: Option<PathBuf>,
}

#[derive(Debug, Serialize, Deserialize, Default)]
struct Configuration {
    use_tabs: Option<bool>,
    shift_only_comments: Option<bool>,
    align_operands: Option<AlignOperandsOpt>,
    align_pseudo_ops: Option<AlignOperandsOpt>,
    uppercase_tokens: Option<Vec<TokenKind>>,
    // u8 because let's not be silly
    indent_directives: Option<u8>,
}

// TODO: read config from a config file

fn main() {
    let Arguments { file, config } = Arguments::parse();
    let config: Configuration = config
        .map(|config| std::fs::read_to_string(config).expect("can read config"))
        .map(|config| serde_yaml::from_str(&config).expect("config is valid"))
        .unwrap_or_default();

    assert_ne!(config.use_tabs, Some(true));

    let file = file.and_then(|x| (x != PathBuf::from("-")).then_some(x));
    let content = if let Some(file) = &file {
        std::fs::read_to_string(file).expect("file did not exist")
    } else {
        let stdin = stdin().lock();
        let mut out = "".to_owned();
        for line in stdin.lines() {
            out += &line.unwrap();
            out.push('\n');
        }
        out
    };
    let parsed = Lexer::new(&content);

    // == apply local rules ==
    let parsed = FixCase::new(parsed).set_uppercase_tokens(std::mem::take(
        &mut config.uppercase_tokens.unwrap_or_default(),
    ));

    let mut parsed = IndentDirectives::new(parsed);
    if let Some(indent_by) = config.indent_directives {
        parsed = parsed.set_indent(indent_by as usize)
    }

    // == apply global rules ==
    let mut buffered = parsed.collect::<Vec<_>>();

    fmt::align_operands(&mut buffered, config.align_operands.unwrap_or_default());
    fmt::align_pseudo(&mut buffered, config.align_pseudo_ops.unwrap_or_default());
    fmt::align_comments(
        &mut buffered,
        config.shift_only_comments.unwrap_or_default(),
    );

    let output = asm_lexer::to_string(buffered.iter());
    println!("{output}");
}
