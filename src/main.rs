use std::{
    io::{stdin, BufRead},
    path::PathBuf,
};

use asm_lexer::Lexer;
use clap::Parser;

#[derive(Parser, Debug)]
#[clap(author, version, about)]
struct Arguments {
    #[clap(value_name = "FILE")]
    file: Option<PathBuf>,
}

fn main() {
    let Arguments { file } = Arguments::parse();
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

    // todo: format stream

    let output = asm_lexer::to_string(parsed);
    println!("{output}");
}
