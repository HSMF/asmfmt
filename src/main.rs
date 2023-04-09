use std::{
    io::{stdin, BufRead},
    path::PathBuf,
};

use asm_lexer::Lexer;
use clap::Parser;

#[derive(Parser, Debug)]
#[clap(author, version, about)]
struct Arguments {
    /// The file to format. If no FILE is provided or FILE is -, then input is taken from stdin
    #[clap(value_name = "FILE")]
    file: Option<PathBuf>,
}

// TODO: read config from a config file

fn main() {
    let Arguments { file } = Arguments::parse();
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

    // == apply global rules ==
    let mut buffered = parsed.collect::<Vec<_>>();
    // align comments
    fmt::align_comments(&mut buffered, false);

    let output = asm_lexer::to_string(buffered.iter());
    println!("{output}");
}
