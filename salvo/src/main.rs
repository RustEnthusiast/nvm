mod codegen;
mod lexer;
mod parser;
use self::{codegen::CodegenError, parser::Item};
use ariadne::{Label, Report, ReportKind, Source};
use clap::Parser as CliParser;
use core::ops::Range;
use std::{borrow::Cow, path::PathBuf};

/// A compiler for the Salvo programming language.
#[derive(CliParser)]
#[command(version)]
struct Cli {
    /// A path to the file to compile.
    file: PathBuf,
}

/// Reports an error and aborts.
fn salvo_error<'id, LabelIter: IntoIterator<Item = Label<(&'id str, Range<usize>)>>>(
    file: (&str, &str, usize),
    msg: &str,
    labels: LabelIter,
    note: Option<&str>,
) -> ! {
    let mut builder = Report::build(ReportKind::Error, file.0, file.2).with_message(msg);
    for label in labels {
        builder = builder.with_label(label);
    }
    if let Some(note) = note {
        builder = builder.with_note(note);
    }
    builder
        .finish()
        .eprint((file.0, Source::from(file.1)))
        .expect("failure to write to stderr");
    std::process::exit(101);
}

/// Checks for the program's `main` function.
fn check_main(filename: &str, src: &str, items: &[Item]) {
    for item in items {
        let Item::Fn(f) = item;
        if f.name() == "main" {
            return;
        }
    }
    salvo_error((filename, src, 0), "`main` function not found.", [], None);
}

/// Compiles Salvo source code.
fn compile(filename: &str, src: &str) -> Result<(), CodegenError> {
    let tokens = lexer::lex(filename, src);
    let items = parser::parse(filename, src, tokens.iter());
    check_main(filename, src, &items);
    codegen::gen(filename, items)
}

/// Main entry point of the program.
fn main() -> Result<(), CodegenError> {
    let cli = Cli::parse();
    let Ok(src) = std::fs::read_to_string(&cli.file) else {
        panic!("failed to read Salvo source code from {:?}", cli.file);
    };
    let filename = cli.file.to_string_lossy();
    match filename {
        Cow::Borrowed(filename) => compile(filename, &src),
        Cow::Owned(filename) => compile(&filename, &src),
    }
}
