mod codegen;
mod lexer;
mod parser;
use ariadne::{Label, Report, ReportKind, Source};
use clap::Parser;
use std::{borrow::Cow, num::ParseIntError, ops::Range, path::PathBuf};

/// An assembler written for the NVM virtual machine.
#[derive(Parser)]
#[command(version)]
struct Cli {
    /// A path to the file to assemble.
    file: PathBuf,
}

/// Main entry point of the program.
fn main() -> Result<(), ParseIntError> {
    let cli = Cli::parse();
    let Ok(src) = std::fs::read_to_string(&cli.file) else {
        panic!("failed to read Grim source code from {:?}", cli.file);
    };
    let tokens = lexer::lex(&cli.file.to_string_lossy(), &src);
    let (items, locations) = parser::parse(&cli.file.to_string_lossy(), &src, tokens.iter())?;
    let bytecode = codegen::gen_bytecode(items, &locations);
    let mut out_file = cli.file.clone();
    if !out_file.set_extension("nvm") {
        out_file = out_file.with_extension("nvm");
    }
    std::fs::write(&out_file, bytecode).expect("failed to write to the output file");
    Ok(())
}

/// Reports an error and aborts.
fn grim_error<'id, LabelIter: IntoIterator<Item = Label<(&'id Cow<'id, str>, Range<usize>)>>>(
    file: (&Cow<str>, &str, usize),
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
    std::process::abort();
}
