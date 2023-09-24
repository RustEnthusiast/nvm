mod codegen;
mod lexer;
mod parser;
use ariadne::{Label, Report, ReportKind, Source};
use core::{num::ParseIntError, ops::Range};

/// Assembles Grim source code.
pub fn assemble(filename: &str, src: &str) -> Result<Vec<u8>, ParseIntError> {
    let tokens = lexer::lex(filename, src);
    let (items, locations) = parser::parse(filename, src, tokens.iter())?;
    Ok(codegen::gen_bytecode(items, &locations))
}

/// Reports an error and aborts.
fn grim_error<'id, LabelIter: IntoIterator<Item = Label<(&'id str, Range<usize>)>>>(
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
    std::process::abort();
}
