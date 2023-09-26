mod codegen;
mod lexer;
mod parser;
use self::codegen::CodegenError;
use ariadne::{Label, Report, ReportKind, Source};
use clap::{Parser as CliParser, ValueEnum};
use core::ops::Range;
use std::{borrow::Cow, path::PathBuf};

/// Describes what type of output file should be generated by the compiler.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
enum OutputFileType {
    /// An executable or system library.
    Bin,
    /// An object file.
    Obj,
    /// The generated assembly.
    Asm,
}

/// Describes an optimization level.
#[derive(Clone, Copy, ValueEnum)]
enum OptLevel {
    /// Do not optimize.
    None,
    /// Slightly optimize.
    Less,
    /// The default level of optimization.
    Default,
    /// Aggressively optimize.
    Aggressive,
}

/// A compiler for the Salvo programming language.
#[derive(CliParser)]
#[command(version)]
struct Cli {
    /// A path to the file to compile.
    file: PathBuf,
    /// The target to compile for.
    #[arg(long, default_value_t = String::from("nvm"))]
    target: String,
    /// The linker to use.
    #[arg(long, default_value_t = String::from("ld"))]
    linker: String,
    /// The output file type.
    #[arg(long, default_value = "bin")]
    out_file_type: OutputFileType,
    /// The optimization level to use.
    #[arg(long, default_value = "default")]
    opt_level: OptLevel,
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
    std::process::abort();
}

/// Compiles Salvo source code.
fn compile(
    filename: &str,
    src: &str,
    target: &str,
    linker: &str,
    out_file_type: OutputFileType,
    opt_level: OptLevel,
) -> Result<(), CodegenError> {
    let tokens = lexer::lex(filename, src);
    let items = parser::parse(filename, src, tokens.iter());
    codegen::gen(filename, target, linker, out_file_type, opt_level, items)
}

/// Main entry point of the program.
fn main() -> Result<(), CodegenError> {
    let cli = Cli::parse();
    let Ok(src) = std::fs::read_to_string(&cli.file) else {
        panic!("failed to read Salvo source code from {:?}", cli.file);
    };
    let filename = cli.file.to_string_lossy();
    match filename {
        Cow::Borrowed(filename) => compile(
            filename,
            &src,
            &cli.target,
            &cli.linker,
            cli.out_file_type,
            cli.opt_level,
        ),
        Cow::Owned(filename) => compile(
            &filename,
            &src,
            &cli.target,
            &cli.linker,
            cli.out_file_type,
            cli.opt_level,
        ),
    }
}
