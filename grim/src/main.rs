use clap::Parser;
use std::{borrow::Cow, num::ParseIntError, path::PathBuf};

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
    let filename = cli.file.to_string_lossy();
    let bytecode = match filename {
        Cow::Borrowed(filename) => grim::assemble(filename, &src)?,
        Cow::Owned(filename) => grim::assemble(&filename, &src)?,
    };
    let mut out_file = cli.file.clone();
    if !out_file.set_extension("nvm") {
        out_file = out_file.with_extension("nvm");
    }
    std::fs::write(&out_file, bytecode).expect("failed to write to the output file");
    Ok(())
}
