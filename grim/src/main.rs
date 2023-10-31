use clap::Parser;
use grim::{Bits, Endianness};
use std::{borrow::Cow, num::ParseIntError, path::PathBuf};

/// An assembler written for the NVM virtual machine.
#[derive(Parser)]
#[command(version)]
struct Cli {
    /// A path to the file to assemble.
    file: PathBuf,
    /// The target VM's bit-width.
    #[arg(long, default_value = "native")]
    bits: String,
    /// The target machine's endianness.
    #[arg(long, value_enum, default_value = "native")]
    endianness: Endianness,
}

/// Main entry point of the program.
fn main() -> Result<(), ParseIntError> {
    let cli = Cli::parse();
    let bits = match cli.bits.as_str() {
        "native" => Bits::BitNative,
        "8" => Bits::Bit8,
        "16" => Bits::Bit16,
        "32" => Bits::Bit32,
        "64" => Bits::Bit64,
        "128" => Bits::Bit128,
        _ => panic!("invalid target bit width \"{}\"", cli.bits),
    };
    let Ok(src) = std::fs::read_to_string(&cli.file) else {
        panic!("failed to read Grim source code from {:?}", cli.file);
    };
    let filename = cli.file.to_string_lossy();
    let bytecode = match filename {
        Cow::Borrowed(filename) => grim::assemble(filename, &src, bits, cli.endianness)?,
        Cow::Owned(filename) => grim::assemble(&filename, &src, bits, cli.endianness)?,
    };
    let mut out_file = cli.file;
    if !out_file.set_extension("nvm") {
        out_file = out_file.with_extension("nvm");
    }
    std::fs::write(&out_file, bytecode).expect("failed to write to the output file");
    Ok(())
}
