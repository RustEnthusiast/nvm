mod codegen;
mod lexer;
mod parser;
use ariadne::{Label, Report, ReportKind, Source};
use core::{num::ParseIntError, ops::Range};

/// An enumeration describing the target bit width.
#[derive(Clone, Copy)]
pub enum Bits {
    /// A host-native-bit VM.
    BitNative,
    /// An 8-bit VM.
    Bit8,
    /// A 16-bit VM.
    Bit16,
    /// A 32-bit VM.
    Bit32,
    /// A 64-bit VM.
    Bit64,
    /// A 128-bit VM.
    Bit128,
}
impl Bits {
    /// Returns the number of bytes required for this number of bits.
    #[inline]
    const fn size(self) -> usize {
        match self {
            Self::BitNative => core::mem::size_of::<usize>(),
            Self::Bit8 => 1,
            Self::Bit16 => 2,
            Self::Bit32 => 4,
            Self::Bit64 => 8,
            Self::Bit128 => 16,
        }
    }
}

/// Assembles Grim source code.
pub fn assemble(filename: &str, src: &str, bits: Bits) -> Result<Vec<u8>, ParseIntError> {
    let tokens = lexer::lex(filename, src);
    let (items, locations) = parser::parse(filename, src, tokens.iter(), bits)?;
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
    std::process::exit(101);
}
