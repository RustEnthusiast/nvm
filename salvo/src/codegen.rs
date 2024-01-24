use crate::parser::{BlockExpression, Expression, Item, LiteralExpression, Statements};
use core::num::ParseIntError;
use grim::{Bits, Endianness};
use std::{io::Error as IOError, path::Path};
use thiserror::Error;

/// Describes a code generation error.
#[derive(Debug, Error)]
pub(super) enum CodegenError {
    /// Parsing an integer during assembly failed.
    #[error(transparent)]
    ParseIntError(#[from] ParseIntError),
    /// An I/O error occurred.
    #[error(transparent)]
    IOError(#[from] IOError),
}

/// Generates code for the given target.
pub(super) fn gen<'src, I: IntoIterator<Item = Item<'src>>>(
    filename: &str,
    items: I,
) -> Result<(), CodegenError> {
    let path = Path::new(filename);
    let mut asm = String::from("call main\nexit r0\n");
    for item in items {
        match item {
            Item::Fn(f) => match f.block() {
                BlockExpression::Unit => asm.push_str(&format!("{} return\n", f.name())),
                BlockExpression::Statements(Statements::Expression(Expression::Literal(
                    LiteralExpression::Int(expr, radix),
                ))) => {
                    let value = usize::from_str_radix(expr, radix.as_u32())?;
                    asm.push_str(&format!("{}\nmovec r0, {value}\nreturn\n", f.name()));
                }
            },
        }
    }
    let nvm = grim::assemble(filename, &asm, Bits::BitNative, Endianness::Native, 4)?;
    std::fs::write(path.with_extension("nvm"), &nvm)?;
    Ok(())
}
