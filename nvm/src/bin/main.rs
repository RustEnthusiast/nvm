//! A small but capable virtual machine written in Rust.
#![warn(
    clippy::complexity,
    clippy::correctness,
    clippy::nursery,
    clippy::pedantic,
    clippy::perf,
    clippy::restriction,
    clippy::style,
    clippy::suspicious
)]
#![allow(
    clippy::absolute_paths,
    clippy::as_conversions,
    clippy::as_underscore,
    clippy::blanket_clippy_restriction_lints,
    clippy::implicit_return,
    clippy::exhaustive_enums,
    clippy::fn_to_numeric_cast_any,
    clippy::min_ident_chars,
    clippy::missing_inline_in_public_items,
    clippy::mod_module_files,
    clippy::panic,
    clippy::panic_in_result_fn,
    clippy::question_mark_used,
    clippy::semicolon_inside_block,
    clippy::semicolon_outside_block,
    clippy::shadow_reuse,
    clippy::shadow_unrelated,
    clippy::single_call_fn,
    clippy::std_instead_of_core,
    clippy::useless_conversion
)]
mod memory;
use self::{constants::REG_COUNT, memory::Memory};
use nvm::{NvmError, VM};
use std::{convert::Infallible, io::Error as IoError, num::TryFromIntError};
use thiserror::Error;

/// Describes an error returned from the NVM binary.
#[derive(Debug, Error)]
pub enum ProgramError {
    /// An error that can never occur.
    #[error(transparent)]
    Infallible(#[from] Infallible),
    /// An I/O operation failed.
    #[error(transparent)]
    IoError(#[from] IoError),
    /// The virtual machine encountered an error.
    #[error(transparent)]
    NvmError(#[from] NvmError),
    /// An unexpected conversion error occurred.
    #[error(transparent)]
    TryFromIntError(#[from] TryFromIntError),
}

/// Compile time constants.
#[allow(clippy::missing_docs_in_private_items)]
mod constants {
    use build_const::build_const;

    build_const!("bin_constants");
}

/// Main entry point of the program.
fn main() -> Result<(), ProgramError> {
    if let Some(f) = std::env::args_os().nth(1) {
        let mut memory = Memory::new();
        let mut vm = VM::<REG_COUNT>::new()?;
        match vm.run(&std::fs::read(f)?, &mut memory) {
            Ok(code) => std::process::exit(code.try_into()?),
            Err(err) => panic!("error: {err}\nvirtual machine state: {vm:?}"),
        }
    }
    Ok(())
}
