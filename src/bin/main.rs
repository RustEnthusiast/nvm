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
    clippy::as_conversions,
    clippy::as_underscore,
    clippy::blanket_clippy_restriction_lints,
    clippy::implicit_return,
    clippy::exhaustive_enums,
    clippy::fn_to_numeric_cast_any,
    clippy::missing_inline_in_public_items,
    clippy::mod_module_files,
    clippy::question_mark_used,
    clippy::semicolon_inside_block,
    clippy::semicolon_outside_block,
    clippy::shadow_reuse,
    clippy::shadow_unrelated,
    clippy::std_instead_of_core
)]
mod memory;
use self::memory::Memory;
use nvm::{NvmError, VM};
use std::{io::Error as IoError, num::TryFromIntError};
use thiserror::Error;

/// Describes an error returned from the NVM binary.
#[derive(Debug, Error)]
pub enum ProgramError {
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

/// Main entry point of the program.
fn main() -> Result<(), ProgramError> {
    if let Some(f) = std::env::args_os().nth(1) {
        let mut memory = Memory::new();
        std::process::exit(VM::new().run(&std::fs::read(f)?, &mut memory)?.try_into()?);
    }
    Ok(())
}
