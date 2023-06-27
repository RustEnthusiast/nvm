//! A small virtual machine that can be used as a Rust library.
#![cfg_attr(not(any(test, feature = "bin")), no_std)]
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
    clippy::missing_inline_in_public_items,
    clippy::mod_module_files,
    clippy::question_mark_used,
    clippy::semicolon_outside_block,
    clippy::shadow_reuse
)]
#![cfg_attr(feature = "bin", allow(clippy::std_instead_of_core))]
pub mod opcode;
use self::opcode::OpCode;
use core::num::TryFromIntError;
#[cfg(feature = "bin")]
use thiserror::Error;

/// Describes an error returned from the NVM virtual machine.
#[cfg_attr(feature = "bin", derive(Debug, Error))]
pub enum NvmError {
    /// An invalid instruction/operation code was encountered.
    #[cfg_attr(
        feature = "bin",
        error("an invalid operation code of {0} was encountered")
    )]
    InvalidOperation(u8),
    /// An attempt to read or write to an invalid register was made.
    #[cfg_attr(
        feature = "bin",
        error("an attempt was made to access an invalid register at index {0}")
    )]
    InvalidRegister(usize),
    /// A memory driver failed to read from a specific memory location.
    #[cfg_attr(
        feature = "bin",
        error("a virtual memory driver failed to read {len} bytes from location {pos}")
    )]
    MemoryReadError { pos: usize, len: usize },
    /// A memory driver failed to write to a specific memory location.
    #[cfg_attr(
        feature = "bin",
        error("a virtual memory driver failed to write {len} bytes to location {pos}")
    )]
    MemoryWriteError { pos: usize, len: usize },
    /// The virtual machine ran into unexpected integer overflow.
    #[cfg_attr(
        feature = "bin",
        error("the virtual machine ran into unexpected integer overflow")
    )]
    OverflowError,
    /// The virtual machine encountered an unexpected conversion error.
    #[cfg_attr(feature = "bin", error(transparent))]
    TryFromIntError(#[cfg_attr(feature = "bin", from)] TryFromIntError),
}

/// A trait that implementors can use to define the behavior of virtual memory reads and writes.
pub trait MemoryDriver {
    /// Reads a value at a specific location in the virtual memory.
    ///
    /// # Errors
    ///
    /// This operation is allowed to fail under any condition.
    fn read<T: Copy>(&self, pos: usize) -> Result<T, NvmError>;

    /// Writes a slice of bytes to this memory at offset `pos`.
    ///
    /// # Errors
    ///
    /// This operation is allowed to fail under any condition.
    fn write_bytes(&mut self, pos: usize, buffer: &[u8]) -> Result<(), NvmError>;
}

/// Computes a checked addition operation on a [usize].
#[inline]
fn checked_add(x: usize, y: usize) -> Result<usize, NvmError> {
    x.checked_add(y).ok_or(NvmError::OverflowError)
}

/// The NVM virtual machine.
pub struct VM {
    /// The instruction pointer.
    ip: usize,
    /// The general purpose registers.
    gpr: [usize; 4],
}
impl VM {
    /// Creates a new NVM virtual machine.
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self { ip: 0, gpr: [0; 4] }
    }

    /// Returns a mutable reference to a general purpose register.
    #[inline]
    fn gpr(&mut self, i: usize) -> Result<&mut usize, NvmError> {
        self.gpr.get_mut(i).ok_or(NvmError::InvalidRegister(i))
    }

    /// Runs the NVM bytecode on the virtual machine.
    ///
    /// # Errors
    ///
    /// This operation may return an error at any time while executing NVM bytecode.
    pub fn run<MD: MemoryDriver>(mut self, code: &[u8], memory: &mut MD) -> Result<(), NvmError> {
        memory.write_bytes(0, code)?;
        while let Ok(opcode) = memory.read::<u8>(self.ip) {
            let opcode: OpCode = opcode.try_into()?;
            let mut rp = checked_add(self.ip, 1)?;
            self.ip = checked_add(self.ip, opcode.size())?;
            match opcode {
                OpCode::Exit => break,
                OpCode::Nop => {}
                OpCode::Move => {
                    let left = memory.read::<u8>(rp)? as _;
                    rp = checked_add(rp, 1)?;
                    let right = memory.read::<u8>(rp)? as _;
                    *self.gpr(left)? = *self.gpr(right)?;
                }
                OpCode::MoveConst => {
                    let r = memory.read::<u8>(rp)? as _;
                    rp = checked_add(rp, 1)?;
                    *self.gpr(r)? = memory.read::<usize>(rp)?;
                }
            }
        }
        Ok(())
    }
}
