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

/// Represents an NVM operation code.
#[repr(u8)]
pub enum OpCode {
    /// Exit operation.
    Exit,
    /// No operation.
    Nop,
    /// A move constant operation.
    MoveConst,
}
impl OpCode {
    /// [u8] constant for exit.
    pub const EXIT: u8 = Self::Exit as _;
    /// [u8] constant for no operation.
    pub const NOP: u8 = Self::Nop as _;
    /// [u8] constant for move constant.
    pub const MOVE_CONST: u8 = Self::MoveConst as _;

    /// Returns the size of this opcode's instruction.
    #[allow(clippy::arithmetic_side_effects, clippy::integer_arithmetic)]
    const fn size(&self) -> usize {
        match *self {
            Self::Exit | Self::Nop => 1,
            Self::MoveConst => 2 + core::mem::size_of::<usize>(),
        }
    }
}
impl TryFrom<u8> for OpCode {
    /// The [Err] type returned from this trait's method.
    type Error = NvmError;

    /// Converts a [u8] into an [`OpCode`].
    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            Self::EXIT => Ok(Self::Exit),
            Self::NOP => Ok(Self::Nop),
            Self::MOVE_CONST => Ok(Self::MoveConst),
            _ => Err(NvmError::InvalidOperation(value)),
        }
    }
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

    /// Runs the NVM bytecode on the virtual machine.
    ///
    /// # Errors
    ///
    /// This operation may return an error at any time while executing NVM bytecode.
    pub fn run<MD: MemoryDriver>(mut self, code: &[u8], memory: &mut MD) -> Result<(), NvmError> {
        memory.write_bytes(0, code)?;
        while let Ok(opcode) = memory.read::<u8>(self.ip) {
            let opcode: OpCode = opcode.try_into()?;
            self.ip = match self.ip.checked_add(opcode.size()) {
                Some(ip) => ip,
                _ => return Err(NvmError::OverflowError),
            };
            match opcode {
                OpCode::Exit => break,
                OpCode::Nop => {}
                OpCode::MoveConst => {
                    let mut rp = match self.ip.checked_sub(self.ip) {
                        Some(rp) => match rp.checked_add(1) {
                            Some(rp) => rp,
                            _ => return Err(NvmError::OverflowError),
                        },
                        _ => return Err(NvmError::OverflowError),
                    };
                    let r = memory.read::<u8>(rp)? as _;
                    rp = match rp.checked_add(1) {
                        Some(rp) => rp,
                        _ => return Err(NvmError::OverflowError),
                    };
                    let value = memory.read::<usize>(rp)?;
                    match self.gpr.get_mut(r) {
                        Some(gpr) => *gpr = value,
                        _ => return Err(NvmError::InvalidRegister(r)),
                    }
                }
            }
        }
        Ok(())
    }
}
