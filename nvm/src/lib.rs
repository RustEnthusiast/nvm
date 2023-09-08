//! A small virtual machine that can be used as a Rust library.
#![cfg_attr(not(any(test, feature = "std")), no_std)]
#![warn(
    future_incompatible,
    let_underscore,
    nonstandard_style,
    rust_2018_compatibility,
    rust_2018_idioms,
    rust_2021_compatibility,
    unused,
    warnings,
    clippy::all,
    clippy::cargo,
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
    clippy::cargo_common_metadata,
    clippy::implicit_return,
    clippy::exhaustive_enums,
    clippy::fn_to_numeric_cast_any,
    clippy::min_ident_chars,
    clippy::missing_inline_in_public_items,
    clippy::mod_module_files,
    clippy::question_mark_used,
    clippy::semicolon_inside_block,
    clippy::semicolon_outside_block,
    clippy::shadow_reuse,
    clippy::shadow_unrelated,
    clippy::single_call_fn,
    clippy::std_instead_of_core
)]
pub mod opcode;
use self::opcode::OpCode;
use bytemuck::NoUninit;
use core::{ffi::FromBytesUntilNulError, num::TryFromIntError, str::Utf8Error};
use num_traits::FromPrimitive;
#[cfg(feature = "std")]
use ::{
    libffi::middle::{Cif, CodePtr, Type},
    libloading::{Error as LibLoadingError, Library},
    std::ffi::CStr,
    thiserror::Error,
};

/// Describes an error returned from the NVM virtual machine.
#[cfg_attr(feature = "std", derive(Debug, Error))]
pub enum NvmError {
    /// An invalid instruction/operation code was encountered.
    #[cfg_attr(
        feature = "std",
        error("an invalid operation code of {0} was encountered")
    )]
    InvalidOperation(u8),
    /// An attempt to read or write to an invalid register was made.
    #[cfg_attr(
        feature = "std",
        error("an attempt was made to access an invalid register at index {0}")
    )]
    InvalidRegister(usize),
    /// A memory driver failed to read from a specific memory location.
    #[cfg_attr(
        feature = "std",
        error("a virtual memory driver failed to read {len} bytes from location {pos}")
    )]
    MemoryReadError { pos: usize, len: usize },
    /// A memory driver failed to write to a specific memory location.
    #[cfg_attr(
        feature = "std",
        error("a virtual memory driver failed to write {len} bytes to location {pos}")
    )]
    MemoryWriteError { pos: usize, len: usize },
    /// A stack memory driver could not be acquired.
    #[cfg_attr(feature = "std", error("a stack memory driver could not be acquired"))]
    GetStackError,
    /// A stack driver failed to read from a specific stack location.
    #[cfg_attr(
        feature = "std",
        error("a virtual stack driver failed to read from location {pos}")
    )]
    StackReadError { pos: usize },
    /// A stack driver failed to write to a specific stack location.
    #[cfg_attr(
        feature = "std",
        error("a virtual stack driver failed to write to location {pos}")
    )]
    StackWriteError { pos: usize },
    /// A syscall's FFI type parameter was invalid.
    #[cfg_attr(
        feature = "std",
        error("a syscall contains an invalid FFI type index parameter {0}")
    )]
    FfiTypeError(usize),
    /// The virtual machine ran into unexpected integer overflow.
    #[cfg_attr(
        feature = "std",
        error("the virtual machine ran into unexpected integer overflow")
    )]
    OverflowError,
    /// The virtual machine encountered an unexpected conversion error.
    #[cfg_attr(feature = "std", error(transparent))]
    TryFromIntError(#[cfg_attr(feature = "std", from)] TryFromIntError),
    /// A C string was expected to end with a null terminating byte but none was found.
    #[cfg_attr(feature = "std", error(transparent))]
    FromBytesUntilNulError(#[cfg_attr(feature = "std", from)] FromBytesUntilNulError),
    /// A string was expected to contain UTF-8 but it's contents are not valid UTF-8.
    #[cfg_attr(feature = "std", error(transparent))]
    Utf8Error(#[cfg_attr(feature = "std", from)] Utf8Error),
    /// An error occurred while attempting to load a library or a library symbol.
    #[cfg(feature = "std")]
    #[cfg_attr(feature = "std", error(transparent))]
    LibLoadingError(#[cfg_attr(feature = "std", from)] LibLoadingError),
}

/// A trait that implementors can use to define the behavior of virtual memory reads and writes.
pub trait MemoryDriver {
    /// Returns an immutable byte slice of the memory driver's buffer.
    fn buffer(&self) -> &[u8];

    /// Reads a value at a specific location in the virtual memory.
    ///
    /// # Errors
    ///
    /// This operation is allowed to fail under any condition.
    fn read<T: Copy>(&self, pos: usize) -> Result<T, NvmError>;

    /// Writes a value to a specific location in the virtual memory.
    ///
    /// # Errors
    ///
    /// This operation is allowed to fail under any condition.
    fn write<T: NoUninit>(&mut self, pos: usize, value: &T) -> Result<(), NvmError>;

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

/// Computes a checked subtraction operation on a [usize].
#[inline]
fn checked_sub(x: usize, y: usize) -> Result<usize, NvmError> {
    x.checked_sub(y).ok_or(NvmError::OverflowError)
}

/// Computes a checked multiplication operation on a [usize].
#[inline]
fn checked_mul(x: usize, y: usize) -> Result<usize, NvmError> {
    x.checked_mul(y).ok_or(NvmError::OverflowError)
}

/// Computes a checked division operation on a [usize].
#[inline]
fn checked_div(x: usize, y: usize) -> Result<usize, NvmError> {
    x.checked_div(y).ok_or(NvmError::OverflowError)
}

/// The NVM virtual machine.
pub struct VM {
    /// The general purpose registers.
    reg: [usize; 6],
}
impl VM {
    /// A constant for indexing the virtual machine's instruction pointer register.
    pub const IP: usize = 4;

    /// A constant for indexing the virtual machine's stack pointer register.
    pub const SP: usize = 5;

    /// Creates a new NVM virtual machine.
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self { reg: [0; 6] }
    }

    /// Returns a copy of a register.
    #[inline]
    fn reg(&self, i: usize) -> Result<usize, NvmError> {
        self.reg.get(i).copied().ok_or(NvmError::InvalidRegister(i))
    }

    /// Returns a mutable reference to a register.
    #[inline]
    fn reg_mut(&mut self, i: usize) -> Result<&mut usize, NvmError> {
        self.reg.get_mut(i).ok_or(NvmError::InvalidRegister(i))
    }

    /// Returns a copy of the instruction pointer.
    #[inline]
    const fn ip(&self) -> usize {
        self.reg[Self::IP]
    }

    /// Returns a mutable reference to the instruction pointer.
    #[inline]
    fn ip_mut(&mut self) -> &mut usize {
        &mut self.reg[Self::IP]
    }

    /// Returns a copy of the stack pointer.
    #[inline]
    const fn sp(&self) -> usize {
        self.reg[Self::SP]
    }

    /// Returns a mutable reference to the stack pointer.
    #[inline]
    fn sp_mut(&mut self) -> &mut usize {
        &mut self.reg[Self::SP]
    }

    /// Pushes a value onto the virtual stack.
    #[inline]
    fn push<T: NoUninit>(
        &mut self,
        memory: &mut impl MemoryDriver,
        value: &T,
    ) -> Result<(), NvmError> {
        memory.write(self.sp(), value)?;
        *self.sp_mut() = checked_add(self.sp(), core::mem::size_of::<T>())?;
        Ok(())
    }

    /// Pops a value off of the virtual stack.
    #[inline]
    fn pop<T: Copy>(&mut self, memory: &mut impl MemoryDriver) -> Result<T, NvmError> {
        *self.sp_mut() = checked_sub(self.sp(), core::mem::size_of::<T>())?;
        memory.read(self.sp())
    }

    /// Runs the NVM bytecode on the virtual machine.
    ///
    /// # Errors
    ///
    /// This operation may return an error at any time while executing NVM bytecode.
    #[allow(clippy::too_many_lines)]
    pub fn run(mut self, code: &[u8], memory: &mut impl MemoryDriver) -> Result<usize, NvmError> {
        memory.write_bytes(0, code)?;
        *self.sp_mut() = code.len();
        loop {
            let ip = self.ip();
            let op = memory.read::<u8>(ip)?;
            let opcode = OpCode::from_u8(op).ok_or(NvmError::InvalidOperation(op))?;
            let mut rp = checked_add(ip, 1)?;
            *self.ip_mut() = checked_add(ip, opcode.size())?;
            match opcode {
                OpCode::Exit => return self.reg(memory.read::<u8>(rp)? as _),
                OpCode::Nop => {}
                OpCode::Jump => *self.ip_mut() = memory.read(rp)?,
                OpCode::Move => {
                    let left = memory.read::<u8>(rp)? as _;
                    rp = checked_add(rp, 1)?;
                    let right = memory.read::<u8>(rp)? as _;
                    *self.reg_mut(left)? = self.reg(right)?;
                }
                OpCode::MoveConst => {
                    let r = self.reg_mut(memory.read::<u8>(rp)? as _)?;
                    rp = checked_add(rp, 1)?;
                    *r = memory.read::<usize>(rp)?;
                }
                OpCode::Load => {
                    let left = memory.read::<u8>(rp)? as _;
                    rp = checked_add(rp, 1)?;
                    let right = memory.read::<u8>(rp)? as _;
                    *self.reg_mut(left)? = memory.read(self.reg(right)?)?;
                }
                OpCode::LoadNum => {
                    let left = memory.read::<u8>(rp)? as _;
                    rp = checked_add(rp, 1)?;
                    let right = memory.read::<u8>(rp)? as _;
                    rp = checked_add(rp, 1)?;
                    let n = memory.read::<u8>(rp)? as usize;
                    let pos = self.reg(right)?;
                    let mem = &memory.buffer()[pos..pos + n];
                    let bytes = bytemuck::bytes_of_mut(self.reg_mut(left)?);
                    #[cfg(target_endian = "little")]
                    {
                        bytes[..n].copy_from_slice(mem);
                        bytes[n..].fill(0);
                    }
                    #[cfg(target_endian = "big")]
                    {
                        let len = bytes.len();
                        bytes[len - n..].copy_from_slice(mem);
                        bytes[..len - n].fill(0);
                    }
                }
                OpCode::Store => {
                    let left = memory.read::<u8>(rp)? as _;
                    rp = checked_add(rp, 1)?;
                    let right = memory.read::<u8>(rp)? as _;
                    memory.write(self.reg(left)?, &self.reg(right)?)?;
                }
                OpCode::StoreNum => {
                    let left = memory.read::<u8>(rp)? as _;
                    rp = checked_add(rp, 1)?;
                    let right = memory.read::<u8>(rp)? as _;
                    rp = checked_add(rp, 1)?;
                    let n = memory.read::<u8>(rp)? as usize;
                    let bytes = self.reg(right)?.to_ne_bytes();
                    #[cfg(target_endian = "little")]
                    memory.write_bytes(self.reg(left)?, &bytes[..n])?;
                    #[cfg(target_endian = "big")]
                    memory.write_bytes(self.reg(left)?, &bytes[bytes.len() - n..])?;
                }
                OpCode::Push => self.push(memory, &self.reg(memory.read::<u8>(rp)? as _)?)?,
                OpCode::Pop => *self.reg_mut(memory.read::<u8>(rp)? as _)? = self.pop(memory)?,
                OpCode::Add => {
                    let left = memory.read::<u8>(rp)? as _;
                    rp = checked_add(rp, 1)?;
                    let right = self.reg(memory.read::<u8>(rp)? as _)?;
                    let left = self.reg_mut(left)?;
                    *left = checked_add(*left, right)?;
                }
                OpCode::Sub => {
                    let left = memory.read::<u8>(rp)? as _;
                    rp = checked_add(rp, 1)?;
                    let right = self.reg(memory.read::<u8>(rp)? as _)?;
                    let left = self.reg_mut(left)?;
                    *left = checked_sub(*left, right)?;
                }
                OpCode::Mul => {
                    let left = memory.read::<u8>(rp)? as _;
                    rp = checked_add(rp, 1)?;
                    let right = self.reg(memory.read::<u8>(rp)? as _)?;
                    let left = self.reg_mut(left)?;
                    *left = checked_mul(*left, right)?;
                }
                OpCode::Div => {
                    let left = memory.read::<u8>(rp)? as _;
                    rp = checked_add(rp, 1)?;
                    let right = self.reg(memory.read::<u8>(rp)? as _)?;
                    let left = self.reg_mut(left)?;
                    *left = checked_div(*left, right)?;
                }
                OpCode::LoadLib => {
                    #[cfg(feature = "std")]
                    {
                        let r = memory.read::<u8>(rp)? as _;
                        let pos = self.reg(r)?;
                        let name = memory
                            .buffer()
                            .get(pos..)
                            .ok_or(NvmError::MemoryReadError { pos, len: 0 })?;
                        let name = CStr::from_bytes_until_nul(name)?;
                        // SAFETY: The safety of this operation is documented by it's `Op`.
                        let lib = unsafe { Box::into_raw(Box::new(Library::new(name.to_str()?)?)) };
                        *self.reg_mut(r)? = lib as _;
                    }
                }
                OpCode::LoadSym => {
                    #[cfg(feature = "std")]
                    {
                        let left = memory.read::<u8>(rp)? as _;
                        rp = checked_add(rp, 1)?;
                        let right = self.reg(memory.read::<u8>(rp)? as _)?;
                        // SAFETY: The safety of this operation is documented by it's `Op`.
                        let lib = unsafe { &*(right as *const Library) };
                        let pos = self.reg(left)?;
                        let name = memory
                            .buffer()
                            .get(pos..)
                            .ok_or(NvmError::MemoryReadError { pos, len: 0 })?;
                        let name = CStr::from_bytes_until_nul(name)?;
                        // SAFETY: We're using an opaque function pointer.
                        let sym = unsafe { lib.get::<fn()>(name.to_bytes())? };
                        *self.reg_mut(left)? = *sym as _;
                    }
                }
                OpCode::Syscall => {
                    #[cfg(feature = "std")]
                    {
                        let left = self.reg(memory.read::<u8>(rp)? as _)?;
                        rp = checked_add(rp, 1)?;
                        let right = self.reg(memory.read::<u8>(rp)? as _)?;
                        let mut types = Vec::new();
                        let mut args = Vec::new();
                        for _ in 0..right {
                            match self.pop::<usize>(memory)? {
                                0 => {
                                    types.push(Type::usize());
                                    let arg = self.pop::<usize>(memory)?;
                                    args.push(libffi::middle::arg(&arg));
                                }
                                t => return Err(NvmError::FfiTypeError(t)),
                            }
                        }
                        let cif = Cif::new(types, Type::void());
                        // SAFETY: The safety of this operation is documented by it's `Op`.
                        unsafe { cif.call::<()>(CodePtr(left as _), &args) };
                    }
                }
                OpCode::FreeLib => {
                    #[cfg(feature = "std")]
                    {
                        let r = self.reg(memory.read::<u8>(rp)? as _)?;
                        // SAFETY: The safety of this operation is documented by it's `Op`.
                        unsafe {
                            drop(Box::from_raw(r as *mut Library));
                        }
                    }
                }
            }
        }
    }
}
