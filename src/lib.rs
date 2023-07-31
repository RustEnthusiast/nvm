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
    clippy::missing_inline_in_public_items,
    clippy::mod_module_files,
    clippy::question_mark_used,
    clippy::semicolon_inside_block,
    clippy::semicolon_outside_block,
    clippy::shadow_reuse,
    clippy::shadow_unrelated,
    clippy::std_instead_of_core
)]
pub mod opcode;
use self::opcode::OpCode;
use core::{ffi::FromBytesUntilNulError, num::TryFromIntError, str::Utf8Error};
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
    /// The memory driver's stack driver type.
    type StackDriver<'stack>: StackDriver
    where
        Self: 'stack;

    /// Returns an immutable byte slice of the memory driver's buffer.
    fn buffer(&self) -> &[u8];

    /// Returns the stack memory driver.
    ///
    /// # Errors
    ///
    /// This operation is allowed to fail under any condition.
    fn stack_driver(&mut self) -> Result<Self::StackDriver<'_>, NvmError>;

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

/// A trait that implementors can use to define the behavior of virtual stack memory reads and
/// writes.
pub trait StackDriver {
    /// Reads a [usize] value from a specific location in the virtual stack.
    ///
    /// # Errors
    ///
    /// This operation is allowed to fail under any condition.
    fn read(&self, pos: usize) -> Result<usize, NvmError>;

    /// Writes a [usize] value to a specific location in the virtual stack.
    ///
    /// # Errors
    ///
    /// This operation is allowed to fail under any condition.
    fn write(&mut self, pos: usize, value: usize) -> Result<(), NvmError>;
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
    /// The instruction pointer.
    ip: usize,
    /// The stack pointer.
    sp: usize,
    /// The general purpose registers.
    gpr: [usize; 4],
}
impl VM {
    /// Creates a new NVM virtual machine.
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self {
            ip: 0,
            sp: 0,
            gpr: [0; 4],
        }
    }

    /// Returns an immutable reference to a general purpose register.
    #[inline]
    fn gpr(&self, i: usize) -> Result<&usize, NvmError> {
        self.gpr.get(i).ok_or(NvmError::InvalidRegister(i))
    }

    /// Returns a mutable reference to a general purpose register.
    #[inline]
    fn gpr_mut(&mut self, i: usize) -> Result<&mut usize, NvmError> {
        self.gpr.get_mut(i).ok_or(NvmError::InvalidRegister(i))
    }

    /// Runs the NVM bytecode on the virtual machine.
    ///
    /// # Errors
    ///
    /// This operation may return an error at any time while executing NVM bytecode.
    #[allow(clippy::too_many_lines)]
    pub fn run(mut self, code: &[u8], memory: &mut impl MemoryDriver) -> Result<usize, NvmError> {
        memory.write_bytes(0, code)?;
        loop {
            let opcode: OpCode = memory.read::<u8>(self.ip)?.try_into()?;
            let mut rp = checked_add(self.ip, 1)?;
            self.ip = checked_add(self.ip, opcode.size())?;
            match opcode {
                OpCode::Exit => return Ok(*self.gpr(0)?),
                OpCode::Nop => {}
                OpCode::Jump => self.ip = *self.gpr(memory.read::<u8>(rp)? as _)?,
                OpCode::Move => {
                    let left = memory.read::<u8>(rp)? as _;
                    rp = checked_add(rp, 1)?;
                    let right = memory.read::<u8>(rp)? as _;
                    *self.gpr_mut(left)? = *self.gpr(right)?;
                }
                OpCode::MoveConst => {
                    let r = self.gpr_mut(memory.read::<u8>(rp)? as _)?;
                    rp = checked_add(rp, 1)?;
                    *r = memory.read::<usize>(rp)?;
                }
                OpCode::Push => {
                    let value = *self.gpr(memory.read::<u8>(rp)? as _)?;
                    memory.stack_driver()?.write(self.sp, value)?;
                    self.sp = checked_add(self.sp, core::mem::size_of::<usize>())?;
                }
                OpCode::PushConst => {
                    let value = memory.read::<usize>(rp)?;
                    memory.stack_driver()?.write(self.sp, value)?;
                    self.sp = checked_add(self.sp, core::mem::size_of::<usize>())?;
                }
                OpCode::Pop => {
                    let sp = self.sp;
                    let r = self.gpr_mut(memory.read::<u8>(rp)? as _)?;
                    *r = memory.stack_driver()?.read(sp)?;
                    self.sp = checked_sub(sp, core::mem::size_of::<usize>())?;
                }
                OpCode::Add => {
                    let left = memory.read::<u8>(rp)? as _;
                    rp = checked_add(rp, 1)?;
                    let right = *self.gpr(memory.read::<u8>(rp)? as _)?;
                    let left = self.gpr_mut(left)?;
                    *left = checked_add(*left, right)?;
                }
                OpCode::AddConst => {
                    let r = self.gpr_mut(memory.read::<u8>(rp)? as _)?;
                    rp = checked_add(rp, 1)?;
                    *r = checked_add(*r, memory.read::<usize>(rp)?)?;
                }
                OpCode::Sub => {
                    let left = memory.read::<u8>(rp)? as _;
                    rp = checked_add(rp, 1)?;
                    let right = *self.gpr(memory.read::<u8>(rp)? as _)?;
                    let left = self.gpr_mut(left)?;
                    *left = checked_sub(*left, right)?;
                }
                OpCode::SubConst => {
                    let r = self.gpr_mut(memory.read::<u8>(rp)? as _)?;
                    rp = checked_add(rp, 1)?;
                    *r = checked_sub(*r, memory.read::<usize>(rp)?)?;
                }
                OpCode::Mul => {
                    let left = memory.read::<u8>(rp)? as _;
                    rp = checked_add(rp, 1)?;
                    let right = *self.gpr(memory.read::<u8>(rp)? as _)?;
                    let left = self.gpr_mut(left)?;
                    *left = checked_mul(*left, right)?;
                }
                OpCode::MulConst => {
                    let r = self.gpr_mut(memory.read::<u8>(rp)? as _)?;
                    rp = checked_add(rp, 1)?;
                    *r = checked_mul(*r, memory.read::<usize>(rp)?)?;
                }
                OpCode::Div => {
                    let left = memory.read::<u8>(rp)? as _;
                    rp = checked_add(rp, 1)?;
                    let right = *self.gpr(memory.read::<u8>(rp)? as _)?;
                    let left = self.gpr_mut(left)?;
                    *left = checked_div(*left, right)?;
                }
                OpCode::DivConst => {
                    let r = self.gpr_mut(memory.read::<u8>(rp)? as _)?;
                    rp = checked_add(rp, 1)?;
                    *r = checked_div(*r, memory.read::<usize>(rp)?)?;
                }
                OpCode::LoadLib => {
                    #[cfg(feature = "std")]
                    {
                        let pos = *self.gpr(0)?;
                        let name = memory
                            .buffer()
                            .get(pos..)
                            .ok_or(NvmError::MemoryReadError { pos, len: 0 })?;
                        let name = CStr::from_bytes_until_nul(name)?;
                        // SAFETY: The safety of this operation is documented by it's `Op`.
                        let lib = unsafe { Box::into_raw(Box::new(Library::new(name.to_str()?)?)) };
                        *self.gpr_mut(0)? = lib as _;
                    }
                }
                OpCode::LoadSym => {
                    #[cfg(feature = "std")]
                    {
                        // SAFETY: The safety of this operation is documented by it's `Op`.
                        let lib = unsafe { &*(*self.gpr(0)? as *const Library) };
                        let pos = *self.gpr(1)?;
                        let name = memory
                            .buffer()
                            .get(pos..)
                            .ok_or(NvmError::MemoryReadError { pos, len: 0 })?;
                        let name = CStr::from_bytes_until_nul(name)?;
                        // SAFETY: We're using an opaque function pointer.
                        let sym = unsafe { lib.get::<fn()>(name.to_bytes())? };
                        *self.gpr_mut(0)? = *sym as _;
                    }
                }
                OpCode::Syscall => {
                    #[cfg(feature = "std")]
                    {
                        let mut types = Vec::new();
                        let mut args = Vec::new();
                        let stack_driver = memory.stack_driver()?;
                        for _ in 0..*self.gpr(1)? {
                            match stack_driver.read(self.sp)? {
                                0 => {
                                    types.push(Type::usize());
                                    self.sp = checked_sub(self.sp, core::mem::size_of::<usize>())?;
                                    args.push(libffi::middle::arg(&stack_driver.read(self.sp)?));
                                }
                                t => return Err(NvmError::FfiTypeError(t)),
                            }
                        }
                        let cif = Cif::new(types, Type::void());
                        // SAFETY: The safety of this operation is documented by it's `Op`.
                        unsafe { cif.call::<()>(CodePtr(*self.gpr(0)? as _), &args) };
                    }
                }
                OpCode::FreeLib => {
                    #[cfg(feature = "std")]
                    {
                        // SAFETY: The safety of this operation is documented by it's `Op`.
                        unsafe {
                            drop(Box::from_raw((*self.gpr(0)?) as *mut Library));
                        }
                    }
                }
            }
        }
    }
}
