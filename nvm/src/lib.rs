//! A small virtual machine that can be used as a Rust library.
#![cfg_attr(not(any(test, feature = "std")), no_std)]
#![warn(
    deprecated_in_future,
    ffi_unwind_calls,
    future_incompatible,
    invalid_reference_casting,
    let_underscore,
    macro_use_extern_crate,
    meta_variable_misuse,
    missing_abi,
    missing_copy_implementations,
    missing_debug_implementations,
    missing_docs,
    non_ascii_idents,
    nonstandard_style,
    noop_method_call,
    rust_2018_compatibility,
    rust_2018_idioms,
    rust_2021_compatibility,
    single_use_lifetimes,
    trivial_casts,
    trivial_numeric_casts,
    unreachable_pub,
    unsafe_op_in_unsafe_fn,
    unused,
    unused_crate_dependencies,
    unused_import_braces,
    unused_lifetimes,
    unused_qualifications,
    unused_results,
    unused_tuple_struct_fields,
    variant_size_differences,
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
    clippy::cognitive_complexity,
    clippy::default_numeric_fallback,
    clippy::host_endian_bytes,
    clippy::implicit_return,
    clippy::exhaustive_enums,
    clippy::fn_to_numeric_cast_any,
    clippy::match_bool,
    clippy::min_ident_chars,
    clippy::missing_inline_in_public_items,
    clippy::mod_module_files,
    clippy::must_use_candidate,
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
    core::{ffi::CStr, mem::MaybeUninit, ptr::addr_of_mut},
    libffi::{
        middle::Type,
        raw::{ffi_abi_FFI_DEFAULT_ABI, ffi_status_FFI_OK},
    },
    libloading::{Error as LibLoadingError, Library},
    std::{
        borrow::Cow,
        env::consts::{DLL_EXTENSION, DLL_PREFIX, DLL_SUFFIX},
        path::PathBuf,
    },
    thiserror::Error,
};

/// Describes an error returned from the NVM virtual machine.
#[derive(Debug)]
#[cfg_attr(feature = "std", derive(Error))]
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
    /// Reading from a register failed.
    #[cfg_attr(feature = "std", error("reading from a register failed"))]
    RegisterReadError,
    /// Writing to a register failed.
    #[cfg_attr(feature = "std", error("writing to a register failed"))]
    RegisterWriteError,
    /// A memory driver failed to read from a specific memory location.
    #[cfg_attr(
        feature = "std",
        error("a virtual memory driver failed to read {len} bytes from location {pos}")
    )]
    MemoryReadError {
        /// The memory position of the read.
        pos: usize,
        /// The attempted number of bytes to read.
        len: usize,
    },
    /// A memory driver failed to write to a specific memory location.
    #[cfg_attr(
        feature = "std",
        error("a virtual memory driver failed to write {len} bytes to location {pos}")
    )]
    MemoryWriteError {
        /// The memory position of the read.
        pos: usize,
        /// The attempted number of bytes to read.
        len: usize,
    },
    /// A syscall's FFI type parameter was invalid.
    #[cfg_attr(
        feature = "std",
        error("a syscall contains an invalid FFI type index parameter {0}")
    )]
    FfiTypeError(u8),
    /// A CIF was unable to be constructed.
    #[cfg_attr(feature = "std", error("a CIF was unable to be constructed"))]
    FfiCifError,
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

    /// Returns a mutable byte slice of the memory driver's buffer.
    fn buffer_mut(&mut self) -> &mut [u8];

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

/// Describes the flags register.
enum Flags {
    /// Indicates a zero result.
    Zero = 1,
    /// Indicates an unsigned overflow.
    Carry = 1 << 1,
    /// Indicates a signed overflow.
    Overflow = 1 << 2,
    /// Indicates a signed result.
    Sign = 1 << 3,
}

/// Computes a checked negation operation on an [isize].
#[inline]
fn checked_neg(x: isize) -> Result<isize, NvmError> {
    x.checked_neg().ok_or(NvmError::OverflowError)
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
#[derive(Clone, Copy, Debug)]
pub struct VM {
    /// The general purpose registers.
    reg: [usize; 7],
}
impl VM {
    /// A constant for indexing the virtual machine's instruction pointer register.
    pub const IP: usize = 4;

    /// A constant for indexing the virtual machine's stack pointer register.
    pub const SP: usize = 5;

    /// A constant for indexing the virtual machine's flags register.
    pub const FLAGS: usize = 6;

    /// Creates a new NVM virtual machine.
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self { reg: [0; 7] }
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

    /// Returns a copy of the flags register.
    #[inline]
    const fn flags(&self) -> usize {
        self.reg[Self::FLAGS]
    }

    /// Returns a mutable reference to the flags register.
    #[inline]
    fn flags_mut(&mut self) -> &mut usize {
        &mut self.reg[Self::FLAGS]
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
    fn pop<T: Copy>(&mut self, memory: &impl MemoryDriver) -> Result<T, NvmError> {
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
            let mut ip = self.ip();
            let op = memory.read::<u8>(ip)?;
            let opcode = OpCode::from_u8(op).ok_or(NvmError::InvalidOperation(op))?;
            *self.ip_mut() = checked_add(ip, opcode.size())?;
            match opcode {
                OpCode::Exit => return self.reg(memory.read::<u8>(checked_add(ip, 1)?)? as _),
                OpCode::Nop => {}
                OpCode::Move => {
                    ip = checked_add(ip, 1)?;
                    let left = memory.read::<u8>(ip)? as _;
                    let right = memory.read::<u8>(checked_add(ip, 1)?)? as _;
                    *self.reg_mut(left)? = self.reg(right)?;
                }
                OpCode::MoveConst => {
                    ip = checked_add(ip, 1)?;
                    let r = self.reg_mut(memory.read::<u8>(ip)? as _)?;
                    *r = memory.read::<usize>(checked_add(ip, 1)?)?;
                }
                OpCode::Load => {
                    ip = checked_add(ip, 1)?;
                    let left = memory.read::<u8>(ip)? as _;
                    let right = memory.read::<u8>(checked_add(ip, 1)?)? as _;
                    *self.reg_mut(left)? = memory.read(self.reg(right)?)?;
                }
                OpCode::LoadNum => {
                    ip = checked_add(ip, 1)?;
                    let left = memory.read::<u8>(ip)? as _;
                    ip = checked_add(ip, 1)?;
                    let right = memory.read::<u8>(ip)? as _;
                    let n = memory.read::<u8>(checked_add(ip, 1)?)? as usize;
                    let pos = self.reg(right)?;
                    let Some(mem) = memory.buffer().get(pos..checked_add(pos, n)?) else {
                        return Err(NvmError::MemoryReadError { pos, len: n });
                    };
                    let bytes = bytemuck::bytes_of_mut(self.reg_mut(left)?);
                    #[cfg(target_endian = "little")]
                    {
                        match bytes.get_mut(..n) {
                            Some(bytes) => bytes.copy_from_slice(mem),
                            _ => return Err(NvmError::RegisterWriteError),
                        }
                        match bytes.get_mut(n..) {
                            Some(bytes) => bytes.fill(0),
                            _ => return Err(NvmError::RegisterWriteError),
                        }
                    }
                    #[cfg(target_endian = "big")]
                    {
                        let len = bytes.len();
                        match bytes.get_mut(len - n..) {
                            Some(bytes) => bytes.copy_from_slice(mem),
                            _ => return Err(NvmError::RegisterWriteError),
                        }
                        match bytes.get_mut(..len - n) {
                            Some(bytes) => bytes.fill(0),
                            _ => return Err(NvmError::RegisterWriteError),
                        }
                    }
                }
                OpCode::Store => {
                    ip = checked_add(ip, 1)?;
                    let left = memory.read::<u8>(ip)? as _;
                    let right = memory.read::<u8>(checked_add(ip, 1)?)? as _;
                    memory.write(self.reg(left)?, &self.reg(right)?)?;
                }
                OpCode::StoreNum => {
                    ip = checked_add(ip, 1)?;
                    let left = memory.read::<u8>(ip)? as _;
                    ip = checked_add(ip, 1)?;
                    let right = memory.read::<u8>(ip)? as _;
                    let n = memory.read::<u8>(checked_add(ip, 1)?)? as usize;
                    let bytes = self.reg(right)?.to_ne_bytes();
                    #[cfg(target_endian = "little")]
                    let Some(bytes) = bytes.get(..n) else {
                        return Err(NvmError::RegisterReadError);
                    };
                    #[cfg(target_endian = "big")]
                    let Some(bytes) = bytes.get(bytes.len() - n..) else {
                        return Err(NvmError::RegisterReadError);
                    };
                    memory.write_bytes(self.reg(left)?, bytes)?;
                }
                OpCode::Push => {
                    let r = memory.read::<u8>(checked_add(ip, 1)?)? as _;
                    self.push(memory, &self.reg(r)?)?;
                }
                OpCode::PushNum => {
                    ip = checked_add(ip, 1)?;
                    let r = memory.read::<u8>(ip)? as _;
                    let n = memory.read::<u8>(checked_add(ip, 1)?)? as usize;
                    let bytes = self.reg(r)?.to_ne_bytes();
                    #[cfg(target_endian = "little")]
                    let Some(bytes) = bytes.get(..n) else {
                        return Err(NvmError::RegisterReadError);
                    };
                    #[cfg(target_endian = "big")]
                    let Some(bytes) = bytes.get(bytes.len() - n..) else {
                        return Err(NvmError::RegisterReadError);
                    };
                    memory.write_bytes(self.sp(), bytes)?;
                    *self.sp_mut() = checked_add(self.sp(), n)?;
                }
                OpCode::Pop => {
                    let r = memory.read::<u8>(checked_add(ip, 1)?)? as _;
                    *self.reg_mut(r)? = self.pop(memory)?;
                }
                OpCode::PopNum => {
                    ip = checked_add(ip, 1)?;
                    let left = memory.read::<u8>(ip)? as _;
                    let n = memory.read::<u8>(checked_add(ip, 1)?)? as usize;
                    let pos = checked_sub(self.sp(), n)?;
                    let Some(mem) = memory.buffer().get(pos..self.sp()) else {
                        return Err(NvmError::MemoryReadError { pos, len: n });
                    };
                    let bytes = bytemuck::bytes_of_mut(self.reg_mut(left)?);
                    #[cfg(target_endian = "little")]
                    {
                        match bytes.get_mut(..n) {
                            Some(bytes) => bytes.copy_from_slice(mem),
                            _ => return Err(NvmError::RegisterWriteError),
                        }
                        match bytes.get_mut(n..) {
                            Some(bytes) => bytes.fill(0),
                            _ => return Err(NvmError::RegisterWriteError),
                        }
                    }
                    #[cfg(target_endian = "big")]
                    {
                        let len = bytes.len();
                        match bytes.get_mut(len - n..) {
                            Some(bytes) => bytes.copy_from_slice(mem),
                            _ => return Err(NvmError::RegisterWriteError),
                        }
                        match bytes.get_mut(..len - n) {
                            Some(bytes) => bytes.fill(0),
                            _ => return Err(NvmError::RegisterWriteError),
                        }
                    }
                    *self.sp_mut() = checked_sub(self.sp(), n)?;
                }
                OpCode::Neg => {
                    let r = self.reg_mut(memory.read::<u8>(checked_add(ip, 1)?)? as _)?;
                    *r = checked_neg(*r as _)? as _;
                }
                OpCode::Add => {
                    ip = checked_add(ip, 1)?;
                    let left = memory.read::<u8>(ip)? as _;
                    let right = self.reg(memory.read::<u8>(checked_add(ip, 1)?)? as _)?;
                    let left = self.reg_mut(left)?;
                    *left = checked_add(*left, right)?;
                }
                OpCode::Sub => {
                    ip = checked_add(ip, 1)?;
                    let left = memory.read::<u8>(ip)? as _;
                    let right = self.reg(memory.read::<u8>(checked_add(ip, 1)?)? as _)?;
                    let left = self.reg_mut(left)?;
                    *left = checked_sub(*left, right)?;
                }
                OpCode::Mul => {
                    ip = checked_add(ip, 1)?;
                    let left = memory.read::<u8>(ip)? as _;
                    let right = self.reg(memory.read::<u8>(checked_add(ip, 1)?)? as _)?;
                    let left = self.reg_mut(left)?;
                    *left = checked_mul(*left, right)?;
                }
                OpCode::Div => {
                    ip = checked_add(ip, 1)?;
                    let left = memory.read::<u8>(ip)? as _;
                    let right = self.reg(memory.read::<u8>(checked_add(ip, 1)?)? as _)?;
                    let left = self.reg_mut(left)?;
                    *left = checked_div(*left, right)?;
                }
                OpCode::Not => {
                    let r = self.reg_mut(memory.read::<u8>(checked_add(ip, 1)?)? as _)?;
                    *r = !*r;
                }
                OpCode::And => {
                    ip = checked_add(ip, 1)?;
                    let left = memory.read::<u8>(ip)? as _;
                    let right = self.reg(memory.read::<u8>(checked_add(ip, 1)?)? as _)?;
                    *self.reg_mut(left)? &= right;
                }
                OpCode::Or => {
                    ip = checked_add(ip, 1)?;
                    let left = memory.read::<u8>(ip)? as _;
                    let right = self.reg(memory.read::<u8>(checked_add(ip, 1)?)? as _)?;
                    *self.reg_mut(left)? |= right;
                }
                OpCode::Xor => {
                    ip = checked_add(ip, 1)?;
                    let left = memory.read::<u8>(ip)? as _;
                    let right = self.reg(memory.read::<u8>(checked_add(ip, 1)?)? as _)?;
                    *self.reg_mut(left)? ^= right;
                }
                OpCode::Shl => {
                    ip = checked_add(ip, 1)?;
                    let left = memory.read::<u8>(ip)? as _;
                    let right = self.reg(memory.read::<u8>(checked_add(ip, 1)?)? as _)?;
                    *self.reg_mut(left)? <<= right;
                }
                OpCode::Shr => {
                    ip = checked_add(ip, 1)?;
                    let left = memory.read::<u8>(ip)? as _;
                    let right = self.reg(memory.read::<u8>(checked_add(ip, 1)?)? as _)?;
                    *self.reg_mut(left)? >>= right;
                }
                OpCode::Call => {
                    self.push(memory, &self.ip())?;
                    *self.ip_mut() = memory.read(checked_add(ip, 1)?)?;
                }
                OpCode::Return => *self.ip_mut() = self.pop(memory)?,
                OpCode::Cmp => {
                    ip = checked_add(ip, 1)?;
                    let left = self.reg(memory.read::<u8>(ip)? as _)?;
                    let right = self.reg(memory.read::<u8>(checked_add(ip, 1)?)? as _)?;
                    let (_, c) = left.overflowing_sub(right);
                    match c {
                        true => *self.flags_mut() |= Flags::Carry as usize,
                        false => *self.flags_mut() &= !(Flags::Carry as usize),
                    }
                    #[allow(clippy::cast_possible_wrap)]
                    let (sub, o) = (left as isize).overflowing_sub(right as isize);
                    match o {
                        true => *self.flags_mut() |= Flags::Overflow as usize,
                        false => *self.flags_mut() &= !(Flags::Overflow as usize),
                    }
                    if sub == 0 {
                        *self.flags_mut() =
                            self.flags() | Flags::Zero as usize & !(Flags::Sign as usize);
                    } else {
                        *self.flags_mut() &= !(Flags::Zero as usize);
                        match sub < 0 {
                            true => *self.flags_mut() |= Flags::Sign as usize,
                            false => *self.flags_mut() &= !(Flags::Sign as usize),
                        }
                    }
                }
                OpCode::Jump => *self.ip_mut() = memory.read(checked_add(ip, 1)?)?,
                OpCode::JZ | OpCode::JE => {
                    if (self.flags() & (Flags::Zero as usize)) != 0 {
                        *self.ip_mut() = memory.read(checked_add(ip, 1)?)?;
                    }
                }
                OpCode::JNZ | OpCode::JNE => {
                    if (self.flags() & (Flags::Zero as usize)) == 0 {
                        *self.ip_mut() = memory.read(checked_add(ip, 1)?)?;
                    }
                }
                OpCode::JC | OpCode::JB => {
                    if (self.flags() & (Flags::Carry as usize)) != 0 {
                        *self.ip_mut() = memory.read(checked_add(ip, 1)?)?;
                    }
                }
                OpCode::JNC | OpCode::JAE => {
                    if (self.flags() & (Flags::Carry as usize)) == 0 {
                        *self.ip_mut() = memory.read(checked_add(ip, 1)?)?;
                    }
                }
                OpCode::JO => {
                    if (self.flags() & (Flags::Overflow as usize)) != 0 {
                        *self.ip_mut() = memory.read(checked_add(ip, 1)?)?;
                    }
                }
                OpCode::JNO => {
                    if (self.flags() & (Flags::Overflow as usize)) == 0 {
                        *self.ip_mut() = memory.read(checked_add(ip, 1)?)?;
                    }
                }
                OpCode::JS => {
                    if (self.flags() & (Flags::Sign as usize)) != 0 {
                        *self.ip_mut() = memory.read(checked_add(ip, 1)?)?;
                    }
                }
                OpCode::JNS => {
                    if (self.flags() & (Flags::Sign as usize)) == 0 {
                        *self.ip_mut() = memory.read(checked_add(ip, 1)?)?;
                    }
                }
                OpCode::JA => {
                    if (self.flags() & (Flags::Zero as usize)) == 0
                        && (self.flags() & (Flags::Carry as usize)) == 0
                    {
                        *self.ip_mut() = memory.read(checked_add(ip, 1)?)?;
                    }
                }
                OpCode::JBE => {
                    if (self.flags() & (Flags::Zero as usize)) != 0
                        || (self.flags() & (Flags::Carry as usize)) != 0
                    {
                        *self.ip_mut() = memory.read(checked_add(ip, 1)?)?;
                    }
                }
                OpCode::JG => {
                    if (self.flags() & (Flags::Zero as usize)) == 0
                        && (((self.flags() & (Flags::Sign as usize)) == 0)
                            == ((self.flags() & (Flags::Overflow as usize)) == 0))
                    {
                        *self.ip_mut() = memory.read(checked_add(ip, 1)?)?;
                    }
                }
                OpCode::JGE => {
                    if ((self.flags() & (Flags::Sign as usize)) == 0)
                        == ((self.flags() & (Flags::Overflow as usize)) == 0)
                    {
                        *self.ip_mut() = memory.read(checked_add(ip, 1)?)?;
                    }
                }
                OpCode::JL => {
                    if ((self.flags() & (Flags::Sign as usize)) == 0)
                        != ((self.flags() & (Flags::Overflow as usize)) == 0)
                    {
                        *self.ip_mut() = memory.read(checked_add(ip, 1)?)?;
                    }
                }
                OpCode::JLE => {
                    if (self.flags() & (Flags::Zero as usize)) != 0
                        || (((self.flags() & (Flags::Sign as usize)) == 0)
                            != ((self.flags() & (Flags::Overflow as usize)) == 0))
                    {
                        *self.ip_mut() = memory.read(checked_add(ip, 1)?)?;
                    }
                }
                OpCode::LoadLib => {
                    #[cfg(feature = "std")]
                    {
                        let r = memory.read::<u8>(checked_add(ip, 1)?)? as _;
                        let pos = self.reg(r)?;
                        let name = memory
                            .buffer()
                            .get(pos..)
                            .ok_or(NvmError::MemoryReadError { pos, len: 0 })?;
                        let name = CStr::from_bytes_until_nul(name)?.to_str()?;
                        let mut path = PathBuf::from(name);
                        if !name.contains(DLL_SUFFIX) {
                            path = path.with_extension(DLL_EXTENSION);
                        }
                        if let Some(file_name) = path.file_name() {
                            let has_prefix = match file_name.to_string_lossy() {
                                Cow::Borrowed(f) => f.starts_with(DLL_PREFIX),
                                Cow::Owned(f) => f.starts_with(DLL_PREFIX),
                            };
                            if !has_prefix {
                                path = path.with_file_name(format!(
                                    "{DLL_PREFIX}{}",
                                    file_name.to_string_lossy()
                                ));
                            }
                        }
                        // SAFETY: The safety of this operation is documented by it's `Op`.
                        let lib = unsafe { Library::new(path) };
                        *self.reg_mut(r)? = match lib {
                            Ok(lib) => Box::into_raw(Box::new(lib)) as _,
                            _ => 0,
                        };
                    }
                }
                OpCode::LoadSym => {
                    #[cfg(feature = "std")]
                    {
                        ip = checked_add(ip, 1)?;
                        let left = memory.read::<u8>(ip)? as _;
                        let right = self.reg(memory.read::<u8>(checked_add(ip, 1)?)? as _)?;
                        // SAFETY: The safety of this operation is documented by it's `Op`.
                        let lib = unsafe { &*(right as *const Library) };
                        let pos = self.reg(left)?;
                        let name = memory
                            .buffer()
                            .get(pos..)
                            .ok_or(NvmError::MemoryReadError { pos, len: 0 })?;
                        let name = CStr::from_bytes_until_nul(name)?;
                        // SAFETY: We're using an opaque function pointer.
                        let sym = unsafe { lib.get::<fn()>(name.to_bytes()) };
                        *self.reg_mut(left)? = match sym {
                            Ok(sym) => *sym as _,
                            _ => 0,
                        };
                    }
                }
                OpCode::Syscall => {
                    #[cfg(feature = "std")]
                    {
                        /// Gets the next FFI type from memory.
                        fn next_type(
                            vm: &mut VM,
                            memory: &impl MemoryDriver,
                        ) -> Result<Type, NvmError> {
                            match vm.pop::<u8>(memory)? {
                                0 => Ok(Type::void()),
                                1 => Ok(Type::pointer()),
                                2 => Ok(Type::usize()),
                                3 => Ok(Type::isize()),
                                4 => Ok(Type::u8()),
                                5 => Ok(Type::i8()),
                                6 => Ok(Type::u16()),
                                7 => Ok(Type::i16()),
                                8 => Ok(Type::u32()),
                                9 => Ok(Type::i32()),
                                10 => Ok(Type::u64()),
                                11 => Ok(Type::i64()),
                                12 => Ok(Type::c_uchar()),
                                13 => Ok(Type::c_schar()),
                                14 => Ok(Type::c_ushort()),
                                15 => Ok(Type::c_short()),
                                16 => Ok(Type::c_uint()),
                                17 => Ok(Type::c_int()),
                                18 => Ok(Type::c_ulong()),
                                19 => Ok(Type::c_long()),
                                20 => Ok(Type::c_ulonglong()),
                                21 => Ok(Type::c_longlong()),
                                22 => {
                                    let num_fields = vm.pop::<usize>(memory)?;
                                    let mut fields = Vec::with_capacity(num_fields);
                                    for _ in 0..num_fields {
                                        fields.push(next_type(vm, memory)?);
                                    }
                                    Ok(Type::structure(fields))
                                }
                                ty => Err(NvmError::FfiTypeError(ty)),
                            }
                        }
                        ip = checked_add(ip, 1)?;
                        let left = self.reg(memory.read::<u8>(ip)? as _)?;
                        let right = self.reg(memory.read::<u8>(checked_add(ip, 1)?)? as _)?;
                        #[allow(clippy::collection_is_never_read)]
                        let mut types = Vec::with_capacity(right);
                        let mut raw_types = Vec::with_capacity(right);
                        for _ in 0..right {
                            let ty = next_type(&mut self, memory)?;
                            raw_types.push(ty.as_raw_ptr());
                            types.push(ty);
                        }
                        let ret = next_type(&mut self, memory)?;
                        // SAFETY: `ret` is stored on the stack.
                        let ret_size = unsafe { (*ret.as_raw_ptr()).size };
                        let mut cif = MaybeUninit::uninit();
                        // SAFETY: The safety of this operation is documented by it's `Op`.
                        unsafe {
                            let err = libffi::raw::ffi_prep_cif(
                                cif.as_mut_ptr(),
                                ffi_abi_FFI_DEFAULT_ABI,
                                right.try_into()?,
                                ret.as_raw_ptr(),
                                raw_types.as_mut_ptr(),
                            );
                            if err != ffi_status_FFI_OK {
                                return Err(NvmError::FfiCifError);
                            }
                        }
                        let mut args = Vec::with_capacity(raw_types.len());
                        for ty in &raw_types {
                            // SAFETY: `ty` is pointing to a valid `ffi_type`.
                            let arg_size = unsafe { (**ty).size };
                            *self.sp_mut() = checked_sub(self.sp(), arg_size)?;
                            let Some(byte) = memory.buffer_mut().get_mut(self.sp()) else {
                                return Err(NvmError::MemoryReadError {
                                    pos: self.sp(),
                                    len: arg_size,
                                });
                            };
                            args.push(addr_of_mut!(*byte).cast());
                        }
                        let ret_addr = checked_sub(self.sp(), ret_size)?;
                        let Some(ret) = memory.buffer_mut().get_mut(ret_addr) else {
                            return Err(NvmError::MemoryWriteError {
                                pos: ret_addr,
                                len: ret_size,
                            });
                        };
                        let ret = addr_of_mut!(*ret).cast();
                        // SAFETY: `usize` to function pointer transmute.
                        let f = unsafe { Some(std::mem::transmute(left)) };
                        // SAFETY: The safety of this operation is documented by it's `Op`.
                        unsafe {
                            libffi::raw::ffi_call(cif.as_mut_ptr(), f, ret, args.as_mut_ptr());
                        }
                    }
                }
                OpCode::FreeLib => {
                    #[cfg(feature = "std")]
                    {
                        let r = self.reg(memory.read::<u8>(checked_add(ip, 1)?)? as _)?;
                        // SAFETY: The safety of this operation is documented by it's `Op`.
                        unsafe { drop(Box::from_raw(r as *mut Library)) };
                    }
                }
            }
        }
    }
}
