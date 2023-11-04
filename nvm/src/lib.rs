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
    clippy::absolute_paths,
    clippy::as_conversions,
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
    clippy::std_instead_of_core,
    clippy::useless_conversion
)]
#![cfg_attr(feature = "bin", allow(unused_crate_dependencies))]
#[cfg(feature = "std")]
extern crate alloc;
pub mod constants;
pub mod opcode;
use self::{constants::BUILTIN_REGS, opcode::OpCode};
use bytemuck::NoUninit;
use cfg_if::cfg_if;
use core::{
    convert::Infallible, ffi::FromBytesUntilNulError, num::TryFromIntError, str::Utf8Error,
};
use num_traits::FromPrimitive;
#[cfg(feature = "std")]
use ::{
    alloc::borrow::Cow,
    core::{ffi::CStr, mem::MaybeUninit, ptr::addr_of_mut},
    libffi::{
        middle::Type,
        raw::{ffi_abi_FFI_DEFAULT_ABI, ffi_status_FFI_OK},
    },
    libloading::{Error as LibLoadingError, Library},
    std::{
        env::consts::{DLL_EXTENSION, DLL_PREFIX, DLL_SUFFIX},
        path::PathBuf,
    },
    thiserror::Error,
};

cfg_if! {
    if #[cfg(feature = "8bit")] {
        /// The virtual machine's unsigned word type.
        pub type UInt = u8;
        /// The virtual machine's signed word type.
        pub type Int = i8;
    } else if #[cfg(feature = "16bit")] {
        /// The virtual machine's unsigned word type.
        pub type UInt = u16;
        /// The virtual machine's signed word type.
        pub type Int = i16;
    } else if #[cfg(feature = "32bit")] {
        /// The virtual machine's unsigned word type.
        pub type UInt = u32;
        /// The virtual machine's signed word type.
        pub type Int = i32;
    } else if #[cfg(feature = "64bit")] {
        /// The virtual machine's unsigned word type.
        pub type UInt = u64;
        /// The virtual machine's signed word type.
        pub type Int = i64;
    } else if #[cfg(feature = "128bit")] {
        /// The virtual machine's unsigned word type.
        pub type UInt = u128;
        /// The virtual machine's signed word type.
        pub type Int = i128;
    } else {
        /// The virtual machine's unsigned word type.
        pub type UInt = usize;
        /// The virtual machine's signed word type.
        pub type Int = isize;
    }
}

/// Describes an error returned from the NVM virtual machine.
#[derive(Debug)]
#[cfg_attr(feature = "std", derive(Error))]
pub enum NvmError {
    /// An error that can never occur.
    #[cfg_attr(feature = "std", error("this error should never be encountered"))]
    Infallible,
    /// A virtual machine was created with an invalid number of registers.
    #[cfg_attr(
        feature = "std",
        error("a virtual machine was created with an invalid register count of {0}")
    )]
    InvalidRegisterCount(usize),
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
        pos: UInt,
        /// The attempted number of bytes to read.
        len: UInt,
    },
    /// A memory driver failed to write to a specific memory location.
    #[cfg_attr(
        feature = "std",
        error("a virtual memory driver failed to write {len} bytes to location {pos}")
    )]
    MemoryWriteError {
        /// The memory position of the read.
        pos: UInt,
        /// The attempted number of bytes to read.
        len: UInt,
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
    TryFromIntError(TryFromIntError),
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
impl From<Infallible> for NvmError {
    /// Converts an [`Infallible`] error into an [`NvmError`].
    #[inline]
    fn from(_: Infallible) -> Self {
        Self::Infallible
    }
}
impl From<TryFromIntError> for NvmError {
    /// Converts a [`TryFromIntError`] error into an [`NvmError`].
    #[inline]
    fn from(value: TryFromIntError) -> Self {
        Self::TryFromIntError(value)
    }
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
    fn read<T: Copy>(&self, pos: UInt) -> Result<T, NvmError>;

    /// Writes a value to a specific location in the virtual memory.
    ///
    /// # Errors
    ///
    /// This operation is allowed to fail under any condition.
    fn write<T: NoUninit>(&mut self, pos: UInt, value: &T) -> Result<(), NvmError>;

    /// Writes a slice of bytes to this memory at offset `pos`.
    ///
    /// # Errors
    ///
    /// This operation is allowed to fail under any condition.
    fn write_bytes(&mut self, pos: UInt, buffer: &[u8]) -> Result<(), NvmError>;
}

/// A trait implemented on types that have an endian dependent layout.
trait HasEndianness: Sized {
    /// Reads a value from `memory`.
    ///
    /// How the value is read from memory is dependent on what endian feature flags are set.
    fn read(memory: &impl MemoryDriver, pos: UInt) -> Result<Self, NvmError>;
}
impl HasEndianness for UInt {
    /// Reads a value from `memory`.
    ///
    /// How the value is read from memory is dependent on what endian feature flags are set.
    #[inline]
    fn read(memory: &impl MemoryDriver, pos: UInt) -> Result<Self, NvmError> {
        let mut s = memory.read::<Self>(pos)?;
        if cfg!(feature = "little_endian") {
            s = Self::from_le(s);
        } else if cfg!(feature = "big_endian") {
            s = Self::from_be(s);
        }
        Ok(s)
    }
}
impl HasEndianness for RegConst {
    /// Reads a value from `memory`.
    ///
    /// How the value is read from memory is dependent on what endian feature flags are set.
    #[inline]
    fn read(memory: &impl MemoryDriver, pos: UInt) -> Result<Self, NvmError> {
        let mut s = memory.read::<Self>(pos)?;
        if cfg!(feature = "little_endian") {
            s.1 = UInt::from_le(s.1);
        } else if cfg!(feature = "big_endian") {
            s.1 = UInt::from_be(s.1);
        }
        Ok(s)
    }
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

/// Computes a checked addition operation on a value.
macro_rules! checked_add {
    ($x: expr, $y: expr) => {
        $x.checked_add($y).ok_or(NvmError::OverflowError)
    };
}

/// Computes a checked subtraction operation on a value.
macro_rules! checked_sub {
    ($x: expr, $y: expr) => {
        $x.checked_sub($y).ok_or(NvmError::OverflowError)
    };
}

/// A structure that contains a register index and a register-sized constant value.
#[repr(packed)]
#[derive(Clone, Copy)]
struct RegConst(u8, UInt);

/// The NVM virtual machine.
#[derive(Debug)]
#[allow(missing_copy_implementations)]
pub struct VM<const REG_COUNT: usize> {
    /// The general purpose registers.
    reg: [UInt; REG_COUNT],
}
impl<const REG_COUNT: usize> VM<REG_COUNT> {
    /// A constant for indexing the virtual machine's instruction pointer register.
    pub const IP: usize = REG_COUNT - BUILTIN_REGS;

    /// A constant for indexing the virtual machine's stack pointer register.
    pub const SP: usize = REG_COUNT - BUILTIN_REGS + 1;

    /// A constant for indexing the virtual machine's flags register.
    pub const FLAGS: usize = REG_COUNT - BUILTIN_REGS + 2;

    /// Creates a new NVM virtual machine.
    ///
    /// # Errors
    ///
    /// This operation will return an [`InvalidRegisterCount`] error if `REG_COUNT` is
    /// less than [`BUILTIN_REGS`].
    ///
    /// [`InvalidRegisterCount`]: NvmError::InvalidRegisterCount
    #[inline]
    pub const fn new() -> Result<Self, NvmError> {
        if REG_COUNT < BUILTIN_REGS {
            return Err(NvmError::InvalidRegisterCount(REG_COUNT));
        }
        Ok(Self {
            reg: [0; REG_COUNT],
        })
    }

    /// Returns a copy of a register.
    #[inline]
    fn reg(&self, i: usize) -> Result<UInt, NvmError> {
        self.reg.get(i).copied().ok_or(NvmError::InvalidRegister(i))
    }

    /// Returns a mutable reference to a register.
    #[inline]
    fn reg_mut(&mut self, i: usize) -> Result<&mut UInt, NvmError> {
        self.reg.get_mut(i).ok_or(NvmError::InvalidRegister(i))
    }

    /// Returns a copy of the instruction pointer.
    #[inline]
    #[allow(clippy::indexing_slicing)]
    const fn ip(&self) -> UInt {
        self.reg[Self::IP]
    }

    /// Returns a mutable reference to the instruction pointer.
    #[inline]
    #[allow(clippy::indexing_slicing)]
    fn ip_mut(&mut self) -> &mut UInt {
        &mut self.reg[Self::IP]
    }

    /// Returns a copy of the stack pointer.
    #[inline]
    #[allow(clippy::indexing_slicing)]
    const fn sp(&self) -> UInt {
        self.reg[Self::SP]
    }

    /// Returns a mutable reference to the stack pointer.
    #[inline]
    #[allow(clippy::indexing_slicing)]
    fn sp_mut(&mut self) -> &mut UInt {
        &mut self.reg[Self::SP]
    }

    /// Returns a copy of the flags register.
    #[inline]
    #[allow(clippy::indexing_slicing)]
    const fn flags(&self) -> UInt {
        self.reg[Self::FLAGS]
    }

    /// Returns a mutable reference to the flags register.
    #[inline]
    #[allow(clippy::indexing_slicing)]
    fn flags_mut(&mut self) -> &mut UInt {
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
        *self.sp_mut() = checked_add!(self.sp(), core::mem::size_of::<T>().try_into()?)?;
        Ok(())
    }

    /// Pops a value off of the virtual stack.
    #[inline]
    fn pop<T: Copy>(&mut self, memory: &impl MemoryDriver) -> Result<T, NvmError> {
        *self.sp_mut() = checked_sub!(self.sp(), core::mem::size_of::<T>().try_into()?)?;
        memory.read(self.sp())
    }

    /// Runs the NVM bytecode on the virtual machine.
    ///
    /// # Errors
    ///
    /// This operation may return an error at any time while executing NVM bytecode.
    #[allow(clippy::too_many_lines)]
    pub fn run(&mut self, code: &[u8], memory: &mut impl MemoryDriver) -> Result<UInt, NvmError> {
        memory.write_bytes(0, code)?;
        *self.sp_mut() = code.len().try_into()?;
        loop {
            let ip = self.ip();
            let op = memory.read::<u8>(ip)?;
            let opcode = OpCode::from_u8(op).ok_or(NvmError::InvalidOperation(op))?;
            *self.ip_mut() = checked_add!(ip, opcode.size().try_into()?)?;
            match opcode {
                OpCode::Exit => {
                    return self.reg(memory.read::<u8>(checked_add!(ip, 1)?)?.try_into()?);
                }
                OpCode::Nop => {}
                OpCode::Move => {
                    let [l, r] = memory.read::<[u8; 2]>(checked_add!(ip, 1)?)?;
                    *self.reg_mut(l.try_into()?)? = self.reg(r.try_into()?)?;
                }
                OpCode::MoveConst => {
                    let RegConst(r, c) = RegConst::read(memory, checked_add!(ip, 1)?)?;
                    *self.reg_mut(r.try_into()?)? = c;
                }
                OpCode::Load => {
                    let [l, r] = memory.read::<[u8; 2]>(checked_add!(ip, 1)?)?;
                    *self.reg_mut(l.try_into()?)? = memory.read(self.reg(r.try_into()?)?)?;
                }
                OpCode::LoadNum => {
                    let [l, r, n] = memory.read::<[u8; 3]>(checked_add!(ip, 1)?)?;
                    let n = n.try_into()?;
                    let pos = self.reg(r.try_into()?)?;
                    let mem_pos: usize = pos.try_into()?;
                    let Some(mem) = memory.buffer().get(mem_pos..checked_add!(mem_pos, n)?) else {
                        return Err(NvmError::MemoryReadError {
                            pos,
                            len: n.try_into()?,
                        });
                    };
                    let r = self.reg_mut(l.try_into()?)?;
                    *r = 0;
                    let bytes = bytemuck::bytes_of_mut(r);
                    let bytes = match cfg!(target_endian = "little") {
                        true => bytes.get_mut(..n),
                        false => bytes.get_mut(checked_sub!(bytes.len(), n)?..),
                    }
                    .ok_or(NvmError::RegisterWriteError)?;
                    bytes.copy_from_slice(mem);
                }
                OpCode::Store => {
                    let [l, r] = memory.read::<[u8; 2]>(checked_add!(ip, 1)?)?;
                    memory.write(self.reg(l.try_into()?)?, &self.reg(r.try_into()?)?)?;
                }
                OpCode::StoreNum => {
                    let [l, r, n] = memory.read::<[u8; 3]>(checked_add!(ip, 1)?)?;
                    let n = n.try_into()?;
                    let bytes = self.reg(r.try_into()?)?.to_ne_bytes();
                    let bytes = match cfg!(target_endian = "little") {
                        true => bytes.get(..n),
                        false => bytes.get(checked_sub!(bytes.len(), n)?..),
                    }
                    .ok_or(NvmError::RegisterReadError)?;
                    memory.write_bytes(self.reg(l.try_into()?)?, bytes)?;
                }
                OpCode::Push => {
                    let r = memory.read::<u8>(checked_add!(ip, 1)?)?.try_into()?;
                    self.push(memory, &self.reg(r)?)?;
                }
                OpCode::PushNum => {
                    let [r, n] = memory.read::<[u8; 2]>(checked_add!(ip, 1)?)?;
                    let n = n.try_into()?;
                    let bytes = self.reg(r.try_into()?)?.to_ne_bytes();
                    let bytes = match cfg!(target_endian = "little") {
                        true => bytes.get(..n),
                        false => bytes.get(checked_sub!(bytes.len(), n)?..),
                    }
                    .ok_or(NvmError::RegisterReadError)?;
                    memory.write_bytes(self.sp(), bytes)?;
                    *self.sp_mut() = checked_add!(self.sp(), n.try_into()?)?;
                }
                OpCode::Pop => {
                    let r = memory.read::<u8>(checked_add!(ip, 1)?)?.try_into()?;
                    *self.reg_mut(r)? = self.pop(memory)?;
                }
                OpCode::PopNum => {
                    let [r, n] = memory.read::<[u8; 2]>(checked_add!(ip, 1)?)?;
                    let n = n.try_into()?;
                    let pos = checked_sub!(self.sp(), n)?;
                    let Some(mem) = memory.buffer().get(pos.try_into()?..self.sp().try_into()?)
                    else {
                        return Err(NvmError::MemoryReadError { pos, len: n });
                    };
                    let r = self.reg_mut(r.try_into()?)?;
                    *r = 0;
                    let bytes = bytemuck::bytes_of_mut(r);
                    let bytes = match cfg!(target_endian = "little") {
                        true => bytes.get_mut(..n.try_into()?),
                        false => bytes.get_mut(checked_sub!(bytes.len(), n.try_into()?)?..),
                    }
                    .ok_or(NvmError::RegisterWriteError)?;
                    bytes.copy_from_slice(mem);
                    *self.sp_mut() = checked_sub!(self.sp(), n)?;
                }
                #[allow(clippy::cast_possible_wrap, clippy::cast_sign_loss)]
                OpCode::Neg => {
                    let r = memory.read::<u8>(checked_add!(ip, 1)?)?.try_into()?;
                    let (n, o) = (self.reg(r)? as Int).overflowing_neg();
                    match o {
                        true => *self.flags_mut() |= Flags::Overflow as UInt,
                        false => *self.flags_mut() &= !(Flags::Overflow as UInt),
                    }
                    if n == 0 {
                        *self.flags_mut() =
                            self.flags() | Flags::Zero as UInt & !(Flags::Sign as UInt);
                    } else {
                        *self.flags_mut() &= !(Flags::Zero as UInt);
                        match n < 0 {
                            true => *self.flags_mut() |= Flags::Sign as UInt,
                            false => *self.flags_mut() &= !(Flags::Sign as UInt),
                        }
                    }
                    *self.reg_mut(r)? = n as UInt;
                }
                OpCode::Add => {
                    let [l, r] = memory.read::<[u8; 2]>(checked_add!(ip, 1)?)?;
                    let l = l.try_into()?;
                    let (add, c) = self.reg(l)?.overflowing_add(self.reg(r.try_into()?)?);
                    match c {
                        true => *self.flags_mut() |= Flags::Carry as UInt,
                        false => *self.flags_mut() &= !(Flags::Carry as UInt),
                    }
                    match add == 0 {
                        true => *self.flags_mut() |= Flags::Zero as UInt,
                        false => *self.flags_mut() &= !(Flags::Zero as UInt),
                    }
                    *self.reg_mut(l)? = add;
                }
                #[allow(clippy::cast_possible_wrap, clippy::cast_sign_loss)]
                OpCode::AddI => {
                    let [l, r] = memory.read::<[u8; 2]>(checked_add!(ip, 1)?)?;
                    let l = l.try_into()?;
                    let r = self.reg(r.try_into()?)? as Int;
                    let (add, o) = (self.reg(l)? as Int).overflowing_add(r);
                    match o {
                        true => *self.flags_mut() |= Flags::Overflow as UInt,
                        false => *self.flags_mut() &= !(Flags::Overflow as UInt),
                    }
                    if add == 0 {
                        *self.flags_mut() =
                            self.flags() | Flags::Zero as UInt & !(Flags::Sign as UInt);
                    } else {
                        *self.flags_mut() &= !(Flags::Zero as UInt);
                        match add < 0 {
                            true => *self.flags_mut() |= Flags::Sign as UInt,
                            false => *self.flags_mut() &= !(Flags::Sign as UInt),
                        }
                    }
                    *self.reg_mut(l)? = add as UInt;
                }
                OpCode::Sub => {
                    let [l, r] = memory.read::<[u8; 2]>(checked_add!(ip, 1)?)?;
                    let l = l.try_into()?;
                    let (sub, c) = self.reg(l)?.overflowing_sub(self.reg(r.try_into()?)?);
                    match c {
                        true => *self.flags_mut() |= Flags::Carry as UInt,
                        false => *self.flags_mut() &= !(Flags::Carry as UInt),
                    }
                    match sub == 0 {
                        true => *self.flags_mut() |= Flags::Zero as UInt,
                        false => *self.flags_mut() &= !(Flags::Zero as UInt),
                    }
                    *self.reg_mut(l)? = sub;
                }
                #[allow(clippy::cast_possible_wrap, clippy::cast_sign_loss)]
                OpCode::SubI => {
                    let [l, r] = memory.read::<[u8; 2]>(checked_add!(ip, 1)?)?;
                    let l = l.try_into()?;
                    let r = self.reg(r.try_into()?)? as Int;
                    let (sub, o) = (self.reg(l)? as Int).overflowing_sub(r);
                    match o {
                        true => *self.flags_mut() |= Flags::Overflow as UInt,
                        false => *self.flags_mut() &= !(Flags::Overflow as UInt),
                    }
                    if sub == 0 {
                        *self.flags_mut() =
                            self.flags() | Flags::Zero as UInt & !(Flags::Sign as UInt);
                    } else {
                        *self.flags_mut() &= !(Flags::Zero as UInt);
                        match sub < 0 {
                            true => *self.flags_mut() |= Flags::Sign as UInt,
                            false => *self.flags_mut() &= !(Flags::Sign as UInt),
                        }
                    }
                    *self.reg_mut(l)? = sub as UInt;
                }
                OpCode::Mul => {
                    let [l, r] = memory.read::<[u8; 2]>(checked_add!(ip, 1)?)?;
                    let l = l.try_into()?;
                    let (mul, c) = self.reg(l)?.overflowing_mul(self.reg(r.try_into()?)?);
                    match c {
                        true => *self.flags_mut() |= Flags::Carry as UInt,
                        false => *self.flags_mut() &= !(Flags::Carry as UInt),
                    }
                    match mul == 0 {
                        true => *self.flags_mut() |= Flags::Zero as UInt,
                        false => *self.flags_mut() &= !(Flags::Zero as UInt),
                    }
                    *self.reg_mut(l)? = mul;
                }
                #[allow(clippy::cast_possible_wrap, clippy::cast_sign_loss)]
                OpCode::MulI => {
                    let [l, r] = memory.read::<[u8; 2]>(checked_add!(ip, 1)?)?;
                    let l = l.try_into()?;
                    let r = self.reg(r.try_into()?)? as Int;
                    let (mul, o) = (self.reg(l)? as Int).overflowing_mul(r);
                    match o {
                        true => *self.flags_mut() |= Flags::Overflow as UInt,
                        false => *self.flags_mut() &= !(Flags::Overflow as UInt),
                    }
                    if mul == 0 {
                        *self.flags_mut() =
                            self.flags() | Flags::Zero as UInt & !(Flags::Sign as UInt);
                    } else {
                        *self.flags_mut() &= !(Flags::Zero as UInt);
                        match mul < 0 {
                            true => *self.flags_mut() |= Flags::Sign as UInt,
                            false => *self.flags_mut() &= !(Flags::Sign as UInt),
                        }
                    }
                    *self.reg_mut(l)? = mul as UInt;
                }
                OpCode::Div => {
                    let [l, r] = memory.read::<[u8; 2]>(checked_add!(ip, 1)?)?;
                    let l = l.try_into()?;
                    let (div, c) = self.reg(l)?.overflowing_div(self.reg(r.try_into()?)?);
                    match c {
                        true => *self.flags_mut() |= Flags::Carry as UInt,
                        false => *self.flags_mut() &= !(Flags::Carry as UInt),
                    }
                    match div == 0 {
                        true => *self.flags_mut() |= Flags::Zero as UInt,
                        false => *self.flags_mut() &= !(Flags::Zero as UInt),
                    }
                    *self.reg_mut(l)? = div;
                }
                #[allow(clippy::cast_possible_wrap, clippy::cast_sign_loss)]
                OpCode::DivI => {
                    let [l, r] = memory.read::<[u8; 2]>(checked_add!(ip, 1)?)?;
                    let l = l.try_into()?;
                    let r = self.reg(r.try_into()?)? as Int;
                    let (div, o) = (self.reg(l)? as Int).overflowing_div(r);
                    match o {
                        true => *self.flags_mut() |= Flags::Overflow as UInt,
                        false => *self.flags_mut() &= !(Flags::Overflow as UInt),
                    }
                    if div == 0 {
                        *self.flags_mut() =
                            self.flags() | Flags::Zero as UInt & !(Flags::Sign as UInt);
                    } else {
                        *self.flags_mut() &= !(Flags::Zero as UInt);
                        match div < 0 {
                            true => *self.flags_mut() |= Flags::Sign as UInt,
                            false => *self.flags_mut() &= !(Flags::Sign as UInt),
                        }
                    }
                    *self.reg_mut(l)? = div as UInt;
                }
                OpCode::Not => {
                    let r = self.reg_mut(memory.read::<u8>(checked_add!(ip, 1)?)?.try_into()?)?;
                    *r = !*r;
                }
                OpCode::And => {
                    let [l, r] = memory.read::<[u8; 2]>(checked_add!(ip, 1)?)?;
                    *self.reg_mut(l.try_into()?)? &= self.reg(r.try_into()?)?;
                }
                OpCode::Or => {
                    let [l, r] = memory.read::<[u8; 2]>(checked_add!(ip, 1)?)?;
                    *self.reg_mut(l.try_into()?)? |= self.reg(r.try_into()?)?;
                }
                OpCode::Xor => {
                    let [l, r] = memory.read::<[u8; 2]>(checked_add!(ip, 1)?)?;
                    *self.reg_mut(l.try_into()?)? ^= self.reg(r.try_into()?)?;
                }
                OpCode::Shl => {
                    let [l, r] = memory.read::<[u8; 2]>(checked_add!(ip, 1)?)?;
                    let l = l.try_into()?;
                    let r = self.reg(r.try_into()?)?.try_into()?;
                    let (shl, c) = self.reg(l)?.overflowing_shl(r);
                    match c {
                        true => *self.flags_mut() |= Flags::Carry as UInt,
                        false => *self.flags_mut() &= !(Flags::Carry as UInt),
                    }
                    match shl == 0 {
                        true => *self.flags_mut() |= Flags::Zero as UInt,
                        false => *self.flags_mut() &= !(Flags::Zero as UInt),
                    }
                    *self.reg_mut(l)? = shl;
                }
                OpCode::Shr => {
                    let [l, r] = memory.read::<[u8; 2]>(checked_add!(ip, 1)?)?;
                    let l = l.try_into()?;
                    let r = self.reg(r.try_into()?)?.try_into()?;
                    let (shr, c) = self.reg(l)?.overflowing_shr(r);
                    match c {
                        true => *self.flags_mut() |= Flags::Carry as UInt,
                        false => *self.flags_mut() &= !(Flags::Carry as UInt),
                    }
                    match shr == 0 {
                        true => *self.flags_mut() |= Flags::Zero as UInt,
                        false => *self.flags_mut() &= !(Flags::Zero as UInt),
                    }
                    *self.reg_mut(l)? = shr;
                }
                OpCode::Call => {
                    self.push(memory, &self.ip())?;
                    *self.ip_mut() = UInt::read(memory, checked_add!(ip, 1)?)?;
                }
                OpCode::Return => *self.ip_mut() = self.pop(memory)?,
                OpCode::Cmp => {
                    let [l, r] = memory.read::<[u8; 2]>(checked_add!(ip, 1)?)?;
                    let l = self.reg(l.try_into()?)?;
                    let r = self.reg(r.try_into()?)?;
                    let (_, c) = l.overflowing_sub(r);
                    match c {
                        true => *self.flags_mut() |= Flags::Carry as UInt,
                        false => *self.flags_mut() &= !(Flags::Carry as UInt),
                    }
                    #[allow(clippy::cast_possible_wrap)]
                    let (sub, o) = (l as Int).overflowing_sub(r as Int);
                    match o {
                        true => *self.flags_mut() |= Flags::Overflow as UInt,
                        false => *self.flags_mut() &= !(Flags::Overflow as UInt),
                    }
                    if sub == 0 {
                        *self.flags_mut() =
                            self.flags() | Flags::Zero as UInt & !(Flags::Sign as UInt);
                    } else {
                        *self.flags_mut() &= !(Flags::Zero as UInt);
                        match sub < 0 {
                            true => *self.flags_mut() |= Flags::Sign as UInt,
                            false => *self.flags_mut() &= !(Flags::Sign as UInt),
                        }
                    }
                }
                OpCode::Jump => *self.ip_mut() = UInt::read(memory, checked_add!(ip, 1)?)?,
                OpCode::JZ | OpCode::JE => {
                    if (self.flags() & (Flags::Zero as UInt)) != 0 {
                        *self.ip_mut() = UInt::read(memory, checked_add!(ip, 1)?)?;
                    }
                }
                OpCode::JNZ | OpCode::JNE => {
                    if (self.flags() & (Flags::Zero as UInt)) == 0 {
                        *self.ip_mut() = UInt::read(memory, checked_add!(ip, 1)?)?;
                    }
                }
                OpCode::JC | OpCode::JB => {
                    if (self.flags() & (Flags::Carry as UInt)) != 0 {
                        *self.ip_mut() = UInt::read(memory, checked_add!(ip, 1)?)?;
                    }
                }
                OpCode::JNC | OpCode::JAE => {
                    if (self.flags() & (Flags::Carry as UInt)) == 0 {
                        *self.ip_mut() = UInt::read(memory, checked_add!(ip, 1)?)?;
                    }
                }
                OpCode::JO => {
                    if (self.flags() & (Flags::Overflow as UInt)) != 0 {
                        *self.ip_mut() = UInt::read(memory, checked_add!(ip, 1)?)?;
                    }
                }
                OpCode::JNO => {
                    if (self.flags() & (Flags::Overflow as UInt)) == 0 {
                        *self.ip_mut() = UInt::read(memory, checked_add!(ip, 1)?)?;
                    }
                }
                OpCode::JS => {
                    if (self.flags() & (Flags::Sign as UInt)) != 0 {
                        *self.ip_mut() = UInt::read(memory, checked_add!(ip, 1)?)?;
                    }
                }
                OpCode::JNS => {
                    if (self.flags() & (Flags::Sign as UInt)) == 0 {
                        *self.ip_mut() = UInt::read(memory, checked_add!(ip, 1)?)?;
                    }
                }
                OpCode::JA => {
                    if (self.flags() & (Flags::Zero as UInt)) == 0
                        && (self.flags() & (Flags::Carry as UInt)) == 0
                    {
                        *self.ip_mut() = UInt::read(memory, checked_add!(ip, 1)?)?;
                    }
                }
                OpCode::JBE => {
                    if (self.flags() & (Flags::Zero as UInt)) != 0
                        || (self.flags() & (Flags::Carry as UInt)) != 0
                    {
                        *self.ip_mut() = UInt::read(memory, checked_add!(ip, 1)?)?;
                    }
                }
                OpCode::JG => {
                    if (self.flags() & (Flags::Zero as UInt)) == 0
                        && (((self.flags() & (Flags::Sign as UInt)) == 0)
                            == ((self.flags() & (Flags::Overflow as UInt)) == 0))
                    {
                        *self.ip_mut() = UInt::read(memory, checked_add!(ip, 1)?)?;
                    }
                }
                OpCode::JGE => {
                    if ((self.flags() & (Flags::Sign as UInt)) == 0)
                        == ((self.flags() & (Flags::Overflow as UInt)) == 0)
                    {
                        *self.ip_mut() = UInt::read(memory, checked_add!(ip, 1)?)?;
                    }
                }
                OpCode::JL => {
                    if ((self.flags() & (Flags::Sign as UInt)) == 0)
                        != ((self.flags() & (Flags::Overflow as UInt)) == 0)
                    {
                        *self.ip_mut() = UInt::read(memory, checked_add!(ip, 1)?)?;
                    }
                }
                OpCode::JLE => {
                    if (self.flags() & (Flags::Zero as UInt)) != 0
                        || (((self.flags() & (Flags::Sign as UInt)) == 0)
                            != ((self.flags() & (Flags::Overflow as UInt)) == 0))
                    {
                        *self.ip_mut() = UInt::read(memory, checked_add!(ip, 1)?)?;
                    }
                }
                OpCode::LoadLib => {
                    #[cfg(feature = "std")]
                    {
                        let r = memory.read::<u8>(checked_add!(ip, 1)?)?.try_into()?;
                        let pos = self.reg(r)?;
                        let name = memory
                            .buffer()
                            .get(pos.try_into()?..)
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
                        *self.reg_mut(r)? = lib
                            .map_or(0, |lib| Box::into_raw(Box::new(lib)) as usize)
                            .try_into()?;
                    }
                }
                OpCode::LoadSym => {
                    #[cfg(feature = "std")]
                    {
                        let [l, r] = memory.read::<[u8; 2]>(checked_add!(ip, 1)?)?;
                        let l = l.try_into()?;
                        // SAFETY: The safety of this operation is documented by it's `Op`.
                        let lib = unsafe { &*(self.reg(r.try_into()?)? as *const Library) };
                        let pos = self.reg(l)?;
                        let name = memory
                            .buffer()
                            .get(pos.try_into()?..)
                            .ok_or(NvmError::MemoryReadError { pos, len: 0 })?;
                        let name = CStr::from_bytes_until_nul(name)?;
                        // SAFETY: We're using an opaque function pointer.
                        let sym = unsafe { lib.get::<fn()>(name.to_bytes()) };
                        *self.reg_mut(l)? = sym.map_or(0, |sym| *sym as usize).try_into()?;
                    }
                }
                OpCode::Syscall => {
                    #[cfg(feature = "std")]
                    {
                        /// Gets the next FFI type from memory.
                        fn next_type<const REG_COUNT: usize>(
                            vm: &mut VM<REG_COUNT>,
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
                        let [l, r] = memory.read::<[u8; 2]>(checked_add!(ip, 1)?)?;
                        let l = self.reg(l.try_into()?)?;
                        let r = self.reg(r.try_into()?)?.try_into()?;
                        #[allow(clippy::collection_is_never_read)]
                        let mut types = Vec::with_capacity(r);
                        let mut raw_types = Vec::with_capacity(r);
                        for _ in 0..r {
                            let ty = next_type(self, memory)?;
                            raw_types.push(ty.as_raw_ptr());
                            types.push(ty);
                        }
                        let ret = next_type(self, memory)?;
                        // SAFETY: `ret` is stored on the stack.
                        let ret_size = unsafe { (*ret.as_raw_ptr()).size.try_into()? };
                        let mut cif = MaybeUninit::uninit();
                        // SAFETY: The safety of this operation is documented by it's `Op`.
                        unsafe {
                            let err = libffi::raw::ffi_prep_cif(
                                cif.as_mut_ptr(),
                                ffi_abi_FFI_DEFAULT_ABI,
                                r.try_into()?,
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
                            let arg_size = unsafe { (**ty).size.try_into()? };
                            *self.sp_mut() = checked_sub!(self.sp(), arg_size)?;
                            let Some(byte) =
                                memory
                                    .buffer_mut()
                                    .get_mut(<UInt as TryInto<usize>>::try_into(self.sp())?)
                            else {
                                return Err(NvmError::MemoryReadError {
                                    pos: self.sp(),
                                    len: arg_size,
                                });
                            };
                            args.push(addr_of_mut!(*byte).cast());
                        }
                        let ret_addr = checked_sub!(self.sp(), ret_size)?;
                        let Some(ret) = memory
                            .buffer_mut()
                            .get_mut(<UInt as TryInto<usize>>::try_into(ret_addr)?)
                        else {
                            return Err(NvmError::MemoryWriteError {
                                pos: ret_addr,
                                len: ret_size,
                            });
                        };
                        let ret = addr_of_mut!(*ret).cast();
                        let f = match l {
                            0 => None,
                            // SAFETY: `usize` to function pointer transmute.
                            _ => unsafe {
                                Some(std::mem::transmute(<UInt as TryInto<usize>>::try_into(l)?))
                            },
                        };
                        // SAFETY: The safety of this operation is documented by it's `Op`.
                        unsafe {
                            libffi::raw::ffi_call(cif.as_mut_ptr(), f, ret, args.as_mut_ptr());
                        }
                    }
                }
                OpCode::FreeLib => {
                    #[cfg(feature = "std")]
                    {
                        let r = self.reg(memory.read::<u8>(checked_add!(ip, 1)?)?.try_into()?)?;
                        // SAFETY: The safety of this operation is documented by it's `Op`.
                        unsafe { drop(Box::from_raw(r as *mut Library)) };
                    }
                }
            }
        }
    }
}
