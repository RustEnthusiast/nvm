//! Represents an NVM operation code.
use super::NvmError;

/// Represents an NVM operation code.
#[repr(u8)]
pub enum OpCode {
    /// Exits the program with a given exit code.
    ///
    /// # Register arguments
    ///
    /// - `R0` - The `uint` value to exit the program with.
    Exit,
    /// No operation, does nothing.
    Nop,
    /// Jumps to another location in memory.
    ///
    /// # Format arguments
    ///
    /// - `u8 i` - The index of the register that contains the memory location to jump to.
    Jump,
    /// Copies the value of one register to another.
    ///
    /// # Format arguments
    ///
    /// - `u8 i1` - The index of the destination register.
    ///
    /// - `u8 i2` - The index of the source register.
    Move,
    /// Copies a constant value into a register.
    ///
    /// # Format arguments
    ///
    /// - `u8 i` - The index of the destination register.
    ///
    /// - `uint value` - The value to move into the destination register.
    MoveConst,
    /// Pushes a value onto the stack.
    ///
    /// # Format arguments
    ///
    /// - `u8 i` - The index of the register that contains the value to push onto the stack.
    Push,
    /// Pushes a constant value onto the stack.
    ///
    /// # Format arguments
    ///
    /// - `uint value` - The value to push onto the stack.
    PushConst,
    /// Pops a value off of the stack into a register.
    ///
    /// # Format arguments
    ///
    /// - `u8 i` - The index of the register to pop data into.
    Pop,
    /// Adds the `uint` value in the register at index `i2` to the `uint` value in the register at
    /// index `i1`.
    ///
    /// # Format arguments
    ///
    /// - `u8 i1` - The index of the register to add to.
    ///
    /// - `u8 i2` - The index of the source register.
    Add,
    /// Adds a constant `uint` value to the `uint` value in the register at index `i`.
    ///
    /// # Format arguments
    ///
    /// - `u8 i` - The index of the register to add to.
    ///
    /// - `uint value` - The source value.
    AddConst,
    /// Subtracts the `uint` value in the register at index `i2` from the `uint` value in the
    /// register at index `i1`.
    ///
    /// # Format arguments
    ///
    /// - `u8 i1` - The index of the register to subtract from.
    ///
    /// - `u8 i2` - The index of the source register.
    Sub,
    /// Subtracts a constant `uint` value from the `uint` value in the register at index `i`.
    ///
    /// # Format arguments
    ///
    /// - `u8 i` - The index of the register to subtract from.
    ///
    /// - `uint value` - The source value.
    SubConst,
    /// Multiplies the `uint` value in the register at index `i2` with the `uint` value in the
    /// register at index `i1`.
    ///
    /// # Format arguments
    ///
    /// - `u8 i1` - The index of the register to multiply.
    ///
    /// - `u8 i2` - The index of the source register.
    Mul,
    /// Multiplies a constant `uint` value with the `uint` value in the register at index `i`.
    ///
    /// # Format arguments
    ///
    /// - `u8 i` - The index of the register to multiply.
    ///
    /// - `uint value` - The source value.
    MulConst,
    /// Divides the `uint` value in the register at index `i2` by the `uint` value in the
    /// register at index `i1`.
    ///
    /// # Format arguments
    ///
    /// - `u8 i1` - The index of the register to divide.
    ///
    /// - `u8 i2` - The index of the source register.
    Div,
    /// Divides a constant `uint` value by the `uint` value in the register at index `i`.
    ///
    /// # Format arguments
    ///
    /// - `u8 i` - The index of the register to divide.
    ///
    /// - `uint value` - The source value.
    DivConst,
    /// Loads a native dynamic library.
    ///
    /// The library handle is stored in the register at index 0.
    ///
    /// # Register arguments
    ///
    /// - `R0` - The memory location of the null-terminated C string containing to the name of the
    /// library to load.
    ///
    /// # Safety
    ///
    /// - Unsafe initialization routines may be ran when the library is loaded.
    ///
    /// - `R0` must point to a null terminated sequence of bytes.
    LoadLib,
    /// Loads a native library symbol.
    ///
    /// The library symbol is stored in the register at index 0.
    ///
    /// # Register arguments
    ///
    /// - `R0` - A handle to the native library to load the symbol from.
    ///
    /// - `R1` - The memory location of the null-terminated C string containing to the name of the
    /// symbol to load.
    ///
    /// # Safety
    ///
    /// - `R0` must contain a valid handle to a native system library.
    ///
    /// - `R1` must point to a null terminated sequence of bytes.
    LoadSym,
    /// Makes a C call to a native external library symbol.
    ///
    /// Arguments are passed on the stack.
    ///
    /// Argument format: `[type, value]`
    ///
    /// Types:
    ///
    /// - 0 - `uint`
    ///
    /// # Register arguments
    ///
    /// - `R0` - The symbol to call.
    ///
    /// - `R1` - The number of arguments the symbol takes.
    Syscall,
    /// Frees a loaded native dynamic library.
    ///
    /// # Register arguments
    ///
    /// - `R0` - A handle to the native library to free.
    ///
    /// # Safety
    ///
    /// - `R0` must contain a valid handle to a native system library.
    FreeLib,
}
impl OpCode {
    /// [u8] constant for exit.
    pub const EXIT: u8 = Self::Exit as _;
    /// [u8] constant for no operation.
    pub const NOP: u8 = Self::Nop as _;
    /// [u8] constant for jump.
    pub const JUMP: u8 = Self::Jump as _;
    /// [u8] constant for move.
    pub const MOVE: u8 = Self::Move as _;
    /// [u8] constant for move constant.
    pub const MOVE_CONST: u8 = Self::MoveConst as _;
    /// [u8] constant for push.
    pub const PUSH: u8 = Self::Push as _;
    /// [u8] constant for push constant.
    pub const PUSH_CONST: u8 = Self::PushConst as _;
    /// [u8] constant for pop.
    pub const POP: u8 = Self::Pop as _;
    /// [u8] constant for add.
    pub const ADD: u8 = Self::Add as _;
    /// [u8] constant for add const.
    pub const ADD_CONST: u8 = Self::AddConst as _;
    /// [u8] constant for sub.
    pub const SUB: u8 = Self::Sub as _;
    /// [u8] constant for sub const.
    pub const SUB_CONST: u8 = Self::SubConst as _;
    /// [u8] constant for mul.
    pub const MUL: u8 = Self::Mul as _;
    /// [u8] constant for mul const.
    pub const MUL_CONST: u8 = Self::MulConst as _;
    /// [u8] constant for div.
    pub const DIV: u8 = Self::Div as _;
    /// [u8] constant for div const.
    pub const DIV_CONST: u8 = Self::DivConst as _;
    /// [u8] constant for load lib.
    pub const LOAD_LIB: u8 = Self::LoadLib as _;
    /// [u8] constant for load sym.
    pub const LOAD_SYM: u8 = Self::LoadSym as _;
    /// [u8] constant for syscall.
    pub const SYSCALL: u8 = Self::Syscall as _;
    /// [u8] constant for free lib.
    pub const FREE_LIB: u8 = Self::FreeLib as _;

    /// Returns the size of this opcode's instruction.
    #[allow(clippy::arithmetic_side_effects, clippy::arithmetic_side_effects)]
    pub(super) const fn size(&self) -> usize {
        match *self {
            Self::Exit
            | Self::Nop
            | Self::Syscall
            | Self::LoadLib
            | Self::LoadSym
            | Self::FreeLib => 1,
            Self::Jump | Self::Push | Self::Pop => 2,
            Self::Move | Self::Add | Self::Sub | Self::Mul | Self::Div => 3,
            Self::PushConst => 1 + core::mem::size_of::<usize>(),
            Self::MoveConst | Self::AddConst | Self::SubConst | Self::MulConst | Self::DivConst => {
                2 + core::mem::size_of::<usize>()
            }
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
            Self::JUMP => Ok(Self::Jump),
            Self::MOVE => Ok(Self::Move),
            Self::MOVE_CONST => Ok(Self::MoveConst),
            Self::PUSH => Ok(Self::Push),
            Self::PUSH_CONST => Ok(Self::PushConst),
            Self::POP => Ok(Self::Pop),
            Self::ADD => Ok(Self::Add),
            Self::ADD_CONST => Ok(Self::AddConst),
            Self::SUB => Ok(Self::Sub),
            Self::SUB_CONST => Ok(Self::SubConst),
            Self::MUL => Ok(Self::Mul),
            Self::MUL_CONST => Ok(Self::MulConst),
            Self::DIV => Ok(Self::Div),
            Self::DIV_CONST => Ok(Self::DivConst),
            Self::LOAD_LIB => Ok(Self::LoadLib),
            Self::LOAD_SYM => Ok(Self::LoadSym),
            Self::SYSCALL => Ok(Self::Syscall),
            Self::FREE_LIB => Ok(Self::FreeLib),
            _ => Err(NvmError::InvalidOperation(value)),
        }
    }
}
