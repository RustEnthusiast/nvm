//! Represents an NVM operation code.
use num_derive::FromPrimitive;

/// Represents an NVM operation code.
#[repr(u8)]
#[derive(FromPrimitive)]
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
    /// Copies a value from memory into a register.
    ///
    /// - `u8 i1` - The index of the destination register.
    ///
    /// - `u8 i2` - The index of the register holding the memory location.
    Load,
    /// Copies a specific number of bytes from memory into a register.
    ///
    /// - `u8 i1` - The index of the destination register.
    ///
    /// - `u8 i2` - The index of the register holding the memory location.
    ///
    /// - `u8 n` - The number of bytes to transfer.
    LoadNum,
    /// Copies a value from a register into memory.
    ///
    /// - `u8 i1` - The index of the register holding the memory location.
    ///
    /// - `u8 i2` - The index of the source register.
    Store,
    /// Copies a specific number of bytes from a register into memory.
    ///
    /// - `u8 i1` - The index of the register holding the memory location.
    ///
    /// - `u8 i2` - The index of the source register.
    ///
    /// - `u8 n` - The number of bytes to transfer.
    StoreNum,
    /// Pushes a value onto the stack.
    ///
    /// # Format arguments
    ///
    /// - `u8 i` - The index of the register that contains the value to push onto the stack.
    Push,
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
    /// Subtracts the `uint` value in the register at index `i2` from the `uint` value in the
    /// register at index `i1`.
    ///
    /// # Format arguments
    ///
    /// - `u8 i1` - The index of the register to subtract from.
    ///
    /// - `u8 i2` - The index of the source register.
    Sub,
    /// Multiplies the `uint` value in the register at index `i2` with the `uint` value in the
    /// register at index `i1`.
    ///
    /// # Format arguments
    ///
    /// - `u8 i1` - The index of the register to multiply.
    ///
    /// - `u8 i2` - The index of the source register.
    Mul,
    /// Divides the `uint` value in the register at index `i2` by the `uint` value in the
    /// register at index `i1`.
    ///
    /// # Format arguments
    ///
    /// - `u8 i1` - The index of the register to divide.
    ///
    /// - `u8 i2` - The index of the source register.
    Div,
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
    /// Returns the size of this opcode's instruction.
    #[allow(clippy::arithmetic_side_effects)]
    pub const fn size(&self) -> usize {
        match *self {
            Self::Exit
            | Self::Nop
            | Self::Syscall
            | Self::LoadLib
            | Self::LoadSym
            | Self::FreeLib => 1,
            Self::Jump | Self::Push | Self::Pop => 2,
            Self::Move
            | Self::Load
            | Self::Store
            | Self::Add
            | Self::Sub
            | Self::Mul
            | Self::Div => 3,
            Self::LoadNum | Self::StoreNum => 4,
            Self::MoveConst => 2 + core::mem::size_of::<usize>(),
        }
    }
}
