//! Represents an NVM operation code.
use num_derive::FromPrimitive;

/// Represents an NVM operation code.
#[repr(u8)]
#[derive(Clone, Copy, Debug, FromPrimitive)]
pub enum OpCode {
    /// Exits the program with a given exit code.
    ///
    /// # Format arguments
    ///
    /// - `u8 i` - The index of the register holding the value to exit the program with.
    Exit,
    /// No operation, does nothing.
    Nop,
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
    /// Pushes a specific number of bytes from a register onto the stack.
    ///
    /// # Format arguments
    ///
    /// - `u8 i` - The index of the register that contains the value to push onto the stack.
    ///
    /// - `u8 n` - The number of bytes to push.
    PushNum,
    /// Pops a value off of the stack into a register.
    ///
    /// # Format arguments
    ///
    /// - `u8 i` - The index of the register to pop data into.
    Pop,
    /// Pops a specific number of bytes off of the stack into a register.
    ///
    /// # Format arguments
    ///
    /// - `u8 i` - The index of the register to pop data into.
    ///
    /// - `u8 n` - The number of bytes to pop.
    PopNum,
    /// Negates the `uint` value in the register at index `i`.
    ///
    /// # Format arguments
    ///
    /// - `u8 i` - The index of the register to negate.
    Neg,
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
    /// Performs a bitwise not operation on the `uint` value in the register at index `i`.
    ///
    /// # Format arguments
    ///
    /// - `u8 i` - The index of the register.
    Not,
    /// Performs a bitwise and operation on the `uint` values in the registers at index `i1` and
    /// `i2`.
    ///
    /// # Format arguments
    ///
    /// - `u8 i1` - The index of the destination register.
    ///
    /// - `u8 i2` - The index of the source register.
    And,
    /// Performs a bitwise or operation on the `uint` values in the registers at index `i1` and
    /// `i2`.
    ///
    /// # Format arguments
    ///
    /// - `u8 i1` - The index of the destination register.
    ///
    /// - `u8 i2` - The index of the source register.
    Or,
    /// Performs a bitwise xor operation on the `uint` values in the registers at index `i1` and
    /// `i2`.
    ///
    /// # Format arguments
    ///
    /// - `u8 i1` - The index of the destination register.
    ///
    /// - `u8 i2` - The index of the source register.
    Xor,
    /// Performs a left bit shift on the `uint` value in the register at index `i1`.
    ///
    /// # Format arguments
    ///
    /// - `u8 i1` - The index of the register containing the value to shift.
    ///
    /// - `u8 i2` - The index of the register containing the number of bits to shift.
    Shl,
    /// Performs a right bit shift on the `uint` value in the register at index `i1`.
    ///
    /// # Format arguments
    ///
    /// - `u8 i1` - The index of the register containing the value to shift.
    ///
    /// - `u8 i2` - The index of the register containing the number of bits to shift.
    Shr,
    /// Pushes the instruction pointer onto the stack and jumps to a location in memory.
    ///
    /// # Format arguments
    ///
    /// - `uint i` - The memory location to jump to.
    Call,
    /// Jumps to a location stored on the stack.
    Return,
    /// Compares two register operands, updating the flags register accordingly.
    ///
    /// # Format arguments
    ///
    /// - `u8 i1` - The index of the first operand.
    ///
    /// - `u8 i2` - The index of the second operand.
    Cmp,
    /// Jumps to a location in memory.
    ///
    /// # Format arguments
    ///
    /// - `uint i` - The memory location to jump to.
    Jump,
    /// Jumps to a location in memory if the zero flag is set.
    ///
    /// # Format arguments
    ///
    /// - `uint i` - The memory location to jump to.
    JZ,
    /// Jumps to a location in memory if the zero flag is not set.
    ///
    /// # Format arguments
    ///
    /// - `uint i` - The memory location to jump to.
    JNZ,
    /// Jumps to a location in memory if the overflow flag is set.
    ///
    /// # Format arguments
    ///
    /// - `uint i` - The memory location to jump to.
    JO,
    /// Jumps to a location in memory if the overflow flag is not set.
    ///
    /// # Format arguments
    ///
    /// - `uint i` - The memory location to jump to.
    JNO,
    /// Jumps to a location in memory if the carry flag is set.
    ///
    /// # Format arguments
    ///
    /// - `uint i` - The memory location to jump to.
    JC,
    /// Jumps to a location in memory if the carry flag is not set.
    ///
    /// # Format arguments
    ///
    /// - `uint i` - The memory location to jump to.
    JNC,
    /// Jumps to a location in memory if the sign flag is set.
    ///
    /// # Format arguments
    ///
    /// - `uint i` - The memory location to jump to.
    JS,
    /// Jumps to a location in memory if the sign flag is not set.
    ///
    /// # Format arguments
    ///
    /// - `uint i` - The memory location to jump to.
    JNS,
    /// Jumps to a location in memory if the last comparison resulted in equality.
    ///
    /// # Format arguments
    ///
    /// - `uint i` - The memory location to jump to.
    JE,
    /// Jumps to a location in memory if the last comparison resulted in inequality.
    ///
    /// # Format arguments
    ///
    /// - `uint i` - The memory location to jump to.
    JNE,
    /// Jumps to a location in memory if the last comparison resulted in a greater unsigned left
    /// operand.
    ///
    /// # Format arguments
    ///
    /// - `uint i` - The memory location to jump to.
    JA,
    /// Jumps to a location in memory if the last comparison resulted in a greater or equal
    /// unsigned left operand.
    ///
    /// # Format arguments
    ///
    /// - `uint i` - The memory location to jump to.
    JAE,
    /// Jumps to a location in memory if the last comparison resulted in a lesser unsigned left
    /// operand.
    ///
    /// # Format arguments
    ///
    /// - `uint i` - The memory location to jump to.
    JB,
    /// Jumps to a location in memory if the last comparison resulted in a lesser or equal
    /// unsigned left operand.
    ///
    /// # Format arguments
    ///
    /// - `uint i` - The memory location to jump to.
    JBE,
    /// Jumps to a location in memory if the last comparison resulted in a greater signed left
    /// operand.
    ///
    /// # Format arguments
    ///
    /// - `uint i` - The memory location to jump to.
    JG,
    /// Jumps to a location in memory if the last comparison resulted in a greater or equal signed
    /// left operand.
    ///
    /// # Format arguments
    ///
    /// - `uint i` - The memory location to jump to.
    JGE,
    /// Jumps to a location in memory if the last comparison resulted in a lesser signed left
    /// operand.
    ///
    /// # Format arguments
    ///
    /// - `uint i` - The memory location to jump to.
    JL,
    /// Jumps to a location in memory if the last comparison resulted in a lesser or equal signed
    /// left operand.
    ///
    /// # Format arguments
    ///
    /// - `uint i` - The memory location to jump to.
    JLE,
    /// Loads a native dynamic library.
    ///
    /// The library handle is stored in the register at index `i`.
    ///
    /// # Format arguments
    ///
    /// - `u8 i` - The index of the register that holds the memory location of the null-terminated
    /// C string containing to the name of the library to load.
    ///
    /// # Safety
    ///
    /// - Unsafe initialization routines may be ran when the library is loaded.
    ///
    /// - `i` must point to a null terminated sequence of bytes.
    LoadLib,
    /// Loads a native library symbol.
    ///
    /// The library symbol is stored in the register at index `i1`.
    ///
    /// # Format arguments
    ///
    /// - `u8 i1` - The index of the register that holds the memory location of the null-terminated C
    /// string containing to the name of the symbol to load.
    ///
    /// - `u8 i2` - The index of the register that holds a handle to the native library to load the
    /// symbol from.
    ///
    /// # Safety
    ///
    /// - `i1` must point to a null terminated sequence of bytes.
    ///
    /// - `i2` must contain a valid handle to a native system library.
    LoadSym,
    /// Makes a C call to a native external library symbol.
    ///
    /// Arguments are passed on the stack.
    ///
    /// Argument format (reversed order on the stack): `[u8 type, value]`
    ///
    /// Types:
    ///
    /// - 0 - `void`
    ///
    /// - 1 - `void *`
    ///
    /// - 2 - `uint`
    ///
    /// - 3 - `int`
    ///
    /// - 4 - `u8`
    ///
    /// - 5 - `i8`
    ///
    /// - 6 - `u16`
    ///
    /// - 7 - `i16`
    ///
    /// - 8 - `u32`
    ///
    /// - 9 - `i32`
    ///
    /// - 10 - `u64`
    ///
    /// - 11 - `i64`
    ///
    /// - 12 - `c_uchar`
    ///
    /// - 13 - `c_schar`
    ///
    /// - 14 - `c_ushort`
    ///
    /// - 15 - `c_short`
    ///
    /// - 16 - `c_uint`
    ///
    /// - 17 - `c_int`
    ///
    /// - 18 - `c_ulong`
    ///
    /// - 19 - `c_long`
    ///
    /// - 20 - `c_ulonglong`
    ///
    /// - 21 - `c_longlong`
    ///
    /// - 22 - A structure (format: `[usize num_fields, types]`)
    ///
    /// # Format arguments
    ///
    /// - `u8 i1` - The index of the register containing the symbol to call.
    ///
    /// - `u8 i2` - The index of the register containing the number of arguments the symbol takes.
    Syscall,
    /// Frees a loaded native dynamic library.
    ///
    /// # Format arguments
    ///
    /// - `u8 i` - The index of the register holding a handle to the native library to free.
    ///
    /// # Safety
    ///
    /// - `i` must contain a valid handle to a native system library.
    FreeLib,
}
impl OpCode {
    /// Returns the size of this opcode's instruction.
    #[allow(clippy::arithmetic_side_effects)]
    pub const fn size(&self) -> usize {
        match *self {
            Self::Nop | Self::Return => 1,
            Self::Exit
            | Self::Push
            | Self::Pop
            | Self::Neg
            | Self::Not
            | Self::LoadLib
            | Self::FreeLib => 2,
            Self::Move
            | Self::Load
            | Self::Store
            | Self::PushNum
            | Self::PopNum
            | Self::Add
            | Self::Sub
            | Self::Mul
            | Self::Div
            | Self::And
            | Self::Or
            | Self::Xor
            | Self::Shl
            | Self::Shr
            | Self::Cmp
            | Self::LoadSym
            | Self::Syscall => 3,
            Self::LoadNum | Self::StoreNum => 4,
            Self::Call
            | Self::Jump
            | Self::JZ
            | Self::JNZ
            | Self::JO
            | Self::JNO
            | Self::JC
            | Self::JNC
            | Self::JS
            | Self::JNS
            | Self::JE
            | Self::JNE
            | Self::JA
            | Self::JAE
            | Self::JB
            | Self::JBE
            | Self::JG
            | Self::JGE
            | Self::JL
            | Self::JLE => 1 + core::mem::size_of::<usize>(),
            Self::MoveConst => 2 + core::mem::size_of::<usize>(),
        }
    }
}
