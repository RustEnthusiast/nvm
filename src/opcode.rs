//! Represents an NVM operation code.
use super::NvmError;

/// Represents an NVM operation code.
#[repr(u8)]
pub enum OpCode {
    /// Exit operation.
    Exit,
    /// No operation.
    Nop,
    /// The move operation.
    Move,
    /// The move constant operation.
    MoveConst,
}
impl OpCode {
    /// [u8] constant for exit.
    pub const EXIT: u8 = Self::Exit as _;
    /// [u8] constant for no operation.
    pub const NOP: u8 = Self::Nop as _;
    /// [u8] constant for move.
    pub const MOVE: u8 = Self::Move as _;
    /// [u8] constant for move constant.
    pub const MOVE_CONST: u8 = Self::MoveConst as _;

    /// Returns the size of this opcode's instruction.
    #[allow(clippy::arithmetic_side_effects, clippy::integer_arithmetic)]
    pub(super) const fn size(&self) -> usize {
        match *self {
            Self::Exit | Self::Nop => 1,
            Self::Move => 3,
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
            Self::MOVE => Ok(Self::Move),
            Self::MOVE_CONST => Ok(Self::MoveConst),
            _ => Err(NvmError::InvalidOperation(value)),
        }
    }
}
