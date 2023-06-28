//! Represents an NVM operation code.
use super::NvmError;

/// Represents an NVM operation code.
#[repr(u8)]
pub enum OpCode {
    /// Exit operation.
    Exit,
    /// No operation.
    Nop,
    /// The jump operation.
    Jump,
    /// The move operation.
    Move,
    /// The move constant operation.
    MoveConst,
    /// The add operation.
    Add,
    /// The add const operation.
    AddConst,
    /// The sub operation.
    Sub,
    /// The sub const operation.
    SubConst,
    /// The mul operation.
    Mul,
    /// The mul const operation.
    MulConst,
    /// The div operation.
    Div,
    /// The div const operation.
    DivConst,
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

    /// Returns the size of this opcode's instruction.
    #[allow(clippy::arithmetic_side_effects, clippy::integer_arithmetic)]
    pub(super) const fn size(&self) -> usize {
        match *self {
            Self::Exit | Self::Nop => 1,
            Self::Jump => 2,
            Self::Move | Self::Add | Self::Sub | Self::Mul | Self::Div => 3,
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
            Self::ADD => Ok(Self::Add),
            Self::ADD_CONST => Ok(Self::AddConst),
            Self::SUB => Ok(Self::Sub),
            Self::SUB_CONST => Ok(Self::SubConst),
            Self::MUL => Ok(Self::Mul),
            Self::MUL_CONST => Ok(Self::MulConst),
            Self::DIV => Ok(Self::Div),
            Self::DIV_CONST => Ok(Self::DivConst),
            _ => Err(NvmError::InvalidOperation(value)),
        }
    }
}
