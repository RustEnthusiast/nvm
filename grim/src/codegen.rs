use crate::{
    parser::{Instruction, Int, Item, RegConst, Static, UInt},
    Endianness,
};
use nvm::opcode::OpCode;
use std::collections::HashMap;

/// Describes a value that has endianness.
trait HasEndianness {
    /// Interprets this data as bytes based on `endianness`.
    fn as_endian_bytes(&self, endianness: Endianness) -> Vec<u8>;
}
impl HasEndianness for UInt {
    /// Interprets this data as bytes based on `endianness`.
    fn as_endian_bytes(&self, endianness: Endianness) -> Vec<u8> {
        match endianness {
            Endianness::Native => match self {
                Self::USize(n) => n.to_ne_bytes().into(),
                Self::U8(n) => n.to_ne_bytes().into(),
                Self::U16(n) => n.to_ne_bytes().into(),
                Self::U32(n) => n.to_ne_bytes().into(),
                Self::U64(n) => n.to_ne_bytes().into(),
                Self::U128(n) => n.to_ne_bytes().into(),
            },
            Endianness::Little => match self {
                Self::USize(n) => n.to_le_bytes().into(),
                Self::U8(n) => n.to_le_bytes().into(),
                Self::U16(n) => n.to_le_bytes().into(),
                Self::U32(n) => n.to_le_bytes().into(),
                Self::U64(n) => n.to_le_bytes().into(),
                Self::U128(n) => n.to_le_bytes().into(),
            },
            Endianness::Big => match self {
                Self::USize(n) => n.to_be_bytes().into(),
                Self::U8(n) => n.to_be_bytes().into(),
                Self::U16(n) => n.to_be_bytes().into(),
                Self::U32(n) => n.to_be_bytes().into(),
                Self::U64(n) => n.to_be_bytes().into(),
                Self::U128(n) => n.to_be_bytes().into(),
            },
        }
    }
}
impl HasEndianness for Int {
    /// Interprets this data as bytes based on `endianness`.
    fn as_endian_bytes(&self, endianness: Endianness) -> Vec<u8> {
        match endianness {
            Endianness::Native => match self {
                Self::ISize(n) => n.to_ne_bytes().into(),
                Self::I8(n) => n.to_ne_bytes().into(),
                Self::I16(n) => n.to_ne_bytes().into(),
                Self::I32(n) => n.to_ne_bytes().into(),
                Self::I64(n) => n.to_ne_bytes().into(),
                Self::I128(n) => n.to_ne_bytes().into(),
            },
            Endianness::Little => match self {
                Self::ISize(n) => n.to_le_bytes().into(),
                Self::I8(n) => n.to_le_bytes().into(),
                Self::I16(n) => n.to_le_bytes().into(),
                Self::I32(n) => n.to_le_bytes().into(),
                Self::I64(n) => n.to_le_bytes().into(),
                Self::I128(n) => n.to_le_bytes().into(),
            },
            Endianness::Big => match self {
                Self::ISize(n) => n.to_be_bytes().into(),
                Self::I8(n) => n.to_be_bytes().into(),
                Self::I16(n) => n.to_be_bytes().into(),
                Self::I32(n) => n.to_be_bytes().into(),
                Self::I64(n) => n.to_be_bytes().into(),
                Self::I128(n) => n.to_be_bytes().into(),
            },
        }
    }
}

/// Gets a numeric constant or the location of an identifier.
///
/// # Panics
///
/// This operation panics if the identifier could not be found.
fn get_reg_const(n: &RegConst, locations: &HashMap<&str, UInt>) -> UInt {
    match n {
        RegConst::UInt(n) => *n,
        RegConst::Int(n) => (*n).into(),
        RegConst::Ident(ident) => match locations.get(ident) {
            Some(loc) => *loc,
            _ => panic!("failed to get the location of `{ident}`"),
        },
    }
}

/// Generates NVM bytecode from a collection of items.
pub(super) fn gen_bytecode<'tok, I: IntoIterator<Item = Item<'tok>>>(
    items: I,
    locations: &HashMap<&str, UInt>,
    endianness: Endianness,
) -> Vec<u8> {
    let mut bytes = Vec::new();
    for item in items {
        match item {
            Item::Static(Static::UInt(n)) => bytes.extend(n.as_endian_bytes(endianness)),
            Item::Static(Static::Int(n)) => bytes.extend(n.as_endian_bytes(endianness)),
            Item::Static(Static::String(s)) => bytes.extend(s.as_bytes()),
            Item::Instruction(Instruction::Exit(r)) => bytes.extend([OpCode::Exit as _, r]),
            Item::Instruction(Instruction::Nop) => bytes.push(OpCode::Nop as _),
            Item::Instruction(Instruction::Move(r1, r2)) => {
                bytes.extend([OpCode::Move as _, r1, r2]);
            }
            Item::Instruction(Instruction::MoveConst(r, n)) => {
                bytes.extend([OpCode::MoveConst as _, r]);
                let n = get_reg_const(&n, locations);
                bytes.extend(n.as_endian_bytes(endianness));
            }
            Item::Instruction(Instruction::Load(r1, r2)) => {
                bytes.extend([OpCode::Load as _, r1, r2]);
            }
            Item::Instruction(Instruction::LoadNum(r1, r2, n)) => {
                bytes.extend([OpCode::LoadNum as _, r1, r2, n]);
            }
            Item::Instruction(Instruction::Store(r1, r2)) => {
                bytes.extend([OpCode::Store as _, r1, r2]);
            }
            Item::Instruction(Instruction::StoreNum(r1, r2, n)) => {
                bytes.extend([OpCode::StoreNum as _, r1, r2, n]);
            }
            Item::Instruction(Instruction::Push(r)) => bytes.extend([OpCode::Push as _, r]),
            Item::Instruction(Instruction::PushNum(r, n)) => {
                bytes.extend([OpCode::PushNum as _, r, n]);
            }
            Item::Instruction(Instruction::Pop(r)) => bytes.extend([OpCode::Pop as _, r]),
            Item::Instruction(Instruction::PopNum(r, n)) => {
                bytes.extend([OpCode::PopNum as _, r, n]);
            }
            Item::Instruction(Instruction::Neg(r)) => bytes.extend([OpCode::Neg as _, r]),
            Item::Instruction(Instruction::Add(r1, r2)) => bytes.extend([OpCode::Add as _, r1, r2]),
            Item::Instruction(Instruction::AddI(r1, r2)) => {
                bytes.extend([OpCode::AddI as _, r1, r2]);
            }
            Item::Instruction(Instruction::Sub(r1, r2)) => bytes.extend([OpCode::Sub as _, r1, r2]),
            Item::Instruction(Instruction::SubI(r1, r2)) => {
                bytes.extend([OpCode::SubI as _, r1, r2]);
            }
            Item::Instruction(Instruction::Mul(r1, r2)) => bytes.extend([OpCode::Mul as _, r1, r2]),
            Item::Instruction(Instruction::MulI(r1, r2)) => {
                bytes.extend([OpCode::MulI as _, r1, r2]);
            }
            Item::Instruction(Instruction::Div(r1, r2)) => bytes.extend([OpCode::Div as _, r1, r2]),
            Item::Instruction(Instruction::DivI(r1, r2)) => {
                bytes.extend([OpCode::DivI as _, r1, r2]);
            }
            Item::Instruction(Instruction::Not(r)) => bytes.extend([OpCode::Not as _, r]),
            Item::Instruction(Instruction::And(r1, r2)) => bytes.extend([OpCode::And as _, r1, r2]),
            Item::Instruction(Instruction::Or(r1, r2)) => bytes.extend([OpCode::Or as _, r1, r2]),
            Item::Instruction(Instruction::Xor(r1, r2)) => bytes.extend([OpCode::Xor as _, r1, r2]),
            Item::Instruction(Instruction::Shl(r1, r2)) => bytes.extend([OpCode::Shl as _, r1, r2]),
            Item::Instruction(Instruction::Shr(r1, r2)) => bytes.extend([OpCode::Shr as _, r1, r2]),
            Item::Instruction(Instruction::Call(n)) => {
                bytes.push(OpCode::Call as _);
                let n = get_reg_const(&n, locations);
                bytes.extend(n.as_endian_bytes(endianness));
            }
            Item::Instruction(Instruction::Return) => bytes.push(OpCode::Return as _),
            Item::Instruction(Instruction::Cmp(r1, r2)) => bytes.extend([OpCode::Cmp as _, r1, r2]),
            Item::Instruction(Instruction::Jmp(n)) => {
                bytes.push(OpCode::Jmp as _);
                let n = get_reg_const(&n, locations);
                bytes.extend(n.as_endian_bytes(endianness));
            }
            Item::Instruction(Instruction::JZ(n)) => {
                bytes.push(OpCode::JZ as _);
                let n = get_reg_const(&n, locations);
                bytes.extend(n.as_endian_bytes(endianness));
            }
            Item::Instruction(Instruction::JNZ(n)) => {
                bytes.push(OpCode::JNZ as _);
                let n = get_reg_const(&n, locations);
                bytes.extend(n.as_endian_bytes(endianness));
            }
            Item::Instruction(Instruction::JO(n)) => {
                bytes.push(OpCode::JO as _);
                let n = get_reg_const(&n, locations);
                bytes.extend(n.as_endian_bytes(endianness));
            }
            Item::Instruction(Instruction::JNO(n)) => {
                bytes.push(OpCode::JNO as _);
                let n = get_reg_const(&n, locations);
                bytes.extend(n.as_endian_bytes(endianness));
            }
            Item::Instruction(Instruction::JC(n)) => {
                bytes.push(OpCode::JC as _);
                let n = get_reg_const(&n, locations);
                bytes.extend(n.as_endian_bytes(endianness));
            }
            Item::Instruction(Instruction::JNC(n)) => {
                bytes.push(OpCode::JNC as _);
                let n = get_reg_const(&n, locations);
                bytes.extend(n.as_endian_bytes(endianness));
            }
            Item::Instruction(Instruction::JS(n)) => {
                bytes.push(OpCode::JS as _);
                let n = get_reg_const(&n, locations);
                bytes.extend(n.as_endian_bytes(endianness));
            }
            Item::Instruction(Instruction::JNS(n)) => {
                bytes.push(OpCode::JNS as _);
                let n = get_reg_const(&n, locations);
                bytes.extend(n.as_endian_bytes(endianness));
            }
            Item::Instruction(Instruction::JE(n)) => {
                bytes.push(OpCode::JE as _);
                let n = get_reg_const(&n, locations);
                bytes.extend(n.as_endian_bytes(endianness));
            }
            Item::Instruction(Instruction::JNE(n)) => {
                bytes.push(OpCode::JNE as _);
                let n = get_reg_const(&n, locations);
                bytes.extend(n.as_endian_bytes(endianness));
            }
            Item::Instruction(Instruction::JA(n)) => {
                bytes.push(OpCode::JA as _);
                let n = get_reg_const(&n, locations);
                bytes.extend(n.as_endian_bytes(endianness));
            }
            Item::Instruction(Instruction::JAE(n)) => {
                bytes.push(OpCode::JAE as _);
                let n = get_reg_const(&n, locations);
                bytes.extend(n.as_endian_bytes(endianness));
            }
            Item::Instruction(Instruction::JB(n)) => {
                bytes.push(OpCode::JB as _);
                let n = get_reg_const(&n, locations);
                bytes.extend(n.as_endian_bytes(endianness));
            }
            Item::Instruction(Instruction::JBE(n)) => {
                bytes.push(OpCode::JBE as _);
                let n = get_reg_const(&n, locations);
                bytes.extend(n.as_endian_bytes(endianness));
            }
            Item::Instruction(Instruction::JG(n)) => {
                bytes.push(OpCode::JG as _);
                let n = get_reg_const(&n, locations);
                bytes.extend(n.as_endian_bytes(endianness));
            }
            Item::Instruction(Instruction::JGE(n)) => {
                bytes.push(OpCode::JGE as _);
                let n = get_reg_const(&n, locations);
                bytes.extend(n.as_endian_bytes(endianness));
            }
            Item::Instruction(Instruction::JL(n)) => {
                bytes.push(OpCode::JL as _);
                let n = get_reg_const(&n, locations);
                bytes.extend(n.as_endian_bytes(endianness));
            }
            Item::Instruction(Instruction::JLE(n)) => {
                bytes.push(OpCode::JLE as _);
                let n = get_reg_const(&n, locations);
                bytes.extend(n.as_endian_bytes(endianness));
            }
            Item::Instruction(Instruction::LoadLib(r)) => bytes.extend([OpCode::LoadLib as _, r]),
            Item::Instruction(Instruction::LoadSym(r1, r2)) => {
                bytes.extend([OpCode::LoadSym as _, r1, r2]);
            }
            Item::Instruction(Instruction::Syscall(r1, r2)) => {
                bytes.extend([OpCode::Syscall as _, r1, r2]);
            }
            Item::Instruction(Instruction::FreeLib(r)) => bytes.extend([OpCode::FreeLib as _, r]),
        }
    }
    bytes
}
