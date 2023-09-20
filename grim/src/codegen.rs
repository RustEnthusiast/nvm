use crate::parser::{Instruction, Item, RegConst, Static};
use nvm::opcode::OpCode;
use std::collections::HashMap;

/// Gets a numeric constant or the location of an identifier.
///
/// # Panics
///
/// This operation panics if the identifier could not be found.
fn get_reg_const(n: &RegConst, locations: &HashMap<&str, usize>) -> usize {
    match n {
        RegConst::UInt(n) => *n,
        RegConst::Int(n) => *n as _,
        RegConst::Ident(ident) => match locations.get(ident) {
            Some(loc) => *loc,
            _ => panic!("failed to get the location of `{ident}`"),
        },
    }
}

/// Generates NVM bytecode from a collection of items.
pub(super) fn gen_bytecode<'tok, I: IntoIterator<Item = Item<'tok>>>(
    items: I,
    locations: &HashMap<&str, usize>,
) -> Vec<u8> {
    let mut bytes = Vec::new();
    for item in items {
        match item {
            Item::Static(Static::UInt(n)) => bytes.extend(bytemuck::bytes_of(&n)),
            Item::Static(Static::Int(n)) => bytes.extend(bytemuck::bytes_of(&n)),
            Item::Static(Static::U8(n)) => bytes.extend(bytemuck::bytes_of(&n)),
            Item::Static(Static::I8(n)) => bytes.extend(bytemuck::bytes_of(&n)),
            Item::Static(Static::U16(n)) => bytes.extend(bytemuck::bytes_of(&n)),
            Item::Static(Static::I16(n)) => bytes.extend(bytemuck::bytes_of(&n)),
            Item::Static(Static::U32(n)) => bytes.extend(bytemuck::bytes_of(&n)),
            Item::Static(Static::I32(n)) => bytes.extend(bytemuck::bytes_of(&n)),
            Item::Static(Static::U64(n)) => bytes.extend(bytemuck::bytes_of(&n)),
            Item::Static(Static::I64(n)) => bytes.extend(bytemuck::bytes_of(&n)),
            Item::Static(Static::String(s)) => bytes.extend(s.as_bytes()),
            Item::Instruction(Instruction::Exit(r)) => bytes.extend([OpCode::Exit as _, r]),
            Item::Instruction(Instruction::Nop) => bytes.push(OpCode::Nop as _),
            Item::Instruction(Instruction::Jump(n)) => {
                bytes.push(OpCode::Jump as _);
                let n = get_reg_const(&n, locations);
                bytes.extend(bytemuck::bytes_of(&n));
            }
            Item::Instruction(Instruction::Move(r1, r2)) => {
                bytes.extend([OpCode::Move as _, r1, r2]);
            }
            Item::Instruction(Instruction::MoveConst(r, n)) => {
                bytes.extend([OpCode::MoveConst as _, r]);
                let n = get_reg_const(&n, locations);
                bytes.extend(bytemuck::bytes_of(&n));
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
            Item::Instruction(Instruction::Add(r1, r2)) => bytes.extend([OpCode::Add as _, r1, r2]),
            Item::Instruction(Instruction::Sub(r1, r2)) => bytes.extend([OpCode::Sub as _, r1, r2]),
            Item::Instruction(Instruction::Mul(r1, r2)) => bytes.extend([OpCode::Mul as _, r1, r2]),
            Item::Instruction(Instruction::Div(r1, r2)) => bytes.extend([OpCode::Div as _, r1, r2]),
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
