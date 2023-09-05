use crate::parser::{Const, Instruction, Item};
use nvm::opcode::OpCode;
use std::collections::HashMap;

/// Generates NVM bytecode from a collection of items.
pub(super) fn gen_bytecode(items: &[Item], locations: &HashMap<&str, usize>) -> Vec<u8> {
    let mut bytes = Vec::new();
    for item in items {
        match *item {
            Item::Instruction(Instruction::Exit) => bytes.push(OpCode::Exit as _),
            Item::Instruction(Instruction::Nop) => bytes.push(OpCode::Nop as _),
            Item::Instruction(Instruction::Jump(r)) => bytes.extend([OpCode::Jump as _, r]),
            Item::Instruction(Instruction::Move(r1, r2)) => {
                bytes.extend([OpCode::Move as _, r1, r2]);
            }
            Item::Instruction(Instruction::MoveConst(r, n)) => {
                bytes.extend([OpCode::MoveConst as _, r]);
                let n = match n {
                    Const::Num(n) => n,
                    Const::Ident(ident) => match locations.get(ident) {
                        Some(loc) => *loc,
                        _ => panic!("failed to get the location of `{ident}`"),
                    },
                };
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
            Item::Instruction(Instruction::Pop(r)) => bytes.extend([OpCode::Pop as _, r]),
            Item::Instruction(Instruction::Add(r1, r2)) => bytes.extend([OpCode::Add as _, r1, r2]),
            Item::Instruction(Instruction::Sub(r1, r2)) => bytes.extend([OpCode::Sub as _, r1, r2]),
            Item::Instruction(Instruction::Mul(r1, r2)) => bytes.extend([OpCode::Mul as _, r1, r2]),
            Item::Instruction(Instruction::Div(r1, r2)) => bytes.extend([OpCode::Div as _, r1, r2]),
            Item::Instruction(Instruction::LoadLib) => bytes.push(OpCode::LoadLib as _),
            Item::Instruction(Instruction::LoadSym) => bytes.push(OpCode::LoadSym as _),
            Item::Instruction(Instruction::Syscall) => bytes.push(OpCode::Syscall as _),
            Item::Instruction(Instruction::FreeLib) => bytes.push(OpCode::FreeLib as _),
        }
    }
    bytes
}
