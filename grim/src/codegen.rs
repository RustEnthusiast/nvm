use crate::parser::{Instruction, Item};
use nvm::opcode::OpCode;

/// Generates NVM bytecode from a collection of items.
pub(super) fn gen_bytecode(items: &[Item]) -> Vec<u8> {
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
                bytes.extend(bytemuck::bytes_of(&n));
            }
            Item::Instruction(Instruction::Push(r)) => bytes.extend([OpCode::Push as _, r]),
            Item::Instruction(Instruction::PushConst(n)) => {
                bytes.push(OpCode::PushConst as _);
                bytes.extend(bytemuck::bytes_of(&n));
            }
            Item::Instruction(Instruction::Pop(r)) => bytes.extend([OpCode::Pop as _, r]),
            Item::Instruction(Instruction::Add(r1, r2)) => bytes.extend([OpCode::Add as _, r1, r2]),
            Item::Instruction(Instruction::AddConst(r, n)) => {
                bytes.extend([OpCode::AddConst as _, r]);
                bytes.extend(bytemuck::bytes_of(&n));
            }
            Item::Instruction(Instruction::Sub(r1, r2)) => bytes.extend([OpCode::Sub as _, r1, r2]),
            Item::Instruction(Instruction::SubConst(r, n)) => {
                bytes.extend([OpCode::SubConst as _, r]);
                bytes.extend(bytemuck::bytes_of(&n));
            }
            Item::Instruction(Instruction::Mul(r1, r2)) => bytes.extend([OpCode::Mul as _, r1, r2]),
            Item::Instruction(Instruction::MulConst(r, n)) => {
                bytes.extend([OpCode::MulConst as _, r]);
                bytes.extend(bytemuck::bytes_of(&n));
            }
            Item::Instruction(Instruction::Div(r1, r2)) => bytes.extend([OpCode::Div as _, r1, r2]),
            Item::Instruction(Instruction::DivConst(r, n)) => {
                bytes.extend([OpCode::DivConst as _, r]);
                bytes.extend(bytemuck::bytes_of(&n));
            }
            Item::Instruction(Instruction::LoadLib) => bytes.push(OpCode::LoadLib as _),
            Item::Instruction(Instruction::LoadSym) => bytes.push(OpCode::LoadSym as _),
            Item::Instruction(Instruction::Syscall) => bytes.push(OpCode::Syscall as _),
            Item::Instruction(Instruction::FreeLib) => bytes.push(OpCode::FreeLib as _),
        }
    }
    bytes
}
