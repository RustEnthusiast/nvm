use crate::{
    lexer::{Token, TokenType},
    Bits,
};
use ariadne::Color;
use std::{collections::HashMap, num::ParseIntError, slice::Iter, str::FromStr};

/// An unsigned integer.
#[derive(Clone, Copy)]
pub(super) enum UInt {
    /// An unsigned host-native-bit integer.
    USize(usize),
    /// An unsigned 8-bit integer.
    U8(u8),
    /// An unsigned 16-bit integer.
    U16(u16),
    /// An unsigned 32-bit integer.
    U32(u32),
    /// An unsigned 64-bit integer.
    U64(u64),
    /// An unsigned 128-bit integer.
    U128(u128),
}
impl UInt {
    /// Converts a [`u128`] into a [`UInt`] based on `bits`.
    fn from_u128(n: u128, bits: Bits) -> Self {
        match bits {
            Bits::BitNative => Self::USize(n as _),
            Bits::Bit8 => Self::U8(n as _),
            Bits::Bit16 => Self::U16(n as _),
            Bits::Bit32 => Self::U32(n as _),
            Bits::Bit64 => Self::U64(n as _),
            Bits::Bit128 => Self::U128(n),
        }
    }

    /// Converts a string slice into a [`UInt`] based on `bits`.
    fn from_str(str: &str, bits: Bits) -> Result<Self, ParseIntError> {
        match bits {
            Bits::BitNative => Ok(Self::USize(str.parse()?)),
            Bits::Bit8 => Ok(Self::U8(str.parse()?)),
            Bits::Bit16 => Ok(Self::U16(str.parse()?)),
            Bits::Bit32 => Ok(Self::U32(str.parse()?)),
            Bits::Bit64 => Ok(Self::U64(str.parse()?)),
            Bits::Bit128 => Ok(Self::U128(str.parse()?)),
        }
    }

    /// Returns the byte representation of this integer.
    pub(super) fn as_bytes(&self) -> &[u8] {
        match self {
            Self::USize(n) => bytemuck::bytes_of(n),
            Self::U8(n) => bytemuck::bytes_of(n),
            Self::U16(n) => bytemuck::bytes_of(n),
            Self::U32(n) => bytemuck::bytes_of(n),
            Self::U64(n) => bytemuck::bytes_of(n),
            Self::U128(n) => bytemuck::bytes_of(n),
        }
    }
}
impl From<Int> for UInt {
    /// Converts an [`Int`] into a [`UInt`].
    fn from(value: Int) -> Self {
        match value {
            Int::ISize(n) => Self::USize(n as _),
            Int::I8(n) => Self::U8(n as _),
            Int::I16(n) => Self::U16(n as _),
            Int::I32(n) => Self::U32(n as _),
            Int::I64(n) => Self::U64(n as _),
            Int::I128(n) => Self::U128(n as _),
        }
    }
}

/// A signed integer.
#[derive(Clone, Copy)]
pub(super) enum Int {
    /// A signed host-native-bit integer.
    ISize(isize),
    /// A signed 8-bit integer.
    I8(i8),
    /// A signed 16-bit integer.
    I16(i16),
    /// A signed 32-bit integer.
    I32(i32),
    /// A signed 64-bit integer.
    I64(i64),
    /// A signed 128-bit integer.
    I128(i128),
}
impl Int {
    /// Converts a string slice into an [`Int`] based on `bits`.
    fn from_str(str: &str, bits: Bits) -> Result<Self, ParseIntError> {
        match bits {
            Bits::BitNative => Ok(Self::ISize(str.parse()?)),
            Bits::Bit8 => Ok(Self::I8(str.parse()?)),
            Bits::Bit16 => Ok(Self::I16(str.parse()?)),
            Bits::Bit32 => Ok(Self::I32(str.parse()?)),
            Bits::Bit64 => Ok(Self::I64(str.parse()?)),
            Bits::Bit128 => Ok(Self::I128(str.parse()?)),
        }
    }

    /// Returns the byte representation of this integer.
    pub(super) fn as_bytes(&self) -> &[u8] {
        match self {
            Self::ISize(n) => bytemuck::bytes_of(n),
            Self::I8(n) => bytemuck::bytes_of(n),
            Self::I16(n) => bytemuck::bytes_of(n),
            Self::I32(n) => bytemuck::bytes_of(n),
            Self::I64(n) => bytemuck::bytes_of(n),
            Self::I128(n) => bytemuck::bytes_of(n),
        }
    }
}

/// Describes an NVM register constant.
#[derive(Clone, Copy)]
pub(super) enum RegConst<'tok> {
    /// An unsigned pointer-sized numeric constant.
    UInt(UInt),
    /// A signed pointer-sized numeric constant.
    Int(Int),
    /// An identifier for a module location.
    Ident(&'tok str),
}

/// Describes an NVM instruction.
pub(super) enum Instruction<'tok> {
    /// The `exit` instruction.
    Exit(u8),
    /// The `nop` instruction.
    Nop,
    /// The `move` instruction.
    Move(u8, u8),
    /// The `movec` instruction.
    MoveConst(u8, RegConst<'tok>),
    /// The `load` instruction.
    Load(u8, u8),
    /// The `loadn` instruction.
    LoadNum(u8, u8, u8),
    /// The `store` instruction.
    Store(u8, u8),
    /// The `storen` instruction.
    StoreNum(u8, u8, u8),
    /// The `push` instruction.
    Push(u8),
    /// The `pushn` instruction.
    PushNum(u8, u8),
    /// The `pop` instruction.
    Pop(u8),
    /// The `popn` instruction.
    PopNum(u8, u8),
    /// The `neg` instruction.
    Neg(u8),
    /// The `add` instruction.
    Add(u8, u8),
    /// The `addi` instruction.
    AddI(u8, u8),
    /// The `sub` instruction.
    Sub(u8, u8),
    /// The `subi` instruction.
    SubI(u8, u8),
    /// The `mul` instruction.
    Mul(u8, u8),
    /// The `muli` instruction.
    MulI(u8, u8),
    /// The `div` instruction.
    Div(u8, u8),
    /// The `divi` instruction.
    DivI(u8, u8),
    /// The `not` instruction.
    Not(u8),
    /// The `and` instruction.
    And(u8, u8),
    /// The `or` instruction.
    Or(u8, u8),
    /// The `xor` instruction.
    Xor(u8, u8),
    /// The `shl` instruction.
    Shl(u8, u8),
    /// The `shr` instruction.
    Shr(u8, u8),
    /// The `call` instruction.
    Call(RegConst<'tok>),
    /// The `return` instruction.
    Return,
    /// The `cmp` instruction.
    Cmp(u8, u8),
    /// The `jump` instruction.
    Jump(RegConst<'tok>),
    /// The `jz` instruction.
    JZ(RegConst<'tok>),
    /// The `jnz` instruction.
    JNZ(RegConst<'tok>),
    /// The `jo` instruction.
    JO(RegConst<'tok>),
    /// The `jno` instruction.
    JNO(RegConst<'tok>),
    /// The `jc` instruction.
    JC(RegConst<'tok>),
    /// The `jnc` instruction.
    JNC(RegConst<'tok>),
    /// The `js` instruction.
    JS(RegConst<'tok>),
    /// The `jns` instruction.
    JNS(RegConst<'tok>),
    /// The `je` instruction.
    JE(RegConst<'tok>),
    /// The `jne` instruction.
    JNE(RegConst<'tok>),
    /// The `ja` instruction.
    JA(RegConst<'tok>),
    /// The `jae` instruction.
    JAE(RegConst<'tok>),
    /// The `jb` instruction.
    JB(RegConst<'tok>),
    /// The `jbe` instruction.
    JBE(RegConst<'tok>),
    /// The `jg` instruction.
    JG(RegConst<'tok>),
    /// The `jge` instruction.
    JGE(RegConst<'tok>),
    /// The `jl` instruction.
    JL(RegConst<'tok>),
    /// The `jle` instruction.
    JLE(RegConst<'tok>),
    /// The `loadlib` instruction.
    LoadLib(u8),
    /// The `loadsym` instruction.
    LoadSym(u8, u8),
    /// The `syscall` instruction.
    Syscall(u8, u8),
    /// The `freelib` instruction.
    FreeLib(u8),
}
impl Instruction<'_> {
    /// Gets the instruction's size.
    const fn size(&self, bits: Bits) -> usize {
        match self {
            Self::Nop | Self::Return => 1,
            Self::Exit(_)
            | Self::Push(_)
            | Self::Pop(_)
            | Self::Neg(_)
            | Self::Not(_)
            | Self::LoadLib(_)
            | Self::FreeLib(_) => 2,
            Self::Move(_, _)
            | Self::Load(_, _)
            | Self::Store(_, _)
            | Self::PushNum(_, _)
            | Self::PopNum(_, _)
            | Self::Add(_, _)
            | Self::AddI(_, _)
            | Self::Sub(_, _)
            | Self::SubI(_, _)
            | Self::Mul(_, _)
            | Self::MulI(_, _)
            | Self::Div(_, _)
            | Self::DivI(_, _)
            | Self::And(_, _)
            | Self::Or(_, _)
            | Self::Xor(_, _)
            | Self::Shl(_, _)
            | Self::Shr(_, _)
            | Self::Cmp(_, _)
            | Self::LoadSym(_, _)
            | Self::Syscall(_, _) => 3,
            Self::LoadNum(_, _, _) | Self::StoreNum(_, _, _) => 4,
            Self::Call(_)
            | Self::Jump(_)
            | Self::JZ(_)
            | Self::JNZ(_)
            | Self::JO(_)
            | Self::JNO(_)
            | Self::JC(_)
            | Self::JNC(_)
            | Self::JS(_)
            | Self::JNS(_)
            | Self::JE(_)
            | Self::JNE(_)
            | Self::JA(_)
            | Self::JAE(_)
            | Self::JB(_)
            | Self::JBE(_)
            | Self::JG(_)
            | Self::JGE(_)
            | Self::JL(_)
            | Self::JLE(_) => 1 + bits.size(),
            Self::MoveConst(_, _) => 2 + bits.size(),
        }
    }
}

/// Describes a static item.
pub(super) enum Static {
    /// An unsigned pointer-sized numeric constant.
    UInt(UInt),
    /// A signed pointer-sized numeric constant.
    Int(Int),
    /// An unsigned 8-bit numeric constant.
    U8(u8),
    /// A signed 8-bit numeric constant.
    I8(i8),
    /// An unsigned 16-bit numeric constant.
    U16(u16),
    /// A signed 16-bit numeric constant.
    I16(i16),
    /// An unsigned 32-bit numeric constant.
    U32(u32),
    /// A signed 32-bit numeric constant.
    I32(i32),
    /// An unsigned 64-bit numeric constant.
    U64(u64),
    /// A signed 64-bit numeric constant.
    I64(i64),
    /// A string literal.
    String(String),
}

/// Describes an NVM item.
pub(super) enum Item<'tok> {
    /// An instruction.
    Instruction(Instruction<'tok>),
    /// A static item.
    Static(Static),
}

/// Makes sure a token is a valid register identifier.
fn assert_reg_ident(filename: &str, src: &str, token: &Token, reg_tok: &Token) -> u8 {
    if reg_tok.ty() == TokenType::Ident {
        match reg_tok.tok() {
            "r0" => return 0,
            "r1" => return 1,
            "r2" => return 2,
            "r3" => return 3,
            "ip" => return 4,
            "sp" => return 5,
            _ => {}
        }
    }
    let tok_label = token.label(filename, "Instruction encountered here.", Color::Blue);
    let reg_label = reg_tok.label(filename, "Invalid operand encountered here.", Color::Red);
    crate::grim_error(
        (filename, src, token.loc().byte_pos()),
        "Expected a register identifier as an instruction operand.",
        [tok_label, reg_label],
        None,
    );
}

/// Consumes a register identifier.
fn next_reg_ident<'tok, 'src>(
    filename: &str,
    src: &str,
    token: &Token,
    tokens: &mut Iter<'tok, Token<'src>>,
) -> (u8, &'tok Token<'src>) {
    match tokens.next() {
        Some(reg_tok) => (assert_reg_ident(filename, src, token, reg_tok), reg_tok),
        _ => crate::grim_error(
            (filename, src, token.loc().byte_pos()),
            "Expected a register identifier as an instruction operand.",
            [token.label(filename, "Instruction encountered here.", Color::Red)],
            None,
        ),
    }
}

/// Makes sure a token is an numeric constant.
fn assert_num<F: FromStr>(
    filename: &str,
    src: &str,
    token: &Token,
    num_token: &Token,
) -> Result<F, F::Err> {
    if num_token.ty() != TokenType::Num {
        let label = token.label(filename, "Instruction encountered here.", Color::Blue);
        let num_label = num_token.label(filename, "Invalid token encountered here.", Color::Red);
        crate::grim_error(
            (filename, src, num_token.loc().byte_pos()),
            "Expected a numeric constant as an instruction operand.",
            [label, num_label],
            None,
        );
    }
    num_token.tok().parse()
}

/// Consumes an numeric constant.
fn next_num<F: FromStr>(
    filename: &str,
    src: &str,
    token: &Token,
    tokens: &mut Iter<Token>,
) -> Result<F, F::Err> {
    match tokens.next() {
        Some(num_token) => assert_num(filename, src, token, num_token),
        _ => crate::grim_error(
            (filename, src, token.loc().byte_pos()),
            "Expected a numeric constant as an instruction operand.",
            [token.label(filename, "Instruction encountered here.", Color::Red)],
            None,
        ),
    }
}

/// Makes sure a token is a register constant.
fn assert_reg_const<'tok>(
    filename: &str,
    src: &str,
    token: &Token,
    tokens: &mut Iter<Token>,
    const_token: &'tok Token,
    bits: Bits,
) -> Result<RegConst<'tok>, ParseIntError> {
    match const_token.ty() {
        TokenType::Punct if const_token.tok() == "-" => {
            if let Some(num_token) = tokens.next() {
                let sign_pos = const_token.loc().byte_pos();
                let n_pos = num_token.loc().byte_pos();
                if num_token.ty() == TokenType::Num && n_pos == sign_pos + 1 {
                    let n_len = num_token.tok().len();
                    let tok = &src[sign_pos..n_pos + n_len];
                    return Ok(RegConst::Int(Int::from_str(tok, bits)?));
                }
            }
        }
        TokenType::Num => return Ok(RegConst::UInt(UInt::from_str(&const_token.tok(), bits)?)),
        TokenType::Ident => return Ok(RegConst::Ident(const_token.tok())),
        _ => {}
    }
    let tok_label = token.label(filename, "Instruction encountered here.", Color::Blue);
    let const_label = const_token.label(filename, "Invalid token encountered here.", Color::Red);
    crate::grim_error(
        (filename, src, token.loc().byte_pos()),
        "Expected a numeric constant or an identifier as an instruction operand.",
        [tok_label, const_label],
        None,
    );
}

/// Consumes a constant.
fn next_reg_const<'tok>(
    filename: &str,
    src: &str,
    op_token: &Token,
    tokens: &mut Iter<'tok, Token>,
    bits: Bits,
) -> Result<RegConst<'tok>, ParseIntError> {
    match tokens.next() {
        Some(const_token) => assert_reg_const(filename, src, op_token, tokens, const_token, bits),
        _ => crate::grim_error(
            (filename, src, op_token.loc().byte_pos()),
            "Expected a constant or an identifier as an instruction operand.",
            [op_token.label(filename, "Instruction encountered here.", Color::Red)],
            None,
        ),
    }
}

/// Makes sure a token is an operand separator.
fn assert_op_separator(filename: &str, src: &str, op_token: &Token, sep_token: &Token) {
    if sep_token.ty() != TokenType::Punct || sep_token.tok() != "," {
        let op_label = op_token.label(filename, "Operand encountered here.", Color::Blue);
        let sep_label = sep_token.label(filename, "Invalid token encountered here.", Color::Red);
        crate::grim_error(
            (filename, src, sep_token.loc().byte_pos()),
            "Expected a separator after an instruction operand.",
            [op_label, sep_label],
            Some("Try adding an operand separator (,) between these operands."),
        );
    }
}

/// Consumes an operand separator.
fn next_op_separator(filename: &str, src: &str, op_token: &Token, tokens: &mut Iter<Token>) {
    match tokens.next() {
        Some(sep_token) => assert_op_separator(filename, src, op_token, sep_token),
        _ => crate::grim_error(
            (filename, src, op_token.loc().byte_pos()),
            "Expected a separator after an instruction operand.",
            [op_token.label(filename, "Operand encountered here.", Color::Red)],
            Some("Try adding an operand separator (,) after this operand."),
        ),
    }
}

/// Attempts to get the next instruction.
fn next_instruction<'tok>(
    filename: &str,
    src: &str,
    token: &'tok Token,
    tokens: &mut Iter<'tok, Token>,
    bits: Bits,
) -> Result<Result<Instruction<'tok>, &'tok str>, ParseIntError> {
    match token.tok() {
        "exit" => {
            let (r, _) = next_reg_ident(filename, src, token, tokens);
            Ok(Ok(Instruction::Exit(r)))
        }
        "nop" => Ok(Ok(Instruction::Nop)),
        "move" => {
            let (r1, reg_tok) = next_reg_ident(filename, src, token, tokens);
            next_op_separator(filename, src, reg_tok, tokens);
            let (r2, _) = next_reg_ident(filename, src, token, tokens);
            Ok(Ok(Instruction::Move(r1, r2)))
        }
        "movec" => {
            let (r, reg_tok) = next_reg_ident(filename, src, token, tokens);
            next_op_separator(filename, src, reg_tok, tokens);
            let const_tok = next_reg_const(filename, src, token, tokens, bits)?;
            Ok(Ok(Instruction::MoveConst(r, const_tok)))
        }
        "load" => {
            let (r1, reg_tok) = next_reg_ident(filename, src, token, tokens);
            next_op_separator(filename, src, reg_tok, tokens);
            let (r2, _) = next_reg_ident(filename, src, token, tokens);
            Ok(Ok(Instruction::Load(r1, r2)))
        }
        "loadn" => {
            let (r1, reg_tok) = next_reg_ident(filename, src, token, tokens);
            next_op_separator(filename, src, reg_tok, tokens);
            let (r2, reg_tok) = next_reg_ident(filename, src, token, tokens);
            next_op_separator(filename, src, reg_tok, tokens);
            let n = next_num(filename, src, token, tokens)?;
            Ok(Ok(Instruction::LoadNum(r1, r2, n)))
        }
        "store" => {
            let (r1, reg_tok) = next_reg_ident(filename, src, token, tokens);
            next_op_separator(filename, src, reg_tok, tokens);
            let (r2, _) = next_reg_ident(filename, src, token, tokens);
            Ok(Ok(Instruction::Store(r1, r2)))
        }
        "storen" => {
            let (r1, reg_tok) = next_reg_ident(filename, src, token, tokens);
            next_op_separator(filename, src, reg_tok, tokens);
            let (r2, reg_tok) = next_reg_ident(filename, src, token, tokens);
            next_op_separator(filename, src, reg_tok, tokens);
            let n = next_num(filename, src, token, tokens)?;
            Ok(Ok(Instruction::StoreNum(r1, r2, n)))
        }
        "push" => {
            let (r, _) = next_reg_ident(filename, src, token, tokens);
            Ok(Ok(Instruction::Push(r)))
        }
        "pushn" => {
            let (r, reg_tok) = next_reg_ident(filename, src, token, tokens);
            next_op_separator(filename, src, reg_tok, tokens);
            let n = next_num(filename, src, token, tokens)?;
            Ok(Ok(Instruction::PushNum(r, n)))
        }
        "pop" => {
            let (r, _) = next_reg_ident(filename, src, token, tokens);
            Ok(Ok(Instruction::Pop(r)))
        }
        "popn" => {
            let (r, reg_tok) = next_reg_ident(filename, src, token, tokens);
            next_op_separator(filename, src, reg_tok, tokens);
            let n = next_num(filename, src, token, tokens)?;
            Ok(Ok(Instruction::PopNum(r, n)))
        }
        "neg" => {
            let (r, _) = next_reg_ident(filename, src, token, tokens);
            Ok(Ok(Instruction::Neg(r)))
        }
        "add" => {
            let (r1, reg_tok) = next_reg_ident(filename, src, token, tokens);
            next_op_separator(filename, src, reg_tok, tokens);
            let (r2, _) = next_reg_ident(filename, src, token, tokens);
            Ok(Ok(Instruction::Add(r1, r2)))
        }
        "addi" => {
            let (r1, reg_tok) = next_reg_ident(filename, src, token, tokens);
            next_op_separator(filename, src, reg_tok, tokens);
            let (r2, _) = next_reg_ident(filename, src, token, tokens);
            Ok(Ok(Instruction::AddI(r1, r2)))
        }
        "sub" => {
            let (r1, reg_tok) = next_reg_ident(filename, src, token, tokens);
            next_op_separator(filename, src, reg_tok, tokens);
            let (r2, _) = next_reg_ident(filename, src, token, tokens);
            Ok(Ok(Instruction::Sub(r1, r2)))
        }
        "subi" => {
            let (r1, reg_tok) = next_reg_ident(filename, src, token, tokens);
            next_op_separator(filename, src, reg_tok, tokens);
            let (r2, _) = next_reg_ident(filename, src, token, tokens);
            Ok(Ok(Instruction::SubI(r1, r2)))
        }
        "mul" => {
            let (r1, reg_tok) = next_reg_ident(filename, src, token, tokens);
            next_op_separator(filename, src, reg_tok, tokens);
            let (r2, _) = next_reg_ident(filename, src, token, tokens);
            Ok(Ok(Instruction::Mul(r1, r2)))
        }
        "muli" => {
            let (r1, reg_tok) = next_reg_ident(filename, src, token, tokens);
            next_op_separator(filename, src, reg_tok, tokens);
            let (r2, _) = next_reg_ident(filename, src, token, tokens);
            Ok(Ok(Instruction::MulI(r1, r2)))
        }
        "div" => {
            let (r1, reg_tok) = next_reg_ident(filename, src, token, tokens);
            next_op_separator(filename, src, reg_tok, tokens);
            let (r2, _) = next_reg_ident(filename, src, token, tokens);
            Ok(Ok(Instruction::Div(r1, r2)))
        }
        "divi" => {
            let (r1, reg_tok) = next_reg_ident(filename, src, token, tokens);
            next_op_separator(filename, src, reg_tok, tokens);
            let (r2, _) = next_reg_ident(filename, src, token, tokens);
            Ok(Ok(Instruction::DivI(r1, r2)))
        }
        "not" => {
            let (r, _) = next_reg_ident(filename, src, token, tokens);
            Ok(Ok(Instruction::Not(r)))
        }
        "and" => {
            let (r1, reg_tok) = next_reg_ident(filename, src, token, tokens);
            next_op_separator(filename, src, reg_tok, tokens);
            let (r2, _) = next_reg_ident(filename, src, token, tokens);
            Ok(Ok(Instruction::And(r1, r2)))
        }
        "or" => {
            let (r1, reg_tok) = next_reg_ident(filename, src, token, tokens);
            next_op_separator(filename, src, reg_tok, tokens);
            let (r2, _) = next_reg_ident(filename, src, token, tokens);
            Ok(Ok(Instruction::Or(r1, r2)))
        }
        "xor" => {
            let (r1, reg_tok) = next_reg_ident(filename, src, token, tokens);
            next_op_separator(filename, src, reg_tok, tokens);
            let (r2, _) = next_reg_ident(filename, src, token, tokens);
            Ok(Ok(Instruction::Xor(r1, r2)))
        }
        "shl" => {
            let (r1, reg_tok) = next_reg_ident(filename, src, token, tokens);
            next_op_separator(filename, src, reg_tok, tokens);
            let (r2, _) = next_reg_ident(filename, src, token, tokens);
            Ok(Ok(Instruction::Shl(r1, r2)))
        }
        "shr" => {
            let (r1, reg_tok) = next_reg_ident(filename, src, token, tokens);
            next_op_separator(filename, src, reg_tok, tokens);
            let (r2, _) = next_reg_ident(filename, src, token, tokens);
            Ok(Ok(Instruction::Shr(r1, r2)))
        }
        "call" => {
            let n = next_reg_const(filename, src, token, tokens, bits)?;
            Ok(Ok(Instruction::Call(n)))
        }
        "return" => Ok(Ok(Instruction::Return)),
        "cmp" => {
            let (r1, reg_tok) = next_reg_ident(filename, src, token, tokens);
            next_op_separator(filename, src, reg_tok, tokens);
            let (r2, _) = next_reg_ident(filename, src, token, tokens);
            Ok(Ok(Instruction::Cmp(r1, r2)))
        }
        "jump" => {
            let n = next_reg_const(filename, src, token, tokens, bits)?;
            Ok(Ok(Instruction::Jump(n)))
        }
        "jz" => {
            let n = next_reg_const(filename, src, token, tokens, bits)?;
            Ok(Ok(Instruction::JZ(n)))
        }
        "jnz" => {
            let n = next_reg_const(filename, src, token, tokens, bits)?;
            Ok(Ok(Instruction::JNZ(n)))
        }
        "jo" => {
            let n = next_reg_const(filename, src, token, tokens, bits)?;
            Ok(Ok(Instruction::JO(n)))
        }
        "jno" => {
            let n = next_reg_const(filename, src, token, tokens, bits)?;
            Ok(Ok(Instruction::JNO(n)))
        }
        "jc" => {
            let n = next_reg_const(filename, src, token, tokens, bits)?;
            Ok(Ok(Instruction::JC(n)))
        }
        "jnc" => {
            let n = next_reg_const(filename, src, token, tokens, bits)?;
            Ok(Ok(Instruction::JNC(n)))
        }
        "js" => {
            let n = next_reg_const(filename, src, token, tokens, bits)?;
            Ok(Ok(Instruction::JS(n)))
        }
        "jns" => {
            let n = next_reg_const(filename, src, token, tokens, bits)?;
            Ok(Ok(Instruction::JNS(n)))
        }
        "je" => {
            let n = next_reg_const(filename, src, token, tokens, bits)?;
            Ok(Ok(Instruction::JE(n)))
        }
        "jne" => {
            let n = next_reg_const(filename, src, token, tokens, bits)?;
            Ok(Ok(Instruction::JNE(n)))
        }
        "ja" => {
            let n = next_reg_const(filename, src, token, tokens, bits)?;
            Ok(Ok(Instruction::JA(n)))
        }
        "jae" => {
            let n = next_reg_const(filename, src, token, tokens, bits)?;
            Ok(Ok(Instruction::JAE(n)))
        }
        "jb" => {
            let n = next_reg_const(filename, src, token, tokens, bits)?;
            Ok(Ok(Instruction::JB(n)))
        }
        "jbe" => {
            let n = next_reg_const(filename, src, token, tokens, bits)?;
            Ok(Ok(Instruction::JBE(n)))
        }
        "jg" => {
            let n = next_reg_const(filename, src, token, tokens, bits)?;
            Ok(Ok(Instruction::JG(n)))
        }
        "jge" => {
            let n = next_reg_const(filename, src, token, tokens, bits)?;
            Ok(Ok(Instruction::JGE(n)))
        }
        "jl" => {
            let n = next_reg_const(filename, src, token, tokens, bits)?;
            Ok(Ok(Instruction::JL(n)))
        }
        "jle" => {
            let n = next_reg_const(filename, src, token, tokens, bits)?;
            Ok(Ok(Instruction::JLE(n)))
        }
        "loadlib" => {
            let (r, _) = next_reg_ident(filename, src, token, tokens);
            Ok(Ok(Instruction::LoadLib(r)))
        }
        "loadsym" => {
            let (r1, reg_tok) = next_reg_ident(filename, src, token, tokens);
            next_op_separator(filename, src, reg_tok, tokens);
            let (r2, _) = next_reg_ident(filename, src, token, tokens);
            Ok(Ok(Instruction::LoadSym(r1, r2)))
        }
        "syscall" => {
            let (r1, reg_tok) = next_reg_ident(filename, src, token, tokens);
            next_op_separator(filename, src, reg_tok, tokens);
            let (r2, _) = next_reg_ident(filename, src, token, tokens);
            Ok(Ok(Instruction::Syscall(r1, r2)))
        }
        "freelib" => {
            let (r, _) = next_reg_ident(filename, src, token, tokens);
            Ok(Ok(Instruction::FreeLib(r)))
        }
        ident => Ok(Err(ident)),
    }
}

/// Adds a static item.
fn add_static<T>(items: &mut Vec<Item>, loc: &mut u128, s: Static) {
    *loc += core::mem::size_of::<T>() as u128;
    items.push(Item::Static(s));
}

/// Turns Grim source tokens into NVM items.
pub(super) fn parse<'tok>(
    filename: &str,
    src: &str,
    mut tokens: Iter<'tok, Token>,
    bits: Bits,
) -> Result<(Vec<Item<'tok>>, HashMap<&'tok str, UInt>), ParseIntError> {
    let mut items = Vec::new();
    let mut loc = 0;
    let mut locations = HashMap::new();
    while let Some(token) = tokens.next() {
        match token.ty() {
            TokenType::Ident => match next_instruction(filename, src, token, &mut tokens, bits)? {
                Ok(instruction) => {
                    loc += instruction.size(bits) as u128;
                    items.push(Item::Instruction(instruction));
                }
                Err(ident) => {
                    locations.insert(ident, UInt::from_u128(loc, bits));
                }
            },
            TokenType::Punct if token.tok() == "-" => {
                if let Some(num_tok) = tokens.next() {
                    let sign_pos = token.loc().byte_pos();
                    let n_pos = num_tok.loc().byte_pos();
                    if num_tok.ty() == TokenType::Num && n_pos == sign_pos + 1 {
                        if let Some(ty_tok) = tokens.next() {
                            let ty_pos = ty_tok.loc().byte_pos();
                            let n_len = num_tok.tok().len();
                            if ty_tok.ty() == TokenType::Ident && ty_pos == n_pos + n_len {
                                match ty_tok.tok() {
                                    "int" => {
                                        let tok = &src[sign_pos..n_pos + n_len];
                                        let s = Static::Int(Int::from_str(tok, bits)?);
                                        loc += bits.size() as u128;
                                        items.push(Item::Static(s));
                                        continue;
                                    }
                                    "i8" => {
                                        let n_len = num_tok.tok().len();
                                        let s = Static::I8(src[sign_pos..n_pos + n_len].parse()?);
                                        add_static::<i8>(&mut items, &mut loc, s);
                                        continue;
                                    }
                                    "i16" => {
                                        let n_len = num_tok.tok().len();
                                        let s = Static::I16(src[sign_pos..n_pos + n_len].parse()?);
                                        add_static::<i16>(&mut items, &mut loc, s);
                                        continue;
                                    }
                                    "i32" => {
                                        let n_len = num_tok.tok().len();
                                        let s = Static::I32(src[sign_pos..n_pos + n_len].parse()?);
                                        add_static::<i32>(&mut items, &mut loc, s);
                                        continue;
                                    }
                                    "i64" => {
                                        let n_len = num_tok.tok().len();
                                        let s = Static::I64(src[sign_pos..n_pos + n_len].parse()?);
                                        add_static::<i64>(&mut items, &mut loc, s);
                                        continue;
                                    }
                                    _ => {}
                                }
                            }
                        }
                        crate::grim_error(
                            (filename, src, num_tok.loc().byte_pos()),
                            "Expected a signed type identifier after a numeric literal.",
                            [num_tok.label(filename, "Numeric token encountered here.", Color::Red)],
                            Some("Add a signed type identifier, such as 'int', directly after this number."),
                        );
                    }
                }
                crate::grim_error(
                    (filename, src, token.loc().byte_pos()),
                    "Expected a numeric literal after the negation operator.",
                    [token.label(filename, "Negation operator encountered here.", Color::Red)],
                    None,
                );
            }
            TokenType::Num => {
                if let Some(ty_tok) = tokens.next() {
                    let n_pos = token.loc().byte_pos();
                    let ty_pos = ty_tok.loc().byte_pos();
                    let n_len = token.tok().len();
                    if ty_tok.ty() == TokenType::Ident && ty_pos == n_pos + n_len {
                        match ty_tok.tok() {
                            "uint" => {
                                let s = Static::UInt(UInt::from_str(token.tok(), bits)?);
                                loc += bits.size() as u128;
                                items.push(Item::Static(s));
                                continue;
                            }
                            "int" => {
                                let s = Static::Int(Int::from_str(token.tok(), bits)?);
                                loc += bits.size() as u128;
                                items.push(Item::Static(s));
                                continue;
                            }
                            "u8" => {
                                let s = Static::U8(token.tok().parse()?);
                                add_static::<u8>(&mut items, &mut loc, s);
                                continue;
                            }
                            "i8" => {
                                let s = Static::I8(token.tok().parse()?);
                                add_static::<i8>(&mut items, &mut loc, s);
                                continue;
                            }
                            "u16" => {
                                let s = Static::U16(token.tok().parse()?);
                                add_static::<u16>(&mut items, &mut loc, s);
                                continue;
                            }
                            "i16" => {
                                let s = Static::I16(token.tok().parse()?);
                                add_static::<i16>(&mut items, &mut loc, s);
                                continue;
                            }
                            "u32" => {
                                let s = Static::U32(token.tok().parse()?);
                                add_static::<u32>(&mut items, &mut loc, s);
                                continue;
                            }
                            "i32" => {
                                let s = Static::I32(token.tok().parse()?);
                                add_static::<i32>(&mut items, &mut loc, s);
                                continue;
                            }
                            "u64" => {
                                let s = Static::U64(token.tok().parse()?);
                                add_static::<u64>(&mut items, &mut loc, s);
                                continue;
                            }
                            "i64" => {
                                let s = Static::I64(token.tok().parse()?);
                                add_static::<i64>(&mut items, &mut loc, s);
                                continue;
                            }
                            _ => {}
                        }
                    }
                }
                crate::grim_error(
                    (filename, src, token.loc().byte_pos()),
                    "Expected a type identifier after a numeric literal.",
                    [token.label(filename, "Numeric token encountered here.", Color::Red)],
                    Some("Add a type identifier, such as 'uint', directly after this number."),
                );
            }
            TokenType::String => {
                let s = token.tok();
                let mut chars = s[1..s.len() - 1].chars();
                let mut s = String::with_capacity(s.len());
                while let Some(c) = chars.next() {
                    if c == '\\' {
                        match chars.next() {
                            Some('0') => s.push('\0'),
                            Some('n') => s.push('\n'),
                            Some('t') => s.push('\t'),
                            Some('r') => s.push('\r'),
                            _ => {}
                        }
                    } else {
                        s.push(c);
                    }
                }
                loc += s.len() as u128;
                items.push(Item::Static(Static::String(s)));
            }
            _ => crate::grim_error(
                (filename, src, token.loc().byte_pos()),
                "Expected an identifier or a static literal.",
                [token.label(filename, "Unexpected token encountered here.", Color::Red)],
                None,
            ),
        }
    }
    Ok((items, locations))
}
