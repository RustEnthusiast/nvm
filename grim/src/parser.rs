use crate::lexer::{Token, TokenType};
use ariadne::Color;
use nvm::opcode::OpCode;
use std::{collections::HashMap, num::ParseIntError, slice::Iter, str::FromStr};

/// Describes an NVM register constant.
#[derive(Clone, Copy)]
pub(super) enum RegConst<'tok> {
    /// An unsigned pointer-sized numeric constant.
    UInt(usize),
    /// A signed pointer-sized numeric constant.
    Int(isize),
    /// An identifier for a module location.
    Ident(&'tok str),
}

/// Describes an NVM instruction.
pub(super) enum Instruction<'tok> {
    /// The `exit` instruction.
    Exit(u8),
    /// The `nop` instruction.
    Nop,
    /// The `jump` instruction.
    Jump(RegConst<'tok>),
    /// The `call` instruction.
    Call(RegConst<'tok>),
    /// The `return` instruction.
    Return,
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
    /// The `add` instruction.
    Add(u8, u8),
    /// The `sub` instruction.
    Sub(u8, u8),
    /// The `mul` instruction.
    Mul(u8, u8),
    /// The `div` instruction.
    Div(u8, u8),
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
    const fn size(&self) -> usize {
        match self {
            Instruction::Exit(_) => OpCode::Exit.size(),
            Instruction::Nop => OpCode::Nop.size(),
            Instruction::Jump(_) => OpCode::Jump.size(),
            Instruction::Call(_) => OpCode::Call.size(),
            Instruction::Return => OpCode::Return.size(),
            Instruction::Move(_, _) => OpCode::Move.size(),
            Instruction::MoveConst(_, _) => OpCode::MoveConst.size(),
            Instruction::Load(_, _) => OpCode::Load.size(),
            Instruction::LoadNum(_, _, _) => OpCode::LoadNum.size(),
            Instruction::Store(_, _) => OpCode::Store.size(),
            Instruction::StoreNum(_, _, _) => OpCode::StoreNum.size(),
            Instruction::Push(_) => OpCode::Push.size(),
            Instruction::PushNum(_, _) => OpCode::PushNum.size(),
            Instruction::Pop(_) => OpCode::Pop.size(),
            Instruction::PopNum(_, _) => OpCode::PopNum.size(),
            Instruction::Add(_, _) => OpCode::Add.size(),
            Instruction::Sub(_, _) => OpCode::Sub.size(),
            Instruction::Mul(_, _) => OpCode::Mul.size(),
            Instruction::Div(_, _) => OpCode::Div.size(),
            Instruction::LoadLib(_) => OpCode::LoadLib.size(),
            Instruction::LoadSym(_, _) => OpCode::LoadSym.size(),
            Instruction::Syscall(_, _) => OpCode::Syscall.size(),
            Instruction::FreeLib(_) => OpCode::FreeLib.size(),
        }
    }
}

/// Describes a static item.
pub(super) enum Static {
    /// An unsigned pointer-sized numeric constant.
    UInt(usize),
    /// A signed pointer-sized numeric constant.
    Int(isize),
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
) -> Result<RegConst<'tok>, ParseIntError> {
    match const_token.ty() {
        TokenType::Punct if const_token.tok() == "-" => {
            if let Some(num_token) = tokens.next() {
                let sign_pos = const_token.loc().byte_pos();
                let n_pos = num_token.loc().byte_pos();
                if num_token.ty() == TokenType::Num && n_pos == sign_pos + 1 {
                    let n_len = num_token.tok().len();
                    return Ok(RegConst::Int(src[sign_pos..n_pos + n_len].parse()?));
                }
            }
        }
        TokenType::Num => return Ok(RegConst::UInt(const_token.tok().parse()?)),
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
) -> Result<RegConst<'tok>, ParseIntError> {
    match tokens.next() {
        Some(const_token) => assert_reg_const(filename, src, op_token, tokens, const_token),
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
) -> Result<Result<Instruction<'tok>, &'tok str>, ParseIntError> {
    match token.tok() {
        "exit" => {
            let (r, _) = next_reg_ident(filename, src, token, tokens);
            Ok(Ok(Instruction::Exit(r)))
        }
        "nop" => Ok(Ok(Instruction::Nop)),
        "jump" => {
            let n = next_reg_const(filename, src, token, tokens)?;
            Ok(Ok(Instruction::Jump(n)))
        }
        "call" => {
            let n = next_reg_const(filename, src, token, tokens)?;
            Ok(Ok(Instruction::Call(n)))
        }
        "return" => Ok(Ok(Instruction::Return)),
        "move" => {
            let (r1, reg_tok) = next_reg_ident(filename, src, token, tokens);
            next_op_separator(filename, src, reg_tok, tokens);
            let (r2, _) = next_reg_ident(filename, src, token, tokens);
            Ok(Ok(Instruction::Move(r1, r2)))
        }
        "movec" => {
            let (r, reg_tok) = next_reg_ident(filename, src, token, tokens);
            next_op_separator(filename, src, reg_tok, tokens);
            let const_tok = next_reg_const(filename, src, token, tokens)?;
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
        "add" => {
            let (r1, reg_tok) = next_reg_ident(filename, src, token, tokens);
            next_op_separator(filename, src, reg_tok, tokens);
            let (r2, _) = next_reg_ident(filename, src, token, tokens);
            Ok(Ok(Instruction::Add(r1, r2)))
        }
        "sub" => {
            let (r1, reg_tok) = next_reg_ident(filename, src, token, tokens);
            next_op_separator(filename, src, reg_tok, tokens);
            let (r2, _) = next_reg_ident(filename, src, token, tokens);
            Ok(Ok(Instruction::Sub(r1, r2)))
        }
        "mul" => {
            let (r1, reg_tok) = next_reg_ident(filename, src, token, tokens);
            next_op_separator(filename, src, reg_tok, tokens);
            let (r2, _) = next_reg_ident(filename, src, token, tokens);
            Ok(Ok(Instruction::Mul(r1, r2)))
        }
        "div" => {
            let (r1, reg_tok) = next_reg_ident(filename, src, token, tokens);
            next_op_separator(filename, src, reg_tok, tokens);
            let (r2, _) = next_reg_ident(filename, src, token, tokens);
            Ok(Ok(Instruction::Div(r1, r2)))
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
fn add_static<T>(items: &mut Vec<Item>, loc: &mut usize, s: Static) {
    *loc += core::mem::size_of::<T>();
    items.push(Item::Static(s));
}

/// Turns Grim source tokens into NVM items.
pub(super) fn parse<'tok>(
    filename: &str,
    src: &str,
    mut tokens: Iter<'tok, Token>,
) -> Result<(Vec<Item<'tok>>, HashMap<&'tok str, usize>), ParseIntError> {
    let mut items = Vec::new();
    let mut loc = 0usize;
    let mut locations = HashMap::new();
    while let Some(token) = tokens.next() {
        match token.ty() {
            TokenType::Ident => match next_instruction(filename, src, token, &mut tokens)? {
                Ok(instruction) => {
                    loc += instruction.size();
                    items.push(Item::Instruction(instruction));
                }
                Err(ident) => {
                    locations.insert(ident, loc);
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
                                        let s = Static::Int(src[sign_pos..n_pos + n_len].parse()?);
                                        add_static::<isize>(&mut items, &mut loc, s);
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
                                let s = Static::UInt(token.tok().parse()?);
                                add_static::<usize>(&mut items, &mut loc, s);
                                continue;
                            }
                            "int" => {
                                let s = Static::Int(token.tok().parse()?);
                                add_static::<isize>(&mut items, &mut loc, s);
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
                loc += s.len();
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
