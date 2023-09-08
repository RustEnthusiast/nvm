use crate::lexer::{Token, TokenType};
use ariadne::Color;
use nvm::opcode::OpCode;
use std::{borrow::Cow, collections::HashMap, num::ParseIntError, slice::Iter, str::FromStr};

/// Describes an NVM constant item.
#[derive(Clone, Copy)]
pub(super) enum Const<'tok> {
    /// A numeric constant.
    Num(usize),
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
    Jump(Const<'tok>),
    /// The `move` instruction.
    Move(u8, u8),
    /// The `movec` instruction.
    MoveConst(u8, Const<'tok>),
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
    /// The `pop` instruction.
    Pop(u8),
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
            Instruction::Move(_, _) => OpCode::Move.size(),
            Instruction::MoveConst(_, _) => OpCode::MoveConst.size(),
            Instruction::Load(_, _) => OpCode::Load.size(),
            Instruction::LoadNum(_, _, _) => OpCode::LoadNum.size(),
            Instruction::Store(_, _) => OpCode::Store.size(),
            Instruction::StoreNum(_, _, _) => OpCode::StoreNum.size(),
            Instruction::Push(_) => OpCode::Push.size(),
            Instruction::Pop(_) => OpCode::Pop.size(),
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
    /// A numeric constant.
    Num(usize),
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
fn assert_reg_ident(filename: &Cow<str>, src: &str, token: &Token, reg_tok: &Token) -> u8 {
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
    filename: &Cow<str>,
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
    filename: &Cow<str>,
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
    filename: &Cow<str>,
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

/// Makes sure a token is a constant.
fn assert_const<'tok>(
    filename: &Cow<str>,
    src: &str,
    token: &Token,
    const_token: &'tok Token,
) -> Result<Const<'tok>, ParseIntError> {
    match const_token.ty() {
        TokenType::Num => Ok(Const::Num(const_token.tok().parse()?)),
        TokenType::Ident => Ok(Const::Ident(const_token.tok())),
        _ => {
            let tok_label = token.label(filename, "Instruction encountered here.", Color::Blue);
            let const_label =
                const_token.label(filename, "Invalid token encountered here.", Color::Red);
            crate::grim_error(
                (filename, src, token.loc().byte_pos()),
                "Expected a numeric constant or an identifier as an instruction operand.",
                [tok_label, const_label],
                None,
            );
        }
    }
}

/// Consumes a constant.
fn next_const<'tok>(
    filename: &Cow<str>,
    src: &str,
    op_token: &Token,
    tokens: &mut Iter<'tok, Token>,
) -> Result<Const<'tok>, ParseIntError> {
    match tokens.next() {
        Some(const_token) => assert_const(filename, src, op_token, const_token),
        _ => crate::grim_error(
            (filename, src, op_token.loc().byte_pos()),
            "Expected a constant or an identifier as an instruction operand.",
            [op_token.label(filename, "Instruction encountered here.", Color::Red)],
            None,
        ),
    }
}

/// Makes sure a token is an operand separator.
fn assert_op_separator(filename: &Cow<str>, src: &str, op_token: &Token, sep_token: &Token) {
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
fn next_op_separator(filename: &Cow<str>, src: &str, op_token: &Token, tokens: &mut Iter<Token>) {
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
    filename: &Cow<str>,
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
            let n = next_const(filename, src, token, tokens)?;
            Ok(Ok(Instruction::Jump(n)))
        }
        "move" => {
            let (r1, reg_tok) = next_reg_ident(filename, src, token, tokens);
            next_op_separator(filename, src, reg_tok, tokens);
            let (r2, _) = next_reg_ident(filename, src, token, tokens);
            Ok(Ok(Instruction::Move(r1, r2)))
        }
        "movec" => {
            let (r, reg_tok) = next_reg_ident(filename, src, token, tokens);
            next_op_separator(filename, src, reg_tok, tokens);
            let const_tok = next_const(filename, src, token, tokens)?;
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
        "pop" => {
            let (r, _) = next_reg_ident(filename, src, token, tokens);
            Ok(Ok(Instruction::Pop(r)))
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

/// Turns Grim source tokens into NVM items.
pub(super) fn parse<'tok>(
    filename: &Cow<str>,
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
            TokenType::Num => {
                loc += core::mem::size_of::<usize>();
                items.push(Item::Static(Static::Num(token.tok().parse()?)));
            }
            TokenType::String => {
                let s = token.tok();
                let mut chars = s[1..s.len() - 1].chars();
                let mut s = String::with_capacity(s.len());
                while let Some(c) = chars.next() {
                    if c == '\\' {
                        match chars.next() {
                            Some('0') => s.push('\0'),
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
