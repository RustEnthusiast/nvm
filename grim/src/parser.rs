use crate::lexer::{Token, TokenType};
use ariadne::Color;
use std::{borrow::Cow, num::ParseIntError, slice::Iter};

/// Describes an NVM instruction.
pub(super) enum Instruction {
    /// The `exit` instruction.
    Exit,
    /// The `nop` instruction.
    Nop,
    /// The `jump` instruction.
    Jump(u8),
    /// The `move` instruction.
    Move(u8, u8),
    /// The `movec` instruction.
    MoveConst(u8, usize),
    /// The `push` instruction.
    Push(u8),
    /// The `pushc` instruction.
    PushConst(usize),
    /// The `pop` instruction.
    Pop(u8),
    /// The `add` instruction.
    Add(u8, u8),
    /// The `addc` instruction.
    AddConst(u8, usize),
    /// The `sub` instruction.
    Sub(u8, u8),
    /// The `subc` instruction.
    SubConst(u8, usize),
    /// The `mul` instruction.
    Mul(u8, u8),
    /// The `mulc` instruction.
    MulConst(u8, usize),
    /// The `div` instruction.
    Div(u8, u8),
    /// The `divc` instruction.
    DivConst(u8, usize),
    /// The `loadlib` instruction.
    LoadLib,
    /// The `loadsym` instruction.
    LoadSym,
    /// The `syscall` instruction.
    Syscall,
    /// The `freelib` instruction.
    FreeLib,
}

/// Describes an NVM item.
pub(super) enum Item {
    /// An instruction.
    Instruction(Instruction),
}

/// Makes sure that `token` is an identifier token.
fn assert_ident(filename: &Cow<str>, src: &str, token: &Token) {
    if token.ty() != TokenType::Ident {
        crate::grim_error(
            (filename, src, token.loc().byte_pos()),
            "Expected an identifier.",
            [token.label(filename, "Unexpected token encountered here.", Color::Red)],
            None,
        );
    }
}

/// A register identifier was expected but no token was found.
fn absent_reg_ident(filename: &Cow<str>, src: &str, token: &Token) -> ! {
    crate::grim_error(
        (filename, src, token.loc().byte_pos()),
        "Expected a register identifier as an instruction operand.",
        [token.label(filename, "Instruction encountered here.", Color::Red)],
        None,
    );
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
#[inline]
fn next_reg_ident<'tok, 'src>(
    filename: &Cow<str>,
    src: &str,
    token: &Token,
    tokens: &mut Iter<'tok, Token<'src>>,
) -> (u8, &'tok Token<'src>) {
    match tokens.next() {
        Some(reg_tok) => (assert_reg_ident(filename, src, token, reg_tok), reg_tok),
        _ => absent_reg_ident(filename, src, token),
    }
}

/// A numeric constant was expected but no token was found.
fn absent_num(filename: &Cow<str>, src: &str, token: &Token) -> ! {
    crate::grim_error(
        (filename, src, token.loc().byte_pos()),
        "Expected a numeric constant as an instruction operand.",
        [token.label(filename, "Instruction encountered here.", Color::Red)],
        None,
    );
}

/// Makes sure a token is a numeric constant.
fn assert_num(
    filename: &Cow<str>,
    src: &str,
    token: &Token,
    num_token: &Token,
) -> Result<usize, ParseIntError> {
    if num_token.ty() != TokenType::Num {
        let tok_label = token.label(filename, "First operand encountered here.", Color::Blue);
        let num_label = num_token.label(filename, "Invalid token encountered here.", Color::Red);
        crate::grim_error(
            (filename, src, token.loc().byte_pos()),
            "Expected a numeric constant as an instruction operand.",
            [tok_label, num_label],
            None,
        );
    }
    num_token.tok().parse()
}

/// Consumes a numeric constant.
#[inline]
fn next_num<'tok, 'src>(
    filename: &Cow<str>,
    src: &str,
    op_token: &Token,
    tokens: &mut Iter<'tok, Token<'src>>,
) -> Result<(usize, &'tok Token<'src>), ParseIntError> {
    match tokens.next() {
        Some(num_token) => Ok((assert_num(filename, src, op_token, num_token)?, num_token)),
        _ => absent_num(filename, src, op_token),
    }
}

/// An operand separator was expected but no token was found.
fn absent_op_separator(filename: &Cow<str>, src: &str, op_token: &Token) -> ! {
    crate::grim_error(
        (filename, src, op_token.loc().byte_pos()),
        "Expected a separator after an instruction operand.",
        [op_token.label(filename, "Operand encountered here.", Color::Red)],
        Some("Try adding an operand separator (,) after this operand."),
    );
}

/// Makes sure a token is an operand separator.
fn assert_op_separator(filename: &Cow<str>, src: &str, op_token: &Token, sep_token: &Token) {
    if sep_token.ty() != TokenType::Punct || sep_token.tok() != "," {
        let op_label = op_token.label(filename, "First operand encountered here.", Color::Blue);
        let sep_label = sep_token.label(filename, "Invalid token encountered here.", Color::Red);
        crate::grim_error(
            (filename, src, sep_token.loc().byte_pos()),
            "Expected a separator after an instruction operand.",
            [op_label, sep_label],
            Some("Try adding an operand separator (,) after this operand."),
        );
    }
}

/// Consumes an operand separator.
#[inline]
fn next_op_separator(filename: &Cow<str>, src: &str, op_token: &Token, tokens: &mut Iter<Token>) {
    match tokens.next() {
        Some(sep_token) => assert_op_separator(filename, src, op_token, sep_token),
        _ => absent_op_separator(filename, src, op_token),
    }
}

/// Turns Grim source tokens into NVM items.
pub(super) fn parse(
    filename: &Cow<str>,
    src: &str,
    mut tokens: Iter<Token>,
) -> Result<Vec<Item>, ParseIntError> {
    let mut items = Vec::new();
    while let Some(token) = tokens.next() {
        assert_ident(filename, src, token);
        match token.tok() {
            "exit" => items.push(Item::Instruction(Instruction::Exit)),
            "nop" => items.push(Item::Instruction(Instruction::Nop)),
            "jump" => {
                let (r, _) = next_reg_ident(filename, src, token, &mut tokens);
                items.push(Item::Instruction(Instruction::Jump(r)));
            }
            "move" => {
                let (r1, reg_tok) = next_reg_ident(filename, src, token, &mut tokens);
                next_op_separator(filename, src, reg_tok, &mut tokens);
                let (r2, _) = next_reg_ident(filename, src, token, &mut tokens);
                items.push(Item::Instruction(Instruction::Move(r1, r2)));
            }
            "movec" => {
                let (r, reg_tok) = next_reg_ident(filename, src, token, &mut tokens);
                next_op_separator(filename, src, reg_tok, &mut tokens);
                let (n, _) = next_num(filename, src, token, &mut tokens)?;
                items.push(Item::Instruction(Instruction::MoveConst(r, n)));
            }
            "push" => {
                let (r, _) = next_reg_ident(filename, src, token, &mut tokens);
                items.push(Item::Instruction(Instruction::Push(r)));
            }
            "pushc" => {
                let (n, _) = next_num(filename, src, token, &mut tokens)?;
                items.push(Item::Instruction(Instruction::PushConst(n)));
            }
            "pop" => {
                let (r, _) = next_reg_ident(filename, src, token, &mut tokens);
                items.push(Item::Instruction(Instruction::Pop(r)));
            }
            "add" => {
                let (r1, reg_tok) = next_reg_ident(filename, src, token, &mut tokens);
                next_op_separator(filename, src, reg_tok, &mut tokens);
                let (r2, _) = next_reg_ident(filename, src, token, &mut tokens);
                items.push(Item::Instruction(Instruction::Add(r1, r2)));
            }
            "addc" => {
                let (r, reg_tok) = next_reg_ident(filename, src, token, &mut tokens);
                next_op_separator(filename, src, reg_tok, &mut tokens);
                let (n, _) = next_num(filename, src, token, &mut tokens)?;
                items.push(Item::Instruction(Instruction::AddConst(r, n)));
            }
            "sub" => {
                let (r1, reg_tok) = next_reg_ident(filename, src, token, &mut tokens);
                next_op_separator(filename, src, reg_tok, &mut tokens);
                let (r2, _) = next_reg_ident(filename, src, token, &mut tokens);
                items.push(Item::Instruction(Instruction::Sub(r1, r2)));
            }
            "subc" => {
                let (r, reg_tok) = next_reg_ident(filename, src, token, &mut tokens);
                next_op_separator(filename, src, reg_tok, &mut tokens);
                let (n, _) = next_num(filename, src, token, &mut tokens)?;
                items.push(Item::Instruction(Instruction::SubConst(r, n)));
            }
            "mul" => {
                let (r1, reg_tok) = next_reg_ident(filename, src, token, &mut tokens);
                next_op_separator(filename, src, reg_tok, &mut tokens);
                let (r2, _) = next_reg_ident(filename, src, token, &mut tokens);
                items.push(Item::Instruction(Instruction::Mul(r1, r2)));
            }
            "mulc" => {
                let (r, reg_tok) = next_reg_ident(filename, src, token, &mut tokens);
                next_op_separator(filename, src, reg_tok, &mut tokens);
                let (n, _) = next_num(filename, src, token, &mut tokens)?;
                items.push(Item::Instruction(Instruction::MulConst(r, n)));
            }
            "div" => {
                let (r1, reg_tok) = next_reg_ident(filename, src, token, &mut tokens);
                next_op_separator(filename, src, reg_tok, &mut tokens);
                let (r2, _) = next_reg_ident(filename, src, token, &mut tokens);
                items.push(Item::Instruction(Instruction::Div(r1, r2)));
            }
            "divc" => {
                let (r, reg_tok) = next_reg_ident(filename, src, token, &mut tokens);
                next_op_separator(filename, src, reg_tok, &mut tokens);
                let (n, _) = next_num(filename, src, token, &mut tokens)?;
                items.push(Item::Instruction(Instruction::DivConst(r, n)));
            }
            "loadlib" => items.push(Item::Instruction(Instruction::LoadLib)),
            "loadsym" => items.push(Item::Instruction(Instruction::LoadSym)),
            "syscall" => items.push(Item::Instruction(Instruction::Syscall)),
            "freelib" => items.push(Item::Instruction(Instruction::FreeLib)),
            _ => {
                crate::grim_error(
                    (filename, src, token.loc().byte_pos()),
                    "Unexpected identifier.",
                    [token.label(filename, "Identifier encountered here.", Color::Red)],
                    Some("You may have misspelled an instruction."),
                );
            }
        }
    }
    Ok(items)
}
