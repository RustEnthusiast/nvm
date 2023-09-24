use crate::lexer::{Token, TokenType};
use ariadne::Color;
use core::slice::Iter;

/// Describes a Salvo item.
pub(super) enum Item<'src> {
    /// A function.
    Fn(Fn<'src>),
}

/// Describes a function.
pub(super) struct Fn<'src> {
    /// The function's identifier.
    name: &'src str,
}
impl Fn<'_> {
    /// Returns a function's identifier.
    #[inline]
    pub(super) fn name(&self) -> &str {
        self.name
    }
}

/// Turns Salvo source tokens into items.
pub(super) fn parse<'src>(
    filename: &str,
    src: &str,
    mut tokens: Iter<'src, Token>,
) -> Vec<Item<'src>> {
    let mut items = Vec::new();
    while let Some(token) = tokens.next() {
        if token.ty() == TokenType::Ident && token.tok() == "fn" {
            match tokens.next() {
                Some(ident) if ident.ty() == TokenType::Ident => match tokens.next() {
                    Some(open_brace)
                        if open_brace.ty() == TokenType::Punct && open_brace.tok() == "(" =>
                    {
                        match tokens.next() {
                            Some(close_brace)
                                if close_brace.ty() == TokenType::Punct
                                    && close_brace.tok() == ")" =>
                            {
                                match tokens.next() {
                                    Some(open_bracket)
                                        if open_bracket.ty() == TokenType::Punct
                                            && open_bracket.tok() == "{" =>
                                    {
                                        match tokens.next() {
                                            Some(close_bracket)
                                                if close_bracket.ty() == TokenType::Punct
                                                    && close_bracket.tok() == "}" => {
                                                        items.push(Item::Fn(Fn {
                                                            name: ident.tok(),
                                                        }));
                                                    }
                                            _ => crate::salvo_error(
                                                (filename, src, ident.loc().byte_pos()),
                                                "Expected a closing bracket after an opening bracket.",
                                                [ident.label(
                                                    filename,
                                                    "Function identifier encountered here.",
                                                    Color::Red,
                                                )],
                                                None,
                                            ),
                                        }
                                    }
                                    _ => crate::salvo_error(
                                        (filename, src, ident.loc().byte_pos()),
                                        "Expected an opening bracket after a function identifier.",
                                        [ident.label(
                                            filename,
                                            "Function identifier encountered here.",
                                            Color::Red,
                                        )],
                                        None,
                                    ),
                                }
                            }
                            _ => crate::salvo_error(
                                (filename, src, ident.loc().byte_pos()),
                                "Expected a closing brace after an opening brace.",
                                [ident.label(
                                    filename,
                                    "Function identifier encountered here.",
                                    Color::Red,
                                )],
                                None,
                            ),
                        }
                    }
                    _ => crate::salvo_error(
                        (filename, src, ident.loc().byte_pos()),
                        "Expected an opening brace after a function identifier.",
                        [ident.label(
                            filename,
                            "Function identifier encountered here.",
                            Color::Red,
                        )],
                        None,
                    ),
                },
                _ => crate::salvo_error(
                    (filename, src, token.loc().byte_pos()),
                    "Expected an identifier after the `fn` keyword.",
                    [token.label(filename, "Function definition starts here.", Color::Red)],
                    None,
                ),
            }
        } else {
            crate::salvo_error(
                (filename, src, token.loc().byte_pos()),
                "Expected an item definition.",
                [token.label(filename, "Unexpected token encountered here.", Color::Red)],
                None,
            );
        }
    }
    items
}
