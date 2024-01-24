use crate::lexer::{Radix, Token, TokenType};
use ariadne::Color;
use core::slice::Iter;

/// A literal expression.
pub(super) enum LiteralExpression<'src> {
    /// An integer literal.
    Int(&'src str, Radix),
}

/// Describes an expression.
pub(super) enum Expression<'src> {
    /// A literal expression.
    Literal(LiteralExpression<'src>),
}

/// A series of statements that may evaluate into an expression.
pub(super) enum Statements<'src> {
    /// A single expression.
    Expression(Expression<'src>),
}

/// Describes a block expression.
pub(super) enum BlockExpression<'src> {
    /// A unit/empty block expression.
    Unit,
    /// A series of statements that may evaluate into an expression.
    Statements(Statements<'src>),
}
impl<'src> BlockExpression<'src> {
    /// Parses a block expression.
    fn parse(filename: &str, src: &str, tokens: &mut Iter<'src, Token>, last_pos: usize) -> Self {
        match tokens.next() {
            Some(open_bracket)
                if open_bracket.ty() == TokenType::Punct && open_bracket.tok() == "{" =>
            {
                match tokens.next() {
                    Some(next) => match next.ty() {
                        TokenType::Punct if next.tok() == "}" => Self::Unit,
                        TokenType::Num(radix) => match tokens.next() {
                            Some(close) if close.ty() == TokenType::Punct && close.tok() == "}" => {
                                Self::Statements(Statements::Expression(Expression::Literal(
                                    LiteralExpression::Int(next.tok(), radix),
                                )))
                            }
                            _ => {
                                crate::salvo_error(
                                    (filename, src, next.loc().byte_pos()),
                                    "Expected a closing brace after an expression.",
                                    [next.label(
                                        filename,
                                        "Expression encountered here.",
                                        Color::Red,
                                    )],
                                    None,
                                )
                            }
                        },
                        _ => crate::salvo_error(
                            (filename, src, open_bracket.loc().byte_pos()),
                            "Expected a closing bracket after an opening bracket.",
                            [],
                            None,
                        ),
                    },
                    _ => crate::salvo_error(
                        (filename, src, open_bracket.loc().byte_pos()),
                        "Expected a closing bracket after an opening bracket.",
                        [],
                        None,
                    ),
                }
            }
            _ => crate::salvo_error(
                (filename, src, last_pos),
                "Expected an opening bracket at the beginning of a block expression.",
                [],
                None,
            ),
        }
    }
}

/// Describes a function.
pub(super) struct Fn<'src> {
    /// The function's identifier.
    name: &'src str,
    /// The block expression.
    block: BlockExpression<'src>,
}
impl<'src> Fn<'src> {
    /// Returns a function's identifier.
    #[inline]
    pub(super) fn name(&self) -> &str {
        self.name
    }

    /// Returns an immutable reference to the function's block expression.
    #[inline]
    pub(super) fn block(&self) -> &BlockExpression {
        &self.block
    }

    /// Parses a function.
    fn parse(filename: &str, src: &str, tokens: &mut Iter<'src, Token>, token: &Token) -> Self {
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
                                return Self {
                                    name: ident.tok(),
                                    block: BlockExpression::parse(
                                        filename,
                                        src,
                                        tokens,
                                        ident.loc().byte_pos(),
                                    ),
                                };
                            }
                            _ => crate::salvo_error(
                                (filename, src, ident.loc().byte_pos()),
                                "Expected a block expression.",
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
                "Expected a function definition.",
                [token.label(filename, "Unexpected token encountered here.", Color::Red)],
                None,
            );
        }
    }
}

/// Describes a Salvo item.
pub(super) enum Item<'src> {
    /// A function.
    Fn(Fn<'src>),
}
impl<'src> Item<'src> {
    /// Parses an item.
    fn parse(filename: &str, src: &str, tokens: &mut Iter<'src, Token>, token: &Token) -> Self {
        if token.ty() == TokenType::Ident && token.tok() == "fn" {
            Self::Fn(Fn::parse(filename, src, tokens, token))
        } else {
            crate::salvo_error(
                (filename, src, token.loc().byte_pos()),
                "Expected an item definition.",
                [token.label(filename, "Unexpected token encountered here.", Color::Red)],
                None,
            );
        }
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
        items.push(Item::parse(filename, src, &mut tokens, token));
    }
    items
}
