use ariadne::{Color, Label};
use std::{borrow::Cow, iter::Peekable, ops::Range, str::Chars};

/// Contains data about a token's source location.
#[derive(Clone, Copy, Default)]
pub(super) struct SrcLoc {
    /// The byte offset.
    byte_pos: usize,
    /// The Unicode scalar value offset.
    char_pos: usize,
    /// The line index.
    line: usize,
    /// The column index.
    col: usize,
}
impl SrcLoc {
    /// Returns the token's byte offset.
    #[inline]
    pub(super) fn byte_pos(&self) -> usize {
        self.byte_pos
    }

    /// Consumes a character.
    fn next(&mut self, chr: char) {
        self.byte_pos += chr.len_utf8();
        self.char_pos += 1;
        if chr == '\n' {
            self.line += 1;
            self.col = 0;
        } else {
            self.col += 1;
        }
    }

    /// Consumes a non-newline character.
    ///
    /// # SAFETY
    ///
    /// `chr` must not be the newline character (`\n`).
    #[inline]
    unsafe fn next_unchecked(&mut self, chr: char) {
        self.byte_pos += chr.len_utf8();
        self.char_pos += 1;
        self.col += 1;
    }
}

/// Describes the type of a token.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum TokenType {
    /// An identifier token.
    Ident,
    /// A numeric token.
    Num,
    /// A punctuation token.
    Punct,
}

/// Describes a standalone token within Grim source code.
pub(super) struct Token<'tok> {
    /// The token's starting location.
    loc: SrcLoc,
    /// The token string slice.
    tok: &'tok str,
    /// The token type.
    ty: TokenType,
}
impl Token<'_> {
    /// Returns the token's source location.
    #[inline]
    pub(super) fn loc(&self) -> &SrcLoc {
        &self.loc
    }

    /// Returns a string slice of the token.
    #[inline]
    pub(super) fn tok(&self) -> &str {
        self.tok
    }

    /// Returns the token's type.
    #[inline]
    pub(super) fn ty(&self) -> TokenType {
        self.ty
    }

    /// Creates a [`Label`] for a token.
    #[inline]
    pub(super) fn label<'id>(
        &'id self,
        filename: &'id Cow<str>,
        msg: &str,
        color: Color,
    ) -> Label<(&'id Cow<str>, Range<usize>)> {
        Label::new((
            filename,
            self.loc.byte_pos..self.loc.byte_pos + self.tok().len(),
        ))
        .with_message(msg)
        .with_color(color)
    }
}

/// Skips whitespace.
fn skip_whitespace(chars: &mut Peekable<Chars>, loc: &mut SrcLoc) -> Option<char> {
    for chr in chars {
        if !chr.is_whitespace() {
            return Some(chr);
        }
        loc.next(chr);
    }
    None
}

/// Skips over an identifier.
fn skip_ident(chars: &mut Peekable<Chars>, loc: &mut SrcLoc) {
    while let Some(chr) = chars.peek().copied() {
        if unicode_ident::is_xid_continue(chr) {
            chars.next();
            unsafe { loc.next_unchecked(chr) };
        } else {
            break;
        }
    }
}

/// Skips over a numerical token.
fn skip_num(chars: &mut Peekable<Chars>, loc: &mut SrcLoc) {
    while let Some(chr) = chars.peek().copied() {
        if chr.is_numeric() {
            chars.next();
            unsafe { loc.next_unchecked(chr) };
        } else {
            break;
        }
    }
}

/// Skips over a comment token.
fn skip_comment(chars: &mut Peekable<Chars>, loc: &mut SrcLoc) {
    while let Some(chr) = chars.next() {
        if chr == '\n' {
            loc.next(chr);
            break;
        } else {
            unsafe { loc.next_unchecked(chr) };
        }
    }
}

/// Turns Grim source code into a series of low level tokens.
pub(super) fn lex<'src>(filename: &Cow<str>, src: &'src str) -> Vec<Token<'src>> {
    let mut chars = src.chars().peekable();
    let mut loc = SrcLoc::default();
    let mut tokens = Vec::new();
    while let Some(chr) = skip_whitespace(&mut chars, &mut loc) {
        let token_loc = loc;
        unsafe { loc.next_unchecked(chr) };
        if chr == '_' || unicode_ident::is_xid_start(chr) {
            skip_ident(&mut chars, &mut loc);
            tokens.push(Token {
                loc: token_loc,
                tok: &src[token_loc.byte_pos..loc.byte_pos],
                ty: TokenType::Ident,
            });
        } else if chr.is_numeric() {
            skip_num(&mut chars, &mut loc);
            tokens.push(Token {
                loc: token_loc,
                tok: &src[token_loc.byte_pos..loc.byte_pos],
                ty: TokenType::Num,
            });
        } else if chr == ';' {
            skip_comment(&mut chars, &mut loc);
        } else if chr.is_ascii_punctuation() {
            tokens.push(Token {
                loc: token_loc,
                tok: &src[token_loc.byte_pos..loc.byte_pos],
                ty: TokenType::Punct,
            });
        } else {
            crate::grim_error(
                (filename, src, token_loc.byte_pos),
                "Unexpected token.",
                [
                    Label::new((filename, token_loc.byte_pos..token_loc.byte_pos + 1))
                        .with_message("Token encountered here.")
                        .with_color(Color::Red),
                ],
                None,
            );
        }
    }
    tokens
}
