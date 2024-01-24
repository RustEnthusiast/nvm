use ariadne::{Color, Label};
use core::{iter::Peekable, ops::Range, str::Chars};

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

/// Represents a numeric literal's base/radix.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Radix {
    /// Base 2.
    Bin,
    /// Base 8.
    Oct,
    /// Base 10.
    Default,
    /// Base 16.
    Hex,
}
impl Radix {
    /// Converts a `Radix` value into a `u32`.
    #[inline]
    pub(super) fn as_u32(&self) -> u32 {
        match self {
            Self::Bin => 2,
            Self::Oct => 8,
            Self::Default => 10,
            Self::Hex => 16,
        }
    }
}

/// Describes the type of a token.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum TokenType {
    /// An identifier token.
    Ident,
    /// A numeric token.
    Num(Radix),
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
        &self,
        filename: &'id str,
        msg: &str,
        color: Color,
    ) -> Label<(&'id str, Range<usize>)> {
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
fn skip_num(chars: &mut Peekable<Chars>, loc: &mut SrcLoc, base: Radix) {
    let check = match base {
        Radix::Bin => |c: char| c == '0' || c == '1',
        Radix::Oct => |c: char| matches!(c, '0'..='7'),
        Radix::Default => |c: char| matches!(c, '0'..='9'),
        Radix::Hex => |c: char| matches!(c, '0'..='9' | 'a'..='f' | 'A'..='F'),
    };
    while let Some(chr) = chars.peek().copied() {
        if check(chr) {
            chars.next();
            unsafe { loc.next_unchecked(chr) };
        } else {
            break;
        }
    }
}

pub(super) fn lex<'src>(filename: &str, src: &'src str) -> Vec<Token<'src>> {
    let mut chars = src.chars().peekable();
    let mut loc = SrcLoc::default();
    let mut tokens = Vec::new();
    while let Some(chr) = skip_whitespace(&mut chars, &mut loc) {
        let mut token_loc = loc;
        unsafe { loc.next_unchecked(chr) };
        if chr == '_' || unicode_ident::is_xid_start(chr) {
            skip_ident(&mut chars, &mut loc);
            tokens.push(Token {
                loc: token_loc,
                tok: &src[token_loc.byte_pos..loc.byte_pos],
                ty: TokenType::Ident,
            });
        } else if chr.is_numeric() {
            let mut base = Radix::Default;
            if chr == '0' {
                match chars.peek() {
                    Some(r) if r.eq_ignore_ascii_case(&'b') => base = Radix::Bin,
                    Some(r) if r.eq_ignore_ascii_case(&'o') => base = Radix::Oct,
                    Some(r) if r.eq_ignore_ascii_case(&'x') => base = Radix::Hex,
                    _ => {}
                }
                if base != Radix::Default {
                    // SAFETY: The next character is a numeric literal radix specifier.
                    unsafe { loc.next_unchecked(chars.next().unwrap_unchecked()) };
                    token_loc = loc;
                }
            }
            skip_num(&mut chars, &mut loc, base);
            tokens.push(Token {
                loc: token_loc,
                tok: &src[token_loc.byte_pos..loc.byte_pos],
                ty: TokenType::Num(base),
            });
        } else if chr.is_ascii_punctuation() {
            tokens.push(Token {
                loc: token_loc,
                tok: &src[token_loc.byte_pos..loc.byte_pos],
                ty: TokenType::Punct,
            });
        } else {
            crate::salvo_error(
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
