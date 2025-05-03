use std::{
    fmt,
    iter::Peekable,
    str::Chars,
};

use crate::env::ansi::*;

struct Src<'a> {
    src: &'a String,
    start: Loc,
}

impl<'a> Src<'a> {
    fn chars(&'a self) -> Chars<'a> {
        self.src[self.start.idx..].chars()
    }
}

const _: fn(bool) -> TokenData = TokenData::Offset; // WUT!

/// Remove unecessary characters from the source code.
fn normalize<'a>(file: &String, src: &'a mut String) -> Result<Src<'a>, CompError> {
    // Remove BOM
    if src.starts_with('\u{FEFF}') {
        src.remove(0);
    }

    // Normalize CRLF sequences
    *src = src.replace("\r\n", "\n");

    let is_invalid = |ch| {
        match ch {
            // ASCII control characters
            '\u{0000}' ..= '\u{0008}' | '\u{000b}' ..= '\u{001f}' | '\u{007f}' |
            // Non-ASCII line endings (in case they are supported)
            '\u{0085}' | '\u{2028}' | '\u{2029}' => true,
            _ => false,
        }
    };

    if src.contains(is_invalid) {
        return Err(CompError::new(file.clone(), "source contains unallowed Unicode code points"));
    }

    /*
    // Skip byte order mark
    let mut start = if src.starts_with('\u{FEFF}') {
        println!("sus");
        Loc { line: 1, col: 2, idx: 1, b_idx: '\u{FEFF}'.len_utf8() }
    } else {
        println!("not sus");
        Loc { line: 1, col: 1, idx: 0, b_idx: 0 }
    };
    */

    // BOM is already skipped?
    let mut start = Loc { line: 1, col: 1, idx: 0, b_idx: 0 };

    // Skip Shebang
    if src.chars().skip(start.idx).take(2).collect::<String>() == "#!" {
        start.col += 2;
        start.idx += 2;
        start.b_idx += 2;

        for ch in src[start.idx..].chars() {
            match ch {
                '\n' => {
                    start.line = 2;
                    start.col = 1;
                    start.idx += 1;
                    start.b_idx += 1;
                    break;
                },
                ch => {
                    start.col += 1;
                    start.idx += 1;
                    start.b_idx += ch.len_utf8();
                },
            }
        }
    }

    Ok(Src { src, start })
}

pub fn tokenize<'a>(file: &'a String, src: &'a mut String) -> Result<Vec<Token>, CompError> {
    let src = normalize(&file, src)?;
    let lexer = Lexer::init(file, &src);
    let mut tokens = Vec::new();

    for token in lexer {
        tokens.push(token?);
    }

    Ok(tokens)
}

/// The location of a token.
#[derive(Clone, Copy, Debug)]
pub struct Loc {
    line: u32,
    col: u32,
    idx: usize,
    b_idx: usize,
}

impl fmt::Display for Loc {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!("{}:{}", self.line, self.col))?;
        Ok(())
    }
}

pub struct CompError {
    file: String,
    msg: String,
    ctx: Option<(String, Loc, usize)>,
    note_msg: Option<(String, Option<(String, Loc, usize)>)>,
}

impl CompError {
    pub fn new<S: ToString>(file: String, msg: S) -> Self {
        Self { file, msg: msg.to_string(), ctx: None, note_msg: None }
    }

    pub fn at<S: ToString>(file: String, src: String, loc: Loc, end: usize, msg: S) -> Self {
        Self {
            file,
            msg: msg.to_string(),
            ctx: Some((src, loc, end)),
            note_msg: None,
        }
    }

    pub fn note_msg<S: ToString>(mut self, note_msg: S) -> Self {
        self.note_msg = Some((note_msg.to_string(), None));
        self
    }

    pub fn note_msg_at<S: ToString>(mut self, note_msg: S, src: String, loc: Loc, end: usize) -> Self {
        self.note_msg = Some((note_msg.to_string(), Some((src, loc, end))));
        self
    }

    pub fn note_msg_from<S: ToString>(self, note_msg: S, src: String, token: Token) -> Self {
        self.note_msg_at(note_msg, src, token.loc, token.end)
    }
}

impl fmt::Display for CompError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn line_ends(src: &String, loc: &Loc) -> (usize, usize) {
            let line = src.bytes().collect::<Vec<_>>();
            let mut line_start = 0;
            for i in (0..loc.b_idx).rev() {
                if line[i] == b'\n' {
                    line_start = i + 1;
                    break;
                }
            }

            let mut line_end = src.len();
            for i in loc.b_idx..line_end {
                if line[i] == b'\n' {
                    line_end = i;
                    break;
                }
            }

            (line_start, line_end)
        }

        if let Some((src, loc, end)) = &self.ctx {
            f.write_fmt(format_args!("{}:{}: {ERR} {}{NORM}\n", self.file, loc, self.msg))?;

            let (line_start, line_end) = line_ends(src, loc);
            let line = &src[line_start..line_end];
            let lineno = loc.line.to_string();
            let lineno_pad = " ".repeat(lineno.len());
            f.write_fmt(format_args!("{} |\n", lineno_pad))?;
            f.write_fmt(format_args!("{} | {}\n", lineno, line))?;

            let annot_pad = " ".repeat(loc.col as usize - 1);
            let annot = format!("{ELINE}^{}{NORM}", "~".repeat(end - loc.idx as usize));
            f.write_fmt(format_args!("{} | {}{}", lineno_pad, annot_pad, annot))?;

            if let Some((msg, ctx)) = &self.note_msg {
                if let Some((src, loc, end)) = ctx {
                    f.write_fmt(format_args!("\n{}:{}: {NOTE} {}{NORM}\n", self.file, loc, msg))?;

                    let (line_start, line_end) = line_ends(src, loc);
                    let line = &src[line_start..line_end];
                    let lineno = loc.line.to_string();
                    let lineno_pad = " ".repeat(lineno.len());
                    f.write_fmt(format_args!("{} |\n", lineno_pad))?;
                    f.write_fmt(format_args!("{} | {}\n", lineno, line))?;

                    let annot_pad = " ".repeat(loc.col as usize - 1);
                    let annot = format!("{NLINE}^{}{NORM}", "-".repeat(end - loc.idx as usize));
                    f.write_fmt(format_args!("{} | {}{}", lineno_pad, annot_pad, annot))?;
                } else {
                    f.write_fmt(format_args!("\n{}:{}: {NOTE} {}{NORM}", self.file, loc, msg))?;
                }
            }
        } else {
            f.write_fmt(format_args!("{}: {ERR} {}{NORM}", self.file, self.msg))?;
        }

        Ok(())
    }
}

#[derive(Clone, Debug)]
#[repr(u8)]
pub enum TokenData {
    Reg(String),
    Imm { base: u8, lit: String },
    OpenBrack,
    CloseBrack,
    /// Always `false`.
    Offset(bool),
    /// Always `true`.
    NegOffset(bool),
    Comma,
    Ident(String),
    Op(u8),
}

/// A token.
#[derive(Clone, Debug)]
pub struct Token {
    data: TokenData,
    loc: Loc,
    /// Points directly to the corresponding index in the source of the *last* character of the token.
    end: usize,
}

impl Token {
    fn new(data: TokenData, loc: Loc, end: usize) -> Self {
        Self { data, loc, end }
    }

    pub fn data(&self) -> &TokenData {
        &self.data
    }

    pub fn into_err<'a, S: ToString>(self, file: String, src: String, msg: S) -> CompError {
        CompError::at(file, src, self.loc, self.end, msg)
    }
}

struct Lexer<'a> {
    file: &'a String,
    src: &'a String,
    chars: Peekable<Chars<'a>>,
    cursor: Loc,
}

impl<'a> Lexer<'a> {
    /// Initializes a lexer from a `Src`.
    /// 
    /// See [`normalize`] which creates a `Src`.
    fn init(file: &'a String, src: &'a Src<'a>) -> Self {
        Self {
            file,
            src: src.src,
            chars: src.chars().peekable(),
            cursor: src.start,
        }
    }

    /// Returns the current cursor and character.
    /// 
    /// Advances the lexer to the next character and moves the cursor.
    fn pop(&mut self) -> (Loc, Option<char>) {
        let start = self.cursor;

        (start, match self.chars.next() {
            Some(ch) if ch == '\n' => {
                self.cursor.line += 1;
                self.cursor.col = 1;
                self.cursor.idx += 1;
                self.cursor.b_idx += 1;
                Some(ch)
            },
            Some(ch) => {
                self.cursor.col += 1;
                self.cursor.idx += 1;
                self.cursor.b_idx += ch.len_utf8();
                Some(ch)
            },
            _ => None,
        })
    }

    /// Returns the current cursor and character.
    /// 
    /// Neither advances the lexer nor moves the cursor.
    fn peek(&mut self) -> (Loc, Option<&char>) {
        let start = self.cursor;

        (start, self.chars.peek())
    }

    #[inline]
    fn throw<S: ToString>(&self, loc: Loc, end: usize, msg: S) -> CompError {
        CompError::at(self.file.clone(), self.src.clone(), loc, end, msg)
    }

    fn take_imm(&mut self, start: Loc) -> Result<Token, CompError> {
        let mut lit = String::new();
        let (_, opt) = self.pop();
        let Some(ch) = opt else {
            return Err(self.throw(start, start.idx, "immediate is empty"));
        };

        let base = if ch == '0' {
            let (loc, opt) = self.peek();

            let base = match opt {
                Some('b') => 2,
                Some('o') => 8,
                Some('x') => 16,
                Some(&ch) if ch.is_ascii_alphabetic() => {
                    return Err(self.throw(
                        loc,
                        loc.idx,
                        format!("invalid base prefix `{}`", ch),
                    ).note_msg("valid base prefixes are `b` (binary), `o` (octal), and `x` (hexadecimal)."));
                },
                Some(&ch) if ch.is_ascii_digit() => {
                    lit.push('0');
                    lit.push(ch);
                    10
                },
                _ => return Ok(Token::new(TokenData::Imm { base: 10, lit: "0".into() }, start, start.idx)),
            };

            _ = self.pop();
            base
        } else {
            lit.push(ch);
            10
        };
        
        while let (_, Some(ch)) = self.peek() {
            match ch {
                '_' => _ = self.pop(),
                &ch if ch.is_digit(base as u32) => {
                    lit.push(ch);
                    _ = self.pop();
                },
                _ => break,
            }
        };

        let end = self.cursor.idx - 1;

        if lit.chars().count() == 0 {
            return Err(self.throw(start, end, "immediate is empty"));
        }

        Ok(Token::new(TokenData::Imm { base, lit }, start, end))
    }

    fn take_ident(&mut self, ch: char, start: Loc) -> Token {
        let mut ident = String::from(ch);
        
        while let (_, Some(ch)) = self.peek() {
            match ch {
                ',' | ' ' | '\t' | '\n' => {
                    break;
                },
                &ch => {
                    ident.push(ch);
                    _ = self.pop();
                },
            }
        }

        let end = self.cursor.idx - 1;

        eval_ident(ident, start, end)
    }

    fn take_reg(&mut self, start: Loc) -> Result<Token, CompError> {
        let mut ident = String::new();
        
        while let (_, Some(ch)) = self.peek() {
            match ch {
                '[' | ']' | '+' | '-' | ',' | ' ' | '\t' | '\n' => {
                    break;
                },
                &ch => {
                    ident.push(ch);
                    _ = self.pop();
                },
            }
        }

        let end = self.cursor.idx - 1;

        match ident.as_str() {
            "b0" | "b1" | "b2" | "b3" | "b4" | "b5" | "b6" | "b7" | "b8" | "b9" | "ba" |
            "w0" | "w1" | "w2" | "w3" | "w4" | "w5" | "w6" | "w7" | "w8" | "w9" | "wa" |
            "d0" | "d1" | "d2" | "d3" | "d4" | "d5" | "d6" | "d7" | "d8" | "d9" | "da" |
            "q0" | "q1" | "q2" | "q3" | "q4" | "q5" | "q6" | "q7" | "q8" | "q9" | "qa" |
            "o0" | "o1" | "o2" | "o3" | "o4" | "o5" | "o6" | "o7" | "o8" | "o9" | "oa" => Ok(
                Token::new(TokenData::Reg(ident), start, end)
            ),
            _ => Err(self.throw(start, end, format!("invalid register `{}`", ident))
                .note_msg("for more information on registers, see <TODO: father>")),
        }
    }

    fn _comment(&mut self) {
        while let (_, Some(ch)) = self.pop() {
            match ch {
                '\n' => break,
                _ => {/* Skip comment character */},
            }
        }
    }

    fn _block_comment(&mut self, start: Loc) -> Result<(), CompError> {
        loop {
            match self.pop() {
                (_, Some('}')) => match self.peek() {
                    (_, Some('@')) => {
                        _ = self.pop();
                        break;
                    },
                    _ => {/* Fall back */},
                },
                (start, Some('@')) => self.skip_comment(start)?,
                (loc, None) => return Err(
                    CompError::at(self.file.clone(), self.src.clone(), loc, loc.idx,
                    "block comment is never terminated",
                    ).note_msg_at(
                        "block comment starts here", 
                        self.src.clone(), start, start.idx,
                    )
                ),
                _ => {/* Skip comment character */},
            }
        }

        Ok(())
    }

    fn skip_comment(&mut self, start: Loc) -> Result<(), CompError> {
        if let (_, Some(ch)) = self.peek() {
            match ch {
                '{' => self._block_comment(start)?,
                _ => self._comment(),
            }
        }
        
        Ok(())
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Result<Token, CompError>;

    fn next(&mut self) -> Option<Self::Item> {
        while let (start, Some(ch)) = self.pop() {
            // Make sure that `self.loc` is at the character
            // intended to be acquired by `self.chars.next()`
            // at the end of the following match statement
            match ch {
                ' ' | '\t' | '\n' => {/* Skip whitespace */},
                '@' => if let Err(err) = self.skip_comment(start) {
                    return Some(Err(err));
                },
                '%' => return Some(self.take_reg(start)),
                '#' => return Some(self.take_imm(start)),
                '[' => return Some(Ok(Token::new(TokenData::OpenBrack, start, start.idx))),
                ']' => return Some(Ok(Token::new(TokenData::CloseBrack, start, start.idx))),
                '+' => return Some(Ok(Token::new(TokenData::Offset(false), start, start.idx))),
                '-' => return Some(Ok(Token::new(TokenData::NegOffset(true), start, start.idx))),
                ',' => return Some(Ok(Token::new(TokenData::Comma, start, start.idx))),
                ch if ch.is_ascii_alphabetic() || ch == '_' =>
                    return Some(Ok(self.take_ident(ch, start))),
                ch => return Some(Err(self.throw(start, start.idx, format!("invalid start of token `{}`", ch)))),
            }
        }

        None
    }
}

fn eval_ident(ident: String, start: Loc, end: usize) -> Token {
    Token::new(TokenData::Op(match ident.as_str() {
        "nop" => 0x00,
        "clr" => 0x01,
        "str" => 0x02,
        "stri" => 0x03,
        "swp" => 0x04,
        "add" => 0x05,
        "addi" => 0x06,
        "uadd" => 0x07,
        "uaddi" => 0x08,
        "sub" => 0x09,
        "subi" => 0x0a,
        "usub" => 0x0b,
        "usubi" => 0x0c,
        "mul" => 0x0d,
        "muli" => 0x0e,
        "umul" => 0x0f,
        "umuli" => 0x10,
        "div" => 0x11,
        "divi" => 0x12,
        "udiv" => 0x13,
        "udivi" => 0x14,
        "rem" => 0x15,
        "remi" => 0x16,
        "urem" => 0x17,
        "uremi" => 0x18,
        "neg" => 0x19,
        "shl" => 0x1a,
        "shli" => 0x1b,
        "shr" => 0x1c,
        "shri" => 0x1d,
        "sar" => 0x1e,
        "sari" => 0x1f,
        "rol" => 0x20,
        "roli" => 0x21,
        "ror" => 0x22,
        "rori" => 0x23,
        "and" => 0x24,
        "andi" => 0x25,
        "or" => 0x26,
        "ori" => 0x27,
        "xor" => 0x28,
        "xori" => 0x29,
        "not" => 0x2a,
        "adc" => 0x2b,
        "adci" => 0x2c,
        "uadc" => 0x2d,
        "uadci" => 0x2e,
        "sbb" => 0x2f,
        "sbbi" => 0x30,
        "usbb" => 0x31,
        "usbbi" => 0x32,
        "adw" => 0x33,
        "adwi" => 0x34,
        "uadw" => 0x35,
        "uadwi" => 0x36,
        "sbw" => 0x37,
        "sbwi" => 0x38,
        "usbw" => 0x39,
        "usbwi" => 0x3a,
        "mlw" => 0x3b,
        "mlwi" => 0x3c,
        "umlw" => 0x3d,
        "umlwi" => 0x3e,
        "dvw" => 0x3f,
        "dvwi" => 0x40,
        "udvw" => 0x41,
        "udvwi" => 0x42,
        "remw" => 0x43,
        "remwi" => 0x44,
        "uremw" => 0x45,
        "uremwi" => 0x46,
        "negw" => 0x47,
        "shlw" => 0x48,
        "shlwi" => 0x49,
        "shrw" => 0x4a,
        "shrwi" => 0x4b,
        "sarw" => 0x4c,
        "sarwi" => 0x4d,
        "ads" => 0x4e,
        "adsi" => 0x4f,
        "uads" => 0x50,
        "uadsi" => 0x51,
        "sbs" => 0x52,
        "sbsi" => 0x53,
        "usbs" => 0x54,
        "usbsi" => 0x55,
        "mls" => 0x56,
        "mlsi" => 0x57,
        "umls" => 0x58,
        "umlsi" => 0x59,
        "dvs" => 0x5a,
        "dvsi" => 0x5b,
        "udvs" => 0x5c,
        "udvsi" => 0x5d,
        "ctpop" => 0x5e,
        "ctlz" => 0x5f,
        "cttz" => 0x60,
        "brev" => 0x61,
        "rvbit" => 0x62,
        "max" => 0x63,
        "maxi" => 0x64,
        "umax" => 0x65,
        "umaxi" => 0x66,
        "min" => 0x67,
        "mini" => 0x68,
        "umin" => 0x69,
        "umini" => 0x6a,
        "cmp" => 0x6b,
        "cmpi" => 0x6c,
        "ucmp" => 0x6d,
        "ucmpi" => 0x6e,
        "jeq" => 0x6f,
        "jeqr" => 0x70,
        "jne" => 0x71,
        "jner" => 0x72,
        "jlt" => 0x73,
        "jltr" => 0x74,
        "jgt" => 0x75,
        "jgtr" => 0x76,
        "jle" => 0x77,
        "jler" => 0x78,
        "jge" => 0x79,
        "jger" => 0x7a,
        "jo" => 0x7b,
        "jor" => 0x7c,
        "jno" => 0x7d,
        "jnor" => 0x7e,
        "jc" => 0x7f,
        "jcr" => 0x80,
        "jnc" => 0x81,
        "jncr" => 0x82,
        "j" => 0x83,
        "jr" => 0x84,
        "jl" => 0x85,
        "jrl" => 0x86,
        "lnk" => 0x87,
        "yld" => 0x88,
        "syscall" => 0x89,
        _ => return Token::new(TokenData::Ident(ident), start, end),
    }), start, end)
}
