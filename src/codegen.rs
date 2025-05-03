use std::{
    fmt,
    fs::{self, File},
    io::Write,
    num::IntErrorKind,
    slice::Iter,
};

use crate::env::ansi::*;
use crate::lex::{
    CompError,
    Token,
    TokenData,
};

pub fn codegen<'a>(input: &'a String, src: &'a String, tokens: Vec<Token>, output: &'a String) -> Result<(), CompError> {
    let mut dst = Vec::new();
    BackEnd::init(input, src, &tokens, &mut dst).start_codegen()?;

    if let Ok(meta) = fs::metadata(output) {
        let mut perms = meta.permissions();
        perms.set_readonly(false);
        _ = fs::set_permissions(output, perms);
    }

    let mut out = match File::create(output) {
        Ok(out) => out,
        Err(err) => return Err(CompError::new(input.clone(), format!(
            "{ERR} parent directories of output file `{}` were moved or removed during TOCTOU: {}{NORM}",
            output,
            err
        ))),
    };

    if let Err(err) = out.write_all(&dst) {
        return Err(CompError::new(input.clone(), format!(
            "{ERR} failed to write to `{}`: {}{NORM}",
            output,
            err,
        )));
    }
        
    let mut perms = out.metadata().unwrap().permissions();
    perms.set_readonly(true);
    out.set_permissions(perms).unwrap();
    Ok(())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
enum TokenType {
    Reg,
    Imm,
    OpenBrack,
    CloseBrack,
    Offset,
    NegOffset,
    Comma,
    Ident,
    Op,
}

impl fmt::Display for TokenType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            TokenType::Reg => "register",
            TokenType::Imm => "immediate",
            TokenType::OpenBrack => "`[`",
            TokenType::CloseBrack => "`]`",
            TokenType::Offset => "`+`",
            TokenType::NegOffset => "`-`",
            TokenType::Comma => "`,`",
            TokenType::Ident => "identifier",
            TokenType::Op => "opcode",
        })?;
        Ok(())
    }
}

impl Token {
    fn typ(&self) -> TokenType {
        unsafe { *<*const _>::from(self.data()).cast::<TokenType>() }
    }
}

struct Expected<'a>(&'a [TokenType]);

impl<'a> fmt::Display for Expected<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        debug_assert!(self.0.len() != 0);

        let fmtted = if self.0.len() == 1 {
            self.0[0].to_string()
        } else {
            self.0.iter().enumerate()
            .fold(String::from("one of "), |msg, (i, typ)| if i == self.0.len() - 1 {
                format!("{}or {}", msg, typ.to_string())
            } else {
                format!("{}{}, ", msg, typ.to_string())
            })
        };

        f.write_str(&fmtted)?;
        Ok(())
    }
}

/*
enum RegArg {
    Reg(u8),
    Mem(u32),
}
*/

enum Imm {
    Byte(u8),
    Word(u16),
    Dword(u32),
    Qword(u64),
    Oword(u128),
}

enum Args {
    Nullary,
    Unary(u32),
    UnaryImm(Imm),
    Binary(u32, u32),
    BinaryImm(u32, Imm),
}

struct BackEnd<'ctx, 'f> {
    file: &'f String,
    src: &'f String,
    tokens: Iter<'ctx, Token>,
    curr: Option<&'ctx Token>,
    dst: &'ctx mut Vec<u8>,
}

fn parse_reg(ident: &str) -> (u8, u8) {
    let mut ident = ident.chars();
    let size = match ident.next().unwrap() {
        'b' => 0,
        'w' => 1,
        'd' => 2,
        'q' => 3,
        'o' => 4,
        _ => unreachable!(),
    };
    let reg = u8::from_str_radix(&ident.next().unwrap().to_string(), 16).unwrap();
    (size, reg << 1)
}

fn display_size(sized: u8) -> &'static str {
    match sized {
        0 => "byte",
        1 => "word",
        2 => "doubleword",
        3 => "quadword",
        4 => "octoword",
        _ => unreachable!(),
    }
}

fn display_num<T>(num: T, radix: u8) -> String
where
    T: fmt::Display + fmt::Binary + fmt::Octal + fmt::LowerHex,
{
    match radix {
        2 => format!("{:b}", num),
        8 => format!("{:o}", num),
        10 => format!("{}", num),
        16 => format!("{:x}", num),
        _ => unreachable!(),
    }
}

impl<'ctx, 'f> BackEnd<'ctx, 'f> {
    const MAGIC: [u8; 8] = [0x7f, 0x41, 0x52, 0x43, 0x00, 0x00, 0x01, 0x00];

    fn init(file: &'f String, src: &'f String, tokens: &'ctx Vec<Token>, dst: &'ctx mut Vec<u8>) -> Self {
        Self { file, src, tokens: tokens.iter(), dst, curr: None }
    }

    #[inline]
    fn throw<S: ToString>(&self, token: Token, msg: S) -> CompError {
        token.into_err(self.file.clone(), self.src.clone(), msg)
    }

    /// Tries to get the next token, returning a `CompError` if the token is not the expected token.
    /// 
    /// If there are no tokens left, this will also return a `CompError`.
    fn pop(&mut self, expect: &[TokenType]) -> Result<&Token, CompError> {
        let Some(token) = self.tokens.next() else {
            return Err(self.throw(self.curr.unwrap().clone(), format!("expected {}, found `<EOF>`", Expected(expect))));
        };

        match token.typ() {
            found if expect.contains(&found) => {
                self.curr = Some(token);
                Ok(token)
            },
            found => Err(self.throw(
                token.clone(),
                format!("expected {}, found {}", Expected(expect), found),
            )),
        }
    }

    /// Tries to get the next token, returning a `CompError` if the token is not the expected token.
    /// 
    /// If there are no tokens left, this will return `None`, otherwise, it will return `Some`,
    /// with a reference to the token.
    fn try_pop(&mut self, expect: &[TokenType]) -> Result<Option<&Token>, CompError> {
        let Some(token) = self.tokens.next() else {
            return Ok(None);
        };

        match token.typ() {
            found if expect.contains(&found) => {
                self.curr = Some(token);
                Ok(Some(token))
            },
            found => Err(self.throw(
                token.clone(),
                format!("expected {}, found {}", Expected(expect), found))),
        }
    }

    /*
    fn store_reg_arg(&mut self, arg: RegArg) {
        match arg {
            RegArg::Reg(reg) => self.dst.push(reg),
            RegArg::Mem(mem) => self.dst.extend_from_slice(&mem.to_le_bytes()),
        }
    }
    */

    fn store_ins(&mut self, op: u8, size: Option<u8>, args: Args) {
        let size = size.unwrap_or(0) as u64; // if instruction is unsized, `size` is implementation defined

        match args {
            Args::Nullary => self.dst.extend_from_slice(&(op as u64).to_le_bytes()),
            Args::Unary(reg) => {
                let mut ins = op as u64;
                ins |= size << 8;
                ins |= (reg as u64) << 12;
                self.dst.extend_from_slice(&ins.to_le_bytes());
            },
            Args::UnaryImm(imm) => {
                let mut ins = op as u64;
                ins |= size << 8;
                self.dst.extend_from_slice(&ins.to_le_bytes());
                self.store_imm(imm);
            },
            Args::Binary(reg1, reg2) => {
                let mut ins = op as u64;
                ins |= size << 8;
                //println!("{:026b}", reg1); // culprit
                ins |= (reg1 as u64) << 12;
                /*
                println!("{}", reg2);
                println!("{:026b}", reg2);
                println!("{}", reg2 >> 1);
                println!("{:064b}", ins);
                println!("{:064b}", (reg2 as u64) << 38);
                */
                ins |= (reg2 as u64) << 38;
                self.dst.extend_from_slice(&ins.to_le_bytes());
            },
            Args::BinaryImm(reg, imm) => {
                let mut ins = op as u64;
                ins |= size << 8;
                ins |= (reg as u64) << 12;
                self.dst.extend_from_slice(&ins.to_le_bytes());
                self.store_imm(imm);
            },
        }
    }

    fn store_imm(&mut self, arg: Imm) {
        match arg {
            Imm::Byte(imm) => self.dst.extend_from_slice(&imm.to_le_bytes()),
            Imm::Word(imm) => self.dst.extend_from_slice(&imm.to_le_bytes()),
            Imm::Dword(imm) => self.dst.extend_from_slice(&imm.to_le_bytes()),
            Imm::Qword(imm) => self.dst.extend_from_slice(&imm.to_le_bytes()),
            Imm::Oword(imm) => self.dst.extend_from_slice(&imm.to_le_bytes()),
        }
    }

    /// Continues the code generation, parsing the next statement, returning the result of the compilation.
    fn poll(&mut self) -> Result<Option<()>, CompError> {
        let token = {
            let Some(token) = self.try_pop(&[TokenType::Op])? else {
                return Ok(None);
            };
            token.clone()
        };
        let TokenData::Op(op) = token.data() else { unreachable!() };
        let op = *op;

        Ok(Some(match op {
            // Unimplemented
            0x2b..=0x32 => return Err(
                self.throw(token, "this opcode is not yet implemented in the UArc specification")
                    .note_msg("for more information on opcodes, see <TODO: father>")
            ),
            // Nullary
            0x00 | 0x87 | 0x88 | 0x89 => self.store_ins(op, None, Args::Nullary),
            // Unary
            0x01 => {
                let (size, arg1) = self.parse_reg_arg(&token)?;
                self.store_ins(op, Some(size), Args::Unary(arg1));
            },
            // Binary
            0x02 | 0x04 | 0x05 | 0x07 | 0x09 | 0x0b | 0x0d | 0x0f | 0x11 | 0x13 | 0x15 | 0x17 | 0x19 |
            0x24 | 0x26 | 0x28 | 0x2a | 0x33 | 0x35 | 0x37 | 0x39 | 0x3b | 0x3d | 0x3f | 0x41 | 0x43 |
            0x45 | 0x47 | 0x4e | 0x50 | 0x52 | 0x54 | 0x56 | 0x58 | 0x5a | 0x5c | 0x61 | 0x62 | 0x63 |
            0x65 | 0x67 | 0x69 | 0x6b | 0x6d => {
                let (size, arg1) = self.parse_reg_arg(&token)?;
                let _ = self.pop(&[TokenType::Comma])?;
                let arg2 = self.parse_reg_arg_size(size, &token)?;
                self.store_ins(op, Some(size), Args::Binary(arg1, arg2));
            },
            // Binary Immediate
            0x03 | 0x06 | 0x08 | 0x0a | 0x0c | 0x0e | 0x10 | 0x12 | 0x14 | 0x16 | 0x18 | 0x25 | 0x27 |
            0x29 | 0x34 | 0x36 | 0x38 | 0x3a | 0x3c | 0x3e | 0x40 | 0x42 | 0x44 | 0x46 | 0x4f | 0x51 |
            0x53 | 0x55 | 0x57 | 0x59 | 0x5b | 0x5d | 0x64 | 0x66 | 0x68 | 0x6a | 0x6c | 0x6e => {
                let (size, arg1) = self.parse_reg_arg(&token)?;
                let _ = self.pop(&[TokenType::Comma])?;
                let arg2 = self.parse_imm(size, &token)?;
                self.store_ins(op, Some(size), Args::BinaryImm(arg1, arg2));
            },
            // Binary Shift
            0x1a | 0x1c | 0x1e | 0x20 | 0x22 | 0x48 | 0x4a | 0x4c => {
                let (size, arg1) = self.parse_reg_arg(&token)?;
                let _ = self.pop(&[TokenType::Comma])?;
                let arg2 = self.parse_reg_arg_param_size::<2>(&token)?; // u32
                self.store_ins(op, Some(size), Args::Binary(arg1, arg2));
            },
            // Binary Shift Immediate
            0x1b | 0x1d | 0x1f | 0x21 | 0x23 | 0x49 | 0x4b | 0x4d => {
                let (size, arg1) = self.parse_reg_arg(&token)?;
                let _ = self.pop(&[TokenType::Comma])?;
                let arg2 = self.parse_imm(2, &token)?; // u32
                self.store_ins(op, Some(size), Args::BinaryImm(arg1, arg2));
            },
            // Binary Bit Count
            0x5e..=0x60 => {
                let arg1 = self.parse_reg_arg_param_size::<2>(&token)?; // u32
                let _ = self.pop(&[TokenType::Comma])?;
                let (size, arg2) = self.parse_reg_arg(&token)?;
                self.store_ins(op, Some(size), Args::Binary(arg1, arg2));
            },
            // Unary Jump
            0x6f | 0x71 | 0x73 | 0x75 | 0x77 | 0x79 | 0x7b | 0x7d | 0x7f | 0x81 | 0x83 | 0x85 => {
                let arg1 = self.parse_jmp_target_imm(&token)?;
                self.store_ins(op, None, Args::UnaryImm(arg1));
            },
            // Unary Jump Register
            0x70 | 0x72 | 0x74 | 0x76 | 0x78 | 0x7a | 0x7c | 0x7e | 0x80 | 0x82 | 0x84 | 0x86 => {
                let arg1 = self.parse_reg_arg_param_size::<2>(&token)?; // u32
                self.store_ins(op, None, Args::Unary(arg1));
            },
            0x8a..=0xff => unreachable!(),
        }))
    }

    /// The `Imm` returned will always be `Imm::Dword(u32)`.
    fn parse_jmp_target_imm(&mut self, op_token: &Token) -> Result<Imm, CompError> {
        const PI_FLAG: u32 = 0b1 << 31;
        let token = match self.pop(&[TokenType::Imm, TokenType::Offset, TokenType::NegOffset]) {
            Ok(token) => token,
            Err(err) => return Err(err.note_msg_from("argument to this opcode's instruction is incorrect", self.src.clone(), op_token.clone())),
        };

        match token.data() {
            TokenData::Imm { base, lit } => {
                match u32::from_str_radix(lit, *base as u32) {
                    Ok(imm) => if imm < 0x80000000 { Ok(Imm::Dword(imm)) } else {
                        let token = token.clone();
                        let max = display_num(0x80000000u32, *base);
                        Err(self.throw(token, format!("immediate overflows the max value `{}` for an instruction address", max)))
                    },
                    Err(err) => match err.kind() {
                        IntErrorKind::PosOverflow => {
                            let token = token.clone();
                            let max = display_num(0x80000000u32, *base);
                            Err(self.throw(token, format!("immediate overflows the max value `{}` for an instruction address", max)))
                        },
                        _ => unreachable!(),
                    }
                }
            },
            TokenData::Offset(neg) | TokenData::NegOffset(neg) => {
                let neg = *neg;
                let token = self.pop(&[TokenType::Imm])?;
                let TokenData::Imm { base, lit } = token.data() else { unreachable!() };
                let imm = match u32::from_str_radix(lit, *base as u32) {
                    Ok(imm) => if imm < 0x40000000 { Ok(imm) } else {
                        let token = token.clone();
                        let max = display_num(0x40000000u32, *base);
                        Err(self.throw(token, format!("immediate overflows the max value `{}` for an instruction address offset", max)))
                    },
                    Err(err) => match err.kind() {
                        IntErrorKind::PosOverflow => {
                            let token = token.clone();
                            let max = display_num(0x40000000u32, *base);
                            Err(self.throw(token, format!("immediate overflows the max value `{}` for an instruction address offset", max)))
                        },
                        _ => unreachable!(),
                    }
                }?;

                let imm = if neg { imm.wrapping_neg() } else { imm };
                Ok(Imm::Dword(imm | PI_FLAG))
            },
            _ => unreachable!(),
        }
    }

    fn _parse_reg_arg(&mut self, op_token: &Token) -> Result<(Token, u8, u32), CompError> {
        let token = match self.pop(&[TokenType::Reg, TokenType::OpenBrack]) {
            Ok(token) => token,
            Err(err) => return Err(err.note_msg_from("argument to this opcode's instruction is incorrect", self.src.clone(), op_token.clone())),
        };

        match token.data() {
            TokenData::Reg(ident) => {
                let (size, reg) = parse_reg(ident);
                let token = token.clone();

                if size == 4 {
                    Err(self.throw(token, "cannot use octoword registers directly"))
                } else {
                    Ok((token, size, reg as u32))
                }
            },
            TokenData::OpenBrack => {
                let reg_token = self.pop(&[TokenType::Reg])?.clone();
                let TokenData::Reg(ident) = reg_token.data() else { unreachable!() };
                let (size, reg) = parse_reg(ident);
                let token = self.pop(&[TokenType::CloseBrack, TokenType::Offset, TokenType::NegOffset])?;

                match token.data() {
                    TokenData::CloseBrack => {
                        //println!("{}", (reg as u32 | 0b1) >> 1);
                        Ok((reg_token, size, reg as u32 | 0b1))
                    },
                    TokenData::Offset(neg) | TokenData::NegOffset(neg) => {
                        let neg = *neg;
                        let token = self.pop(&[TokenType::Imm])?;
                        let TokenData::Imm { base, lit } = token.data() else { unreachable!() };
                        let imm = match u32::from_str_radix(lit, *base as u32) {
                            Ok(imm) => if imm < 0x100000 { Ok(imm) } else {
                                let token = token.clone();
                                let max = display_num(0x100000, *base);
                                Err(self.throw(token, format!("immediate overflows the max value `{}` for an address offset", max)))
                            },
                            Err(err) => match err.kind() {
                                IntErrorKind::PosOverflow => {
                                    let token = token.clone();
                                    let max = display_num(0x100000, *base);
                                    Err(self.throw(token, format!("immediate overflows the max value `{}` for an address offset", max)))
                                },
                                _ => unreachable!(),
                            }
                        }?;

                        _ = self.pop(&[TokenType::CloseBrack])?;
                        const REG_MASK: u32 = !(0b111111 << 26);
                        let imm = if neg { (imm.wrapping_neg() << 5) & REG_MASK } else { imm << 5 };
                        Ok((reg_token, size, imm | reg as u32 | 0b1))
                    },
                    _ => unreachable!(),
                }
            },
            _ => unreachable!(),
        }
    }

    fn parse_reg_arg(&mut self, op_token: &Token) -> Result<(u8, u32), CompError> {
        let (_, size, reg_arg) = self._parse_reg_arg(op_token)?;
        Ok((size, reg_arg))
    }

    fn parse_reg_arg_size(&mut self, sized: u8, op_token: &Token) -> Result<u32, CompError> {
        let (reg_token, size, reg_arg) = self._parse_reg_arg(op_token)?;

        if size == sized {
            Ok(reg_arg)
        } else {
            let token = reg_token.clone();
            Err(self.throw(token, format!(
                "expected a {}-sized register found a {}-sized register",
                display_size(sized), display_size(size))
                ).note_msg_from("size inferred from other arguments to this opcode's instruction", self.src.clone(), op_token.clone()))
        }
    }

    fn parse_reg_arg_param_size<const SIZED: u8>(&mut self, op_token: &Token) -> Result<u32, CompError> {
        let (reg_token, size, reg_arg) = self._parse_reg_arg(op_token)?;

        if size == SIZED {
            Ok(reg_arg)
        } else {
            let token = reg_token.clone();
            Err(self.throw(token, format!(
                "expected a {}-sized register found a {}-sized register",
                display_size(SIZED), display_size(size))
                ).note_msg_from("argument to this opcode's instruction is incorrect", self.src.clone(), op_token.clone()))
        }
    }

    fn parse_imm(&mut self, sized: u8, op_token: &Token) -> Result<Imm, CompError> {
        let token = match self.pop(&[TokenType::Imm]) {
            Ok(token) => token,
            Err(err) => return Err(err.note_msg_from("argument to this opcode's instruction is incorrect", self.src.clone(), op_token.clone())),
        };
        let TokenData::Imm { base, lit } = token.data() else { unreachable!() };

        macro_rules! parse_arm {
            ($T:ident, $size:ident, $dp_size:expr) => {
                match $T::from_str_radix(lit, *base as u32) {
                    Ok(imm) => Ok(Imm::$size(imm)),
                    Err(err) => match err.kind() {
                        IntErrorKind::PosOverflow => {
                            let token = token.clone();
                            let max = display_num($T::MAX, *base);
                            Err(self.throw(token, format!("immediate overflows the max value `{}` for a {}", max, $dp_size)))
                        },
                        _ => unreachable!(),
                    }
                }
            };
        }

        match sized {
            0 => parse_arm!(u8, Byte, "byte"),
            1 => parse_arm!(u16, Word, "word"),
            2 => parse_arm!(u32, Dword, "doubleword"),
            3 => parse_arm!(u64, Qword, "quadword"),
            4 => parse_arm!(u128, Oword, "octoword"),
            _ => unreachable!(),
        }
    }

    fn start_codegen(&mut self) -> Result<(), CompError> {
        self.dst.extend_from_slice(&Self::MAGIC);
        while let Some(_) = self.poll()? {}
        Ok(())
    }
}
