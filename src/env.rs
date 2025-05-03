//! Interactions with command-line arguments.

use std::{
    fmt,
    fs::{self, OpenOptions},
    io::{self, Write},
    slice::Iter,
    path::{PathBuf, MAIN_SEPARATOR},
    process,
};

pub mod ansi {
    //! ANSI escape codes for formatting status messages.
    
    /// Bold and default.
    pub const BOLD: &str = "\x1B[1m";

    /// Bold and red for error annotations.
    pub const ELINE: &str = "\x1B[1;31m";

    /// Bold and green for note annotations.
    pub const NLINE: &str = "\x1B[1;32m";

    /// Bold and cyan for headers
    pub const BLD_CYAN: &str = "\x1B[1;36m";

    /// Bold and red snippet of error header and then set to bold and white.
    /// 
    /// Value of `ERR` is `"error:"`.
    pub const ERR: &str = "\x1B[1;31merror\x1B[39m:";

    /// Bold and green snippet of note header and then set to bold and white.
    /// 
    /// Value of `NOTE` is `"note:"`.
    pub const NOTE: &str = "\x1B[1;32mnote\x1B[39m:";

    /// Reset to default.
    pub const NORM: &str = "\x1B[m";
}

use ansi::*;

/// Version number.
const VERSION: Option<&str> = option_env!("CARGO_PKG_VERSION");

const U_HELP: [&str; 2] =    ["-h, --help", "       Print help"];
const U_VERSION: [&str; 2] = ["-V, --version", "    Print version info"];
const U_O: [&str; 2] =       ["-o <filepath>", "    Write output to <filepath>"];

fn usage(src: [&str; 2]) -> String {
    format!("  {BOLD}{}{NORM}{}", src[0], src[1])
}

/// Print help message.
pub fn help_msg() {
    print!("{BLD_CYAN}OVERVIEW:{NORM} Susm, a UArc assembler\n\n");
    print!("{BLD_CYAN}USAGE:{NORM} {BOLD}susm [options] <input>\n\n");
    print!("{BLD_CYAN}OPTIONS:{NORM}\n");
    print!("{}\n", usage(U_HELP));
    print!("{}\n", usage(U_VERSION));
    print!("{}\n", usage(U_O));

    let Ok(_) = io::stdout().flush() else {
        process::abort();
    };
}

/// Print version info.
pub fn version_info() {
    println!("{BLD_CYAN}VERSION:{NORM} susm v{} (UArc v0.1.0)", VERSION.unwrap_or("<unknown>"));
}

// Represents a `susm` command-line argument.
enum Arg {
    Input(String),
    Opt(Opt),
}

/// Represents a `susm` command-line option.
#[derive(PartialEq, Eq)]
#[repr(u8)]
#[non_exhaustive]
pub enum Opt {
    Help,
    Version,
    O { is_dir: bool, path: String },
}

impl fmt::Display for Opt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Opt::Help => "help",
            Opt::Version => "version",
            Opt::O { .. } => "o",
        })?;
        Ok(())
    }
}

enum ParseArgError {
    UnrecognizedOpt(String),
    OsError(i32, String),
    MissingArg { option: String, usage: String },
}

fn parse_arg(args: &mut Iter<'_, String>) -> Option<Result<Arg, ParseArgError>> {
    let arg = args.next()?;

    Some(Ok(Arg::Opt(match arg.as_str() {
        "-h" | "--help" => Opt::Help,
        "-V" | "--version" => Opt::Version,
        "-o" => match args.next() {
            Some(arg) => {
                let path = PathBuf::from(arg);
                let exists = path.exists();

                if path.is_dir() && arg.ends_with(MAIN_SEPARATOR) {
                    Opt::O { is_dir: true, path: arg.clone() }
                } else {
                    match OpenOptions::new().write(true).create(true).open(arg) {
                        Err(err) => return Some(Err(ParseArgError::OsError(
                            err.raw_os_error().unwrap(),
                            format!("{ERR} cannot open `{}` to write output to: {}{NORM}", arg, err),
                        ))),
                        _ => {
                            if !exists {
                                fs::remove_file(path).unwrap();
                            }
                            Opt::O { is_dir: false, path: arg.clone() }
                        },
                    }
                }
            },
            _ => return Some(Err(ParseArgError::MissingArg { option: "-o".into(), usage: usage(U_O) })),
        },
        option if option.starts_with("-") => {
            return Some(Err(ParseArgError::UnrecognizedOpt(option.trim_start_matches('-').to_string())));
        },
        _ => return Some(Ok(Arg::Input(arg.clone()))),
    })))
}

/*
pub fn hr_opt(opt: &str) -> &'static str {
    match opt {
        "-h" | "--help" => "help",
        "-V" | "--version" => "version",
        "-o" => "o",
        _ => unreachable!(),
    }
}
*/

/// Represents command-line options that are inputted into `susm`.
#[non_exhaustive]
pub enum Options {
    /// The help option. Overrides all other options.
    Help,
    /// The version info option. Overrides all other options execpt the help option.
    Version,
    /// An input file is sepcified and no overriding options are specified.
    /// Contains the name of the file and source code in the file for compilation.
    Compile { file: PathBuf, src: String, options: Vec<Opt> },
}

/// Evaluates command-line arguments.
/// 
/// If the options are invalid this will return an error code and an error message.
/// Otherwise, a `Options` (representing the parsed command-line arguments) will be returned.
pub fn eval_args(args: Vec<String>) -> Result<Options, (i32, String)> {
    /*
    if args.len() < 2 {
        return Err((1, format!("{ERR} no input file{NORM}")));
    }
    */

    let mut args = args[1..].into_iter();
    let mut input = None;
    let mut options = Vec::new();

    while let Some(arg) = parse_arg(&mut args) {
        match arg {
            Ok(arg) => match arg {
                Arg::Input(filepath) => if let Some(input) = input {
                    return Err((1, format!(
                        "{ERR} multiple input filepaths are provided (first two are `{}` and `{}`){NORM}",
                        input,
                        filepath,
                    )));
                } else {
                    input = Some(filepath);
                },
                Arg::Opt(option) => if options.contains(&option) {
                    return Err((1, format!("{ERR} option '{}' inputted multiple times{NORM}", option)));
                } else {
                    options.push(option);
                },
            },
            Err(err) => match err {
                ParseArgError::UnrecognizedOpt(option) => return Err((1,
                    format!("{ERR} unrecognized option '{}'{NORM}", option),
                )),
                ParseArgError::OsError(errno, msg) => return Err((errno, msg)),
                ParseArgError::MissingArg { option, usage } => return Err((1,
                    format!("{ERR} missing argument to option '{}'\n{BLD_CYAN}USAGE:\n{}", option, usage),
                )),
            },
        }
    }

    if options.contains(&Opt::Help) {
        Ok(Options::Help)
    } else if options.contains(&Opt::Version) {
        Ok(Options::Version)
    } else {
        match &input {
            Some(input) => match fs::read_to_string(input) {
                Ok(src) => Ok(Options::Compile { file: PathBuf::from(input), src, options }),
                Err(err) => Err((
                    err.raw_os_error().unwrap(),
                    format!("{ERR} failed to read `{}`: {}{NORM}", input, err),
                )),
            },
            _ => Err((1, format!("{ERR} no input file{NORM}"))),
        }
    }
}
