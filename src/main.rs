//! ¯\_(ツ)_/¯
//! TODO: comments because I can't remember what the code is even doing

mod codegen;
mod env;
mod lex;

use std::{
    env::args_os,
    path::PathBuf,
    process::ExitCode,
};

use env::{Opt, Options};

fn main() -> ExitCode {
    let args = args_os().map(|s| s.to_string_lossy().into_owned()).collect::<Vec<_>>();
    let res = env::eval_args(args);

    match res {
        Ok(opt) => match opt {
            Options::Help => env::help_msg(),
            Options::Version => env::version_info(),
            Options::Compile { file, mut src, options } => {
                fn default_output(file: &PathBuf) -> String {
                    file.file_stem().unwrap().to_str().unwrap().to_string() + ".ux"
                }

                let mut output = None;

                for option in options {
                    match option {
                        Opt::O { is_dir, path } => if is_dir {
                            output = Some(path + &default_output(&file))
                        } else {
                            output = Some(path);
                        },
                        _ => unreachable!(),
                    }
                }

                let output = output.unwrap_or(default_output(&file));
                // MAYBE: wait for file lock on output and then lock output
                let input = file.to_str().unwrap().to_string();                

                // Make file params &str????
                let res = lex::tokenize(&input, &mut src)
                    .and_then(|tokens| {
                        /*
                        for token in tokens.iter() {
                            println!("{:?}", token);
                        }
                        */

                        codegen::codegen(&input, &src, tokens, &output)
                    });

                if let Err(err) = res {
                    eprintln!("{}", err);
                    return ExitCode::from(101);
                }
            },
        },
        Err((errno, msg)) => {
            eprintln!("{}", msg);
            return ExitCode::from(errno as u8);
        },
    }

    ExitCode::SUCCESS
}
