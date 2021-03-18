// Ignore while building
#![ allow( dead_code, unused_imports, unused_variables, unused_must_use ) ]

use std::error::Error;
use std::fs::File;
use std::io::{BufRead, Read};

use rlox::lox::Lox;

fn main() -> Result<(), Box<dyn Error>> {
    let args: Vec<String> = std::env::args().collect();
    let mut lox = Lox::new();

    /*
    The book has two methods, run_file and run_prompt, that handle two
    different behaviors. However, I think this way of organizing makes more
    sense, where the main class handles all IO operations directly (it could
    run_prompt and run_file, but I don't think there's a clear benefit to
    separating them into two methods) and delegates all "pure" behavior to
    the Lox class.

    This way Lox doesn't need to know about File IO.
    */
    if args.len() > 2 {
        println!("Usage: jlox [script]");
        std::process::exit(64);
    } else if args.len() == 2 {
        let mut contents = String::new();
        let name = &args[1];
        File::open(name)?.read_to_string(&mut contents)?;

        lox.run(contents);
        if lox.had_error {
            std::process::exit(65);
        } else if lox.had_runtime_error {
            std::process::exit(70);
        }
    } else {
        println!("Getting input");
        let stdin = std::io::stdin();
        let lock = stdin.lock();

        for line in lock.lines() {
            // TODO: Better error handling here, probably addressed in book
            lox.run(line?);
            lox.had_error = false;
        }
        println!("Go Tigers!");
    }

    Ok(())
}
