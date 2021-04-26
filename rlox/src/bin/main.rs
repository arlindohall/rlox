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

        match lox.run(contents) {
            Ok(_) => (),
            Err(e) => println!("continuing after error: {}", e.to_string()),
        }
        if rlox::lox::had_error() {
            std::process::exit(65);
        } else if rlox::lox::had_runtime_error() {
            std::process::exit(70);
        }
    } else {
        println!("Getting input");
        let stdin = std::io::stdin();
        let lock = stdin.lock();

        for line in lock.lines() {
            match lox.run(line?) {
                Ok(_) => (),
                Err(e) => println!("Error: {}", e.to_string()),
            };
            rlox::lox::clear_errors();
        }
        println!("Go Tigers!");
    }

    Ok(())
}
