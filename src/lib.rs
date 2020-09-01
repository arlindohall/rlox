use std::fs::File;
use std::io::{Read, BufRead};
use std::error::Error;

mod scanner;
use crate::scanner::Scanner;

pub fn run_file(name: &str) -> Result<(), Box<dyn Error>> {
    let mut contents = String::new();
    File::open(name)?.read_to_string(&mut contents)?;

    run(&contents);

    return Ok(());
}
pub fn run_prompt() -> Result<(), Box<dyn Error>> {
    println!("Getting input");
    let stdin = std::io::stdin();
    let lock = stdin.lock();

    for line in lock.lines() {
        run(&line?);
    }

    return Ok(());
}

fn run(snippet: &str) {
    let scanner = Scanner::new(snippet);
    let tokens = scanner.scan_tokens();

    for token in tokens {
        println!("{}", token);
    }
}