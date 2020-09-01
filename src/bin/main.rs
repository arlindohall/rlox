use std::error::Error;

use rlox::{run_file, run_prompt};

fn main() -> Result<(), Box<dyn Error>> {
    let args: Vec<String> = std::env::args().collect();

    if args.len() > 2 {
        println!("Usage: jlox [script]");
        std::process::exit(64);
    } else if args.len() == 2 {
        if let Ok(_) = run_file(&args[0]) {
            println!("Done!");
        }
    } else {
        if let Ok(_) = run_prompt() {
            println!("Done!");
        }
    }

    return Ok(());
}
