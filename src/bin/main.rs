use std::error::Error;

use rlox::lox::Lox;

fn main() -> Result<(), Box<dyn Error>> {
    let args: Vec<String> = std::env::args().collect();

    if args.len() > 2 {
        println!("Usage: jlox [script]");
        std::process::exit(64);
    } else if args.len() == 2 {
        if let Ok(_) = Lox::new().run_file(&args[1]) {
            println!("Done!");
        }
    } else {
        if let Ok(_) = Lox::new().run_prompt() {
            println!("Done!");
        }
    }

    return Ok(());
}
