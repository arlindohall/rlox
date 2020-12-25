use std::error::Error;
use std::fs::File;
use std::io::{BufRead, Read};

use rlox::lox::Lox;

fn main() -> Result<(), Box<dyn Error>> {
    let args: Vec<String> = std::env::args().collect();
    let mut lox = Lox::new();

    /*
    The book has two methods, run_file and run_prompt, that handle
    two different behaviors. However, I think this way of organizing
    makes more sense, where the main class handles all IO operations
    directly (it could run_prompt and run_file, but I don't think
    there's a clear benefit to separating them into two methods) and
    delegates all "pure" behavior to the Lox class.

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
        } else {
            println!("Done!");
        }
    } else {
        println!("Getting input");
        let stdin = std::io::stdin();
        let lock = stdin.lock();

        for line in lock.lines() {
            lox.run(line?);
            lox.had_error = false;
        }
        println!("Done!");
    }

    Ok(())
}

/*
This function doesn't work, first of all. It needs to be run in
the scope of lox. However, it shows off the behavior from the
section on visitor patterns without chaning the overall program.

It'll probably be redundant after a few more chapters so I'll
remove it then.
*/
// use rlox::lox::{Token, Expression};
// fn main() -> () {
//     let expression = Expression::binary(
//         Expression::unary(
//             Token {
//                 token_type: TokenType::Minus,
//                 lexeme: String::from("-"),
//                 literal: Literal::None,
//                 line: 1
//             },
//             Expression::literal(Literal::LoxNumber(123.0)),
//         ),
//         Token {
//             token_type: TokenType::Star ,
//             lexeme: String::from("*"),
//             literal: Literal::None,
//             line: 1
//         },
//         Expression::grouping(
//             Expression::literal(Literal::LoxNumber(45.67))
//         ),
//     );

//     println!("{}", expression.print());
// }
