
use std::io;
use std::io::Write;
use std::cmp::Ordering;

use rand::Rng;

fn main() {
    println!("Hello, world!\n");

    //let x: Result<u32, &str> = Err("Emergency Failure");
    //x.expect("Testing expect");

    let max  = 100;
    let lang = true;

    if  lang { println!("### 猜数字游戏 (1-{}) ###", max) } else {
        println!("Game guess the number (1-{})", max);
    }

   let secret = rand::thread_rng().gen_range(1..=max);
    //println!("The secret Number is {}", secret);

    loop {
        if lang { print!("\n输入你的猜测: ") } else { print!("\nPlease input your guess: ") }
        io::stdout().flush().expect("Failed to flush"); //.unwrap();

        let mut guess = String::new();
        io::stdin().read_line(&mut guess).expect("Failed to read!");
        //println!("You guessed: {}", guess);

        //let guess: i32 = guess.trim().parse().expect("Please type a number");
        let guess = guess.trim().parse::<i32>();

        //if  guess.is_err() { continue }
        //let guess = guess.expect("");
        
        //if let Ok(guess) = guess {
        //} //else { continue }
        match  guess {
            Ok(guess) => {
                match guess.cmp(&secret) {
                    Ordering::Greater   =>   if lang { println!("[大了]") } else { println!("[Too large]") },
                    Ordering::Less      =>   if lang { println!("[小了]") } else { println!("[Too small]") },
                    Ordering::Equal     => { if lang { println!("[你赢了!]") } else { println!("[Bingo!]") } break }
                }
            } 

            _ => ()
        }
        
    }
}
