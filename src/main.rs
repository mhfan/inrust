
use std::io;
use std::io::Write;
use std::cmp::Ordering;

use rand::Rng;

#[allow(unused_macros)]
//macro_rules! var_args { ($($args: expr), *) => {{ }} }  //$(f($args);)*     // XXX
macro_rules! printvar { ($var: expr) => { println!("{}: {}", stringify!($var), $var); } }

fn main() { // src/main.rs (default application entry point)
    println!("Hello, world!\n");

    //let x: Result<u32, &str> = Err("Emergency Failure");
    //x.expect("Testing expect");

    let (max, lang) = (100, true);
    if  lang { println!("### 猜数字游戏 (1-{}) ###", max) } else {
        println!("Game guess the number (1-{})", max);
    }

   let secret = rand::thread_rng().gen_range(1..=max);
   //printvar!(secret);

    loop {
        if lang { print!("\n输入你猜的数字: ") } else { print!("\nInput a number you guess: ") }
        io::stdout().flush().expect("Failed to flush"); //.unwrap();

        let mut guess = String::new();
        io::stdin().read_line(&mut guess).expect("Failed to read!");
        let guess = guess.trim();   //printvar!(guess);

        //let guess: i32 = guess.parse().expect("Please type a number");

        //match guess { Ok(guess) => { ... }, _ => () }
        if let Ok(guess) = guess.parse::<i32>() { // isize
            match guess.cmp(&secret) {
                Ordering::Greater   =>   if lang { println!("[大了]") } else { println!("[Too large]") },
                Ordering::Less      =>   if lang { println!("[小了]") } else { println!("[Too small]") },
                Ordering::Equal     => { if lang { println!("[你赢了!]") } else { println!("[Bingo!]") } break }
            }
        } else if guess.to_lowercase() == "quit" { break }
    }
}
