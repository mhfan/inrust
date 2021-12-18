
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

    //let _a = [1; 5]; //_a.len();
    //let _a = [1, 2, 3, 4, 5];
    //for i in _a { println!("{:?}", i); }
    //for i in (1..5).rev() { println!("{:?}", i); }

    guess_number();
}

fn  guess_number() {
    let (max, lang) = (100, true);

    if  lang { println!("### 猜数字游戏 (1-{}) ###", max) } else {
        println!("Guess the number (1-{})", max);
    }

   let secret = rand::thread_rng().gen_range(1..=max);
   //printvar!(secret);

    let _result = 'label: loop {
        if lang { print!("\n输入你猜的数字: ") } else { print!("\nInput a number you guess: ") }
        io::stdout().flush().expect("Failed to flush"); //.unwrap();

        let mut guess = String::new();
        io::stdin().read_line(&mut guess).expect("Failed to read!");
        //printvar!(guess);

        //let guess: i32 = guess.parse().expect("Please type a number");

        //match guess.trim().parse::<i32>() { Ok(_guess) => { }, _ => () }
        if let Ok(guess) = guess.trim().parse::<i32>() { // isize
            match guess.cmp(&secret) {
                Ordering::Greater   =>   if lang { println!("[太大了]") } else { println!("[Too large]") },
                Ordering::Less      =>   if lang { println!("[太小了]") } else { println!("[Too small]") },
                Ordering::Equal     => { if lang { println!("[猜对了]") } else { println!("[Bingo!]") } break 1 }
            }
        } else { guess.make_ascii_lowercase();  //guess.to_lowercase();
            if   guess.trim() == "quit" { break 'label 0 }
        }
    };
}
