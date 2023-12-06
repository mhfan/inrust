
//mod common;   // subdirectory module

#[test] fn largest() {  let array = [1, 2, 3];
    assert_eq!(inrust::misc::largest(&array), &array[2]);
    // Integration tests (and benchmarks) 'depend' to the crate
    // like a 3rd party would. Hence, they only see public items.
}

use {inrust::calc24::*, yansi::Paint, std::error::Error};
#[test] fn inrust_cli() -> Result<(), Box<dyn Error>> {
    //let tnow = std::time::Instant::now();
    let mut ptys = rexpect::spawn(concat!(env!("CARGO_BIN_EXE_inrust"),
        " -A 0 -g 24"), Some(1_000))?;   // XXX: " -a a -G a 1 2 a"
    let inps = r"\n.*Input .+ for .+: ";
    ptys.exp_regex(inps)?;

    ptys.send_line("1 2 3 4")?;
    ptys.send_line("g24")?;         ptys.exp_regex(r"\n.*Reset GOAL to .*24.*")?;

    ptys.send_line("cards")?;
    let ns = ptys.exp_regex(r"\n( .*[2-9AJQK].*){4}: ")?.1;
    //println!(r"{}s: ", tnow.elapsed().as_secs_f32());

    // XXX: how to just disable ansi escape codes for a pty/tty?
    let ns = regex::Regex::new( // regex for ANSI escape codes
        r"\x1b\[([\x30-\x3f]*[\x20-\x2f]*[\x40-\x7e])").unwrap().replace_all(&ns, "");
    let nums = ns.chars().filter_map(|n| match n {
            ' ' | '\n' | '\r' | ':'   => None, _ => Some(match n {
            'T' => 10, 'J' => 11, 'Q' => 12, 'K' => 13, 'A' => 1, //'2'..='9'
            _   => n as i32 - '0' as i32 }.into()) }).collect::<Vec<_>>();
    let sol = calc24_first(&24.into(), &nums[(nums.len() - 4)..], DynProg);

    ptys.send_line(sol.as_str())?;  ptys.exp_regex(r".*Bingo.+: ")?;
    ptys.send_line("N1")?;          ptys.exp_regex(r"\n.*Solution.*: .+")?;
    ptys.send_line("1*2*3*4")?;     ptys.exp_regex(r"\n.*Tryagain.*: ")?;
    ptys.send_line("quit")?;        ptys.exp_regex(inps)?;

    ptys.send_line("exit")?;        ptys.exp_eof()?;    Ok(())
}

#[test] fn game24_sols() -> Result<(), Box<dyn Error>> {  // XXX: many unwraps
    use std::{fs::File, io::{BufRead, BufReader}};
    BufReader::new(File::open("tests/game24_sols.fmh")?)
        .lines().for_each(|line| line.unwrap().split(':')
            .last().unwrap().split(',').for_each(|str| if !str.is_empty() {
                //let str = str.chars.map(|ch|  // cargo r -- -G > tests/game24_sols.fmh
                //    match ch { '×' => '*', '÷' => '/', _ => ch }).collect::<String>();
                assert!(str.parse::<Expr>().is_ok_and(|e|
                    e.value() == &24.into()), "failed at: `{str}'");
            }));

    let mut cnt = (0, 0);   // https://4shu.net/solutions/allsolutions/
    BufReader::new(File::open("tests/game24_sols.txt")?)
        .lines().for_each(|line| if let Ok(line) = line {
            let mut cols = line.split('\t');
            let nstr = cols.next().unwrap();

            let nums = nstr.split(' ')  // split_ascii_whitespace
                .map(|s| s.parse::<Rational>().unwrap()).collect::<Vec<_>>();
            let exps = calc24_coll(&24.into(), &nums, DynProg);

            let sols = cols.collect::<Vec<_>>();
            cnt.0 += 1u32;  cnt.1 += sols.len() as u32;

            assert_eq!(exps.len(), sols.len(), r"[{}]: {:?}\n[{}]: {:?}",   // line,
                Paint::cyan(nstr), Paint::magenta(&sols), Paint::cyan(nstr), Paint::green(&exps));
        });

    /* TODO: try use tokio and scraper to extract url and parse html?
    let mut rdr = csv::ReaderBuilder::new()
        .has_headers(false).delimiter(b'\t').flexible(true)
        .trim(csv::Trim::All).from_path("tests/game24_sols.txt").unwrap();

    for record in rdr.records() {
        let record = record.unwrap();
        cnt.0 += 1usize;    cnt.1 += record.len() - 1;

        let nums = record[0].split(' ').map(|s|
            s.parse::<i32>().unwrap().into()).collect::<Vec<_>>();
        let exps = calc24_coll(&24.into(), &nums, DynProg);

        assert_eq!(exps.len(), record.len() - 1, r"{:?}\n[{}]: {:?}", record,
            Paint::cyan(&record[0]), Paint::green(exps));
    }*/ assert!(cnt == (1362, 3017), r"records: {}, solutions: {}",
            Paint::red(&cnt.0), Paint::red(&cnt.1));    Ok(())
}

