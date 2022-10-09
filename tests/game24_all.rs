
//mod common;   // subdirectory module

#[test] fn largest() {
    let array = [1, 2, 3];
    assert_eq!(inrust::largest(&array), &array[2]);
    // Integration tests (and benchmarks) 'depend' to the crate
    // like a 3rd party would. Hence, they only see public items.
}

#[test] fn game24_all() {
    use {inrust::calc24::*, yansi::Paint};

    use std::{fs::File, io::{BufRead, BufReader}};
    BufReader::new(File::open("tests/game24_all.fmh").unwrap())
        .lines().for_each(|line| line.unwrap().split(':')
            .last().unwrap().split(' ').for_each(|str| if !str.is_empty() {
                //let str = str.chars.map(|ch|
                //    match ch { '×' => '*', '÷' => '/', _ => ch }).collect::<String>();
                assert_eq!((mexe::eval(str).unwrap() + 0.1) as i32, 24, "failed at: `{str}'");
            }));    // split_ascii_whitespace

    let mut cnt = (0, 0);   // https://4shu.net/solutions/allsolutions/
    BufReader::new(File::open("tests/game24_all.txt").unwrap())
        .lines().for_each(|line| if let Ok(line) = line {
            let mut cols = line.split('\t');
            let nstr = cols.next().unwrap();

            let nums = nstr.split(' ').map(|s|
                s.parse::<i32>().unwrap().into()).collect::<Vec<_>>();
            let exps = calc24_coll(&24.into(), &nums, DynProg);

            let sols = cols.collect::<Vec<_>>();
            cnt.0 += 1usize;    cnt.1 += sols.len();

            assert_eq!(exps.len(), sols.len(), r"[{}]: {:?}\n[{}]: {:?}",   // line,
                Paint::cyan(nstr), Paint::magenta(sols), Paint::cyan(nstr), Paint::green(exps));
        });

    /* TODO: try use tokio and scraper to extract url and parse html?
    let mut rdr = csv::ReaderBuilder::new()
        .has_headers(false).delimiter(b'\t').flexible(true)
        .trim(csv::Trim::All).from_path("tests/game24_all.txt").unwrap();

    for record in rdr.records() {
        let record = record.unwrap();
        cnt.0 += 1usize;    cnt.1 += record.len() - 1;

        let nums = record[0].split(' ').map(|s|
            s.parse::<i32>().unwrap().into()).collect::<Vec<_>>();
        let exps = calc24_coll(&24.into(), &nums, DynProg);

        assert_eq!(exps.len(), record.len() - 1, r"{:?}\n[{}]: {:?}", record,
            Paint::cyan(&record[0]), Paint::green(exps));
    }*/ assert!(cnt == (1362, 3017), r"records: {}, solutions: {}",
            Paint::red(cnt.0), Paint::red(cnt.1));
}
