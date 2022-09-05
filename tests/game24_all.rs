
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
            .last().unwrap().split(' ').for_each(|res| if !res.is_empty() {
                assert_eq!((mexe::eval(res).unwrap() + 0.5) as u32, 24, "failed at: `{res}'");
            })  // split_ascii_whitespace
        );

    // TODO: try use tokio and scraper to extract url and parse html?
    let mut rdr = csv::ReaderBuilder::new()
        .has_headers(false).delimiter(b'\t').flexible(true)
        .trim(csv::Trim::All).from_path("tests/game24_all.txt").unwrap();
        // https://4shu.net/solutions/allsolutions/

    let mut cnt = (0, 0);
    for result in rdr.records() {
        let record = result.unwrap();
        cnt.0 += 1usize;    cnt.1 += record.len() - 1;

        let nums = record[0].split(' ').map(|s|
            s.parse::<i32>().unwrap().into()).collect::<Vec<_>>();
        let exps = calc24_coll(&24.into(), &nums, DynProg);

        if  exps.len() != record.len() - 1 {
            eprint!(r"[{}]:", Paint::cyan(&record[0]));
            record.iter().skip(1).for_each(|s| eprint!(r" {}", Paint::magenta(s)));

            eprint!(r"\n[{}]:", Paint::cyan(&record[0]));
            exps.iter().for_each(|e| eprint!(r" {}", Paint::green(e))); eprintln!();
        }

        assert_eq!(exps.len(), record.len() - 1, r"{}", &record[0]);
    }   assert!(cnt == (1362, 3017), r"records: {}, solutions: {}",
            Paint::red(cnt.0), Paint::red(cnt.1));
}
