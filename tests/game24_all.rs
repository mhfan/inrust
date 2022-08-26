
//mod common;   // subdirectory module

#[test] fn largest() {
    let array = [1, 2, 3];
    assert_eq!(inrust::largest(&array), &array[2]);
    // Integration tests (and benchmarks) 'depend' to the crate
    // like a 3rd party would. Hence, they only see public items.
}

#[test] fn game24_all() {   // TODO: try use tokio and scraper to extract url and parse html
    use {inrust::calc24::*, yansi::Paint};
    let game24_all = "tests/game24_all.txt"; // https://4shu.net/solutions/allsolutions/
    //let _ = std::fs::read_to_string(game24_all).unwrap();     // XXX: parse game24_all.fmh

    let mut rdr = csv::ReaderBuilder::new()
        .has_headers(false).delimiter(b'\t').flexible(true)
        .trim(csv::Trim::All).from_path(game24_all).unwrap();

    let mut cnt = (0, 0);
    for result in rdr.records() {
        let record = result.unwrap();
        let mut nums = record[0].split(' ').map(|s| Rc::new(Rational::from(s.parse::<i32>().unwrap()).into())).collect::<Vec<_>>();
        let exps = calc24_algo(&24.into(), &mut nums, DynProg(false));

        cnt.0 += 1;
        cnt.1 += record.len() - 1;
        if exps.len() != record.len() - 1 {
            eprint!("[{}]:", Paint::cyan(&record[0]));
            record.iter().skip(1).for_each(|s| eprint!(" {}", Paint::magenta(s)));

            eprint!("\n[{}]:", Paint::cyan(&record[0]));
            exps.iter().for_each(|e| eprint!(" {}", Paint::green(e))); eprintln!();
        }

        assert_eq!(exps.len(), record.len() - 1, "{}", &record[0]);
    }   assert!(cnt == (1362, 3017), "records: {}, solutions: {}",
            Paint::red(cnt.0), Paint::red(cnt.1));
}
