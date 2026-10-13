// Thin verification driver for existing polytool APIs; generates no rows.
use std::io::{self, BufRead};

fn main() {
    for (n, line) in io::stdin().lock().lines().enumerate() {
        let line = line.expect("input");
        let coefficients: Vec<_> = line.split(',')
            .map(|entry| entry.trim().parse().expect("integer coefficient"))
            .collect();
        let degree = coefficients.len() - 1;
        let distinct = polytool::count_real_roots_prs_bigint_coeffs(&coefficients);
        assert_eq!(distinct, degree, "B_{n}: distinct real-root count");
        println!("{{\"n\":{n},\"degree\":{degree},\"distinct_real_roots\":{distinct}}}");
    }
}
