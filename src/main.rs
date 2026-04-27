use std::env;
use std::fs;

use glucose_rs::io::dimacs::DimacsParser;
use glucose_rs::solver::Solver;
use glucose_rs::types::{LBool, Lit};

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("Usage: glucose_rs <input.cnf>");
        std::process::exit(1);
    }

    let content = fs::read_to_string(&args[1]).expect("Failed to read file");
    let parsed = DimacsParser::parse(&content).expect("Failed to parse DIMACS");

    let mut solver = Solver::new();

    for _ in 0..parsed.num_vars {
        solver.new_var();
    }

    for clause in &parsed.clauses {
        let lits: Vec<Lit> = clause
            .iter()
            .map(|&x| {
                let var = (x.unsigned_abs() - 1) as u32;
                Lit::new(var, x < 0)
            })
            .collect();
        if !solver.add_clause(&lits) {
            println!("s UNSATISFIABLE");
            std::process::exit(20);
        }
    }

    match solver.solve() {
        LBool::True => {
            println!("s SATISFIABLE");
            let model: Vec<i32> = (0..parsed.num_vars)
                .map(|v| match solver.model[v] {
                    LBool::True => (v + 1) as i32,
                    _ => -((v + 1) as i32),
                })
                .collect();
            let model_str: Vec<String> = model.iter().map(|x| x.to_string()).collect();
            println!("v {} 0", model_str.join(" "));
            std::process::exit(10);
        }
        LBool::False => {
            println!("s UNSATISFIABLE");
            std::process::exit(20);
        }
        LBool::Undef => {
            println!("s UNKNOWN");
            std::process::exit(0);
        }
    }
}
