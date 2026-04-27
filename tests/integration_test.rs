use glucose_rs::solver::Solver;
use glucose_rs::types::{LBool, Lit};

fn make_lit(var: u32, neg: bool) -> Lit {
    Lit::new(var, neg)
}

#[test]
fn test_simple_sat() {
    // (x1 OR x2) AND (NOT x1 OR x2) — satisfied by x2=true
    let mut solver = Solver::new();
    let x1 = solver.new_var();
    let x2 = solver.new_var();

    solver.add_clause(&[make_lit(x1, false), make_lit(x2, false)]);
    solver.add_clause(&[make_lit(x1, true), make_lit(x2, false)]);

    assert_eq!(solver.solve(), LBool::True);
    // x2 must be true
    assert_eq!(solver.model[x2 as usize], LBool::True);
}

#[test]
fn test_simple_unsat() {
    // (x1) AND (NOT x1)
    let mut solver = Solver::new();
    let x1 = solver.new_var();

    solver.add_clause(&[make_lit(x1, false)]);
    solver.add_clause(&[make_lit(x1, true)]);

    assert_eq!(solver.solve(), LBool::False);
}

#[test]
fn test_empty_clause_set() {
    // No clauses → trivially SAT
    let mut solver = Solver::new();
    solver.new_var();
    solver.new_var();

    assert_eq!(solver.solve(), LBool::True);
}

#[test]
fn test_3sat_solvable() {
    // (x1 OR x2 OR x3) AND (NOT x1 OR x2 OR x3) AND (x1 OR NOT x2 OR x3)
    // AND (x1 OR x2 OR NOT x3)
    let mut solver = Solver::new();
    let x1 = solver.new_var();
    let x2 = solver.new_var();
    let x3 = solver.new_var();

    solver.add_clause(&[
        make_lit(x1, false),
        make_lit(x2, false),
        make_lit(x3, false),
    ]);
    solver.add_clause(&[
        make_lit(x1, true),
        make_lit(x2, false),
        make_lit(x3, false),
    ]);
    solver.add_clause(&[
        make_lit(x1, false),
        make_lit(x2, true),
        make_lit(x3, false),
    ]);
    solver.add_clause(&[
        make_lit(x1, false),
        make_lit(x2, false),
        make_lit(x3, true),
    ]);

    assert_eq!(solver.solve(), LBool::True);
}

#[test]
fn test_php32_unsat() {
    // Pigeonhole principle PHP(3,2):
    // 3 pigeons, 2 holes — UNSAT
    // Variables: p[i][j] = pigeon i in hole j, i in 0..3, j in 0..2
    // => 6 variables total
    //
    // At least one hole per pigeon:
    //   (p00 OR p01) for pigeon 0
    //   (p10 OR p11) for pigeon 1
    //   (p20 OR p21) for pigeon 2
    //
    // At most one pigeon per hole:
    //   (NOT p00 OR NOT p10), (NOT p00 OR NOT p20), (NOT p10 OR NOT p20)  -- hole 0
    //   (NOT p01 OR NOT p11), (NOT p01 OR NOT p21), (NOT p11 OR NOT p21)  -- hole 1

    let mut solver = Solver::new();
    // p[i][j] = var index i*2 + j
    let mut vars = [[0u32; 2]; 3];
    for i in 0..3 {
        for j in 0..2 {
            vars[i][j] = solver.new_var();
        }
    }

    // At least one hole per pigeon
    for i in 0..3 {
        solver.add_clause(&[make_lit(vars[i][0], false), make_lit(vars[i][1], false)]);
    }

    // At most one pigeon per hole
    for j in 0..2 {
        for i1 in 0..3 {
            for i2 in (i1 + 1)..3 {
                solver.add_clause(&[
                    make_lit(vars[i1][j], true),
                    make_lit(vars[i2][j], true),
                ]);
            }
        }
    }

    assert_eq!(solver.solve(), LBool::False);
}

#[test]
fn test_unit_propagation_sat() {
    // Force x1=true via unit clause, then check
    let mut solver = Solver::new();
    let x1 = solver.new_var();
    let x2 = solver.new_var();
    // x1 is forced true
    solver.add_clause(&[make_lit(x1, false)]);
    // (NOT x1 OR x2) => x2 must be true
    solver.add_clause(&[make_lit(x1, true), make_lit(x2, false)]);

    assert_eq!(solver.solve(), LBool::True);
    assert_eq!(solver.model[x1 as usize], LBool::True);
    assert_eq!(solver.model[x2 as usize], LBool::True);
}
