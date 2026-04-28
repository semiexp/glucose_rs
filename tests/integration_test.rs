use glucose_rs::solver::Solver;
use glucose_rs::types::{LBool, Lit};
use glucose_rs::constraints::{
    AtMost, Xor, OrderEncodingLinear, DirectEncodingExtensionSupports,
    ActiveVerticesConnected,
};
use glucose_rs::constraints::order_encoding_linear::LinearTerm;

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

// ──────────────────────────────────────────────────────────────────────────────
// AtMost constraint tests
// ──────────────────────────────────────────────────────────────────────────────

#[test]
fn test_at_most_sat() {
    // AtMost([x0, x1, x2], 1): at most 1 of the 3 can be TRUE.
    // With clause (x0 OR x1) forcing at least one, the solver should find x0 XOR x1.
    let mut solver = Solver::new();
    let x0 = solver.new_var();
    let x1 = solver.new_var();
    let x2 = solver.new_var();

    let c = AtMost::new(
        vec![make_lit(x0, false), make_lit(x1, false), make_lit(x2, false)],
        1,
    );
    assert!(solver.add_constraint(Box::new(c)));
    // Force at least one of x0, x1 to be true
    solver.add_clause(&[make_lit(x0, false), make_lit(x1, false)]);

    assert_eq!(solver.solve(), LBool::True);

    // At most 1 of the three must be true in the model
    let n_true = [x0, x1, x2]
        .iter()
        .filter(|&&v| solver.model[v as usize] == LBool::True)
        .count();
    assert!(n_true <= 1);
    // At least one of x0, x1 must be true
    assert!(
        solver.model[x0 as usize] == LBool::True
            || solver.model[x1 as usize] == LBool::True
    );
}

#[test]
fn test_at_most_unsat() {
    // AtMost([x0, x1], 1) AND (x0) AND (x1) → UNSAT
    let mut solver = Solver::new();
    let x0 = solver.new_var();
    let x1 = solver.new_var();

    let c = AtMost::new(vec![make_lit(x0, false), make_lit(x1, false)], 1);
    assert!(solver.add_constraint(Box::new(c)));
    solver.add_clause(&[make_lit(x0, false)]);
    solver.add_clause(&[make_lit(x1, false)]);

    assert_eq!(solver.solve(), LBool::False);
}

// ──────────────────────────────────────────────────────────────────────────────
// Xor constraint tests
// ──────────────────────────────────────────────────────────────────────────────

#[test]
fn test_xor_sat() {
    // XOR([x0, x1, x2], parity=1): x0 XOR x1 XOR x2 == 1
    // With x0=true forced, x1 XOR x2 must be 0 (both same).
    let mut solver = Solver::new();
    let x0 = solver.new_var();
    let x1 = solver.new_var();
    let x2 = solver.new_var();

    let c = Xor::new(
        &[make_lit(x0, false), make_lit(x1, false), make_lit(x2, false)],
        1,
    );
    assert!(solver.add_constraint(Box::new(c)));
    solver.add_clause(&[make_lit(x0, false)]); // x0 = true

    assert_eq!(solver.solve(), LBool::True);

    let v0 = solver.model[x0 as usize] == LBool::True;
    let v1 = solver.model[x1 as usize] == LBool::True;
    let v2 = solver.model[x2 as usize] == LBool::True;
    let parity = (v0 as u8) ^ (v1 as u8) ^ (v2 as u8);
    assert_eq!(parity, 1);
}

#[test]
fn test_xor_unsat() {
    // XOR([x0, x1], parity=1) AND x0=false AND x1=false => 0 XOR 0 = 0 ≠ 1 → UNSAT
    let mut solver = Solver::new();
    let x0 = solver.new_var();
    let x1 = solver.new_var();

    let c = Xor::new(&[make_lit(x0, false), make_lit(x1, false)], 1);
    assert!(solver.add_constraint(Box::new(c)));
    solver.add_clause(&[make_lit(x0, true)]); // x0 = false
    solver.add_clause(&[make_lit(x1, true)]); // x1 = false

    assert_eq!(solver.solve(), LBool::False);
}

// ──────────────────────────────────────────────────────────────────────────────
// OrderEncodingLinear constraint tests
// ──────────────────────────────────────────────────────────────────────────────

#[test]
fn test_order_encoding_linear_sat() {
    // Variable x with domain {0, 1, 2, 3}, encoded with 3 lits:
    //   l0 <=> x >= 1
    //   l1 <=> x >= 2
    //   l2 <=> x >= 3
    // Constraint: x >= 2, expressed as "x + (-2) >= 0" (constant=-2, coef=1)
    // We expect the solver to force l1 (x >= 2) to be true.
    let mut solver = Solver::new();
    let l0 = solver.new_var();
    let l1 = solver.new_var();
    let l2 = solver.new_var();

    // lits[i] <=> (x >= domain[i+1])
    let term = LinearTerm {
        lits: vec![make_lit(l0, false), make_lit(l1, false), make_lit(l2, false)],
        domain: vec![0, 1, 2, 3],
        coef: 1,
    };
    // sum(terms) + constant >= 0  i.e.  x - 2 >= 0
    let c = OrderEncodingLinear::new(vec![term], -2);
    assert!(solver.add_constraint(Box::new(c)));

    assert_eq!(solver.solve(), LBool::True);

    // In a valid model l1 (x>=2) must be true
    assert_eq!(solver.model[l1 as usize], LBool::True);
}

#[test]
fn test_order_encoding_linear_unsat() {
    // x in {0, 1}, l0 <=> x >= 1.
    // Constraint: x >= 2  i.e. x - 2 >= 0 — impossible since max(x)=1.
    let mut solver = Solver::new();
    let l0 = solver.new_var();

    let term = LinearTerm {
        lits: vec![make_lit(l0, false)],
        domain: vec![0, 1],
        coef: 1,
    };
    let c = OrderEncodingLinear::new(vec![term], -2);
    assert!(!solver.add_constraint(Box::new(c)));
}

// ──────────────────────────────────────────────────────────────────────────────
// DirectEncodingExtensionSupports tests
// ──────────────────────────────────────────────────────────────────────────────

#[test]
fn test_direct_encoding_extension_sat() {
    // Two variables each taking values in {0, 1}.
    //   var0_lits[0] = x0  (x0 TRUE <=> var0 = 0)
    //   var0_lits[1] = x1  (x1 TRUE <=> var0 = 1)
    //   var1_lits[0] = x2  (x2 TRUE <=> var1 = 0)
    //   var1_lits[1] = x3  (x3 TRUE <=> var1 = 1)
    // Supports: {(0,0), (1,1)} — only equal assignments allowed.
    let mut solver = Solver::new();
    let x0 = solver.new_var();
    let x1 = solver.new_var();
    let x2 = solver.new_var();
    let x3 = solver.new_var();

    // Encode "exactly one of x0, x1" and "exactly one of x2, x3"
    solver.add_clause(&[make_lit(x0, false), make_lit(x1, false)]);
    solver.add_clause(&[make_lit(x0, true), make_lit(x1, true)]);
    solver.add_clause(&[make_lit(x2, false), make_lit(x3, false)]);
    solver.add_clause(&[make_lit(x2, true), make_lit(x3, true)]);

    let vars = vec![
        vec![make_lit(x0, false), make_lit(x1, false)],
        vec![make_lit(x2, false), make_lit(x3, false)],
    ];
    let supports = vec![
        vec![0i32, 0], // (var0=0, var1=0)
        vec![1, 1],    // (var0=1, var1=1)
    ];
    let c = DirectEncodingExtensionSupports::new(vars, supports);
    assert!(solver.add_constraint(Box::new(c)));

    assert_eq!(solver.solve(), LBool::True);

    // Model must have var0 == var1 (both 0 or both 1)
    let var0_val = if solver.model[x0 as usize] == LBool::True { 0 } else { 1 };
    let var1_val = if solver.model[x2 as usize] == LBool::True { 0 } else { 1 };
    assert_eq!(var0_val, var1_val);
}

#[test]
fn test_direct_encoding_extension_unsat() {
    // Force var0=0 (x0=true) and var1=1 (x3=true), but support only {(0,0), (1,1)}.
    // Add the constraint first, then force the incompatible assignments.
    let mut solver = Solver::new();
    let x0 = solver.new_var();
    let x1 = solver.new_var();
    let x2 = solver.new_var();
    let x3 = solver.new_var();

    // Exactly one of each pair
    solver.add_clause(&[make_lit(x0, false), make_lit(x1, false)]);
    solver.add_clause(&[make_lit(x0, true), make_lit(x1, true)]);
    solver.add_clause(&[make_lit(x2, false), make_lit(x3, false)]);
    solver.add_clause(&[make_lit(x2, true), make_lit(x3, true)]);

    let vars = vec![
        vec![make_lit(x0, false), make_lit(x1, false)],
        vec![make_lit(x2, false), make_lit(x3, false)],
    ];
    let supports = vec![vec![0i32, 0], vec![1, 1]];
    let c = DirectEncodingExtensionSupports::new(vars, supports);
    // Add constraint before forcing incompatible assignments
    assert!(solver.add_constraint(Box::new(c)));

    // Force var0=0 and var1=1 (incompatible with supports)
    solver.add_clause(&[make_lit(x0, false)]); // x0=true => var0=0
    solver.add_clause(&[make_lit(x3, false)]); // x3=true => var1=1

    assert_eq!(solver.solve(), LBool::False);
}

// ──────────────────────────────────────────────────────────────────────────────
// ActiveVerticesConnected (Graph) constraint tests
// ──────────────────────────────────────────────────────────────────────────────

#[test]
fn test_active_vertices_connected_sat() {
    // Graph: 4 vertices in a path: 0-1-2-3
    // lits[i] = TRUE iff vertex i is active.
    // Force vertices 0 and 2 to be active; the constraint should force vertex 1 to be active too.
    let mut solver = Solver::new();
    let v0 = solver.new_var();
    let v1 = solver.new_var();
    let v2 = solver.new_var();
    let v3 = solver.new_var();

    let lits = vec![
        make_lit(v0, false),
        make_lit(v1, false),
        make_lit(v2, false),
        make_lit(v3, false),
    ];
    let edges = vec![(0, 1), (1, 2), (2, 3)];
    let c = ActiveVerticesConnected::new(lits, &edges);
    assert!(solver.add_constraint(Box::new(c)));

    // Force v0 and v2 active
    solver.add_clause(&[make_lit(v0, false)]);
    solver.add_clause(&[make_lit(v2, false)]);

    assert_eq!(solver.solve(), LBool::True);

    // v1 must be active (it's the only path between v0 and v2)
    assert_eq!(solver.model[v1 as usize], LBool::True);
}

#[test]
fn test_active_vertices_connected_unsat() {
    // Graph: 4 vertices, edges 0-1 and 2-3 (two disconnected components).
    // Force v0 and v3 active → they can't be connected → UNSAT.
    let mut solver = Solver::new();
    let v0 = solver.new_var();
    let v1 = solver.new_var();
    let v2 = solver.new_var();
    let v3 = solver.new_var();

    let lits = vec![
        make_lit(v0, false),
        make_lit(v1, false),
        make_lit(v2, false),
        make_lit(v3, false),
    ];
    let edges = vec![(0, 1), (2, 3)]; // disconnected graph
    let c = ActiveVerticesConnected::new(lits, &edges);
    assert!(solver.add_constraint(Box::new(c)));

    // Force v0 and v3 active
    solver.add_clause(&[make_lit(v0, false)]);
    solver.add_clause(&[make_lit(v3, false)]);
    // Force v1 and v2 inactive (close off both possible bridges)
    solver.add_clause(&[make_lit(v1, true)]);
    solver.add_clause(&[make_lit(v2, true)]);

    assert_eq!(solver.solve(), LBool::False);
}
