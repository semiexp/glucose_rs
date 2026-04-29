use glucose_rs::solver::Solver;
use glucose_rs::types::{LBool, Lit};
use glucose_rs::constraints::{
    AtMost, Xor, OrderEncodingLinear, DirectEncodingExtensionSupports,
    ActiveVerticesConnected, GraphDivision,
};
use glucose_rs::constraints::order_encoding_linear::LinearTerm;
use glucose_rs::constraints::graph_division::OptionalOrderEncoding;

// ── Core helpers ──────────────────────────────────────────────────────────────

fn stress_test_rounds() -> usize {
    std::env::var("GLUCOSE_RS_STRESS_ROUNDS")
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .filter(|&n| n > 0)
        .unwrap_or(5)
}

fn lcg_next(state: &mut u64) -> u64 {
    *state = state
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    *state
}

fn lcg_range(state: &mut u64, upper: usize) -> usize {
    let mut x = lcg_next(state);
    let upper = upper as u64;
    let t = u64::MAX / upper;
    let threshold = t * upper;
    loop {
        if x < threshold {
            return (x / t) as usize;
        }
        x = lcg_next(state);
    }
}

const SAT_STRESS_FREE_VARS: usize = 4;

/// Enumerate all solutions over `vars` by iteratively blocking each found solution.
fn count_num_assignments(solver: &mut Solver, vars: &[u32]) -> usize {
    let mut count = 0;
    loop {
        if solver.solve() != LBool::True {
            break;
        }
        count += 1;
        // Blocking clause: for each var, add the literal that negates its current value.
        // If model[v]=True  → push Lit(v, neg=true)  so the clause says "v must be false".
        // If model[v]=False → push Lit(v, neg=false) so the clause says "v must be true".
        let deny: Vec<Lit> = vars
            .iter()
            .map(|&v| Lit::new(v, solver.model[v as usize] == LBool::True))
            .collect();
        solver.add_clause(&deny);
    }
    count
}

/// Create order-encoding literals for an integer variable with the given sorted domain.
/// Adds monotonicity constraints: lits[i] => lits[i-1].
/// Returns the lits vec (length domain.len()-1).
fn make_order_encoding_vars(
    solver: &mut Solver,
    domain: &[i32],
    all_vars: &mut Vec<u32>,
) -> Vec<Lit> {
    let mut lits = Vec::new();
    for _ in 0..domain.len() - 1 {
        let v = solver.new_var();
        all_vars.push(v);
        lits.push(Lit::new(v, false));
    }
    // Monotonicity: lits[i] => lits[i-1]  i.e.  ~lits[i] OR lits[i-1]
    for i in 1..lits.len() {
        solver.add_clause(&[!lits[i], lits[i - 1]]);
    }
    lits
}

/// Create direct-encoding literals for an integer variable with domain size `dom_size`.
/// Adds exactly-one constraints (at-least-one and at-most-one pairwise).
fn make_direct_encoding_vars(
    solver: &mut Solver,
    dom_size: usize,
    all_vars: &mut Vec<u32>,
) -> Vec<Lit> {
    let mut lits = Vec::new();
    for _ in 0..dom_size {
        let v = solver.new_var();
        all_vars.push(v);
        lits.push(Lit::new(v, false));
    }
    // At-least-one
    solver.add_clause(&lits);
    // At-most-one (pairwise)
    for i in 0..lits.len() {
        for j in i + 1..lits.len() {
            solver.add_clause(&[!lits[i], !lits[j]]);
        }
    }
    lits
}

// ── Clause-only large tests ───────────────────────────────────────────────────

/// Count how many of 2^n_vars boolean assignments satisfy all 3-clauses.
/// Each clause is [(var, is_negated); 3]; a clause is satisfied when at least one
/// literal evaluates to true (val != is_negated).
fn brute_force_count(n_vars: usize, clauses: &[[(usize, bool); 3]]) -> usize {
    (0u32..1u32 << n_vars)
        .filter(|&bits| {
            clauses.iter().all(|clause| {
                clause.iter().any(|&(v, neg)| {
                    let val = (bits >> v) & 1 == 1;
                    val != neg
                })
            })
        })
        .count()
}

/// Build a deterministic set of 3-clauses using a PCG-inspired LCG.
fn make_3sat_clauses(n_vars: usize, n_clauses: usize, seed: u64) -> Vec<[(usize, bool); 3]> {
    let mut state = seed;
    let mut next = || -> u64 {
        state = state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        state
    };
    (0..n_clauses)
        .map(|_| {
            let v0 = (next() % n_vars as u64) as usize;
            let v1 = (next() % n_vars as u64) as usize;
            let v2 = (next() % n_vars as u64) as usize;
            let n0 = next() % 2 == 0;
            let n1 = next() % 2 == 0;
            let n2 = next() % 2 == 0;
            [(v0, n0), (v1, n1), (v2, n2)]
        })
        .collect()
}

/// Compare SAT solver solution count vs brute force over 18 variables with 36 random 3-clauses.
#[test]
fn test_brute_force_compare_18vars() {
    let n_vars = 18;
    let clauses = make_3sat_clauses(n_vars, 36, 42);

    let expected = brute_force_count(n_vars, &clauses);

    let mut solver = Solver::new();
    let vars: Vec<u32> = (0..n_vars).map(|_| solver.new_var()).collect();
    for &[(v0, n0), (v1, n1), (v2, n2)] in &clauses {
        solver.add_clause(&[
            Lit::new(vars[v0], n0),
            Lit::new(vars[v1], n1),
            Lit::new(vars[v2], n2),
        ]);
    }
    let actual = count_num_assignments(&mut solver, &vars);

    assert_eq!(expected, actual);
}

/// 200-variable satisfiable instance: each 3-clause guarantees at least one TRUE
/// literal under the known assignment (var i is TRUE iff i is even).
#[test]
fn test_large_sat_known_assignment() {
    let n = 200usize;
    let mut solver = Solver::new();
    let vars: Vec<u32> = (0..n).map(|_| solver.new_var()).collect();

    // For each clause, the first literal evaluates to TRUE under the known assignment.
    // assignment[i] = (i % 2 == 0): even vars are TRUE.
    // To get a TRUE literal for var v:
    //   v even (assignment=true)  → positive lit (neg=false)
    //   v odd  (assignment=false) → negative lit (neg=true)
    // In both cases: neg = (v % 2 == 1).
    for c in 0..300usize {
        let v0 = c % n;
        let v1 = (c + 57) % n;
        let v2 = (c + 113) % n;
        let l0 = Lit::new(vars[v0], v0 % 2 == 1); // guaranteed TRUE
        let l1 = Lit::new(vars[v1], false);
        let l2 = Lit::new(vars[v2], false);
        solver.add_clause(&[l0, l1, l2]);
    }

    assert_eq!(solver.solve(), LBool::True);
}

/// PHP(n, n): n pigeons into n holes — SAT (bijection exists).
#[test]
fn test_large_sat_pigeonhole_bijection() {
    let n = 8usize;
    let mut solver = Solver::new();
    let mut p = vec![[0u32; 8]; 8]; // p[i][j] = pigeon i in hole j
    for i in 0..n {
        for j in 0..n {
            p[i][j] = solver.new_var();
        }
    }
    // Each pigeon in at least one hole
    for i in 0..n {
        let clause: Vec<Lit> = (0..n).map(|j| Lit::new(p[i][j], false)).collect();
        solver.add_clause(&clause);
    }
    // Each hole has at most one pigeon
    for j in 0..n {
        for i1 in 0..n {
            for i2 in i1 + 1..n {
                solver.add_clause(&[Lit::new(p[i1][j], true), Lit::new(p[i2][j], true)]);
            }
        }
    }
    // Each pigeon in at most one hole
    for i in 0..n {
        for j1 in 0..n {
            for j2 in j1 + 1..n {
                solver.add_clause(&[Lit::new(p[i][j1], true), Lit::new(p[i][j2], true)]);
            }
        }
    }
    assert_eq!(solver.solve(), LBool::True);
}

/// PHP(n+1, n): n+1 pigeons into n holes — UNSAT (classic pigeonhole).
#[test]
fn test_large_unsat_pigeonhole() {
    let n = 8usize; // 9 pigeons, 8 holes
    let pigeons = n + 1;
    let holes = n;
    let mut solver = Solver::new();
    let mut p: Vec<Vec<u32>> = (0..pigeons)
        .map(|_| (0..holes).map(|_| solver.new_var()).collect())
        .collect();
    // Each pigeon in at least one hole
    for i in 0..pigeons {
        let clause: Vec<Lit> = (0..holes).map(|j| Lit::new(p[i][j], false)).collect();
        solver.add_clause(&clause);
    }
    // At most one pigeon per hole
    for j in 0..holes {
        for i1 in 0..pigeons {
            for i2 in i1 + 1..pigeons {
                solver.add_clause(&[Lit::new(p[i1][j], true), Lit::new(p[i2][j], true)]);
            }
        }
    }
    assert_eq!(solver.solve(), LBool::False);
}

// ── AtMost constraint tests ───────────────────────────────────────────────────

fn atmost_test_count(n: usize, k: i32) -> usize {
    let mut solver = Solver::new();
    let vars: Vec<u32> = (0..n).map(|_| solver.new_var()).collect();
    let lits: Vec<Lit> = vars.iter().map(|&v| Lit::new(v, false)).collect();
    solver.add_constraint(Box::new(AtMost::new(lits, k)));
    count_num_assignments(&mut solver, &vars)
}

/// For n variables with AtMost(k), the solution count equals sum_{i=0}^{k} C(n, i).
#[test]
fn test_atmost_count() {
    const MAXN: usize = 10;
    // Build Pascal's triangle
    let mut binom = [[0u64; MAXN + 1]; MAXN + 1];
    binom[0][0] = 1;
    for i in 1..=MAXN {
        binom[i][0] = 1;
        for j in 1..=i {
            binom[i][j] = binom[i - 1][j - 1] + binom[i - 1][j];
        }
    }
    for n in 1..=MAXN {
        let mut cumsum = 0u64;
        for k in 0..=n {
            cumsum += binom[n][k];
            let count = atmost_test_count(n, k as i32) as u64;
            assert_eq!(
                count, cumsum,
                "AtMost({n}, {k}): expected {cumsum}, got {count}"
            );
        }
    }
}

/// After adding AtMost(lits, k), already-true literals propagate to force the rest false.
#[test]
fn test_atmost_propagation_on_init() {
    let mut solver = Solver::new();
    for k in 0..=1i32 {
        let vars: Vec<u32> = (0..10).map(|_| solver.new_var()).collect();
        let lits: Vec<Lit> = vars.iter().map(|&v| Lit::new(v, false)).collect();
        if k == 1 {
            // Force vars[1] true before adding constraint
            solver.add_clause(&[Lit::new(vars[1], false)]);
        }
        solver.add_constraint(Box::new(AtMost::new(lits, k)));
        assert_eq!(
            solver.value_of_var(vars[0]),
            LBool::False,
            "k={k}: vars[0] should be propagated to false"
        );
        assert_eq!(
            solver.value_of_var(vars[9]),
            LBool::False,
            "k={k}: vars[9] should be propagated to false"
        );
    }
}

/// Count satisfying assignments for multiple AtMost constraints, compared to brute force.
fn count_num_atmost_patterns(n: usize, groups: &[Vec<i32>], thresholds: &[i32]) -> usize {
    // For each bit-assignment over n vars, check that each group satisfies its threshold.
    (0u32..1u32 << n)
        .filter(|&bits| {
            groups.iter().zip(thresholds.iter()).all(|(group, &thresh)| {
                let count: i32 = group
                    .iter()
                    .map(|&v| {
                        if v >= 0 {
                            ((bits >> (v as u32)) & 1) as i32
                        } else {
                            // Negative v represents a negated literal (C++ ~k convention).
                            // (!v) gives the variable index; count is 1 when var is FALSE.
                            1 - ((bits >> ((!v) as u32)) & 1) as i32
                        }
                    })
                    .sum();
                count <= thresh
            })
        })
        .count()
}

fn atmost_test_pattern(n: usize, groups: &[Vec<i32>], thresholds: &[i32]) {
    let expected = count_num_atmost_patterns(n, groups, thresholds);

    let mut solver = Solver::new();
    let vars: Vec<u32> = (0..n).map(|_| solver.new_var()).collect();
    for (group, &thresh) in groups.iter().zip(thresholds.iter()) {
        let lits: Vec<Lit> = group
            .iter()
            .map(|&v| {
                if v >= 0 {
                    Lit::new(vars[v as usize], false)
                } else {
                    // C++ ~k convention: !v gives var index, literal is negated.
                    Lit::new(vars[(!v) as usize], true)
                }
            })
            .collect();
        solver.add_constraint(Box::new(AtMost::new(lits, thresh)));
    }
    let actual = count_num_assignments(&mut solver, &vars);
    assert_eq!(expected, actual, "atmost_pattern n={n} groups={groups:?} thresholds={thresholds:?}");
}

/// Multiple AtMost constraints with positive and negated literals.
#[test]
fn test_atmost_complex() {
    // In C++: ~3 = -4, ~2 = -3 (bitwise NOT).
    atmost_test_pattern(
        10,
        &[
            vec![0, 1, 2, 3, 4],
            vec![2, -4, 4, 5, 6, 7], // -4 represents C++ ~3 (var 3 negated)
            vec![-3, 7, 8, 9],       // -3 represents C++ ~2 (var 2 negated)
        ],
        &[3, 3, 2],
    );
}

// ── Xor constraint tests ──────────────────────────────────────────────────────

fn xor_test_dimension(constraints: &[Vec<usize>], parities: &[i32], n: usize) -> usize {
    let mut solver = Solver::new();
    let vars: Vec<u32> = (0..n).map(|_| solver.new_var()).collect();
    for (con, &parity) in constraints.iter().zip(parities.iter()) {
        let lits: Vec<Lit> = con.iter().map(|&v| Lit::new(vars[v], false)).collect();
        solver.add_constraint(Box::new(Xor::new(&lits, parity)));
    }
    count_num_assignments(&mut solver, &vars)
}

/// XOR system over n vars: solution count = 2^(n - rank) or 0 if inconsistent.
#[test]
fn test_xor_dimension() {
    // One constraint, rank 1: 2^(3-1) = 4
    assert_eq!(xor_test_dimension(&[vec![0, 1]], &[0], 3), 4);
    // Two independent constraints, rank 2: 2^(3-2) = 2
    assert_eq!(xor_test_dimension(&[vec![0, 1], vec![1, 2]], &[0, 1], 3), 2);
    // Two constraints, rank 2 over 6 vars: 2^(6-2) = 16
    assert_eq!(
        xor_test_dimension(&[vec![0, 1, 3, 5], vec![1, 3, 5]], &[1, 1], 6),
        16
    );
    // Three constraints, effective rank 2 over 10 vars: 2^(10-2) = 256
    assert_eq!(
        xor_test_dimension(
            &[vec![0, 1, 3, 5, 8], vec![2, 3], vec![0, 1, 2, 5, 8]],
            &[1, 0, 1],
            10
        ),
        256
    );
    // Inconsistent system: 0 solutions
    assert_eq!(
        xor_test_dimension(
            &[vec![0, 1, 3, 5, 8], vec![2, 3], vec![0, 1, 2, 5, 8]],
            &[0, 0, 1],
            10
        ),
        0
    );
}

// ── OrderEncodingLinear constraint tests ──────────────────────────────────────

fn count_num_ip_assignments(domains: &[Vec<i32>], coefs: &[Vec<i32>]) -> usize {
    fn helper(
        idx: usize,
        domains: &[Vec<i32>],
        coefs: &[Vec<i32>],
        vals: &mut Vec<i32>,
    ) -> usize {
        if idx == domains.len() {
            for coef_row in coefs {
                let constant = *coef_row.last().unwrap();
                let sum: i32 = coef_row[..domains.len()]
                    .iter()
                    .zip(vals.iter())
                    .map(|(&c, &v)| c * v)
                    .sum();
                if sum + constant < 0 {
                    return 0;
                }
            }
            return 1;
        }
        let mut ret = 0;
        for &x in &domains[idx] {
            vals.push(x);
            ret += helper(idx + 1, domains, coefs, vals);
            vals.pop();
        }
        ret
    }
    helper(0, domains, coefs, &mut Vec::new())
}

fn order_encoding_linear_test_ip(domains: &[Vec<i32>], coefs: &[Vec<i32>]) {
    let expected = count_num_ip_assignments(domains, coefs);

    let mut solver = Solver::new();
    let mut all_vars: Vec<u32> = Vec::new();
    let mut all_lits: Vec<Vec<Lit>> = Vec::new();

    for domain in domains {
        let lits = make_order_encoding_vars(&mut solver, domain, &mut all_vars);
        all_lits.push(lits);
    }

    for coef_row in coefs {
        assert_eq!(coef_row.len(), domains.len() + 1);
        let constant = *coef_row.last().unwrap();
        let terms: Vec<LinearTerm> = (0..domains.len())
            .filter(|&j| coef_row[j] != 0)
            .map(|j| LinearTerm {
                lits: all_lits[j].clone(),
                domain: domains[j].clone(),
                coef: coef_row[j],
            })
            .collect();
        solver.add_constraint(Box::new(OrderEncodingLinear::new(terms, constant)));
    }

    let actual = count_num_assignments(&mut solver, &all_vars);
    assert_eq!(expected, actual);
}

fn order_encoding_linear_test_inconsistent(domains: &[Vec<i32>], coef_row: &[i32]) {
    let mut solver = Solver::new();
    let mut all_vars: Vec<u32> = Vec::new();
    let mut all_lits: Vec<Vec<Lit>> = Vec::new();

    for domain in domains {
        let lits = make_order_encoding_vars(&mut solver, domain, &mut all_vars);
        all_lits.push(lits);
    }

    assert_eq!(coef_row.len(), domains.len() + 1);
    let constant = *coef_row.last().unwrap();
    let terms: Vec<LinearTerm> = (0..domains.len())
        .filter(|&j| coef_row[j] != 0)
        .map(|j| LinearTerm {
            lits: all_lits[j].clone(),
            domain: domains[j].clone(),
            coef: coef_row[j],
        })
        .collect();
    assert!(
        !solver.add_constraint(Box::new(OrderEncodingLinear::new(terms, constant))),
        "Expected add_constraint to return false for inconsistent constraint"
    );
}

/// Count valid integer assignments under linear constraints vs brute force.
#[test]
fn test_order_encoding_linear_count() {
    // x + 2y >= 6, x,y in {1,2,3}
    order_encoding_linear_test_ip(&[vec![1, 2, 3], vec![1, 2, 3]], &[vec![1, 2, -6]]);

    // x + 2y >= 6, x - y >= 0, x,y in {1,2,3}
    order_encoding_linear_test_ip(
        &[vec![1, 2, 3], vec![1, 2, 3]],
        &[vec![1, 2, -6], vec![1, -1, 0]],
    );

    // Four variables, three constraints
    order_encoding_linear_test_ip(
        &[
            vec![1, 2, 3],
            vec![1, 2, 3],
            vec![2, 3, 4, 5],
            vec![3, 4, 5, 6],
        ],
        &[
            vec![1, 2, 0, 0, -6],
            vec![1, 1, 1, 1, -10],
            vec![2, 1, -3, 1, 2],
        ],
    );

    // Larger domains
    order_encoding_linear_test_ip(
        &[
            vec![1, 2, 3, 5, 6, 8],
            vec![1, 2, 4, 8, 15],
            vec![2, 3, 7, 9, 11],
            vec![3, 4, 5, 6, 9],
        ],
        &[
            vec![1, 2, 0, 0, -8],
            vec![1, 1, 1, 1, -15],
            vec![1, 2, -3, 1, -10],
        ],
    );

    // One fixed variable (domain {0}), ten binary variables, sum >= 5
    order_encoding_linear_test_ip(
        &[
            vec![0],
            vec![0, 1],
            vec![0, 1],
            vec![0, 1],
            vec![0, 1],
            vec![0, 1],
            vec![0, 1],
            vec![0, 1],
            vec![0, 1],
            vec![0, 1],
            vec![0, 1],
        ],
        &[vec![0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -5]],
    );
}

/// Constraints that are unsatisfiable from initialization.
#[test]
fn test_order_encoding_linear_unsatisfiable() {
    // x + 2y >= 10, but max(x+2y) = 3 + 6 = 9 < 10
    order_encoding_linear_test_inconsistent(&[vec![1, 2, 3], vec![1, 2, 3]], &[1, 2, -10]);

    // x + 2y >= 4, but x=1 and y=1 fixed → 1+2=3 < 4
    order_encoding_linear_test_inconsistent(&[vec![1], vec![1]], &[1, 2, -4]);
}

/// After adding a feasible constraint, forcing a literal can make it UNSAT.
#[test]
fn test_order_encoding_linear_propagate_on_creation() {
    // x in {1,2,3,4}, y in {2,4,6,8}, constraint: x + y >= 7.
    // At creation the solver propagates: y=2 is impossible (4+2=6 < 7),
    // so lits[1][0] (y>=4) is forced TRUE.
    // Adding ~lits[1][0] (y<4) afterwards must therefore be UNSAT.
    let domains: &[Vec<i32>] = &[vec![1, 2, 3, 4], vec![2, 4, 6, 8]];
    let coef_row = [1i32, 1, -7]; // x + y - 7 >= 0

    let mut solver = Solver::new();
    let mut all_vars: Vec<u32> = Vec::new();
    let mut all_lits: Vec<Vec<Lit>> = Vec::new();

    for domain in domains {
        let lits = make_order_encoding_vars(&mut solver, domain, &mut all_vars);
        all_lits.push(lits);
    }

    let constant = coef_row[2];
    let terms: Vec<LinearTerm> = (0..domains.len())
        .filter(|&j| coef_row[j] != 0)
        .map(|j| LinearTerm {
            lits: all_lits[j].clone(),
            domain: domains[j].clone(),
            coef: coef_row[j],
        })
        .collect();
    solver.add_constraint(Box::new(OrderEncodingLinear::new(terms, constant)));

    // ~all_lits[1][0] forces y < 4, i.e. y = 2.
    // Max sum becomes 4 + 2 = 6 < 7 → UNSAT.
    assert!(
        !solver.add_clause(&[!all_lits[1][0]]),
        "Forcing y<4 should be UNSAT (max x+y = 4+2 = 6 < 7)"
    );
}

// ── DirectEncodingExtensionSupports tests ─────────────────────────────────────

fn count_valid_assignments_direct(
    dom_sizes: &[usize],
    constraints: &[(Vec<usize>, Vec<Vec<i32>>)],
) -> usize {
    fn helper(
        idx: usize,
        dom_sizes: &[usize],
        constraints: &[(Vec<usize>, Vec<Vec<i32>>)],
        vals: &mut Vec<usize>,
    ) -> usize {
        if idx == dom_sizes.len() {
            for (var_ids, supports) in constraints {
                // At least one support must match
                let ok = supports.iter().any(|support| {
                    support.iter().zip(var_ids.iter()).all(|(&s, &vid)| {
                        s == -1 || s == vals[vid] as i32
                    })
                });
                if !ok {
                    return 0;
                }
            }
            return 1;
        }
        let mut ret = 0;
        for v in 0..dom_sizes[idx] {
            vals.push(v);
            ret += helper(idx + 1, dom_sizes, constraints, vals);
            vals.pop();
        }
        ret
    }
    helper(0, dom_sizes, constraints, &mut Vec::new())
}

fn direct_encoding_test(dom_sizes: &[usize], constraints: &[(Vec<usize>, Vec<Vec<i32>>)]) {
    let expected = count_valid_assignments_direct(dom_sizes, constraints);

    let mut solver = Solver::new();
    let mut all_vars: Vec<u32> = Vec::new();
    let mut var_descs: Vec<Vec<Lit>> = Vec::new();

    for &sz in dom_sizes {
        var_descs.push(make_direct_encoding_vars(&mut solver, sz, &mut all_vars));
    }

    for (var_ids, supports) in constraints {
        let lits: Vec<Vec<Lit>> = var_ids.iter().map(|&id| var_descs[id].clone()).collect();
        let c = DirectEncodingExtensionSupports::new(lits, supports.clone());
        solver.add_constraint(Box::new(c));
    }

    let actual = count_num_assignments(&mut solver, &all_vars);
    assert_eq!(expected, actual);
}

/// Various extension-support tables compared to brute-force enumeration.
#[test]
fn test_direct_encoding_extension_supports_count() {
    direct_encoding_test(
        &[3, 4, 5],
        &[(
            vec![0, 1, 2],
            vec![
                vec![0, 0, 0],
                vec![0, 0, 2],
                vec![0, 0, 3],
                vec![0, 1, 4],
                vec![1, 2, 1],
                vec![1, 3, 3],
                vec![2, 0, 1],
                vec![2, 0, 2],
                vec![2, 1, 3],
                vec![2, 2, 0],
            ],
        )],
    );

    direct_encoding_test(
        &[3, 4, 5],
        &[(
            vec![0, 1, 2],
            vec![
                vec![0, -1, 0],
                vec![0, 0, 2],
                vec![0, 0, 3],
                vec![0, 1, 4],
                vec![1, 2, -1],
                vec![1, 3, 3],
                vec![2, 0, 1],
                vec![-1, -1, 3],
            ],
        )],
    );

    direct_encoding_test(
        &[4, 4, 5, 5],
        &[
            (
                vec![0, 1, 2],
                vec![
                    vec![0, -1, 0],
                    vec![0, 0, 2],
                    vec![0, 0, 3],
                    vec![0, 1, 4],
                    vec![1, 2, -1],
                    vec![1, 3, 3],
                    vec![2, 0, 1],
                    vec![-1, -1, 3],
                ],
            ),
            (
                vec![1, 2, 3],
                vec![
                    vec![0, -1, 0],
                    vec![0, 0, 2],
                    vec![0, 0, 3],
                    vec![0, 1, 4],
                    vec![1, 2, -1],
                    vec![1, 3, 3],
                    vec![2, 0, 1],
                    vec![-1, -1, 3],
                ],
            ),
        ],
    );

    direct_encoding_test(
        &[3, 3],
        &[(
            vec![0, 1, 0],
            vec![
                vec![0, 0, 0],
                vec![0, 0, 1],
                vec![-1, 1, 2],
                vec![2, -1, -1],
            ],
        )],
    );

    direct_encoding_test(
        &[4, 4, 4, 4, 4],
        &[
            (
                vec![0, 1, 2],
                vec![
                    vec![0, -1, -1],
                    vec![-1, 0, -1],
                    vec![-1, -1, 0],
                ],
            ),
            (
                vec![1, 2, 4],
                vec![
                    vec![1, -1, -1],
                    vec![-1, 2, -1],
                    vec![-1, -1, 3],
                ],
            ),
            (
                vec![0, 2, 3],
                vec![
                    vec![2, -1, -1],
                    vec![-1, 2, -1],
                    vec![-1, -1, 3],
                ],
            ),
        ],
    );
}

// ── ActiveVerticesConnected (Graph) tests ─────────────────────────────────────

fn enumerate_connected_subgraph_by_sat(n: usize, edges: &[(usize, usize)]) -> usize {
    let mut solver = Solver::new();
    let vars: Vec<u32> = (0..n).map(|_| solver.new_var()).collect();
    let lits: Vec<Lit> = vars.iter().map(|&v| Lit::new(v, false)).collect();
    solver.add_constraint(Box::new(ActiveVerticesConnected::new(lits, edges)));
    count_num_assignments(&mut solver, &vars)
}

fn enumerate_connected_subgraph_bruteforce(n: usize, edges: &[(usize, usize)]) -> usize {
    (0u64..(1u64 << n))
        .filter(|&bits| {
            let active_cnt = (0..n).filter(|&v| ((bits >> v) & 1) == 1).count();
            if active_cnt <= 1 {
                return true;
            }
            let start = (0..n).find(|&v| ((bits >> v) & 1) == 1).unwrap();
            let mut seen = vec![false; n];
            let mut queue = std::collections::VecDeque::new();
            seen[start] = true;
            queue.push_back(start);
            while let Some(u) = queue.pop_front() {
                for &(v, w) in edges {
                    let next = if v == u {
                        w
                    } else if w == u {
                        v
                    } else {
                        continue;
                    };
                    if ((bits >> next) & 1) == 0 || seen[next] {
                        continue;
                    }
                    seen[next] = true;
                    queue.push_back(next);
                }
            }
            (0..n)
                .filter(|&v| ((bits >> v) & 1) == 1)
                .all(|v| seen[v])
        })
        .count()
}

fn active_vertices_connected_count_bruteforce(
    n_vars: usize,
    lits: &[Lit],
    edges: &[(usize, usize)],
) -> usize {
    assert!(n_vars < 64, "n_vars must be < 64 for bit-enumeration");
    for &lit in lits {
        assert!(
            (lit.var() as usize) < n_vars,
            "literal variable index out of range: var={} n_vars={n_vars}",
            lit.var()
        );
    }

    (0u64..(1u64 << n_vars))
        .filter(|&bits| {
            let is_active = |lit: Lit| -> bool {
                let val = ((bits >> lit.var()) & 1) == 1;
                if lit.is_neg() { !val } else { val }
            };
            let active_vertices: Vec<usize> = (0..lits.len())
                .filter(|&i| is_active(lits[i]))
                .collect();
            if active_vertices.len() <= 1 {
                return true;
            }

            let start = active_vertices[0];
            let mut seen = vec![false; lits.len()];
            let mut queue = std::collections::VecDeque::new();
            seen[start] = true;
            queue.push_back(start);
            while let Some(u) = queue.pop_front() {
                for &(v, w) in edges {
                    let next = if v == u {
                        w
                    } else if w == u {
                        v
                    } else {
                        continue;
                    };
                    if !is_active(lits[next]) || seen[next] {
                        continue;
                    }
                    seen[next] = true;
                    queue.push_back(next);
                }
            }

            active_vertices.into_iter().all(|v| seen[v])
        })
        .count()
}

fn active_vertices_connected_count_sat(n_vars: usize, lits: Vec<Lit>, edges: &[(usize, usize)]) -> usize {
    let mut solver = Solver::new();
    let vars: Vec<u32> = (0..n_vars).map(|_| solver.new_var()).collect();
    let mapped_lits: Vec<Lit> = lits
        .into_iter()
        .map(|lit| Lit::new(vars[lit.var() as usize], lit.is_neg()))
        .collect();
    solver.add_constraint(Box::new(ActiveVerticesConnected::new(mapped_lits, edges)));
    count_num_assignments(&mut solver, &vars)
}

/// For a path of n vertices, connected subsets are contiguous sub-paths plus the empty set.
/// Count = n*(n+1)/2 + 1.
fn connected_subgraph_test_path(n: usize) {
    let edges: Vec<(usize, usize)> = (0..n.saturating_sub(1)).map(|i| (i, i + 1)).collect();
    let expected = n * (n + 1) / 2 + 1;
    let actual = enumerate_connected_subgraph_by_sat(n, &edges);
    assert_eq!(expected, actual, "graph_path n={n}");
}

/// For a cycle of n vertices, connected subsets are contiguous arcs plus the empty and full set.
/// Count = n*(n-1) + 2.
fn connected_subgraph_test_cycle(n: usize) {
    let edges: Vec<(usize, usize)> = (0..n).map(|i| (i, (i + 1) % n)).collect();
    let expected = n * (n - 1) + 2;
    let actual = enumerate_connected_subgraph_by_sat(n, &edges);
    assert_eq!(expected, actual, "graph_cycle n={n}");
}

#[test]
fn test_graph_path() {
    connected_subgraph_test_path(1);
    connected_subgraph_test_path(2);
    connected_subgraph_test_path(5);
    connected_subgraph_test_path(50);
}

#[test]
fn test_graph_cycle() {
    connected_subgraph_test_cycle(1);
    connected_subgraph_test_cycle(2);
    connected_subgraph_test_cycle(5);
    connected_subgraph_test_cycle(50);
}

/// After fixing one vertex active and one inactive, the constraint forces
/// the disconnected part to be inactive; adding an active vertex there is UNSAT.
#[test]
fn test_graph_propagation_on_init() {
    let mut solver = Solver::new();
    let vars: Vec<u32> = (0..5).map(|_| solver.new_var()).collect();
    let edges: Vec<(usize, usize)> = (0..4).map(|i| (i, i + 1)).collect();
    let lits: Vec<Lit> = vars.iter().map(|&v| Lit::new(v, false)).collect();

    // Fix var1=active, var2=inactive before adding constraint
    solver.add_clause(&[Lit::new(vars[1], false)]); // var1 = active
    solver.add_clause(&[Lit::new(vars[2], true)]);  // var2 = inactive

    solver.add_constraint(Box::new(ActiveVerticesConnected::new(lits, &edges)));

    // The constraint propagates: vars 3 and 4 are in a different cluster from var1,
    // so they must be inactive. Forcing var4=active leads to UNSAT.
    assert!(
        !solver.add_clause(&[Lit::new(vars[4], false)]),
        "Forcing var4=active should be UNSAT after var2=inactive is set"
    );
}

#[test]
fn test_graph_duplicate_literal_count_regression() {
    let n_vars = 4;
    let lits = vec![
        Lit::new(0, false),
        Lit::new(1, false),
        Lit::new(2, false),
        Lit::new(3, false),
        Lit::new(0, false),
        Lit::new(0, false),
        Lit::new(1, true),
    ];
    let edges = vec![
        (0, 1),
        (0, 2),
        (0, 3),
        (0, 6),
        (1, 5),
        (2, 3),
        (2, 4),
        (3, 4),
        (4, 6),
        (5, 6),
    ];

    let expected = active_vertices_connected_count_bruteforce(n_vars, &lits, &edges);
    let actual = active_vertices_connected_count_sat(n_vars, lits.clone(), &edges);
    assert_eq!(expected, actual);
}

#[test]
fn test_stress_random_sat_16_to_20vars() {
    let rounds = stress_test_rounds();
    let mut seed = 0x5a9du64;

    for round in 0..rounds {
        let n_vars = 16 + (round % 5);
        let n_clauses = n_vars * 4;
        let planted_assignment: Vec<bool> = (0..n_vars).map(|_| lcg_range(&mut seed, 2) == 0).collect();

        let mut clauses = Vec::new();
        for _ in 0..n_clauses {
            let v0 = lcg_range(&mut seed, n_vars);
            let v1 = lcg_range(&mut seed, n_vars);
            let v2 = lcg_range(&mut seed, n_vars);
            let mut neg0 = lcg_range(&mut seed, 2) == 0;
            let neg1 = lcg_range(&mut seed, 2) == 0;
            let neg2 = lcg_range(&mut seed, 2) == 0;
            // If all three literals are false under the planted assignment
            // (var_value == is_negated), flipping one
            // literal (here the first) is enough to make the whole clause satisfiable.
            if planted_assignment[v0] == neg0
                && planted_assignment[v1] == neg1
                && planted_assignment[v2] == neg2
            {
                neg0 = !planted_assignment[v0];
            }
            clauses.push([(v0, neg0), (v1, neg1), (v2, neg2)]);
        }
        // Fix all but SAT_STRESS_FREE_VARS variables to shrink the model space while
        // still requiring full enumeration on 16..20 variables.
        for v in SAT_STRESS_FREE_VARS..n_vars {
            clauses.push([
                (v, !planted_assignment[v]),
                (v, !planted_assignment[v]),
                (v, !planted_assignment[v]),
            ]);
        }

        let expected = brute_force_count(n_vars, &clauses);

        let mut solver = Solver::new();
        let vars: Vec<u32> = (0..n_vars).map(|_| solver.new_var()).collect();
        for &[(v0, n0), (v1, n1), (v2, n2)] in &clauses {
            solver.add_clause(&[
                Lit::new(vars[v0], n0),
                Lit::new(vars[v1], n1),
                Lit::new(vars[v2], n2),
            ]);
        }
        let actual = count_num_assignments(&mut solver, &vars);
        assert_eq!(
            expected, actual,
            "round={round} n_vars={n_vars} n_clauses={n_clauses}"
        );
    }
}

#[test]
fn test_stress_active_vertices_connected() {
    let rounds = stress_test_rounds();
    let mut seed = 0x3344_7788u64;

    for round in 0..rounds {
        let n = 8 + lcg_range(&mut seed, 5);
        let mut edges = Vec::new();
        for u in 0..n {
            for v in u + 1..n {
                if lcg_range(&mut seed, 3) == 0 {
                    edges.push((u, v));
                }
            }
        }
        let expected = enumerate_connected_subgraph_bruteforce(n, &edges);
        let actual = enumerate_connected_subgraph_by_sat(n, &edges);
        assert_eq!(expected, actual, "round={round} n={n}");
    }
}

// ── GraphDivision tests ───────────────────────────────────────────────────────

fn enumerate_graph_division_by_sat(
    n: usize,
    graph: &[(usize, usize)],
    size_cands: &[Vec<i32>],
) -> usize {
    let mut solver = Solver::new();

    // Build per-vertex order-encoding objects
    let mut vertices: Vec<OptionalOrderEncoding> = (0..n)
        .map(|_| OptionalOrderEncoding {
            lits: Vec::new(),
            values: Vec::new(),
        })
        .collect();

    if !size_cands.is_empty() {
        for i in 0..n {
            if size_cands[i].is_empty() {
                continue;
            }
            // Create (size_cands[i].len()-1) bool vars for the order encoding.
            let lits: Vec<Lit> = (1..size_cands[i].len())
                .map(|_| Lit::new(solver.new_var(), false))
                .collect();
            // Monotonicity for order encoding: (x >= values[j+1]) => (x >= values[j]).
            for j in 1..lits.len() {
                solver.add_clause(&[!lits[j], lits[j - 1]]);
            }
            vertices[i].lits = lits;
            vertices[i].values = size_cands[i].clone();
        }
    }

    // Edge variables: lit=TRUE means edge is a border (disconnected).
    let edge_vars: Vec<u32> = (0..graph.len()).map(|_| solver.new_var()).collect();
    let edge_lits: Vec<Lit> = edge_vars.iter().map(|&v| Lit::new(v, false)).collect();

    let c = GraphDivision::new(vertices, graph, edge_lits);
    solver.add_constraint(Box::new(c));

    count_num_assignments(&mut solver, &edge_vars)
}

/// Naive enumeration over all 2^m edge-border assignments.
/// An assignment is valid iff:
/// 1. No border edge connects two vertices in the same BFS-connected component.
/// 2. All size constraints are satisfied.
fn enumerate_graph_division_naive(
    n: usize,
    graph: &[(usize, usize)],
    size_cands: &[Vec<i32>],
) -> usize {
    let m = graph.len();
    let mut adj: Vec<Vec<(usize, usize)>> = vec![Vec::new(); n];
    for (e, &(u, v)) in graph.iter().enumerate() {
        adj[u].push((v, e));
        adj[v].push((u, e));
    }

    let mut ret = 0;
    'outer: for bits in 0u64..1u64 << m {
        let mut region_id = vec![-1i32; n];

        for start in 0..n {
            if region_id[start] >= 0 {
                continue;
            }

            // BFS using only non-border edges
            let mut region = Vec::new();
            let mut queue = std::collections::VecDeque::new();
            queue.push_back(start);
            region.push(start);
            region_id[start] = start as i32;

            while let Some(p) = queue.pop_front() {
                for &(q, e) in &adj[p] {
                    if (bits >> e) & 1 == 1 {
                        continue; // border edge
                    }
                    if region_id[q] >= 0 {
                        continue; // already visited
                    }
                    queue.push_back(q);
                    region.push(q);
                    region_id[q] = start as i32;
                }
            }

            // Rule 1: a border edge must not have both endpoints in the same region
            for &p in &region {
                for &(q, e) in &adj[p] {
                    if (bits >> e) & 1 == 1 && region_id[q] == start as i32 {
                        continue 'outer; // invalid
                    }
                }
            }

            // Rule 2: size constraints
            if !size_cands.is_empty() {
                let size = region.len() as i32;
                for &p in &region {
                    if size_cands[p].is_empty() {
                        continue;
                    }
                    if !size_cands[p].contains(&size) {
                        continue 'outer; // invalid
                    }
                }
            }
        }

        ret += 1;
    }
    ret
}

/// For a path of n vertices, any border-assignment of the n-1 edges is valid: 2^(n-1) total.
fn graph_division_test_path(n: usize) {
    let graph: Vec<(usize, usize)> = (0..n.saturating_sub(1)).map(|i| (i, i + 1)).collect();
    let expected = 1usize << n.saturating_sub(1);
    let actual = enumerate_graph_division_by_sat(n, &graph, &[]);
    assert_eq!(expected, actual, "graph_division_path n={n}");
}

/// For a cycle of n vertices (n >= 3), the only invalid assignments are those with
/// exactly one non-border edge (creates a chord within the full region): 2^n - n valid.
fn graph_division_test_cycle(n: usize) {
    let mut graph: Vec<(usize, usize)> = (0..n - 1).map(|i| (i, i + 1)).collect();
    graph.push((0, n - 1));
    let expected = (1usize << n) - n;
    let actual = enumerate_graph_division_by_sat(n, &graph, &[]);
    assert_eq!(expected, actual, "graph_division_cycle n={n}");
}

#[test]
fn test_graph_division_path() {
    graph_division_test_path(1);
    graph_division_test_path(2);
    graph_division_test_path(5);
    graph_division_test_path(10);
}

#[test]
fn test_graph_division_cycle() {
    graph_division_test_cycle(3);
    graph_division_test_cycle(5);
    graph_division_test_cycle(10);
}

/// Complex graphs compared against naive enumeration.
#[test]
fn test_graph_division_complex() {
    // 3×3 grid (9 vertices, 12 edges)
    let grid3x3: Vec<(usize, usize)> = vec![
        (0, 1), (1, 2), (3, 4), (4, 5), (6, 7), (7, 8),
        (0, 3), (1, 4), (2, 5), (3, 6), (4, 7), (5, 8),
    ];

    let expected1 = enumerate_graph_division_naive(9, &grid3x3, &[]);
    let actual1 = enumerate_graph_division_by_sat(9, &grid3x3, &[]);
    assert_eq!(expected1, actual1, "3x3 grid no size constraints");

    let size_cands1: Vec<Vec<i32>> = vec![
        vec![2, 3], vec![], vec![], vec![], vec![1, 3], vec![], vec![], vec![], vec![4, 5],
    ];
    let expected2 = enumerate_graph_division_naive(9, &grid3x3, &size_cands1);
    let actual2 = enumerate_graph_division_by_sat(9, &grid3x3, &size_cands1);
    assert_eq!(expected2, actual2, "3x3 grid with size constraints");

    // 3×4 grid (12 vertices, 17 edges)
    let grid3x4: Vec<(usize, usize)> = vec![
        (0, 1), (1, 2), (2, 3),
        (4, 5), (5, 6), (6, 7),
        (8, 9), (9, 10), (10, 11),
        (0, 4), (1, 5), (2, 6), (3, 7),
        (4, 8), (5, 9), (6, 10), (7, 11),
    ];
    let size_cands2: Vec<Vec<i32>> = vec![
        vec![4], vec![5], vec![3], vec![], vec![], vec![], vec![],
        vec![], vec![], vec![], vec![], vec![],
    ];
    let expected3 = enumerate_graph_division_naive(12, &grid3x4, &size_cands2);
    let actual3 = enumerate_graph_division_by_sat(12, &grid3x4, &size_cands2);
    assert_eq!(expected3, actual3, "3x4 grid with size constraints");
}

/// Edge-case handling: constraints that are UNSAT from the start.
#[test]
fn test_graph_division_out_of_range() {
    // Case 1: vertex 0 requires minimum size 3, but there are only 2 vertices total.
    {
        let mut solver = Solver::new();
        let vertices: Vec<OptionalOrderEncoding> = vec![
            OptionalOrderEncoding { lits: Vec::new(), values: vec![3] },
            OptionalOrderEncoding { lits: Vec::new(), values: Vec::new() },
        ];
        let graph: Vec<(usize, usize)> = vec![(0, 1)];
        let edge_lits: Vec<Lit> = (0..1).map(|_| Lit::new(solver.new_var(), false)).collect();
        let c = GraphDivision::new(vertices, &graph, edge_lits);
        solver.add_constraint(Box::new(c));
        assert_eq!(solver.solve(), LBool::False,
            "vertex requiring size > total vertices must be UNSAT");
    }

    // Case 2: vertex 0 requires size 3, but edge (1,2) is forced disconnected,
    // so the potential region of vertex 0 is at most {0, 1} (size 2).
    {
        let mut solver = Solver::new();
        let vertices: Vec<OptionalOrderEncoding> = vec![
            OptionalOrderEncoding { lits: Vec::new(), values: vec![3] },
            OptionalOrderEncoding { lits: Vec::new(), values: Vec::new() },
            OptionalOrderEncoding { lits: Vec::new(), values: Vec::new() },
        ];
        let graph: Vec<(usize, usize)> = vec![(0, 1), (1, 2)];
        let edge_lits: Vec<Lit> = (0..2).map(|_| Lit::new(solver.new_var(), false)).collect();

        // Force edge (1,2) disconnected BEFORE adding the constraint
        solver.add_clause(&[edge_lits[1]]);

        let c = GraphDivision::new(vertices, &graph, edge_lits);
        solver.add_constraint(Box::new(c));
        assert_eq!(solver.solve(), LBool::False,
            "vertex requiring size 3 with max reachable 2 must be UNSAT");
    }
}

#[test]
fn test_stress_graph_division() {
    let rounds = stress_test_rounds();
    let mut seed = 0x1020_3040u64;

    for round in 0..rounds {
        let n = 5 + lcg_range(&mut seed, 5);
        let mut edge_used = vec![vec![false; n]; n];
        let mut graph = Vec::new();
        for i in 0..n.saturating_sub(1) {
            edge_used[i][i + 1] = true;
            edge_used[i + 1][i] = true;
            graph.push((i, i + 1));
        }
        let max_edges = std::cmp::min(n * (n - 1) / 2, 15);
        let target_edges = (n - 1) + lcg_range(&mut seed, max_edges - (n - 1) + 1);
        while graph.len() < target_edges {
            let a = lcg_range(&mut seed, n);
            let b = lcg_range(&mut seed, n - 1);
            let b = if b >= a { b + 1 } else { b };
            let (u, v) = if a < b { (a, b) } else { (b, a) };
            if edge_used[u][v] {
                continue;
            }
            edge_used[u][v] = true;
            edge_used[v][u] = true;
            graph.push((u, v));
        }

        let mut size_cands = vec![Vec::new(); n];
        let max_size_cand = std::cmp::min(n, 4);
        for cand in &mut size_cands {
            if lcg_range(&mut seed, 2) == 0 {
                continue;
            }
            *cand = vec![(1 + lcg_range(&mut seed, max_size_cand)) as i32];
        }

        let expected = enumerate_graph_division_naive(n, &graph, &size_cands);
        let actual = enumerate_graph_division_by_sat(n, &graph, &size_cands);
        assert_eq!(
            expected, actual,
            "round={round} n={n} edges={} size_cands={size_cands:?}",
            graph.len()
        );
    }
}
