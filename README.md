# glucose_rs

A complete Rust port of the [Glucose](https://www.labri.fr/perso/lsimon/glucose/) CDCL SAT solver.

## Features

- **CDCL** (Conflict-Driven Clause Learning) algorithm
- **VSIDS** variable activity heuristics with exponential decay
- **Two-watched-literals** BCP (binary propagation optimised separately)
- **Glucose restart heuristics** – LBD moving-average (K=0.8) vs trail-length blocking (R=1.4)
- **LBD** (Literal Block Distance) scored learned clauses
- **Phase saving** for decision polarity
- **Deep clause minimization** (ccmin\_mode = 2)
- **Periodic learned-clause database reduction**
- **DIMACS CNF** input parser

## Key parameters

| Parameter | Value |
|-----------|-------|
| LBD queue size | 50 |
| Trail queue size | 5000 |
| K (restart force) | 0.8 |
| R (restart block) | 1.4 |
| `firstReduceDB` | 2000 |
| `incReduceDB` | 300 |
| `var_decay` | 0.8 |
| `clause_decay` | 0.999 |
| Phase saving | 2 |

## Building

```bash
cargo build --release
```

## Usage

```bash
cargo run --release -- input.cnf
```

Exit codes follow SAT-competition conventions: **10** = SATISFIABLE, **20** = UNSATISFIABLE, **0** = UNKNOWN.

## Running tests

```bash
cargo test
```

## Project structure

```
src/
  lib.rs          – crate root
  types.rs        – Lit, Var, LBool primitives
  clause.rs       – Clause, ClauseDb
  watch.rs        – WatchList (two-watched-literals)
  solver.rs       – full CDCL solver
  io/
    mod.rs
    dimacs.rs     – DIMACS CNF parser
tests/
  integration_test.rs
```
