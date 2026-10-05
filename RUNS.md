# Recorded runs

This file lists the solver runs reported in *EFX Allocations for Three Agents
and Seven or Eight Chores* ([arXiv:2609.10585](https://arxiv.org/abs/2609.10585)),
with the command that produces each one. `Phi_7` is the seven-chore formula of
Section 3 of the paper and `Phi_8` the eight-chore formula of Section 4.
Timings depend on the hardware and are given only to identify the runs.

## Environment

| | |
|---|---|
| Machine | 14-core Apple M4 Pro (macOS 26.6.2 for the September 2026 reruns) |
| Python | CPython 3.13.3 |
| Solvers | `z3-solver` 5.1.0.0 (reports Z3 5.1.0), `cvc5` 1.3.4, pinned in [`requirements.txt`](requirements.txt) |

All formulas are over SMT reals with exact rational arithmetic. The
`--timeout` values are soft limits inside the solvers; every `unsat` run below
finished before its limit.

## Primary decisions

Table 1 of the paper. Both cvc5 runs produce a proof and check it inside cvc5
(`produce-proofs=true`, `check-proofs=true`).

| Formula | Solver | Result | Build (s) | Check (s) | Check (s), Sept. 2026 rerun |
|---|---|---|---:|---:|---:|
| `Phi_7` | Z3 5.1.0 | `unsat` | 0.959 | 517.911 | 485.669 |
| `Phi_7` | cvc5 1.3.4 | `unsat` | 0.114 | 483.318 | 399.756 |
| `Phi_8` | Z3 5.1.0, `arith.solver=2` | `unsat` | 4.625 | 852.824 | 606.183 |
| `Phi_8` | cvc5 1.3.4 | `unsat` | 0.521 | 3729.851 | 3156.109 |

```sh
python smt/seven_chores_z3.py   --timeout 900
python smt/seven_chores_cvc5.py --timeout 900
python smt/eight_chores_z3.py   --m 8 --timeout 7200 --arith-solver 2 --residual-disjoint-argmins
python smt/eight_chores_cvc5.py --m 8 --timeout 7200 --residual-disjoint-argmins
```

The eight-chore scripts build `Phi_8` only when `--residual-disjoint-argmins`
is given. Without it they build the formula over all eight-chore matrices,
which no solver configuration decided (see below). Z3's default phase
selection, 3, is used unless `--phase-selection` is given.

## Further eight-chore runs

Table 2 of the paper. The first three rows decide `Phi_8` again with other Z3
settings or with the alternative encoding `smt/eight_chores_alt_z3.py`, which
requires only positive row totals, sorts the free columns in decreasing order
and keeps the `j = i` comparisons. The `m = 7` rows run the same scripts on
seven chores, where the answer is known from Theorem 1. The last two rows
change the predicate and must be satisfiable.

| Run | Result | Check (s) |
|---|---|---:|
| `Phi_8`, Z3, `arith.solver=2`, `phase_selection=1` | `unsat` | 850.863 |
| `Phi_8`, Z3, `arith.solver=6` | `unsat` | 2717.209 |
| `Phi_8`, alternative encoding (Z3) | `unsat` | 469.389 |
| `m = 7`, Z3, `arith.solver=2` | `unsat` | 17.952 |
| `m = 7`, cvc5 with proof checking | `unsat` | 44.497 |
| `m = 7`, alternative encoding (Z3) | `unsat` | 4.725 |
| `m = 8`, `>` replaced by `>=` | `sat` | 79.500 |
| `m = 8`, no chore removed (envy-freeness) | `sat` | 12.036 |

```sh
python smt/eight_chores_z3.py --m 8 --timeout 7200 --arith-solver 2 --phase-selection 1 --residual-disjoint-argmins
python smt/eight_chores_z3.py --m 8 --timeout 7200 --arith-solver 6 --residual-disjoint-argmins
python smt/eight_chores_alt_z3.py --m 8 --timeout 7200

python smt/eight_chores_z3.py   --m 7 --timeout 7200 --arith-solver 2 --residual-disjoint-argmins
python smt/eight_chores_cvc5.py --m 7 --timeout 7200 --residual-disjoint-argmins
python smt/eight_chores_alt_z3.py --m 7 --timeout 7200

python smt/eight_chores_z3.py --m 8 --timeout 7200 --arith-solver 2 --residual-disjoint-argmins --variant ge-control
python smt/eight_chores_z3.py --m 8 --timeout 7200 --arith-solver 2 --residual-disjoint-argmins --variant ef-control
```

The same two changes make `Phi_7` satisfiable as well, within a few seconds:

```sh
python smt/eight_chores_z3.py --m 7 --timeout 900 --variant ge-control
python smt/eight_chores_z3.py --m 7 --timeout 900 --variant ef-control
```

(Without `--residual-disjoint-argmins` and with `--m 7`, `eight_chores_z3.py`
builds exactly the constraints of `Phi_7`.)

## Runs without a result

An `unknown` answer or a timeout says nothing about the theorems. These runs
are listed because they explain which constraints the formulas contain.

| Run | Outcome |
|---|---|
| `Phi_7` without column sorting, Z3 | stopped after 4 h 19 min |
| seven chores with only `c >= 0` (no normalization, no sorting), Z3 and cvc5 | `unknown` after 3600 s |
| all eight-chore matrices (no shared-minimum reduction) | timed out in several solver configurations |

## Formula sizes

| | `Phi_7` | `Phi_8` | `Phi_8`, alternative encoding |
|---|---:|---:|---:|
| Real variables | 21 | 24 | 24 |
| Allocation clauses | 2187 | 6561 | 6561 |
| Literals per clause | 14 | 16 | 24 |
| Assertions | 2217 | 6640 | 6640 |

The 2217 assertions of `Phi_7` are 21 nonnegativity constraints, three row
sums, six column comparisons and 2187 allocation clauses.

## Checks of the eight-chore encoding

`python smt/check_eight_chores_encoding.py` (about two minutes) prints a JSON
report ending in `"result": "pass"`. It

- evaluates the clause builders of `eight_chores_z3.py` and
  `eight_chores_alt_z3.py` on 8 exact rational matrices and all 6561
  allocations (52,488 pairs) and finds no disagreement with the brute-force
  checker in `efx_checker/`;
- checks that five wrong predicates disagree with it: removing a chore from
  the envied bundle (goods EFX), skipping zero-cost chores, `>=` instead of
  `>`, costing the other bundle in the wrong row, and removing no chore;
- checks the zero-row construction (3360 cases), invariance of the EFX
  allocations under row scaling and chore permutation (78,732 allocations
  each), 1000 canonical and 1000 residual canonical forms, and the
  shared-minimum lifting step on 30 random instances.

The cvc5 clause builder is not exercised by this script.

## Occupancy examples

`python examples/occupancy_examples.py` goes through all 2187 allocations of
the four matrices in [`examples/occupancy_examples.json`](examples/occupancy_examples.json)
and reproduces Table 3 of the paper.

| Matrix | Bundle sizes of every EFX allocation | EFX allocations |
|---|---|---:|
| `only-322` | (3,2,2) | 64 |
| `only-331` | (3,3,1) | 21 |
| `only-421` | (4,2,1) | 8 |
| `only-511` | (5,1,1) | 6 |
