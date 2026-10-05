# Recorded runs

This file lists the solver runs reported in *EFX Allocations for Three Agents
and Seven or Eight Chores* ([arXiv:2609.10585](https://arxiv.org/abs/2609.10585)),
with the command for each one. `Phi_7` is the seven-chore formula of Section 3
of the paper and `Phi_8` the eight-chore formula of Section 4. Timings are
indicative.

## Environment

| | |
|---|---|
| Machine | 14-core Apple M4 Pro |
| Python | CPython 3.13.3 |
| Solvers | `z3-solver` 5.1.0.0 (Z3 5.1.0), `cvc5` 1.3.4, pinned in [`requirements.txt`](requirements.txt) |

All formulas are over SMT reals with exact rational arithmetic. The
`--timeout` values are soft limits inside the solvers; every `unsat` run below
finished before its limit.

## Runs for Propositions 2 and 4

Table 1 of the paper. Both cvc5 runs produce a proof and check it inside cvc5
(`produce-proofs=true`, `check-proofs=true`). The last column is the check time
when the runs were repeated in September 2026 on the same machine.

| Formula | Solver | Result | Build (s) | Check (s) | Rerun (s) |
|---|---|---|---:|---:|---:|
| `Phi_7` | Z3 5.1.0 | `unsat` | 0.959 | 517.911 | 485.669 |
| `Phi_7` | cvc5 1.3.4 | `unsat` | 0.114 | 483.318 | 399.756 |
| `Phi_8` | Z3 5.1.0, `arith.solver=2` | `unsat` | 4.625 | 852.824 | 606.183 |
| `Phi_8` | cvc5 1.3.4 | `unsat` | 0.521 | 3729.851 | 3156.109 |

```sh
python smt/seven_chores_z3.py   --timeout 900
python smt/seven_chores_cvc5.py --timeout 900
python smt/eight_chores_z3.py   --m 8 --timeout 7200 --arith-solver 2 --disjoint-argmins
python smt/eight_chores_cvc5.py --m 8 --timeout 7200 --disjoint-argmins
```

The eight-chore scripts build `Phi_8` only when `--disjoint-argmins` is given;
without it they build the formula of Remark 2. Z3's default phase selection,
3, is used unless `--phase-selection` is given.

## Further eight-chore runs

Table 2 of the paper. The first three rows decide `Phi_8` again with other Z3
settings or with the second encoding `smt/eight_chores_alt_z3.py`, which
requires only positive row sums, sorts the free columns in decreasing order
and keeps the `j = i` comparisons. The `m = 7` rows run the same scripts on
seven chores, where the answer is known from Theorem 1. The last two rows
change the clauses and are expected to be satisfiable.

| Run | Result | Check (s) |
|---|---|---:|
| `Phi_8`, Z3, `arith.solver=2`, `phase_selection=1` | `unsat` | 850.863 |
| `Phi_8`, Z3, `arith.solver=6` | `unsat` | 2717.209 |
| `Phi_8`, second encoding (Z3) | `unsat` | 469.389 |
| `m = 7`, Z3, `arith.solver=2` | `unsat` | 17.952 |
| `m = 7`, cvc5 with proof checking | `unsat` | 44.497 |
| `m = 7`, second encoding (Z3) | `unsat` | 4.725 |
| `Phi_8` with `>=` instead of `>` | `sat` | 79.500 |
| `Phi_8` with no chore removed (envy-freeness) | `sat` | 12.036 |

```sh
python smt/eight_chores_z3.py --m 8 --timeout 7200 --arith-solver 2 --phase-selection 1 --disjoint-argmins
python smt/eight_chores_z3.py --m 8 --timeout 7200 --arith-solver 6 --disjoint-argmins
python smt/eight_chores_alt_z3.py --m 8 --timeout 7200

python smt/eight_chores_z3.py   --m 7 --timeout 7200 --arith-solver 2 --disjoint-argmins
python smt/eight_chores_cvc5.py --m 7 --timeout 7200 --disjoint-argmins
python smt/eight_chores_alt_z3.py --m 7 --timeout 7200

python smt/eight_chores_z3.py --m 8 --timeout 7200 --arith-solver 2 --disjoint-argmins --variant weak
python smt/eight_chores_z3.py --m 8 --timeout 7200 --arith-solver 2 --disjoint-argmins --variant envy
```

The same two changes make `Phi_7` satisfiable as well, within a few seconds.
Without `--disjoint-argmins` and with `--m 7`, `eight_chores_z3.py` builds the
constraints of `Phi_7`:

```sh
python smt/eight_chores_z3.py --m 7 --timeout 900 --variant weak
python smt/eight_chores_z3.py --m 7 --timeout 900 --variant envy
```

## Runs without a result

Section 6 of the paper mentions three runs that did not finish.

| Run | Outcome |
|---|---|
| `Phi_7` without column sorting, Z3 | stopped after 4 h 19 min |
| seven chores with only `c >= 0` (no normalization, no sorting), Z3 and cvc5 | `unknown` after 3600 s |
| the formula of Remark 2 (eight chores, all columns sorted) | timed out in several solver configurations |

The first formula is built by `python smt/eight_chores_z3.py --m 7
--no-column-symmetry`, and the third by `python smt/eight_chores_z3.py --m 8`
(or `eight_chores_cvc5.py --m 8`). The scripts in this repository always add
unit row sums, so they do not build the second formula.

## Formula sizes

| | `Phi_7` | `Phi_8` | `Phi_8`, second encoding |
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
  allocations (52,488 pairs) and finds no disagreement with the exhaustive
  checker in `efx_checker/`;
- checks that five wrong predicates disagree with it: removing a chore from
  the envied bundle (goods EFX), skipping zero-cost chores, `>=` instead of
  `>`, costing the other bundle in the wrong row, and removing no chore;
- checks the zero-row construction (3360 cases), invariance of the EFX
  allocations under row scaling and chore permutation (78,732 allocations
  each), the canonical forms of Sections 3.1 and 4.2 on 1000 random matrices
  each, and the steps of the proof of Lemma 5 on 30 random instances with a
  shared cheapest chore.

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
