# EFX allocations for three agents and seven or eight chores

Code for the paper

> Xinkai Zhang. *EFX Allocations for Three Agents and Seven or Eight Chores.*
> [arXiv:2609.10585](https://arxiv.org/abs/2609.10585), 2026.

The paper proves that every additive chore instance with three agents and seven
or eight chores has an EFX allocation. In both cases a short argument by hand
reduces the question to a formula of linear real arithmetic with one clause for
every allocation, and the formula is shown to be unsatisfiable with the SMT
solvers Z3 and cvc5. This repository contains the scripts that build and decide
those formulas, together with the checks described in the paper.

## Contents

| Path | Purpose | Paper |
|---|---|---|
| `smt/seven_chores_z3.py` | builds `Phi_7` and decides it with Z3 | Prop. 2, Table 1 |
| `smt/seven_chores_cvc5.py` | the same with cvc5 (proof checking on) | Prop. 2, Table 1 |
| `smt/eight_chores_z3.py` | builds `Phi_8` (with `--residual-disjoint-argmins`) and decides it with Z3 | Prop. 4, Tables 1-2 |
| `smt/eight_chores_cvc5.py` | the same with cvc5 (proof checking on) | Prop. 4, Tables 1-2 |
| `smt/eight_chores_alt_z3.py` | a second, separately written encoding of `Phi_8` | Table 2 |
| `smt/check_eight_chores_encoding.py` | finite exact checks of the eight-chore encoding | Section 5 |
| `efx_checker/` | brute-force EFX checker over all `n**m` allocations, exact fractions | Section 5 |
| `examples/` | the four matrices of Appendix A and the script that checks them | Table 3 |
| `tests/` | tests of `efx_checker`, including the He-Tao counterexamples | |
| `RUNS.md` | every reported run with its command, result and timing | |

## Setup

Python 3.11 or newer.

```sh
python3 -m venv .venv
.venv/bin/pip install -r requirements.txt   # z3-solver==5.1.0.0, cvc5==1.3.4
.venv/bin/pip install pytest                # for the tests only
```

The pinned versions are those of the reported runs. Other versions should give
the same answers but may take very different times, especially on `Phi_8`.

## Reproducing the proofs

From the repository root:

```sh
# Theorem 1 (seven chores): about 8 minutes each on a 14-core Apple M4 Pro
.venv/bin/python smt/seven_chores_z3.py   --timeout 900
.venv/bin/python smt/seven_chores_cvc5.py --timeout 900

# Theorem 2 (eight chores): about 15 minutes with Z3, about 1 hour with cvc5
.venv/bin/python smt/eight_chores_z3.py   --m 8 --timeout 7200 --arith-solver 2 --residual-disjoint-argmins
.venv/bin/python smt/eight_chores_cvc5.py --m 8 --timeout 7200 --residual-disjoint-argmins
```

Each script prints a JSON report with the solver version, the formula size and
the field `"result"`, which should be `unsat`. A `sat` answer would give a
counterexample to the corresponding theorem; `unknown` or a timeout gives no
information. For `Phi_8` the flag `--residual-disjoint-argmins` is required:
without it the scripts build the formula over all eight-chore matrices, which
the paper does not use.

The further runs of Table 2 and the commands for them are listed in
[`RUNS.md`](RUNS.md).

## Checks

```sh
.venv/bin/python -m pytest -q                            # under a minute
.venv/bin/python examples/occupancy_examples.py          # Table 3, a few seconds
.venv/bin/python smt/check_eight_chores_encoding.py      # about two minutes
```

The last command compares the eight-chore clause builders with
`efx_checker` on exact rational matrices, checks that five wrong predicates are
detected, and tests the reduction steps on random instances; it ends with
`"result": "pass"`. Set `EFX_CHECKER_SLOW=1` to include two slower test sweeps
of the He-Tao five-agent instance.

`efx_checker` can also be run on any matrix file:

```sh
.venv/bin/python -m efx_checker.cli tests/data/he_tao_counterexamples.json --mode chores
```

## Use of AI tools

Large language models were used, as coding agents, in developing the proofs and
the code and in drafting the paper. The author has checked the mathematics and
the code and is responsible for both.

## Citation

```bibtex
@misc{Zhang2026EFXChores,
  author        = {Xinkai Zhang},
  title         = {{EFX} Allocations for Three Agents and Seven or Eight Chores},
  year          = {2026},
  eprint        = {2609.10585},
  archivePrefix = {arXiv},
  primaryClass  = {cs.GT},
  url           = {https://arxiv.org/abs/2609.10585}
}
```

## License

MIT, see [LICENSE](LICENSE).
