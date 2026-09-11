# EFX Allocations for Three Agents and Seven or Eight Chores — artifact

Artifact repository for

> Xinkai Zhang. *EFX Allocations for Three Agents and Seven or Eight Chores.*
> [arXiv:2609.10585](https://arxiv.org/abs/2609.10585) (cs.GT), 2026.

The paper proves that every nonnegative additive chore instance with three
agents and either seven or eight indivisible chores admits a chores-EFX
allocation, in the zero-tolerant sense that every owned chore, including one of
zero cost, is quantified in the trim. Both proofs are computer-assisted: hand
lemmas reduce nonexistence to a quantifier-free linear real arithmetic
(QF_LRA) formula with one failure clause per complete allocation, and Z3 and
cvc5 report that formula unsatisfiable.

This repository contains the scripts that build and decide those two formulas,
the cross-checking encoder and audit harness, the record of every reported run,
and the regression suite. The paper source is on arXiv, not in this repository.

## What the machine decides

The two theorems rest on exactly two machine premises:

| Machine premise | Formula | Decided by |
|---|---|---|
| Proposition 2: `Phi_all` is unsatisfiable | seven-chore all-allocation formula, 21 real variables, 2187 clauses | `artifacts/s5_all_z3.py`, `artifacts/s5_all_cvc5.py` |
| Proposition 4: `Phi_res` is unsatisfiable | eight-chore pairwise-disjoint-argmin residual, 24 real variables, 6561 clauses | `artifacts/s6_all_z3.py`, `artifacts/s6_all_cvc5.py` with `--residual-disjoint-argmins` |

Everything else in this repository is corroboration, calibration, or a control.
In particular, the two solvers per theorem give solver diversity rather than
independent mathematical encodings, and the cross-checking encoder and the
audit harness were produced inside the same machine-assisted workflow, so they
give transcription diversity rather than an audit by an independent group.

The reduction lemmas are *not* machine-checked. They are short by design and
are meant to be checked by hand from the paper; Appendix F of the paper
reproduces the formula construction verbatim from `artifacts/s5_all_z3.py` and
`artifacts/s6_all_z3.py`, so the predicate, the polarity and the canonical
constraints can be audited from the paper alone.

Every decision uses exact rational arithmetic over unbounded SMT reals. There
is no finite or discretized cost domain and no floating-point comparison
anywhere in the decision path.

## Layout

```
artifacts/                      code and data cited by the paper
  s5_all_z3.py                  Phi_all in QF_LRA through the Z3 API
  s5_all_cvc5.py                Phi_all in QF_LRA through the cvc5 API
  s6_all_z3.py                  Phi_res (and the full m=8 class) through Z3
  s6_all_cvc5.py                Phi_res (and the full m=8 class) through cvc5
  s6_residual_referee.py        cross-checking transcription of Phi_res
  s6_audit.py                   finite exact audit of the m=8 clause builders
  s5_occupancy_check.py         self-contained 3^7 walk behind Table 4
  s5_matrices.json              the four occupancy witnesses of Table 4
  hetao.json                    He-Tao counterexample instances, used by the suite
  requirements-pinned.txt       pinned solver versions of the reported runs
record/
  RUNS.md                       every reported run, result and timing
  SPEC_GAPS.md                  semantic gaps found while reimplementing the predicate
spec/SPEC.md                    the predicate contract behind Definition 1
verifier_b/                     independent exhaustive certifier, reimplemented
                                from spec/SPEC.md and sharing no code with src/
src/                            exhaustive enumerator and a bounded integer-domain
                                search; used by the regression suite only
tests/                          regression suite
```

## Requirements

Python 3.11 or newer, plus the two pinned solvers. The reported runs used
CPython 3.13.3.

```sh
python3 -m venv .venv
.venv/bin/pip install -r artifacts/requirements-pinned.txt
.venv/bin/pip install pytest          # regression suite only
```

`artifacts/requirements-pinned.txt` pins `z3-solver==5.1.0.0`, which reports Z3
5.1.0, and `cvc5==1.3.4`. Because the decisions are exact, no verdict depends on
the hardware; the pins fix the solver search strategy, and therefore the
timings, and are how the reported runs are identified. Solver heuristics can
change between releases, so an unpinned solver may take a different amount of
time or, for the eight-chore formula, fail to terminate.

All commands below are run from the repository root.

## Smoke test

Under a minute, and enough to show that the environment is working:

```sh
.venv/bin/python -m pytest -q                       # 117 passed, 2 skipped
.venv/bin/python artifacts/s5_occupancy_check.py    # Table 4 of the paper
```

The second command walks all 2187 allocations of each of the four stored
matrices and should print EFX counts 64, 21, 8 and 6 against sole occupancy
shapes `3+2+2`, `3+3+1`, `4+2+1` and `5+1+1`.

## Reproducing the two machine premises

Each script prints one JSON report with its solver version, logic, scope,
domain, allocation and assertion counts, result and timings. **Read the
`"result"` field, not the exit status.** A successful reproduction prints
`unsat`. An `unknown`, a timeout or an error is no result and neither confirms
nor refutes anything; a `sat` result on either of these two formulas would
refute the corresponding proposition and theorem.

```sh
# Theorem 1, Table 1 rows 1 and 2.  About 9 minutes each.
.venv/bin/python artifacts/s5_all_z3.py   --timeout 900
.venv/bin/python artifacts/s5_all_cvc5.py --timeout 900

# Theorem 2, Table 1 rows 3 and 4.  About 15 minutes and about 1 hour.
.venv/bin/python artifacts/s6_all_z3.py   --m 8 --timeout 7200 \
    --arith-solver 2 --residual-disjoint-argmins
.venv/bin/python artifacts/s6_all_cvc5.py --m 8 --timeout 7200 \
    --residual-disjoint-argmins
```

Three details matter.

- `--residual-disjoint-argmins` is **not** on by default. Omitting it builds the
  unrestricted formula over the full m=8 class, which is a different formula
  and which timed out in several solver configurations. The residual formula is
  sufficient only because the shared-minimum lifting lemma of Section 4.1
  discharges its complement by hand.
- `--timeout` is a solver-internal soft limit, not a hard wall-clock guard. The
  reported UNSAT runs completed before their limits.
- The Z3 eight-chore script writes a candidate model only when `--model-out` is
  supplied. Such a candidate would still require separate certification, namely
  that both exhaustive checkers report no EFX allocation for it.

Both cvc5 scripts set `produce-proofs=true` and `check-proofs=true` by default,
so their reports carry `"proofs_checked_internally": true`. This is an internal
cvc5 proof check, not a certificate exported to an independent proof kernel. No
unsatisfiable core or Farkas combination is reported, and neither encoding is
formally verified.

## Claim-to-command map

| Paper | Command | Expected |
|---|---|---|
| Table 1, rows 1-2; Proposition 2 | `artifacts/s5_all_z3.py`, `artifacts/s5_all_cvc5.py` | `unsat` |
| Table 1, rows 3-4; Proposition 4 | `artifacts/s6_all_z3.py`, `artifacts/s6_all_cvc5.py` with `--m 8 --residual-disjoint-argmins` | `unsat` |
| Table 3, rows 1-2 (further Z3 strategies) | `s6_all_z3.py` with `--phase-selection 1`, or `--arith-solver 6` | `unsat` |
| Table 3, row 3 (cross-checking transcription) | `artifacts/s6_residual_referee.py --m 8 --timeout 7200` | `unsat` |
| Table 3, rows 4-6 (m=7 calibration) | the same three commands with `--m 7` | `unsat` |
| Table 3, rows 7-8 (SAT controls) | `s6_all_z3.py ... --variant ge-control`, `--variant ef-control` | `sat` |
| Section 5 and Appendix C.2, eight-chore finite checks | `artifacts/s6_audit.py` | `"result": "pass"` |
| Section 5, regression suite | `python -m pytest -q` | 117 passed, 2 skipped |
| Appendix D, Table 4 | `artifacts/s5_occupancy_check.py` | counts 64, 21, 8, 6 |
| Appendix F, verbatim formula construction | `artifacts/s5_all_z3.py`, `artifacts/s6_all_z3.py` | source matches the appendix |
| Table 2 and Appendix C.1, seven-chore corroborations | — | not archived, see below |

The exact invocation of every row, together with its recorded result and
timing, is in [`record/RUNS.md`](record/RUNS.md).

## Corroborating and control runs

`record/RUNS.md` lists them all. Two are worth naming here.

`artifacts/s6_residual_referee.py` is a separately written transcription of the
eight-chore residual: it drops row normalization, reverses the free-column
order, and retains the harmless `j=i` literals, giving 24 literal positions per
clause instead of 16. It takes only `--m` and `--timeout`, because those three
choices are fixed in the file rather than selected by a flag. It is another
encoding from this project, not an audit independent of the project.

`artifacts/s6_audit.py` compares both eight-chore clause builders against the
independent certifier in `verifier_b/` on 8 exact rational matrices and every
one of the 6561 allocations, and checks that the comparison rejects five
deliberate mutations: trimming the envied bundle as in goods EFX, skipping
zero-cost owned chores, making the boundary non-strict, evaluating the compared
bundle in the wrong row, and omitting the trim. It also exercises the zero-row
construction, row-scaling and chore-permutation invariance, the two
canonicalizations, and the shared-minimum lifting step on 30 exact instances.
Those 30 instances are empirical support for the implementation only; they are
not a proof of the cited insertion lemma. The harness takes under two minutes
and prints `"result": "pass"`.

## What is not in this artifact

Stated here rather than left to be discovered.

- **The seven-chore cross-checking encoder and its soundness harness.** The
  three corroborating rows of Table 2 and the finite checks of Appendix C.1 —
  the 54,675 matrix-allocation comparisons, the mutation battery and the
  polarity check — were run in files that were never committed. The paper
  reports them; this repository does not reproduce them. The later eight-chore
  campaign archives its counterparts, `s6_residual_referee.py` and
  `s6_audit.py`.
- **A checkable proof object.** cvc5's `check-proofs` is a self-check inside
  cvc5. Nothing here exports a proof to an independent kernel, and neither
  encoding is formally verified.
- **An independent audit.** Every encoding, harness and control in this
  repository was produced inside the same machine-assisted workflow as the
  primary generators. Appendix G of the paper discloses which component each
  tool produced and which checks remain undone.
- **Process material.** The development repository also held language-model
  prompts, adversarial review reports, superseded drafts and the cited PDFs.
  None of it is a premise of either theorem and none of it is here.

`spec/SPEC.md` and `record/SPEC_GAPS.md` are kept because `verifier_b/` was
reimplemented from the first of them and the regression suite reads the second.
Section 1 of `spec/SPEC.md` is the predicate contract that fixes Definition 1 of
the paper; its remaining sections specify a bounded integer-domain search that
is used by neither theorem. Cross-references inside those two documents point at
working files of the development repository that are not part of this artifact.

## Runtime budget

Timings from the recorded runs on a 14-core Darwin machine. They are
hardware-dependent and are not complexity claims.

| Step | Wall clock |
|---|---|
| Smoke test | under 1 minute |
| Theorem 1, both solvers | about 17 minutes |
| Theorem 2, Z3 | about 15 minutes |
| Theorem 2, cvc5 with proof checking | about 1 hour |
| Cross-checking transcription and audit | about 10 minutes |
| Everything above | about 2 hours |

## Citation

```bibtex
@misc{Zhang2026EFXChores,
  author        = {Xinkai Zhang},
  title         = {{EFX} Allocations for Three Agents and Seven or Eight Chores},
  year          = {2026},
  eprint        = {2609.10585},
  archivePrefix = {arXiv},
  primaryClass  = {cs.GT},
  url           = {https://arxiv.org/abs/2609.10585},
  note          = {Artifact: https://github.com/KaixxxZhang/Chores-EFX-n3m7or8}
}
```

## License

MIT, see [LICENSE](LICENSE).
