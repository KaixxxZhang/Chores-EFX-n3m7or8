# Recorded runs

This is the run record behind the tables of *EFX Allocations for Three Agents
and Seven or Eight Chores*. Every status string and timing below reproduces the
record of the run that produced it. Timings are hardware-dependent and are not
complexity claims; they are here to identify the reported runs.

Section 1 holds the only two machine premises of the paper, the
unsatisfiability of `Phi_all`, the seven-chore all-allocation formula of
Section 3.2, and of `Phi_res`, the eight-chore residual formula of Section 4.2.
Everything else in this file is corroboration, calibration, or a control.

Each entry says whether it can be re-run from this repository. Two groups
cannot: the seven-chore cross-checking encoder and its soundness harness
(Sections 3 and 7.1) were written during verification in files that were never
committed, and the paper reports rather than archives them.

## 0. Environment

| | Original campaigns | September 2026 reruns |
|---|---|---|
| Machine | 14-core Darwin machine | Apple M4 Pro |
| OS | Darwin | macOS 26.6.2 |
| Python | CPython 3.13.3 | CPython 3.13.3 |
| Solvers | `z3-solver` 5.1.0.0 (reports Z3 5.1.0), `cvc5` 1.3.4 | same pins |

The pins are in [`../artifacts/requirements-pinned.txt`](../artifacts/requirements-pinned.txt).
Every decision uses exact rational arithmetic over unbounded SMT reals, so no
result depends on hardware or on floating point; the pins fix the solver search
strategy and therefore the timings. The `--timeout` values are solver-internal
soft limits, not hard wall-clock guards, and every UNSAT run below completed
before its limit.

## 1. Primary decisions

These four runs are Table 1 of the paper: `Phi_all` decides Theorem 1 and
`Phi_res` decides Theorem 2. Both cvc5 runs set `produce-proofs=true` and
`check-proofs=true`, which is an internal cvc5 proof check and not an exported
certificate.

| Formula | Theorem | Solver and strategy | Result | Build (s) | Check (s) |
|---|---|---|---|---:|---:|
| `Phi_all` | 1 | Z3 5.1.0 | `unsat` | 0.959 | 517.911 |
| `Phi_all` | 1 | cvc5 1.3.4, proof checking | `unsat` | 0.114 | 483.318 |
| `Phi_res` | 2 | Z3 5.1.0, `arith.solver=2`, `phase_selection=3` | `unsat` | 4.625 | 852.824 |
| `Phi_res` | 2 | cvc5 1.3.4, proof checking | `unsat` | 0.521 | 3729.851 |

```sh
python artifacts/s5_all_z3.py   --timeout 900
python artifacts/s5_all_cvc5.py --timeout 900
python artifacts/s6_all_z3.py   --m 8 --timeout 7200 --arith-solver 2 \
    --residual-disjoint-argmins
python artifacts/s6_all_cvc5.py --m 8 --timeout 7200 \
    --residual-disjoint-argmins
```

`arith.solver=2` with `phase_selection=3` is the default of `s6_all_z3.py` once
`--arith-solver 2` is given, so the third row needs no phase flag. Omitting
`--residual-disjoint-argmins` runs the full class at m=8 rather than the
residual formula of Theorem 2, which is not the same decision and which timed
out (Section 5).

## 2. The two `Phi_all` dumps

The campaign record dumps of the two runs in the first two rows of Section 1
carry check times that differ from the campaign summary that the paper's Table 1
reproduces. Both dumps report `unsat` on the same formula. Appendix B of the
paper records the discrepancy; where the two disagree, the paper's table
governs.

```text
$ python artifacts/s5_all_z3.py --timeout 900
solver: z3-5.1.0
logic: QF_LRA
scope: all n=3,m=7 nonnegative matrices with positive row totals
domain: unbounded normalized nonnegative Reals
allocations: 2187
result: unsat
build_s: 0.942
check_s: 515.499

$ python artifacts/s5_all_cvc5.py --timeout 900
solver: cvc5-1.3.4
logic: QF_LRA
scope: all n=3,m=7 nonnegative matrices with positive row totals
domain: unbounded normalized nonnegative Reals
allocations: 2187
result: unsat
proofs_checked_internally: true
build_s: 0.113
check_s: 475.351
```

## 3. Corroborating seven-chore runs — not re-runnable here

Table 2 of the paper. All three used the seven-chore cross-checking encoder,
which was written directly from the EFX predicate, retained the harmless `j=i`
literals, and was never committed. **No script in this repository reproduces
these three rows.**

| Run | Matrix constraints | Solver, result | Check (s) |
|---|---|---|---:|
| `posrows` | `c >= 0`, every row sum `> 0`, ascending column lex | Z3 5.1.0, `unsat` | 149.2 |
| `sort-desc` | `c >= 0`, every row sum `= 1`, descending column lex | Z3 5.1.0, `unsat` | 521.7 |
| m=6 calibration | `c >= 0` only, no normalization or column ordering | Z3 5.1.0, `unsat` | 484.2 |

`posrows` is logically the strongest of the three: its matrix constraints are
implied by those of `Phi_all` and its clauses are weaker, so every model of
`Phi_all` is a model of it, and that decision already entails the
unsatisfiability of `Phi_all`. It is reported rather than treated as primary
because the encoder is not part of this archive.

## 4. Eight-chore runs beyond Table 1

Table 3 of the paper. The three `Phi_res` rows are the same formula under a
different Z3 strategy or a different transcription. The residual m=7 rows are
known-true calibration of these generators, not evidence for Theorem 2. The two
m=8 controls show that the residual harness can still return `sat` when the
boundary or the target predicate is changed.

| Run | Result | Build (s) | Check (s) |
|---|---|---:|---:|
| `Phi_res`, primary Z3, `arith.solver=2`, `phase_selection=1` | `unsat` | 4.561 | 850.863 |
| `Phi_res`, primary Z3, `arith.solver=6` | `unsat` | 4.502 | 2717.209 |
| `Phi_res`, cross-checking Z3: positive unnormalized rows, descending free columns, `j=i` retained | `unsat` | 9.155 | 469.389 |
| Residual m=7, Z3 `arith.solver=2` | `unsat` | — | 17.952 |
| Residual m=7, cvc5 with internal proof checking | `unsat` | — | 44.497 |
| Residual m=7, cross-checking transcription | `unsat` | — | 4.725 |
| Residual m=8, strict `>` replaced by `>=` | `sat` | — | 79.500 |
| Residual m=8, trim removed, encoding envy-freeness | `sat` | — | 12.036 |

```sh
# same residual formula, two further Z3 strategies
python artifacts/s6_all_z3.py --m 8 --timeout 7200 --arith-solver 2 \
    --phase-selection 1 --residual-disjoint-argmins
python artifacts/s6_all_z3.py --m 8 --timeout 7200 --arith-solver 6 \
    --residual-disjoint-argmins

# cross-checking transcription; it takes only --m and --timeout, because its
# positive unnormalized rows, descending free-column order and retained j=i
# literals are fixed in the file rather than selected by a flag
python artifacts/s6_residual_referee.py --m 8 --timeout 7200

# known-true residual calibration at m=7
python artifacts/s6_all_z3.py   --m 7 --timeout 7200 --arith-solver 2 \
    --residual-disjoint-argmins
python artifacts/s6_all_cvc5.py --m 7 --timeout 7200 \
    --residual-disjoint-argmins
python artifacts/s6_residual_referee.py --m 7 --timeout 7200

# the two SAT controls at m=8
python artifacts/s6_all_z3.py --m 8 --timeout 7200 --arith-solver 2 \
    --residual-disjoint-argmins --variant ge-control
python artifacts/s6_all_z3.py --m 8 --timeout 7200 --arith-solver 2 \
    --residual-disjoint-argmins --variant ef-control
```

## 5. Inconclusive runs

An `unknown`, a timeout, or an error is no result: it neither confirms nor
refutes anything. These runs are recorded because they are the reason the paper
asserts the canonical constraints that it does.

| Run | Outcome |
|---|---|
| `Phi_all` without column sorting, Z3 | stopped after 4 h 19 min, no result |
| m=7 with only `c >= 0`, Z3 and cvc5 | `unknown` after 3600 s in both |
| unrestricted 6561-clause m=8 formula | timed out in several solver configurations |

The first two say that column sorting, licensed by the column-canonicalization
lemma, is what makes the seven-chore decision terminate; row normalization is a
convenience, as the `posrows` run of Section 3 shows. The third is why the
shared-minimum lifting lemma is load-bearing for Theorem 2 rather than a
convenience.

## 6. Structural counts

| | m=7 primary (`Phi_all`) | m=8 residual (`Phi_res`) | m=8 cross-checking |
|---|---:|---:|---:|
| Real-sorted cost variables | 21 | 24 | 24 |
| Allocation clauses | 2187 | 6561 | 6561 |
| Literal positions per clause | 14 | 16 | 24 |
| Top-level assertions | 2217 | 6640 | 6640 |

The 2217 assertions of `Phi_all` are 21 nonnegativity assertions, three row
equations, six adjacent column-order assertions, and the 2187 allocation
clauses. The cross-checking encoder has 24 literal positions per clause because
it retains the `j=i` comparisons, which are automatic under nonnegativity. For
the three m=7 assignments that give all seven chores to one agent, the clause
still has 14 literal positions but only seven distinct inequalities, because
both other bundles are empty.

## 7. Finite exact checks

### 7.1 Seven chores — not re-runnable here

The seven-chore soundness harness was reported but never committed, so **no
script in this repository reproduces this subsection.**

- Predicate equivalence: both primary clause builders were compared with a
  separate literal transcription of the EFX predicate on 25 exact rational
  matrices and all 2187 allocations each, that is 54,675 matrix-allocation
  pairs, with zero disagreements. The matrices included all-zero and partially
  zero rows, ties, exact fractions, uniform rows, and stored low-EFX-count
  witnesses.
- Mutation testing: the comparison rejects trimming the envied bundle as in
  goods EFX, skipping zero-cost owned chores, making the boundary non-strict,
  evaluating the compared bundle in the wrong row, and omitting the trim.
- Polarity: on a stored matrix with exactly six EFX allocations, the
  2187-clause formula is unsatisfiable; dropping exactly the six clauses of its
  EFX allocations makes it satisfiable, and dropping only one of the six leaves
  five false clauses and remains unsatisfiable.
- Lexicographic order: forcing all seven columns equal is satisfiable under the
  ordering constraints, and conjoining equality with the negation of
  lexicographic order is unsatisfiable, so duplicate chores are not discarded.
- Clause-set invariance: the identity `Bad_a(C . pi) = Bad_{a . pi^-1}(C)` was
  checked for syntactic identity on all 2187 allocations and each of the six
  adjacent transpositions, which generate the full chore symmetric group.
- Positive controls: `sat` in 0.912 s with `>` replaced by `>=`, and in
  0.766 s with the trim removed.
- No individual clause was unsatisfiable under the matrix constraints, and
  those constraints alone were satisfiable, so the unsatisfiability does not
  come from a single dead clause.

### 7.2 Eight chores

`python artifacts/s6_audit.py` reproduces this subsection. It compares the
primary 16-position Z3 clause builder and the cross-checking 24-position builder
against the separate literal verifier in `verifier_b/`, and reports:

- 8 exact rational matrices times 6561 allocations, that is 52,488
  matrix-allocation pairs, with zero disagreements for either builder;
- all five deliberate mutations detected;
- 3360 matrix/allocation checks of the eight-chore zero-row construction;
- 78,732 allocation comparisons under independent row scaling and 78,732 under
  chore permutation;
- 1000 ordinary and 1000 residual canonical representatives constructed,
  including tied instances with pairwise-disjoint argmin sets;
- 30 exact shared-minimum instances for which a seven-chore EFX partition and a
  matching-preserving reinsertion were found.

The harness did not programmatically exercise the cvc5 builder. The 30
shared-minimum instances are empirical support for the implementation only.
They are not a proof of the cited insertion lemma or of the shared-minimum
lifting lemma, whose justification is the cited Lemma 4.2 together with
Observations 2.2 and 2.3.

## 8. Occupancy census

`python artifacts/s5_occupancy_check.py` walks all 2187 allocations of each of
the four matrices in [`../artifacts/s5_matrices.json`](../artifacts/s5_matrices.json)
and reproduces Table 4 of the paper.

| Identifier | Sole sorted occupancy | EFX allocations out of 2187 |
|---|---|---:|
| `s5-only-322` | (3,2,2) | 64 |
| `s5-only-331` | (3,3,1) | 21 |
| `s5-only-421` | (4,2,1) | 8 |
| `s5-only-511` | (5,1,1) | 6 |

The census was cross-checked by three exhaustive walks inside the same
campaign: the self-contained checker above, the separate verifier in
`verifier_b/`, and a third enumerator that is not archived here. No walk was
carried out independently of that campaign. Appendix D of the paper is used in
the proof of neither theorem.

## 9. Regression suite

`python -m pytest -q` was recorded as 117 passed and 2 skipped. That result and
the finite audit of Section 7.2 are software checks, not premises of either
theorem.

## 10. September 2026 reruns

The four decisions of Section 1 were re-run in September 2026 on the second
environment of Section 0, at the same pinned solver versions. All four returned
`unsat` again, both cvc5 runs again checking their proofs internally, and the
residual formula again reported 6640 assertions.

| Formula | Solver | Result | Check (s), original | Check (s), rerun |
|---|---|---|---:|---:|
| `Phi_all` | Z3 5.1.0 | `unsat` | 517.911 | 485.669 |
| `Phi_all` | cvc5 1.3.4 | `unsat` | 483.318 | 399.756 |
| `Phi_res` | Z3 5.1.0 | `unsat` | 852.824 | 606.183 |
| `Phi_res` | cvc5 1.3.4 | `unsat` | 3729.851 | 3156.109 |

The same four configurations, uniformly faster on newer hardware. Table 1 of
the paper still reports the original runs. These reruns execute the archived
scripts, so they confirm the recorded verdicts and the pinned environment
rather than adding an independent encoding. The corroborating and control runs
of Sections 3 and 4 have not been repeated.
