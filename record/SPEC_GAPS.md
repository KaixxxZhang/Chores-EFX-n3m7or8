# SPEC gaps found while building `verifier_b`

Written by the independent certifier. Scope: only what `verifier_b/` needed in
order to implement EFX for chores and goods from `SPEC.md`. One gap is open;
`verifier_b` refuses to guess it and requires the caller to choose.

## 1. Chores: no gap

Every question that arises while transcribing `SPEC.md` (1) is answered by
`SPEC.md` itself, so `verifier_b/efx_chores.py` has no free parameter.

| Question | `SPEC.md` answer | Where |
| --- | --- | --- |
| Which bundle is trimmed? | the envier's own `X_i` | §6 "Goods versus chores" |
| Empty own bundle? | explicit disjunct, vacuously EFX for that agent as envier | §1 after (1); checklist 9 |
| Must a nonempty agent compare against an empty bundle? | yes, at cost 0 | §6 "Empty bundles" |
| Zero-cost owned chores? | quantified, never skipped, no `c[i][g] > 0` guard | §1 after (1); §6 "Zeros"; checklist 8 |
| `j == i` conjuncts? | retained in (1), automatic for nonnegative costs | §1 after (1) |
| Which row evaluates both bundles? | the envier's row `i` | §6 "Perspective"; checklist 6 |
| Boundary? | equality is EFX; only strict `>` witnesses failure | §1 after (2); §6 "Boundary direction" |
| `m = 0`? | the unique all-empty allocation is EFX | §1 after (1) |
| Negative costs? | excluded by the `c_ig >= 0` conjunct of (2) | §1 (2) |

`verifier_b` rejects negative and `float` inputs rather than interpreting them:
(2) conjoins nonnegativity, and the omission of `j == i` literals in (6) is
justified only for nonnegative costs, so a negative matrix is out of spec, not
a hard case.

## 2. Goods, GAP-1 (open): are zero-valued goods trimmed?

`SPEC.md` states no goods predicate. Its only goods sentence is §6 "Goods
versus chores": *"goods remove a good from the envied `X_j`"*. That fixes the
trim direction and nothing else. The undecided question is which goods the
inner quantifier ranges over:

- **`trim="positive"` (classical EFX)** — quantify only `g in X_j` with
  `v_ig > 0`, i.e. `v_i(X_i) >= v_i(X_j \ {g})` for every positively valued
  `g`.
- **`trim="all"` (EFX0)** — quantify every `g in X_j`, zero-valued goods
  included.

The two predicates genuinely differ. With
`v = [[0, 5, 1], [3, 3, 1]]` and `X_1 = {0, 1}`, `X_0 = {2}`:
`trim="positive"` holds (only good 1 is trimmable for agent 0, and
`1 >= 5 - 5`), while `trim="all"` fails (trimming good 0 leaves
`5 > 1`).

Why the gap cannot be closed from the documents in this repo:

- §6 "EFX versus EFX0" says *"Ignore the label and implement (1): all owned
  chores are quantified."* That instruction is about **chores** — (1) is the
  chores predicate and its quantifier is over `X_i`, the envier's own bundle.
  Reading it as "quantify all goods too" is an extrapolation across the very
  distinction §6 opens by warning about.
- `KNOWN.md` line "n=4 additive goods EFX0 exists for m<=9 (AFM
  arXiv:2608.08590)" shows the goods work this repo cares about is stated for
  **EFX0**, i.e. `trim="all"`. That is evidence for one reading, not a
  specification of the checker's default.
- Nothing in `SPEC.md` §§1-5 or the checklist mentions goods at all, so there
  is no third place to break the tie.

### What `verifier_b` does instead of guessing

- `is_efx_goods(alloc, values, trim=...)` and
  `goods_violation(alloc, values, trim=...)` take a **required** keyword-only
  `trim`; omitting it raises `verifier_b.SpecGapError` pointing at this file.
- `exhaust(costs, "goods", goods_trim=...)` likewise.
- `python -m verifier_b.cli file.json --mode goods` fails with a nonzero exit
  status unless `--goods-trim {positive,all}` is supplied.
- The chores path has no such parameter, and `--goods-trim` with
  `--mode chores` is an error rather than a silently ignored flag.

### One line would close it

Add to `SPEC.md` §6, next to the goods/chores trim direction, e.g.: *"For
goods, quantify every `g in X_j` including `v_ig = 0` (EFX0)"*, or *"...only
`g` with `v_ig > 0` (EFX)"*. Until then a goods answer from `verifier_b` is
only meaningful together with its `trim` label, which is why the CLI prints
`mode = goods (trim=...)`.

## 3. Goods: derived, not guessed

These are consequences of the one fixed goods fact (trim the envied bundle)
plus the clauses of (1) that are not about direction. `verifier_b` implements
them without a parameter, and states the derivation here so that a referee can
reject the derivation instead of having to find it.

- **Empty envied bundle.** `X_j = empty` contributes no `g`, so the pair
  `(i, j)` has no literal. This is the exact mirror of the chores empty-bundle
  disjunct: in (1) the vacuity sits on the bundle being trimmed, and for goods
  the trimmed bundle is `X_j`. It is also the right answer on the merits, since
  `v_i(empty) = 0 <= v_i(X_i)` can never be envy.
- **Empty own bundle.** An agent with `X_i = empty` is *not* excused: it still
  requires `0 >= v_i(X_j \ {g})`. For chores the excused agent is the one whose
  bundle is trimmed (§6 "Empty bundles" insists the *other* agents still
  compare), and for goods that is `j`, not `i`.
- **Perspective, boundary, `j == i`.** §6 "Perspective" and "Boundary
  direction" are stated for the predicate in general, not for chores only: both
  sides use row `i`, equality is not envy, and the `j == i` case is retained
  and automatic for nonnegative values.

## 4. Not a gap, but recorded

`SPEC.md` fixes `n = 3` (checklist 1) while `KNOWN.md` and
`artifacts/hetao.json` need `n = 4` and `n = 5`. `verifier_b` therefore reads
`n` from the matrix and implements (1) for arbitrary `n`; for `n = 3` it is
exactly (1). Nothing in (1) depends on `n = 3`.
