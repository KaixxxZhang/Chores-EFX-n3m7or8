## Grok handoff (8 lines)
1. Encode a bounded nonnegative additive \(3\times m\) cost matrix for which every complete allocation is non-EFX.
2. Start with \(m=7\), \(D=\{1,2,3\}\), and require some agent to use all three values; then increase \(m\) and/or use \(D=\{1,\ldots,5\}\).
3. Compile the universal allocation quantifier into one non-EFX disjunction for each of the \(3^m\) allocations.
4. A chores violation removes an owned chore from the envier: own cost minus that chore is strictly greater than another bundle's cost.
5. Quantify zero-cost owned chores too; an empty own bundle has no violation witness and is vacuously EFX for that agent.
6. Treat \(m\le6\), personalized bi-valued, and IDO/all-but-one-IDO instances as UNSAT soundness probes, not counterexample targets.
7. Break chore symmetry by lexicographic columns and agent symmetry by row histograms; the fixed domain supplies the scale normalization.
8. Reject every SAT matrix unless both the enumerator and `verifier_b` find no EFX allocation; bounded UNSAT has no unbounded implication.

# Encoding specification

## 1. Exact predicate

Let \(N=\{0,1,2\}\), \(M=\{0,\ldots,m-1\}\), and let
\(C=(c_{ig})_{i\in N,g\in M}\) have \(c_{ig}\in\mathbb Q_{\ge0}\).
Costs are additive:
\[
  c_i(S)=\sum_{g\in S}c_{ig},\qquad c_i(\varnothing)=0.
\]
An allocation is a total assignment \(a=(a_0,\ldots,a_{m-1})\in N^m\).
It induces disjoint bundles \(X_k(a)=\{g\in M:a_g=k\}\) whose union is
\(M\). Bundles may be empty; no chore may be unallocated or duplicated.

The exact \(n=3\) additive-chores EFX predicate is
\[
\operatorname{EFX}_3(C,a)\ \Longleftrightarrow\
\bigwedge_{i\in N}\left[
 X_i(a)=\varnothing\ \lor\
 \bigwedge_{g\in X_i(a)}\ \bigwedge_{j\in N}
 \left(
   \sum_{\substack{h:a_h=i\\h\ne g}}c_{ih}
   \le
   \sum_{h:a_h=j}c_{ih}
 \right)\right].
\tag{1}
\]
The explicit empty-bundle disjunct agrees with the enumerator and is also
the vacuous value of the inner conjunction. Both bundle costs in a
comparison use row \(i\). The quantifier over \(g\) includes \(c_{ig}=0\);
zero-cost chores are not skipped. The \(j=i\) conjuncts are retained in
(1), as in the enumerator, although they are automatic for nonnegative
costs. For \(m=0\), the unique all-empty allocation is EFX.

A cost matrix is a counterexample exactly when every complete allocation
fails (1):
\[
\begin{aligned}
\operatorname{CE}_m(C)
&\Longleftrightarrow
 \left(\bigwedge_{i,g}c_{ig}\ge0\right)
 \land \bigwedge_{a\in N^m}\neg\operatorname{EFX}_3(C,a)\\
&\Longleftrightarrow
 \left(\bigwedge_{i,g}c_{ig}\ge0\right)
 \land
 \bigwedge_{a\in N^m}
 \bigvee_{\substack{i,j\in N,\ g\in M\\a_g=i}}
 \left(
   \sum_{h:a_h=i}c_{ih}-c_{ig}
   >
   \sum_{h:a_h=j}c_{ih}
 \right).
\tag{2}
\end{aligned}
\]
Thus the bounded search statement is \(\exists(c_{ig})\in D^{3m}\,
\operatorname{CE}_m(C)\), plus only sound domain and symmetry constraints.
Equation (2) is first-order: both displayed conjunctions and disjunctions
are finite. Equality is EFX, so failure must use strict \(>\).

## 2. CLOSED CASES: soundness tests only

- **At most six chores.** For every bounded nonnegative domain \(D\) and
  every \(m\le6\), the \(n=3\) formula claiming a counterexample exists must
  be UNSAT. Run this only as a short probe of the core clauses, with
  tri-valued and non-IDO filters disabled. If it returns SAT, the decoded
  model plus the enumerator should expose an EFX allocation and therefore
  an encoding bug; if not, stop and investigate the trusted assumptions.
- **Personalized bi-valued costs.** If each agent's row uses at most two
  cost values (the two values may depend on the agent), the corresponding
  \(n=3\) counterexample formula must be UNSAT. Use this as a probe, never
  as a counterexample search domain.
- **IDO costs.** Define (weak / common-order) IDO by the existence of one
  permutation \(\pi\in S_m\) such that
  \(c_{i,\pi(0)}\le\cdots\le c_{i,\pi(m-1)}\) for every agent \(i\).
  Ties need not match. The IDO-constrained \(n=3\) counterexample formula
  must be UNSAT. A counterexample must fail (3) below. For \(n=3\),
  Theorem 4.1 as proved also closes every instance with a reversal-free
  pair, so a genuine counterexample must have a `Rev` for every pair.

For agents \(p,q\) and chores \(g,h\), define
\[
\operatorname{Rev}(p,q,g,h):=
(c_{pg}<c_{ph}\land c_{qg}>c_{qh})\ \lor\
(c_{pg}>c_{ph}\land c_{qg}<c_{qh}).
\]
This handles ties correctly. To justify the non-IDO blocker, let \(R\) be
the union of all agents' strict cost orders. A common order clearly forbids
`Rev`. Conversely, if there is no `Rev` and \(gRh\) via agent \(p\) while
\(hRk\) via agent \(q\), then \(p\) cannot rank \(k<h\); hence
\(c_{pg}<c_{ph}\le c_{pk}\), so \(gRk\). Thus \(R\) is transitive and
irreflexive, and any linear extension is a common nondecreasing order.
Therefore **not fully IDO** (no common nondecreasing order) is exactly
\[
 \bigvee_{p<q}\ \bigvee_{g<h}\operatorname{Rev}(p,q,g,h).
\tag{3}
\]
Kobayashi (arXiv:2305.04168) §4 *defines* a pair \((p,q)\) to be
identical-ordering (**Kobayashi-IDO**) iff for all chores \(e,e'\),
\[
(c_p(e)<c_p(e'))\ \Longleftrightarrow\ (c_q(e)<c_q(e')).
\]
Ties must agree. The PDF’s Algorithm 2 line 2 consumes only a common
non-increasing order (ties may disagree), and Lemma 4.2’s hypothesis is
already the pointwise inequality. Li–Li–Wu (WWW 2022) define IDO as that
sortable ranking. **Theorem 4.1 as proved** therefore closes every
instance in which some pair of the three agents is reversal-free.
Pairwise `Rev` is the correct necessary condition for an \(n=3\)
counterexample; it is not an over-restriction relative to the theorem
(`VERDICT2.md` §2.2). Two rows can still share a common weak order
(\(\neg\mathrm{Rev}\)) and fail the §4 biconditional on a strict-vs-tie.
That “G1 remainder” is **closed**, not open. Round-1 `VERDICT.md` G1’s
percentage figures measure that closed region.

Constraint (4) (every pair fails the biconditional) remains a *valid*
necessary condition, because a Kobayashi-IDO pair is reversal-free.
It is weaker than pairwise `Rev`, so a (4)-search is a superset of a
pairwise-`Rev` search and cannot drop a counterexample. G1-remainder
UNSAT is a soundness probe over a closed class, not new open coverage.
Write
\[
\operatorname{Dis}(p,q,e,e'):=
(c_p(e)<c_p(e'))\ \mathrm{XOR}\ (c_q(e)<c_q(e')).
\]
`XOR` is true on a strict-vs-tie disagreement and on a strict reversal
(evaluate both ordered pairs \((e,e')\) and \((e',e)\)). Then
\[
 \bigwedge_{p<q}\ \bigvee_{e\neq e'}\operatorname{Dis}(p,q,e,e').
\tag{4}
\]
Counterexample search should force pairwise `Rev`. Keep (4) as the
implemented XOR blocker; do not treat it as the boundary of the open class.

## 3. Bounded Z3 encoding

Use Z3 `Int` variables \(c_{ig}\). For finite \(D\), constrain each variable
with a disjunction of equalities, not merely `min(D) <= c <= max(D)` if
\(D\) has gaps.

The first search domain is:

- \(n=3\), \(m=7\), \(D=\{1,2,3\}\);
- \(\bigwedge_{i,g}(c_{ig}=1\lor c_{ig}=2\lor c_{ig}=3)\);
- at least one row uses all three values:
  \[
  \bigvee_{i\in N}\ \bigwedge_{v\in D}\ \bigvee_{g\in M}(c_{ig}=v);
  \tag{5}
  \]
- pairwise `Rev` for every agent pair, the CE filter justified by
  Theorem 4.1 as proved (a reversal-free pair is closed). Round-2 also
  ran (4) without pairwise `Rev`; those G1-remainder UNSATs are
  closed-class soundness probes (`VERDICT2.md` §2.2), not a claim that
  pairwise `Rev` over-restricts the open class.

Condition (5), rather than merely using all three values somewhere in the
matrix, excludes the personalized bi-valued closed class. After this run,
try \(m=8,9,\ldots\) with the same domain and/or
\(D=\{1,2,3,4,5\}\). In a wider domain, require that at least one row use
at least three distinct values; do not require all five values to occur.

Compile the universal quantifier in (2). For each constant allocation
\(a\in N^m\), precompute
\[
S_{i,k}^{a}=\sum_{g:a_g=k}c_{ig}
\]
and assert
\[
\operatorname{NotEFX}_a :=
\bigvee_{\substack{i\in N,\ g:a_g=i\\j\in N\setminus\{i\}}}
\left(S_{i,i}^{a}-c_{ig}>S_{i,j}^{a}\right).
\tag{6}
\]
Omitting \(j=i\) is exact because
\(S_{i,i}^{a}-c_{ig}\le S_{i,i}^{a}\) for \(c_{ig}\ge0\).
If \(X_i(a)\) is empty, it contributes no literal. If all candidate lists
are empty, the disjunction is `False`. Assert (6) for every one of the
\(3^m\) allocations. Do not introduce one existential assignment vector:
that would encode that some allocation fails EFX, not that all do.

Reference Z3Py structure:

```python
from itertools import combinations, product
from z3 import And, Int, IntVal, Or, Solver, Sum, Xor

N, M, D = range(3), range(m), tuple(domain)
c = [[Int(f"c_{i}_{g}") for g in M] for i in N]
s = Solver()
zsum = lambda xs: Sum(xs) if xs else IntVal(0)

for i in N:
    for g in M:
        s.add(Or(*(c[i][g] == v for v in D)))

uses = lambda i, v: Or(*(c[i][g] == v for g in M))
s.add(Or(*(And(*(uses(i, v) for v in (1, 2, 3))) for i in N)))

def rev(p, q, g, h):
    return Or(And(c[p][g] < c[p][h], c[q][g] > c[q][h]),
              And(c[p][g] > c[p][h], c[q][g] < c[q][h]))

def dis(p, q, e, ep):  # Kobayashi-IDO disagreement, including ties
    return Xor(c[p][e] < c[p][ep], c[q][e] < c[q][ep])

for p, q in combinations(N, 2):  # constraint (4), not pairwise Rev
    s.add(Or(*(dis(p, q, e, ep) for e in M for ep in M if e != ep)))

for a in product(N, repeat=m):
    total = [[zsum([c[i][g] for g in M if a[g] == k])
              for k in N] for i in N]
    bad = [total[i][i] - c[i][g] > total[i][j]
           for i in N for g in M if a[g] == i
           for j in N if j != i]
    s.add(Or(*bad) if bad else False)
```

The production implementation must add the symmetry constraints below.
Sharing `total` expressions or named subexpressions is an optimization only;
it must not change (6). A lazy variant may add allocation clauses found by
the enumerator, but it may report a counterexample only after exhaustive
independent validation finds no EFX allocation.

## 4. Symmetry

EFX is invariant under agent permutations and chore permutations. It is
also invariant under multiplying each agent's entire row by an independent
positive scalar. The first encoding uses a fixed finite integer domain, so
scaling generally leaves the domain and is not a model symmetry; add no
further scale constraint. If an unbounded positive rational encoding is
later used, normalize each nonzero row independently. If unbounded integers
are used, primitive-row (gcd \(=1\)) normalization is sound; `min = 1` is
not generally sound for integer rows.

Use these simultaneously sound, partial symmetry breaks:

1. For each row \(i\), form its domain histogram
   \(H_i=(|\{g:c_{ig}=v\}|)_{v\in D}\), and assert
   \(H_0\le_{\rm lex}H_1\le_{\rm lex}H_2\).
2. Form each column \(K_g=(c_{0g},c_{1g},c_{2g})\), and assert
   \(K_0\le_{\rm lex}\cdots\le_{\rm lex}K_{m-1}\).

These constraints cannot remove an orbit: first permute agents to sort the
histograms, which are chore-permutation invariant, then sort the resulting
columns. Histogram ties leave residual agent symmetry intentionally. Define
lexicographic comparison as the explicit disjunction of the first strict
coordinate or equality in every coordinate; do not rely on host-language
list comparison.

## 5. Implementer checklist (exactly 20 lines)

1. Fix `n = 3` and use zero-based agent and chore indices consistently with the enumerator.
2. Represent every bounded cost as a Z3 `Int` constrained by equality to a member of `D`.
3. Start with `m = 7`, `D = {1,2,3}`, before increasing `m` or widening `D`.
4. Require at least one agent row to contain three distinct values in every counterexample search.
5. Enumerate all `3**m` complete assignments; do not allow unallocated or duplicated chores.
6. Compute both compared bundle sums from the evaluating agent's row `i`.
7. Assert a strict `>` violation disjunction for every fixed allocation.
8. Quantify every owned chore, including chores with zero cost to the owner.
9. Give an empty own bundle no violation literal; it is vacuously EFX for that agent.
10. Omit `j == i` literals only while all costs are constrained nonnegative.
11. Add histogram agent ordering and lexicographic column ordering as the declared symmetry breaks.
12. Disable structural target filters when running broad `m <= 6` core-encoding probes.
13. Do not restrict the search to two cost values.
14. A SAT model with a reversal-free pair is not a counterexample (Thm 4.1 as proved). Pairwise Rev is the CE filter; (4) is a valid weaker blocker, not the open-class boundary (VERDICT2).
15. Do not search m≤6 for counterexamples except as a short unsoundness probe.
16. Run separate expected-UNSAT probes for `m <= 6`, personalized bi-valued, and IDO domains.
17. Decode SAT costs as exact integers and recheck all domain, value-use, and order constraints.
18. SAT model must be rejected if enumerator OR verifier_b finds any EFX allocation.
19. Treat Z3 `unknown`, timeout, verifier disagreement, or an enumerator cap as no result.
20. Report UNSAT only with its exact `m`, domain, and filters; never promote bounded UNSAT to general existence.

## 6. Encoding pitfalls

- **Goods versus chores:** chores remove \(g\) from the envier's own
  \(X_i\); goods remove a good from the envied \(X_j\). Swapping the trim
  direction certifies a different predicate.
- **Zeros:** this project checks every \(g\in X_i\), including
  \(c_{ig}=0\). Do not guard (1) or (6) with `c[i][g] > 0`.
- **Empty bundles:** empty is vacuous only for that empty-bundle agent as
  envier. A nonempty agent must still compare against the empty bundle,
  whose cost is zero.
- **EFX versus EFX0:** terminology around zero-marginal items varies.
  Ignore the label and implement (1): all owned chores are quantified.
- **Additive versus monotone:** every bundle expression here is a sum of
  singleton costs. The monotone/submodular result in arXiv:2604.18216 is
  not this problem and supplies neither a model nor a clause.
- **Quantifier polarity:** `exists costs; for every allocation; exists a
  violating (i,j,g)` is required. `exists costs, allocation` is unsound.
- **Boundary direction:** EFX uses `<=`; only `>` witnesses failure.
- **Perspective:** \(c_i(X_j)\), not \(c_j(X_j)\), appears when agent \(i\)
  compares bundles.

## Optional appendix: what an \(m=7\) existence proof would owe

1. It would have to cover every nonnegative additive \(3\times7\) matrix, including zero, non-bi-valued, and non-IDO rows.
2. It would have to produce or certify some complete three-bundle allocation satisfying (1) for all agents.
3. Kobayashi's \(m\le2n=6\) theorem does not supply that allocation after a seventh chore is present.
4. In particular, its matching invariant for the \(m\le6\) construction cannot simply be cited for a bundle that acquires the extra chore.
5. The missing argument must control all new EFX inequalities created by placing or rearranging that chore, including comparisons with empty bundles.
6. UNSAT over any finite cost domain would cover only that domain and would not by itself discharge the universal matrix claim.
7. No particular proof mechanism is prescribed here.
