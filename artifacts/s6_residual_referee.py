"""Cross-checking referee encoding of the n=3,m=8 disjoint-argmin residual.

Unlike the two primary encodings, this transcription uses positive (not
unit-sum) rows, sorts the five free columns in descending order, and retains
the automatic j == i non-EFX literals.  It is written directly from SPEC.md
rather than importing another project module.  It is another encoding from
this project, not an independent third-party audit.
"""

from __future__ import annotations

import argparse
import json
import time
from itertools import combinations, product

import z3
from z3 import And, Or, Real, SolverFor, Sum

N = tuple(range(3))


def z_or(terms):
    terms = list(terms)
    return Or(*terms) if terms else z3.BoolVal(False)


def lex_ge(left, right):
    """Non-strict descending lexicographic order, including equality."""
    equal_prefix = []
    cases = []
    for x, y in zip(left, right):
        cases.append(And(*(equal_prefix + [x > y])))
        equal_prefix.append(x == y)
    cases.append(And(*equal_prefix))
    return Or(*cases)


def non_efx_clause(cost, allocation):
    """Negate chores EFX literally, retaining the harmless j == i cases."""
    m = len(allocation)
    bundles = [[g for g in range(m) if allocation[g] == i] for i in N]
    violations = []
    for i in N:
        own = Sum([cost[i][g] for g in bundles[i]]) if bundles[i] else 0
        for g in bundles[i]:
            for j in N:
                other = (
                    Sum([cost[i][h] for h in bundles[j]]) if bundles[j] else 0
                )
                violations.append(own - cost[i][g] > other)
    return z_or(violations)


def build_solver(*, m: int, timeout_s: int):
    if m < len(N):
        raise ValueError("the pinned residual requires at least three chores")
    solver = SolverFor("QF_LRA")
    solver.set("timeout", timeout_s * 1000)
    solver.set("arith.solver", 2)
    cost = [[Real(f"r_{i}_{g}") for g in range(m)] for i in N]

    for i in N:
        solver.add(*(cost[i][g] >= 0 for g in range(m)))
        solver.add(Sum(cost[i]) > 0)
        solver.add(*(cost[i][i] <= cost[i][g] for g in range(m)))

    for p, q in combinations(N, 2):
        for g in range(m):
            solver.add(
                Or(
                    z_or(cost[p][h] < cost[p][g] for h in range(m) if h != g),
                    z_or(cost[q][h] < cost[q][g] for h in range(m) if h != g),
                )
            )

    columns = [[cost[i][g] for i in N] for g in range(m)]
    for g in range(len(N), m - 1):
        solver.add(lex_ge(columns[g], columns[g + 1]))

    for allocation in product(N, repeat=m):
        solver.add(non_efx_clause(cost, allocation))
    return solver


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--m", type=int, default=8)
    parser.add_argument("--timeout", type=int, default=7200)
    args = parser.parse_args()

    started = time.perf_counter()
    solver = build_solver(m=args.m, timeout_s=args.timeout)
    built = time.perf_counter()
    result = solver.check()
    finished = time.perf_counter()
    print(
        json.dumps(
            {
                "solver": f"z3-{z3.get_version_string()}",
                "logic": "QF_LRA",
                "scope": f"n=3,m={args.m} pairwise-disjoint-argmin residual",
                "domain": "unbounded nonnegative Reals with positive row totals",
                "row_normalization": False,
                "free_column_order": "descending lexicographic",
                "self_comparison_literals": True,
                "allocations": 3**args.m,
                "allocation_clauses": 3**args.m,
                "literals_per_clause": 3 * args.m,
                "assertions": len(solver.assertions()),
                "result": str(result),
                "reason_unknown": solver.reason_unknown() if result == z3.unknown else None,
                "build_s": round(built - started, 3),
                "check_s": round(finished - built, 3),
            },
            indent=2,
        )
    )
    return 0 if result in (z3.sat, z3.unsat) else 2


if __name__ == "__main__":
    raise SystemExit(main())
