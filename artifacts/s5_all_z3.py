"""Exact QF_LRA decision for all positive-row n=3, m=7 chore matrices."""

from __future__ import annotations

import argparse
import json
import time
from itertools import product

import z3
from z3 import And, Or, Real, SolverFor, Sum

N = range(3)
M = range(7)


def z_or(terms):
    terms = list(terms)
    return Or(*terms) if terms else z3.BoolVal(False)


def lex_le(left, right):
    prefix = []
    cases = []
    for x, y in zip(left, right):
        cases.append(And(*(prefix + [x < y])))
        prefix.append(x == y)
    cases.append(And(*prefix))
    return Or(*cases)


def not_efx_clause(cost, allocation):
    bundles = [[g for g in M if allocation[g] == i] for i in N]
    violations = []
    for i in N:
        own = Sum([cost[i][g] for g in bundles[i]]) if bundles[i] else 0
        for j in N:
            if i == j:
                continue
            other = Sum([cost[i][g] for g in bundles[j]]) if bundles[j] else 0
            for g in bundles[i]:  # includes zero-cost owned chores
                violations.append(own - cost[i][g] > other)
    return z_or(violations)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--timeout", type=int, default=3600)
    args = parser.parse_args()

    started = time.perf_counter()
    solver = SolverFor("QF_LRA")
    solver.set("timeout", args.timeout * 1000)
    cost = [[Real(f"c_{i}_{g}") for g in M] for i in N]

    for i in N:
        solver.add(*(cost[i][g] >= 0 for g in M))
        solver.add(Sum(cost[i]) == 1)

    # WLOG sort all seven normalized cost columns.
    columns = [[cost[i][g] for i in N] for g in M]
    for g in range(6):
        solver.add(lex_le(columns[g], columns[g + 1]))

    for allocation in product(N, repeat=7):
        solver.add(not_efx_clause(cost, allocation))
    built = time.perf_counter()
    result = solver.check()
    finished = time.perf_counter()

    print(
        json.dumps(
            {
                "solver": f"z3-{z3.get_version_string()}",
                "logic": "QF_LRA",
                "scope": "all n=3,m=7 nonnegative matrices with positive row totals",
                "domain": "unbounded normalized nonnegative Reals",
                "allocations": 3**7,
                "result": str(result),
                "build_s": round(built - started, 3),
                "check_s": round(finished - built, 3),
            },
            indent=2,
        )
    )
    return 0 if result == z3.unsat else 1


if __name__ == "__main__":
    raise SystemExit(main())
