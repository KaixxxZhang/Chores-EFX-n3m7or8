"""Independent cvc5 encoding of artifacts/s5_all_z3.py."""

from __future__ import annotations

import argparse
import json
import time
from itertools import product

import cvc5
from cvc5 import Kind

N = range(3)
M = range(7)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--timeout", type=int, default=3600)
    args = parser.parse_args()

    solver = cvc5.Solver()
    solver.setLogic("QF_LRA")
    solver.setOption("produce-proofs", "true")
    solver.setOption("check-proofs", "true")
    solver.setOption("tlimit-per", str(args.timeout * 1000))
    zero, one = solver.mkReal(0), solver.mkReal(1)

    def app(kind, terms, identity):
        terms = list(terms)
        if not terms:
            return identity
        if len(terms) == 1:
            return terms[0]
        return solver.mkTerm(kind, *terms)

    def z_or(terms):
        return app(Kind.OR, terms, solver.mkFalse())

    def z_and(terms):
        return app(Kind.AND, terms, solver.mkTrue())

    def z_sum(terms):
        return app(Kind.ADD, terms, zero)

    def eq(x, y):
        return solver.mkTerm(Kind.EQUAL, x, y)

    def lt(x, y):
        return solver.mkTerm(Kind.LT, x, y)

    def gt(x, y):
        return solver.mkTerm(Kind.GT, x, y)

    def ge(x, y):
        return solver.mkTerm(Kind.GEQ, x, y)

    def sub(x, y):
        return solver.mkTerm(Kind.SUB, x, y)

    def lex_le(left, right):
        prefix = []
        cases = []
        for x, y in zip(left, right):
            cases.append(z_and(prefix + [lt(x, y)]))
            prefix.append(eq(x, y))
        cases.append(z_and(prefix))
        return z_or(cases)

    def not_efx_clause(cost, allocation):
        bundles = [[g for g in M if allocation[g] == i] for i in N]
        violations = []
        for i in N:
            own = z_sum(cost[i][g] for g in bundles[i])
            for j in N:
                if i == j:
                    continue
                other = z_sum(cost[i][g] for g in bundles[j])
                for g in bundles[i]:
                    violations.append(gt(sub(own, cost[i][g]), other))
        return z_or(violations)

    started = time.perf_counter()
    real = solver.getRealSort()
    cost = [[solver.mkConst(real, f"c_{i}_{g}") for g in M] for i in N]

    for i in N:
        for g in M:
            solver.assertFormula(ge(cost[i][g], zero))
        solver.assertFormula(eq(z_sum(cost[i]), one))

    columns = [[cost[i][g] for i in N] for g in M]
    for g in range(6):
        solver.assertFormula(lex_le(columns[g], columns[g + 1]))

    for allocation in product(N, repeat=7):
        solver.assertFormula(not_efx_clause(cost, allocation))
    built = time.perf_counter()
    result = solver.checkSat()
    finished = time.perf_counter()

    print(
        json.dumps(
            {
                "solver": f"cvc5-{cvc5.__version__}",
                "logic": "QF_LRA",
                "scope": "all n=3,m=7 nonnegative matrices with positive row totals",
                "domain": "unbounded normalized nonnegative Reals",
                "allocations": 3**7,
                "result": str(result),
                "proofs_checked_internally": True,
                "build_s": round(built - started, 3),
                "check_s": round(finished - built, 3),
            },
            indent=2,
        )
    )
    return 0 if result.isUnsat() else 1


if __name__ == "__main__":
    raise SystemExit(main())
