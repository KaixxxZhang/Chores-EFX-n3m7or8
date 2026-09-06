"""cvc5 QF_LRA transcription of the n=3, m=8 frontier decision.

This is a direct cvc5 transcription, not an import of the Z3 generator.
``--m 7`` provides the known-UNSAT calibration.  The default exact formula
quantifies all 3**8 complete allocations.  Solver diversity is not an
independent mathematical encoding.
"""

from __future__ import annotations

import argparse
import json
import time
from itertools import combinations, product
from pathlib import Path

import cvc5
from cvc5 import Kind

N = tuple(range(3))
VARIANTS = ("efx", "ge-control", "ef-control")


def load_allocation_order(path: Path | None, m: int) -> list[tuple[int, ...]]:
    if path is None:
        return []
    payload = json.loads(path.read_text(encoding="utf-8"))
    raw = payload.get("allocation_order") if isinstance(payload, dict) else payload
    if not isinstance(raw, list):
        raise ValueError("allocation-order JSON must be a list or contain allocation_order")
    out = []
    seen = set()
    for index, allocation in enumerate(raw):
        if (
            not isinstance(allocation, list)
            or len(allocation) != m
            or any(type(owner) is not int or owner not in N for owner in allocation)
        ):
            raise ValueError(f"invalid allocation_order[{index}]: {allocation!r}")
        item = tuple(allocation)
        if item in seen:
            raise ValueError(f"duplicate allocation_order[{index}]: {allocation!r}")
        seen.add(item)
        out.append(item)
    return out


def ordered_allocations(m: int, prefix):
    prefix = list(prefix)
    seen = set(prefix)
    yield from prefix
    yield from (allocation for allocation in product(N, repeat=m) if allocation not in seen)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--m", type=int, default=8)
    parser.add_argument("--timeout", type=int, default=7200, help="soft solver timeout, seconds")
    parser.add_argument("--variant", choices=VARIANTS, default="efx")
    parser.add_argument("--no-column-symmetry", action="store_true")
    parser.add_argument("--row-min-symmetry", action="store_true")
    parser.add_argument("--row-minmax-symmetry", action="store_true")
    parser.add_argument("--no-proof-check", action="store_true")
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--residual-disjoint-argmins", action="store_true")
    parser.add_argument(
        "--allocation-order",
        type=Path,
        help="JSON allocation_order prefix; every remaining allocation is still added",
    )
    args = parser.parse_args()
    if args.m < 1:
        parser.error("--m must be positive")
    if args.row_min_symmetry and args.row_minmax_symmetry:
        parser.error("choose at most one row symmetry mode")
    if args.residual_disjoint_argmins and (
        args.row_min_symmetry or args.row_minmax_symmetry
    ):
        parser.error("row symmetry modes are not composed with the pinned residual")

    allocation_prefix = load_allocation_order(args.allocation_order, args.m)
    solver = cvc5.Solver()
    solver.setLogic("QF_LRA")
    solver.setOption("produce-models", "true")
    if not args.no_proof_check:
        solver.setOption("produce-proofs", "true")
        solver.setOption("check-proofs", "true")
    solver.setOption("tlimit-per", str(args.timeout * 1000))
    solver.setOption("seed", str(args.seed))
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

    def le(x, y):
        return solver.mkTerm(Kind.LEQ, x, y)

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
        bundles = [[g for g in range(args.m) if allocation[g] == i] for i in N]
        violations = []
        for i in N:
            own = z_sum(cost[i][g] for g in bundles[i])
            for j in N:
                if i == j:
                    continue
                other = z_sum(cost[i][g] for g in bundles[j])
                if args.variant == "ef-control":
                    violations.append(gt(own, other))
                    continue
                for g in bundles[i]:  # includes zero-cost owned chores
                    residual = sub(own, cost[i][g])
                    if args.variant == "ge-control":
                        violations.append(ge(residual, other))
                    else:
                        violations.append(gt(residual, other))
        return z_or(violations)

    assertion_count = 0

    def assert_formula(term):
        nonlocal assertion_count
        solver.assertFormula(term)
        assertion_count += 1

    started = time.perf_counter()
    real = solver.getRealSort()
    cost = [
        [solver.mkConst(real, f"c_{i}_{g}") for g in range(args.m)]
        for i in N
    ]

    for i in N:
        for g in range(args.m):
            assert_formula(ge(cost[i][g], zero))
        assert_formula(eq(z_sum(cost[i]), one))

    if args.row_minmax_symmetry:
        minima = [solver.mkConst(real, f"row_min_{i}") for i in N]
        maxima = [solver.mkConst(real, f"row_max_{i}") for i in N]
        for i in N:
            for g in range(args.m):
                assert_formula(ge(cost[i][g], minima[i]))
            assert_formula(z_or(eq(minima[i], cost[i][g]) for g in range(args.m)))
            for g in range(args.m):
                assert_formula(ge(maxima[i], cost[i][g]))
            assert_formula(z_or(eq(maxima[i], cost[i][g]) for g in range(args.m)))
        for i in range(2):
            assert_formula(lex_le([minima[i], maxima[i]], [minima[i + 1], maxima[i + 1]]))
    elif args.row_min_symmetry:
        for i in range(2):
            assert_formula(
                z_or(
                    z_and(le(x, y) for y in cost[i + 1])
                    for x in cost[i]
                )
            )

    if args.residual_disjoint_argmins:
        if args.m < len(N):
            parser.error("--residual-disjoint-argmins requires at least three chores")
        for i in N:
            for g in range(args.m):
                assert_formula(le(cost[i][i], cost[i][g]))
        for p, q in combinations(N, 2):
            for g in range(args.m):
                assert_formula(
                    z_or(
                        (
                            z_or(
                                lt(cost[row][h], cost[row][g])
                                for h in range(args.m)
                                if h != g
                            )
                            for row in (p, q)
                        )
                    )
                )

    if not args.no_column_symmetry:
        columns = [[cost[i][g] for i in N] for g in range(args.m)]
        first_interchangeable = len(N) if args.residual_disjoint_argmins else 0
        for g in range(first_interchangeable, args.m - 1):
            assert_formula(lex_le(columns[g], columns[g + 1]))

    allocation_clauses = 0
    for allocation in ordered_allocations(args.m, allocation_prefix):
        assert_formula(not_efx_clause(cost, allocation))
        allocation_clauses += 1
    built = time.perf_counter()
    result = solver.checkSat()
    finished = time.perf_counter()

    print(
        json.dumps(
            {
                "solver": f"cvc5-{cvc5.__version__}",
                "logic": "QF_LRA",
                "scope": (
                    f"n=3,m={args.m} pairwise-disjoint-argmin residual"
                    if args.residual_disjoint_argmins
                    else f"all n=3,m={args.m} nonnegative matrices with positive row totals"
                ),
                "domain": "unbounded normalized nonnegative Reals",
                "variant": args.variant,
                "column_symmetry": not args.no_column_symmetry,
                "row_min_symmetry": args.row_min_symmetry,
                "row_minmax_symmetry": args.row_minmax_symmetry,
                "residual_disjoint_argmins": args.residual_disjoint_argmins,
                "allocations": 3**args.m,
                "allocation_clauses": allocation_clauses,
                "allocation_order_prefix": len(allocation_prefix),
                "literals_per_clause": 2 * args.m if args.variant != "ef-control" else 6,
                "assertions": assertion_count,
                "result": str(result),
                "proofs_checked_internally": not args.no_proof_check,
                "build_s": round(built - started, 3),
                "check_s": round(finished - built, 3),
            },
            indent=2,
        )
    )
    return 2 if result.isUnknown() else 0


if __name__ == "__main__":
    raise SystemExit(main())
