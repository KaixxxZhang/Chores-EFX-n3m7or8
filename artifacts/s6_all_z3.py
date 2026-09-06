"""Exact QF_LRA frontier decision for all positive-row n=3 chore matrices.

The default instance is n=3, m=8.  ``--m 7`` is the known-UNSAT calibration
from ``artifacts/s5_all_z3.py``.  The script is intentionally self-contained:
it imports neither ``src`` nor ``verifier_b``.
"""

from __future__ import annotations

import argparse
import json
import time
from itertools import combinations, product
from pathlib import Path

import z3
from z3 import And, Or, Real, SolverFor, Sum

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


def z_or(terms):
    terms = list(terms)
    return Or(*terms) if terms else z3.BoolVal(False)


def lex_le(left, right):
    """Non-strict lexicographic order; the final case permits equality."""
    prefix = []
    cases = []
    for x, y in zip(left, right):
        cases.append(And(*(prefix + [x < y])))
        prefix.append(x == y)
    cases.append(And(*prefix))
    return Or(*cases)


def not_efx_clause(cost, allocation, *, variant: str = "efx"):
    """Return one fixed allocation's exact non-EFX clause (or a control)."""
    if variant not in VARIANTS:
        raise ValueError(f"unknown variant: {variant!r}")
    m = len(allocation)
    bundles = [[g for g in range(m) if allocation[g] == i] for i in N]
    violations = []
    for i in N:
        own = Sum([cost[i][g] for g in bundles[i]]) if bundles[i] else 0
        for j in N:
            if i == j:
                continue
            other = Sum([cost[i][g] for g in bundles[j]]) if bundles[j] else 0
            if variant == "ef-control":
                # Deliberately stronger fairness target: every allocation
                # must exhibit ordinary envy, with no chore removed.
                violations.append(own > other)
                continue
            for g in bundles[i]:  # includes zero-cost owned chores
                residual = own - cost[i][g]
                if variant == "ge-control":
                    # Deliberately wrong boundary, used only as a SAT control.
                    violations.append(residual >= other)
                else:
                    violations.append(residual > other)
    return z_or(violations)


def add_row_minmax_symmetry(solver, cost):
    """Sound optional agent symmetry from chore-permutation row invariants.

    After row normalization, independently permute agents so that
    ``(row minimum, row maximum)`` is nondecreasing.  A later chore
    permutation leaves these pairs unchanged, so this composes soundly with
    column sorting.
    """
    m = len(cost[0])
    minima = [Real(f"row_min_{i}") for i in N]
    maxima = [Real(f"row_max_{i}") for i in N]
    for i in N:
        solver.add(*(minima[i] <= cost[i][g] for g in range(m)))
        solver.add(z_or(minima[i] == cost[i][g] for g in range(m)))
        solver.add(*(maxima[i] >= cost[i][g] for g in range(m)))
        solver.add(z_or(maxima[i] == cost[i][g] for g in range(m)))
    for i in range(2):
        solver.add(lex_le([minima[i], maxima[i]], [minima[i + 1], maxima[i + 1]]))


def add_row_min_symmetry(solver, cost):
    """Sort agents by normalized row minimum with two direct LRA disjunctions."""

    def minimum_le(left, right):
        # min(left) <= min(right) iff some entry of left is <= every entry
        # of right.  This avoids auxiliary minimum variables.
        return z_or(And(*(x <= y for y in right)) for x in left)

    for i in range(2):
        solver.add(minimum_le(cost[i], cost[i + 1]))


def add_disjoint_argmin_residual(solver, cost):
    """Pin three distinct row minima and exclude every shared row minimum.

    The full-class reduction is mathematical: if a chore is weakly cheapest
    for two agents, delete it, apply the n=3,m=7 theorem, and reinsert it with
    Kobayashi--Mahara--Sakamoto Lemma 4.2.  A counterexample must therefore
    have pairwise-disjoint argmin sets.  After a chore permutation, one chosen
    minimum of row i can be pinned to chore i.
    """
    m = len(cost[0])
    if m < len(N):
        raise ValueError("disjoint-argmin residual requires at least three chores")
    for i in N:
        solver.add(*(cost[i][i] <= cost[i][g] for g in range(m)))
    for p, q in combinations(N, 2):
        for g in range(m):
            solver.add(
                Or(
                    z_or(cost[p][h] < cost[p][g] for h in range(m) if h != g),
                    z_or(cost[q][h] < cost[q][g] for h in range(m) if h != g),
                )
            )


def build_solver(
    *,
    m: int,
    timeout_s: int,
    variant: str,
    column_symmetry: bool,
    row_minmax_symmetry: bool,
    seed: int,
    allocation_prefix=(),
    row_min_symmetry: bool = False,
    arith_solver: int | None = None,
    phase_selection: int | None = None,
    residual_disjoint_argmins: bool = False,
):
    if m < 1:
        raise ValueError("m must be positive")
    if variant not in VARIANTS:
        raise ValueError(f"unknown variant: {variant!r}")

    solver = SolverFor("QF_LRA")
    solver.set("timeout", timeout_s * 1000)
    solver.set("random_seed", seed)
    if arith_solver is not None:
        solver.set("arith.solver", arith_solver)
    if phase_selection is not None:
        solver.set("phase_selection", phase_selection)
    cost = [[Real(f"c_{i}_{g}") for g in range(m)] for i in N]

    for i in N:
        solver.add(*(cost[i][g] >= 0 for g in range(m)))
        solver.add(Sum(cost[i]) == 1)

    if row_min_symmetry and row_minmax_symmetry:
        raise ValueError("choose at most one row symmetry mode")
    if residual_disjoint_argmins and (row_min_symmetry or row_minmax_symmetry):
        raise ValueError("row symmetry modes are not composed with the pinned residual")
    if row_minmax_symmetry:
        add_row_minmax_symmetry(solver, cost)
    elif row_min_symmetry:
        add_row_min_symmetry(solver, cost)

    if residual_disjoint_argmins:
        add_disjoint_argmin_residual(solver, cost)

    if column_symmetry:
        columns = [[cost[i][g] for i in N] for g in range(m)]
        first_interchangeable = len(N) if residual_disjoint_argmins else 0
        for g in range(first_interchangeable, m - 1):
            solver.add(lex_le(columns[g], columns[g + 1]))

    allocation_clauses = 0
    for allocation in ordered_allocations(m, allocation_prefix):
        solver.add(not_efx_clause(cost, allocation, variant=variant))
        allocation_clauses += 1
    return solver, cost, allocation_clauses


def write_model(path: Path, model, cost, *, m: int, variant: str) -> None:
    rows = [
        [str(model.eval(cost[i][g], model_completion=True)) for g in range(m)]
        for i in N
    ]
    payload = {
        "id": f"s6-z3-n3-m{m}-{variant}",
        "n": 3,
        "m": m,
        "mode": "chores",
        "purpose": (
            "candidate counterexample requiring independent certification"
            if variant == "efx"
            else f"SAT positive-control model ({variant}); not a counterexample claim"
        ),
        "costs": rows,
    }
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--m", type=int, default=8)
    parser.add_argument("--timeout", type=int, default=7200, help="soft solver timeout, seconds")
    parser.add_argument("--variant", choices=VARIANTS, default="efx")
    parser.add_argument("--no-column-symmetry", action="store_true")
    parser.add_argument("--row-min-symmetry", action="store_true")
    parser.add_argument("--row-minmax-symmetry", action="store_true")
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--arith-solver", type=int, choices=(2, 6))
    parser.add_argument("--phase-selection", type=int, choices=range(8))
    parser.add_argument("--residual-disjoint-argmins", action="store_true")
    parser.add_argument("--model-out", type=Path)
    parser.add_argument(
        "--allocation-order",
        type=Path,
        help="JSON allocation_order prefix; every remaining allocation is still added",
    )
    args = parser.parse_args()
    if args.row_min_symmetry and args.row_minmax_symmetry:
        parser.error("choose at most one row symmetry mode")
    if args.residual_disjoint_argmins and (
        args.row_min_symmetry or args.row_minmax_symmetry
    ):
        parser.error("row symmetry modes are not composed with the pinned residual")

    allocation_prefix = load_allocation_order(args.allocation_order, args.m)
    started = time.perf_counter()
    solver, cost, allocation_clauses = build_solver(
        m=args.m,
        timeout_s=args.timeout,
        variant=args.variant,
        column_symmetry=not args.no_column_symmetry,
        row_minmax_symmetry=args.row_minmax_symmetry,
        seed=args.seed,
        allocation_prefix=allocation_prefix,
        row_min_symmetry=args.row_min_symmetry,
        arith_solver=args.arith_solver,
        phase_selection=args.phase_selection,
        residual_disjoint_argmins=args.residual_disjoint_argmins,
    )
    built = time.perf_counter()
    result = solver.check()
    finished = time.perf_counter()

    model_path = None
    if result == z3.sat and args.model_out is not None:
        write_model(args.model_out, solver.model(), cost, m=args.m, variant=args.variant)
        model_path = str(args.model_out)

    print(
        json.dumps(
            {
                "solver": f"z3-{z3.get_version_string()}",
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
                "arith_solver": args.arith_solver or 6,
                "phase_selection": args.phase_selection if args.phase_selection is not None else 3,
                "allocations": 3**args.m,
                "allocation_clauses": allocation_clauses,
                "allocation_order_prefix": len(allocation_prefix),
                "literals_per_clause": 2 * args.m if args.variant != "ef-control" else 6,
                "assertions": len(solver.assertions()),
                "result": str(result),
                "reason_unknown": solver.reason_unknown() if result == z3.unknown else None,
                "model_out": model_path,
                "build_s": round(built - started, 3),
                "check_s": round(finished - built, 3),
            },
            indent=2,
        )
    )
    return 0 if result in (z3.sat, z3.unsat) else 2


if __name__ == "__main__":
    raise SystemExit(main())
