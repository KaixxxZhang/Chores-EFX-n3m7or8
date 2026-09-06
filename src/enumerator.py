"""Exhaustive additive EFX existence for goods and chores.

Trusted path uses nonnegative exact rationals only (fractions.Fraction).
Floats are rejected. Empty bundles are allowed.

Goods EFX (trim the envied bundle; skip zero-value items for the envier):
    for all i ≠ j and every g in A_j with v_i(g) > 0:
        v_i(A_i) >= v_i(A_j) - v_i(g)

Chores EFX (trim the envier's bundle; empty own-bundle is vacuously EFX):
    for all i, j: either X_i is empty, or for every g in X_i:
        c_i(X_i \\ {g}) <= c_i(X_j)

When items have identical columns, occupancy-count enumeration is equivalent
to n^m assignment enumeration for additive valuations. Cap applies to the
number of distinct occupancy (or assignment) cells actually walked.
"""

from __future__ import annotations

from collections import OrderedDict
from fractions import Fraction
from itertools import product
from math import comb
from typing import Iterable, Literal, Sequence

MAX_ALLOCS = 3_000_000

Value = Fraction
Matrix = tuple[tuple[Value, ...], ...]
Assignment = tuple[int, ...]
Mode = Literal["goods", "chores"]


def parse_scalar(x: object) -> Fraction:
    if isinstance(x, bool):
        raise TypeError("bool is not allowed on the trusted path")
    if isinstance(x, float):
        raise TypeError("floats are not allowed on the trusted path")
    if isinstance(x, Fraction):
        val = x
    elif isinstance(x, int):
        val = Fraction(x)
    elif isinstance(x, str):
        s = x.strip()
        if not s:
            raise ValueError("empty scalar")
        if "/" in s[1:]:
            num, den = s.split("/", 1)
            val = Fraction(int(num), int(den))
        else:
            val = Fraction(int(s))
    else:
        raise TypeError(f"unsupported scalar type: {type(x)!r}")
    if val < 0:
        raise ValueError(f"negative value not allowed: {val}")
    return val


def parse_matrix(raw: Sequence[Sequence[object]]) -> Matrix:
    if not raw:
        raise ValueError("matrix must have at least one agent")
    rows = []
    width = None
    for row in raw:
        parsed = tuple(parse_scalar(x) for x in row)
        if width is None:
            width = len(parsed)
        elif len(parsed) != width:
            raise ValueError("ragged cost/value matrix")
        rows.append(parsed)
    if width is None:
        raise ValueError("empty matrix")
    return tuple(rows)


def _n_m(matrix: Matrix) -> tuple[int, int]:
    n = len(matrix)
    m = len(matrix[0]) if n else 0
    return n, m


def _column_groups(matrix: Matrix) -> list[tuple[tuple[Value, ...], tuple[int, ...]]]:
    """Group item indices whose columns are identical."""
    n, m = _n_m(matrix)
    buckets: OrderedDict[tuple[Value, ...], list[int]] = OrderedDict()
    for g in range(m):
        col = tuple(matrix[i][g] for i in range(n))
        buckets.setdefault(col, []).append(g)
    return [(col, tuple(idxs)) for col, idxs in buckets.items()]


def _agent_occupancies(n_agents: int, n_items: int) -> list[tuple[int, ...]]:
    """Nonnegative integer n_agents-tuples summing to n_items."""
    out: list[tuple[int, ...]] = []

    def rec(prefix: tuple[int, ...], agents_left: int, items_left: int) -> None:
        if agents_left == 1:
            out.append(prefix + (items_left,))
            return
        for k in range(items_left + 1):
            rec(prefix + (k,), agents_left - 1, items_left - k)

    rec((), n_agents, n_items)
    return out


def _grouped_cell_count(n: int, group_sizes: Sequence[int]) -> int:
    total = 1
    for s in group_sizes:
        total *= comb(s + n - 1, n - 1)
        if total > MAX_ALLOCS:
            return total
    return total


def _bundles(assignment: Sequence[int], n: int) -> list[list[int]]:
    bundles: list[list[int]] = [[] for _ in range(n)]
    for g, owner in enumerate(assignment):
        if owner < 0 or owner >= n:
            raise ValueError(f"owner {owner} out of range for n={n}")
        bundles[owner].append(g)
    return bundles


def _is_efx_goods_parsed(assignment: Sequence[int], matrix: Matrix) -> bool:
    n, m = _n_m(matrix)
    if len(assignment) != m:
        raise ValueError("assignment length must equal m")
    bundles = _bundles(assignment, n)
    own = [
        sum((matrix[i][g] for g in bundles[i]), Fraction(0)) for i in range(n)
    ]
    for i in range(n):
        row = matrix[i]
        for j in range(n):
            if i == j:
                continue
            other = sum((row[g] for g in bundles[j]), Fraction(0))
            for g in bundles[j]:
                if row[g] > 0 and own[i] < other - row[g]:
                    return False
    return True


def _is_efx_chores_parsed(assignment: Sequence[int], matrix: Matrix) -> bool:
    n, m = _n_m(matrix)
    if len(assignment) != m:
        raise ValueError("assignment length must equal m")
    bundles = _bundles(assignment, n)
    own = [
        sum((matrix[i][g] for g in bundles[i]), Fraction(0)) for i in range(n)
    ]
    for i in range(n):
        xi = bundles[i]
        if not xi:
            continue
        row = matrix[i]
        for j in range(n):
            other = sum((row[g] for g in bundles[j]), Fraction(0))
            for g in xi:
                if own[i] - row[g] > other:
                    return False
    return True


def is_efx_goods(assignment: Sequence[int], values: Sequence[Sequence[object]]) -> bool:
    return _is_efx_goods_parsed(assignment, parse_matrix(values))


def is_efx_chores(assignment: Sequence[int], costs: Sequence[Sequence[object]]) -> bool:
    return _is_efx_chores_parsed(assignment, parse_matrix(costs))


def _chores_efx_from_occupancy(
    occupancies: tuple[tuple[int, ...], ...],
    type_costs_i: tuple[tuple[Value, ...], ...],
) -> bool:
    """occupancies[t][a] = how many type-t items agent a gets.
    type_costs_i[i][t] = cost of one type-t item to agent i.
    Additive: checking the cheapest own chore is equivalent to checking every g.
    """
    n_types = len(occupancies)
    n = len(occupancies[0])
    for i in range(n):
        total_items = 0
        own = Fraction(0)
        min_item: Value | None = None
        row = type_costs_i[i]
        for t in range(n_types):
            k = occupancies[t][i]
            if k:
                total_items += k
                own += row[t] * k
                if min_item is None or row[t] < min_item:
                    min_item = row[t]
        if total_items == 0:
            continue
        assert min_item is not None
        remaining = own - min_item
        for j in range(n):
            if i == j:
                continue
            other = Fraction(0)
            for t in range(n_types):
                other += row[t] * occupancies[t][j]
            if remaining > other:
                return False
    return True


def _goods_efx_from_occupancy(
    occupancies: tuple[tuple[int, ...], ...],
    type_vals_i: tuple[tuple[Value, ...], ...],
) -> bool:
    n_types = len(occupancies)
    n = len(occupancies[0])
    for i in range(n):
        row = type_vals_i[i]
        own = Fraction(0)
        for t in range(n_types):
            own += row[t] * occupancies[t][i]
        for j in range(n):
            if i == j:
                continue
            other = Fraction(0)
            present: list[int] = []
            for t in range(n_types):
                k = occupancies[t][j]
                if k:
                    other += row[t] * k
                    present.append(t)
            for t in present:
                vg = row[t]
                if vg > 0 and own < other - vg:
                    return False
    return True


def _reconstruct(
    occupancies: tuple[tuple[int, ...], ...],
    groups: list[tuple[tuple[Value, ...], tuple[int, ...]]],
    m: int,
) -> Assignment:
    assign = [0] * m
    for t, (_, idxs) in enumerate(groups):
        p = 0
        for agent, k in enumerate(occupancies[t]):
            for _ in range(k):
                assign[idxs[p]] = agent
                p += 1
    return tuple(assign)


def _exists(
    matrix: Matrix,
    mode: Mode,
    max_allocs: int,
    want_assignment: bool,
) -> Assignment | bool | None:
    n, m = _n_m(matrix)
    if n <= 0:
        raise ValueError("n must be positive")
    raw = n**m if m else 1
    groups = _column_groups(matrix)
    sizes = [len(idxs) for _, idxs in groups]
    grouped = _grouped_cell_count(n, sizes)
    use_grouped = grouped < raw
    cells = grouped if use_grouped else raw
    if cells > max_allocs:
        raise ValueError(
            f"allocation space {cells} exceeds max_allocs={max_allocs} "
            f"(n={n} m={m} raw={raw} grouped={grouped})"
        )

    if not use_grouped:
        pred = _is_efx_chores_parsed if mode == "chores" else _is_efx_goods_parsed
        for assignment in product(range(n), repeat=m):
            if pred(assignment, matrix):
                return assignment if want_assignment else True
        return None if want_assignment else False

    occup_tables = [_agent_occupancies(n, len(idxs)) for _, idxs in groups]
    type_by_agent: tuple[tuple[Value, ...], ...] = tuple(
        tuple(col[i] for col, _ in groups) for i in range(n)
    )
    check = (
        _chores_efx_from_occupancy
        if mode == "chores"
        else _goods_efx_from_occupancy
    )
    for combo in product(*occup_tables):
        if check(combo, type_by_agent):
            if want_assignment:
                return _reconstruct(combo, groups, m)
            return True
    return None if want_assignment else False


def find_efx_chores(
    costs: Sequence[Sequence[object]],
    *,
    max_allocs: int = MAX_ALLOCS,
) -> Assignment | None:
    return _exists(parse_matrix(costs), "chores", max_allocs, True)  # type: ignore[return-value]


def find_efx_goods(
    values: Sequence[Sequence[object]],
    *,
    max_allocs: int = MAX_ALLOCS,
) -> Assignment | None:
    return _exists(parse_matrix(values), "goods", max_allocs, True)  # type: ignore[return-value]


def exists_efx_chores(
    costs: Sequence[Sequence[object]],
    *,
    max_allocs: int = MAX_ALLOCS,
) -> bool:
    found = _exists(parse_matrix(costs), "chores", max_allocs, False)
    return bool(found)


def exists_efx_goods(
    values: Sequence[Sequence[object]],
    *,
    max_allocs: int = MAX_ALLOCS,
) -> bool:
    found = _exists(parse_matrix(values), "goods", max_allocs, False)
    return bool(found)


def iter_assignments(n: int, m: int) -> Iterable[Assignment]:
    if n**m > MAX_ALLOCS:
        raise ValueError(f"n^m = {n**m} exceeds {MAX_ALLOCS}")
    return product(range(n), repeat=m)
