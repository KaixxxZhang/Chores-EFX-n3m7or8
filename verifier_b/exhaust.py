"""Exhaustive EFX counting over all ``n**m`` allocations.

``SPEC.md`` §1 quantifies over every ``a in N**m``; a certifier may therefore
never sample. Enumerating ``n**m`` tuples literally is hopeless for the stored
He-Tao instances (``4**13`` and ``5**18``), so this module enumerates *classes*
of allocations and multiplies each class by the exact number of raw allocations
it contains. Two class collapses are used, both exact:

1. **Identical columns.** If chores ``g`` and ``h`` have the same column
   ``(c_0g, ..., c_{n-1}g) == (c_0h, ..., c_{n-1}h)``, swapping them maps
   allocations to allocations and changes no sum in (1). So an allocation is
   determined, up to EFX status, by an occupancy matrix ``O[k][t]`` = how many
   chores of column type ``t`` agent ``k`` receives. One occupancy matrix
   stands for ``prod_t multinomial(k_t; O[0][t], ..., O[n-1][t])`` raw
   allocations.
2. **Identical rows.** If agents ``p`` and ``q`` have identical cost rows, then
   permuting their bundles preserves (1) clause by clause, because agent ``p``
   evaluates the permuted allocation with exactly the row that ``q`` used. So
   only occupancy matrices whose rows are lexicographically nondecreasing
   inside each identical-row group are visited, and each stands for its whole
   orbit (``|group|! / prod (repeat multiplicities)!`` arrangements).

Neither collapse is trusted blindly:

* ``allocations_checked`` accumulates the multiplicities and the function
  raises unless the total is *exactly* ``n**m``. A dropped or double-counted
  class cannot pass that check.
* ``double_check=True`` re-evaluates every class with the literal Fraction
  predicate of :mod:`verifier_b.efx_chores` / :mod:`verifier_b.efx_goods` on a
  representative allocation, and raises on any disagreement. Positive classes
  are always re-checked this way, even when ``double_check`` is off.
* :func:`brute_force` enumerates all ``n**m`` tuples with the literal
  predicate and is compared against :func:`exhaust` in the test suite.

Inside the fast path costs are scaled by the least common denominator of the
whole matrix. Every inequality in (1) is a comparison of two sums of row-``i``
entries, so multiplying the entire matrix by one positive integer flips
nothing; it just replaces Fraction arithmetic with int arithmetic.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from typing import Any

from verifier_b import CHORES, GOODS, MODES, parse_matrix
from verifier_b.efx_chores import is_efx_chores
from verifier_b.efx_goods import TRIM_POSITIVE, check_trim, is_efx_goods

__all__ = [
    "DEFAULT_MAX_CLASSES",
    "ExhaustResult",
    "ExhaustTooLarge",
    "brute_force",
    "class_upper_bound",
    "exhaust",
]

#: Refuse to start an enumeration whose class count exceeds this, instead of
#: hanging. This is a resource guard, never a soundness excuse: a run that
#: raises reports no result at all (``SPEC.md`` checklist 19).
DEFAULT_MAX_CLASSES = 20_000_000


class ExhaustTooLarge(ValueError):
    """The instance is too large to certify exhaustively on this machine."""


@dataclass(frozen=True)
class ExhaustResult:
    """Outcome of a complete sweep of ``N**m``."""

    mode: str
    n: int
    m: int
    total_allocations: int  # n**m
    allocations_checked: int
    efx_count: int
    classes_checked: int
    witness: tuple[int, ...] | None
    goods_trim: str | None = None
    double_checked: bool = False

    @property
    def exhaustive(self) -> bool:
        return self.allocations_checked == self.total_allocations


def _check_mode(mode: str) -> str:
    if mode not in MODES:
        raise ValueError(f"unknown mode {mode!r}; expected one of {MODES}")
    return mode


def _integerize(
    matrix: tuple[tuple[Fraction, ...], ...],
) -> tuple[int, tuple[tuple[int, ...], ...]]:
    """Scale the whole matrix by the least common denominator."""
    scale = 1
    for row in matrix:
        for x in row:
            scale = math.lcm(scale, x.denominator)
    return scale, tuple(tuple(int(x * scale) for x in row) for row in matrix)


def class_upper_bound(costs: Any) -> int:
    """Number of occupancy matrices, ignoring the identical-row collapse."""
    matrix = parse_matrix(costs)
    n, m = len(matrix), len(matrix[0])
    counts: dict[tuple[Fraction, ...], int] = {}
    for g in range(m):
        key = tuple(matrix[i][g] for i in range(n))
        counts[key] = counts.get(key, 0) + 1
    return math.prod(math.comb(k + n - 1, n - 1) for k in counts.values())


def exhaust(
    costs: Any,
    mode: str,
    *,
    goods_trim: str | None = None,
    use_row_symmetry: bool = True,
    double_check: bool = False,
    max_classes: int | None = DEFAULT_MAX_CLASSES,
) -> ExhaustResult:
    """Count every EFX allocation among all ``n**m`` allocations.

    Returns a result whose ``allocations_checked`` equals ``n**m`` exactly, or
    raises: there is no partial answer.
    """
    mode = _check_mode(mode)
    trim = check_trim(goods_trim) if mode == GOODS else None
    if mode == CHORES and goods_trim is not None:
        raise ValueError("goods_trim is meaningless for mode='chores'")

    matrix = parse_matrix(costs)
    n, m = len(matrix), len(matrix[0])
    total = n**m
    _, ints = _integerize(matrix)

    # --- column types -----------------------------------------------------
    type_items: dict[tuple[int, ...], list[int]] = {}
    for g in range(m):
        type_items.setdefault(tuple(ints[i][g] for i in range(n)), []).append(g)
    tcost = list(type_items)  # tcost[t][i] = cost of a type-t chore to agent i
    titems = [type_items[k] for k in tcost]
    tsize = [len(x) for x in titems]
    n_types = len(tcost)
    types = range(n_types)

    bound = math.prod(math.comb(k + n - 1, n - 1) for k in tsize)
    if max_classes is not None and bound > max_classes:
        raise ExhaustTooLarge(
            f"n={n} m={m} needs up to {bound} occupancy classes, "
            f"over the max_classes={max_classes} guard"
        )

    # --- identical-row groups --------------------------------------------
    row_groups: list[list[int]] = []
    prev_in_group = [-1] * n
    if use_row_symmetry:
        by_row: dict[tuple[int, ...], list[int]] = {}
        for i in range(n):
            by_row.setdefault(ints[i], []).append(i)
        for group in by_row.values():
            if len(group) > 1:
                row_groups.append(group)
                for earlier, later in zip(group, group[1:]):
                    prev_in_group[later] = earlier

    # --- multiplicity bookkeeping ----------------------------------------
    fact = math.factorial
    numerator = math.prod(fact(k) for k in tsize)  # prod_t k_t!

    def orbit_size(occ: list[tuple[int, ...]]) -> int:
        """Arrangements of this occupancy under the identical-row groups."""
        size = 1
        for group in row_groups:
            size *= fact(len(group))
            run = 1
            for earlier, later in zip(group, group[1:]):
                if occ[later] == occ[earlier]:
                    run += 1
                else:
                    size //= fact(run)
                    run = 1
            size //= fact(run)
        return size

    # --- per-bundle cost vectors -----------------------------------------
    agents = range(n)
    cost_cache: dict[tuple[int, ...], tuple[int, ...]] = {}

    def bundle_costs(counts: tuple[int, ...]) -> tuple[int, ...]:
        """``(c_0(S), ..., c_{n-1}(S))`` for a bundle with these type counts."""
        cached = cost_cache.get(counts)
        if cached is None:
            cached = tuple(
                sum(counts[t] * tcost[t][i] for t in types) for i in agents
            )
            cost_cache[counts] = cached
        return cached

    occ: list[tuple[int, ...]] = [()] * n
    bcost: list[tuple[int, ...]] = [()] * n

    def leaf_is_efx_chores() -> bool:
        """(1) with the ``g`` quantifier collapsed onto column types."""
        for i in agents:
            mine = occ[i]
            if not any(mine):
                continue  # empty own bundle: vacuous for agent i as envier
            own = bcost[i][i]
            for t in types:
                if mine[t]:  # every owned type, including tcost[t][i] == 0
                    remaining = own - tcost[t][i]
                    for j in agents:  # j == i retained
                        if remaining > bcost[j][i]:
                            return False
        return True

    def leaf_is_efx_goods() -> bool:
        trim_all = trim != TRIM_POSITIVE
        for i in agents:
            own = bcost[i][i]
            for j in agents:
                envied = bcost[j][i]
                theirs = occ[j]
                for t in types:
                    if theirs[t]:
                        value = tcost[t][i]
                        if (value or trim_all) and own < envied - value:
                            return False
        return True

    leaf_is_efx = leaf_is_efx_chores if mode == CHORES else leaf_is_efx_goods

    def representative() -> tuple[int, ...]:
        alloc = [0] * m
        for t in types:
            items = titems[t]
            pos = 0
            for k in agents:
                for _ in range(occ[k][t]):
                    alloc[items[pos]] = k
                    pos += 1
        return tuple(alloc)

    def literal_is_efx(alloc: tuple[int, ...]) -> bool:
        if mode == CHORES:
            return is_efx_chores(alloc, matrix)
        return is_efx_goods(alloc, matrix, trim=trim)

    checked = 0
    efx_count = 0
    classes = 0
    witness: tuple[int, ...] | None = None

    def visit(denominator: int) -> None:
        nonlocal checked, efx_count, classes, witness
        classes += 1
        raw = (numerator // denominator) * orbit_size(occ)
        checked += raw
        efx = leaf_is_efx()
        if efx or double_check:
            alloc = representative()
            if literal_is_efx(alloc) is not efx:
                raise RuntimeError(
                    "verifier_b internal disagreement between the fast "
                    f"occupancy check ({efx}) and the literal predicate on "
                    f"allocation {alloc} of {matrix}"
                )
            if efx:
                efx_count += raw
                if witness is None:
                    witness = alloc

    def descend(k: int, remaining: tuple[int, ...], denominator: int) -> None:
        lower = occ[prev_in_group[k]] if prev_in_group[k] >= 0 else None
        if k == n - 1:
            # The last agent takes whatever is left; nothing to choose.
            if lower is not None and remaining < lower:
                return  # not the sorted representative of its row orbit
            occ[k] = remaining
            bcost[k] = bundle_costs(remaining)
            visit(denominator * math.prod(fact(c) for c in remaining))
            return
        for counts in product(*(range(r + 1) for r in remaining)):
            if lower is not None and counts < lower:
                continue  # product() yields lexicographically; skip small ones
            occ[k] = counts
            bcost[k] = bundle_costs(counts)
            descend(
                k + 1,
                tuple(remaining[t] - counts[t] for t in types),
                denominator * math.prod(fact(c) for c in counts),
            )

    descend(0, tuple(tsize), 1)

    if checked != total:
        raise RuntimeError(
            f"verifier_b accounting error: counted {checked} allocations, "
            f"expected n**m = {total}"
        )

    return ExhaustResult(
        mode=mode,
        n=n,
        m=m,
        total_allocations=total,
        allocations_checked=checked,
        efx_count=efx_count,
        classes_checked=classes,
        witness=witness,
        goods_trim=trim,
        double_checked=double_check,
    )


def brute_force(
    costs: Any,
    mode: str,
    *,
    goods_trim: str | None = None,
    max_allocations: int = 3_000_000,
) -> ExhaustResult:
    """Reference sweep: all ``n**m`` tuples through the literal predicate.

    Slow on purpose. Used to cross-check :func:`exhaust`; never used to certify
    the large stored instances.
    """
    mode = _check_mode(mode)
    trim = check_trim(goods_trim) if mode == GOODS else None
    if mode == CHORES and goods_trim is not None:
        raise ValueError("goods_trim is meaningless for mode='chores'")

    matrix = parse_matrix(costs)
    n, m = len(matrix), len(matrix[0])
    total = n**m
    if total > max_allocations:
        raise ExhaustTooLarge(
            f"n**m = {total} exceeds max_allocations={max_allocations}"
        )

    efx_count = 0
    witness: tuple[int, ...] | None = None
    for alloc in product(range(n), repeat=m):
        if mode == CHORES:
            efx = is_efx_chores(alloc, matrix)
        else:
            efx = is_efx_goods(alloc, matrix, trim=trim)
        if efx:
            efx_count += 1
            if witness is None:
                witness = alloc

    return ExhaustResult(
        mode=mode,
        n=n,
        m=m,
        total_allocations=total,
        allocations_checked=total,
        efx_count=efx_count,
        classes_checked=total,
        witness=witness,
        goods_trim=trim,
        double_checked=True,
    )
