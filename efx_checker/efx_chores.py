"""Additive chores EFX (Definition 1 of the paper), implemented literally.

An allocation ``a`` is EFX when, for every agent ``i`` with a nonempty bundle,
every chore ``g`` in ``X_i`` and every agent ``j``,
``c_i(X_i \\ {g}) <= c_i(X_j)``.  In detail:

* bundles ``X_k(a) = {g : a_g = k}`` are induced by a total assignment, may be
  empty, and cover ``M`` exactly;
* an agent with an empty bundle has nothing to remove and is EFX as envier;
* an agent with a nonempty bundle still compares against empty bundles, whose
  cost is 0;
* the chore is removed from the envier's own bundle;
* every owned chore is removed in turn, including chores with ``c_ig == 0``;
* both sides of a comparison are evaluated in the envier's row ``i``;
* the ``j == i`` comparisons are kept, although they always hold for
  nonnegative costs;
* equality is allowed, so only strict ``>`` witnesses a violation.

For ``m == 0`` the unique all-empty allocation is EFX.
"""

from __future__ import annotations

from collections.abc import Sequence
from fractions import Fraction

from efx_checker import parse_matrix, validate_allocation

__all__ = [
    "bundle_cost",
    "bundles_of",
    "chores_violation",
    "is_efx_chores",
]


def bundles_of(alloc: Sequence[int], n: int) -> tuple[tuple[int, ...], ...]:
    """Return ``(X_0(a), ..., X_{n-1}(a))`` as sorted item-index tuples."""
    out: list[list[int]] = [[] for _ in range(n)]
    for g, owner in enumerate(alloc):
        out[owner].append(g)
    return tuple(tuple(b) for b in out)


def bundle_cost(row: Sequence[Fraction], bundle: Sequence[int]) -> Fraction:
    """``c_i(S) = sum_{g in S} c_ig``, with ``c_i(empty) = 0``."""
    total = Fraction(0)
    for g in bundle:
        total += row[g]
    return total


def chores_violation(
    alloc: Sequence[int], costs: object
) -> tuple[int, int, int] | None:
    """Return the first ``(i, g, j)`` witnessing failure of (1), else ``None``.

    ``(i, g, j)`` means: agent ``i`` owns chore ``g`` and, after removing ``g``
    from its own bundle, still pays strictly more than it would pay for bundle
    ``X_j``, i.e. ``c_i(X_i \\ {g}) > c_i(X_j)``.
    """
    matrix = parse_matrix(costs)
    n = len(matrix)
    m = len(matrix[0])
    alloc = validate_allocation(alloc, n, m)
    bundles = bundles_of(alloc, n)

    for i in range(n):
        own = bundles[i]
        if not own:
            # An empty bundle is EFX for agent i as envier. Other agents still
            # compare against it below, because bundle_cost(row, ()) == 0.
            continue
        own_cost = bundle_cost(matrix[i], own)
        other_costs = [bundle_cost(matrix[i], bundles[j]) for j in range(n)]
        for g in own:  # includes chores with matrix[i][g] == 0
            remaining = own_cost - matrix[i][g]
            for j in range(n):  # j == i retained, as in Definition 1
                if remaining > other_costs[j]:
                    return (i, g, j)
    return None


def is_efx_chores(alloc: Sequence[int], costs: object) -> bool:
    """Chores EFX (Definition 1), for any number ``n = len(costs)`` of agents."""
    return chores_violation(alloc, costs) is None
