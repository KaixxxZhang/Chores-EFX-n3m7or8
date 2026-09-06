"""Additive **chores** EFX, transcribed from ``SPEC.md`` equation (1).

The transcription is deliberately literal and slow. Every clause below cites
the line of ``SPEC.md`` §1 / §6 that forces it:

* bundles ``X_k(a) = {g : a_g = k}`` are induced by a total assignment, may be
  empty, and cover ``M`` exactly (§1);
* an agent with an empty own bundle contributes the explicit empty disjunct and
  is vacuously EFX *as envier* (§1, checklist 9);
* an agent with a nonempty bundle still compares against empty bundles, whose
  cost is 0 (§6 "Empty bundles");
* the trim happens on the **envier's own** bundle (§6 "Goods versus chores");
* every owned chore is quantified, including ``c_ig == 0`` (§1, §6 "Zeros",
  checklist 8) -- there is no ``c[i][g] > 0`` guard;
* both sides of a comparison are evaluated in the envier's row ``i``
  (§6 "Perspective", checklist 6);
* ``j == i`` conjuncts are retained as in (1), even though they are automatic
  for nonnegative costs (§1);
* EFX allows equality, so only strict ``>`` witnesses failure (§1, §6
  "Boundary direction").

For ``m == 0`` the unique all-empty allocation is EFX (§1).
"""

from __future__ import annotations

from collections.abc import Sequence
from fractions import Fraction

from verifier_b import parse_matrix, validate_allocation

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
    """``c_i(S) = sum_{g in S} c_ig``, with ``c_i(empty) = 0`` (§1)."""
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
            # Explicit empty-bundle disjunct of (1): vacuously EFX for agent i
            # as envier. Other agents still compare against this empty bundle,
            # which happens below because bundle_cost(row, ()) == 0.
            continue
        own_cost = bundle_cost(matrix[i], own)
        other_costs = [bundle_cost(matrix[i], bundles[j]) for j in range(n)]
        for g in own:  # includes chores with matrix[i][g] == 0
            remaining = own_cost - matrix[i][g]
            for j in range(n):  # j == i retained, as in (1)
                if remaining > other_costs[j]:
                    return (i, g, j)
    return None


def is_efx_chores(alloc: Sequence[int], costs: object) -> bool:
    """``EFX_3`` of ``SPEC.md`` (1), generalised to any ``n = len(costs)``."""
    return chores_violation(alloc, costs) is None
