"""Additive goods EFX.

The goods predicate is used only in the tests, to make sure that the chores
predicate removes a chore from the envier's own bundle and not, as for goods,
from the envied bundle ``X_j``.  Both sides are evaluated in the envier's row
``i``, ``v_i(empty) = 0``, and only strict ``<`` witnesses a violation.

Two versions of goods EFX are in use: EFX removes only goods with
``v_ig > 0``, while EFX0 removes any good in ``X_j``.  The caller has to choose
one; there is no default.

    is_efx_goods(alloc, values, trim=TRIM_POSITIVE)  # EFX
    is_efx_goods(alloc, values, trim=TRIM_ALL)       # EFX0
"""

from __future__ import annotations

from collections.abc import Sequence

from efx_checker import TrimPolicyError, parse_matrix, validate_allocation
from efx_checker.efx_chores import bundle_cost, bundles_of

__all__ = [
    "TRIM_ALL",
    "TRIM_POSITIVE",
    "TRIMS",
    "check_trim",
    "goods_violation",
    "is_efx_goods",
]

#: Quantify only goods the envier values strictly positively (classical EFX).
TRIM_POSITIVE = "positive"
#: Quantify every good in the envied bundle, zero-valued ones included (EFX0).
TRIM_ALL = "all"
TRIMS = (TRIM_POSITIVE, TRIM_ALL)


def check_trim(trim: str | None) -> str:
    """Validate an explicit goods trim policy; there is no default."""
    if trim is None:
        raise TrimPolicyError(
            "goods EFX needs an explicit trim policy: "
            f"trim={TRIM_POSITIVE!r} (only positively valued goods, classical "
            f"EFX) or trim={TRIM_ALL!r} (every good in the envied bundle, "
            "EFX0)."
        )
    if trim not in TRIMS:
        raise ValueError(f"unknown goods trim policy {trim!r}; expected one of {TRIMS}")
    return trim


def goods_violation(
    alloc: Sequence[int], values: object, *, trim: str | None = None
) -> tuple[int, int, int] | None:
    """Return the first ``(i, j, g)`` witnessing goods-EFX failure, else ``None``.

    ``(i, j, g)`` means: good ``g`` belongs to agent ``j``'s bundle and agent
    ``i`` still strictly prefers ``X_j`` minus ``g`` to its own bundle, i.e.
    ``v_i(X_i) < v_i(X_j \\ {g})``.
    """
    trim = check_trim(trim)
    matrix = parse_matrix(values)
    n = len(matrix)
    m = len(matrix[0])
    alloc = validate_allocation(alloc, n, m)
    bundles = bundles_of(alloc, n)

    for i in range(n):
        row = matrix[i]
        own_value = bundle_cost(row, bundles[i])
        for j in range(n):  # j == i retained; it is automatic for v >= 0
            envied_value = bundle_cost(row, bundles[j])
            for g in bundles[j]:
                # An empty X_j contributes no g, so it can never be envied.
                if trim == TRIM_POSITIVE and row[g] == 0:
                    continue
                if own_value < envied_value - row[g]:
                    return (i, j, g)
    return None


def is_efx_goods(
    alloc: Sequence[int], values: object, *, trim: str | None = None
) -> bool:
    """Goods EFX under an explicitly chosen ``trim`` policy."""
    return goods_violation(alloc, values, trim=trim) is None
