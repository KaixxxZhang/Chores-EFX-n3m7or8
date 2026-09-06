"""verifier_b: an independent EFX certifier rebuilt from ``SPEC.md`` alone.

This package is a second implementation. It imports nothing from ``src/``; the
only thing intentionally shared with the primary implementation is the on-disk
JSON shape for cost matrices, which is data, not code. That shape is parsed
here (:func:`load_instances`) so both halves of the project can read the same
``artifacts/*.json`` files without sharing a helper.

Exactness rules used everywhere below:

* every cost is a :class:`fractions.Fraction`;
* ``float`` input is rejected rather than rounded, because every EFX decision
  is a comparison of two sums and a rounded sum can flip ``<=`` into ``>``;
* negative costs are rejected (``SPEC.md`` (2) conjoins ``c_ig >= 0``, and the
  omission of ``j == i`` literals in (6) is only sound for nonnegative costs).

Public names are deliberately small: the predicates live in
:mod:`verifier_b.efx_chores` and :mod:`verifier_b.efx_goods`, exhaustive
counting lives in :mod:`verifier_b.exhaust`, and this module owns only input.
"""

from __future__ import annotations

import json
from collections.abc import Sequence
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any

__all__ = [
    "CHORES",
    "GOODS",
    "MODES",
    "Instance",
    "SpecGapError",
    "instances_from_obj",
    "load_instances",
    "parse_matrix",
    "parse_scalar",
    "validate_allocation",
]

CHORES = "chores"
GOODS = "goods"
MODES = (CHORES, GOODS)

#: Keys accepted as "the matrix" inside an instance object.
_MATRIX_KEYS = ("costs", "matrix", "values")


class SpecGapError(Exception):
    """Raised instead of guessing where ``SPEC.md`` does not fix the semantics.

    See ``SPEC_GAPS.md``. A certifier that guessed here would certify a
    predicate nobody asked for, which is exactly the failure mode ``SPEC.md``
    §6 warns about for the goods/chores trim direction.
    """


def parse_scalar(value: Any) -> Fraction:
    """Return ``value`` as an exact nonnegative :class:`Fraction`.

    Accepts ``int``, ``Fraction``, and strings such as ``"3"``, ``"2/3"``,
    ``"1.5"`` (all parsed exactly). Rejects ``float`` and ``bool``.
    """
    if isinstance(value, bool):
        raise TypeError(f"bool is not a cost: {value!r}")
    if isinstance(value, float):
        raise TypeError(
            f"float costs are rejected as inexact: {value!r}; "
            'use an int or a string like "3/2"'
        )
    if isinstance(value, Fraction):
        out = value
    elif isinstance(value, int):
        out = Fraction(value)
    elif isinstance(value, str):
        try:
            out = Fraction(value)
        except (ValueError, ZeroDivisionError) as exc:
            raise ValueError(f"not an exact rational: {value!r}") from exc
    else:
        raise TypeError(f"unsupported cost type {type(value).__name__}: {value!r}")
    if out < 0:
        raise ValueError(f"negative cost: {value!r}")
    return out


def parse_matrix(rows: Any) -> tuple[tuple[Fraction, ...], ...]:
    """Return an ``n x m`` matrix of exact nonnegative Fractions.

    ``m == 0`` is allowed: ``SPEC.md`` §1 states that for ``m = 0`` the unique
    all-empty allocation is EFX, so the empty matrix must be representable.
    """
    if isinstance(rows, (str, bytes)) or not isinstance(rows, Sequence):
        raise TypeError("matrix must be a sequence of rows")
    if len(rows) == 0:
        raise ValueError("matrix must have at least one agent row")
    out: list[tuple[Fraction, ...]] = []
    width: int | None = None
    for i, row in enumerate(rows):
        if isinstance(row, (str, bytes)) or not isinstance(row, Sequence):
            raise TypeError(f"row {i} is not a sequence: {row!r}")
        if width is None:
            width = len(row)
        elif len(row) != width:
            raise ValueError(
                f"ragged matrix: row 0 has {width} entries, row {i} has {len(row)}"
            )
        out.append(tuple(parse_scalar(x) for x in row))
    return tuple(out)


def validate_allocation(alloc: Sequence[int], n: int, m: int) -> tuple[int, ...]:
    """Check that ``alloc`` is a total assignment in ``N**m`` and return it.

    ``SPEC.md`` §1: an allocation is a *total* map from chores to agents, so no
    item may be unallocated or duplicated. Representing it as one agent index
    per item makes both failures unrepresentable; this only checks the shape.
    """
    if isinstance(alloc, (str, bytes)) or not isinstance(alloc, Sequence):
        raise TypeError("allocation must be a sequence of agent indices")
    if len(alloc) != m:
        raise ValueError(f"allocation has {len(alloc)} entries, expected m={m}")
    out: list[int] = []
    for g, owner in enumerate(alloc):
        if isinstance(owner, bool) or not isinstance(owner, int):
            raise TypeError(f"allocation[{g}] is not an int: {owner!r}")
        if not 0 <= owner < n:
            raise ValueError(f"allocation[{g}]={owner} outside range(n) with n={n}")
        out.append(owner)
    return tuple(out)


@dataclass(frozen=True)
class Instance:
    """One cost matrix read from JSON, with its declared metadata checked."""

    id: str
    costs: tuple[tuple[Fraction, ...], ...]
    mode: str | None = None
    cite: str | None = None

    @property
    def n(self) -> int:
        return len(self.costs)

    @property
    def m(self) -> int:
        return len(self.costs[0])


def _instance_from_obj(obj: Any, index: int, default_id: str) -> Instance:
    if isinstance(obj, Sequence) and not isinstance(obj, (str, bytes)):
        return Instance(id=f"{default_id}[{index}]", costs=parse_matrix(obj))
    if not isinstance(obj, dict):
        raise ValueError(f"instance {index} is neither a matrix nor an object")

    raw = None
    for key in _MATRIX_KEYS:
        if key in obj:
            raw = obj[key]
            break
    if raw is None:
        raise ValueError(
            f"instance {index} has none of the matrix keys {_MATRIX_KEYS}"
        )
    costs = parse_matrix(raw)

    ident = obj.get("id")
    ident = str(ident) if ident is not None else f"{default_id}[{index}]"

    mode = obj.get("mode")
    if mode is not None:
        mode = str(mode)
        if mode not in MODES:
            raise ValueError(f"instance {ident}: unknown mode {mode!r}")

    n, m = len(costs), len(costs[0])
    if "n" in obj and obj["n"] != n:
        raise ValueError(f"instance {ident}: declared n={obj['n']} but {n} rows")
    if "m" in obj and obj["m"] != m:
        raise ValueError(f"instance {ident}: declared m={obj['m']} but {m} columns")

    cite = obj.get("cite")
    return Instance(
        id=ident, costs=costs, mode=mode, cite=str(cite) if cite else None
    )


def instances_from_obj(obj: Any, *, default_id: str = "instance") -> list[Instance]:
    """Decode the shared matrix JSON schema.

    Accepted shapes:

    * a bare matrix ``[[...], [...]]``;
    * an object with a matrix under ``costs`` / ``matrix`` / ``values``, plus
      optional ``id``, ``n``, ``m``, ``mode``, ``cite`` (``n`` and ``m`` are
      cross-checked against the matrix);
    * an object with ``instances``: a list of either of the above.
    """
    if isinstance(obj, dict) and "instances" in obj:
        raw = obj["instances"]
        if not isinstance(raw, Sequence) or isinstance(raw, (str, bytes)):
            raise ValueError("'instances' must be a list")
        if len(raw) == 0:
            raise ValueError("'instances' is empty")
        return [_instance_from_obj(x, i, default_id) for i, x in enumerate(raw)]
    return [_instance_from_obj(obj, 0, default_id)]


def load_instances(path: str | Path) -> list[Instance]:
    """Read and decode a matrix JSON file."""
    path = Path(path)
    obj = json.loads(path.read_text())
    return instances_from_obj(obj, default_id=path.stem)
