"""Command line certifier.

    python -m verifier_b.cli artifacts/hetao.json --mode chores

Prints, per instance, ``n``, ``m``, ``n**m``, ``allocations_checked`` and
``efx_count``. A claimed counterexample is only certified when
``efx_count = 0`` *and* ``allocations_checked = n**m``; anything else (a
resource guard, a schema error, a mode mismatch) exits nonzero and certifies
nothing.
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from collections.abc import Sequence

from verifier_b import CHORES, GOODS, MODES, Instance, SpecGapError, load_instances
from verifier_b.efx_goods import TRIMS
from verifier_b.exhaust import DEFAULT_MAX_CLASSES, ExhaustResult, exhaust

EXIT_OK = 0
EXIT_ERROR = 1
EXIT_EXPECTATION_FAILED = 2


def _build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="python -m verifier_b.cli",
        description=(
            "Independent EFX certifier (verifier_b). Exhausts every one of the "
            "n**m allocations and counts the EFX ones."
        ),
    )
    parser.add_argument(
        "path", help="matrix JSON file (bare matrix, {costs}, or {instances})"
    )
    parser.add_argument(
        "--mode",
        choices=MODES,
        default=None,
        help="chores or goods; defaults to the mode declared in the file",
    )
    parser.add_argument(
        "--goods-trim",
        choices=TRIMS,
        default=None,
        help=(
            "required with --mode goods: 'positive' trims only positively "
            "valued goods (classical EFX), 'all' trims every good (EFX0). "
            "SPEC.md does not decide this; see SPEC_GAPS.md"
        ),
    )
    parser.add_argument(
        "--instance",
        action="append",
        default=None,
        metavar="ID",
        help="only certify this instance id (repeatable)",
    )
    parser.add_argument(
        "--double-check",
        action="store_true",
        help="re-verify every symmetry class with the literal Fraction predicate",
    )
    parser.add_argument(
        "--no-row-symmetry",
        action="store_true",
        help="disable the identical-row collapse (slower, fewer assumptions)",
    )
    parser.add_argument(
        "--max-classes",
        type=int,
        default=DEFAULT_MAX_CLASSES,
        help=f"resource guard on occupancy classes (default {DEFAULT_MAX_CLASSES})",
    )
    parser.add_argument(
        "--expect-no-efx",
        action="store_true",
        help="exit nonzero unless every instance has efx_count = 0",
    )
    parser.add_argument(
        "--json", action="store_true", help="emit machine-readable JSON"
    )
    return parser


def _resolve_mode(inst: Instance, requested: str | None) -> str:
    if requested is None:
        if inst.mode is None:
            raise ValueError(
                f"instance {inst.id} declares no mode; "
                "pass --mode chores or --mode goods"
            )
        return inst.mode
    if inst.mode is not None and inst.mode != requested:
        raise ValueError(
            f"instance {inst.id} declares mode {inst.mode!r} but --mode "
            f"{requested} was given; refusing to reinterpret the file"
        )
    return requested


def _report(inst: Instance, result: ExhaustResult, elapsed: float) -> list[str]:
    lines = [f"instance: {inst.id}"]
    if inst.cite:
        lines.append(f"  cite = {inst.cite}")
    lines += [
        f"  mode = {result.mode}"
        + (f" (trim={result.goods_trim})" if result.goods_trim else ""),
        f"  n = {result.n}",
        f"  m = {result.m}",
        f"  n**m = {result.total_allocations}",
        f"  allocations_checked = {result.allocations_checked}",
        f"  efx_count = {result.efx_count}",
        f"  symmetry_classes = {result.classes_checked}",
        f"  double_checked = {result.double_checked}",
        f"  elapsed_s = {elapsed:.3f}",
    ]
    if result.witness is not None:
        lines.append(f"  witness_allocation = {tuple(result.witness)}")
    if not result.exhaustive:  # unreachable: exhaust() raises instead
        lines.append("  verdict: NOT EXHAUSTIVE - no result")
    elif result.efx_count == 0:
        lines.append("  verdict: NO EFX ALLOCATION EXISTS (exhaustive)")
    else:
        lines.append("  verdict: EFX ALLOCATION EXISTS - not a counterexample")
    return lines


def main(argv: Sequence[str] | None = None) -> int:
    args = _build_parser().parse_args(argv)

    if args.goods_trim is not None and args.mode == CHORES:
        print("error: --goods-trim is meaningless with --mode chores", file=sys.stderr)
        return EXIT_ERROR

    try:
        instances = load_instances(args.path)
    except (OSError, ValueError, TypeError, json.JSONDecodeError) as exc:
        print(f"error: cannot read {args.path}: {exc}", file=sys.stderr)
        return EXIT_ERROR

    if args.instance:
        wanted = set(args.instance)
        missing = wanted - {inst.id for inst in instances}
        if missing:
            print(f"error: no such instance id: {sorted(missing)}", file=sys.stderr)
            return EXIT_ERROR
        instances = [inst for inst in instances if inst.id in wanted]

    out: list[str] = []
    payload: list[dict[str, object]] = []
    if not args.json:
        out.append(
            "verifier_b: independent EFX certifier, exact Fractions, SPEC.md (1)"
        )
        out.append(f"file: {args.path}")
        out.append("")

    exit_code = EXIT_OK
    for inst in instances:
        try:
            mode = _resolve_mode(inst, args.mode)
            trim = args.goods_trim if mode == GOODS else None
            started = time.perf_counter()
            result = exhaust(
                inst.costs,
                mode,
                goods_trim=trim,
                use_row_symmetry=not args.no_row_symmetry,
                double_check=args.double_check,
                max_classes=args.max_classes,
            )
            elapsed = time.perf_counter() - started
        except SpecGapError as exc:
            print(f"error: instance {inst.id}: {exc}", file=sys.stderr)
            return EXIT_ERROR
        except (ValueError, TypeError) as exc:
            print(f"error: instance {inst.id}: {exc}", file=sys.stderr)
            return EXIT_ERROR

        if args.expect_no_efx and result.efx_count != 0:
            exit_code = EXIT_EXPECTATION_FAILED
        out.extend(_report(inst, result, elapsed))
        out.append("")
        payload.append(
            {
                "id": inst.id,
                "mode": result.mode,
                "goods_trim": result.goods_trim,
                "n": result.n,
                "m": result.m,
                "n**m": result.total_allocations,
                "allocations_checked": result.allocations_checked,
                "efx_count": result.efx_count,
                "symmetry_classes": result.classes_checked,
                "double_checked": result.double_checked,
                "witness_allocation": list(result.witness)
                if result.witness is not None
                else None,
                "elapsed_s": round(elapsed, 3),
            }
        )

    if args.json:
        print(json.dumps({"file": args.path, "instances": payload}, indent=2))
        return exit_code

    with_efx = sum(1 for p in payload if p["efx_count"] != 0)
    out.append(
        f"summary: {len(payload)} instance(s) exhausted, "
        f"{with_efx} with an EFX allocation"
    )
    if args.expect_no_efx and exit_code != EXIT_OK:
        out.append("expectation FAILED: an EFX allocation exists")
    print("\n".join(out))
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
