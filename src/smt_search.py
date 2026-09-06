"""Bounded Z3 search for n=3 additive-chores EFX counterexamples (SPEC.md).

Does not import verifier_b (independence). Dual-check SAT models by
importing the enumerator and spawning `python -m verifier_b.cli`.
"""

from __future__ import annotations

import argparse
import json
import multiprocessing as mp
import subprocess
import sys
import time
from dataclasses import dataclass
from itertools import combinations, product
from pathlib import Path
from typing import Sequence

from z3 import And, BoolRef, BoolVal, If, Int, IntVal, Not, Or, Solver, Sum, Xor, sat, unknown, unsat

from src.enumerator import exists_efx_chores, find_efx_chores, is_efx_chores

ROOT = Path(__file__).resolve().parents[1]
ARTIFACTS = ROOT / "artifacts"
STATUS_PATH = ROOT / "record" / "STATUS.md"
N = range(3)

PROBE_TIMEOUT_S = 120
SEARCH_TIMEOUT_S = 600

HANDMADE = (
    (1, 5, 5),
    (5, 1, 5),
    (5, 5, 1),
)


def _and(xs: Sequence[BoolRef | bool]) -> BoolRef:
    xs = list(xs)
    if not xs:
        return BoolVal(True)
    if len(xs) == 1:
        return xs[0] if isinstance(xs[0], BoolRef) else BoolVal(bool(xs[0]))
    return And(*xs)


def _or(xs: Sequence[BoolRef | bool]) -> BoolRef:
    xs = list(xs)
    if not xs:
        return BoolVal(False)
    if len(xs) == 1:
        return xs[0] if isinstance(xs[0], BoolRef) else BoolVal(bool(xs[0]))
    return Or(*xs)


def lex_le(xs: Sequence, ys: Sequence) -> BoolRef:
    """Explicit first-difference lexicographic xs <= ys (SPEC.md §4)."""
    if len(xs) != len(ys):
        raise ValueError("lex_le length mismatch")
    opts: list[BoolRef] = []
    prefix_eq: list[BoolRef] = []
    for k in range(len(xs)):
        opts.append(_and(prefix_eq + [xs[k] < ys[k]]))
        prefix_eq.append(xs[k] == ys[k])
    opts.append(_and(prefix_eq))
    return _or(opts)


def zsum(xs: list) -> object:
    return Sum(xs) if xs else IntVal(0)


@dataclass(frozen=True)
class EncodeOpts:
    m: int
    domain: tuple[int, ...]
    require_row_kdistinct: int = 0
    require_pairwise_rev: bool = False
    require_not_kobayashi_pair_ido: bool = False
    require_some_pair_no_rev: bool = False
    force_bivalued: bool = False
    force_ido: bool = False
    symmetry: bool = True
    encode_ce: bool = True
    tag: str | None = None


def not_efx_clause(c: list[list], a: tuple[int, ...]) -> BoolRef:
    """SPEC.md (6): some envier i, owned g, j≠i with own-minus-g > other."""
    m = len(a)
    bundles: list[list[int]] = [[] for _ in N]
    for g, owner in enumerate(a):
        bundles[owner].append(g)
    bad: list[BoolRef] = []
    for i in N:
        if not bundles[i]:
            continue
        own = zsum([c[i][h] for h in bundles[i]])
        for j in N:
            if j == i:
                continue
            other = zsum([c[i][h] for h in bundles[j]])
            for g in bundles[i]:
                bad.append(own - c[i][g] > other)
    return _or(bad)


def rev(c: list[list], p: int, q: int, g: int, h: int) -> BoolRef:
    return Or(
        And(c[p][g] < c[p][h], c[q][g] > c[q][h]),
        And(c[p][g] > c[p][h], c[q][g] < c[q][h]),
    )


def dis(c: list[list], p: int, q: int, e: int, ep: int) -> BoolRef:
    """SPEC.md (4): (c_p(e)<c_p(e')) XOR (c_q(e)<c_q(e'))."""
    return Xor(c[p][e] < c[p][ep], c[q][e] < c[q][ep])


def pair_fails_kobayashi_ido(c: list[list], p: int, q: int, m: int) -> BoolRef:
    return _or(
        [dis(c, p, q, e, ep) for e in range(m) for ep in range(m) if e != ep]
    )


def pair_has_rev(c: list[list], p: int, q: int, m: int) -> BoolRef:
    return _or([rev(c, p, q, g, h) for g, h in combinations(range(m), 2)])


def uses(c: list[list], i: int, v: int, m: int) -> BoolRef:
    return _or([c[i][g] == v for g in range(m)])


def build_solver(opts: EncodeOpts) -> tuple[Solver, list[list]]:
    m = opts.m
    D = opts.domain
    M = range(m)
    c = [[Int(f"c_{i}_{g}") for g in M] for i in N]
    s = Solver()

    for i in N:
        for g in M:
            s.add(_or([c[i][g] == v for v in D]))

    if opts.require_row_kdistinct >= 1:
        k = opts.require_row_kdistinct
        if k > len(D):
            raise ValueError("kdistinct larger than |D|")
        row_ok = []
        for i in N:
            row_ok.append(
                _or(
                    [
                        _and([uses(c, i, v, m) for v in triple])
                        for triple in combinations(D, k)
                    ]
                )
            )
        s.add(_or(row_ok))

    if opts.force_bivalued:
        if len(D) >= 3:
            for i in N:
                for triple in combinations(D, 3):
                    s.add(Not(_and([uses(c, i, v, m) for v in triple])))

    if opts.require_pairwise_rev:
        for p, q in combinations(N, 2):
            s.add(_or([rev(c, p, q, g, h) for g, h in combinations(M, 2)]))

    if opts.require_not_kobayashi_pair_ido:
        for p, q in combinations(N, 2):
            s.add(pair_fails_kobayashi_ido(c, p, q, m))

    if opts.require_some_pair_no_rev:
        s.add(_or([Not(pair_has_rev(c, p, q, m)) for p, q in combinations(N, 2)]))

    if opts.force_ido:
        for p, q in combinations(N, 2):
            for g, h in combinations(M, 2):
                s.add(Not(rev(c, p, q, g, h)))

    if opts.symmetry:
        hist = []
        for i in N:
            hist.append([zsum([If(c[i][g] == v, 1, 0) for g in M]) for v in D])
        s.add(lex_le(hist[0], hist[1]))
        s.add(lex_le(hist[1], hist[2]))
        cols = [[c[0][g], c[1][g], c[2][g]] for g in M]
        for g in range(m - 1):
            s.add(lex_le(cols[g], cols[g + 1]))

    if opts.encode_ce:
        for a in product(N, repeat=m):
            s.add(not_efx_clause(c, a))

    return s, c


def decode_costs(model, c: list[list], m: int) -> list[list[int]]:
    return [
        [model.eval(c[i][g], model_completion=True).as_long() for g in range(m)]
        for i in N
    ]


def python_rev(row_p: Sequence[int], row_q: Sequence[int], g: int, h: int) -> bool:
    return (row_p[g] < row_p[h] and row_q[g] > row_q[h]) or (
        row_p[g] > row_p[h] and row_q[g] < row_q[h]
    )


def python_dis(row_p: Sequence[int], row_q: Sequence[int], e: int, ep: int) -> bool:
    return (row_p[e] < row_p[ep]) != (row_q[e] < row_q[ep])


def python_pair_fails_kobayashi_ido(row_p: Sequence[int], row_q: Sequence[int]) -> bool:
    m = len(row_p)
    return any(
        python_dis(row_p, row_q, e, ep) for e in range(m) for ep in range(m) if e != ep
    )


def python_pair_has_rev(row_p: Sequence[int], row_q: Sequence[int]) -> bool:
    m = len(row_p)
    return any(python_rev(row_p, row_q, g, h) for g, h in combinations(range(m), 2))


def recheck_decoded(costs: list[list[int]], opts: EncodeOpts) -> list[str]:
    """Checklist 17: domain, value-use, order. Return problem strings."""
    problems: list[str] = []
    m = opts.m
    D = set(opts.domain)
    if len(costs) != 3 or any(len(row) != m for row in costs):
        problems.append("shape")
        return problems
    for i in N:
        for g in range(m):
            if costs[i][g] not in D:
                problems.append(f"cost[{i}][{g}]={costs[i][g]} not in D")
    if opts.require_row_kdistinct:
        k = opts.require_row_kdistinct
        ok = False
        for i in N:
            if len(set(costs[i])) >= k:
                ok = True
        if not ok:
            problems.append(f"no row has {k} distinct values")
    if opts.force_bivalued:
        for i in N:
            if len(set(costs[i])) > 2:
                problems.append(f"row {i} not bi-valued")
    if opts.require_pairwise_rev:
        for p, q in combinations(N, 2):
            if not python_pair_has_rev(costs[p], costs[q]):
                problems.append(f"no Rev({p},{q})")
    if opts.require_not_kobayashi_pair_ido:
        for p, q in combinations(N, 2):
            if not python_pair_fails_kobayashi_ido(costs[p], costs[q]):
                problems.append(f"pair ({p},{q}) is Kobayashi-IDO")
    if opts.require_some_pair_no_rev:
        if all(python_pair_has_rev(costs[p], costs[q]) for p, q in combinations(N, 2)):
            problems.append("every pair has a Rev; not G1 remainder")
    if opts.force_ido:
        for p, q in combinations(N, 2):
            if any(
                python_rev(costs[p], costs[q], g, h)
                for g, h in combinations(range(m), 2)
            ):
                problems.append("IDO probe model has a reversal")
    same_order = not any(
        python_rev(costs[p], costs[q], g, h)
        for p, q in combinations(N, 2)
        for g, h in combinations(range(m), 2)
    )
    if same_order and not opts.force_ido and opts.encode_ce:
        problems.append("IDO: all three rows induce the same order")
    if opts.symmetry:
        hist = [tuple(row.count(v) for v in opts.domain) for row in costs]
        if not (hist[0] <= hist[1] <= hist[2]):
            problems.append(f"histogram not sorted: {hist}")
        cols = [tuple(costs[i][g] for i in N) for g in range(m)]
        if any(cols[g] > cols[g + 1] for g in range(m - 1)):
            problems.append("columns not lex-sorted")
    return problems


def enumerator_report(costs: list[list[int]]) -> dict:
    found = find_efx_chores(costs)
    exists = found is not None
    return {
        "exists_efx": exists,
        "witness": list(found) if found is not None else None,
        "efx_count_positive": exists,
    }


def verifier_b_report(path: Path, *, double_check: bool = False) -> dict:
    cmd = [
        sys.executable,
        "-m",
        "verifier_b.cli",
        str(path),
        "--mode",
        "chores",
        "--json",
    ]
    if double_check:
        cmd.append("--double-check")
    proc = subprocess.run(
        cmd,
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    if proc.returncode != 0:
        return {
            "ok": False,
            "returncode": proc.returncode,
            "stdout": proc.stdout[-2000:],
            "stderr": proc.stderr[-2000:],
        }
    payload = json.loads(proc.stdout)
    inst = payload["instances"][0]
    return {
        "ok": True,
        "n": inst["n"],
        "m": inst["m"],
        "n**m": inst["n**m"],
        "allocations_checked": inst["allocations_checked"],
        "efx_count": inst["efx_count"],
        "witness_allocation": inst["witness_allocation"],
    }


def write_matrix_json(path: Path, costs: list[list[int]], extra: dict) -> None:
    n = len(costs)
    m = len(costs[0])
    obj = {
        "id": path.stem,
        "n": n,
        "m": m,
        "mode": "chores",
        "costs": costs,
        **extra,
    }
    path.write_text(json.dumps(obj, indent=2) + "\n")


def dual_validate(costs: list[list[int]], tag: str) -> dict:
    """Write JSON, run enumerator + verifier_b CLI. Never claim on disagreement."""
    ARTIFACTS.mkdir(exist_ok=True)
    cand = ARTIFACTS / f"cand_chores_{tag}.json"
    write_matrix_json(
        cand,
        costs,
        {"source": "src/smt_search.py", "tag": tag},
    )
    enum_r = enumerator_report(costs)
    # Potential CE (enumerator sees no EFX): re-check every class, G3.
    ver_r = verifier_b_report(cand, double_check=not enum_r["exists_efx"])
    out = {"path": str(cand), "enumerator": enum_r, "verifier_b": ver_r}

    enum_zero = not enum_r["exists_efx"]
    ver_zero = (
        ver_r.get("ok")
        and ver_r.get("efx_count") == 0
        and ver_r.get("allocations_checked") == ver_r.get("n**m")
    )
    if enum_r["exists_efx"] or (ver_r.get("ok") and ver_r.get("efx_count", 1) > 0):
        rejected = ARTIFACTS / f"rejected_chores_{tag}.json"
        cand.replace(rejected)
        out["path"] = str(rejected)
        out["verdict"] = "REJECTED_HAS_EFX"
        out["encoding_wrong"] = True
        return out
    if not ver_r.get("ok"):
        out["verdict"] = "NO_RESULT_VERIFIER"
        return out
    if enum_zero and ver_zero:
        out["verdict"] = "BOTH_EFX_COUNT_ZERO"
        return out
    out["verdict"] = "NO_RESULT_DISAGREE"
    return out


def polarity_self_check() -> None:
    """SPEC pitfalls: (6) must be true of a non-EFX alloc and false of an EFX alloc."""
    m = 3
    costs = [list(row) for row in HANDMADE]
    assert is_efx_chores((0, 1, 2), costs)
    assert not is_efx_chores((0, 0, 0), costs)

    c = [[Int(f"t_{i}_{g}") for g in range(m)] for i in N]
    fix = [c[i][g] == costs[i][g] for i in N for g in range(m)]

    s_efx = Solver()
    s_efx.add(fix)
    s_efx.add(not_efx_clause(c, (0, 1, 2)))
    if s_efx.check() != unsat:
        raise RuntimeError("polarity: NotEFX is SAT on an EFX allocation")

    s_bad = Solver()
    s_bad.add(fix)
    s_bad.add(not_efx_clause(c, (0, 0, 0)))
    if s_bad.check() != sat:
        raise RuntimeError("polarity: NotEFX is UNSAT on a non-EFX allocation")

    s_ce = Solver()
    s_ce.add(fix)
    for a in product(N, repeat=m):
        s_ce.add(not_efx_clause(c, a))
    if s_ce.check() != unsat:
        raise RuntimeError("polarity: CE is SAT on a matrix that has an EFX allocation")

    s_lex = Solver()
    x, y = Int("lx"), Int("ly")
    s_lex.add(lex_le([x], [y]))
    s_lex.add(x == 2, y == 1)
    if s_lex.check() != unsat:
        raise RuntimeError("lex_le is not <=lex")


def _opts_report(opts: EncodeOpts) -> dict:
    return {
        "m": opts.m,
        "domain": list(opts.domain),
        "require_row_kdistinct": opts.require_row_kdistinct,
        "require_pairwise_rev": opts.require_pairwise_rev,
        "require_not_kobayashi_pair_ido": opts.require_not_kobayashi_pair_ido,
        "require_some_pair_no_rev": opts.require_some_pair_no_rev,
        "force_bivalued": opts.force_bivalued,
        "force_ido": opts.force_ido,
        "symmetry": opts.symmetry,
        "encode_ce": opts.encode_ce,
    }


def solve_inprocess(opts: EncodeOpts, timeout_s: int) -> dict:
    t0 = time.perf_counter()
    s, c = build_solver(opts)
    build_s = time.perf_counter() - t0
    s.set("timeout", max(1, int(timeout_s * 1000)))
    t1 = time.perf_counter()
    result = s.check()
    check_s = time.perf_counter() - t1
    out: dict = {
        **_opts_report(opts),
        "z3": str(result),
        "build_s": round(build_s, 3),
        "check_s": round(check_s, 3),
        "timeout_s": timeout_s,
    }
    if result == unknown:
        out["reason"] = str(s.reason_unknown())
        out["verdict"] = "NO_RESULT_UNKNOWN"
        return out
    if result == unsat:
        out["verdict"] = "UNSAT"
        return out
    if result != sat:
        out["verdict"] = "NO_RESULT"
        return out

    costs = decode_costs(s.model(), c, opts.m)
    out["costs"] = costs
    problems = recheck_decoded(costs, opts)
    if problems:
        out["decode_problems"] = problems
        out["verdict"] = "NO_RESULT_DECODE"
        return out
    if not opts.encode_ce:
        out["verdict"] = "SAT_FILTER_ONLY"
        return out
    tag = opts.tag or f"m{opts.m}_d{''.join(str(v) for v in opts.domain)}"
    dual = dual_validate(costs, tag)
    out["dual"] = dual
    out["verdict"] = dual["verdict"]
    return out


def _solve_worker(opts: EncodeOpts, timeout_s: int, q: mp.Queue) -> None:
    q.put(solve_inprocess(opts, timeout_s))


def solve(opts: EncodeOpts, timeout_s: int) -> dict:
    """Solve with Z3's timeout. For large m, also kill the worker on wall-clock overrun.

    m=12 eager (6) has ~3^12 clauses; Z3's LRA setup can ignore `timeout` for
    many minutes at multi-GB RSS. Checklist 19: that is no result, not UNSAT.
    """
    if opts.m < 12:
        return solve_inprocess(opts, timeout_s)

    nalloc = 3 ** opts.m
    build_grace = min(600, max(60, nalloc // 1500))
    wait_s = timeout_s + build_grace
    ctx = mp.get_context("spawn")
    q: mp.Queue = ctx.Queue()
    proc = ctx.Process(target=_solve_worker, args=(opts, timeout_s, q))
    proc.start()
    proc.join(wait_s)
    if proc.is_alive():
        proc.terminate()
        proc.join(20)
        if proc.is_alive():
            proc.kill()
            proc.join(5)
        return {
            **_opts_report(opts),
            "z3": "unknown",
            "build_s": None,
            "check_s": wait_s,
            "timeout_s": timeout_s,
            "reason": f"wall-clock timeout after {wait_s}s (Z3 check did not return)",
            "verdict": "NO_RESULT_UNKNOWN",
        }
    if not q.empty():
        return q.get()
    return {
        **_opts_report(opts),
        "z3": "unknown",
        "build_s": None,
        "check_s": None,
        "timeout_s": timeout_s,
        "reason": "worker exited without a result",
        "verdict": "NO_RESULT_UNKNOWN",
    }


_STATUS_LINES: list[str] = []


def status_reset_header() -> None:
    _STATUS_LINES.clear()
    _STATUS_LINES.extend(
        [
            "# STATUS",
            "",
            "- date: 2026-08-19",
            "- python: 3.13.3",
            "- z3: 5.1.0",
            "- PHASE = B",
            "- encoding: `src/smt_search.py` = SPEC.md (1)(2)(6), Int domain equalities, histogram+column lex",
            "- OPEN n=3 additive chores m≥7: not claimed solved",
        ]
    )


def status_add(line: str) -> None:
    _STATUS_LINES.append(line)
    STATUS_PATH.write_text("\n".join(_STATUS_LINES) + "\n")
    print(line, flush=True)


def status_append(line: str) -> None:
    """Append to the committed STATUS.md; do not wipe round-1 rows."""
    existing = STATUS_PATH.read_text() if STATUS_PATH.exists() else ""
    if existing and not existing.endswith("\n"):
        existing += "\n"
    STATUS_PATH.write_text(existing + line + "\n")
    print(line, flush=True)


def fmt_result(label: str, r: dict) -> str:
    extra = ""
    if r.get("verdict") == "UNSAT":
        extra = (
            f" bounded UNSAT only (m={r['m']} D={r['domain']}"
            f" filters kdistinct={r['require_row_kdistinct']}"
            f" pairwise_rev={r.get('require_pairwise_rev')}"
            f" not_kido={r.get('require_not_kobayashi_pair_ido')}"
            f" some_no_rev={r.get('require_some_pair_no_rev')}"
            f" bivalued={r['force_bivalued']} ido={r['force_ido']}"
            f" sym={r['symmetry']}); not existence"
        )
    if r.get("costs"):
        extra += f" costs={r['costs']}"
    if r.get("dual"):
        extra += f" dual={r['dual'].get('verdict')}"
    if r.get("reason"):
        extra += f" reason={r['reason']}"
    return (
        f"- {label}: z3={r['z3']} verdict={r['verdict']} "
        f"build={r['build_s']}s check={r['check_s']}s{extra}"
    )


def stop_if_m_le_6_fake_ce(r: dict) -> None:
    if r["m"] > 6:
        return
    if r.get("verdict") == "BOTH_EFX_COUNT_ZERO":
        status_add("- ENCODING_CONTRADICTS_THEOREM")
        status_add(
            f"- SAT model at m={r['m']} has efx_count=0 on both checkers; "
            "Kobayashi m≤2n forbids this. Do not publish. Waiting for humans."
        )
        raise SystemExit("ENCODING_CONTRADICTS_THEOREM")


def run_probes() -> None:
    polarity_self_check()
    status_add("- polarity self-check: pass (EFX alloc ⇒ NotEFX unsat; non-EFX alloc ⇒ sat; handmade CE unsat)")

    for m in (4, 5, 6):
        opts = EncodeOpts(
            m=m,
            domain=(1, 2, 3),
            require_row_kdistinct=0,
            require_pairwise_rev=False,
            symmetry=True,
        )
        r = solve(opts, PROBE_TIMEOUT_S)
        status_add(fmt_result(f"probe core m={m} D={{1,2,3}} (no tri/IDO filters)", r))
        stop_if_m_le_6_fake_ce(r)
        if r["verdict"] == "REJECTED_HAS_EFX":
            status_add("- SAT at m≤6 rejected: enumerator/verifier found EFX (encoding would be unsound if we had claimed CE)")
        if r["z3"] == "sat" and r["verdict"] == "REJECTED_HAS_EFX":
            raise RuntimeError(
                f"core probe m={m} SAT but checkers found EFX: encoding of (6) is wrong"
            )
        if r["verdict"] not in {"UNSAT", "REJECTED_HAS_EFX"}:
            status_add(f"- probe m={m} did not finish as UNSAT; stopping probes")
            raise SystemExit(f"soundness probe m={m} inconclusive: {r}")

    bv = solve(
        EncodeOpts(
            m=7,
            domain=(1, 2, 3),
            force_bivalued=True,
            symmetry=True,
        ),
        PROBE_TIMEOUT_S,
    )
    status_add(fmt_result("probe bi-valued m=7 D={1,2,3}", bv))
    if bv["verdict"] == "BOTH_EFX_COUNT_ZERO":
        status_add("- ENCODING_CONTRADICTS_THEOREM (bi-valued SAT with efx_count=0)")
        raise SystemExit("ENCODING_CONTRADICTS_THEOREM")
    if bv["z3"] == "sat" and bv["verdict"] == "REJECTED_HAS_EFX":
        raise RuntimeError("bi-valued probe SAT with EFX: encoding wrong")
    if bv["verdict"] not in {"UNSAT", "REJECTED_HAS_EFX"}:
        status_add("- bi-valued probe inconclusive")
        raise SystemExit(f"bi-valued probe inconclusive: {bv}")

    ido = solve(
        EncodeOpts(
            m=7,
            domain=(1, 2, 3),
            force_ido=True,
            symmetry=True,
        ),
        PROBE_TIMEOUT_S,
    )
    status_add(fmt_result("probe IDO m=7 D={1,2,3}", ido))
    if ido["verdict"] == "BOTH_EFX_COUNT_ZERO":
        status_add("- ENCODING_CONTRADICTS_THEOREM (IDO SAT with efx_count=0)")
        raise SystemExit("ENCODING_CONTRADICTS_THEOREM")
    if ido["z3"] == "sat" and ido["verdict"] == "REJECTED_HAS_EFX":
        raise RuntimeError("IDO probe SAT with EFX: encoding wrong")
    if ido["verdict"] not in {"UNSAT", "REJECTED_HAS_EFX"}:
        status_add("- IDO probe inconclusive")
        raise SystemExit(f"IDO probe inconclusive: {ido}")

    status_add("- soundness probes: pass")


def run_primary() -> None:
    domains: list[tuple[int, ...]] = [(1, 2, 3), (1, 2, 3, 4, 5)]
    for m in range(7, 13):
        for D in domains:
            k = 3
            opts = EncodeOpts(
                m=m,
                domain=D,
                require_row_kdistinct=k,
                require_pairwise_rev=True,
                symmetry=True,
            )
            r = solve(opts, SEARCH_TIMEOUT_S)
            status_add(fmt_result(f"primary m={m} D={set(D)} tri≥3 pairwise-rev", r))
            if r["verdict"] == "BOTH_EFX_COUNT_ZERO":
                status_add(
                    f"- CANDIDATE: both checkers efx_count=0 at m={m} "
                    f"file={r['dual']['path']}. Not a paper. Dual-checked only."
                )
                return
            if r["verdict"] == "REJECTED_HAS_EFX":
                status_add("- SAT model has EFX; encoding of (6) is wrong; stopping")
                raise SystemExit("encoding rejected by dual check")
        status_add(f"- m={m} done (no dual-checked counterexample)")
    status_add("- stop after m=12; no dual-checked counterexample; no unbounded existence claim")


def _round2_handle(label: str, r: dict) -> dict:
    status_append(fmt_result(label, r))
    if r["m"] <= 6 and r.get("verdict") == "BOTH_EFX_COUNT_ZERO":
        status_append("- ENCODING_CONTRADICTS_THEOREM")
        status_append(
            f"- SAT model at m={r['m']} has efx_count=0 on both checkers; "
            "Kobayashi m≤2n forbids this. Do not publish."
        )
        raise SystemExit("ENCODING_CONTRADICTS_THEOREM")
    if r.get("verdict") == "REJECTED_HAS_EFX":
        status_append("- SAT model has EFX; encoding of (6) is wrong; stopping")
        raise SystemExit("encoding rejected by dual check")
    if r.get("verdict") == "BOTH_EFX_COUNT_ZERO":
        status_append(
            f"- CANDIDATE: both checkers efx_count=0 file={r['dual']['path']}. "
            "Not a paper. Dual-checked with --double-check."
        )
    return r


def run_round2() -> None:
    """G1 remainder + zeros + large-ratio search. Appends to STATUS.md."""
    status_append("")
    status_append("## Round 2 / G2")
    status_append("")
    status_append("- date: 2026-08-20")
    status_append(
        "- encoding: SPEC.md (4) = Kobayashi-IDO blocker; "
        "`require_pairwise_rev` kept to reproduce round-1 numbers"
    )
    status_append(
        "- G1: round-1 primary UNSATs used the stricter Rev filter; "
        "this section searches the remainder and new domains"
    )
    polarity_self_check()
    status_append("- polarity self-check: pass")

    for m in (4, 5, 6):
        opts = EncodeOpts(
            m=m,
            domain=(1, 2, 3),
            require_row_kdistinct=0,
            require_pairwise_rev=False,
            require_not_kobayashi_pair_ido=False,
            require_some_pair_no_rev=False,
            symmetry=True,
        )
        r = solve(opts, PROBE_TIMEOUT_S)
        _round2_handle(f"round2 soundness core m={m} D={{1,2,3}} (new filter off)", r)
        if r["verdict"] not in {"UNSAT", "REJECTED_HAS_EFX"}:
            raise SystemExit(f"soundness probe m={m} inconclusive: {r}")

    jobs: list[tuple[str, EncodeOpts]] = [
        (
            "G1 remainder m=7 D={1,2,3} tri≥3 not-kido some-no-rev",
            EncodeOpts(
                m=7,
                domain=(1, 2, 3),
                require_row_kdistinct=3,
                require_not_kobayashi_pair_ido=True,
                require_some_pair_no_rev=True,
                symmetry=True,
                tag="m7_d123_g1rem",
            ),
        ),
        (
            "G1 remainder m=7 D={1..5} tri≥3 not-kido some-no-rev",
            EncodeOpts(
                m=7,
                domain=(1, 2, 3, 4, 5),
                require_row_kdistinct=3,
                require_not_kobayashi_pair_ido=True,
                require_some_pair_no_rev=True,
                symmetry=True,
                tag="m7_d12345_g1rem",
            ),
        ),
        (
            "zeros m=7 D={0,1,2,3} tri≥3 not-kido",
            EncodeOpts(
                m=7,
                domain=(0, 1, 2, 3),
                require_row_kdistinct=3,
                require_not_kobayashi_pair_ido=True,
                symmetry=True,
                tag="m7_d0123_zeros",
            ),
        ),
        (
            "large-ratio m=7 D={0,1,2,3,5,8,13} tri≥3 not-kido",
            EncodeOpts(
                m=7,
                domain=(0, 1, 2, 3, 5, 8, 13),
                require_row_kdistinct=3,
                require_not_kobayashi_pair_ido=True,
                symmetry=True,
                tag="m7_d01235813_ratio",
            ),
        ),
        (
            "large-ratio m=7 D={1..20} tri≥3 not-kido",
            EncodeOpts(
                m=7,
                domain=tuple(range(1, 21)),
                require_row_kdistinct=3,
                require_not_kobayashi_pair_ido=True,
                symmetry=True,
                tag="m7_d1to20_ratio",
            ),
        ),
    ]
    for label, opts in jobs:
        r = solve(opts, SEARCH_TIMEOUT_S)
        _round2_handle(label, r)
        if r.get("verdict") == "BOTH_EFX_COUNT_ZERO":
            return
    status_append(
        "- round-2 primary: no dual-checked counterexample; bounded only; not existence"
    )


def main(argv: Sequence[str] | None = None) -> int:
    p = argparse.ArgumentParser(prog="python -m src.smt_search")
    p.add_argument(
        "--run",
        choices=("self-check", "probe", "search", "phase-b", "round2"),
        default="phase-b",
    )
    p.add_argument("--m", type=int, default=None)
    p.add_argument("--domain", default="1,2,3")
    p.add_argument("--timeout", type=int, default=None, help="seconds")
    args = p.parse_args(argv)

    if args.run == "self-check":
        polarity_self_check()
        print("self-check ok")
        return 0

    if args.run == "round2":
        run_round2()
        return 0

    status_reset_header()
    status_add("- smt_search started")

    if args.run == "probe":
        run_probes()
        return 0

    if args.run == "search":
        if args.m is None:
            p.error("--m is required for --run search")
        D = tuple(int(x) for x in args.domain.split(",") if x)
        opts = EncodeOpts(
            m=args.m,
            domain=D,
            require_row_kdistinct=3 if args.m > 6 else 0,
            require_pairwise_rev=args.m > 6,
            symmetry=True,
        )
        r = solve(opts, args.timeout or SEARCH_TIMEOUT_S)
        status_add(fmt_result(f"search m={args.m} D={set(D)}", r))
        print(json.dumps({k: v for k, v in r.items() if k != "dual"}, indent=2))
        if "dual" in r:
            print(json.dumps(r["dual"], indent=2))
        return 0

    run_probes()
    run_primary()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
