"""Kobayashi Algorithm 2 (n-1 IDO insertion) as a heuristic.

Also accepts a common WEAK order: ties may disagree across the n-1 agents.
This is not a proof that Alg 2 survives ties.

EFX-graph: bipartite (agents, n bundles); edge (i,u) iff
max_{e in A_u} c_i(A_u \\ {e}) <= min_k c_i(A_k) (empty A_u is vacuous).
A perfect matching is EFX (Kobayashi Obs 2.3).
"""

from __future__ import annotations

import random
from graphlib import CycleError, TopologicalSorter
from itertools import combinations, permutations
from typing import Sequence

from src.enumerator import is_efx_chores
from src.smt_search import python_pair_fails_kobayashi_ido, python_pair_has_rev

# VERDICT.md G1 example: pair (0,1) has no Rev but is not Kobayashi-IDO.
G1_EXAMPLE = (
    (1, 1, 2, 2, 3, 3, 3),
    (1, 2, 2, 3, 3, 3, 3),
    (3, 3, 2, 2, 1, 1, 1),
)


def common_nonincreasing_order(
    row_p: Sequence[int], row_q: Sequence[int]
) -> list[int] | None:
    """Heavy-first linear extension of the union of two strict orders.

    None if the union has a cycle (a Rev). Ties may disagree.
    """
    m = len(row_p)
    ts: TopologicalSorter[int] = TopologicalSorter()
    for g in range(m):
        ts.add(g)
    for g in range(m):
        for h in range(m):
            if g == h:
                continue
            if row_p[h] > row_p[g] or row_q[h] > row_q[g]:
                ts.add(g, h)
    try:
        return list(ts.static_order())
    except CycleError:
        return None


def _bundle_costs(costs: Sequence[Sequence[int]], bundles: list[list[int]]) -> list[list[int]]:
    n = len(costs)
    return [
        [sum(costs[i][g] for g in bundles[u]) for u in range(n)] for i in range(n)
    ]


def efx_edges(costs: Sequence[Sequence[int]], bundles: list[list[int]]) -> list[list[bool]]:
    n = len(costs)
    bc = _bundle_costs(costs, bundles)
    edges = [[False] * n for _ in range(n)]
    for i in range(n):
        min_k = min(bc[i])
        for u in range(n):
            bu = bundles[u]
            if not bu:
                edges[i][u] = True
                continue
            min_item = min(costs[i][g] for g in bu)
            edges[i][u] = (bc[i][u] - min_item) <= min_k
    return edges


def perfect_matching(edges: list[list[bool]]) -> tuple[int, ...] | None:
    n = len(edges)
    for perm in permutations(range(n)):
        if all(edges[i][perm[i]] for i in range(n)):
            return perm
    return None


def assignment_from_matching(
    bundles: list[list[int]], perm: Sequence[int], m: int
) -> tuple[int, ...]:
    assign = [0] * m
    for i, u in enumerate(perm):
        for g in bundles[u]:
            assign[g] = i
    return tuple(assign)


def alg2_insert(
    costs: Sequence[Sequence[int]], order: Sequence[int]
) -> tuple[int, ...] | None:
    """Insert chores heavy-first; each into some bundle that keeps a matching."""
    n = len(costs)
    m = len(costs[0])
    bundles: list[list[int]] = [[] for _ in range(n)]
    for e in order:
        placed = False
        for u in range(n):
            bundles[u].append(e)
            if perfect_matching(efx_edges(costs, bundles)) is not None:
                placed = True
                break
            bundles[u].pop()
        if not placed:
            return None
    perm = perfect_matching(efx_edges(costs, bundles))
    if perm is None:
        return None
    return assignment_from_matching(bundles, perm, m)


def alg2_weak(costs: Sequence[Sequence[int]]) -> dict:
    """Try Alg 2 on every pair that admits a common weak order.

    Returns a dict with keys: ok, assignment, pair, order, reason.
    """
    n = len(costs)
    attempts = []
    for p, q in combinations(range(n), 2):
        order = common_nonincreasing_order(costs[p], costs[q])
        if order is None:
            attempts.append({"pair": (p, q), "reason": "rev"})
            continue
        alloc = alg2_insert(costs, order)
        if alloc is None:
            attempts.append({"pair": (p, q), "order": order, "reason": "no_bundle"})
            continue
        if not is_efx_chores(alloc, costs):
            return {
                "ok": False,
                "assignment": alloc,
                "pair": (p, q),
                "order": order,
                "reason": "matching_not_efx",
                "attempts": attempts,
            }
        return {
            "ok": True,
            "assignment": alloc,
            "pair": (p, q),
            "order": order,
            "reason": "efx",
            "attempts": attempts,
        }
    return {
        "ok": False,
        "assignment": None,
        "pair": None,
        "order": None,
        "reason": "all_pairs_failed",
        "attempts": attempts,
    }


def is_g1_remainder(costs: Sequence[Sequence[int]], min_distinct: int = 3) -> bool:
    """Open-class G1 remainder: not-kido, some pair has no Rev, not fully IDO."""
    if not any(len(set(row)) >= min_distinct for row in costs):
        return False
    n = len(costs)
    pairs = list(combinations(range(n), 2))
    if not all(python_pair_fails_kobayashi_ido(costs[p], costs[q]) for p, q in pairs):
        return False
    no_rev = [not python_pair_has_rev(costs[p], costs[q]) for p, q in pairs]
    if not any(no_rev):
        return False
    if all(no_rev):
        return False
    return True


def sample_g1_remainder(
    rng: random.Random,
    *,
    m: int = 7,
    domain: tuple[int, ...] = (1, 2, 3),
    n_samples: int = 200,
    max_draws: int = 200_000,
) -> list[list[list[int]]]:
    out: list[list[list[int]]] = []
    draws = 0
    while len(out) < n_samples and draws < max_draws:
        draws += 1
        costs = [[rng.choice(domain) for _ in range(m)] for _ in range(3)]
        if is_g1_remainder(costs):
            out.append(costs)
    return out


def run_oracle(
    n_samples: int = 200,
    seed: int = 20260820,
    domain: tuple[int, ...] = (1, 2, 3),
    m: int = 7,
) -> dict:
    rng = random.Random(seed)
    matrices = sample_g1_remainder(rng, m=m, domain=domain, n_samples=n_samples)
    failures: list[dict] = []
    n_ok = 0
    for costs in matrices:
        r = alg2_weak(costs)
        if r["ok"]:
            n_ok += 1
        else:
            failures.append({"costs": costs, **{k: v for k, v in r.items() if k != "attempts"}})
    return {
        "n_requested": n_samples,
        "n_sampled": len(matrices),
        "n_ok": n_ok,
        "n_fail": len(failures),
        "failures": failures,
        "seed": seed,
        "domain": list(domain),
        "m": m,
    }
