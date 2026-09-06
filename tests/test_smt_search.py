"""SMT encoding polarity and a tiny closed-case UNSAT (not a search)."""

from itertools import combinations, product

from z3 import Int, Solver, sat, unsat

from src.smt_search import (
    HANDMADE,
    EncodeOpts,
    lex_le,
    not_efx_clause,
    polarity_self_check,
    python_pair_fails_kobayashi_ido,
    python_pair_has_rev,
    recheck_decoded,
    solve,
)
from src.enumerator import is_efx_chores
from src.kobayashi_alg2 import G1_EXAMPLE


def test_polarity_self_check():
    polarity_self_check()


def test_handmade_efx_status():
    costs = [list(row) for row in HANDMADE]
    assert is_efx_chores((0, 1, 2), costs)
    assert not is_efx_chores((0, 0, 0), costs)


def test_lex_le_z3():
    s = Solver()
    x, y = Int("x"), Int("y")
    s.add(lex_le([x], [y]), x == 2, y == 1)
    assert s.check() == unsat
    s2 = Solver()
    s2.add(lex_le([x], [y]), x == 1, y == 2)
    assert s2.check() == sat


def test_m3_core_ce_unsat():
    r = solve(
        EncodeOpts(m=3, domain=(1, 2, 3), symmetry=True),
        timeout_s=30,
    )
    assert r["z3"] == "unsat"
    assert r["verdict"] == "UNSAT"


def test_not_efx_false_on_efx_alloc():
    m = 3
    costs = [list(row) for row in HANDMADE]
    c = [[Int(f"u_{i}_{g}") for g in range(m)] for i in range(3)]
    s = Solver()
    for i in range(3):
        for g in range(m):
            s.add(c[i][g] == costs[i][g])
    s.add(not_efx_clause(c, (0, 1, 2)))
    assert s.check() == unsat
    for a in product(range(3), repeat=3):
        if is_efx_chores(a, costs):
            s2 = Solver()
            for i in range(3):
                for g in range(m):
                    s2.add(c[i][g] == costs[i][g])
            s2.add(not_efx_clause(c, a))
            assert s2.check() == unsat, a


G1_COSTS = [list(row) for row in G1_EXAMPLE]


def test_g1_example_is_not_pairwise_rev_but_fails_kido():
    """VERDICT.md G1: pair (0,1) has no Rev, yet is not Kobayashi-IDO."""
    assert not python_pair_has_rev(G1_COSTS[0], G1_COSTS[1])
    assert python_pair_fails_kobayashi_ido(G1_COSTS[0], G1_COSTS[1])
    assert python_pair_has_rev(G1_COSTS[0], G1_COSTS[2])
    assert python_pair_has_rev(G1_COSTS[1], G1_COSTS[2])
    assert python_pair_fails_kobayashi_ido(G1_COSTS[0], G1_COSTS[2])
    assert python_pair_fails_kobayashi_ido(G1_COSTS[1], G1_COSTS[2])

    kido_opts = EncodeOpts(
        m=7,
        domain=(1, 2, 3),
        require_row_kdistinct=3,
        require_not_kobayashi_pair_ido=True,
        require_some_pair_no_rev=True,
        require_pairwise_rev=False,
        symmetry=False,
        encode_ce=False,
    )
    assert recheck_decoded(G1_COSTS, kido_opts) == []

    rev_opts = EncodeOpts(
        m=7,
        domain=(1, 2, 3),
        require_pairwise_rev=True,
        symmetry=False,
        encode_ce=False,
    )
    problems = recheck_decoded(G1_COSTS, rev_opts)
    assert any("no Rev" in p for p in problems)


def test_g1_remainder_filter_region_sat():
    """Filter+symmetry region is non-empty (encode_ce off)."""
    r = solve(
        EncodeOpts(
            m=7,
            domain=(1, 2, 3),
            require_row_kdistinct=3,
            require_not_kobayashi_pair_ido=True,
            require_some_pair_no_rev=True,
            symmetry=True,
            encode_ce=False,
        ),
        timeout_s=10,
    )
    assert r["z3"] == "sat"
    assert r["verdict"] != "UNSAT"
    costs = r["costs"]
    assert any(len(set(row)) >= 3 for row in costs)
    pairs = list(combinations(range(3), 2))
    assert all(python_pair_fails_kobayashi_ido(costs[p], costs[q]) for p, q in pairs)
    assert any(not python_pair_has_rev(costs[p], costs[q]) for p, q in pairs)

