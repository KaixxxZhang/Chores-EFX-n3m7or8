"""Kobayashi Alg 2 weak-order heuristic: not a theorem, just an oracle."""

import random

from src.enumerator import exists_efx_chores, is_efx_chores
from src.kobayashi_alg2 import (
    G1_EXAMPLE,
    alg2_weak,
    common_nonincreasing_order,
    is_g1_remainder,
    sample_g1_remainder,
)
from src.smt_search import python_pair_has_rev


def test_g1_example_is_g1_remainder():
    costs = [list(row) for row in G1_EXAMPLE]
    assert is_g1_remainder(costs)
    order = common_nonincreasing_order(costs[0], costs[1])
    assert order is not None
    assert not python_pair_has_rev(costs[0], costs[1])


def test_alg2_on_ido_random_is_efx():
    rng = random.Random(20260820)
    m = 7
    for _ in range(20):
        base = [sorted(rng.randint(1, 5) for _ in range(m)) for _a in range(3)]
        perm = list(range(m))
        rng.shuffle(perm)
        costs = [[row[j] for j in perm] for row in base]
        assert exists_efx_chores(costs)
        r = alg2_weak(costs)
        assert r["ok"], costs
        assert is_efx_chores(r["assignment"], costs)


def test_alg2_on_g1_example():
    costs = [list(row) for row in G1_EXAMPLE]
    r = alg2_weak(costs)
    if r["ok"]:
        assert is_efx_chores(r["assignment"], costs)
    else:
        # Open instance for the weak-order heuristic, not yet a CE.
        assert exists_efx_chores(costs) is True


def test_sample_g1_remainder_and_alg2():
    rng = random.Random(1)
    mats = sample_g1_remainder(rng, n_samples=12, max_draws=20_000)
    assert len(mats) == 12
    for costs in mats:
        assert is_g1_remainder(costs)
        r = alg2_weak(costs)
        if r["ok"]:
            assert is_efx_chores(r["assignment"], costs)


def test_common_order_none_on_rev():
    row_p = (1, 2, 3)
    row_q = (3, 2, 1)
    assert python_pair_has_rev(row_p, row_q)
    assert common_nonincreasing_order(row_p, row_q) is None
