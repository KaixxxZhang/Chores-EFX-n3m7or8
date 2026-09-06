"""Closed existence cases used as enumerator sanity checks, not as search targets."""

import random

from src.enumerator import exists_efx_chores, exists_efx_goods, is_efx_chores


def test_handmade_chores_efx_exists():
    costs = [
        [1, 5, 5],
        [5, 1, 5],
        [5, 5, 1],
    ]
    assert exists_efx_chores(costs) is True
    assert is_efx_chores((0, 1, 2), costs)


def test_n2_goods_random_instances_have_efx():
    rng = random.Random(20260819)
    for m in (2, 3, 4, 5, 6):
        for _ in range(8):
            values = [[rng.randint(0, 9) for _ in range(m)] for _ in range(2)]
            assert exists_efx_goods(values) is True, values


def test_n3_goods_m_le_6_random_instances_have_efx():
    rng = random.Random(20260819 + 1)
    for m in (3, 4, 5, 6):
        for _ in range(6):
            values = [[rng.randint(0, 9) for _ in range(m)] for _ in range(3)]
            assert exists_efx_goods(values) is True, values


def test_n3_chores_m_le_6_random_instances_have_efx():
    """Kobayashi m ≤ 2n. A False here means the enumerator is wrong."""
    rng = random.Random(20260819 + 2)
    for m in (1, 2, 3, 4, 5, 6):
        for _ in range(8):
            costs = [[rng.randint(0, 9) for _ in range(m)] for _ in range(3)]
            assert exists_efx_chores(costs) is True, costs


def test_n3_chores_m8_bivalued_12_have_efx():
    """Kobayashi n=3 personalized bi-valued. A False here means the enumerator is wrong."""
    rng = random.Random(20260819 + 3)
    m = 8
    for _ in range(12):
        costs = [[rng.choice((1, 2)) for _ in range(m)] for _ in range(3)]
        assert exists_efx_chores(costs) is True, costs


def test_n3_chores_m8_ido_have_efx():
    """IDO closed. A False here means the enumerator is wrong."""
    rng = random.Random(20260819 + 4)
    m = 8
    for _ in range(12):
        costs = []
        for _a in range(3):
            row = sorted(rng.randint(1, 9) for _ in range(m))
            costs.append(row)
        # common permutation of columns keeps identical ordering
        perm = list(range(m))
        rng.shuffle(perm)
        costs = [[row[j] for j in perm] for row in costs]
        assert exists_efx_chores(costs) is True, costs
