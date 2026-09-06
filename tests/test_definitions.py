"""Definition tests: trim direction, empty bundles, fractions, no floats."""

from fractions import Fraction

import pytest

from src.enumerator import (
    exists_efx_chores,
    exists_efx_goods,
    is_efx_chores,
    is_efx_goods,
    parse_matrix,
    parse_scalar,
)


def test_z3_is_available():
    import z3

    assert z3.get_version_string()


def test_parse_rejects_floats():
    with pytest.raises(TypeError, match="float"):
        parse_scalar(1.5)
    with pytest.raises(TypeError, match="float"):
        parse_matrix([[1.0, 2]])


def test_parse_fractions_and_ints():
    m = parse_matrix([[0, "1/2", 3], ["2/3", 1, "4/5"]])
    assert m[0][1] == Fraction(1, 2)
    assert m[1][0] == Fraction(2, 3)
    assert m[0][2] == Fraction(3)


def test_parse_rejects_negatives():
    with pytest.raises(ValueError, match="negative"):
        parse_matrix([[1, -1]])


def test_empty_own_bundle_is_vacuous_but_nonempty_must_still_beat_empty():
    # Agent 0 empty is vacuously EFX as envier. Agent 1 holding both chores
    # still has to satisfy c1(X1 \\ {g}) <= c1(empty)=0 for every g, so fails.
    costs = [[3, 1], [1, 3]]
    alloc = (1, 1)
    assert not is_efx_chores(alloc, costs)


def test_empty_bundle_vacuous_for_envier_only():
    # n=2, m=1: whoever gets the chore, after removing it remaining 0 <= other's 0.
    costs = [[5], [9]]
    assert is_efx_chores((0,), costs)
    assert is_efx_chores((1,), costs)
    assert exists_efx_chores(costs)


def test_goods_efx0_skips_zero_value_items():
    # Aj = {zero-for-i, positive}. Only the positive item is trimmed.
    # v0(A0)=0, A1={item0 cost 0 to agent 0, item1 cost 5}.
    # If we required trim of the zero item, 0 >= 5-0 would fail (EFX vs EFX0).
    values = [[0, 5, 1], [3, 3, 1]]
    alloc = (1, 1, 0)  # items 0,1 → agent 1; item 2 → agent 0
    # i=0 vs j=1: g=item0 v=0 skipped; g=item1 v=5: 1 >= 5-5 = 0. OK
    assert is_efx_goods(alloc, values)
    # If zeros were trimmed, own 1 >= (0+5)-0 = 5 would fail.
    # Chores: agent 1 remaining 3 > c1(A0)=1.
    assert not is_efx_chores(alloc, values)


def test_swapping_goods_trim_and_chores_trim_disagrees():
    """If the two predicates were swapped, this test fails."""
    # Chores-EFX, not goods-EFX.
    costs_chores_yes = [
        [3, 1, 3],
        [1, 5, 2],
    ]
    alloc_a = (0, 0, 1)
    assert is_efx_chores(alloc_a, costs_chores_yes)
    assert not is_efx_goods(alloc_a, costs_chores_yes)

    # Goods-EFX, not chores-EFX.
    costs_goods_yes = [
        [10, 1, 5],
        [2, 2, 8],
    ]
    alloc_b = (0, 0, 1)
    assert is_efx_goods(alloc_b, costs_goods_yes)
    assert not is_efx_chores(alloc_b, costs_goods_yes)


def test_chores_for_every_g_not_just_some_g():
    # Remaining after expensive chore is small (easy); after cheap chore is hard.
    # own = 5+1=6 vs other=4. Remove 5: rem 1 <= 4. Remove 1: rem 5 > 4.
    # EF1-style "some g" would pass; EFX "every g" must fail.
    costs = [[5, 1, 4], [1, 1, 1]]
    alloc = (0, 0, 1)
    assert not is_efx_chores(alloc, costs)


def test_goods_for_every_positive_g_not_just_some():
    # own=3, other={4, 10}. Remove 10: 3 >= 4. Remove 4: 3 >= 10. Fail EFX.
    values = [[3, 4, 10], [1, 1, 1]]
    alloc = (0, 1, 1)
    assert not is_efx_goods(alloc, values)


def test_fractional_chores_efx():
    costs = [["1/2", "2/3"], ["3/4", "1/5"]]
    # singletons: remaining 0 <= other.
    assert is_efx_chores((0, 1), costs)
    assert exists_efx_chores(costs)


def test_grouped_occupancy_matches_raw_assignments():
    from itertools import product

    costs = [
        [2, 2, 1],
        [1, 1, 3],
    ]
    raw = any(is_efx_chores(a, costs) for a in product(range(2), repeat=3))
    assert exists_efx_chores(costs) is raw
    raw_g = any(is_efx_goods(a, costs) for a in product(range(2), repeat=3))
    assert exists_efx_goods(costs) is raw_g


def test_exists_goods_and_chores_are_different_functions():
    matrix = [
        [10, 1, 5],
        [2, 2, 8],
    ]
    # Some allocation is goods-EFX; that same matrix may still have chores-EFX
    # (e.g. singletons plus empty). Existence of one does not imply the other
    # predicate on a fixed allocation — covered above. Here: goods exists.
    assert exists_efx_goods(matrix)
    # n=2 additive chores always exist as well; so existence alone is not a
    # swap detector. The allocation-level test above is the swap detector.
    assert exists_efx_chores(matrix)
