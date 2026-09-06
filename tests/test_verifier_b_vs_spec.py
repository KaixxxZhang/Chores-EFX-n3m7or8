"""`verifier_b` against `SPEC.md`, with no reference to `src/`.

This file is the certifier's own regression suite. It never imports `src`, so a
green run here says "the second implementation agrees with the written spec",
independently of whatever the first implementation does.

Coverage map:

* isolation from `src/` (hard requirement 1);
* clause-by-clause transcription of `SPEC.md` (1): trim side, empty bundles,
  zero costs, every-`g`, perspective row, `>` boundary;
* trim-direction swap detectors for both goods and chores (hard requirement 2),
  including inline *swapped* reimplementations that must disagree;
* `artifacts/hetao.json`: exhaustive, no chores EFX allocation (hard
  requirement 3);
* `allocations_checked == n**m` on every path (hard requirement 4);
* the goods zero-value gap is refused, not guessed (hard requirement 5);
* random `n=3, m=6` chores instances have `efx_count > 0` (hard requirement 6);
* `exhaust` (symmetry classes plus multiplicities) against `brute_force` (all
  `n**m` tuples through the literal predicate).

Set `VERIFIER_B_SLOW=1` to also run the two minute-scale paranoia sweeps.
"""

from __future__ import annotations

import json
import os
import random
import re
import subprocess
import sys
from fractions import Fraction
from itertools import product
from pathlib import Path

import pytest

from verifier_b import (
    CHORES,
    GOODS,
    SpecGapError,
    load_instances,
    parse_matrix,
    parse_scalar,
    validate_allocation,
)
from verifier_b.efx_chores import (
    bundle_cost,
    bundles_of,
    chores_violation,
    is_efx_chores,
)
from verifier_b.efx_goods import TRIM_ALL, TRIM_POSITIVE, goods_violation, is_efx_goods
from verifier_b.exhaust import ExhaustTooLarge, brute_force, class_upper_bound, exhaust

ROOT = Path(__file__).resolve().parents[1]
HETAO = ROOT / "artifacts" / "hetao.json"
SLOW = os.environ.get("VERIFIER_B_SLOW") == "1"
slow = pytest.mark.skipif(not SLOW, reason="set VERIFIER_B_SLOW=1")


# --------------------------------------------------------------------------
# 1. isolation: verifier_b shares nothing with src/
# --------------------------------------------------------------------------

_IMPORT_SRC = re.compile(r"^\s*(?:from|import)\s+src\b", re.MULTILINE)
_IMPORT_VERIFIER_B = re.compile(r"^\s*(?:from|import)\s+verifier_b\b", re.MULTILINE)


def test_verifier_b_has_the_required_modules():
    for name in ("__init__", "efx_chores", "efx_goods", "exhaust", "cli"):
        assert (ROOT / "verifier_b" / f"{name}.py").is_file()


def test_no_verifier_b_source_imports_src():
    for path in sorted((ROOT / "verifier_b").glob("*.py")):
        text = path.read_text()
        assert not _IMPORT_SRC.search(text), f"{path.name} imports src"
        assert "__import__" not in text, f"{path.name} hides an import"


def test_src_does_not_import_verifier_b():
    for path in sorted((ROOT / "src").glob("*.py")):
        assert not _IMPORT_VERIFIER_B.search(path.read_text()), (
            f"src/{path.name} imports verifier_b; the two implementations must "
            "stay independent"
        )


def test_importing_verifier_b_never_loads_src_or_z3():
    """A fresh interpreter that imports all of verifier_b must not pull in src."""
    probe = (
        "import sys;"
        "import verifier_b, verifier_b.efx_chores, verifier_b.efx_goods,"
        " verifier_b.exhaust, verifier_b.cli;"
        "print(sorted(n for n in sys.modules"
        " if n == 'src' or n.startswith('src.') or n == 'z3' or n.startswith('z3.')))"
    )
    done = subprocess.run(
        [sys.executable, "-c", probe], cwd=ROOT, capture_output=True, text=True
    )
    assert done.returncode == 0, done.stderr
    assert done.stdout.strip() == "[]", done.stdout


# --------------------------------------------------------------------------
# 2. input handling: exact rationals only
# --------------------------------------------------------------------------


def test_parse_rejects_floats_and_bools():
    with pytest.raises(TypeError, match="float"):
        parse_scalar(1.5)
    with pytest.raises(TypeError, match="float"):
        parse_matrix([[1.0, 2]])
    with pytest.raises(TypeError, match="bool"):
        parse_scalar(True)


def test_parse_keeps_fractions_exact():
    matrix = parse_matrix([[0, "1/2", 3], ["2/3", 1, "4/5"]])
    assert matrix[0][1] == Fraction(1, 2)
    assert matrix[1][0] == Fraction(2, 3)
    assert matrix[0][2] == Fraction(3)
    assert all(isinstance(x, Fraction) for row in matrix for x in row)
    # 1/3 + 1/3 + 1/3 == 1 exactly, which float would not guarantee.
    assert bundle_cost(parse_matrix([["1/3"] * 3])[0], (0, 1, 2)) == 1


def test_parse_rejects_negatives_and_ragged_rows():
    with pytest.raises(ValueError, match="negative"):
        parse_matrix([[1, -1]])
    with pytest.raises(ValueError, match="ragged"):
        parse_matrix([[1, 2], [3]])
    with pytest.raises(ValueError, match="at least one agent"):
        parse_matrix([])


def test_allocation_must_be_total():
    with pytest.raises(ValueError, match="expected m=3"):
        validate_allocation((0, 1), n=2, m=3)
    with pytest.raises(ValueError, match="outside range"):
        validate_allocation((0, 2), n=2, m=2)
    assert validate_allocation([0, 1, 0], n=2, m=3) == (0, 1, 0)


# --------------------------------------------------------------------------
# 3. SPEC.md (1), clause by clause
# --------------------------------------------------------------------------


def test_empty_own_bundle_is_vacuous_for_that_agent_only():
    """SPEC.md §1 empty disjunct + §6 "Empty bundles"."""
    # Agent 0 holds nothing and is vacuously EFX as envier. Agent 1 holds both
    # chores and must still beat c1(empty) = 0 after removing either chore.
    assert not is_efx_chores((1, 1), [[3, 1], [1, 3]])
    assert chores_violation((1, 1), [[3, 1], [1, 3]]) == (1, 0, 0)
    # A singleton owner is fine: what remains after the trim is 0 <= 0.
    assert is_efx_chores((0,), [[5], [9]])
    assert is_efx_chores((1,), [[5], [9]])


def test_m_zero_all_empty_allocation_is_efx():
    """SPEC.md §1: "For m = 0, the unique all-empty allocation is EFX"."""
    assert is_efx_chores((), [[], [], []])
    result = exhaust([[], [], []], CHORES)
    assert (result.total_allocations, result.allocations_checked) == (1, 1)
    assert result.efx_count == 1 and result.witness == ()


def test_zero_cost_owned_chores_are_quantified():
    """SPEC.md §6 "Zeros" / checklist 8: no `c[i][g] > 0` guard."""
    # Agent 0 owns a free chore and a costly one; agent 1 owns nothing.
    # Trimming the free chore leaves 5 > c0(empty) = 0, so this fails EFX.
    # Skipping zero-cost chores would trim only the costly one and pass.
    assert not is_efx_chores((0, 0), [[0, 5], [1, 1]])
    assert chores_violation((0, 0), [[0, 5], [1, 1]]) == (0, 0, 1)
    # And a zero-cost chore held alone is harmless.
    assert is_efx_chores((0, 1), [[0, 5], [1, 1]])


def test_every_owned_chore_not_merely_some():
    """EFX, not EF1: the trim quantifier is universal (SPEC.md (1))."""
    # own = 5 + 1 = 6 vs other = 4. Trim the 5 and 1 <= 4 passes; trim the 1
    # and 5 > 4 fails. "Some g" would accept, "every g" must reject.
    assert not is_efx_chores((0, 0, 1), [[5, 1, 4], [1, 1, 1]])
    assert chores_violation((0, 0, 1), [[5, 1, 4], [1, 1, 1]]) == (0, 1, 1)


def test_both_bundles_are_costed_in_the_enviers_row():
    """SPEC.md §6 "Perspective" / checklist 6: c_i(X_j), never c_j(X_j)."""
    costs = [[1, 1, 5], [9, 9, 0]]
    alloc = (0, 0, 1)
    # Agent 0: own 2, trim either chore -> 1 <= c0(X1) = 5. Agent 1: own 0.
    assert is_efx_chores(alloc, costs)
    # An implementation costing X1 in row 1 would see c1(X1) = 0 and report a
    # violation, so this assertion is the perspective detector.
    matrix = parse_matrix(costs)
    bundles = bundles_of(alloc, 2)
    assert bundle_cost(matrix[0], bundles[1]) == 5
    assert bundle_cost(matrix[1], bundles[1]) == 0


def test_equality_is_efx_and_only_strict_excess_fails():
    """SPEC.md §6 "Boundary direction"."""
    # Agent 0 keeps {0,1}, agent 1 keeps {2}. After trimming chore 0 the
    # remainder is exactly c0(X1), so equality must be accepted.
    assert is_efx_chores((0, 0, 1), [[2, 3, 3], [1, 1, 1]])
    # Nudge the compared bundle down by one and the same shape now fails.
    assert not is_efx_chores((0, 0, 1), [[2, 3, 2], [1, 1, 1]])


def test_fractional_costs_decide_a_boundary_case():
    costs = [["1/2", "1/3", "5/6"], [1, 1, 1]]
    # 1/2 + 1/3 - 1/3 = 1/2 <= 5/6 and 1/3 <= 5/6: EFX by exact arithmetic.
    assert is_efx_chores((0, 0, 1), costs)
    # Now the compared bundle is 499/1000, one thousandth under the 1/2 that
    # remains after the trim, so EFX must fail.
    assert not is_efx_chores((0, 0, 1), [["1/2", "1/3", "499/1000"], [1, 1, 1]])


# --------------------------------------------------------------------------
# 4. trim direction: goods vs chores (hard requirement 2)
# --------------------------------------------------------------------------

# Both fixtures use n=2, m=3 and alloc (0,0,1), so X0 = {0,1}, X1 = {2}.
# With row0 = [a,b,c] and row1 = [d,e,f]:
#   chores EFX <=> max(a,b) <= c          (agent 0 trims its own bundle)
#   goods  EFX <=> f >= max(d,e)          (agent 1 trims the envied bundle)
# Choosing the two conditions independently separates the predicates.
CHORES_YES_GOODS_NO = [[1, 1, 5], [4, 4, 1]]
GOODS_YES_CHORES_NO = [[5, 5, 1], [1, 1, 3]]
SPLIT_ALLOC = (0, 0, 1)


def _chores_with_the_goods_trim(alloc, costs):
    """Wrong on purpose: trims the *envied* bundle in a chores comparison."""
    matrix = parse_matrix(costs)
    bundles = bundles_of(alloc, len(matrix))
    for i in range(len(matrix)):
        own = bundle_cost(matrix[i], bundles[i])
        for j in range(len(matrix)):
            envied = bundle_cost(matrix[i], bundles[j])
            for g in bundles[j]:
                if own > envied - matrix[i][g]:
                    return False
    return True


def _goods_with_the_chores_trim(alloc, values):
    """Wrong on purpose: trims the *envier's own* bundle in a goods comparison."""
    matrix = parse_matrix(values)
    bundles = bundles_of(alloc, len(matrix))
    for i in range(len(matrix)):
        own = bundle_cost(matrix[i], bundles[i])
        for j in range(len(matrix)):
            envied = bundle_cost(matrix[i], bundles[j])
            for g in bundles[i]:
                if own - matrix[i][g] < envied:
                    return False
    return True


@pytest.mark.parametrize("trim", [TRIM_POSITIVE, TRIM_ALL])
def test_chores_efx_and_goods_efx_disagree_in_both_directions(trim):
    """Swap the two trim directions and every assertion here flips."""
    assert is_efx_chores(SPLIT_ALLOC, CHORES_YES_GOODS_NO)
    assert not is_efx_goods(SPLIT_ALLOC, CHORES_YES_GOODS_NO, trim=trim)

    assert not is_efx_chores(SPLIT_ALLOC, GOODS_YES_CHORES_NO)
    assert is_efx_goods(SPLIT_ALLOC, GOODS_YES_CHORES_NO, trim=trim)


@pytest.mark.parametrize("trim", [TRIM_POSITIVE, TRIM_ALL])
def test_the_swapped_predicates_really_do_disagree_with_ours(trim):
    """Guards the fixtures above: they are genuine discriminators."""
    assert _chores_with_the_goods_trim(SPLIT_ALLOC, CHORES_YES_GOODS_NO) is False
    assert is_efx_chores(SPLIT_ALLOC, CHORES_YES_GOODS_NO) is True

    assert _goods_with_the_chores_trim(SPLIT_ALLOC, GOODS_YES_CHORES_NO) is False
    assert is_efx_goods(SPLIT_ALLOC, GOODS_YES_CHORES_NO, trim=trim) is True


def test_goods_violation_names_the_envied_bundle():
    # own = 3; X1 = {1,2} worth 4 + 10. Trimming good 1 leaves 10 > 3.
    assert goods_violation((0, 1, 1), [[3, 4, 10], [1, 1, 1]], trim=TRIM_POSITIVE) == (
        0,
        1,
        1,
    )
    assert not is_efx_goods((0, 1, 1), [[3, 4, 10], [1, 1, 1]], trim=TRIM_POSITIVE)


@pytest.mark.parametrize("costs", [CHORES_YES_GOODS_NO, GOODS_YES_CHORES_NO])
def test_exhaust_modes_are_different_predicates_not_aliases(costs):
    """The two modes accept different *sets*, and exhaust counts each set."""
    allocs = list(product(range(2), repeat=3))
    chores_set = {a for a in allocs if is_efx_chores(a, costs)}
    goods_set = {a for a in allocs if is_efx_goods(a, costs, trim=TRIM_POSITIVE)}
    assert chores_set != goods_set
    assert (SPLIT_ALLOC in chores_set) is not (SPLIT_ALLOC in goods_set)

    chores_run = exhaust(costs, CHORES, double_check=True)
    goods_run = exhaust(costs, GOODS, goods_trim=TRIM_POSITIVE, double_check=True)
    assert chores_run.allocations_checked == goods_run.allocations_checked == 2**3
    assert chores_run.efx_count == len(chores_set)
    assert goods_run.efx_count == len(goods_set)


# --------------------------------------------------------------------------
# 5. the goods zero-value gap is refused, not guessed (hard requirement 5)
# --------------------------------------------------------------------------

# v0 = [0, 5, 1]: agent 0 gets good 2, agent 1 gets goods 0 and 1.
GAP_VALUES = [[0, 5, 1], [3, 3, 1]]
GAP_ALLOC = (1, 1, 0)


def test_goods_requires_an_explicit_trim_policy():
    with pytest.raises(SpecGapError, match="SPEC_GAPS.md"):
        is_efx_goods(GAP_ALLOC, GAP_VALUES)
    with pytest.raises(SpecGapError, match="SPEC_GAPS.md"):
        exhaust(GAP_VALUES, GOODS)
    with pytest.raises(ValueError, match="unknown goods trim"):
        is_efx_goods(GAP_ALLOC, GAP_VALUES, trim="whatever")
    # chores has no such knob, and offering one is an error
    with pytest.raises(ValueError, match="meaningless"):
        exhaust(GAP_VALUES, CHORES, goods_trim=TRIM_ALL)


def test_the_two_goods_readings_really_differ():
    """Why the gap matters: the policies disagree on this instance."""
    assert is_efx_goods(GAP_ALLOC, GAP_VALUES, trim=TRIM_POSITIVE)
    assert not is_efx_goods(GAP_ALLOC, GAP_VALUES, trim=TRIM_ALL)
    assert goods_violation(GAP_ALLOC, GAP_VALUES, trim=TRIM_ALL) == (0, 1, 0)


def test_spec_gaps_file_documents_the_open_question():
    text = (ROOT / "record" / "SPEC_GAPS.md").read_text()
    assert "GAP-1" in text
    assert TRIM_POSITIVE in text and TRIM_ALL in text
    assert "EFX0" in text


# --------------------------------------------------------------------------
# 6. exhaust == brute force (hard requirement 4 accounting)
# --------------------------------------------------------------------------

CROSS_CHECK_MATRICES = [
    pytest.param([[2, 2, 1], [1, 1, 3]], id="duplicate-columns"),
    pytest.param([[1, 1, 2], [1, 1, 2], [3, 1, 1]], id="duplicate-rows-and-columns"),
    pytest.param([[1, 2, 3], [3, 1, 2], [2, 3, 1]], id="all-distinct"),
    pytest.param([[0, 5, 0], [1, 0, 1], [2, 2, 2]], id="zeros"),
    pytest.param([["1/2", "2/3", 1], ["3/4", "1/5", 0]], id="fractions"),
    pytest.param([[7]], id="n1-m1"),
    pytest.param([[1, 1], [1, 1], [1, 1]], id="all-identical"),
    pytest.param(
        [[20, 20, 20, 1, 1, 7], [20, 20, 20, 1, 1, 7],
         [20, 20, 20, 7, 7, 1], [20, 20, 20, 7, 7, 1]],
        id="hetao-n4-truncated-to-m6",
    ),
]


@pytest.mark.parametrize("costs", CROSS_CHECK_MATRICES)
@pytest.mark.parametrize(
    "mode,trim",
    [(CHORES, None), (GOODS, TRIM_POSITIVE), (GOODS, TRIM_ALL)],
)
def test_exhaust_matches_brute_force(costs, mode, trim):
    kwargs = {} if trim is None else {"goods_trim": trim}
    fast = exhaust(costs, mode, double_check=True, **kwargs)
    slow_result = brute_force(costs, mode, **kwargs)
    assert fast.total_allocations == slow_result.total_allocations
    assert fast.allocations_checked == slow_result.allocations_checked
    assert fast.efx_count == slow_result.efx_count
    assert fast.exhaustive and slow_result.exhaustive
    # Row/column collapses must not change the counts either.
    plain = exhaust(costs, mode, use_row_symmetry=False, double_check=True, **kwargs)
    assert plain.efx_count == fast.efx_count
    assert plain.allocations_checked == fast.allocations_checked
    if fast.witness is not None:
        literal = (
            is_efx_chores(fast.witness, costs)
            if mode == CHORES
            else is_efx_goods(fast.witness, costs, trim=trim)
        )
        assert literal


@pytest.mark.parametrize("costs", CROSS_CHECK_MATRICES)
def test_symmetry_classes_never_exceed_the_raw_space(costs):
    result = exhaust(costs, CHORES)
    assert result.classes_checked <= result.total_allocations
    assert result.classes_checked <= class_upper_bound(costs)


def test_scaling_the_whole_matrix_changes_nothing():
    fractional = [["1/2", "1/3", "5/6"], ["2/3", "1/6", 1], [0, "1/2", "1/2"]]
    scaled = [[6 * Fraction(x) for x in row] for row in fractional]
    a = exhaust(fractional, CHORES, double_check=True)
    b = exhaust(scaled, CHORES, double_check=True)
    assert (a.efx_count, a.allocations_checked) == (b.efx_count, b.allocations_checked)
    assert a.efx_count == brute_force(fractional, CHORES).efx_count


def test_exhaust_refuses_instead_of_hanging():
    big = [[i * 7 + g for g in range(30)] for i in range(3)]
    with pytest.raises(ExhaustTooLarge):
        exhaust(big, CHORES, max_classes=1000)
    with pytest.raises(ExhaustTooLarge):
        brute_force(big, CHORES)


def test_exhaust_reports_n_to_the_m_exactly():
    for costs, expected in (
        ([[1, 2], [3, 4]], 2**2),
        ([[1, 2, 3], [3, 1, 2], [2, 3, 1]], 3**3),
        ([[1, 1, 1, 1, 1], [2, 2, 2, 2, 2], [3, 3, 3, 3, 3]], 3**5),
    ):
        result = exhaust(costs, CHORES)
        assert result.total_allocations == expected
        assert result.allocations_checked == expected


# --------------------------------------------------------------------------
# 7. He-Tao: no chore EFX allocation (hard requirement 3)
# --------------------------------------------------------------------------


def test_hetao_schema_loads_with_our_own_parser():
    instances = load_instances(HETAO)
    assert {inst.id for inst in instances} == {
        "theorem1-n4-table1",
        "theorem1-n5-appendix-a",
    }
    for inst in instances:
        assert inst.mode == CHORES
        assert all(len(row) == inst.m for row in inst.costs)
        assert all(x >= 0 for row in inst.costs for x in row)


def test_hetao_has_no_chores_efx_allocation():
    """Hard requirement 3: exhaust, and assert efx_count == 0 everywhere."""
    instances = load_instances(HETAO)
    assert instances
    for inst in instances:
        # The n=4 instance is small enough to re-check every symmetry class
        # with the literal Fraction predicate; the n=5 one re-checks positives.
        result = exhaust(
            inst.costs, CHORES, double_check=inst.n**inst.m <= 10**8
        )
        assert result.exhaustive
        assert result.allocations_checked == inst.n**inst.m
        assert result.efx_count == 0, f"{inst.id} is not a counterexample"
        assert result.witness is None


def test_hetao_n4_is_exhausted_without_the_row_collapse_too():
    inst = next(x for x in load_instances(HETAO) if x.id == "theorem1-n4-table1")
    result = exhaust(inst.costs, CHORES, use_row_symmetry=False, double_check=True)
    assert result.allocations_checked == 4**13 == result.total_allocations
    assert result.classes_checked == class_upper_bound(inst.costs)
    assert result.efx_count == 0


def test_hetao_n4_first_three_chores_are_the_expensive_block():
    """Cheap guard that the stored matrix is still He-Tao Table 1."""
    inst = next(x for x in load_instances(HETAO) if x.id == "theorem1-n4-table1")
    assert inst.costs[0] == inst.costs[1]
    assert inst.costs[2] == inst.costs[3]
    assert [int(x) for x in inst.costs[0]] == [20] * 3 + [1] * 5 + [7] * 5
    assert [int(x) for x in inst.costs[2]] == [20] * 3 + [7] * 5 + [1] * 5


@slow
def test_hetao_n5_literal_predicate_on_every_class():
    inst = next(x for x in load_instances(HETAO) if x.id == "theorem1-n5-appendix-a")
    result = exhaust(inst.costs, CHORES, double_check=True)
    assert result.allocations_checked == 5**18
    assert result.efx_count == 0


@slow
def test_hetao_n5_without_the_row_collapse():
    inst = next(x for x in load_instances(HETAO) if x.id == "theorem1-n5-appendix-a")
    result = exhaust(inst.costs, CHORES, use_row_symmetry=False)
    assert result.allocations_checked == 5**18
    assert result.classes_checked == class_upper_bound(inst.costs)
    assert result.efx_count == 0


# --------------------------------------------------------------------------
# 8. positive fixtures: the predicate is not vacuously strict
# --------------------------------------------------------------------------


def test_handmade_positive_chores_fixture():
    costs = [[1, 2, 3], [3, 1, 2], [2, 3, 1]]
    result = exhaust(costs, CHORES, double_check=True)
    assert result.allocations_checked == 3**3
    assert result.efx_count > 0
    assert is_efx_chores(result.witness, costs)
    # Every agent taking one chore leaves 0 after the trim.
    assert is_efx_chores((0, 1, 2), costs)


def test_hetao_matrix_truncated_below_2n_becomes_positive():
    """Same matrix family as the counterexample, but m = 6 <= 2n = 8.

    A predicate that says "no EFX" everywhere would pass the He-Tao test for
    the wrong reason; this fixture fails unless the checker can still say yes.
    """
    costs = [
        [20, 20, 20, 1, 1, 7],
        [20, 20, 20, 1, 1, 7],
        [20, 20, 20, 7, 7, 1],
        [20, 20, 20, 7, 7, 1],
    ]
    result = exhaust(costs, CHORES, double_check=True)
    assert result.allocations_checked == 4**6
    assert result.efx_count > 0
    assert is_efx_chores(result.witness, costs)


def test_positive_goods_fixture_under_both_policies():
    values = [[3, 1, 1], [1, 3, 1], [1, 1, 3]]
    for trim in (TRIM_POSITIVE, TRIM_ALL):
        result = exhaust(values, GOODS, goods_trim=trim, double_check=True)
        assert result.efx_count > 0
        assert is_efx_goods(result.witness, values, trim=trim)


# --------------------------------------------------------------------------
# 9. hard requirement 6: random n=3, m=6 chores instances must have EFX
# --------------------------------------------------------------------------

# KNOWN.md: additive chores EFX exists whenever m <= 2n
# (Kobayashi-Mahara-Sakamoto, arXiv:2305.04168). For n = 3, m = 6 is exactly
# the closed boundary, so efx_count == 0 there means the predicate is wrong,
# not that a counterexample was found. A predicate trimming the wrong bundle
# reports no EFX allocation on essentially every one of these instances.
DRAWS = {
    "positive-ints": lambda rng: rng.randint(1, 9),
    "ints-with-zeros": lambda rng: rng.randint(0, 9),
    "small-range": lambda rng: rng.randint(1, 3),
    "fractions": lambda rng: f"{rng.randint(1, 20)}/{rng.randint(1, 9)}",
    "fractions-with-zeros": lambda rng: f"{rng.randint(0, 20)}/{rng.randint(1, 9)}",
}


@pytest.mark.parametrize("draw_name", sorted(DRAWS))
def test_random_n3_m6_chores_instances_have_efx(draw_name):
    draw = DRAWS[draw_name]
    rng = random.Random(f"verifier_b/{draw_name}")
    for trial in range(40):
        costs = [[draw(rng) for _ in range(6)] for _ in range(3)]
        result = exhaust(costs, CHORES)
        assert result.allocations_checked == 3**6
        assert result.efx_count > 0, (
            f"{draw_name} trial {trial}: no EFX allocation for m=6 <= 2n, "
            f"which contradicts KNOWN.md; costs={costs}"
        )
        assert is_efx_chores(result.witness, costs)


def test_random_instances_agree_with_brute_force():
    rng = random.Random("verifier_b/cross-check")
    for _ in range(25):
        n = rng.randint(2, 4)
        m = rng.randint(0, 5)
        costs = [[rng.randint(0, 4) for _ in range(m)] for _ in range(n)]
        fast = exhaust(costs, CHORES, double_check=True)
        slow_result = brute_force(costs, CHORES)
        assert (fast.allocations_checked, fast.efx_count) == (
            slow_result.allocations_checked,
            slow_result.efx_count,
        ), costs
        for trim in (TRIM_POSITIVE, TRIM_ALL):
            fast_g = exhaust(costs, GOODS, goods_trim=trim, double_check=True)
            slow_g = brute_force(costs, GOODS, goods_trim=trim)
            assert fast_g.efx_count == slow_g.efx_count, (costs, trim)


def test_raw_enumeration_agrees_with_the_predicate_on_a_fixed_instance():
    """No occupancy machinery at all: plain product() over N**m."""
    costs = [[2, 2, 1], [1, 1, 3], [3, 1, 2]]
    raw = sum(1 for a in product(range(3), repeat=3) if is_efx_chores(a, costs))
    assert exhaust(costs, CHORES).efx_count == raw


# --------------------------------------------------------------------------
# 10. CLI (hard requirement 4)
# --------------------------------------------------------------------------


def run_cli(*args, expect_returncode=0):
    done = subprocess.run(
        [sys.executable, "-m", "verifier_b.cli", *args],
        cwd=ROOT,
        capture_output=True,
        text=True,
    )
    assert done.returncode == expect_returncode, done.stderr or done.stdout
    return done


def test_cli_on_hetao_prints_the_required_fields():
    done = run_cli("artifacts/hetao.json", "--mode", "chores")
    out = done.stdout
    for field in ("n =", "m =", "n**m =", "allocations_checked =", "efx_count ="):
        assert field in out, out
    assert "efx_count = 0" in out
    assert f"allocations_checked = {4 ** 13}" in out
    assert f"allocations_checked = {5 ** 18}" in out
    assert "NO EFX ALLOCATION EXISTS" in out
    assert "witness_allocation" not in out


def test_cli_json_output_is_exhaustive_and_zero():
    done = run_cli("artifacts/hetao.json", "--mode", "chores", "--json")
    payload = json.loads(done.stdout)
    assert len(payload["instances"]) == 2
    for item in payload["instances"]:
        assert item["efx_count"] == 0
        assert item["allocations_checked"] == item["n"] ** item["m"]
        assert item["allocations_checked"] == item["n**m"]
        assert item["witness_allocation"] is None


def test_cli_expect_no_efx_fails_loudly_on_a_positive_instance(tmp_path):
    path = tmp_path / "positive.json"
    path.write_text(
        json.dumps({"id": "positive", "mode": "chores", "costs": [[1, 2], [2, 1]]})
    )
    done = run_cli(str(path), "--mode", "chores")
    # Both split allocations are EFX; both hoarding allocations are not.
    assert "efx_count = 2" in done.stdout
    assert "witness_allocation" in done.stdout
    assert "EFX ALLOCATION EXISTS" in done.stdout
    failed = run_cli(str(path), "--expect-no-efx", expect_returncode=2)
    assert "expectation FAILED" in failed.stdout


def test_cli_accepts_a_bare_matrix_file(tmp_path):
    path = tmp_path / "bare.json"
    path.write_text(json.dumps([[1, "1/2", 0], [2, 1, 1], [1, 1, 1]]))
    done = run_cli(str(path), "--mode", "chores", "--json")
    payload = json.loads(done.stdout)
    assert payload["instances"][0]["allocations_checked"] == 3**3


def test_cli_refuses_to_guess_the_goods_policy(tmp_path):
    path = tmp_path / "goods.json"
    path.write_text(json.dumps({"id": "g", "costs": [[1, 0], [0, 1]]}))
    done = run_cli(path.as_posix(), "--mode", "goods", expect_returncode=1)
    assert "SPEC_GAPS.md" in done.stderr
    ok = run_cli(path.as_posix(), "--mode", "goods", "--goods-trim", "all", "--json")
    assert json.loads(ok.stdout)["instances"][0]["goods_trim"] == "all"


def test_cli_will_not_reinterpret_a_declared_mode():
    done = run_cli("artifacts/hetao.json", "--mode", "goods",
                   "--goods-trim", "all", expect_returncode=1)
    assert "refusing to reinterpret" in done.stderr


def test_cli_instance_filter_and_double_check():
    done = run_cli(
        "artifacts/hetao.json",
        "--mode",
        "chores",
        "--instance",
        "theorem1-n4-table1",
        "--double-check",
    )
    assert done.stdout.count("instance: ") == 1
    assert "double_checked = True" in done.stdout
    assert "efx_count = 0" in done.stdout
    run_cli("artifacts/hetao.json", "--instance", "nope", expect_returncode=1)
