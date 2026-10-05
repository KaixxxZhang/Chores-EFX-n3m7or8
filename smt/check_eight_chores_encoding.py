"""Finite exact checks of the eight-chore encoding.

The clause builders of eight_chores_z3.py and eight_chores_alt_z3.py are
compared with the brute-force EFX checker in ``efx_checker`` on exact rational
matrices and all 3**8 allocations, and five deliberately wrong predicates are
shown to disagree with the correct one.  The script also checks the zero-row
construction, the invariance of EFX under row scaling and chore permutation,
the two canonical forms, and the shared-minimum lifting step on small random
instances.  None of these checks is used in the proofs.
"""

from __future__ import annotations

import json
import random
import sys
from fractions import Fraction
from itertools import permutations, product
from pathlib import Path

import z3

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(ROOT))

import eight_chores_alt_z3 as alternative  # noqa: E402
import eight_chores_z3 as encoding  # noqa: E402
from efx_checker.efx_chores import is_efx_chores  # noqa: E402

N = tuple(range(3))
M = tuple(range(8))


def bundles_of(allocation):
    return [[g for g in M if allocation[g] == i] for i in N]


def cost_of(row, bundle):
    return sum((row[g] for g in bundle), Fraction(0))


def mutant_bad(allocation, costs, mutation):
    bundles = bundles_of(allocation)
    for i in N:
        own = cost_of(costs[i], bundles[i])
        for j in N:
            if i == j:
                continue
            other = cost_of(costs[i], bundles[j])
            if mutation == "no-trim":
                if own > other:
                    return True
                continue
            if mutation == "goods-trim":
                for g in bundles[j]:
                    if own > other - costs[i][g]:
                        return True
                continue
            for g in bundles[i]:
                if mutation == "skip-zero" and costs[i][g] == 0:
                    continue
                residual = own - costs[i][g]
                if mutation == "ge":
                    if residual >= other:
                        return True
                elif mutation == "wrong-row":
                    if residual > cost_of(costs[j], bundles[j]):
                        return True
                elif mutation in {"exact", "skip-zero"}:
                    if residual > other:
                        return True
                else:
                    raise ValueError(mutation)
    return False


def rational_matrices():
    matrices = [
        [[Fraction(0) for _ in M] for _ in N],
        [
            [Fraction(x) for x in (0, 0, 1, 1, 2, 3, 5, 8)],
            [Fraction(x) for x in (1, 0, 1, 2, 0, 3, 8, 5)],
            [Fraction(x) for x in (2, 1, 0, 3, 1, 0, 5, 8)],
        ],
        [
            [Fraction(x) for x in (3, 4, 16, 6, 4, 3, 6, 9)],
            [Fraction(x) for x in (29, 0, 4, 2, 5, 57, 19, 1)],
            [Fraction(x) for x in (55, 4, 6, 0, 11, 36, 18, 2)],
        ],
        [
            [Fraction(1, d) for d in (2, 3, 5, 7, 11, 13, 17, 19)],
            [Fraction(d, 23) for d in (0, 1, 2, 3, 5, 8, 13, 21)],
            [Fraction(d, 29) for d in (21, 13, 8, 5, 3, 2, 1, 0)],
        ],
    ]
    rng = random.Random(608)
    for _ in range(4):
        matrices.append(
            [[Fraction(rng.randrange(0, 31)) for _ in M] for _ in N]
        )
    return matrices


def eval_z3_clause(clause, variables, matrix):
    substitutions = [
        (variables[i][g], z3.Q(matrix[i][g].numerator, matrix[i][g].denominator))
        for i in N
        for g in M
    ]
    reduced = z3.simplify(z3.substitute(clause, *substitutions))
    if z3.is_true(reduced):
        return True
    if z3.is_false(reduced):
        return False
    raise AssertionError(f"concrete clause did not reduce to Boolean: {reduced}")


def check_clause_builders(matrices):
    variables = [[z3.Real(f"check_c_{i}_{g}") for g in M] for i in N]
    allocations = list(product(N, repeat=8))
    assert len(allocations) == len(set(allocations)) == 6561

    mismatches = 0
    alternative_mismatches = 0
    bad_literal_counts = set()
    alternative_literal_counts = set()
    mutation_counts = {
        "goods-trim": 0,
        "skip-zero": 0,
        "ge": 0,
        "wrong-row": 0,
        "no-trim": 0,
    }
    for allocation in allocations:
        clause = encoding.not_efx_clause(variables, allocation, variant="efx")
        alternative_clause = alternative.non_efx_clause(variables, allocation)
        bad_literal_counts.add(len(clause.children()))
        alternative_literal_counts.add(len(alternative_clause.children()))
        for matrix in matrices:
            expected_bad = not is_efx_chores(allocation, matrix)
            actual_bad = eval_z3_clause(clause, variables, matrix)
            mismatches += actual_bad != expected_bad
            alternative_bad = eval_z3_clause(alternative_clause, variables, matrix)
            alternative_mismatches += alternative_bad != expected_bad
            for mutation in mutation_counts:
                mutation_counts[mutation] += (
                    mutant_bad(allocation, matrix, mutation) != expected_bad
                )

    assert mismatches == 0
    assert alternative_mismatches == 0
    assert bad_literal_counts == {16}
    assert alternative_literal_counts == {24}
    assert all(count > 0 for count in mutation_counts.values())
    return {
        "matrices": len(matrices),
        "allocation_matrix_pairs": len(matrices) * len(allocations),
        "z3_vs_checker_mismatches": mismatches,
        "alternative_vs_checker_mismatches": alternative_mismatches,
        "literal_counts": sorted(bad_literal_counts),
        "alternative_literal_counts": sorted(alternative_literal_counts),
        "mutation_mismatches": mutation_counts,
    }


def check_zero_row():
    rng = random.Random(609)
    checked = 0
    for zero_agent in N:
        other_agents = [i for i in N if i != zero_agent]
        for _ in range(20):
            matrix = [
                [Fraction(rng.randrange(0, 101)) for _ in M] for _ in N
            ]
            matrix[zero_agent] = [Fraction(0) for _ in M]
            for singleton_chores in permutations(M, 2):
                allocation = [zero_agent] * 8
                allocation[singleton_chores[0]] = other_agents[0]
                allocation[singleton_chores[1]] = other_agents[1]
                assert is_efx_chores(allocation, matrix)
                checked += 1
    return checked


def check_invariance():
    rng = random.Random(610)
    scaling_checks = 0
    permutation_checks = 0
    for _ in range(12):
        matrix = [[Fraction(rng.randrange(0, 41)) for _ in M] for _ in N]
        if any(sum(row) == 0 for row in matrix):
            matrix[0][0] = Fraction(1)
        scales = [Fraction(rng.randrange(1, 11), rng.randrange(1, 11)) for _ in N]
        scaled = [[matrix[i][g] * scales[i] for g in M] for i in N]
        chore_perm = list(M)
        rng.shuffle(chore_perm)
        permuted = [[matrix[i][chore_perm[g]] for g in M] for i in N]

        for allocation in product(N, repeat=8):
            base = is_efx_chores(allocation, matrix)
            assert base == is_efx_chores(allocation, scaled)
            scaling_checks += 1

            permuted_allocation = tuple(allocation[chore_perm[g]] for g in M)
            assert base == is_efx_chores(permuted_allocation, permuted)
            permutation_checks += 1
    return scaling_checks, permutation_checks


def check_canonical_form():
    x = [z3.Real(f"lex_x_{i}") for i in N]
    y = [z3.Real(f"lex_y_{i}") for i in N]
    solver = z3.Solver()
    solver.add(*(x[i] == y[i] for i in N))
    solver.add(z3.Not(encoding.lex_le(x, y)))
    assert solver.check() == z3.unsat

    rng = random.Random(611)
    canonicalized = 0
    for _ in range(1000):
        matrix = [[Fraction(rng.randrange(0, 31)) for _ in M] for _ in N]
        if any(sum(row) == 0 for row in matrix):
            continue
        normalized = [[value / sum(row) for value in row] for row in matrix]
        normalized.sort(key=lambda row: (min(row), max(row)))
        columns = sorted(zip(*normalized))
        canonical = [list(row) for row in zip(*columns)]
        invariants = [(min(row), max(row)) for row in canonical]
        assert invariants == sorted(invariants)
        assert list(zip(*canonical)) == sorted(zip(*canonical))
        canonicalized += 1
    return canonicalized


def check_residual_canonical_form():
    """Construct the pinned/sorted representative of disjoint-argmin orbits."""
    rng = random.Random(612)
    checked = 0
    for _ in range(1000):
        # Give every row a nonempty, pairwise-disjoint zero-valued argmin
        # set, with ties allowed inside a row.
        owner = [None] * len(M)
        for i in N:
            owner[i] = i
        for g in range(len(N), len(M)):
            choice = rng.randrange(5)
            owner[g] = choice if choice in N else None
        matrix = []
        for i in N:
            row = [
                Fraction(0) if owner[g] == i else Fraction(rng.randrange(1, 31))
                for g in M
            ]
            matrix.append(row)
        shuffle = list(M)
        rng.shuffle(shuffle)
        matrix = [[row[g] for g in shuffle] for row in matrix]

        selected = []
        argmins = []
        for row in matrix:
            minimum = min(row)
            argmin = {g for g in M if row[g] == minimum}
            argmins.append(argmin)
            selected.append(min(argmin))
        assert all(argmins[p].isdisjoint(argmins[q]) for p in N for q in N if p < q)
        assert len(set(selected)) == len(N)

        normalized = [[value / sum(row) for value in row] for row in matrix]
        remaining = [g for g in M if g not in selected]
        remaining.sort(key=lambda g: tuple(normalized[i][g] for i in N))
        order = selected + remaining
        canonical = [[normalized[i][g] for g in order] for i in N]

        assert all(sum(row) == 1 for row in canonical)
        assert all(canonical[i][i] == min(canonical[i]) for i in N)
        canonical_argmins = [
            {g for g in M if canonical[i][g] == min(canonical[i])} for i in N
        ]
        assert all(
            canonical_argmins[p].isdisjoint(canonical_argmins[q])
            for p in N
            for q in N
            if p < q
        )
        assert list(zip(*canonical))[len(N) :] == sorted(
            list(zip(*canonical))[len(N) :]
        )
        checked += 1
    return checked


def check_shared_minimum_lifting():
    """Exercise the m=7 theorem + matching-insertion proof on exact matrices."""

    def edge(matrix, i, bundle, bundles):
        if not bundle:
            return True
        own = cost_of(matrix[i], bundle)
        residual = own - min(matrix[i][g] for g in bundle)
        floor = min(cost_of(matrix[i], other) for other in bundles)
        return residual <= floor

    def has_perfect_matching(matrix, bundles):
        return any(
            all(edge(matrix, i, bundles[matching[i]], bundles) for i in N)
            for matching in permutations(N)
        )

    rng = random.Random(613)
    checked = 0
    remaining = tuple(g for g in M if g != 0)
    for _ in range(30):
        matrix = [
            [Fraction(rng.randrange(1, 51)) for _ in M] for _ in N
        ]
        matrix[0][0] = Fraction(0)
        matrix[1][0] = Fraction(0)

        efx_partition = None
        for owners in product(N, repeat=len(remaining)):
            bundles = [[] for _ in N]
            for g, i in zip(remaining, owners):
                bundles[i].append(g)
            if all(edge(matrix, i, bundles[i], bundles) for i in N):
                efx_partition = bundles
                break
        assert efx_partition is not None

        insertion_found = False
        for target in N:
            lifted = [bundle[:] for bundle in efx_partition]
            lifted[target].append(0)
            if has_perfect_matching(matrix, lifted):
                insertion_found = True
                break
        assert insertion_found
        checked += 1
    return checked


def main() -> int:
    matrices = rational_matrices()
    clause = check_clause_builders(matrices)
    zero_rows = check_zero_row()
    scaling, permutation = check_invariance()
    canonicalized = check_canonical_form()
    residual_canonicalized = check_residual_canonical_form()
    shared_minimum_lifted = check_shared_minimum_lifting()
    print(
        json.dumps(
            {
                "scope": "n=3,m=8 exact rational checks",
                "clause_builder": clause,
                "zero_row_constructions_checked": zero_rows,
                "row_scaling_allocation_checks": scaling,
                "chore_permutation_allocation_checks": permutation,
                "canonical_representatives_checked": canonicalized,
                "residual_canonical_representatives_checked": residual_canonicalized,
                "shared_minimum_lifting_instances_checked": shared_minimum_lifted,
                "result": "pass",
            },
            indent=2,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
