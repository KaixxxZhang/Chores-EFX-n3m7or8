"""Independent literal 3^7 occupancy check for artifacts/s5_matrices.json."""

from __future__ import annotations

import json
from collections import Counter
from itertools import combinations, product
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MATRICES = ROOT / "artifacts" / "s5_matrices.json"
N, M = 3, 7


def bundles(allocation):
    return [[g for g, owner in enumerate(allocation) if owner == i] for i in range(N)]


def is_efx_chores(allocation, costs):
    owned = bundles(allocation)
    for i in range(N):
        if not owned[i]:
            continue
        own_cost = sum(costs[i][g] for g in owned[i])
        for j in range(N):
            other_cost = sum(costs[i][g] for g in owned[j])
            for g in owned[i]:  # includes zero-cost chores
                if own_cost - costs[i][g] > other_cost:
                    return False
    return True


def open_class(costs):
    argmins = []
    for row in costs:
        minimum = min(row)
        argmins.append({g for g, value in enumerate(row) if value == minimum})
    disjoint = all(
        argmins[p].isdisjoint(argmins[q]) for p, q in combinations(range(N), 2)
    )
    reversals = all(
        any(
            (costs[p][g] < costs[p][h] and costs[q][g] > costs[q][h])
            or (costs[p][g] > costs[p][h] and costs[q][g] < costs[q][h])
            for g, h in combinations(range(M), 2)
        )
        for p, q in combinations(range(N), 2)
    )
    return disjoint and reversals and any(len(set(row)) >= 3 for row in costs)


def shape(allocation):
    return tuple(
        sorted((allocation.count(0), allocation.count(1), allocation.count(2)), reverse=True)
    )


def shape_key(value):
    return "+".join(str(part) for part in value)


def main():
    document = json.loads(MATRICES.read_text())
    report = []
    for instance in document["instances"]:
        costs = instance["costs"]
        if not open_class(costs):
            raise SystemExit(f"{instance['id']} is outside the open class")
        occupancy = Counter()
        for allocation in product(range(N), repeat=M):
            if is_efx_chores(allocation, costs):
                occupancy[shape(allocation)] += 1
        observed = {shape_key(key): value for key, value in occupancy.items()}
        if observed != instance["efx_occupancy"]:
            raise SystemExit(
                f"{instance['id']} occupancy mismatch: {observed} != "
                f"{instance['efx_occupancy']}"
            )
        if sum(occupancy.values()) != instance["efx_count"]:
            raise SystemExit(f"{instance['id']} EFX count mismatch")
        report.append(
            {
                "id": instance["id"],
                "open_class": True,
                "allocations_checked": N**M,
                "efx_count": sum(occupancy.values()),
                "efx_occupancy": observed,
            }
        )
    print(json.dumps({"instances": report}, indent=2))


if __name__ == "__main__":
    main()
