"""He–Tao n≥4 additive chore counterexamples (arXiv:2606.08872)."""

import json
from pathlib import Path

from src.enumerator import MAX_ALLOCS, exists_efx_chores, parse_matrix

ROOT = Path(__file__).resolve().parents[1]
HETAO_PATH = ROOT / "artifacts" / "hetao.json"


def load_hetao():
    data = json.loads(HETAO_PATH.read_text())
    return data["instances"]


def test_hetao_json_schema():
    instances = load_hetao()
    assert instances
    ids = set()
    for inst in instances:
        assert inst["mode"] == "chores"
        n = inst["n"]
        m = inst["m"]
        costs = inst["costs"]
        assert n == len(costs)
        assert m == len(costs[0])
        assert all(len(row) == m for row in costs)
        parse_matrix(costs)
        assert inst["id"] not in ids
        ids.add(inst["id"])
    assert "theorem1-n4-table1" in ids


def test_hetao_n4_matches_table1():
    inst = next(x for x in load_hetao() if x["id"] == "theorem1-n4-table1")
    costs = inst["costs"]
    # Agents 1,2: A=20, B=1, C=7; agents 3,4: A=20, B=7, C=1.
    assert costs[0] == [20, 20, 20, 1, 1, 1, 1, 1, 7, 7, 7, 7, 7]
    assert costs[1] == costs[0]
    assert costs[2] == [20, 20, 20, 7, 7, 7, 7, 7, 1, 1, 1, 1, 1]
    assert costs[3] == costs[2]


def test_hetao_n5_matches_appendix_a():
    inst = next(x for x in load_hetao() if x["id"] == "theorem1-n5-appendix-a")
    # t1=2, t2=3, s=7, q=9, r=(2*3+1)*(3+2)=35; |A|=4, |B|=|C|=7.
    costs = inst["costs"]
    assert inst["n"] == 5 and inst["m"] == 18
    for i in range(2):
        assert costs[i][:4] == [35, 35, 35, 35]
        assert costs[i][4:11] == [1] * 7
        assert costs[i][11:] == [9] * 7
    for i in range(2, 5):
        assert costs[i][:4] == [35, 35, 35, 35]
        assert costs[i][4:11] == [9] * 7
        assert costs[i][11:] == [1] * 7


def test_hetao_enumerable_instances_have_no_chores_efx():
    checked = 0
    for inst in load_hetao():
        try:
            found = exists_efx_chores(inst["costs"])
        except ValueError as exc:
            if "exceeds max_allocs" in str(exc):
                continue
            raise
        assert found is False
        checked += 1
    assert checked >= 1, "expected at least the n=4 Table 1 instance to be enumerable"


def test_hetao_n4_raw_space_over_cap_but_exists_is_false():
    inst = next(x for x in load_hetao() if x["id"] == "theorem1-n4-table1")
    assert 4 ** 13 > MAX_ALLOCS
    assert exists_efx_chores(inst["costs"]) is False
