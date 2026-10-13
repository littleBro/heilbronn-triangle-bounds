"""Finite rank-window branch bounds; no global packing optimality claim."""
from functools import lru_cache
from itertools import combinations
from math import prod
from pathlib import Path
import heapq
import json

ROOT = Path(__file__).resolve().parents[1]
TARGET = 25*18**6


def digit_energy(a, d):
    r = abs(2*d-(2*a-1))//2
    return r*(r+1)//2


def prefix_tables(alphabets):
    rows = [[1]]
    for a in alphabets:
        row = [0]*(len(rows[-1])+a*(a-1)//2)
        for e, c in enumerate(rows[-1]):
            for d in range(2*a):
                row[e+digit_energy(a, d)] += c
        rows.append(row)
    return rows


def at(row, e):
    return row[e] if 0 <= e < len(row) else 0


def unrank(alphabets, rows, e, rank):
    """Encoded word at a zero-based rank, without enumerating the layer."""
    assert 0 <= rank < at(rows[-1], e)
    place, encoded = prod(4*a-1 for a in alphabets), 0
    for i in reversed(range(len(alphabets))):
        a = alphabets[i]
        place //= 4*a-1
        for d in range(2*a):
            block = at(rows[i], e-digit_energy(a, d))
            if rank < block:
                encoded += d*place
                e -= digit_energy(a, d)
                break
            rank -= block
        else:
            raise AssertionError("rank exceeds layer")
    assert e == rank == 0
    return encoded


def best_window(alphabets, rows, e, target, max_k):
    """Search all ranks, pruning with monotonicity of the encoded word list.

    For lo <= r <= hi, code(r+target-1)-code(r) is at least
    code(lo+target-1)-code(hi). A pruned interval therefore cannot improve
    the current feasible bound. Only scalar word ranks are evaluated.
    """
    @lru_cache(maxsize=65536)
    def code(rank):
        return unrank(alphabets, rows, e, rank)
    best, evaluated, queue = None, 0, []
    def push(lo, hi):
        if lo <= hi:
            bound = 2*(code(lo+target-1)-code(hi))+1
            if bound < max_k:
                heapq.heappush(queue, (bound, lo, hi))
    push(0, at(rows[-1], e)-target)
    while queue:
        bound, lo, hi = heapq.heappop(queue)
        if bound >= max_k:
            continue
        rank = (lo+hi)//2
        lower, upper = code(rank), code(rank+target-1)+1
        k = 2*(upper-lower)-1
        evaluated += 1
        if k < max_k:
            max_k, best = k, (k, rank, lower, upper)
        push(lo, rank-1)
        push(rank+1, hi)
    return best, evaluated


def search():
    best, evaluated, layers = None, 0, 0
    best_k = 15**7*19**4
    for positions in combinations(range(11), 4):
        alphabets = [5 if i in positions else 4 for i in range(11)]
        rows = prefix_tables(alphabets)
        for e, count in enumerate(rows[-1]):
            if count < TARGET:
                continue
            layers += 1
            current, visited = best_window(alphabets, rows, e, TARGET, best_k)
            evaluated += visited
            if current is None:
                continue
            item = {"half_alphabets_low_first": alphabets, "energy": e,
                    "layer_count": count, "first_rank": current[1],
                    "lower_inclusive": current[2], "upper_exclusive": current[3],
                    "k": current[0], "box_k": prod(4*a-1 for a in alphabets)}
            best_k, best = item["k"], item
    return {"scope": "all ranks in the listed finite family via exact branch bounds; no Lean optimality proof or global packing optimality claim",
            "target": TARGET, "coordinate_orders": 330, "feasible_layers": layers,
            "initial_k": 15**7*19**4, "search_completed": True,
            "rank_windows_evaluated": evaluated,
            "best": best}


def main():
    report = search()
    (ROOT/"artifacts/trimmed-search.json").write_text(json.dumps(report, indent=2)+"\n",
                                                   encoding="utf-8", newline="\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
