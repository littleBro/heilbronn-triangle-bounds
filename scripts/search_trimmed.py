"""Bounded rank-window search on the retained mixed sphere; no optimality claim."""
from itertools import combinations
from math import prod
from pathlib import Path
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


def search():
    best, evaluated, layers = None, 0, 0
    for positions in combinations(range(11), 4):
        alphabets = [5 if i in positions else 4 for i in range(11)]
        rows = prefix_tables(alphabets)
        for e, count in enumerate(rows[-1]):
            if count < TARGET:
                continue
            layers += 1
            maximum_rank = count-TARGET
            seen = {}
            def evaluate(rank):
                if rank not in seen:
                    lo = unrank(alphabets, rows, e, rank)
                    hi = unrank(alphabets, rows, e, rank+TARGET-1)
                    seen[rank] = (2*(hi-lo)+1, rank, lo, hi)
                return seen[rank]
            current = min(evaluate(maximum_rank*i//128) for i in range(129))
            radius = maximum_rank//128+1
            for _ in range(4):
                left, right = max(0, current[1]-radius), min(maximum_rank, current[1]+radius)
                current = min(current, *(evaluate(left+(right-left)*i//64) for i in range(65)))
                radius = (right-left)//64+1
            evaluated += len(seen)
            item = {"half_alphabets_low_first": alphabets, "energy": e,
                    "layer_count": count, "first_rank": current[1],
                    "lower_inclusive": current[2], "upper_exclusive": current[3]+1,
                    "k": current[0], "box_k": prod(4*a-1 for a in alphabets)}
            if best is None or item["k"] < best["k"]:
                best = item
    return {"scope": "exact evaluations on the listed finite grids, not interval or packing optimality",
            "target": TARGET, "coordinate_orders": 330, "feasible_layers": layers,
            "coarse_grid_subdivisions": 128, "local_refinement_rounds": 4,
            "local_grid_subdivisions": 64, "distinct_windows_evaluated": evaluated,
            "best": best}


def main():
    report = search()
    (ROOT/"artifacts/trimmed-search.json").write_text(json.dumps(report, indent=2)+"\n",
                                                   encoding="utf-8", newline="\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
