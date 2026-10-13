"""Bounded, exact search in explicitly listed finite families; no optimality claim.

This optional research experiment uses only integer convolutions, one process,
and a 512-entry cache. The proof checker verifies the final witness separately.
"""
from functools import lru_cache
from itertools import combinations_with_replacement
from math import gcd, prod
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]
EVEN_DOMAINS = [(8, 10, 19), (9, 6, 13), (10, 4, 10), (11, 3, 8), (12, 3, 7)]
GENERAL_DOMAINS = [(8, 24, 34), (9, 15, 23), (10, 10, 17), (11, 7, 13),
                   (12, 6, 11), (13, 4, 9), (14, 4, 7)]


@lru_cache(maxsize=512)
def distribution(spec):
    """Quarter squared norm after subtracting each coordinate's minimum."""
    if not spec:
        return (1,)
    n, w = spec[-1]
    old = distribution(spec[:-1])
    terms = {}
    for x in range(n):
        e = w*((2*x-(n-1))**2-((n-1) % 2))//4
        terms[e] = terms.get(e, 0)+1
    row = [0]*(len(old)+max(terms))
    for e, c in enumerate(old):
        for s, m in terms.items():
            row[e+s] += m*c
    return tuple(row)


def search(target, initial_k, domains, factor):
    best_k = initial_k
    best = None
    evaluated = 0
    for dim, lo, hi in domains:
        for sizes in combinations_with_replacement(range(lo, hi+1), dim):
            digits = tuple(factor*a for a in sizes)
            k = prod(2*n-1 for n in digits)
            if k >= best_k:
                continue
            # Each digit score occurs at most twice; convolution with the
            # other coordinates bounds every coefficient by 2*total/max(n).
            if 2*prod(digits)//max(digits) < target:
                continue
            row = distribution(tuple((n, 1) for n in digits))
            count = max(row)
            evaluated += 1
            if count >= target:
                best_k = k
                best = {"k": str(k), "digit_sizes": list(digits),
                        "quarter_norm_index": row.index(count), "layer_count": str(count)}
    distribution.cache_clear()
    return {"target": str(target), "initial_k": str(initial_k),
            "domains_dimension_min_max": domains, "size_multiplier": factor,
            "histograms_evaluated": evaluated, "best_improvement": best}


def main():
    old_k = 39*35**8
    previous = search(2347506125, old_k, EVEN_DOMAINS, 2)
    paired = search(1600000000, old_k, EVEN_DOMAINS, 2)
    winner = paired["best_improvement"]
    assert winner["k"] == str(27*23**9)
    general = search(1600000000, int(winner["k"]), GENERAL_DOMAINS, 1)
    weighted = []
    for common_weights in combinations_with_replacement(range(1, 4), 9):
        for last in range(1, 4):
            weights = (*common_weights, last)
            if gcd(*weights) > 1:
                continue
            row = distribution(tuple(zip([12]*9+[14], weights)))
            weighted.append((max(row), weights, row.index(max(row))))
    strongest = max(weighted, key=lambda x: x[0])
    report = {"scope": "exact search only in the listed finite families; no global optimality claim",
              "previous_term_count_search": previous, "paired_term_count_search": paired,
              "odd_and_even_alphabet_search": general,
              "weighted_sphere_search": {"digit_sizes": [12]*9+[14], "positive_weights": [1, 2, 3],
                  "primitive_weight_vectors_evaluated": len(weighted),
                  "largest_coefficient": str(strongest[0]), "weights": strongest[1],
                  "quarter_norm_index": strongest[2]},
              "proof_boundary": "The witness has separate Lean proofs; the search procedure is not formalized."}
    (ROOT/"artifacts/packing-search.json").write_text(json.dumps(report, indent=2)+"\n",
                                                    encoding="utf-8", newline="\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
