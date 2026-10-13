"""Independent lexicographic counts and exhaustive small interval controls."""
from bisect import bisect_left
from functools import lru_cache
from itertools import product
from math import prod

from verify import require


def cost(a, digit):
    return ((2*digit-(2*a-1))**2-1)//8


@lru_cache(maxsize=64)
def histograms(alphabets):
    rows = [{0: 1}]
    for a in alphabets:
        row = {}
        for e, count in rows[-1].items():
            for digit in range(2*a):
                target = e+cost(a, digit)
                row[target] = row.get(target, 0)+count
        rows.append(row)
    return rows


def count_below(alphabets, energy, cutoff):
    """Sum complete lower-coordinate blocks, reading high digits first."""
    if cutoff <= 0 or energy < 0:
        return 0
    rows = histograms(tuple(alphabets))
    radices = [4*a-1 for a in alphabets]
    if cutoff >= prod(radices):
        return rows[-1].get(energy, 0)
    places, running = [], 1
    for radix in radices:
        places.append(running)
        running *= radix
    total = 0
    for i in reversed(range(len(alphabets))):
        a = alphabets[i]
        digit = cutoff//places[i] % radices[i]
        total += sum(rows[i].get(energy-cost(a, x), 0) for x in range(min(digit, 2*a)))
        if digit >= 2*a:
            return total
        energy -= cost(a, digit)
        if energy < 0:
            return total
    return total


def finite_controls():
    cases = [[1], [2], [2,2], [1,2,2], [2,3,2], [3,2,2,1]]
    counts = triples = 0
    for alphabets in cases:
        radices = [4*a-1 for a in alphabets]
        places = [prod(radices[:i]) for i in range(len(radices))]
        layers = {}
        for digits in product(*(range(2*a) for a in alphabets)):
            e = sum(cost(a, d) for a, d in zip(alphabets, digits))
            code = sum(p*d for p, d in zip(places, digits))
            layers.setdefault(e, []).append(code)
        for e, codes in sorted(layers.items()):
            codes.sort()
            for cutoff in range(prod(radices)+2):
                require(count_below(alphabets, e, cutoff) == bisect_left(codes, cutoff), "small cutoff count")
                counts += 1
            lower, upper = codes[len(codes)//4], codes[len(codes)-1-len(codes)//4]+1
            selected = [c for c in codes if lower <= c < upper]
            shifted = [c-lower for c in selected]
            k = 2*(upper-lower)-1
            right = [k-1-2*c for c in shifted]
            require(len(set(shifted)) == len(set(right)) == len(selected), "small injections")
            require(all(0 <= u < k and 0 <= v < k for u,v in zip(shifted,right)), "small position bounds")
            for a,b,c in product(range(len(selected)), repeat=3):
                require((shifted[a]+shifted[b]+right[c] == k-1) == (a==b==c), "small matching")
                triples += 1
    return {"half_alphabets": cases, "cutoff_counts_compared_with_enumeration": counts,
            "translated_matching_triples": triples, "scope": "exhaustive on the listed small cases only"}
