"""Independent finite controls for row ranges, degree seven, and sphere counts."""
from collections import Counter
from fractions import Fraction
from itertools import product
from math import comb
from random import Random

from bilinear_controls import bilinear_descent, interpolation_elements
from eighteen_controls import pair_values
from frobenius_controls import conjugate_matrices
from norm_controls import Field
from paired_controls import combined
from search_packing import distribution
from verify import require


def packing_rows():
    # Full digit-score convolution, independently of the truncated two-sign recurrence.
    rows = []
    for n in range(10):
        spec = tuple((2*a, 1) for a in [2]*min(n, 8)+([3] if n == 9 else []))
        row = distribution(spec)
        rows.append([row[2*e] if 2*e < len(row) else 0 for e in range(6)])
    return rows


def packing_controls():
    count = 2**9*(comb(8, 5)+comb(8, 4)+comb(8, 2))
    require(packing_rows()[-1][5] == count == 78848, "independent binomial count")
    # Exhaustive small spheres exercise mixed-radix matching, not the large word cube.
    triples = 0
    for alphabets in ([2, 2], [3, 2], [2, 1, 2]):
        groups = {}
        for word in product(*(range(2*a) for a in alphabets)):
            norm = sum((2*x-(2*a-1))**2 for x, a in zip(word, alphabets))
            code, place = 0, 1
            for x, a in zip(word, alphabets):
                code += x*place
                place *= 4*a-1
            groups.setdefault(norm, []).append(code)
        for words in groups.values():
            for a, b, c in product(words, repeat=3):
                require((a+b == 2*c) == (a == b == c), "small mixed matching")
                triples += 1
    return {"independent_table_entries": 60, "binomial_coefficient": str(count),
            "exhaustive_small_matching_triples": triples}


def digit_controls():
    reports = []
    wrong_four_power = 0
    for B, k, lengths in [(5, 1, (2, 2, 4)), (7, 1, (2, 4, 6)), (5, 2, (2, 2, 4))]:
        r = 2
        entries = []
        for L in lengths:
            row = []
            for digits in product(range(1, L+1), repeat=k):
                row.append((sum(a*B**i for i, a in enumerate(digits)), tuple(a % r for a in digits)))
            entries.append(row)
        # k=1 exhausts every matrix. k=2 exhausts bottom-row draws for
        # twelve reproducible top-row configurations; each retained label group is complete.
        if k == 1:
            tops = list(product(entries[0], repeat=3))
        else:
            rng = Random(191702)
            tops = [tuple([entries[0][0]]*3)]+[
                tuple(rng.choice(entries[0]) for _ in range(3)) for _ in range(11)]
        total_matrices = groups_checked = tails_checked = 0
        pstar = Fraction(r, lengths[1])**2*Fraction(r, lengths[2])**2
        for top in tops:
            mids = list(product(entries[1], repeat=3)) if k == 1 else [top]
            counts, tails, moments = Counter(), Counter(), Counter()
            for middle in mids:
                for bottom in product(entries[2], repeat=3):
                    rows = [top, middle, bottom]
                    labels = tuple(x[1] for row in rows for x in row)
                    counts[labels] += 1
                    matrix = [[x[0] for x in row] for row in rows]
                    # With unit C11, these four Schur minors vanish exactly when all minors do.
                    minors = [matrix[0][0]*matrix[i][v]-matrix[i][0]*matrix[0][v]
                              for i in (1, 2) for v in (1, 2)]
                    b = 0
                    for j in range(1, k+1):
                        if all(m % (B**j) == 0 for m in minors):
                            tails[labels, j] += 1
                            b = j
                    moments[labels] += B**b
                    total_matrices += 1
            for labels, total in counts.items():
                for j in range(1, k+1):
                    tail = Fraction(tails[labels, j], total)
                    require(tail <= pstar**j, "conditional row-digit tail")
                    wrong_four_power += tail > Fraction(r, lengths[2])**(4*j)
                    tails_checked += 1
                require(Fraction(moments[labels], total) <=
                        1+sum((B*pstar)**j for j in range(1, k+1)), "finite moment bound")
                groups_checked += 1
        reports.append({"B": B, "k": k, "r": r, "row_lengths": lengths,
            "enumerated_matrices": total_matrices, "complete_conditioned_groups": groups_checked,
            "tail_inequalities": tails_checked, "all_top_rows_enumerated": k == 1})
    require(wrong_four_power > 0, "wrong uniform-range tail rejected")
    return {"cases": reports, "incorrect_four_power_tail_counterexamples": wrong_four_power,
            "scope": "finite tail and finite moment controls; not the universal probability theorem"}


def field_controls():
    p = 37
    # A fixed irreducible degree-seven polynomial is checked by Rabin's criterion.
    modulus = [1, 1, 0, 0, 0, 0, 0, 1]
    field = Field(p, modulus)
    require(field.irreducible(), "degree-seven fixture irreducible")
    rng = Random(191703)
    u = next(a for a in range(p) if (a*a-a+1) % p == 0)
    nodes = interpolation_elements(field, 13)
    matrix = [[tuple(rng.randrange(p) for _ in range(7)) for _ in range(3)] for _ in range(3)]
    conjugates = conjugate_matrices(field, matrix)
    paired = [pair_values(field, conjugates[2*v+1], conjugates[2*v+2], u) for v in range(3)]
    expected = field.power(field.determinant(matrix), (p**7-1)//(p-1))
    total = field.zero
    descents = wrong_descent = 0
    for index, pattern in enumerate(product(range(18), repeat=3)):
        # Explicitly sum every one of the 18^3 extension-field determinants.
        a = combined(field, conjugates[0], paired, pattern)
        det = field.determinant(a)
        total = field.add(total, det)
        if index < 24:
            require(bilinear_descent(field, a, nodes) == det[0], "degree-seven descent")
            wrong_descent += bilinear_descent(field, a, nodes[:-1]) != det[0]
            descents += 1
    require(total == field.scale(expected, 27), "degree-seven enumerated norm")
    require(field.scale(total, pow(27, -1, p)) == expected, "degree-seven normalization")
    require(total != expected and wrong_descent > 0, "degree-seven negative controls")
    return {"prime": p, "degree": 7, "modulus_low_degree_first": modulus, "root": u,
        "matrices_fully_enumerated": 1, "patterns_enumerated": 18**3,
        "sampled_thirteen_node_descents": descents, "omitted_node_counterexamples": wrong_descent,
        "omitted_normalization_rejected": True,
        "scope": "finite implementation controls; the universal norm theorem is proved separately in Lean"}


if __name__ == "__main__":
    import json
    print(json.dumps({"packing": packing_controls(), "digits": digit_controls(), "field": field_controls()}, indent=2))
