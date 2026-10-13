"""Exact controls for two-factor interpolation and the selected energy layer."""
from itertools import product
from math import factorial
from random import Random

from norm_controls import Field, determinant, evaluate
from verify import require


def interpolation_elements(field, count):
    require(count <= field.p, "distinct bilinear nodes")
    elements = []
    for t in range(count):
        polynomial, denominator = [1], 1
        for u in range(count):
            if u == t:
                continue
            new = [0]*(len(polynomial)+1)
            for j, a in enumerate(polynomial):
                new[j] -= u*a
                new[j+1] += a
            polynomial = [a % field.p for a in new]
            denominator = denominator*(t-u) % field.p
        elements.append(field.scale(field.reduce(polynomial), pow(denominator, -1, field.p)))
    return elements


def bilinear_descent(field, matrix, elements):
    return sum(determinant([
        [evaluate(a, t, field.p) for a in matrix[0]],
        [evaluate(a, t, field.p) for a in matrix[1]],
        [field.mul(c, a)[0] for a in matrix[2]],
    ], field.p) for t, c in enumerate(elements)) % field.p


def field_controls():
    rng = Random(191025)
    fixtures = [(11, [4, 1, 0, 1]), (17, [3, 1, 0, 0, 0, 1]),
                (41, [1, 1]+[0]*11+[1])]
    reports = []
    wrong_third_row = 0
    for p, modulus in fixtures:
        field = Field(p, modulus)
        require(field.irreducible(), "bilinear fixture irreducible")
        nodes = 2*field.d-1
        elements = interpolation_elements(field, nodes)
        for i, j in product(range(field.d), repeat=2):
            actual = field.zero
            for t, c in enumerate(elements):
                actual = field.add(actual, field.scale(c, pow(t, i+j, p)))
            require(actual == field.power(field.x, i+j), "bilinear basis product")
        short = interpolation_elements(field, nodes-1)
        actual = field.zero
        for t, c in enumerate(short):
            actual = field.add(actual, field.scale(c, pow(t, 2*field.d-2, p)))
        require(actual != field.power(field.x, 2*field.d-2), "too few bilinear nodes control")
        corrupted = elements[:]
        corrupted[0] = field.add(corrupted[0], field.one)
        actual = field.zero
        for c in corrupted:
            actual = field.add(actual, c)
        require(actual != field.one, "corrupted bilinear element control")
        matrices = [[[tuple(rng.randrange(p) for _ in range(field.d)) for _ in range(3)]
                     for _ in range(3)] for _ in range(4)]
        labels = [field.zero, field.one, field.x]
        matrices.append([[field.one]*3, labels, [field.mul(a, a) for a in labels]])
        for matrix in matrices:
            expected = field.determinant(matrix)[0]
            require(bilinear_descent(field, matrix, elements) == expected, "bilinear determinant")
            incorrect = sum(c[0]*determinant(
                [[evaluate(a, t, p) for a in row] for row in matrix], p)
                for t, c in enumerate(elements)) % p
            wrong_third_row += incorrect != expected
        reports.append({"p": p, "degree": field.d, "modulus_low_degree_first": modulus,
                        "nodes": nodes, "basis_products": field.d**2,
                        "determinants": len(matrices)})
    require(wrong_third_row > 0, "unchanged third row must fail")
    return {"fields": reports, "negative_controls": {
        "too_few_nodes": len(fixtures), "corrupted_element": len(fixtures),
        "unchanged_third_row_detected": wrong_third_row}}


def exact_rows():
    """Full forward distributions, unlike the generator's truncated recurrence."""
    distribution = {0: 1}
    rows = [[distribution.get(e, 0) for e in range(87)]]
    for _ in range(11):
        new = {}
        for e, count in distribution.items():
            for d in range(14):
                score = ((2*d-13)**2-1)//8
                new[e+score] = new.get(e+score, 0)+count
        distribution = new
        rows.append([distribution.get(e, 0) for e in range(87)])
    require(sum(distribution.values()) == 14**11, "total word count")
    return rows


def composition_count(m, energy):
    """Independent multinomial sum over the seven absolute digit radii."""
    def visit(radius, left, remaining, denominator):
        if radius == 7:
            return factorial(m)*2**m//denominator if left == remaining == 0 else 0
        weight = radius*(radius+1)//2
        return sum(visit(radius+1, left-c, remaining-c*weight, denominator*factorial(c))
                   for c in range(left+1) if c*weight <= remaining)
    return visit(0, m, energy, 1)


def layer_controls():
    rows = exact_rows()
    require(rows[11][86] == composition_count(11, 86) == 67169169408,
            "independent exact layer count")
    for m in range(4):
        histogram = [0]*87
        for word in product(range(14), repeat=m):
            e = sum(((2*d-13)**2-1)//8 for d in word)
            histogram[e] += 1
        require(histogram == rows[m], "small exhaustive histogram")
    return rows, {"energy": 86, "count": str(rows[11][86]),
                  "independent_multinomial_count": str(composition_count(11, 86)),
                  "small_exhaustive_lengths": [0, 1, 2, 3]}
