"""Independent finite controls for the five-term expansion and mixed sphere."""
from functools import lru_cache
from itertools import product
from math import comb, prod
from random import Random

from bilinear_controls import interpolation_elements
from frobenius_controls import averaging_coefficients, conjugate_matrices, projected_descent
from norm_controls import Field, determinant
from verify import require

COEFFICIENTS = (
    ((0, 1, 1), (1, 0, 0), (0, 1, 0)),
    ((-1, 0, -1), (0, 1, 0), (1, 0, 0)),
    ((0, -1, 0), (1, 0, 1), (0, 1, 1)),
    ((-1, 1, 0), (0, 0, 1), (1, 1, 1)),
    ((1, 0, 0), (0, 1, 1), (1, 0, 1)),
)


def rotate(word, a):
    return tuple(word[(i-a) % len(word)] for i in range(len(word)))


def orbit_partition(d):
    unseen = set(product(range(5), repeat=d))
    groups = []
    while unseen:
        w = min(unseen)
        orbit = {rotate(w, a) for a in range(d)}
        require(orbit <= unseen, "rank-five disjoint orbits")
        unseen -= orbit
        groups.append((w, len(orbit)))
    return groups


def forms(field, matrix):
    return [[[tuple(sum(c[r]*matrix[r][j][v] for r in range(3)) % field.p
                     for v in range(field.d)) for j in range(3)] for c in term]
            for term in COEFFICIENTS]


def combined(field, conjugated_forms, word):
    matrix = [[field.one for _ in range(3)] for _ in range(3)]
    for a, t in enumerate(word):
        for i, j in product(range(3), repeat=2):
            matrix[i][j] = field.mul(matrix[i][j], conjugated_forms[a][t][i][j])
    return matrix


def finite_controls():
    rng = Random(19100513)
    rank_checks = 0
    for p in (2, 3, 5, 41):
        for _ in range(32):
            m = [[rng.randrange(p) for _ in range(3)] for _ in range(3)]
            actual = sum(prod(sum(c[r]*m[r][i] for r in range(3))
                              for i, c in enumerate(term)) for term in COEFFICIENTS) % p
            require(actual == determinant(m, p), "integral rank-five identity")
            rank_checks += 1
    reports = []
    missing_six = missing_weights = unaveraged = 0
    for p, modulus in [(11, [4, 1, 0, 1]), (17, [3, 1, 0, 0, 0, 1]),
                       (41, [1, 1]+[0]*11+[1])]:
        field = Field(p, modulus)
        require(field.irreducible(), "rank-five fixture irreducible")
        cs = averaging_coefficients(field)
        linear = lambda z: sum(a*b for a, b in zip(cs, z)) % p
        for i in range(field.d):
            z = tuple(int(i == j) for j in range(field.d))
            require(linear(field.power(z, p)) == linear(z), "rank-five invariant projection")
        elements = interpolation_elements(field, 2*field.d-1)
        groups = orbit_partition(field.d) if field.d <= 5 else None
        if groups:
            require(sum(n == 1 for _, n in groups) == 5, "five constant patterns")
            require(len(groups) == (5**field.d+5*(field.d-1))//field.d, "rank-five class count")
        patterns = list(product(range(5), repeat=field.d)) if groups else [
            (i,)*13 for i in range(5)]+[tuple(rng.randrange(5) for _ in range(13)) for _ in range(9)]
        equivariance = descent = norms = 0
        for _ in range(2):
            matrix = [[tuple(rng.randrange(p) for _ in range(field.d)) for _ in range(3)]
                      for _ in range(3)]
            fs = [forms(field, m) for m in conjugate_matrices(field, matrix)]
            values = {w: field.determinant(combined(field, fs, w)) for w in patterns}
            for w in patterns:
                shifted = rotate(w, 1)
                actual = values[shifted] if shifted in values else field.determinant(combined(field, fs, shifted))
                require(actual == field.power(values[w], p), "rank-five term equivariance")
                equivariance += 1
            for w in patterns[:14]:
                m = combined(field, fs, w)
                require(projected_descent(field, m, elements, linear) == linear(values[w]),
                        "rank-five bilinear descent")
                descent += 1
            if groups:
                expected = field.power(field.determinant(matrix), (p**field.d-1)//(p-1))
                total = field.zero
                for v in values.values():
                    total = field.add(total, v)
                require(total == field.scale(expected, 6), "six times the actual field norm")
                grouped = sum(n*linear(values[w]) for w, n in groups) % p
                require(grouped*pow(6, -1, p) % p == expected[0], "rank-five weighted norm")
                missing_six += grouped != expected[0]
                missing_weights += sum(linear(values[w]) for w, _ in groups)*pow(6, -1, p) % p != expected[0]
                unaveraged += sum(n*values[w][0] for w, n in groups)*pow(6, -1, p) % p != expected[0]
                norms += 1
        reports.append({"p": p, "degree": field.d, "modulus_low_degree_first": modulus,
                        "patterns_per_matrix": len(patterns), "full_enumeration": groups is not None,
                        "classes": len(groups) if groups else None,
                        "fixed_patterns_enumerated": 5 if groups else None,
                        "equivariance_checks": equivariance, "descent_checks": descent,
                        "full_norm_checks": norms})
    require(missing_six > 0 and missing_weights > 0 and unaveraged > 0, "negative norm controls")
    return {"integral_formula_checks": rank_checks, "fields": reports, "negative_controls": {
        "missing_factor_one_sixth": missing_six, "missing_orbit_weights": missing_weights,
        "noninvariant_projection": unaveraged},
        "scope": "finite controls supplement the universal Lean proof; degree 13 is sampled"}


def exact_rows():
    rows = [[1]]
    for a in [9]*8+[10]:
        new = [0]*(len(rows[-1])+a*(a-1)//2)
        for e, c in enumerate(rows[-1]):
            for r in range(a):
                new[e+r*(r+1)//2] += 2*c
        rows.append(new)
    return rows


def multinomial_count():
    @lru_cache(None)
    def distribute(r, left, energy):
        if r == 9:
            return int(left == 0 and energy == 0)
        t = r*(r+1)//2
        return sum(comb(left, n)*distribute(r+1, left-n, energy-n*t)
                   for n in range(left+1) if n*t <= energy)
    return 2**9*sum(distribute(0, 8, 119-r*(r+1)//2) for r in range(10))


def packing_controls():
    rows = exact_rows()
    require(rows[9][119] == multinomial_count() == 2365025280, "mixed independent coefficient")
    # Exhaust all triples within each small equal-norm layer.
    as_ = [2, 3, 2]
    layers = {}
    for w in product(*(range(2*a) for a in as_)):
        energy = sum((2*d-(2*a-1))**2 for a, d in zip(as_, w))
        layers.setdefault(energy, []).append(w)
    def encode(w):
        n = 0
        for a, d in reversed(list(zip(as_, w))):
            n = d+(4*a-1)*n
        return n
    triples = 0
    for layer in layers.values():
        for x, y, z in product(layer, repeat=3):
            require((encode(x)+encode(y) == 2*encode(z)) == (x == y == z), "mixed sphere matching")
            triples += 1
    # Base 26 with fourteen digits admits carries even on one sphere.
    bad = [(0, 6), (13, 6), (0, 7)]
    require(len({sum((2*d-13)**2 for d in w) for w in bad}) == 1, "carry counterexample norm")
    vals = [w[0]+26*w[1] for w in bad]
    require(vals[0]+vals[2] == 2*vals[1] and len(set(vals)) == 3, "carry counterexample progression")
    return {"exact_coefficient": str(rows[9][119]), "multinomial_coefficient": str(multinomial_count()),
            "small_mixed_triples": triples, "unsafe_base_26_counterexample": vals}


if __name__ == "__main__":
    import json
    print(json.dumps({"packing": packing_controls(), "algebra": finite_controls()}, indent=2))
