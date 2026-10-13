"""Independent finite controls for paired determinants and the energy-59 layer."""
from functools import lru_cache
from itertools import product
from math import comb, prod
from random import Random

from bilinear_controls import interpolation_elements, bilinear_descent
from frobenius_controls import conjugate_matrices
from norm_controls import Field, determinant
from rankfive_controls import COEFFICIENTS
from verify import require

SIGNS = ((1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1))
FORMS = tuple(tuple(tuple(s[i]*c[i][r] for i in range(3)) for r in range(3))
              for c in COEFFICIENTS for s in SIGNS)


def pair_values(field, a, b):
    values = []
    for form in FORMS:
        cols = []
        for j in range(3):
            z = field.zero
            for r, i in product(range(3), repeat=2):
                if form[r][i]:
                    z = field.add(z, field.scale(field.mul(a[r][j], b[i][j]), form[r][i]))
            cols.append(z)
        values.append(cols)
    return values


def combined(field, singleton, paired, pattern):
    common = [field.one]*3
    for values, t in zip(paired, pattern):
        common = [field.mul(v, h) for v, h in zip(common, values[t])]
    return [[field.mul(singleton[i][j], common[j]) for j in range(3)] for i in range(3)]


def finite_controls():
    rng = Random(191206)
    pair_checks = missing_four = nonsymmetric = 0
    for p in (2, 3, 5, 37, 101):
        for _ in range(32):
            a = [[rng.randrange(p) for _ in range(3)] for _ in range(3)]
            b = [[rng.randrange(p) for _ in range(3)] for _ in range(3)]
            values = [[sum(f[r][i]*a[r][j]*b[i][j] for r, i in product(range(3), repeat=2)) % p
                       for j in range(3)] for f in FORMS]
            total = sum(prod(v) for v in values) % p
            expected = determinant(a, p)*determinant(b, p) % p
            require(total == 4*expected % p, "paired integral identity")
            missing_four += total != expected
            wrong = sum(values[t][0]*values[t][1]*values[(t+1) % 20][2] for t in range(20)) % p
            nonsymmetric += wrong != 4*expected % p
            pair_checks += 1
    reports = []
    wrong_scale = wrong_pairing = 0
    for p, modulus in [(11, [4, 1, 0, 1]), (17, [3, 1, 0, 0, 0, 1]),
                       (41, [1, 1]+[0]*11+[1])]:
        field = Field(p, modulus)
        require(field.irreducible(), "paired fixture irreducible")
        m = (field.d-1)//2
        elements = interpolation_elements(field, 2*field.d-1)
        patterns = list(product(range(20), repeat=m)) if m <= 2 else [
            (i,)*m for i in range(20)]+[tuple(rng.randrange(20) for _ in range(m)) for _ in range(8)]
        norms = descents = factorized = 0
        for _ in range(2):
            matrix = [[tuple(rng.randrange(p) for _ in range(field.d)) for _ in range(3)]
                      for _ in range(3)]
            conjugates = conjugate_matrices(field, matrix)
            paired = [pair_values(field, conjugates[2*v+1], conjugates[2*v+2]) for v in range(m)]
            expected = field.power(field.determinant(matrix), (p**field.d-1)//(p-1))
            factored = field.determinant(conjugates[0])
            for vals in paired:
                s = field.zero
                for v in vals:
                    s = field.add(s, field.mul(field.mul(v[0], v[1]), v[2]))
                factored = field.mul(factored, s)
            require(factored == field.scale(expected, 4**m), "paired factorized norm")
            factorized += 1
            total = field.zero
            for index, pattern in enumerate(patterns):
                a = combined(field, conjugates[0], paired, pattern)
                v = field.determinant(a)
                total = field.add(total, v)
                if index < 12:
                    require(bilinear_descent(field, a, elements) == v[0], "paired descent")
                    descents += 1
            if m <= 2:
                require(total == field.scale(expected, 4**m), "paired enumerated norm")
                require(field.scale(total, pow(4**m, -1, p)) == expected, "paired normalization")
                wrong_scale += total != expected
                # Replace the first pair's second automorphism by its first.
                bad = field.determinant(conjugates[0])
                for i in range(1, field.d):
                    bad = field.mul(bad, field.determinant(conjugates[1 if i == 2 else i]))
                wrong_pairing += bad != expected
                norms += 1
        reports.append({"p": p, "degree": field.d, "modulus_low_degree_first": modulus,
                        "pairs": m, "patterns_per_matrix": len(patterns),
                        "full_enumeration": m <= 2, "full_norm_checks": norms,
                        "factorized_norm_checks": factorized, "descent_checks": descents})
    require(min(missing_four, nonsymmetric, wrong_scale, wrong_pairing) > 0, "paired negative controls")
    return {"integral_pair_checks": pair_checks, "fields": reports, "negative_controls": {
        "missing_four": missing_four, "different_form_in_third_column": nonsymmetric,
        "missing_normalization": wrong_scale, "duplicated_conjugate": wrong_pairing},
        "scope": "finite controls supplement universal Lean proofs; degree 13 uses factorization and sampled terms"}


def exact_rows():
    # Count actual digits, with full distributions and no truncation.
    rows = [[1]]
    for a in [6]*9+[7]:
        new = [0]*(len(rows[-1])+a*(a-1)//2)
        for e, c in enumerate(rows[-1]):
            for d in range(2*a):
                r = abs(2*d-(2*a-1))//2
                new[e+r*(r+1)//2] += c
        rows.append(new)
    return rows


def multinomial_count():
    @lru_cache(None)
    def distribute(r, left, energy):
        if r == 6:
            return int(left == 0 and energy == 0)
        t = r*(r+1)//2
        return sum(comb(left, n)*distribute(r+1, left-n, energy-n*t)
                   for n in range(left+1) if n*t <= energy)
    return 2**10*sum(distribute(0, 9, 59-r*(r+1)//2) for r in range(7))


def packing_controls():
    count = exact_rows()[10][59]
    require(count == multinomial_count() == 1641775104, "paired independent coefficient")
    return {"full_distribution_coefficient": str(count), "multinomial_coefficient": str(multinomial_count())}


if __name__ == "__main__":
    import json
    print(json.dumps({"packing": packing_controls(), "algebra": finite_controls()}, indent=2))
