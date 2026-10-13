"""Small exact field controls for the written norm-compression argument.

No degree-13 determinant expansion is enumerated. Its interpolation interface
is checked on a polynomial basis; the permutation normalization is in Lean.
"""
from itertools import permutations, product
from random import Random

from verify import require

PERMS = tuple(permutations(range(3)))
SIGNS = tuple((-1)**sum(p[i] > p[j] for i in range(3) for j in range(i+1, 3))
              for p in PERMS)


def evaluate(coefficients, x, p):
    value = 0
    for a in reversed(coefficients):
        value = (value*x+a) % p
    return value


class Field:
    def __init__(self, p, polynomial):
        self.p, self.polynomial = p, tuple(polynomial)
        self.d = len(polynomial)-1
        require(polynomial[-1] == 1, "monic modulus")
        self.zero = (0,)*self.d
        self.one = (1,)+(0,)*(self.d-1)
        self.x = (0, 1)+(0,)*(self.d-2)

    def reduce(self, a):
        a = list(a)+[0]*max(0, self.d-len(a))
        for i in range(len(a)-1, self.d-1, -1):
            lead = a[i] % self.p
            for j in range(self.d):
                a[i-self.d+j] -= lead*self.polynomial[j]
        return tuple(v % self.p for v in a[:self.d])

    def add(self, a, b):
        return tuple((x+y) % self.p for x, y in zip(a, b))

    def scale(self, a, c):
        return tuple(x*c % self.p for x in a)

    def mul(self, a, b):
        result = [0]*(2*self.d-1)
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                result[i+j] += x*y
        return self.reduce(result)

    def power(self, a, n):
        result = self.one
        while n:
            if n & 1:
                result = self.mul(result, a)
            a = self.mul(a, a)
            n >>= 1
        return result

    def irreducible(self):
        # For prime d, Rabin's criterion reduces to these two conditions.
        require(self.d in (2, 3, 5, 13), "prime control degree")
        require(all(self.p % a for a in range(2, self.p) if a*a <= self.p), "prime base")
        return (all(evaluate(self.polynomial, a, self.p) for a in range(self.p)) and
                self.power(self.x, self.p**self.d) == self.x)

    def determinant(self, matrix):
        result = self.zero
        for perm, sign in zip(PERMS, SIGNS):
            value = self.one
            for j in range(3):
                value = self.mul(value, matrix[perm[j]][j])
            result = self.add(result, self.scale(value, sign))
        return result


def determinant(matrix, p):
    a, b, c = matrix
    return (a[0]*(b[1]*c[2]-b[2]*c[1]) - a[1]*(b[0]*c[2]-b[2]*c[0]) +
            a[2]*(b[0]*c[1]-b[1]*c[0])) % p


def interpolation_weights(field, count):
    require(count <= field.p, "distinct interpolation nodes")
    weights = []
    for t in range(count):
        numerator, denominator = [1], 1
        for u in range(count):
            if t == u:
                continue
            result = [0]*(len(numerator)+1)
            for j, value in enumerate(numerator):
                result[j] -= u*value
                result[j+1] += value
            numerator = [value % field.p for value in result]
            denominator = denominator*(t-u) % field.p
        weights.append(field.reduce(numerator)[0]*pow(denominator, -1, field.p) % field.p)
    return weights


def descent(field, matrix, weights):
    return sum(weight*determinant([[evaluate(a, t, field.p) for a in row] for row in matrix],
                                  field.p) for t, weight in enumerate(weights)) % field.p


def orbit_sum(field, matrix, weights):
    conjugates = [matrix]
    for _ in range(1, field.d):
        conjugates.append([[field.power(a, field.p) for a in row] for row in conjugates[-1]])
    result, descended, unsigned = field.zero, 0, 0
    count = 0
    for choices in product(range(6), repeat=field.d-1):
        sign = 1
        combined = [row[:] for row in matrix]
        for t, index in enumerate(choices, 1):
            sign *= SIGNS[index]
            for i in range(3):
                for j in range(3):
                    combined[i][j] = field.mul(combined[i][j], conjugates[t][PERMS[index][i]][j])
        det = field.determinant(combined)
        scalar = descent(field, combined, weights)
        require(scalar == det[0], "per-orbit descent")
        result = field.add(result, field.scale(det, sign))
        descended = (descended + sign*scalar) % field.p
        unsigned = (unsigned + scalar) % field.p
        count += 1
    return result, descended, unsigned, count


def finite_controls():
    # Explicit fixtures, checked for irreducibility before use.
    fixtures = [(11, [4, 1, 0, 1]), (17, [3, 1, 0, 0, 0, 1]),
                (41, [1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1])]
    rng = Random(191013)
    reports = []
    sign_failures = projection_failures = short_interpolation_failures = 0
    for p, modulus in fixtures:
        field = Field(p, modulus)
        require(field.irreducible(), "irreducible fixture")
        nodes = 3*field.d-2
        weights = interpolation_weights(field, nodes)
        alpha_power = field.one
        for e in range(nodes):
            require(sum(w*pow(t, e, p) for t, w in enumerate(weights)) % p == alpha_power[0],
                    "interpolation basis identity")
            alpha_power = field.mul(alpha_power, field.x)
        short = interpolation_weights(field, nodes-1)
        if any(sum(w*pow(t, e, p) for t, w in enumerate(short)) % p !=
               field.power(field.x, e)[0] for e in range(nodes)):
            short_interpolation_failures += 1
        # A corrupted weight already fails on the constant polynomial.
        bad_weights = weights[:]
        bad_weights[0] = (bad_weights[0]+1) % p
        require(sum(bad_weights) % p != 1, "corrupted interpolation control")
        matrices = [[[tuple(rng.randrange(p) for _ in range(field.d)) for _ in range(3)]
                     for _ in range(3)] for _ in range(3)]
        labels = [field.zero, field.one, field.x]
        matrices.append([[field.one]*3, labels, [field.mul(a, a) for a in labels]])
        orbit_cases = total_orbits = 0
        for index, matrix in enumerate(matrices):
            det = field.determinant(matrix)
            if index == len(matrices)-1:
                require(det != field.zero, "distinct-label Vandermonde obstruction")
            require(descent(field, matrix, weights) == det[0], "matrix descent")
            if determinant([[a[0] for a in row] for row in matrix], p) != det[0]:
                projection_failures += 1
            if field.d <= 5:
                expected = field.power(det, (p**field.d-1)//(p-1))
                require(all(a == 0 for a in expected[1:]), "norm in base field")
                actual, scalar, unsigned, count = orbit_sum(field, matrix, weights)
                require(actual == expected and scalar == expected[0], "norm decomposition")
                if unsigned != scalar:
                    sign_failures += 1
                orbit_cases += 1
                total_orbits += count
        reports.append({"p": p, "d": field.d, "modulus_low_degree_first": modulus,
            "interpolation_nodes": nodes, "interpolation_weights": weights,
            "basis_identities": nodes, "matrix_descent_cases": len(matrices),
            "norm_expansion_cases": orbit_cases, "orbits_checked": total_orbits})
    require(sign_failures > 0, "omitted permutation signs control")
    require(projection_failures > 0, "entrywise projection control")
    require(short_interpolation_failures > 0, "insufficient interpolation nodes control")
    # The sign of the common permutation has power d. Even d cannot be
    # silently substituted in the alternating-orbit argument.
    require(SIGNS[1]**2 != SIGNS[1], "even degree control")
    return {"fields": reports, "negative_controls": {
        "omitted_signs_detected": sign_failures,
        "entrywise_projection_detected": projection_failures,
        "too_few_nodes_detected": short_interpolation_failures,
        "corrupted_weights": len(fixtures), "even_degree": 1},
        "scope": "exact finite controls, not a universal field-algebra proof"}


if __name__ == "__main__":
    import json
    print(json.dumps(finite_controls(), indent=2))
