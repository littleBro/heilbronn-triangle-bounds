"""Independent finite controls for rotation, averaging, and orbit descent.

Only degrees three and five are enumerated. Degree thirteen uses a checked
field fixture, all basis vectors, and deterministic sampled patterns.
"""
from itertools import product
from random import Random

from bilinear_controls import interpolation_elements
from norm_controls import Field, PERMS, SIGNS, determinant, evaluate
from verify import require

COMPOSE = tuple(tuple(PERMS.index(tuple(p[q[i]] for i in range(3))) for q in PERMS)
                for p in PERMS)
INVERSE = tuple(next(j for j in range(6) if COMPOSE[i][j] == 0) for i in range(6))


def rotate(word, shift):
    d = len(word)
    correction = INVERSE[word[-shift % d]]
    return tuple(COMPOSE[word[(v-shift) % d]][correction] for v in range(d))


def orbit_partition(d):
    unseen = {(0,)+word for word in product(range(6), repeat=d-1)}
    groups = []
    while unseen:
        word = min(unseen)
        orbit = {rotate(word, a) for a in range(d)}
        require(orbit <= unseen, "disjoint rotation classes")
        unseen -= orbit
        groups.append((word, len(orbit)))
    return groups


def conjugate_matrices(field, matrix):
    result = [matrix]
    for _ in range(1, field.d):
        result.append([[field.power(z, field.p) for z in row] for row in result[-1]])
    return result


def combined_matrix(field, conjugates, word):
    matrix = [[field.one for _ in range(3)] for _ in range(3)]
    sign = 1
    for v, code in enumerate(word):
        sign *= SIGNS[code]
        for i, j in product(range(3), repeat=2):
            matrix[i][j] = field.mul(matrix[i][j], conjugates[v][PERMS[code][i]][j])
    return sign, matrix


def averaging_coefficients(field):
    coefficients = []
    for i in range(field.d):
        z = tuple(int(i == j) for j in range(field.d))
        total = 0
        for _ in range(field.d):
            total += z[0]
            z = field.power(z, field.p)
        coefficients.append(total*pow(field.d, -1, field.p) % field.p)
    return coefficients


def projected_descent(field, matrix, elements, linear):
    return sum(determinant([
        [evaluate(z, t, field.p) for z in matrix[0]],
        [evaluate(z, t, field.p) for z in matrix[1]],
        [linear(field.mul(c, z)) for z in matrix[2]],
    ], field.p) for t, c in enumerate(elements)) % field.p


def finite_controls():
    rng = Random(19101325)
    reports = []
    omitted_weights = unaveraged_projection = 0
    fixtures = [(11, [4, 1, 0, 1]), (17, [3, 1, 0, 0, 0, 1]),
                (41, [1, 1]+[0]*11+[1])]
    for p, modulus in fixtures:
        field = Field(p, modulus)
        require(field.irreducible(), "Frobenius fixture irreducible")
        coefficients = averaging_coefficients(field)
        linear = lambda z: sum(a*b for a, b in zip(coefficients, z)) % p
        require(linear(field.one) == 1, "averaging fixes base field")
        for i in range(field.d):
            z = tuple(int(i == j) for j in range(field.d))
            require(linear(field.power(z, p)) == linear(z), "invariant basis projection")
        elements = interpolation_elements(field, 2*field.d-1)
        groups = orbit_partition(field.d) if field.d <= 5 else None
        if groups is not None:
            sizes = [size for _, size in groups]
            fixed = sizes.count(1)
            expected_fixed = 3 if field.d == 3 else 1
            require(fixed == expected_fixed, "fixed pattern count")
            require(sum(sizes) == 6**(field.d-1), "pattern partition size")
            require(len(groups) == (14 if field.d == 3 else 260), "class count")
            patterns = [(0,)+w for w in product(range(6), repeat=field.d-1)]
        else:
            fixed = None
            patterns = [(0,)*13]+[(0,)+tuple(rng.randrange(6) for _ in range(12)) for _ in range(8)]
        equivariance_checks = descent_checks = norm_checks = 0
        for _ in range(2):
            matrix = [[tuple(rng.randrange(p) for _ in range(field.d)) for _ in range(3)]
                      for _ in range(3)]
            conjugates = conjugate_matrices(field, matrix)
            signed = {}
            for word in patterns:
                sign, combined = combined_matrix(field, conjugates, word)
                signed[word] = field.scale(field.determinant(combined), sign)
                require(rotate(word, 0) == word, "identity action")
                require(rotate(rotate(word, 1), field.d-1) == word, "inverse rotation")
            for word in patterns:
                shifted = rotate(word, 1)
                if shifted in signed:
                    actual = signed[shifted]
                else:
                    sign, combined = combined_matrix(field, conjugates, shifted)
                    actual = field.scale(field.determinant(combined), sign)
                require(actual == field.power(signed[word], p), "signed term equivariance")
                equivariance_checks += 1
            # Check every representative at small degrees, and every sample at degree thirteen.
            for word, _size in groups if groups is not None else [(w, 1) for w in patterns]:
                sign, combined = combined_matrix(field, conjugates, word)
                require(projected_descent(field, combined, elements, linear) ==
                        linear(field.determinant(combined)), "averaged determinant descent")
                descent_checks += 1
            if groups is not None:
                expected = field.power(field.determinant(matrix), (p**field.d-1)//(p-1))
                require(all(z == 0 for z in expected[1:]), "norm in base field")
                total = field.zero
                for value in signed.values():
                    total = field.add(total, value)
                require(total == expected, "full signed norm expansion")
                grouped = sum(size*linear(signed[word]) for word, size in groups) % p
                require(grouped == expected[0], "weighted invariant orbit sum")
                omitted_weights += sum(linear(signed[word]) for word, _ in groups) % p != expected[0]
                unaveraged_projection += sum(size*signed[word][0] for word, size in groups) % p != expected[0]
                norm_checks += 1
        reports.append({"p": p, "degree": field.d, "modulus_low_degree_first": modulus,
            "averaging_coefficients": coefficients, "basis_invariance_checks": field.d,
            "classes_enumerated": len(groups) if groups is not None else None,
            "fixed_patterns": fixed, "signed_equivariance_checks": equivariance_checks,
            "averaged_descent_checks": descent_checks, "full_norm_checks": norm_checks,
            "degree_13_patterns_sampled_per_matrix": len(patterns) if field.d == 13 else None})
    require(omitted_weights > 0, "omitted orbit weights must fail")
    require(unaveraged_projection > 0, "unaveraged projection must fail")
    require((6**2+2) % 3 != 0, "degree three is not a valid unique-fixed-pattern case")
    return {"fields": reports, "negative_controls": {
        "omitted_orbit_weights_detected": omitted_weights,
        "unaveraged_projection_detected": unaveraged_projection,
        "degree_three_unique_fixed_pattern_rejected": True},
        "scope": "finite controls only; universal degree-thirteen claims are proved in Lean"}


if __name__ == "__main__":
    import json
    print(json.dumps(finite_controls(), indent=2))
