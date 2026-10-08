"""Independent exact arithmetic, native Lean, and small exhaustive sphere checks."""
from collections import defaultdict
from copy import deepcopy
from decimal import Decimal, localcontext
from fractions import Fraction
from hashlib import sha256
from itertools import product
from pathlib import Path
from random import Random
import json
import re
import sys

from verify import (PIN, PERMUTATIONS, check_positions, choose_by_recurrence,
                    determinant, read_fraction, require, run_checked)

ROOT = Path(__file__).resolve().parents[1]


def repeated_power(base, exponent):
    value = 1
    for _ in range(exponent):
        value *= base
    return value


def arithmetic(certificate):
    require(certificate["schema"] == "heilbronn-centered-sphere-v1", "schema")
    require(certificate["upstream_commit"] == PIN, "pin")
    require(certificate["status"] == "conditional-on-upstream-estimates", "status")
    require(certificate["scope"] == "paper exponent; not the upstream Lean comparator exponent", "scope")
    require(certificate["d"] == 41, "d")
    monomials = choose_by_recurrence(163, 41)
    terms, remainder = divmod(monomials**3 - 3 * monomials**2 + 2 * monomials, 6)
    require(remainder == 0, "T division")
    require(certificate["M"] == str(monomials), "M")
    require(certificate["T"] == str(terms), "T")
    m, a = certificate["dimension"], certificate["half_alphabet"]
    require((m, a) == (29, 10003), "selected parameters")
    s, b = 2 * a, 4 * a - 1
    # Sum triangular-number increments, independently of the closed formula.
    layers = m * sum(range(a)) + 1
    require(certificate["alphabet"] == s and certificate["base"] == b, "alphabet and base")
    require(certificate["energy_layers"] == layers, "layer count")
    cube, k = repeated_power(s, m), repeated_power(b, m)
    require(certificate["cube_size"] == str(cube), "cube size")
    require(certificate["required_capacity"] == str(terms * layers), "required capacity")
    require(terms * layers <= cube, "insufficient capacity")
    require(repeated_power(s - 2, m) < terms * (m * sum(range(a - 1)) + 1),
            "previous alphabet already sufficient")
    require(certificate["k_sphere"] == str(k), "sphere k")
    require(2 * (s - 1) == b - 1, "carry margin")
    require(certificate["selection"] ==
            "a qualifying energy class, then first T words in increasing base-s index", "selection")
    require(certificate["placement"] == ["u_a", "u_a", "k-1-2*u_a"], "positions")
    require(certificate["parameter_comparison"] == {
        "dimensions_inclusive": [3, 284],
        "criterion": "(2*A)^m >= T*(m*A*(A-1)/2+1)",
        "objective": "minimize (4*A-1)^m",
        "claim": "best of this bounded comparison; no unrestricted optimality claim",
    }, "parameter comparison scope")
    require(certificate["formal_scope"] == {
        "proved": ["sphere midpoint rigidity", "carry-free encoding",
                   "position bounds and injectivity", "matching for equal-energy words",
                   "numeric capacity and exponent ratio", "finite pigeonhole principle",
                   "energy-layer bound and selection of T distinct words",
                   "closed-form binomial calculation of T", "complete finite paper packing"],
        "written_not_formalized": ["geometric transfer", "parameter comparison monotonicity"],
    }, "formal scope")
    # Re-derive the exponent from the scales in alteration, not just 45435*k.
    beta = 15 * (k + 100 * k) - Fraction(k - 1, 2)
    eta = 2 / (1 + 30 * beta)
    ternary_k = repeated_power(3, 384)
    old_eta = Fraction(2, 45435 * (terms * terms + 1) + 16)
    ternary_eta = Fraction(2, 45435 * ternary_k + 16)
    require(read_fraction(certificate["eta_sphere"]) == eta, "sphere eta")
    require(read_fraction(certificate["gain_from_original"]) == eta / old_eta, "original gain")
    require(read_fraction(certificate["gain_from_ternary"]) == eta / ternary_eta, "ternary gain")
    require(5 * 10**49 < eta / ternary_eta < 6 * 10**49, "gain enclosure")
    return eta, eta / old_eta, eta / ternary_eta


def compare_parameters(terms, chosen_k):
    # Directly bound the base by chosen_k, then see whether any smaller k in
    # each dimension could meet the capacity criterion. This does not repeat
    # the generator's search for the least sufficient alphabet.
    for m in range(3, 285):
        lo, hi = 0, 1
        while (4 * hi - 1)**m < chosen_k:
            hi *= 2
        while lo + 1 < hi:
            mid = (lo + hi) // 2
            if (4 * mid - 1)**m < chosen_k:
                lo = mid
            else:
                hi = mid
        if lo >= 1:
            require((2 * lo)**m < terms * (m * lo * (lo - 1) // 2 + 1),
                    "smaller parameter candidate")
    return {"dimensions_checked": 282, "claim": "bounded comparison only"}


def spheres(a, m):
    s = 2 * a
    layers = defaultdict(list)
    for word in product(range(s), repeat=m):
        energy = sum((2 * d - (s - 1))**2 for d in word)
        layers[energy].append(word)
    return layers


def encode(word, base):
    value = 0
    for digit in reversed(word):
        value = value * base + digit
    return value


def rows_for(words, base, k):
    values = [encode(word, base) for word in words]
    return (values, values.copy(), [k - 1 - 2 * value for value in values])


def finite_spheres():
    cases = [(1, 1), (1, 4), (2, 1), (2, 2), (2, 3), (2, 4),
             (3, 2), (3, 3), (4, 2), (4, 3)]
    word_count = layer_count = pair_checks = 0
    for a, m in cases:
        layers = spheres(a, m)
        q = m * a * (a - 1) // 2 + 1
        size = (2 * a)**m
        require(sum(map(len, layers.values())) == size, "cube count")
        require(len(layers) <= q, "too many energies")
        threshold = (size + q - 1) // q
        chosen_energy = min(e for e, words in layers.items() if len(words) >= threshold)
        selected = sorted(layers[chosen_energy], key=lambda word: encode(word, 2 * a))[:threshold]
        require(len(selected) == threshold, "finite selection capacity")
        k, b = (4 * a - 1)**m, 4 * a - 1
        for energy, words in layers.items():
            require((energy - m) % 8 == 0 and 0 <= (energy - m) // 8 < q, "energy range")
            require(check_positions(rows_for(words, b, k), len(words), k, k - 1) == "ok",
                    f"sphere matching: A={a}, m={m}, energy={energy}")
            pair_checks += len(words)**2
        word_count += size
        layer_count += len(layers)
    # Reduced base introduces carries and a genuine off-diagonal collision,
    # even after enlarging k to keep every position in range.
    words = spheres(2, 2)[10]
    values = [encode(w, 6) for w in words]
    k = 2 * max(values) + 1
    require(check_positions(rows_for(words, 6, k), len(words), k, k - 1) == "off_diagonal",
            "bad-base negative control")
    # Mixing two energies destroys the sphere argument.
    require(check_positions(rows_for([(0,), (1,), (2,)], 7, 7), 3, 7, 6) == "off_diagonal",
            "mixed-energy negative control")
    return {"cases": cases, "words": word_count, "layers": layer_count,
            "pair_checks": pair_checks, "negative_controls": 2}


def coefficient_checks():
    rng = Random(19129)
    examples = nonzero = 0
    for a, m in [(1, 3), (2, 2)]:
        layers = spheres(a, m)
        words = max(layers.values(), key=len)
        count, k = len(words), (4 * a - 1)**m
        rows = rows_for(words, 4 * a - 1, k)
        for prime in (3, 5, 7):
            L = prime**2
            digits = [[[prime * rng.randrange(1, prime + 1) for _ in range(k)]
                       for _ in range(3)] for _ in range(3)]
            prescribed = [[[rng.randrange(prime) for _ in range(3)]
                           for _ in range(3)] for _ in words]
            for index in range(count):
                for row in range(3):
                    for col in range(3):
                        residue = prescribed[index][row][col]
                        choices = [v for v in range(1, L + 1) if v % prime == residue]
                        digits[row][col][rows[row][index]] = rng.choice(choices)
            coefficient = 0
            for p, sign in PERMUTATIONS:
                for i in range(k):
                    for j in range(k - i):
                        coefficient += sign * digits[0][p[0]][i] * digits[1][p[1]][j] * digits[2][p[2]][k-1-i-j]
            expected = sum(map(determinant, prescribed)) % prime
            require(coefficient % prime == expected, "sphere coefficient identity")
            require(abs(coefficient) <= 6 * k*k * L**3, "coefficient bound")
            if expected:
                B = 100 * k*k * L**3 + 1
                h = B**k
                matrix = [[sum(digits[row][col][v] * B**v for v in range(k))
                           for col in range(3)] for row in range(3)]
                residue = determinant(matrix) % h
                centered = residue if 2 * residue <= h else residue - h
                require(abs(centered) > B**(k - 1) // 2, "sphere carry separation")
                nonzero += 1
            examples += 1
    require(nonzero > 0, "vacuous carry checks")
    return {"coefficient_examples": examples, "nonzero_carry_examples": nonzero}


def main():
    certificate = json.loads((ROOT / "certificates/sphere.json").read_text(encoding="utf-8"))
    eta, old_gain, ternary_gain = arithmetic(certificate)
    negative = [("energy_layers", 1450725087, "layer count"),
                ("k_sphere", str(int(certificate["k_sphere"]) - 1), "sphere k"),
                ("dimension", 28, "selected parameters"),
                ("T", str(int(certificate["T"]) - 1), "T")]
    for field, replacement, reason in negative:
        bad = deepcopy(certificate)
        bad[field] = replacement
        try:
            arithmetic(bad)
        except AssertionError as error:
            require(str(error) == reason, "unexpected negative-control failure")
        else:
            raise AssertionError("corrupted sphere certificate was accepted")
    comparison = compare_parameters(int(certificate["T"]), int(certificate["k_sphere"]))
    finite = finite_spheres()
    coefficients = coefficient_checks()
    manifest = json.loads((ROOT / "upstream/manifest.json").read_text(encoding="utf-8-sig"))
    require(manifest["commit"] == PIN, "manifest pin")
    for item in manifest["files"]:
        data = (ROOT / item["path"]).read_bytes()
        require(sha256(data).hexdigest() == item["sha256"] and len(data) == item["bytes"], "changed upstream")
    lean_source = (ROOT / "lean/Sphere.lean").read_text(encoding="utf-8")
    require(not re.search(r"\b(sorry|admit|axiom|unsafe|native_decide)\b", lean_source), "proof escape")
    require(re.search(r"def paperT : Nat :=\s*" + certificate["T"] + r"\b", lean_source), "Lean T")
    version = run_checked(["lean", "--version"]).strip()
    require("version 4.11.0," in version, "Lean version")
    lean_output = run_checked(["lean", "lean/Sphere.lean"])
    require("sorryAx" not in lean_output and "error:" not in lean_output, "incomplete Lean proof")
    for name in ("sphere_matching", "position_bounds", "encode_injective",
                 "right_injective", "paper_capacity", "sphere_gain", "sphere_family",
                 "packing_exists", "paper_packing", "paperT_binomial", "paper_packing_binomial"):
        require("'HeilbronnSphere." + name + "'" in lean_output, "missing axiom audit")
    for entry in re.findall(r"depends on axioms: \[([^]]*)\]", lean_output):
        require(set(entry.split(", ")) <= {"propext", "Classical.choice", "Quot.sound"}, "unexpected axiom")
    run_checked(["git", "apply", "--check", "--directory=upstream/manuscript", "patches/sphere-packing.patch"])
    evidence = ["lean/Sphere.lean", "lean-toolchain", "scripts/build_sphere.py", "scripts/verify_sphere.py",
                "scripts/verify.py", "scripts/build_patch.py", "certificates/sphere.json",
                "patches/sphere-packing.patch", "notes/sphere-packing.tex", "notes/packing.tex",
                "README.md", "NOTICE", "upstream/manifest.json", "artifacts/sphere-latex-status.json"]
    with localcontext() as ctx:
        ctx.prec = 40
        decimal = lambda f: format(Decimal(f.numerator) / Decimal(f.denominator), ".14E")
        report = {
            "status": "pass", "python": sys.version, "lean": version, "upstream_commit": PIN,
            "source_files_verified": len(manifest["files"]),
            "eta_sphere_approx": decimal(eta), "gain_from_original_approx": decimal(old_gain),
            "gain_from_ternary_approx": decimal(ternary_gain),
            "arithmetic_negative_controls": len(negative), "parameter_comparison": comparison,
            "sphere_regressions": finite, "determinant_regressions": coefficients,
            "lean_axiom_audit": lean_output.splitlines(), "patch_applies": True,
            "evidence_sha256": {p: sha256((ROOT / p).read_bytes()).hexdigest() for p in evidence},
            "not_established": [
                "complete independent proof or formalization of the upstream geometric theorem",
                "formal proof of parameter-comparison optimality",
                "practical construction of the full sphere or planar point set",
                "novelty, priority, or unrestricted packing optimality",
            ],
        }
    (ROOT / "artifacts/sphere-verification.json").write_text(
        json.dumps(report, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps({key: report[key] for key in (
        "status", "eta_sphere_approx", "gain_from_original_approx", "gain_from_ternary_approx",
        "sphere_regressions", "determinant_regressions")}, indent=2))


if __name__ == "__main__":
    main()
