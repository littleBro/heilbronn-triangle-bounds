"""Independent, bounded checks. Standard library only; no upstream code runs.

The finite tests below are regression evidence. The universal packing claim
comes from lean/Packing.lean; the global geometric transfer is a written,
conditional argument in notes/packing.tex.
"""
from copy import deepcopy
from decimal import Decimal, localcontext
from fractions import Fraction
from hashlib import sha256
from itertools import permutations
from pathlib import Path
from random import Random
import json
import platform
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def choose_by_recurrence(n, k):
    value = 1
    for j in range(1, k + 1):
        value, remainder = divmod(value * (n - j + 1), j)
        require(remainder == 0, "nonintegral binomial recurrence")
    return value


def read_fraction(item):
    value = Fraction(int(item["numerator"]), int(item["denominator"]))
    require(str(value.numerator) == item["numerator"] and
            str(value.denominator) == item["denominator"], "noncanonical fraction")
    return value


def verify_arithmetic(certificate):
    require(certificate["schema"] == "heilbronn-ternary-packing-v1", "schema")
    require(certificate["upstream_commit"] == PIN, "pin")
    require(certificate["status"] == "conditional-on-upstream-estimates", "scope")
    require(certificate["scope"] == "paper exponent; not the upstream Lean comparator exponent", "exponent scope")
    require(certificate["placement"] == {
        "u_a": "binary digits of a interpreted in base 3, padded to m digits",
        "i_a": "u_a", "j_a": "u_a", "ell_a": "3^m - 1 - 2*u_a",
        "target": "3^m - 1", "index_range": "0 <= a < T",
    }, "placement specification")
    require(certificate["unchanged_parameters"] == {
        "L": "r^10", "B": "100*k^2*r^30 < B <= 200*k^2*r^30, B prime",
        "h": "B^k", "tau": "floor(B^(k-1)/2)",
        "q": "h^100 < q <= 2*h^100, q prime",
        "N": "(h*q)^10", "alpha": "45435*k + 16",
    }, "upstream parameter specification")
    require(certificate["d"] == 41, "changed d")
    monomials = choose_by_recurrence(163, 41)
    # Deliberately use the expanded cubic, rather than math.comb(M, 3).
    terms, remainder = divmod(monomials**3 - 3 * monomials**2 + 2 * monomials, 6)
    require(remainder == 0, "nonintegral triple count")
    bits, capacity, new_k = 0, 1, 1
    while capacity < terms:
        bits += 1
        capacity *= 2
        new_k *= 3
    old_k = terms * terms + 1
    require(certificate["M"] == str(monomials), "M")
    require(certificate["T"] == str(terms), "T")
    require(certificate["m"] == bits == 384, "m")
    require(capacity // 2 < terms <= capacity, "minimal capacity")
    require(certificate["k_original"] == str(old_k), "old k")
    require(certificate["k_ternary"] == str(new_k), "new k")
    require(2 <= new_k < old_k, "improvement or k domain")
    # Re-derive alpha through the scaling argument, without starting at 45435.
    alpha = lambda k: 1 + 30 * (15 * (k + 100 * k) - Fraction(k - 1, 2))
    old_eta, new_eta = 2 / alpha(old_k), 2 / alpha(new_k)
    require(alpha(old_k) == 45435 * old_k + 16, "old scaling")
    require(alpha(new_k) == 45435 * new_k + 16, "new scaling")
    require(read_fraction(certificate["eta_original"]) == old_eta, "old eta")
    require(read_fraction(certificate["eta_ternary"]) == new_eta, "new eta")
    gain = new_eta / old_eta
    require(read_fraction(certificate["gain"]) == gain, "gain")
    require(8 * 10**47 < gain < 9 * 10**47, "gain enclosure")
    # The r-exponents needed for theta and deletion remain strictly negative.
    require(30 + 4 * (1 - 10) == -6, "conditional moment exponent")
    require(2 + 30 - 41 == -9, "collision deletion exponent")
    require(1 - 9 * 101 * 30 * new_k < 0, "pair deletion exponent")
    return old_eta, new_eta, gain


def positions(count):
    bits = (count - 1).bit_length()
    k = 3**bits
    # MSB-first parsing is independent of Lean's LSB-first recursive function.
    values = [int(format(a, "b"), 3) for a in range(count)]
    return (values, values.copy(), [k - 1 - 2 * x for x in values]), k


def check_positions(rows, count, k, target):
    if any(len(row) != count for row in rows):
        return "row_length"
    if any(not 0 <= x < k for row in rows for x in row):
        return "range"
    if any(len(set(row)) != count for row in rows):
        return "row_injectivity"
    if any(sum(row[a] for row in rows) != target for a in range(count)):
        return "diagonal"
    third = {x: a for a, x in enumerate(rows[2])}
    for a, x in enumerate(rows[0]):
        for b, y in enumerate(rows[1]):
            c = third.get(target - x - y)
            if c is not None and not a == b == c:
                return "off_diagonal"
    return "ok"


def finite_checks():
    sizes = [1, 2, 3, 4, 5, 7, 8, 9, 16, 17, 31, 32, 33, 63, 64, 65,
             127, 128, 129, 255, 256]
    for count in sizes:
        rows, k = positions(count)
        require(check_positions(rows, count, k, k - 1) == "ok", f"packing T={count}")
    # Invalid arithmetic progression: the diagonal is valid, but (0, 2, 1) is not.
    require(check_positions(([0, 1, 2], [0, 1, 2], [4, 2, 0]), 3, 5, 4)
            == "off_diagonal", "off-diagonal negative control")
    rows, k = positions(5)
    missing = deepcopy(rows)
    missing[0].pop()
    require(check_positions(missing, 5, k, k - 1) == "row_length", "missing position")
    outside = deepcopy(rows)
    outside[0][0] = k
    require(check_positions(outside, 5, k, k - 1) == "range", "out-of-range position")
    duplicate = deepcopy(rows)
    duplicate[1][1] = duplicate[1][0]
    require(check_positions(duplicate, 5, k, k - 1) == "row_injectivity", "duplicate position")
    require(check_positions(rows, 5, k, k - 2) == "diagonal", "wrong coefficient")
    return {"sizes": sizes, "pair_checks": sum(t*t for t in sizes), "negative_controls": 5}


PERMUTATIONS = [
    (p, (-1)**sum(p[i] > p[j] for i in range(3) for j in range(i + 1, 3)))
    for p in permutations(range(3))
]


def determinant(matrix):
    return sum(sign * matrix[0][p[0]] * matrix[1][p[1]] * matrix[2][p[2]]
               for p, sign in PERMUTATIONS)


def determinant_checks():
    # Test the actual coefficient interface, including positive, independently
    # sampled digits with residue zero. No field-norm producer is assumed here.
    rng = Random(191)
    examples, nonzero = 0, 0
    for count in [2, 3, 5, 8]:
        rows, k = positions(count)
        for prime in [3, 5, 7]:
            L = prime**2
            digits = [[[prime * rng.randrange(1, prime + 1) for _ in range(k)]
                       for _ in range(3)] for _ in range(3)]
            prescribed = [[[rng.randrange(prime) for _ in range(3)]
                           for _ in range(3)] for _ in range(count)]
            for a in range(count):
                for row in range(3):
                    for col in range(3):
                        residue = prescribed[a][row][col]
                        allowed = [v for v in range(1, L + 1) if v % prime == residue]
                        digits[row][col][rows[row][a]] = rng.choice(allowed)
            target = k - 1
            coefficient = 0
            for p, sign in PERMUTATIONS:
                for i in range(k):
                    for j in range(k - i):
                        coefficient += sign * digits[0][p[0]][i] * digits[1][p[1]][j] * digits[2][p[2]][target-i-j]
            expected = sum(determinant(matrix) for matrix in prescribed) % prime
            require(coefficient % prime == expected, "determinant coefficient identity")
            require(abs(coefficient) <= 6 * k*k * L**3, "coefficient bound")
            if expected:
                # Primality of B is unnecessary for this integer carry test.
                # It is still required, and retained, in the manuscript's orbit step.
                B = 100 * k*k * L**3 + 1
                h = B**k
                integer_matrix = [[sum(digits[row][col][v] * B**v for v in range(k))
                                   for col in range(3)] for row in range(3)]
                residue = determinant(integer_matrix) % h
                centered = residue if 2 * residue <= h else residue - h
                require(abs(centered) > B**(k-1) // 2, "carry separation")
                nonzero += 1
            examples += 1
    require(nonzero > 0, "vacuous carry coverage")
    return {"coefficient_examples": examples, "nonzero_carry_examples": nonzero}


def run_checked(command):
    result = subprocess.run(command, cwd=ROOT, text=True, encoding="utf-8",
                            errors="replace", capture_output=True, timeout=30)
    require(result.returncode == 0, "command failed: " + " ".join(command) + "\n" + result.stdout + result.stderr)
    return result.stdout + result.stderr


def main():
    source_manifest = json.loads((ROOT / "upstream/manifest.json").read_text(encoding="utf-8-sig"))
    require(source_manifest["commit"] == PIN, "upstream pin")
    for item in source_manifest["files"]:
        data = (ROOT / item["path"]).read_bytes()
        require(sha256(data).hexdigest() == item["sha256"], "changed upstream: " + item["path"])
        require(len(data) == item["bytes"], "changed upstream length")
    certificate_path = ROOT / "certificates/ternary.json"
    certificate = json.loads(certificate_path.read_text(encoding="utf-8"))
    old_eta, new_eta, gain = verify_arithmetic(certificate)
    corrupted = deepcopy(certificate)
    corrupted["k_ternary"] = str(int(corrupted["k_ternary"]) - 1)
    try:
        verify_arithmetic(corrupted)
    except AssertionError as error:
        require(str(error) == "new k", "wrong negative-control failure")
    else:
        raise AssertionError("arithmetic negative control was accepted")
    packing = finite_checks()
    coefficients = determinant_checks()
    lean_source = (ROOT / "lean/Packing.lean").read_text(encoding="utf-8")
    require(not re.search(r"\b(sorry|admit|axiom|unsafe|native_decide)\b", lean_source), "unapproved proof escape")
    require(re.search(r"def paperT : Nat :=\s*" + certificate["T"] + r"\b", lean_source), "Lean T literal")
    version = run_checked(["lean", "--version"]).strip()
    require("version 4.11.0," in version, "Lean version changed")
    lean_output = run_checked(["lean", "lean/Packing.lean"])
    require("sorryAx" not in lean_output and "error:" not in lean_output, "incomplete formal proof")
    theorem_names = ["packing_interface", "paper_matching", "paper_capacity", "smaller_parameter", "exponent_gain"]
    for name in theorem_names:
        require("'HeilbronnPacking." + name + "'" in lean_output, "missing theorem audit: " + name)
    for entry in re.findall(r"depends on axioms: \[([^]]*)\]", lean_output):
        require(set(entry.split(", ")) <= {"propext", "Classical.choice", "Quot.sound"}, "unexpected axiom")
    run_checked(["git", "apply", "--check", "--directory=upstream/manuscript", "patches/ternary-packing.patch"])
    tracked_evidence = ["lean/Packing.lean", "lean-toolchain", "scripts/build_certificate.py",
                        "scripts/build_patch.py", "scripts/verify.py", "certificates/ternary.json",
                        "patches/ternary-packing.patch", "notes/packing.tex", "README.md", "NOTICE",
                        "upstream/manifest.json", ".gitattributes", "artifacts/latex-status.json"]
    with localcontext() as ctx:
        ctx.prec = 40
        decimal = lambda value: format(Decimal(value.numerator) / Decimal(value.denominator), ".14E")
        report = {
            "status": "pass",
            "python": sys.version,
            "platform": platform.platform(),
            "lean": version,
            "source_files_verified": len(source_manifest["files"]),
            "upstream_commit": PIN,
            "packing_regressions": packing,
            "arithmetic_negative_controls": 1,
            "determinant_regressions": coefficients,
            "lean_axiom_audit": lean_output.splitlines(),
            "patch_applies": True,
            "eta_original_approx": decimal(old_eta),
            "eta_ternary_approx": decimal(new_eta),
            "gain_approx": decimal(gain),
            "evidence_sha256": {p: sha256((ROOT/p).read_bytes()).hexdigest() for p in tracked_evidence},
            "not_established": [
                "independent proof or formalization of the complete upstream geometric argument",
                "formal connection of the copied T literal to binomial coefficients",
                "a practical finite-size point configuration at the new exponent",
                "novelty or priority of this application of the classical ternary construction",
            ],
        }
    destination = ROOT / "artifacts/verification.json"
    destination.parent.mkdir(exist_ok=True)
    destination.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps({k: report[k] for k in ["status", "source_files_verified", "packing_regressions",
          "determinant_regressions", "eta_original_approx", "eta_ternary_approx", "gain_approx"]}, indent=2))


if __name__ == "__main__":
    main()
