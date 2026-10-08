"""Independent arithmetic and bounded native proof checks for the retuned scales."""
from copy import deepcopy
from decimal import Decimal, localcontext
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import json
import os
import re
import subprocess
import sys

from verify import PIN, choose_by_recurrence, read_fraction, require, run_checked
from verify_sphere import compare_parameters, repeated_power

ROOT = Path(__file__).resolve().parents[1]


def scale_constraints(d, k, digit_constant, h_multiplier, q_power, n_power, gamma):
    require(d % 2 == 1 and d >= 3, "odd norm dimension")
    require(k >= 2 and 0 < gamma, "positive sample growth")
    theta = Fraction(200, digit_constant)
    require(theta <= Fraction(1, 2), "claimed moment bound")
    require(h_multiplier >= 2, "unchanged shell moment range")
    # The generic equal-pair case is the strongest of the three zero cases.
    zero_powers = [2 + 12 - q_power, 2 + 6 - q_power, 2 + 12 - 2 * q_power]
    require(max(zero_powers) <= 0, "zero-case growth")
    collision_power = 2 * gamma + 12 - d
    require(collision_power < 0, "collision deletion")
    pair_power = (gamma + 12 * (6 - Fraction(3 * n_power, 2)) *
                  (1 + q_power) * k - 6 * (k - 1))
    require(pair_power < 0, "pair deletion")
    return theta, collision_power, pair_power, zero_powers


def arithmetic(c):
    require(c["schema"] == "heilbronn-tuned-scales-v1", "schema")
    require(c["upstream_commit"] == PIN, "pin")
    require(c["status"] == "conditional-on-upstream-estimates", "status")
    require(c["scope"] == "paper exponent; not the upstream Lean comparator exponent", "scope")
    require(c["d"] == 13, "d")
    monomials = choose_by_recurrence(51, 13)
    terms, remainder = divmod(monomials**3 - 3 * monomials**2 + 2 * monomials, 6)
    require(remainder == 0 and c["M"] == str(monomials), "M")
    require(c["T"] == str(terms), "T")
    require((c["dimension"], c["half_alphabet"]) == (17, 101), "sphere parameters")
    require((c["alphabet"], c["base"]) == (202, 403), "encoding base")
    layers = 17 * sum(range(101)) + 1
    cube, k = repeated_power(202, 17), repeated_power(403, 17)
    require(c["energy_layers"] == layers, "layers")
    require(c["cube_size"] == str(cube), "cube")
    require(c["required_capacity"] == str(terms * layers), "capacity value")
    require(terms * layers <= cube, "capacity")
    require(c["k"] == str(k), "k")
    require(c["scales"] == {
        "L": "400*k^2*r^4", "B": "100*k^2*L^3 < B <= 200*k^2*L^3; B prime",
        "h": "B^k", "tau": "floor(B^(k-1)/2)",
        "H": "2*h", "q": "h^14 < q <= 2*h^14; q prime",
        "N": "(h*q)^4", "n_r": "floor(r^gamma*sqrt(N^3/tau))",
    }, "scales")
    # Derive the exponent directly from B ~ r^12, q ~ h^14, N = (hq)^4.
    beta = Fraction(3 * 4, 2) * (1 + 14) * k - Fraction(k - 1, 2)
    rho = 12 * beta
    gamma = rho / (2 * rho + 1)
    alpha = rho + gamma
    eta = 2 * gamma / alpha
    require(c["rho"] == str(rho.numerator) and rho.denominator == 1, "rho")
    for name, value in [("gamma", gamma), ("beta", beta), ("alpha", alpha), ("eta", eta)]:
        require(read_fraction(c[name]) == value, name)
    require(eta == Fraction(1, 1074 * k + 7), "closed exponent")
    theta, collision, pair, zero = scale_constraints(13, k, 400, 2, 14, 4, gamma)
    constraints = c["constraints"]
    require(read_fraction(constraints["theta_upper"]) == theta, "theta")
    require(read_fraction(constraints["collision_r_power"]) == collision, "collision power")
    require(read_fraction(constraints["pair_r_power"]) == pair, "pair power")
    require(constraints["zero_case_h_powers"] == zero, "zero powers")
    require(constraints["cap_condition"] == "h >= 3 implies 2000*(2*h)^2 <= h^14 < q",
            "cap condition")
    require(8000 <= 3**12, "cap constant")
    previous = Fraction(2, 45435 * repeated_power(40011, 29) + 16)
    old_m = choose_by_recurrence(163, 41)
    old_t = old_m * (old_m - 1) * (old_m - 2) // 6
    original = Fraction(2, 45435 * (old_t * old_t + 1) + 16)
    gains = eta / previous, eta / original
    require(read_fraction(c["gain_from_previous_sphere"]) == gains[0], "previous gain")
    require(read_fraction(c["gain_from_original"]) == gains[1], "original gain")
    require(3 * 10**90 < gains[0] < 4 * 10**90, "gain enclosure")
    require(c["parameter_comparison"] == {
        "dimensions_inclusive": [3, 284], "claim": "bounded sphere comparison only"
    }, "comparison scope")
    require(c["formal_scope"] == {
        "proved": ["complete finite packing with binomial T for d=13",
                   "digit divisibility and moment inequality",
                   "shell threshold, cap modulus and three zero-case inequalities",
                   "cleared-denominator alteration inequalities and exponent identity",
                   "exact gain enclosure"],
        "written_not_formalized": ["field norm and determinant decomposition",
            "upstream lattice, orbit, auxiliary and weighted counting arguments",
            "probability, asymptotic deletion and interpolation",
            "parameter comparison monotonicity"],
    }, "formal scope")
    return eta, gains, gamma


def main():
    certificate = json.loads((ROOT / "certificates/tuned.json").read_text(encoding="utf-8"))
    eta, gains, gamma = arithmetic(certificate)
    k = int(certificate["k"])
    negative_scales = [
        ((11, k, 400, 2, 14, 4, gamma), "collision deletion"),
        ((13, k, 400, 2, 13, 4, gamma), "zero-case growth"),
        ((13, k, 400, 1, 14, 4, gamma), "unchanged shell moment range"),
        ((13, k, 400, 2, 14, 3, gamma), "pair deletion"),
        ((13, k, 399, 2, 14, 4, gamma), "claimed moment bound"),
    ]
    for arguments, reason in negative_scales:
        try:
            scale_constraints(*arguments)
        except AssertionError as error:
            require(str(error) == reason, "wrong scale rejection")
        else:
            raise AssertionError("invalid scale change accepted")
    for field, value, reason in [
        ("T", str(int(certificate["T"]) - 1), "T"),
        ("energy_layers", 85850, "layers"),
        ("k", str(k - 1), "k"),
        ("eta", {"numerator": "1", "denominator": str(1074 * k + 6)}, "eta"),
    ]:
        bad = deepcopy(certificate)
        bad[field] = value
        try:
            arithmetic(bad)
        except AssertionError as error:
            require(str(error) == reason, "wrong certificate rejection")
        else:
            raise AssertionError("corrupted certificate accepted")

    comparison = compare_parameters(int(certificate["T"]), k)
    manifest = json.loads((ROOT / "upstream/manifest.json").read_text(encoding="utf-8-sig"))
    require(manifest["commit"] == PIN, "manifest pin")
    for item in manifest["files"]:
        data = (ROOT / item["path"]).read_bytes()
        require(sha256(data).hexdigest() == item["sha256"] and len(data) == item["bytes"],
                "changed upstream: " + item["path"])
    for name in ["Sphere", "Tuned"]:
        source = (ROOT / f"lean/{name}.lean").read_text(encoding="utf-8")
        require(not re.search(r"\b(sorry|admit|axiom|unsafe|native_decide)\b", source), "proof escape")
    require(re.search(r"def tunedT : Nat := " + certificate["T"] + r"\b", source), "Lean T")
    version = run_checked(["lean", "--version"]).strip()
    require("version 4.11.0," in version, "Lean version")
    # Always rebuild the imported proof from its audited source.
    sphere_output = run_checked(["lean", "-o", "lean/Sphere.olean", "lean/Sphere.lean"])
    compiled = subprocess.run(["lean", "lean/Tuned.lean"], cwd=ROOT, text=True,
        encoding="utf-8", errors="replace", capture_output=True, timeout=30,
        env={**os.environ, "LEAN_PATH": str(ROOT / "lean")})
    lean_output = compiled.stdout + compiled.stderr
    require(compiled.returncode == 0, "Lean failure:\n" + lean_output)
    audit = sphere_output + lean_output
    require("sorryAx" not in audit and "error:" not in audit, "incomplete formal proof")
    for name in ["tunedT_binomial", "tuned_capacity", "tuned_packing", "digit_scale_divisible",
                 "digit_moment_bound", "shell_threshold", "cap_modulus", "zero_case_bounds",
                 "alteration_constraints", "exponent_identity", "tuned_gain"]:
        require("'HeilbronnTuned." + name + "'" in lean_output, "missing axiom audit")
    for entry in re.findall(r"depends on axioms: \[([^]]*)\]", audit):
        require(set(entry.split(", ")) <= {"propext", "Classical.choice", "Quot.sound"},
                "unexpected axiom")
    patch = ROOT / "patches/tuned-parameters.patch"
    run_checked(["git", "apply", "--check", "--directory=upstream/manuscript", str(patch)])
    require(patch.read_text(encoding="utf-8").count("\n+++ b/") == 6, "patch section coverage")
    evidence = ["lean/Sphere.lean", "lean/Tuned.lean", "lean-toolchain",
                "scripts/build_tuned.py", "scripts/verify_tuned.py", "scripts/build_sphere.py",
                "scripts/verify_sphere.py", "scripts/verify.py", "scripts/build_patch.py",
                "certificates/tuned.json", "patches/tuned-parameters.patch",
                "notes/sphere-packing.tex", "README.md", "NOTICE", "upstream/manifest.json",
                "artifacts/sphere-latex-status.json"]
    with localcontext() as ctx:
        ctx.prec = 40
        decimal = lambda f: format(Decimal(f.numerator) / Decimal(f.denominator), ".14E")
        report = {
            "status": "pass", "python": sys.version, "lean": version, "upstream_commit": PIN,
            "source_files_verified": len(manifest["files"]),
            "eta_approx": decimal(eta), "gain_from_previous_sphere_approx": decimal(gains[0]),
            "gain_from_original_approx": decimal(gains[1]),
            "scale_negative_controls": [reason for _, reason in negative_scales],
            "negative_control_scope": "failure of the stated sufficient bounds, not impossibility",
            "arithmetic_negative_controls": 4, "parameter_comparison": comparison,
            "lean_axiom_audit": audit.splitlines(), "patch_applies": True,
            "patched_sections": 6,
            "evidence_sha256": {p: sha256((ROOT / p).read_bytes()).hexdigest() for p in evidence},
            "not_established": [
                "complete independent proof or Lean formalization of the geometric theorem",
                "formal asymptotic, probability, field-norm or lattice proofs",
                "formal or unrestricted parameter optimality",
                "practical construction of the full sphere or planar point set",
                "novelty, priority or independent review",
            ],
        }
    (ROOT / "artifacts/tuned-verification.json").write_text(
        json.dumps(report, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps({key: report[key] for key in [
        "status", "eta_approx", "gain_from_previous_sphere_approx", "gain_from_original_approx",
        "scale_negative_controls", "patched_sections"]}, indent=2))


if __name__ == "__main__":
    main()
