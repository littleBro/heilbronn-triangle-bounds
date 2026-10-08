"""Independent exact moments, finite controls and core Lean packing proof."""
from collections import Counter
from copy import deepcopy
from decimal import Decimal, localcontext
from fractions import Fraction
from hashlib import sha256
from itertools import product
from pathlib import Path
import json
import os
import re
import subprocess
import sys

from verify import PIN, choose_by_recurrence, read_fraction, require, run_checked
from verify_sphere import repeated_power
from verify_slab import arithmetic as check_slab, rejected, scale_constraints

ROOT = Path(__file__).resolve().parents[1]


def arithmetic(c, previous):
    require(c["schema"] == "heilbronn-central-sphere-v1", "schema")
    require(c["upstream_commit"] == PIN, "pin")
    require(c["status"] == "conditional-on-upstream-estimates", "status")
    require(c["scope"] == "paper exponent; not the upstream Lean comparator exponent", "scope")
    require(c["previous_certificate"] == "certificates/slab.json", "previous path")
    require(c["previous_sha256"] == sha256((ROOT / "certificates/slab.json").read_bytes()).hexdigest(),
            "previous hash")
    require((c["d"], c["m"], c["A"], c["s"], c["b"]) == (13, 17, 95, 190, 379), "parameters")
    M = choose_by_recurrence(51, 13)
    T, remainder = divmod(M**3 - 3*M**2 + 2*M, 6)
    require(remainder == 0 and c["M"] == str(M) and c["T"] == str(T), "binomial counts")
    k = repeated_power(379, 17)
    require(c["k"] == str(k), "k")
    # Derive the triangular energies independently from centered coordinates.
    energies = [((2*d-189)**2-1)//8 for d in range(190)]
    require(all(((2*d-189)**2-1) % 8 == 0 for d in range(190)), "energy divisibility")
    mu = Fraction(sum(energies), len(energies))
    require(mu == 1504, "digit mean")
    scores = [int(j-mu) for j in energies]
    require(sum(scores) == 0, "digit centering")
    digit_square = sum(z*z for z in scores)
    # Unlike the generator's closed formula, propagate both the word count
    # and second moment through the Cartesian-product recurrence.
    N, V = 1, 0
    for _ in range(17):
        V, N = 190*V + N*digit_square, 190*N
    center, radius, layers, distance = 17*int(mu), 10000, 20001, 10001
    lower = N - V // (distance*distance)
    margin = N*distance*distance - V - layers*T*distance*distance
    require(margin >= 0 and lower >= layers*T, "central capacity")
    require(c["energy"] == {
        "digit_mean": int(mu), "digit_centered_sum": "0",
        "digit_centered_square_sum": str(digit_square), "center": center,
        "radius": radius, "lower": center-radius, "upper": center+radius,
        "layer_count": layers, "outside_distance": distance,
        "word_count": str(N), "centered_square_sum": str(V),
        "central_word_lower_bound": str(lower), "required_words": str(layers*T),
        "capacity_margin": str(margin)}, "energy certificate")
    require(c["cap"] == previous["cap"] and c["scales"] == previous["scales"], "retained scales")
    beta = Fraction(3*4, 2)*(1+6)*k - Fraction(k-1, 2)
    rho = 12*beta
    gamma = rho / (2*rho+1)
    alpha = rho+gamma
    eta = 2*gamma/alpha
    gain = eta / read_fraction(previous["eta"])
    require(c["rho"] == str(rho.numerator) and rho.denominator == 1, "rho")
    for field, value in [("beta", beta), ("gamma", gamma), ("alpha", alpha),
                         ("eta", eta), ("gain_from_slab", gain)]:
        require(read_fraction(c[field]) == value, field)
    require(eta == Fraction(1, 498*k+7), "closed exponent")
    require(Fraction(284, 100) < gain < Fraction(285, 100), "gain enclosure")
    losses, collision, pair = scale_constraints(13, k, 2, 6, 4, gamma)
    require(c["constraints"]["zero_case_h_powers"] == losses, "zero powers")
    require(read_fraction(c["constraints"]["collision_r_power"]) == collision, "collision power")
    require(read_fraction(c["constraints"]["pair_r_power"]) == pair, "pair power")
    require(c["formal_scope"] == {
        "proved": ["symbolic word count, distinctness, first and second moments",
            "central-window count and finite pigeonhole selection",
            "complete finite packing for T = binom(binom(51,13),3), k = 379^17",
            "inherited integer scale inequalities and exponent identity",
            "284/100 < gain from slab < 285/100"],
        "written_not_formalized": ["slab cap geometry and short-relation exclusion",
            "field norm, lattice, orbit and weighted counting estimates",
            "probability, asymptotic deletion and interpolation"]}, "formal scope")
    require(c["parameter_choice"] == "explicit feasible witness; no optimality claim", "search scope")
    return eta, gain


def finite_controls():
    cases = []
    for A, m in [(2, 2), (2, 4), (5, 1), (5, 2), (5, 3), (7, 2)]:
        s = 2*A
        digits = [Fraction((2*d-(s-1))**2-1, 8) for d in range(s)]
        mean = sum(digits)/s
        center = m*mean
        require(center.denominator == 1, "integral control center")
        layers = Counter(sum(digits[d] for d in w) for w in product(range(s), repeat=m))
        V = sum(count*(j-center)**2 for j, count in layers.items())
        predicted = m*s**(m-1)*sum((j-mean)**2 for j in digits)
        require(V == predicted, "finite second moment")
        R = A*m
        central = sum(count for j, count in layers.items() if abs(j-center) <= R)
        lower = s**m - V // (R+1)**2
        require(central >= lower, "finite tail bound")
        maximum = max(count for j, count in layers.items() if abs(j-center) <= R)
        require((2*R+1)*maximum >= central, "finite pigeonhole")
        cases.append({"A": A, "m": m, "words": s**m, "radius": R,
                      "central_words": central, "lower_bound": int(lower)})
    return cases


def main():
    c = json.loads((ROOT / "certificates/central.json").read_text(encoding="utf-8"))
    previous = json.loads((ROOT / "certificates/slab.json").read_text(encoding="utf-8"))
    tuned = json.loads((ROOT / "certificates/tuned.json").read_text(encoding="utf-8"))
    check_slab(previous, tuned)
    eta, gain = arithmetic(c, previous)
    mutations = [
        ("k", str(int(c["k"])-1), "k"),
        ("eta", {"numerator": "1", "denominator": str(498*int(c["k"])+6)}, "eta"),
    ]
    for field, value in [("digit_centered_square_sum", "343855007"),
                         ("outside_distance", 10002), ("layer_count", 20000),
                         ("capacity_margin", str(int(c["energy"]["capacity_margin"])+1))]:
        mutations.append(("energy", {**c["energy"], field: value}, "energy certificate"))
    for field, value, reason in mutations:
        bad = deepcopy(c)
        bad[field] = value
        rejected(lambda: arithmetic(bad, previous), reason)
    finite = finite_controls()
    manifest = json.loads((ROOT / "upstream/manifest.json").read_text(encoding="utf-8-sig"))
    require(manifest["commit"] == PIN, "manifest pin")
    for item in manifest["files"]:
        data = (ROOT / item["path"]).read_bytes()
        require(sha256(data).hexdigest() == item["sha256"] and len(data) == item["bytes"],
                "changed upstream: " + item["path"])
    version = run_checked(["lean", "--version"]).strip()
    require("version 4.11.0," in version, "Lean version")
    outputs = []
    for name in ["Sphere", "Tuned", "Slab", "Central"]:
        source = (ROOT / f"lean/{name}.lean").read_text(encoding="utf-8")
        require(not re.search(r"\b(sorry|admit|axiom|unsafe|native_decide)\b", source), "proof escape")
        result = subprocess.run(["lean", "-o", f"lean/{name}.olean", f"lean/{name}.lean"],
            cwd=ROOT, text=True, encoding="utf-8", errors="replace", capture_output=True,
            timeout=30, env={**os.environ, "LEAN_PATH": str(ROOT / "lean")})
        require(result.returncode == 0, "Lean failure:\n" + result.stdout + result.stderr)
        outputs.append(result.stdout + result.stderr)
    audit = "".join(outputs)
    require("sorryAx" not in audit and "error:" not in audit, "incomplete proof")
    for name in ["digits_nodup", "digit_mean", "digit_square", "words_length", "words_nodup",
                 "words_mean", "words_square", "score_energy", "central_count_bound",
                 "central_capacity", "central_family", "central_packing", "central_packing_binomial",
                 "moment_value", "capacity_arithmetic", "central_gain"]:
        require("'HeilbronnCentral." + name + "'" in outputs[-1], "missing audit: " + name)
    for entry in re.findall(r"depends on axioms: \[([^]]*)\]", audit):
        require(set(entry.split(", ")) <= {"propext", "Classical.choice", "Quot.sound"},
                "unexpected axiom")
    patch = ROOT / "patches/central-sphere.patch"
    run_checked(["git", "apply", "--check", "--directory=upstream/manuscript", str(patch)])
    require(patch.read_text(encoding="utf-8").count("\n+++ b/") == 6, "patch coverage")
    evidence = ["lean/Central.lean", "lean/Sphere.lean", "lean/Tuned.lean", "lean/Slab.lean",
        "lean-toolchain", "scripts/build_central.py", "scripts/verify_central.py",
        "scripts/build_slab.py", "scripts/verify_slab.py", "scripts/build_tuned.py",
        "scripts/verify_tuned.py", "scripts/build_sphere.py", "scripts/verify_sphere.py",
        "scripts/build_patch.py", "scripts/verify.py", "certificates/central.json",
        "certificates/slab.json", "certificates/tuned.json", "patches/central-sphere.patch",
        "upstream/manifest.json", "notes/sphere-packing.tex", "README.md", "docs/review.md",
        "artifacts/sphere-latex-status.json"]
    with localcontext() as ctx:
        ctx.prec = 40
        decimal = lambda f: format(Decimal(f.numerator)/Decimal(f.denominator), ".14E")
        report = {"status": "pass", "python": sys.version, "lean": version,
            "upstream_commit": PIN, "source_files_verified": len(manifest["files"]),
            "eta_approx": decimal(eta), "gain_from_slab_approx": decimal(gain),
            "arithmetic_negative_controls": len(mutations), "finite_controls": finite,
            "finite_control_scope": "small Cartesian products; universal result proved in Lean",
            "lean_axiom_audit": audit.splitlines(), "patch_applies": True, "patched_sections": 6,
            "evidence_sha256": {p: sha256((ROOT / p).read_bytes()).hexdigest() for p in evidence},
            "not_established": ["Lean proof of the slab cap geometry or full geometric theorem",
                "complete independent audit of upstream estimates", "practical finite-n improvement",
                "novelty, priority or global optimality"]}
    (ROOT / "artifacts/central-verification.json").write_text(
        json.dumps(report, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps({key: report[key] for key in
        ["status", "eta_approx", "gain_from_slab_approx", "arithmetic_negative_controls",
         "finite_controls", "patched_sections"]}, indent=2))


if __name__ == "__main__":
    main()
