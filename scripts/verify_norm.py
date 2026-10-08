"""Exact norm-count arithmetic, field controls and the finite Lean interface."""
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

from norm_controls import finite_controls
from verify import PIN, read_fraction, require, run_checked
from verify_central import arithmetic as check_central
from verify_slab import arithmetic as check_slab, rejected, scale_constraints
from verify_sphere import repeated_power

ROOT = Path(__file__).resolve().parents[1]


def arithmetic(c, previous):
    require(c["schema"] == "heilbronn-norm-compression-v1", "schema")
    require(c["upstream_commit"] == PIN, "pin")
    require(c["status"] == "conditional-on-upstream-estimates", "status")
    require(c["scope"] == "paper exponent; not the upstream Lean comparator exponent", "scope")
    require(c["previous_certificate"] == "certificates/central.json", "previous path")
    require(c["previous_sha256"] == sha256((ROOT / "certificates/central.json").read_bytes()).hexdigest(),
            "previous hash")
    require(c["d"] == 13, "d")
    orbits = 1
    for _ in range(12):
        orbits *= 6
    degree, nodes = 3*(13-1), 3*(13-1)+1
    T = orbits*nodes
    require(c["T"] == str(T) and T == 80540946432, "term bound")
    require(c["decomposition"] == {
        "extension_field_terms": str(orbits), "representative_degree_max": 12,
        "determinant_degree_max": degree, "interpolation_nodes": nodes, "prime_minimum": 37,
        "preserved_interface": "homogeneous degree-d polynomials over F_r; exact norm identity",
        "proof_status": "written algebraic proof; permutation normalization and signs in Lean"},
        "decomposition interface")
    Q = 10*sum(range(12))+1
    N, k = repeated_power(24, 10), repeated_power(47, 10)
    require(T*Q <= N, "sphere capacity")
    require(c["packing"] == {"m": 10, "A": 12, "s": 24, "b": 47, "layers": Q,
            "word_count": str(N), "required_words": str(T*Q)}, "packing")
    require(c["k"] == str(k), "k")
    require(c["cap"] == previous["cap"] and c["scales"] == previous["scales"], "retained scales")
    beta = Fraction(3*4, 2)*(1+6)*k-Fraction(k-1, 2)
    rho = 12*beta
    gamma = rho/(2*rho+1)
    alpha = rho+gamma
    eta = 2*gamma/alpha
    gain = eta/read_fraction(previous["eta"])
    require(c["rho"] == str(rho.numerator) and rho.denominator == 1, "rho")
    for field, value in [("beta", beta), ("gamma", gamma), ("alpha", alpha),
                         ("eta", eta), ("gain_from_central", gain)]:
        require(read_fraction(c[field]) == value, field)
    require(eta == Fraction(1, 498*k+7), "closed exponent")
    require(10**27 < gain < 2*10**27, "gain enclosure")
    losses, collision, pair = scale_constraints(13, k, 2, 6, 4, gamma)
    require(c["constraints"]["zero_case_h_powers"] == losses, "zero powers")
    require(read_fraction(c["constraints"]["collision_r_power"]) == collision, "collision power")
    require(read_fraction(c["constraints"]["pair_r_power"]) == pair, "pair power")
    require(c["formal_scope"] == {
        "proved": ["permutation composition, exhaustive list, signs and normalization bijection",
            "sign identity for 13 determinant factors",
            "complete finite packing for T = 37*6^12, k = 47^10",
            "inherited integer scale inequalities and exponent identity",
            "10^27 < gain from central < 2*10^27"],
        "written_not_formalized": ["norm expansion as determinants over the extension field",
            "polynomial interpolation and descent to the base field",
            "slab cap geometry and short-relation exclusion",
            "lattice, orbit and weighted counting estimates",
            "probability, asymptotic deletion and interpolation"]}, "formal scope")
    require(c["parameter_choice"] == "explicit feasible witness; no optimality claim", "search scope")
    return eta, gain


def main():
    certificates = {name: json.loads((ROOT / f"certificates/{name}.json").read_text(encoding="utf-8"))
                    for name in ["tuned", "slab", "central", "norm"]}
    check_slab(certificates["slab"], certificates["tuned"])
    check_central(certificates["central"], certificates["slab"])
    c, previous = certificates["norm"], certificates["central"]
    eta, gain = arithmetic(c, previous)
    mutations = [
        ("T", str(int(c["T"])-1), "term bound"),
        ("k", str(int(c["k"])-1), "k"),
        ("eta", {"numerator": "1", "denominator": str(498*int(c["k"])+6)}, "eta"),
        ("packing", {**c["packing"], "required_words": str(int(c["packing"]["required_words"])-1)},
         "packing"),
    ]
    for field, value in [("interpolation_nodes", 36), ("prime_minimum", 31)]:
        mutations.append(("decomposition", {**c["decomposition"], field: value}, "decomposition interface"))
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
                "changed upstream: "+item["path"])
    version = run_checked(["lean", "--version"]).strip()
    require("version 4.11.0," in version, "Lean version")
    outputs = []
    for name in ["Sphere", "Tuned", "Slab", "NormCompression"]:
        source = (ROOT / f"lean/{name}.lean").read_text(encoding="utf-8")
        require(not re.search(r"\b(sorry|admit|axiom|unsafe|native_decide)\b", source), "proof escape")
        result = subprocess.run(["lean", "-o", f"lean/{name}.olean", f"lean/{name}.lean"],
            cwd=ROOT, text=True, encoding="utf-8", errors="replace", capture_output=True,
            timeout=30, env={**os.environ, "LEAN_PATH": str(ROOT / "lean")})
        require(result.returncode == 0, "Lean failure:\n"+result.stdout+result.stderr)
        outputs.append(result.stdout+result.stderr)
    audit = "".join(outputs)
    require("sorryAx" not in audit and "error:" not in audit, "incomplete proof")
    for name in ["perm_injective", "perm_distinct", "perm_exhaustive", "comp_apply", "sign_comp",
                 "comp_cancel", "shift_cancel", "shift_signature", "normalization_bijection",
                 "normalized_sign", "norm_count", "norm_capacity", "norm_packing", "norm_gain"]:
        require("'HeilbronnNormCompression."+name+"'" in outputs[-1], "missing audit: "+name)
    for entry in re.findall(r"depends on axioms: \[([^]]*)\]", audit):
        require(set(entry.split(", ")) <= {"propext", "Classical.choice", "Quot.sound"},
                "unexpected axiom")
    patch = ROOT / "patches/norm-compression.patch"
    run_checked(["git", "apply", "--check", "--directory=upstream/manuscript", str(patch)])
    require(patch.read_text(encoding="utf-8").count("\n+++ b/") == 6, "patch coverage")
    evidence = ["lean/NormCompression.lean", "lean/Sphere.lean", "lean/Tuned.lean", "lean/Slab.lean",
        "lean-toolchain", "scripts/build_norm.py", "scripts/verify_norm.py", "scripts/norm_controls.py",
        "scripts/build_slab.py", "scripts/verify_slab.py", "scripts/build_tuned.py",
        "scripts/verify_tuned.py", "scripts/build_sphere.py", "scripts/verify_sphere.py",
        "scripts/build_patch.py", "scripts/verify.py", "scripts/verify_central.py",
        "certificates/norm.json", "certificates/central.json", "certificates/slab.json",
        "certificates/tuned.json", "patches/norm-compression.patch", "upstream/manifest.json",
        "notes/sphere-packing.tex", "README.md", "docs/review.md", "artifacts/sphere-latex-status.json"]
    with localcontext() as ctx:
        ctx.prec = 40
        decimal = lambda f: format(Decimal(f.numerator)/Decimal(f.denominator), ".14E")
        report = {"status": "pass", "python": sys.version, "lean": version,
            "upstream_commit": PIN, "source_files_verified": len(manifest["files"]),
            "eta_approx": decimal(eta), "gain_from_central_approx": decimal(gain),
            "arithmetic_negative_controls": len(mutations), "finite_controls": finite,
            "lean_axiom_audit": audit.splitlines(), "patch_applies": True, "patched_sections": 6,
            "evidence_sha256": {p: sha256((ROOT / p).read_bytes()).hexdigest() for p in evidence},
            "not_established": ["complete Lean proof of norm decomposition and field descent",
                "Lean proof of the slab cap geometry or full geometric theorem",
                "complete independent audit of upstream estimates", "practical finite-n improvement",
                "novelty, priority or global optimality"]}
    (ROOT / "artifacts/norm-verification.json").write_text(
        json.dumps(report, indent=2)+"\n", encoding="utf-8", newline="\n")
    print(json.dumps({key: report[key] for key in
        ["status", "eta_approx", "gain_from_central_approx", "arithmetic_negative_controls",
         "patched_sections"]}, indent=2))


if __name__ == "__main__":
    main()
