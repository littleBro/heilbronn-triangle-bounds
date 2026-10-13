"""Check the supplied 18-form certificate, independent controls and Lean proofs."""
from copy import deepcopy
from decimal import Decimal, localcontext
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import json
import os
import re
import subprocess

from eighteen_controls import exact_rows, finite_controls, packing_controls, coefficient_control
from patch_controls import check_patch_references
from verify import PIN, read_fraction, require, run_checked
from verify_algebra import verify_algebra
from verify_paired import arithmetic as check_paired
from verify_slab import rejected, scale_constraints
from verify_sphere import repeated_power

ROOT = Path(__file__).resolve().parents[1]
PACKING_MODULES = ["Sphere", "MixedSphere", "MixedLayerData", "MixedLayerCounting",
                   "EighteenLayerData", "EighteenLayer", "EighteenPacking"]


def arithmetic(c, previous):
    require(c["schema"] == "heilbronn-eighteen-v1" and c["upstream_commit"] == PIN, "schema and pin")
    require(c["status"] == "conditional-on-upstream-estimates", "status")
    require(c["scope"] == "paper exponent; not the upstream Lean comparator exponent", "scope")
    require(c["previous_certificate"] == "certificates/paired.json" and
            c["previous_sha256"] == sha256((ROOT/"certificates/paired.json").read_bytes()).hexdigest(), "previous")
    require(c["d"] == 13 and c["T"] == str(25*repeated_power(18, 6)), "term count")
    require(c["decomposition"] == {"pairs": 6, "unpaired_conjugates": 1, "terms_per_pair": 18,
        "extension_determinants": str(repeated_power(18, 6)), "nodes_per_term": 25,
        "pair_identity_multiplier": 3, "normalization_denominator": 729,
        "root_equation": "u^2-u+1=0", "base_characteristic_excludes": [3],
        "formal_base_field_minimum": 25, "manuscript_prime_minimum": 37,
        "manuscript_prime_residue": 1, "manuscript_prime_modulus": 3,
        "formula_source": "https://arxiv.org/abs/1909.04785",
        "row_maps": ["3^(-6) * eval_t", "eval_t", "constantCoord(c_t * input)"]}, "algebra interface")
    rows = [(r+[0]*33)[:33] for r in exact_rows()]
    require(c["packing"] == {"half_alphabets_low_first": [5]*4+[4]*7,
        "radices_low_first": [19]*4+[15]*7, "energy_index": 32, "squared_norm": 267,
        "layer_count": "872130560", "count_table": rows}, "packing")
    require(rows[11][32] >= int(c["T"]), "capacity")
    require(c["prime_transfer"] == {"progression": "1 mod 3",
        "interval": "m < r <= 2m for all sufficiently large m",
        "theorem": "prime number theorem in a fixed arithmetic progression",
        "source": "https://dlmf.nist.gov/27.11", "lean_formalized": False}, "prime transfer")
    k = repeated_power(15, 7)*repeated_power(19, 4)
    require(c["k"] == str(k), "k")
    require(c["cap"] == previous["cap"] and c["scales"] == previous["scales"], "scales")
    beta = Fraction(3*4, 2)*7*k-Fraction(k-1, 2)
    rho = 12*beta
    gamma = rho/(2*rho+1)
    alpha = rho+gamma
    eta = 2*gamma/alpha
    gain = eta/read_fraction(previous["eta"])
    require(c["rho"] == str(rho.numerator) and rho.denominator == 1, "rho")
    for key, v in [("beta", beta), ("gamma", gamma), ("alpha", alpha), ("eta", eta), ("gain_from_paired", gain)]:
        require(read_fraction(c[key]) == v, key)
    require(eta == Fraction(1, 498*k+7), "closed exponent")
    require(Fraction(218, 100) < gain < Fraction(219, 100), "gain enclosure")
    losses, collision, pair = scale_constraints(13, k, 2, 6, 4, gamma)
    require(c["constraints"] == {"zero_case_h_powers": losses,
        "collision_r_power": {"numerator": str(collision.numerator), "denominator": str(collision.denominator)},
        "pair_r_power": {"numerator": str(pair.numerator), "denominator": str(pair.denominator)}}, "constraints")
    require(c["formal_scope"] == {"proved": [
        "18-form identity over a commutative ring with u^2-u+1=0, with multiplier 3",
        "six pairs and one unpaired determinant, normalization 3^6",
        "degree-13 field-norm identity with homogeneous polynomial coordinates",
        "root existence and distinct-label criterion for primes >= 37 congruent to 1 mod 3",
        "exact energy-32 layer and complete mixed-radix packing",
        "inherited integer scale inequalities and exponent identity",
        "gain from paired checkpoint greater than 2.18"],
        "written_not_formalized": previous["formal_scope"]["written_not_formalized"]+
            ["prime number theorem in the progression 1 mod 3 and its interpolation consequence"]}, "formal scope")
    require(c["parameter_choice"] == "explicit feasible witness; no optimality claim", "optimality scope")
    return eta, gain


def main():
    c = json.loads((ROOT/"certificates/eighteen.json").read_text(encoding="utf-8"))
    previous = json.loads((ROOT/"certificates/paired.json").read_text(encoding="utf-8"))
    rankfive = json.loads((ROOT/"certificates/rankfive.json").read_text(encoding="utf-8"))
    check_paired(previous, rankfive)
    eta, gain = arithmetic(c, previous)
    mutations = [("T", str(int(c["T"])-1), "term count"), ("k", str(int(c["k"])-1), "k"),
        ("decomposition", {**c["decomposition"], "pair_identity_multiplier": 1}, "algebra interface"),
        ("decomposition", {**c["decomposition"], "terms_per_pair": 17}, "algebra interface"),
        ("decomposition", {**c["decomposition"], "base_characteristic_excludes": []}, "algebra interface"),
        ("packing", {**c["packing"], "layer_count": "872130561"}, "packing"),
        ("packing", {**c["packing"], "radices_low_first": [18]+[19]*3+[15]*7}, "packing"),
        ("eta", {"numerator": "1", "denominator": str(498*int(c["k"])+6)}, "eta"),
        ("decomposition", {**c["decomposition"], "manuscript_prime_residue": 2}, "algebra interface"),
        ("prime_transfer", {**c["prime_transfer"], "lean_formalized": True}, "prime transfer")]
    for field, value, reason in mutations:
        bad = deepcopy(c)
        bad[field] = value
        rejected(lambda: arithmetic(bad, previous), reason)
    coefficients = coefficient_control()
    finite, packing = finite_controls(), packing_controls()
    manifest = json.loads((ROOT/"upstream/manifest.json").read_text(encoding="utf-8-sig"))
    require(manifest["commit"] == PIN, "upstream pin")
    for item in manifest["files"]:
        data = (ROOT/item["path"]).read_bytes()
        require(sha256(data).hexdigest() == item["sha256"] and len(data) == item["bytes"], "upstream file")
    # Use the actual executable so subprocess timeouts also terminate Lean on Windows.
    lean = run_checked(["elan", "which", "lean"]).strip()
    version = run_checked([lean, "--version"]).strip()
    require("version 4.11.0," in version, "Lean version")
    audit = []
    for module in PACKING_MODULES:
        source = (ROOT/f"lean/{module}.lean").read_text(encoding="utf-8")
        require(not re.search(r"\b(sorry|admit|axiom|unsafe|native_decide)\b", source), "proof escape")
        r = subprocess.run([lean, "-j", "1", "-M", "2048", "-o", f"lean/{module}.olean",
                            f"lean/{module}.lean"], cwd=ROOT, text=True, encoding="utf-8", errors="replace",
                            capture_output=True, timeout=120,
                            env={**os.environ, "LEAN_PATH": str(ROOT/"lean"), "LEAN_NUM_THREADS": "1"})
        require(r.returncode == 0 and "error:" not in r.stdout+r.stderr, "Lean packing:\n"+r.stdout+r.stderr)
        audit.extend((r.stdout+r.stderr).splitlines())
    output = "\n".join(audit)
    require("sorryAx" not in output, "incomplete proof")
    for name in ["exact_layer_count", "layer_capacity", "exact_layer_family", "trace_packing", "trace_gain"]:
        require("'HeilbronnEighteenPacking."+name+"'" in output, "missing audit")
    for entry in re.findall(r"depends on axioms: \[([^]]*)\]", output):
        require(set(entry.split(", ")) <= {"propext", "Classical.choice", "Quot.sound"}, "unexpected axiom")
    algebra = verify_algebra()
    patch = ROOT/"patches/eighteen-norm.patch"
    run_checked(["git", "apply", "--check", "--directory=upstream/manuscript", str(patch)])
    require(patch.read_text(encoding="utf-8").count("\n+++ b/") == 6, "patch coverage")
    references = [check_patch_references(p) for p in
                  ["patches/rank-five.patch", "patches/paired-norm.patch", "patches/eighteen-norm.patch"]]
    evidence = list(dict.fromkeys([*[f"lean/{m}.lean" for m in PACKING_MODULES],
        "scripts/build_eighteen.py", "scripts/verify_eighteen.py", "scripts/eighteen_controls.py",
        "scripts/patch_controls.py", "scripts/build_rankfive.py", "scripts/build_paired.py",
        "patches/rank-five.patch", "patches/paired-norm.patch",
        "scripts/rankfive_controls.py", "scripts/frobenius_controls.py", "scripts/bilinear_controls.py",
        "scripts/norm_controls.py", "scripts/paired_controls.py", "scripts/verify_paired.py",
        "scripts/verify_rankfive.py", "scripts/build_slab.py",
        "scripts/build_sphere.py", "scripts/build_tuned.py", "scripts/verify.py",
        "scripts/verify_slab.py", "scripts/verify_sphere.py", "scripts/search_packing.py", "scripts/search_eighteen.py",
        "certificates/eighteen.json", "certificates/paired.json", "certificates/rankfive.json",
        "patches/eighteen-norm.patch", "upstream/manifest.json", "notes/sphere-packing.tex",
        "README.md", "docs/review.md", "artifacts/eighteen-search.json",
        "artifacts/sphere-latex-status.json", "artifacts/algebra-verification.json", *algebra["evidence_sha256"]]))
    with localcontext() as ctx:
        ctx.prec = 40
        report = {"status": "pass", "lean": version, "upstream_commit": PIN,
            "source_files_verified": len(manifest["files"]),
            "eta_approx": str(Decimal(eta.numerator)/Decimal(eta.denominator)),
            "gain_from_paired_approx": str(Decimal(gain.numerator)/Decimal(gain.denominator)),
            "arithmetic_negative_controls": len(mutations), "finite_controls": finite,
            "coefficient_control": coefficients, "packing_controls": packing, "lean_axiom_audit": audit,
            "algebra_theorems_audited": algebra["audited_theorems"], "patched_sections": 6,
            "patched_manuscript_reference_checks": references,
            "evidence_sha256": {p: sha256((ROOT/p).read_bytes()).hexdigest() for p in evidence},
            "not_established": ["full geometric Heilbronn theorem in Lean", "prime number theorem in Lean", "practical finite-n bounds",
                                "complete independent audit of upstream estimates", "novelty or optimality"]}
    (ROOT/"artifacts/eighteen-verification.json").write_text(json.dumps(report, indent=2)+"\n",
                                                          encoding="utf-8", newline="\n")
    print(json.dumps({k: report[k] for k in ("status", "eta_approx", "gain_from_paired_approx")}, indent=2))


if __name__ == "__main__":
    main()
