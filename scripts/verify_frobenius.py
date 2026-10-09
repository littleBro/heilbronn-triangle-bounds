"""Check the orbit-compressed norm, exact ten-digit layer, and retained scales."""
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

from bilinear_controls import composition_count, exact_rows
from frobenius_controls import finite_controls
from verify import PIN, read_fraction, require, run_checked
from verify_algebra import verify_algebra
from verify_bilinear import arithmetic as check_bilinear
from verify_norm import arithmetic as check_norm
from verify_slab import rejected, scale_constraints
from verify_sphere import repeated_power

ROOT = Path(__file__).resolve().parents[1]


def arithmetic(c, previous, rows):
    require(c["schema"] == "heilbronn-frobenius-orbits-v1", "schema")
    require(c["upstream_commit"] == PIN, "pin")
    require(c["status"] == "conditional-on-upstream-estimates", "status")
    require(c["scope"] == "paper exponent; not the upstream Lean comparator exponent", "scope")
    require(c["previous_certificate"] == "certificates/bilinear.json", "previous path")
    require(c["previous_sha256"] == sha256((ROOT / "certificates/bilinear.json").read_bytes()).hexdigest(),
            "previous hash")
    patterns = repeated_power(6, 12)
    require((patterns-1) % 13 == 0, "nonfixed orbit divisibility")
    classes = 1+(patterns-1)//13
    require(classes == 167444796 and c["d"] == 13 and c["T"] == str(25*classes), "term count")
    require(c["decomposition"] == {
        "normalized_patterns": str(patterns), "fixed_patterns": 1,
        "nontrivial_orbit_size": 13, "classes": str(classes), "nodes_per_class": 25,
        "singleton_uses_full_descent": True, "base_characteristic_not": 13,
        "formal_base_field_minimum": 25, "retained_manuscript_prime_minimum": 37,
        "projection": "L(z) = sum_a ell(a(z)) / 13",
        "row_maps": ["orbit_size * epsilon_w * eval_t", "eval_t", "L(c_t * input)"]}, "orbit interface")
    require(rows[10][80] == composition_count(10, 80) == 5058395136, "independent layer count")
    require(c["packing"] == {
        "m": 10, "A": 7, "s": 14, "b": 27, "energy_index": 80, "squared_norm": 650,
        "layer_count": str(rows[10][80]), "digit_energies": [0, 1, 3, 6, 10, 15, 21],
        "multiplicity": 2, "count_table_source": "certificates/bilinear.json"}, "layer data")
    require(rows[10][80] >= int(c["T"]), "layer capacity")
    k = repeated_power(27, 10)
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
                         ("eta", eta), ("gain_from_bilinear", gain)]:
        require(read_fraction(c[field]) == value, field)
    require(eta == Fraction(1, 498*k+7) and Fraction(2699, 100) < gain < 27, "exponent and gain")
    losses, collision, pair = scale_constraints(13, k, 2, 6, 4, gamma)
    require(c["constraints"]["zero_case_h_powers"] == losses, "zero powers")
    require(read_fraction(c["constraints"]["collision_r_power"]) == collision, "collision power")
    require(read_fraction(c["constraints"]["pair_r_power"]) == pair, "pair power")
    require(c["formal_scope"] == {"proved": [
        "normalized permutation action, unique fixed pattern and exact orbit count",
        "signed field-norm equivariance and invariant projection fixing the base field",
        "orbit-weighted degree-13 field-norm identity with homogeneous polynomial coordinates",
        "nonzero residue exactly for distinct labels for every prime >= 37",
        "exact energy-80 layer count from the checked recurrence table",
        "complete finite packing for T = 4186119900 and k = 27^10",
        "inherited integer scale inequalities and exponent identity",
        "26.99 < gain from bilinear checkpoint < 27"],
        "written_not_formalized": previous["formal_scope"]["written_not_formalized"]}, "formal scope")
    require(c["parameter_choice"] == "explicit feasible witness; no optimality claim", "search scope")
    return eta, gain


def main():
    c = json.loads((ROOT / "certificates/frobenius.json").read_text(encoding="utf-8"))
    previous = json.loads((ROOT / "certificates/bilinear.json").read_text(encoding="utf-8"))
    norm = json.loads((ROOT / "certificates/norm.json").read_text(encoding="utf-8"))
    central = json.loads((ROOT / "certificates/central.json").read_text(encoding="utf-8"))
    check_norm(norm, central)
    rows = exact_rows()
    check_bilinear(previous, norm, rows)
    eta, gain = arithmetic(c, previous, rows)
    mutations = [
        ("T", str(int(c["T"])-1), "term count"),
        ("k", str(int(c["k"])-1), "k"),
        ("decomposition", {**c["decomposition"], "fixed_patterns": 0}, "orbit interface"),
        ("decomposition", {**c["decomposition"], "classes": str((6**12)//13)}, "orbit interface"),
        ("decomposition", {**c["decomposition"], "nodes_per_class": 24}, "orbit interface"),
        ("decomposition", {**c["decomposition"], "base_characteristic_not": None}, "orbit interface"),
        ("packing", {**c["packing"], "energy_index": 79}, "layer data"),
        ("packing", {**c["packing"], "layer_count": str(rows[10][80]+1)}, "layer data"),
        ("eta", {"numerator": "1", "denominator": str(498*int(c["k"])+6)}, "eta"),
    ]
    for field, value, reason in mutations:
        bad = deepcopy(c)
        bad[field] = value
        rejected(lambda: arithmetic(bad, previous, rows), reason)
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
    for name in ["Sphere", "ExactLayerData", "ExactLayer", "FrobeniusPacking"]:
        source = (ROOT / f"lean/{name}.lean").read_text(encoding="utf-8")
        require(not re.search(r"\b(sorry|admit|axiom|unsafe|native_decide)\b", source), "proof escape")
        result = subprocess.run(["lean", "-j", "1", "-M", "2048", "-o",
            f"lean/{name}.olean", f"lean/{name}.lean"], cwd=ROOT, text=True, encoding="utf-8",
            errors="replace", capture_output=True, timeout=120,
            env={**os.environ, "LEAN_PATH": str(ROOT / "lean"), "LEAN_NUM_THREADS": "1"})
        require(result.returncode == 0, "Lean failure:\n"+result.stdout+result.stderr)
        outputs.append(result.stdout+result.stderr)
    audit = "".join(outputs)
    require("sorryAx" not in audit and "error:" not in audit, "incomplete proof")
    for name in ["exact_layer_count", "layer_capacity", "exact_layer_family", "trace_packing", "trace_gain"]:
        require("'HeilbronnFrobeniusPacking."+name+"'" in outputs[-1], "missing audit: "+name)
    for entry in re.findall(r"depends on axioms: \[([^]]*)\]", audit):
        require(set(entry.split(", ")) <= {"propext", "Classical.choice", "Quot.sound"}, "unexpected axiom")
    algebra = verify_algebra()
    patch = ROOT / "patches/frobenius-orbits.patch"
    run_checked(["git", "apply", "--check", "--directory=upstream/manuscript", str(patch)])
    require(patch.read_text(encoding="utf-8").count("\n+++ b/") == 6, "patch coverage")
    evidence = list(dict.fromkeys([
        "lean/Sphere.lean", "lean/ExactLayerData.lean", "lean/ExactLayer.lean", "lean/FrobeniusPacking.lean",
        "scripts/build_frobenius.py", "scripts/verify_frobenius.py", "scripts/frobenius_controls.py",
        "scripts/verify_bilinear.py", "scripts/build_bilinear.py", "scripts/bilinear_controls.py",
        "scripts/verify_norm.py", "scripts/build_norm.py", "scripts/norm_controls.py",
        "scripts/verify.py", "scripts/verify_slab.py", "scripts/verify_sphere.py",
        "scripts/build_sphere.py", "scripts/build_slab.py", "scripts/build_tuned.py",
        "certificates/frobenius.json", "certificates/bilinear.json", "certificates/norm.json",
        "certificates/central.json", "patches/frobenius-orbits.patch", "upstream/manifest.json",
        "notes/sphere-packing.tex", "README.md", "docs/review.md", "artifacts/sphere-latex-status.json",
        "artifacts/algebra-verification.json", *algebra["evidence_sha256"],
    ]))
    with localcontext() as ctx:
        ctx.prec = 40
        decimal = lambda f: format(Decimal(f.numerator)/Decimal(f.denominator), ".14E")
        report = {"status": "pass", "python": sys.version, "lean": version,
            "upstream_commit": PIN, "source_files_verified": len(manifest["files"]),
            "eta_approx": decimal(eta), "gain_from_bilinear_approx": decimal(gain),
            "gain_interval": "26.99 < gain < 27", "arithmetic_negative_controls": len(mutations),
            "finite_controls": finite, "layer_controls": {"energy": 80, "count": str(rows[10][80]),
                "independent_multinomial_count": str(composition_count(10, 80)),
                "checked_table_source": "certificates/bilinear.json"},
            "lean_axiom_audit": audit.splitlines(), "algebra_theorems_audited": algebra["audited_theorems"],
            "patch_applies": True, "patched_sections": 6,
            "evidence_sha256": {p: sha256((ROOT / p).read_bytes()).hexdigest() for p in evidence},
            "not_established": ["Lean proof of slab cap geometry or full geometric theorem",
                "complete independent audit of upstream estimates", "practical finite-n improvement",
                "novelty, priority or global optimality"]}
    (ROOT / "artifacts/frobenius-verification.json").write_text(
        json.dumps(report, indent=2)+"\n", encoding="utf-8", newline="\n")
    print(json.dumps({key: report[key] for key in
        ["status", "eta_approx", "gain_interval", "arithmetic_negative_controls", "patched_sections"]}, indent=2))


if __name__ == "__main__":
    main()
