"""Check the supplied rank-five certificate, independent controls and Lean proofs."""
from copy import deepcopy
from decimal import Decimal, localcontext
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import json
import os
import re
import subprocess

from rankfive_controls import exact_rows, finite_controls, packing_controls
from bilinear_controls import exact_rows as previous_rows
from verify import PIN, read_fraction, require, run_checked
from verify_algebra import verify_algebra
from verify_norm import arithmetic as check_norm
from verify_bilinear import arithmetic as check_bilinear
from verify_frobenius import arithmetic as check_frobenius
from verify_slab import rejected, scale_constraints
from verify_sphere import repeated_power

ROOT = Path(__file__).resolve().parents[1]
PACKING_MODULES = ["Sphere", "MixedSphere", "MixedLayerData", "MixedLayerCounting",
                   "MixedLayerRows0", "MixedLayerRows1", "MixedLayerRows2", "MixedLayer", "RankFivePacking"]


def arithmetic(c, previous):
    require(c["schema"] == "heilbronn-rank-five-v1" and c["upstream_commit"] == PIN, "schema and pin")
    require(c["status"] == "conditional-on-upstream-estimates", "status")
    require(c["scope"] == "paper exponent; not the upstream Lean comparator exponent", "scope")
    require(c["previous_certificate"] == "certificates/frobenius.json" and
            c["previous_sha256"] == sha256((ROOT/"certificates/frobenius.json").read_bytes()).hexdigest(), "previous")
    patterns = repeated_power(5, 13)
    require((patterns-5) % 13 == 0, "orbit divisibility")
    classes = 5+(patterns-5)//13
    require(c["d"] == 13 and c["T"] == str(25*classes) and classes == 93900245, "term count")
    require(c["decomposition"] == {"patterns": str(patterns), "fixed_patterns": 5,
        "nontrivial_orbit_size": 13, "classes": str(classes), "nodes_per_class": 25,
        "antisymmetrization_divisor": 6, "base_characteristic_excludes": [2, 3, 13],
        "formal_base_field_minimum": 25, "retained_manuscript_prime_minimum": 37,
        "formula_source": "https://arxiv.org/abs/1801.00496",
        "row_maps": ["orbit_size / 6 * eval_t", "eval_t", "L(c_t * input)"]}, "algebra interface")
    rows = [(r+[0]*120)[:120] for r in exact_rows()]
    require(c["packing"] == {"half_alphabets_low_first": [10]+[9]*8, "radices_low_first": [39]+[35]*8,
        "energy_index": 119, "squared_norm": 961, "layer_count": "2365025280", "count_table": rows}, "packing")
    require(rows[9][119] >= 25*classes, "capacity")
    k = 39*repeated_power(35, 8)
    require(c["k"] == str(k), "k")
    require(c["cap"] == previous["cap"] and c["scales"] == previous["scales"], "scales")
    beta = Fraction(3*4, 2)*7*k-Fraction(k-1, 2)
    rho = 12*beta
    gamma = rho/(2*rho+1)
    alpha = rho+gamma
    eta = 2*gamma/alpha
    gain = eta/read_fraction(previous["eta"])
    require(c["rho"] == str(rho.numerator) and rho.denominator == 1, "rho")
    for key, v in [("beta", beta), ("gamma", gamma), ("alpha", alpha), ("eta", eta),
                   ("gain_from_frobenius", gain)]:
        require(read_fraction(c[key]) == v, key)
    require(eta == Fraction(1, 498*k+7) and Fraction(234, 100) < gain < Fraction(235, 100), "gain")
    losses, collision, pair = scale_constraints(13, k, 2, 6, 4, gamma)
    require(c["constraints"]["zero_case_h_powers"] == losses and
            read_fraction(c["constraints"]["collision_r_power"]) == collision and
            read_fraction(c["constraints"]["pair_r_power"]) == pair, "scale constraints")
    require(c["formal_scope"] == {"proved": [
        "integral five-term determinant formula and degree-thirteen antisymmetrization",
        "five-letter rotation action, five fixed patterns and exact orbit count",
        "degree-13 field-norm identity with homogeneous polynomial coordinates",
        "nonzero residue exactly for distinct labels for every prime >= 37",
        "exact mixed-sphere energy-119 count and complete finite packing",
        "inherited integer scale inequalities and exponent identity",
        "gain from Frobenius checkpoint greater than 2.34"],
        "written_not_formalized": previous["formal_scope"]["written_not_formalized"]}, "formal scope")
    require(c["parameter_choice"] == "explicit feasible witness; no optimality claim", "optimality scope")
    return eta, gain


def main():
    c = json.loads((ROOT/"certificates/rankfive.json").read_text(encoding="utf-8"))
    previous = json.loads((ROOT/"certificates/frobenius.json").read_text(encoding="utf-8"))
    bilinear = json.loads((ROOT/"certificates/bilinear.json").read_text(encoding="utf-8"))
    norm = json.loads((ROOT/"certificates/norm.json").read_text(encoding="utf-8"))
    central = json.loads((ROOT/"certificates/central.json").read_text(encoding="utf-8"))
    check_norm(norm, central)
    old_rows = previous_rows()
    check_bilinear(bilinear, norm, old_rows)
    check_frobenius(previous, bilinear, old_rows)
    eta, gain = arithmetic(c, previous)
    mutations = [("T", str(int(c["T"])-1), "term count"), ("k", str(int(c["k"])-1), "k"),
        ("decomposition", {**c["decomposition"], "antisymmetrization_divisor": 1}, "algebra interface"),
        ("decomposition", {**c["decomposition"], "fixed_patterns": 1}, "algebra interface"),
        ("decomposition", {**c["decomposition"], "base_characteristic_excludes": [13]}, "algebra interface"),
        ("packing", {**c["packing"], "layer_count": "2365025281"}, "packing"),
        ("packing", {**c["packing"], "radices_low_first": [38]+[35]*8}, "packing"),
        ("eta", {"numerator": "1", "denominator": str(498*int(c["k"])+6)}, "eta")]
    for field, value, reason in mutations:
        bad = deepcopy(c)
        bad[field] = value
        rejected(lambda: arithmetic(bad, previous), reason)
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
        require("'HeilbronnRankFivePacking."+name+"'" in output, "missing audit")
    for entry in re.findall(r"depends on axioms: \[([^]]*)\]", output):
        require(set(entry.split(", ")) <= {"propext", "Classical.choice", "Quot.sound"}, "unexpected axiom")
    algebra = verify_algebra()
    patch = ROOT/"patches/rank-five.patch"
    run_checked(["git", "apply", "--check", "--directory=upstream/manuscript", str(patch)])
    require(patch.read_text(encoding="utf-8").count("\n+++ b/") == 6, "patch coverage")
    evidence = list(dict.fromkeys([*[f"lean/{m}.lean" for m in PACKING_MODULES],
        "scripts/build_rankfive.py", "scripts/verify_rankfive.py", "scripts/rankfive_controls.py",
        "scripts/frobenius_controls.py", "scripts/bilinear_controls.py", "scripts/norm_controls.py",
        "scripts/verify_norm.py", "scripts/verify_bilinear.py", "scripts/verify_frobenius.py",
        "scripts/build_slab.py", "scripts/build_sphere.py", "scripts/build_tuned.py",
        "scripts/verify.py", "scripts/verify_slab.py", "scripts/verify_sphere.py",
        "certificates/rankfive.json", "certificates/frobenius.json", "patches/rank-five.patch",
        "certificates/bilinear.json", "certificates/norm.json", "certificates/central.json",
        "upstream/manifest.json", "notes/sphere-packing.tex", "README.md", "docs/review.md",
        "artifacts/sphere-latex-status.json", "artifacts/algebra-verification.json", *algebra["evidence_sha256"]]))
    with localcontext() as ctx:
        ctx.prec = 40
        report = {"status": "pass", "lean": version, "upstream_commit": PIN,
            "source_files_verified": len(manifest["files"]),
            "eta_approx": str(Decimal(eta.numerator)/Decimal(eta.denominator)),
            "gain_from_frobenius_approx": str(Decimal(gain.numerator)/Decimal(gain.denominator)),
            "arithmetic_negative_controls": len(mutations), "finite_controls": finite,
            "packing_controls": packing, "lean_axiom_audit": audit,
            "algebra_theorems_audited": algebra["audited_theorems"], "patched_sections": 6,
            "evidence_sha256": {p: sha256((ROOT/p).read_bytes()).hexdigest() for p in evidence},
            "not_established": ["full geometric Heilbronn theorem in Lean", "practical finite-n bounds",
                                "complete independent audit of upstream estimates", "novelty or optimality"]}
    (ROOT/"artifacts/rankfive-verification.json").write_text(json.dumps(report, indent=2)+"\n",
                                                          encoding="utf-8", newline="\n")
    print(json.dumps({k: report[k] for k in ("status", "eta_approx", "gain_from_frobenius_approx")}, indent=2))


if __name__ == "__main__":
    main()
