"""Verify the supplied degree-seven certificate, controls, proofs and patch."""
from copy import deepcopy
from decimal import Decimal, localcontext
from fractions import Fraction
from hashlib import sha256
from math import prod
from pathlib import Path
import json
import os
import re
import subprocess

from patch_controls import check_patch_references
from rowdigits_controls import packing_rows, packing_controls, digit_controls, field_controls
from verify import PIN, read_fraction, require, run_checked
from verify_algebra import verify_algebra
from verify_slab import rejected
from verify_trimmed import arithmetic as check_trimmed

ROOT = Path(__file__).resolve().parents[1]
MODULES = ["Sphere", "Tuned", "Slab", "RowDigits", "MixedSphere", "MixedLayerData",
           "MixedLayerCounting", "SevenLayerData", "SevenLayer", "SevenPacking"]
PROVED = ["degree-7 norm decomposition into 13*18^3 determinants",
          "homogeneous coordinates and distinct-label criterion over split primes",
          "exact energy-5 layer and complete mixed-radix packing",
          "row-digit divisibility, moment-bound arithmetic and base scale identity",
          "cleared-denominator alteration inequalities and exponent identity",
          "gain from trimmed checkpoint greater than 680000"]
WRITTEN = ["conditional divisor tail and expectation with row-dependent digit ranges",
           "upstream lattice, orbit, slab geometry and weighted counting arguments",
           "probability, asymptotic deletion and interpolation",
           "prime number theorem in the progression 1 mod 3"]


def arithmetic(c, previous):
    require(c["schema"] == "heilbronn-rowdigits-v1" and c["upstream_commit"] == PIN, "schema and pin")
    require(c["status"] == "conditional-on-upstream-estimates" and c["scope"] == previous["scope"], "scope")
    require(c["previous_certificate"] == "certificates/trimmed.json" and
            c["previous_sha256"] == sha256((ROOT/"certificates/trimmed.json").read_bytes()).hexdigest(), "previous")
    require(c["d"] == 7 and c["T"] == str(13*18**3), "term count")
    dec = dict(previous["decomposition"])
    dec.update(pairs=3, extension_determinants=str(18**3), nodes_per_term=13,
               normalization_denominator=27, formal_base_field_minimum=13,
               row_maps=["3^(-3) * eval_t", "eval_t", "constantCoord(c_t * input)"])
    require(c["decomposition"] == dec, "algebra interface")
    alphabets = [3]+[2]*8
    radices = [4*a-1 for a in alphabets]
    k = prod(radices)
    require(c["k"] == str(k), "packing size")
    require(c["packing"] == {"half_alphabets_low_first": alphabets, "radices_low_first": radices,
            "energy_index": 5, "squared_norm": 9+8*5, "layer_count": "78848", "count_table": packing_rows()}, "packing")
    require(78848 >= int(c["T"]), "capacity")
    scales = {key: value for key, value in previous["scales"].items() if key not in ("L", "B")}
    scales.update(L1="r", L2="r", L3="400*k^2*r^4", P="L1*L2*L3",
                  B="100*k^2*P < B <= 200*k^2*P; B prime")
    require(c["scales"] == scales, "scales")
    require(c["row_digits"] == {"coefficient_bound": "6*k^2*L1*L2*L3",
        "general_tail": "((r/L2)^2*(r/L3)^2)^j", "chosen_tail": "(r/L3)^(2*j)",
        "theta": "B*(r/L3)^2", "theta_upper": {"numerator": "1", "denominator": "2"},
        "conditional_moment_upper": 2, "base_r_power": 6,
        "conditional_probability_proof": "written; not formalized in Lean"}, "row digits")
    # Independent scale calculation: digit product exponent 1+1+4,
    # conditional-tail exponent 2*(1-1)+2*(1-4), hence zero moment growth.
    base_power = 1+1+4
    require(base_power+2*(1-1)+2*(1-4) == 0 and Fraction(200,400) == Fraction(1,2), "moment exponents")
    beta = Fraction(3*4*(1+6)*k-(k-1), 2)
    rho = base_power*beta
    gamma = rho/(2*rho+1)
    alpha = rho+gamma
    eta = 2*gamma/alpha
    gain = eta/read_fraction(previous["eta"])
    gain_main = eta*Fraction(498*15**7*19**4+7)
    require(c["rho"] == str(rho.numerator) and rho.denominator == 1, "rho")
    for key, v in [("beta",beta),("gamma",gamma),("alpha",alpha),("eta",eta),
                   ("gain_from_trimmed",gain),("gain_from_eighteen",gain_main)]:
        require(read_fraction(c[key]) == v, key)
    require(eta == Fraction(1,249*k+4) and 680000 < gain < 690000, "exponent and gain")
    require(0 < gamma < Fraction(1,2), "sample growth")
    collision, pair = 2*gamma+base_power-c["d"], gamma-Fraction(base_power,2)*(k-1)
    losses = [2+2*2-6, 2+2-6, 2+2*2-2*6]
    require(collision < 0 and pair < 0 and max(losses) <= 0, "deletion inequalities")
    constraints = c["constraints"]
    require(constraints["zero_case_h_powers"] == losses and
            read_fraction(constraints["collision_r_power"]) == collision and
            read_fraction(constraints["pair_r_power"]) == pair, "constraints")
    require(c["prime_transfer"] == previous["prime_transfer"] and c["cap"] == previous["cap"], "retained interfaces")
    require(c["formal_scope"] == {"proved":PROVED,"written_not_formalized":WRITTEN}, "formal scope")
    require(c["parameter_choice"] == "explicit feasible witness; no optimality claim", "optimality scope")
    return eta, gain, gain_main


def main():
    c=json.loads((ROOT/"certificates/rowdigits.json").read_text(encoding="utf-8"))
    previous=json.loads((ROOT/"certificates/trimmed.json").read_text(encoding="utf-8"))
    eighteen=json.loads((ROOT/"certificates/eighteen.json").read_text(encoding="utf-8"))
    check_trimmed(previous,eighteen)
    eta,gain,gain_main=arithmetic(c,previous)
    mutations=[("d",6,"term count"),("T","75815","term count"),("k",str(int(c["k"])-1),"packing size"),
        ("packing",{**c["packing"],"layer_count":"78849"},"packing"),
        ("row_digits",{**c["row_digits"],"base_r_power":12},"row digits"),
        ("row_digits",{**c["row_digits"],"chosen_tail":"(r/L3)^(4*j)"},"row digits"),
        ("scales",{**c["scales"],"L2":"400*k^2*r^4"},"scales"),
        ("decomposition",{**c["decomposition"],"normalization_denominator":1},"algebra interface"),
        ("eta",{"numerator":"1","denominator":str(249*int(c["k"])+3)},"eta"),
        ("formal_scope",{"proved":PROVED+WRITTEN,"written_not_formalized":[]},"formal scope")]
    for field,value,reason in mutations:
        bad=deepcopy(c); bad[field]=value
        rejected(lambda: arithmetic(bad,previous),reason)
    controls={"packing":packing_controls(),"digits":digit_controls(),"field":field_controls()}
    manifest=json.loads((ROOT/"upstream/manifest.json").read_text(encoding="utf-8-sig"))
    require(manifest["commit"] == PIN,"upstream pin")
    for item in manifest["files"]:
        data=(ROOT/item["path"]).read_bytes()
        require(sha256(data).hexdigest() == item["sha256"] and len(data) == item["bytes"],"upstream file")
    lean=run_checked(["elan","which","lean"]).strip()
    version=run_checked([lean,"--version"]).strip()
    require("version 4.11.0," in version,"Lean version")
    audit=[]
    for module in MODULES:
        source=(ROOT/f"lean/{module}.lean").read_text(encoding="utf-8")
        require(not re.search(r"\b(sorry|admit|axiom|unsafe|native_decide)\b",source),"proof escape")
        r=subprocess.run([lean,"-j","1","-M","2048","-o",f"lean/{module}.olean",f"lean/{module}.lean"],
            cwd=ROOT,text=True,encoding="utf-8",errors="replace",capture_output=True,timeout=120,
            env={**os.environ,"LEAN_PATH":str(ROOT/"lean"),"LEAN_NUM_THREADS":"1"})
        require(r.returncode == 0 and "error:" not in r.stdout+r.stderr,"Lean row-digit checkpoint:\n"+r.stdout+r.stderr)
        audit.extend((r.stdout+r.stderr).splitlines())
    output="\n".join(audit)
    require("sorryAx" not in output,"incomplete proof")
    for namespace,names in {"HeilbronnRowDigits":["long_digits_divisible","digit_moment_bound","base_scale",
        "alteration_constraints","exponent_identity"],"HeilbronnSevenPacking":["exact_layer_count",
        "layer_capacity","exact_layer_family","trace_packing","trace_gain"]}.items():
        for name in names:
            require("'"+namespace+"."+name+"'" in output,"missing audit")
    for entry in re.findall(r"depends on axioms: \[([^]]*)\]",output):
        require(set(entry.split(", ")) <= {"propext","Classical.choice","Quot.sound"},"unexpected axiom")
    algebra=verify_algebra()
    patch="patches/row-digits.patch"
    run_checked(["git","apply","--check","--directory=upstream/manuscript",str(ROOT/patch)])
    require((ROOT/patch).read_text(encoding="utf-8").count("\n+++ b/") == 6,"patch coverage")
    references=check_patch_references(patch)
    evidence=list(dict.fromkeys([*[f"lean/{m}.lean" for m in MODULES],
        "scripts/build_rowdigits.py","scripts/verify_rowdigits.py","scripts/rowdigits_controls.py",
        "scripts/build_eighteen.py","scripts/verify_trimmed.py","scripts/trimmed_controls.py",
        "scripts/patch_controls.py","scripts/verify.py","scripts/verify_slab.py","scripts/search_packing.py",
        "scripts/build_slab.py","scripts/build_sphere.py","scripts/build_tuned.py",
        "scripts/norm_controls.py","scripts/bilinear_controls.py","scripts/frobenius_controls.py",
        "scripts/paired_controls.py","scripts/eighteen_controls.py",
        "certificates/rowdigits.json","certificates/trimmed.json","certificates/eighteen.json",patch,
        "upstream/manifest.json","artifacts/sphere-latex-status.json","notes/sphere-packing.tex",
        "README.md","docs/review.md","artifacts/algebra-verification.json",*algebra["evidence_sha256"]]))
    with localcontext() as ctx:
        ctx.prec=40
        report={"status":"pass","lean":version,"upstream_commit":PIN,"source_files_verified":len(manifest["files"]),
            "eta_approx":str(Decimal(eta.numerator)/Decimal(eta.denominator)),
            "gain_from_trimmed_approx":str(Decimal(gain.numerator)/Decimal(gain.denominator)),
            "gain_from_eighteen_approx":str(Decimal(gain_main.numerator)/Decimal(gain_main.denominator)),
            "corrupted_certificates_rejected":len(mutations),"finite_controls":controls,"lean_axiom_audit":audit,
            "algebra_theorems_audited":algebra["audited_theorems"],"patched_sections":6,
            "patched_manuscript_reference_check":references,
            "evidence_sha256":{p:sha256((ROOT/p).read_bytes()).hexdigest() for p in evidence},
            "not_established":["full geometric Heilbronn theorem in Lean","conditional probability lemma in Lean",
                "prime number theorem in Lean","practical finite-n bounds",
                "complete independent audit of upstream estimates","novelty or optimality"]}
    (ROOT/"artifacts/rowdigits-verification.json").write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8",newline="\n")
    print(json.dumps({k:report[k] for k in ["status","eta_approx","gain_from_trimmed_approx","gain_from_eighteen_approx"]},indent=2))


if __name__ == "__main__":
    main()
