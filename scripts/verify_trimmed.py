"""Verify the supplied interval certificate, independent counts and Lean proofs."""
from copy import deepcopy
from decimal import Decimal, localcontext
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import json
import os
import re
import subprocess

from patch_controls import check_patch_references
from trimmed_controls import count_below, histograms, finite_controls
from verify import PIN, read_fraction, require, run_checked
from verify_algebra import verify_algebra
from verify_eighteen import arithmetic as check_eighteen
from verify_slab import rejected, scale_constraints

ROOT = Path(__file__).resolve().parents[1]
MODULES = ["Sphere", "MixedSphere", "MixedLayerData", "MixedLayerCounting",
           "IntervalCounting", "TrimmedLayerData", "TrimmedLayerRows0", "TrimmedLayerRows1",
           "TrimmedLayerRows2", "TrimmedLayerRows3", "TrimmedLayer", "TrimmedPacking"]


def arithmetic(c, previous):
    require(c["schema"] == "heilbronn-trimmed-v1" and c["upstream_commit"] == PIN, "schema and pin")
    require(c["status"] == previous["status"] and c["scope"] == previous["scope"], "conditional scope")
    require(c["previous_certificate"] == "certificates/eighteen.json" and
            c["previous_sha256"] == sha256((ROOT/"certificates/eighteen.json").read_bytes()).hexdigest(), "previous")
    require(c["d"] == 13 and c["T"] == str(25*18**6), "term count")
    require(c["decomposition"] == previous["decomposition"] and c["prime_transfer"] == previous["prime_transfer"], "algebra and primes")
    p = c["packing"]
    alphabets = [4,4,4,4,4,4,5,4,5,5,5]
    require(p["half_alphabets_low_first"] == alphabets and
            p["radices_low_first"] == [4*a-1 for a in alphabets], "alphabets")
    require(p["energy_index"] == 32 and p["squared_norm"] == 11+8*32, "energy")
    require(p["source_box_k"] == str(15**7*19**4), "source box")
    require(p["full_layer_count"] == str(histograms(tuple(alphabets))[-1][32]) == "872130560", "full layer")
    lower, upper = int(p["lower_inclusive"]), int(p["upper_exclusive"])
    require(0 <= lower < upper, "cutoff order")
    low, high = count_below(alphabets,32,lower), count_below(alphabets,32,upper)
    require((p["count_below_lower"],p["count_below_upper"]) == (str(low),str(high)), "cutoff counts")
    require(high-low == int(p["interval_count"]) == int(c["T"]), "interval capacity")
    require((lower,upper) == (133535493048,10996285570280), "witness cutoffs")
    states = p["count_states"]
    require(len(states) == 44 and (p["lower_state"],p["upper_state"]) == (22,43), "state roots")
    keys = set()
    for i, state in enumerate(states):
        depth, bound = state["depth"], int(state["bound"])
        require(0 <= depth <= len(alphabets) and bound >= 0, "state range")
        require((depth,bound) not in keys, "duplicate state")
        keys.add((depth,bound))
        require(state["counts"] == [count_below(alphabets[depth:],e,bound) for e in range(33)], "count state")
        if depth < len(alphabets):
            q = bound//(4*alphabets[depth]-1)
            for name, target in [("low",q),("high",q+1)]:
                child = state[name]
                require(0 <= child < i, "state order")
                require((states[child]["depth"],int(states[child]["bound"])) == (depth+1,target), "state edge")
        else:
            require(set(state) == {"depth","bound","counts"}, "leaf state")
    for key,bound in [("lower_state",lower),("upper_state",upper)]:
        root=states[p[key]]
        require(root["depth"] == 0 and int(root["bound"]) == bound, "root cutoff")
    k = 2*(upper-lower)-1
    require(c["k"] == str(k) == "21725500154463", "translated size")
    require(c["cap"] == previous["cap"] and c["scales"] == previous["scales"], "scales")
    beta = Fraction(83*k+1,2)
    rho = 12*beta
    gamma = rho/(2*rho+1)
    alpha = rho+gamma
    eta = 2*gamma/alpha
    gain = eta/read_fraction(previous["eta"])
    require(c["rho"] == str(rho.numerator) and rho.denominator == 1, "rho")
    for key, value in [("beta",beta),("gamma",gamma),("alpha",alpha),("eta",eta),("gain_from_eighteen",gain)]:
        require(read_fraction(c[key]) == value, key)
    require(eta == Fraction(1,498*k+7), "closed exponent")
    require(Fraction(10249,10000) < gain < Fraction(10250,10000), "gain enclosure")
    losses, collision, pair = scale_constraints(13,k,2,6,4,gamma)
    require(c["constraints"]["zero_case_h_powers"] == losses and
            read_fraction(c["constraints"]["collision_r_power"]) == collision and
            read_fraction(c["constraints"]["pair_r_power"]) == pair, "constraints")
    require(c["formal_scope"] == {"inherited": "18-form norm decomposition and split-prime specialization",
        "new_proved": ["exact counts below both encoded cutoffs", "exact interval count",
            "complete translated packing", "gain from the eighteen-form checkpoint greater than 1.0249"],
        "written_not_formalized": previous["formal_scope"]["written_not_formalized"]}, "formal scope")
    require(c["parameter_choice"] == "explicit feasible witness; no optimality claim", "optimality scope")
    return eta, gain


def negative_controls(c, previous):
    mutations = [("T",str(int(c["T"])-1),"term count"), ("k",str(int(c["k"])-1),"translated size"),
        ("packing",{**c["packing"],"count_below_lower":"10308153"},"cutoff counts"),
        ("packing",{**c["packing"],"energy_index":33},"energy"),
        ("prime_transfer",{**c["prime_transfer"],"lean_formalized":True},"algebra and primes"),
        ("decomposition",{**c["decomposition"],"manuscript_prime_residue":2},"algebra and primes"),
        ("eta",{"numerator":"1","denominator":"10819299076922580"},"eta")]
    damaged = deepcopy(c["packing"])
    damaged["count_states"][3]["counts"][0] += 1
    mutations.append(("packing",damaged,"count state"))
    for field, value, reason in mutations:
        bad=deepcopy(c)
        bad[field]=value
        rejected(lambda: arithmetic(bad,previous),reason)
    p=c["packing"]; a=p["half_alphabets_low_first"]
    low,high=int(p["lower_inclusive"]),int(p["upper_exclusive"])
    require(count_below(a,32,high)-count_below(a,32,low+1) == int(c["T"])-1, "lower off-by-one control")
    require(count_below(a,32,high-1)-count_below(a,32,low) == int(c["T"])-1, "upper off-by-one control")
    require(2*(high-1) > int(c["k"])-1, "omitted translation violates right-position bound")
    wrong_right = max(0,int(c["k"])-1-2*(high-1))
    require(2*(high-1)+wrong_right != int(c["k"])-1, "omitted translation breaks diagonal matching")
    return {"corrupted_certificates_rejected": len(mutations), "lower_endpoint_omission_loses_one_word": True,
            "upper_endpoint_omission_loses_one_word": True, "omitted_translation_rejected": True,
            "omitted_translation_breaks_diagonal_matching": True}


def main():
    c=json.loads((ROOT/"certificates/trimmed.json").read_text(encoding="utf-8"))
    previous=json.loads((ROOT/"certificates/eighteen.json").read_text(encoding="utf-8"))
    paired=json.loads((ROOT/"certificates/paired.json").read_text(encoding="utf-8"))
    check_eighteen(previous,paired)
    eta,gain=arithmetic(c,previous)
    controls=negative_controls(c,previous)
    finite=finite_controls()
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
        require(r.returncode == 0 and "error:" not in r.stdout+r.stderr,"Lean interval packing:\n"+r.stdout+r.stderr)
        audit.extend((r.stdout+r.stderr).splitlines())
    output="\n".join(audit)
    require("sorryAx" not in output,"incomplete proof")
    for namespace,names in {"HeilbronnInterval":["digit_bound","below_cons","interval_partition"],
        "HeilbronnTrimmedLayer":["below_lower","below_upper","exact_interval_count"],
        "HeilbronnTrimmedPacking":["interval_family","translated_packing","trimmed_gain"]}.items():
        for name in names:
            require("'"+namespace+"."+name+"'" in output,"missing audit")
    for entry in re.findall(r"depends on axioms: \[([^]]*)\]",output):
        require(set(entry.split(", ")) <= {"propext","Classical.choice","Quot.sound"},"unexpected axiom")
    algebra=verify_algebra()
    patch="patches/trimmed-sphere.patch"
    run_checked(["git","apply","--check","--directory=upstream/manuscript",str(ROOT/patch)])
    require((ROOT/patch).read_text(encoding="utf-8").count("\n+++ b/") == 6,"patch coverage")
    references=check_patch_references(patch)
    search=json.loads((ROOT/"artifacts/trimmed-search.json").read_text(encoding="utf-8"))
    best=search["best"]; p=c["packing"]
    require(best["half_alphabets_low_first"] == p["half_alphabets_low_first"] and
            best["energy"] == p["energy_index"] and best["k"] == int(c["k"]) and
            best["lower_inclusive"] == int(p["lower_inclusive"]) and
            best["upper_exclusive"] == int(p["upper_exclusive"]),"search witness")
    evidence=list(dict.fromkeys([*[f"lean/{m}.lean" for m in MODULES],
        "scripts/build_trimmed.py","scripts/verify_trimmed.py","scripts/trimmed_controls.py",
        "scripts/search_trimmed.py","scripts/build_eighteen.py","scripts/verify_eighteen.py",
        "scripts/eighteen_controls.py","scripts/patch_controls.py","scripts/verify.py","scripts/verify_slab.py",
        "scripts/build_slab.py","scripts/build_sphere.py","scripts/build_tuned.py",
        "certificates/trimmed.json","certificates/eighteen.json",patch,"upstream/manifest.json",
        "artifacts/trimmed-search.json","artifacts/sphere-latex-status.json","notes/sphere-packing.tex",
        "README.md","docs/review.md","artifacts/algebra-verification.json",*algebra["evidence_sha256"]]))
    with localcontext() as ctx:
        ctx.prec=40
        report={"status":"pass","lean":version,"upstream_commit":PIN,
            "source_files_verified":len(manifest["files"]),
            "eta_approx":str(Decimal(eta.numerator)/Decimal(eta.denominator)),
            "gain_from_eighteen_approx":str(Decimal(gain.numerator)/Decimal(gain.denominator)),
            "independent_count_entries":len(p["count_states"])*33,"negative_controls":controls,
            "finite_controls":finite,"lean_axiom_audit":audit,
            "algebra_theorems_audited":algebra["audited_theorems"],
            "patched_sections":6,"patched_manuscript_reference_check":references,
            "evidence_sha256":{path:sha256((ROOT/path).read_bytes()).hexdigest() for path in evidence},
            "not_established":["full geometric Heilbronn theorem in Lean","prime number theorem in Lean",
                               "practical finite-n bounds","complete independent audit of upstream estimates","novelty or optimality"]}
    (ROOT/"artifacts/trimmed-verification.json").write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8",newline="\n")
    print(json.dumps({k:report[k] for k in ["status","eta_approx","gain_from_eighteen_approx"]},indent=2))


if __name__ == "__main__":
    main()
