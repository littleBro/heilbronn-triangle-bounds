"""Verify the supplied degree-five checkpoint and retained proof boundary."""
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

from five_controls import packing_rows, packing_controls, collision_controls, field_controls
from patch_controls import check_patch_references
from verify import PIN, read_fraction, require, run_checked
from verify_algebra import verify_algebra
from verify_rowdigits import arithmetic as check_rowdigits
from verify_slab import rejected

ROOT = Path(__file__).resolve().parents[1]
MODULES = ["Sphere","Tuned","Slab","RowDigits","FiveScales","MixedSphere",
           "MixedLayerData","MixedLayerCounting","FiveLayerData","FiveLayer","FivePacking"]
PROVED = [
    "degree-5 norm decomposition into 9*18^2 determinants",
    "homogeneous norm coordinates and distinct-label criterion over split primes",
    "exact 3072-word layer, shifted packing and separation from label tags",
    "determinant factorization for two repeated top columns",
    "tag-minor valuation, exact joint digit tails and uniform minor-divisor moment",
    "balanced determinant coefficients and the tagged small-residue pair moment",
    "column-reindexing invariance and the finite label-mixture bound",
    "fresh-position and cleared-denominator alteration inequalities",
    "exponent identity and gain greater than 108 over degree seven",
]
WRITTEN = [
    "instantiation of norm packing and tags in the finite digit theorem, including distinct-label exclusion",
    "identification of the minor exponent with the upstream Smith divisor",
    "upstream lattice, orbit, slab geometry and weighted counting arguments",
    "asymptotic deletion and prime progression interpolation",
]


def arithmetic(c, previous):
    require(c["schema"]=="heilbronn-five-v1" and c["upstream_commit"]==PIN,"schema and pin")
    require(c["status"]=="conditional-on-upstream-estimates" and c["scope"]==previous["scope"],"scope")
    require(c["previous_certificate"]=="certificates/rowdigits.json" and
        c["previous_sha256"]==sha256((ROOT/"certificates/rowdigits.json").read_bytes()).hexdigest(),"previous")
    require(c["d"]==5 and c["T"]==str(9*18**2),"term count")
    dec=dict(previous["decomposition"])
    dec.update(pairs=2,extension_determinants="324",nodes_per_term=9,normalization_denominator=9,
               formal_base_field_minimum=9,row_maps=["3^(-2) * eval_t","eval_t","constantCoord(c_t * input)"])
    require(c["decomposition"]==dec,"algebra interface")
    alphabets=[2]*4+[1]*5
    radices=[4*a-1 for a in alphabets]
    K0=prod(radices); S=(K0-1)//2+5; k=K0+2*S
    require(c["k"]==str(k)=="1166895","packing size")
    require(c["packing"]=={"half_alphabets_low_first":alphabets,"radices_low_first":radices,
        "unshifted_base":str(K0),"shift":str(S),"energy_index":2,"squared_norm":25,
        "layer_count":"3072","count_table":packing_rows(),"positions":["S+u","S+u","K0-1-2*u"]},"packing")
    require(3072>=int(c["T"]),"capacity")
    require(c["tags"]=={"row1":{"0":"1"},"row2":"basis coordinates of the label at positions 0..d-1",
        "top_row_digit_choices":1,"minor_valuation_max":4,"fresh_digit_index_min":k-5,
        "required_k_min":10,"largest_tagged_position_sum":k-2},"tags")
    # Independent support inequalities and prefix disjointness.
    require(5<=S and 4+S+(K0-1)//2+K0-1<k-1 and k>=10,"tag separation")
    for a in range(5):
        require(k-1-a>a and k-1-a<k,"fresh position")
    require(c["scales"]==previous["scales"] and c["row_digits"]==previous["row_digits"],"scales")
    require(c["collision"]=={"M":"L3/r = 400*k^2*r^3","exactly_two_equal_moment":"2/M",
        "joint_tail":"Pr(b>=j and J | labels) <= M^(-2*j-1), 1<=j<=a<d",
        "all_three_equal_moment":2,"total":"6/(M*r^d)+2/r^(2*d)","r_powers":[-8,-10],
        "proof_status":"Lean; explicit tag and distinct-label interfaces",
        "pair_theorem":"HeilbronnFive.DigitModel.tagged_small_residue_moment",
        "total_theorem":"HeilbronnFive.total_small_residue_moment"},"collision interface")
    base_power=1+1+4
    require(base_power-2*(4-1)==0 and Fraction(200,400)==Fraction(1,2),"moment scale")
    beta=Fraction(3*4*(1+6)*k-(k-1),2)
    rho=base_power*beta; gamma=rho/(rho+1); alpha=rho+gamma; eta=2*gamma/alpha
    gain=eta/read_fraction(previous["eta"])
    require(rho.denominator==1 and c["rho"]==str(rho.numerator),"rho")
    for key,value in [("beta",beta),("gamma",gamma),("alpha",alpha),("eta",eta),("gain_from_rowdigits",gain)]:
        require(read_fraction(c[key])==value,key)
    require(eta==Fraction(1,145278430) and 108<gain<109,"exponent and gain")
    two=2*gamma+base_power-(c["d"]+3)
    three=2*gamma+base_power-2*c["d"]
    pair=gamma-Fraction(base_power,2)*(k-1)
    require(0<gamma<1 and max(two,three,pair)<0,"deletion inequalities")
    constraints=c["constraints"]
    require(constraints["zero_case_h_powers"]==[0,-2,-6] and
        read_fraction(constraints["two_equal_r_power"])==two and
        read_fraction(constraints["three_equal_r_power"])==three and
        read_fraction(constraints["pair_r_power"])==pair,"constraints")
    require(c["prime_transfer"]==previous["prime_transfer"] and c["cap"]==previous["cap"],"retained interfaces")
    require(c["formal_scope"]=={"proved":PROVED,"written_not_formalized":WRITTEN},"formal scope")
    require(c["parameter_choice"]=="explicit feasible witness; no optimality claim","optimality scope")
    return eta,gain


def main():
    c=json.loads((ROOT/"certificates/five.json").read_text(encoding="utf-8"))
    previous=json.loads((ROOT/"certificates/rowdigits.json").read_text(encoding="utf-8"))
    trimmed=json.loads((ROOT/"certificates/trimmed.json").read_text(encoding="utf-8"))
    check_rowdigits(previous,trimmed)
    eta,gain=arithmetic(c,previous)
    mutations=[("d",3,"term count"),("T","2915","term count"),
        ("k",str(int(c["k"])-1),"packing size"),
        ("packing",{**c["packing"],"layer_count":"3073"},"packing"),
        ("packing",{**c["packing"],"shift":"0"},"packing"),
        ("tags",{**c["tags"],"row1":{}},"tags"),
        ("tags",{**c["tags"],"fresh_digit_index_min":0},"tags"),
        ("collision",{**c["collision"],"all_three_equal_moment":0},"collision interface"),
        ("collision",{**c["collision"],"r_powers":[-10,-10]},"collision interface"),
        ("scales",{**c["scales"],"L2":"400*k^2*r^4"},"scales"),
        ("decomposition",{**c["decomposition"],"normalization_denominator":1},"algebra interface"),
        ("eta",{"numerator":"1","denominator":"145278429"},"eta"),
        ("formal_scope",{"proved":PROVED+WRITTEN,"written_not_formalized":[]},"formal scope")]
    for field,value,reason in mutations:
        bad=deepcopy(c);bad[field]=value
        rejected(lambda:arithmetic(bad,previous),reason)
    controls={"packing":packing_controls(),"collisions":collision_controls(),"field":field_controls()}
    manifest=json.loads((ROOT/"upstream/manifest.json").read_text(encoding="utf-8-sig"))
    require(manifest["commit"]==PIN,"upstream pin")
    for item in manifest["files"]:
        data=(ROOT/item["path"]).read_bytes()
        require(sha256(data).hexdigest()==item["sha256"] and len(data)==item["bytes"],"upstream file")
    lean=run_checked(["elan","which","lean"]).strip()
    version=run_checked([lean,"--version"]).strip()
    require("version 4.11.0," in version,"Lean version")
    audit=[]
    for module in MODULES:
        source=(ROOT/f"lean/{module}.lean").read_text(encoding="utf-8")
        require(not re.search(r"\b(sorry|admit|axiom|unsafe|native_decide)\b",source),"proof escape")
        result=subprocess.run([lean,"-j","1","-M","2048","-o",f"lean/{module}.olean",f"lean/{module}.lean"],
            cwd=ROOT,text=True,encoding="utf-8",errors="replace",capture_output=True,timeout=120,
            env={**os.environ,"LEAN_PATH":str(ROOT/"lean"),"LEAN_NUM_THREADS":"1"})
        require(result.returncode==0 and "error:" not in result.stdout+result.stderr,"Lean degree-five checkpoint:\n"+result.stdout+result.stderr)
        audit.extend((result.stdout+result.stderr).splitlines())
    output="\n".join(audit)
    require("sorryAx" not in output,"incomplete proof")
    for namespace,names in {"HeilbronnFiveScales":["fresh_position","alteration_constraints","exponent_identity","exact_exponent"],
        "HeilbronnFivePacking":["exact_layer_count","layer_capacity","exact_layer_family","trace_packing",
                                "tagged_packing","tag_separation","trace_gain"]}.items():
        for name in names:
            require("'"+namespace+"."+name+"'" in output,"missing audit")
    for entry in re.findall(r"depends on axioms: \[([^]]*)\]",output):
        require(set(entry.split(", "))<={"propext","Classical.choice","Quot.sound"},"unexpected axiom")
    algebra=verify_algebra()
    patch="patches/degree-five.patch"
    run_checked(["git","apply","--check","--directory=upstream/manuscript",str(ROOT/patch)])
    require((ROOT/patch).read_text(encoding="utf-8").count("\n+++ b/")==6,"patch coverage")
    references=check_patch_references(patch)
    evidence=list(dict.fromkeys([*[f"lean/{m}.lean" for m in MODULES],
        "scripts/build_five.py","scripts/verify_five.py","scripts/five_controls.py",
        "scripts/build_rowdigits.py","scripts/build_eighteen.py","scripts/verify_rowdigits.py",
        "scripts/rowdigits_controls.py","scripts/patch_controls.py","scripts/verify.py","scripts/verify_slab.py",
        "scripts/search_packing.py","scripts/build_slab.py","scripts/build_sphere.py","scripts/build_tuned.py",
        "scripts/norm_controls.py","scripts/bilinear_controls.py","scripts/frobenius_controls.py",
        "scripts/paired_controls.py","scripts/eighteen_controls.py","certificates/five.json",
        "certificates/rowdigits.json","certificates/trimmed.json",patch,"upstream/manifest.json",
        "artifacts/sphere-latex-status.json","notes/sphere-packing.tex","README.md","docs/review.md",
        "artifacts/algebra-verification.json",*algebra["evidence_sha256"]]))
    with localcontext() as ctx:
        ctx.prec=40
        report={"status":"pass","lean":version,"upstream_commit":PIN,"source_files_verified":len(manifest["files"]),
            "eta_approx":str(Decimal(eta.numerator)/Decimal(eta.denominator)),
            "gain_from_rowdigits_approx":str(Decimal(gain.numerator)/Decimal(gain.denominator)),
            "corrupted_certificates_rejected":len(mutations),"finite_controls":controls,"lean_axiom_audit":audit,
            "algebra_theorems_audited":algebra["audited_theorems"],"patched_sections":6,
            "patched_manuscript_reference_check":references,
            "evidence_sha256":{p:sha256((ROOT/p).read_bytes()).hexdigest() for p in evidence},
            "not_established":["full geometric Heilbronn theorem in Lean","end-to-end norm-packing instantiation of the finite probability theorem",
                "Smith normal form and identification of the minor exponent",
                "prime number theorem in Lean","practical finite-n bounds",
                "complete independent audit of upstream estimates","novelty or optimality"]}
    (ROOT/"artifacts/five-verification.json").write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8",newline="\n")
    print(json.dumps({k:report[k] for k in ["status","eta_approx","gain_from_rowdigits_approx"]},indent=2))


if __name__ == "__main__":
    main()
