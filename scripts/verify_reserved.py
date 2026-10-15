"""Independent finite checks and Lean audit for the reserved-tag checkpoint."""
from copy import deepcopy
from decimal import Decimal, localcontext
from fractions import Fraction
from functools import cache
from hashlib import sha256
from itertools import permutations, product
from pathlib import Path
from random import Random
import json
import os
import re
import subprocess

from verify import PIN, read_fraction, require, run_checked
from verify_algebra import verify_algebra
from verify_five import arithmetic as check_five
from verify_slab import rejected
from patch_controls import check_patch_references
from five_controls import det

ROOT=Path(__file__).resolve().parents[1]
MODULES=["Sphere","Tuned","Slab","RowDigits","FiveScales","MixedSphere",
         "MixedLayerData","MixedLayerCounting","IntervalCounting",
         "ReservedLayerData","ReservedLayer","ReservedPacking"]
PROVED=["exact counts of five tags and 2916 norm words",
        "position bounds, injectivity and matching",
        "exclusion of one or two reserved tags from the target coefficient",
        "sparse tag distinction and fresh-position bounds"]


@cache
def codes(m):
    return tuple(sum(((n>>j)&1)*3**j for j in range(m)) for n in range(2**m))


def arithmetic(c,previous):
    require(c["schema"]=="heilbronn-reserved-v1" and c["upstream_commit"]==PIN,"schema and pin")
    require(c["status"]==previous["status"]=="conditional-on-upstream-estimates"
            and c["scope"]==previous["scope"],"scope")
    require(c["previous_certificate"]=="certificates/five.json" and
            c["previous_sha256"]==sha256((ROOT/"certificates/five.json").read_bytes()).hexdigest(),"previous")
    require(c["d"]==5 and c["T"]=="2916","term count")
    for key in ["decomposition","scales","row_digits","cap","prime_transfer"]:
        require(c[key]==previous[key],"inherited "+key)
    require(c["k"]=="408781","packing size")
    p=c["packing"]
    require(p["half_alphabets_low_first"]==[1]*12 and p["energy_index"]==0
            and p["squared_norm"]==12 and p["source_box_k"]==3**12,"cube")
    require(p["lower_inclusive"]==10 and p["upper_exclusive"]==204391,"cutoffs")
    require(p["count_below_lower"]==5 and p["count_below_upper"]==2921
            and p["interval_count"]==2916,"capacity")
    require(p["positions"]==["u","u","k-1-2*u"],"positions")
    states=p["count_states"]
    require(len(states)==47 and len({(s["depth"],s["bound"]) for s in states})==47,"count states")
    for i,s in enumerate(states):
        depth,bound=s["depth"],s["bound"]
        require(type(depth) is int and 0<=depth<=12 and type(bound) is int and bound>=0,"count state")
        require(s["count"]==sum(x<bound for x in codes(12-depth)),"count state")
        if depth<12:
            q,_=divmod(bound,3)
            require(0<=s["low"]<i and 0<=s["high"]<i,"state dependency")
            for key,b in [("low",q),("high",q+1)]:
                require(states[s[key]]["depth"]==depth+1 and states[s[key]]["bound"]==b,"state dependency")
    for key,bound,count in [("lower_state",10,5),("upper_state",204391,2921)]:
        require((states[p[key]]["depth"],states[p[key]]["bound"],states[p[key]]["count"])
                ==(0,bound,count),"root state")
    k=int(c["k"])
    require(k==2*p["upper_exclusive"]-1,"range")
    require(c["tags"]=={"positions":[0,1,3,4,9],"span":10,"row1":{"0":"1"},
        "row2":"five basis coordinates at the reserved positions","top_row_digit_choices":1,
        "minor_valuation_max":9,"fresh_digit_index_min":k-10,"required_k_min":20,
        "exclusion":"all five tag words and all norm words share one midpoint-free cube"},"tags")
    require(c["collision"]=={"M":"L3/r = 400*k^2*r^3","exactly_two_equal_moment":"2/M",
        "all_three_equal_moment":2,"total":"6/(M*r^d)+2/r^(2*d)","r_powers":[-8,-10],
        "minor_bound":"a < 10; field degree remains 5"},"collision")
    beta=Fraction(3*4*7*k-(k-1),2)
    rho=6*beta
    gamma=rho/(rho+1)
    alpha=rho+gamma
    eta=2*gamma/alpha
    gain=eta/read_fraction(previous["eta"])
    require(c["rho"]==str(rho.numerator) and rho.denominator==1,"rho")
    for key,value in [("beta",beta),("gamma",gamma),("alpha",alpha),("eta",eta),("gain_from_five",gain)]:
        require(read_fraction(c[key])==value,key)
    require(eta==Fraction(1,50893237) and Fraction(285,100)<gain<3,"exponent and gain")
    require(0<gamma<1 and k>=20,"feasibility")
    require(c["constraints"]["zero_case_h_powers"]==[0,-2,-6],"zero case")
    for key,v in [("two_equal_r_power",2*gamma+6-(5+3)),
                  ("three_equal_r_power",2*gamma+6-2*5),
                  ("pair_r_power",gamma-3*(k-1))]:
        require(read_fraction(c["constraints"][key])==v and v<0,"deletion")
    require(c["formal_scope"]=={"new_proved":PROVED,
        "inherited":"degree-five algebra and finite probability theorems",
        "written_not_formalized":previous["formal_scope"]["written_not_formalized"]},"formal scope")
    require(c["parameter_choice"]=="explicit feasible witness; no optimality claim","optimality scope")
    return eta,gain


def finite_controls():
    tags=[x for x in codes(12) if x<10]
    norm=[x for x in codes(12) if 10<=x<204391]
    whole=tags+norm
    require(tags==[0,1,3,4,9] and len(norm)==2916 and max(norm)==204390,"independent enumeration")
    members=set(whole)
    pair_checks=0
    for i,x in enumerate(whole):
        for y in whole[i:]:
            s=x+y
            require(s%2 or s//2 not in members or x==y,"complete midpoint check")
            pair_checks+=1
    require(2*max(norm)==408780 and min(norm)==10,"exact endpoints")
    # All actual tag/norm combinations are covered by the preceding midpoint check.
    # Inspect sparse low coefficients independently, using positive representatives.
    labels=list(product(range(2),repeat=5))
    sparse_pairs=0
    for left,right in product(labels,repeat=2):
        if left==right:
            continue
        q=[2]*10; qp=[2]*10
        for pos,x,y in zip(tags,left,right):
            q[pos]=x or 2; qp[pos]=y or 2
        a=next(i for i in range(10) if q[i]!=qp[i])
        A=[1]+[2]*9
        u=[sum(A[i]*(qp[n-i]-q[n-i]) for i in range(n+1)) for n in range(10)]
        require(all(t==0 for t in u[:a]) and u[a]!=0 and abs(u[a])<2,"sparse minor")
        require(408780-a>a and 408780-a<408781,"fresh position")
        sparse_pairs+=1
    # Complete support convolution on small instances, with an overlapping-tag control.
    rng=Random(191512)
    positions=[3,4,9]
    right=[18-2*x for x in positions]
    failures=0
    for _ in range(32):
        forms=[[[rng.randrange(7) for _ in range(3)] for _ in range(3)] for _ in positions]
        values=[[rng.randrange(7) for _ in range(2)] for _ in range(3)]
        expected=sum(det(f) for f in forms)%7
        for low in ([0,1],[3,1]):
            polys=[[{} for _ in range(3)] for _ in range(3)]
            for row,col,a in product(range(3),repeat=3):
                pos=positions[a] if row<2 else right[a]
                polys[row][col][pos]=forms[a][row][col]
            for col in range(3):
                polys[0][col][low[0]]=polys[0][col].get(low[0],0)+1
                for t,value in zip(low,values[col]):
                    polys[1][col][t]=polys[1][col].get(t,0)+value
            actual=0
            for perm in permutations(range(3)):
                sign=(-1)**sum(perm[i]>perm[j] for i in range(3) for j in range(i+1,3))
                for x,y,z in product(*(polys[row][perm[row]].items() for row in range(3))):
                    if x[0]+y[0]+z[0]==18:
                        actual+=sign*x[1]*y[1]*z[1]
            if low==[0,1]:
                require(actual%7==expected,"coefficient transfer")
            else:
                failures+=actual%7!=expected
    require(failures>0,"overlapping-tag negative control")
    return {"enumerated_cube_words":4096,"norm_words":2916,"tag_words":5,
            "complete_midpoint_pair_checks":pair_checks,"sparse_ordered_label_pairs":sparse_pairs,
            "coefficient_identities":32,"overlapping_tag_counterexamples":failures,
            "endpoints_attained":True}


def main():
    c=json.loads((ROOT/"certificates/reserved.json").read_text(encoding="utf-8"))
    previous=json.loads((ROOT/"certificates/five.json").read_text(encoding="utf-8"))
    older=json.loads((ROOT/"certificates/rowdigits.json").read_text(encoding="utf-8"))
    check_five(previous,older)
    eta,gain=arithmetic(c,previous)
    mutations=[("d",3,"term count"),("T","2915","term count"),("k","408779","packing size"),
        ("packing",{**c["packing"],"lower_inclusive":9},"cutoffs"),
        ("packing",{**c["packing"],"interval_count":2917},"capacity"),
        ("tags",{**c["tags"],"positions":[0,1,3,4,10]},"tags"),
        ("tags",{**c["tags"],"span":5},"tags"),
        ("collision",{**c["collision"],"all_three_equal_moment":0},"collision"),
        ("eta",{"numerator":"1","denominator":"50893236"},"eta"),
        ("formal_scope",{**c["formal_scope"],"written_not_formalized":[]},"formal scope")]
    damaged=deepcopy(c["packing"]); damaged["count_states"][0]["count"]+=1
    mutations.append(("packing",damaged,"count state"))
    for key,value,reason in mutations:
        bad=deepcopy(c);bad[key]=value
        rejected(lambda:arithmetic(bad,previous),reason)
    finite=finite_controls()
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
        p=subprocess.run([lean,"-j","1","-M","2048","-o",f"lean/{module}.olean",f"lean/{module}.lean"],
            cwd=ROOT,text=True,encoding="utf-8",errors="replace",capture_output=True,timeout=120,
            env={**os.environ,"LEAN_PATH":str(ROOT/"lean"),"LEAN_NUM_THREADS":"1"})
        output=p.stdout+p.stderr
        require(p.returncode==0 and "error:" not in output and "sorryAx" not in output,
                "Lean reserved checkpoint:\n"+output)
        audit.extend(output.splitlines())
    output="\n".join(audit)
    exports={"HeilbronnReservedLayer":["below_lower","below_upper","exact_interval_count"],
             "HeilbronnReservedPacking":["tag_values","tag_bounds","tag_injective","tag_energy",
                 "interval_family","zero_energy_midpoint","reserved_packing","sparse_tag_distinction",
                 "fresh_position","exact_exponent","gain_from_five"]}
    for namespace,names in exports.items():
        for name in names:
            require(output.count("'"+namespace+"."+name+"'")==1,"missing or duplicate audit")
    for entry in re.findall(r"depends on axioms: \[([^]]*)\]",output):
        require(set(entry.split(", "))<={"propext","Classical.choice","Quot.sound"},"unexpected axiom")
    algebra=verify_algebra()
    patch="patches/reserved-tags.patch"
    run_checked(["git","apply","--check","--directory=upstream/manuscript",str(ROOT/patch)])
    require((ROOT/patch).read_text(encoding="utf-8").count("\n+++ b/")==6,"patch coverage")
    references=check_patch_references(patch)
    evidence=list(dict.fromkeys([*[f"lean/{m}.lean" for m in MODULES],
        "scripts/build_reserved.py","scripts/verify_reserved.py","scripts/build_five.py",
        "scripts/verify_five.py","scripts/five_controls.py","scripts/build_rowdigits.py",
        "scripts/build_eighteen.py","scripts/build_slab.py","scripts/build_sphere.py",
        "scripts/build_tuned.py","scripts/verify.py","scripts/verify_slab.py","scripts/patch_controls.py",
        "certificates/reserved.json","certificates/five.json","certificates/rowdigits.json",
        patch,"upstream/manifest.json","notes/sphere-packing.tex","artifacts/sphere-latex-status.json",
        "README.md","docs/review.md","artifacts/algebra-verification.json",*algebra["evidence_sha256"]]))
    with localcontext() as ctx:
        ctx.prec=40
        report={"status":"pass","lean":version,"upstream_commit":PIN,
            "source_files_verified":len(manifest["files"]),
            "eta_approx":str(Decimal(eta.numerator)/Decimal(eta.denominator)),
            "gain_from_five_approx":str(Decimal(gain.numerator)/Decimal(gain.denominator)),
            "corrupted_certificates_rejected":len(mutations),"finite_controls":finite,
            "lean_axiom_audit":audit,"new_exports_audited":sum(map(len,exports.values())),
            "algebra_theorems_audited":algebra["audited_theorems"],
            "patched_sections":6,"patched_manuscript_reference_check":references,
            "evidence_sha256":{p:sha256((ROOT/p).read_bytes()).hexdigest() for p in evidence},
            "not_established":previous["formal_scope"]["written_not_formalized"]+
                ["practical finite-n bounds","novelty or global optimality"]}
    (ROOT/"artifacts/reserved-verification.json").write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8",newline="\n")
    print(json.dumps({k:report[k] for k in ("status","eta_approx","gain_from_five_approx")},indent=2))


if __name__=="__main__":
    main()
