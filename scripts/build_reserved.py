"""Reserve five words of a ternary binary cube for the label coordinates."""
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import difflib
import json

from build_sphere import PIN, rational
from build_tuned import replace_once
from build_five import five_sections, POSITIONS as FIVE_POSITIONS

ROOT = Path(__file__).resolve().parents[1]
ALPHABETS = [1]*12
LOWER, UPPER = 10, 204391
TAGS = [0, 1, 3, 4, 9]
K, TARGET = 2*UPPER-1, 2916

POSITIONS = r"""Use twelve binary coordinates $x_j\in\{0,1\}$, encoded by
$c(x)=\sum_{j=0}^{11}x_j3^j$. All words have centered squared norm $12$.
An exact cutoff recurrence gives
\[
 \#\{c(x)<10\}=5,\qquad
 \#\{c(x)<204\,391\}=2\,921.
\]
Reserve the five encodings
\[
 (t_0,t_1,t_2,t_3,t_4)=(0,1,3,4,9)
\]
for tags, and use the $T=2\,916$ words with $10\le c(x)<204\,391$
for norm positions. The original encoding radix product is $3^{12}$;
the position range, after restriction, is
\[
 k=2(204\,391)-1=408\,781.
\]
For each retained norm word set
\begin{equation}\label{norm:positions}
 i_a=j_a=c(x_a),\qquad \ell_a=k-1-2c(x_a).
\end{equation}
These maps are injective and take values in $[0,k)$. No carries in
base three give $c(x)+c(y)=2c(z)$ only when $x=y=z$, so
\begin{equation}\label{norm:matching}
 i_a+j_{a'}+\ell_{a''}=k-1
 \quad\Longleftrightarrow\quad a=a'=a''.
\end{equation}
Every tag is the encoding of another word of the same cube. Hence
$t_s+i_a+\ell_b=k-1$ would force the tag word to equal a norm word,
contradicting their disjoint ranges. The same argument excludes
$t_s+t_t+\ell_a=k-1$. It also applies when the single tag is in row two.
Thus tags cannot contribute to the target coefficient. Lean proves
the exact cutoff counts, selection, bounds, injections, matching and
both tag exclusions; no large shift of the norm supports is used.
"""


def patch_source():
    originals, changed = five_sections()
    name="03-norm-digits.tex"
    text=replace_once(changed[name],FIVE_POSITIONS,POSITIONS)
    text=replace_once(text,
        r"residue $\lambda_s$ in row 2 at position $s$, for $0\le s<d$.",
        r"residue $\lambda_s$ in row 2 at position $t_s$, for $0\le s<5$.")
    text=replace_once(text,"The tag separation inequality excludes every tag from a triple",
                      "The reserved-word matching property excludes every tag from a triple")
    changed[name]=text
    name="04-orbits.tex"
    text=changed[name]
    text=replace_once(text,r"with $k\ge2d$,",r"with $k\ge20$,")
    text=replace_once(text,
        "Let $a<d$ be the first coordinate where the two label vectors differ.\n"
        "For degrees below $d$, both $A$ polynomials have constant coefficient $1$\n"
        "and all other coefficients $r$. The coefficients of $Q$ there are the\n"
        "unique positive representatives in $\\{1,\\ldots,r\\}$ of label coordinates.",
        "Let $s$ be the first coordinate where the two label vectors differ,\n"
        "and put $a=t_s<10$. For degrees below $10$, both $A$ polynomials\n"
        "have constant coefficient $1$ and all other coefficients $r$.\n"
        "At $t_0,t_1,t_2,t_3,t_4$, the coefficients of $Q$ are the unique\n"
        "positive representatives of the corresponding label coordinates;\n"
        "at the other positions below $10$ they equal $r$.")
    text=replace_once(text,
        "Put $v=k-1-a$. Since $a<d$ and $k\\ge2d$, we have $v\\ge d>a$.",
        "Put $v=k-1-a$. Since $a<10$ and $k\\ge20$, we have $v\\ge10>a$.")
    text=replace_once(text,"The tags\nand $k\\ge2d$","The tags\nand $k\\ge20$")
    changed[name]=text
    for name,text in changed.items():
        changed[name]=text.replace(r"m=9,\qquad k=1\,166\,895",r"m=12,\qquad k=408\,781").replace(
            r"145\,278\,430",r"50\,893\,237")
    return "".join("".join(difflib.unified_diff(
        originals[n].splitlines(keepends=True),changed[n].splitlines(keepends=True),
        fromfile="a/build/sections/"+n,tofile="b/build/sections/"+n)) for n in originals)


def count_states():
    states, ids = [], {}
    def add(depth, bound):
        key = depth, bound
        if key in ids:
            return ids[key]
        if depth == len(ALPHABETS):
            state = {"depth":depth, "bound":bound, "count":int(bound>0)}
        else:
            q, r = divmod(bound, 3)
            low, high = add(depth+1,q), add(depth+1,q+1)
            count = sum(states[high if digit<r else low]["count"] for digit in (0,1))
            state = {"depth":depth,"bound":bound,"low":low,"high":high,"count":count}
        ids[key] = len(states)
        states.append(state)
        return ids[key]
    lower, upper = add(0,LOWER), add(0,UPPER)
    return states, lower, upper


def data_source(states):
    text = "import Lean\n\nnamespace HeilbronnReservedData\n\n"
    for i,s in enumerate(states):
        text += f"def row{i} : Array Nat := #[{s['count']}]\n\n"
    return text+"end HeilbronnReservedData\n"


def proof_source(states,lower,upper):
    text = """import IntervalCounting
import ReservedLayerData

/-! Generated exact prefix-count recurrence, checked by the Lean kernel. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace HeilbronnReservedLayer
open HeilbronnInterval HeilbronnReservedData

"""
    for i,s in enumerate(states):
        depth,bound=s["depth"],s["bound"]
        tail=str(ALPHABETS[depth:])
        if depth<len(ALPHABETS):
            lo,hi=s["low"],s["high"]
            text+=f"theorem transition_{i} : tableAdvance 1 1 {bound} row{lo}.toList row{hi}.toList = row{i}.toList := by decide\n\n"
        binder="_he" if depth==len(ALPHABETS) else "he"
        text+=f"theorem row_{i}_correct (e : Nat) ({binder} : e < 1) :\n    belowCount {tail} e {bound} = row{i}.toList.getD e 0 := by\n"
        if depth==len(ALPHABETS):
            if bound>0:
                text+=f"  rw [show row{i}.toList = 1 :: List.replicate 0 0 by decide, unit_row, below_nil]\n  simp\n\n"
            else:
                text+=f"  rw [show row{i}.toList = List.replicate 1 0 by decide, zero_row, below_nil]\n  simp\n\n"
        else:
            suffix=str(ALPHABETS[depth+1:])
            text+=f"""  rw [below_cons]
  have h := step_from_tables 1 {bound} e (belowCount {suffix})
    (fun j => row{lo}.toList.getD j 0) (fun j => row{hi}.toList.getD j 0)
    (fun j hj => row_{lo}_correct j (by omega))
    (fun j hj => row_{hi}_correct j (by omega))
  rw [h, ← tableAdvance_get 1 1 {bound} row{lo}.toList row{hi}.toList e he, transition_{i}]

"""
    text+=f"""def alphabets : List Nat := {ALPHABETS}
def lower : Nat := {LOWER}
def upper : Nat := {UPPER}

theorem below_lower : belowCount alphabets 0 lower = 5 :=
  row_{lower}_correct 0 (by decide)

theorem below_upper : belowCount alphabets 0 upper = 2921 :=
  row_{upper}_correct 0 (by decide)

theorem exact_interval_count : intervalCount alphabets 0 lower upper = 2916 := by
  have h := interval_partition alphabets 0 lower upper (by decide)
  rw [below_lower, below_upper] at h
  omega

#print axioms below_lower
#print axioms below_upper
#print axioms exact_interval_count

end HeilbronnReservedLayer
"""
    return text


def main():
    states,lo,hi=count_states()
    previous_path="certificates/five.json"
    previous=json.loads((ROOT/previous_path).read_text(encoding="utf-8"))
    rho=249*K+3
    gamma=Fraction(rho,rho+1)
    eta=Fraction(2,249*K+5)
    old=Fraction(int(previous["eta"]["numerator"]),int(previous["eta"]["denominator"]))
    c={"schema":"heilbronn-reserved-v1","upstream_commit":PIN,
       "status":previous["status"],"scope":previous["scope"],
       "previous_certificate":previous_path,
       "previous_sha256":sha256((ROOT/previous_path).read_bytes()).hexdigest(),
       "d":5,"T":str(TARGET),"k":str(K),
       "decomposition":previous["decomposition"],"scales":previous["scales"],
       "row_digits":previous["row_digits"],"cap":previous["cap"],
       "prime_transfer":previous["prime_transfer"],
       "packing":{"half_alphabets_low_first":ALPHABETS,"energy_index":0,
                  "squared_norm":12,"source_box_k":3**12,
                  "lower_inclusive":LOWER,"upper_exclusive":UPPER,
                  "count_below_lower":5,"count_below_upper":2921,"interval_count":TARGET,
                  "lower_state":lo,"upper_state":hi,"count_states":states,
                  "positions":["u","u","k-1-2*u"]},
       "tags":{"positions":TAGS,"span":10,"row1":{"0":"1"},
               "row2":"five basis coordinates at the reserved positions",
               "top_row_digit_choices":1,"minor_valuation_max":9,
               "fresh_digit_index_min":K-10,"required_k_min":20,
               "exclusion":"all five tag words and all norm words share one midpoint-free cube"},
       "collision":{"M":"L3/r = 400*k^2*r^3","exactly_two_equal_moment":"2/M",
                    "all_three_equal_moment":2,"total":"6/(M*r^d)+2/r^(2*d)",
                    "r_powers":[-8,-10],"minor_bound":"a < 10; field degree remains 5"},
       "rho":str(rho),"beta":rational(Fraction(83*K+1,2)),
       "gamma":rational(gamma),"alpha":rational(rho+gamma),"eta":rational(eta),
       "gain_from_five":rational(eta/old),
       "constraints":{"zero_case_h_powers":[0,-2,-6],
                      "two_equal_r_power":rational(2*gamma-2),
                      "three_equal_r_power":rational(2*gamma-4),
                      "pair_r_power":rational(gamma-3*(K-1))},
       "formal_scope":{"new_proved":["exact counts of five tags and 2916 norm words",
                        "position bounds, injectivity and matching",
                        "exclusion of one or two reserved tags from the target coefficient",
                        "sparse tag distinction and fresh-position bounds"],
                       "inherited":"degree-five algebra and finite probability theorems",
                       "written_not_formalized":previous["formal_scope"]["written_not_formalized"]},
       "parameter_choice":"explicit feasible witness; no optimality claim"}
    for path,text in [
        ("certificates/reserved.json",json.dumps(c,indent=2)+"\n"),
        ("lean/ReservedLayerData.lean",data_source(states)),
        ("lean/ReservedLayer.lean",proof_source(states,lo,hi)),
        ("patches/reserved-tags.patch",patch_source())]:
        (ROOT/path).write_text(text,encoding="utf-8",newline="\n")
    print(f"Generated reserved-word certificate and {len(states)} exact count rows.")


if __name__=="__main__":
    main()
