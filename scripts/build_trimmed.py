"""Generate the interval-packing certificate, kernel count tables and source patch."""
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import difflib
import json

from build_eighteen import DECOMPOSITION, PRIME_TRANSFER
from build_slab import slab_sections
from build_sphere import PIN, rational
from build_tuned import replace_once

ROOT = Path(__file__).resolve().parents[1]
ALPHABETS = [4,4,4,4,4,4,5,4,5,5,5]
ENERGY = 32
LOWER = 133966008273
UPPER = 10996717764905
TARGET = 25*18**6
K = 2*(UPPER-LOWER)-1


def count_states():
    states, ids = [], {}
    def add(depth, bound):
        key = depth, bound
        if key in ids:
            return ids[key]
        if depth == len(ALPHABETS):
            row = [int(bound > 0)]+[0]*ENERGY
            state = {"depth": depth, "bound": str(bound), "counts": row}
        else:
            a = ALPHABETS[depth]
            q, r = divmod(bound, 4*a-1)
            low, high = add(depth+1, q), add(depth+1, q+1)
            row = [0]*(ENERGY+1)
            for digit in range(2*a):
                radius = abs(2*digit-(2*a-1))//2
                cost = radius*(radius+1)//2
                child = states[high if digit < r else low]["counts"]
                for e in range(cost, ENERGY+1):
                    row[e] += child[e-cost]
            state = {"depth": depth, "bound": str(bound), "low": low, "high": high, "counts": row}
        ids[key] = len(states)
        states.append(state)
        return ids[key]
    lower, upper = add(0, LOWER), add(0, UPPER)
    return states, lower, upper


def data_source(states):
    text = "import Lean\n\nnamespace HeilbronnTrimmedData\n\n"
    for i, state in enumerate(states):
        row = state["counts"]
        text += f"def row{i} : Array Nat := #[\n"
        text += ",\n".join("  "+", ".join(map(str, row[j:j+8])) for j in range(0, len(row), 8))+"\n]\n\n"
    return text+"end HeilbronnTrimmedData\n"


def proof_source(states, lower, upper):
    text = """import IntervalCounting
import TrimmedLayerData

/-! Generated recurrence proof; every finite transition is kernel-checked. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace HeilbronnTrimmedLayer
open HeilbronnInterval HeilbronnTrimmedData

"""
    for i, state in enumerate(states):
        depth, bound = state["depth"], int(state["bound"])
        tail = str(ALPHABETS[depth:])
        if depth < len(ALPHABETS):
            a, low, high = ALPHABETS[depth], state["low"], state["high"]
            text += f"theorem transition_{i} : tableAdvance 33 {a} {bound} row{low}.toList row{high}.toList = row{i}.toList := by decide\n\n"
        binder = "_he" if depth == len(ALPHABETS) else "he"
        text += f"theorem row_{i}_correct (e : Nat) ({binder} : e < 33) :\n    belowCount {tail} e {bound} = row{i}.toList.getD e 0 := by\n"
        if depth == len(ALPHABETS):
            if bound > 0:
                text += f"  rw [show row{i}.toList = 1 :: List.replicate 32 0 by decide, unit_row, below_nil]\n  simp\n\n"
            else:
                text += f"  rw [show row{i}.toList = List.replicate 33 0 by decide, zero_row, below_nil]\n  simp\n\n"
        else:
            suffix = str(ALPHABETS[depth+1:])
            text += f"""  rw [below_cons]
  have h := step_from_tables {a} {bound} e (belowCount {suffix})
    (fun j => row{low}.toList.getD j 0) (fun j => row{high}.toList.getD j 0)
    (fun j hj => row_{low}_correct j (by omega))
    (fun j hj => row_{high}_correct j (by omega))
  rw [h, ← tableAdvance_get 33 {a} {bound} row{low}.toList row{high}.toList e he, transition_{i}]

"""
    text += f"""def alphabets : List Nat := {ALPHABETS}
def lower : Nat := {LOWER}
def upper : Nat := {UPPER}

theorem below_lower : belowCount alphabets 32 lower = {states[lower]['counts'][ENERGY]} :=
  row_{lower}_correct 32 (by decide)

theorem below_upper : belowCount alphabets 32 upper = {states[upper]['counts'][ENERGY]} :=
  row_{upper}_correct 32 (by decide)

theorem exact_interval_count : intervalCount alphabets 32 lower upper = {TARGET} := by
  have h := interval_partition alphabets 32 lower upper (by decide)
  rw [below_lower, below_upper] at h
  omega

#print axioms below_lower
#print axioms below_upper
#print axioms exact_interval_count

end HeilbronnTrimmedLayer
"""
    return text


POSITIONS = r"""Use eleven coordinates with half-alphabets
$(4,4,4,4,4,4,5,4,5,5,5)$ and radices $b_j=4A_j-1$.
For $0\le x_j<2A_j$, put
\[
 E(x)=\sum_j\frac{(2x_j-(2A_j-1))^2-1}{8},\qquad
 c(x)=\sum_j x_j\prod_{h<j}b_h.
\]
The energy-$32$ layer has $872\,130\,560$ words of common squared
norm $267$. We retain only words whose encodings lie in $[C_-,C_+)$, where
\[
 C_-=133\,966\,008\,273,\qquad C_+=10\,996\,717\,764\,905.
\]
An exact cutoff recurrence gives
\[
 \#\{E(x)=32:c(x)<C_-\}=10\,596\,664,\qquad
 \#\{E(x)=32:c(x)<C_+\}=860\,902\,264.
\]
Their difference is exactly $T=850\,305\,600$. Lean proves these
counts from the actual finite word list, without enumerating it.
For a low digit $d$ in radix $b$, the cutoff for the remaining word is
$\lfloor R/b\rfloor+\mathbf1_{d<R\bmod b}$ for cutoff $R$. Subtract the digit's
energy and sum over digits; the empty word is the base case.

For each retained word define
\[
 u(x)=c(x)-C_-,\qquad v(x)=k-1-2u(x),\qquad
 k=2(C_+-C_-)-1=21\,725\,503\,513\,263.
\]
Both maps take values in $[0,k)$ and are injective. A relation
$u(x)+u(y)+v(z)=k-1$ is equivalent to $c(x)+c(y)=2c(z)$.
The original radices still prevent carries; equal squared norms then
force $x=y=z$. Translation and interval restriction preserve this
argument. The shorter $k$ is the final position range, not a new radix
product. Enumerate the retained words by $0\le a<T$ and set
\begin{equation}\label{norm:positions}
 i_a=j_a=u(x(a)),\qquad \ell_a=v(x(a)).
\end{equation}
The matching property is
\begin{equation}\label{norm:matching}
 i_a+j_{a'}+\ell_{a''}=k-1\quad\Longleftrightarrow\quad a=a'=a''.
\end{equation}
Lean proves selection, both bounds and injections, and matching.
The interval is a verified feasible witness; optimality is not claimed.
"""


def patch_source():
    originals, changed = slab_sections()
    name = "03-norm-digits.tex"
    text = replace_once(changed[name], "M=\\binom{4d-1}{d},\\qquad\n T=\\binom{M}{3}", "T=25\\cdot18^6")
    text = replace_once(text, r"m=17,\qquad A=101,\qquad k=403^{17}",
                        r"m=11,\qquad k=21\,725\,503\,513\,263")
    text = replace_once(text, "Let $r$ be an odd prime.", r"Let $r\ge37$ be prime with $r\equiv1\pmod3$.")
    text = replace_once(text, r"Choose an $\mathbb F_r$-basis $\beta_1,\ldots,\beta_d$ of $K$.",
                        r"Choose a power basis $\beta_\nu=\vartheta^{\nu-1}$, $1\le\nu\le13$, of $K/\mathbb F_r$.")
    start, stop = text.index(r"\begin{lemma}\label{norm:decomposition}"), text.index("For a label")
    text = text[:start]+DECOMPOSITION+text[stop:]
    text = replace_once(text, "numbers $d,M,T,k$", "numbers $d,T,k$")
    start, stop = text.index("We use a finite centered-sphere"), text.index("A random column")
    changed[name] = text[:start]+POSITIONS+"\n\n"+text[stop:]
    name = "08-alteration.tex"
    changed[name] = replace_once(changed[name], "a set for each sufficiently large prime $r$", r"a set for each sufficiently large prime $r\equiv1\pmod3$")
    changed[name] = replace_once(changed[name], "for every sufficiently large prime $r$.", r"for every sufficiently large prime $r\equiv1\pmod3$.")
    changed[name] = replace_once(changed[name], "Lemma~\\ref{norm:prime-interval} supplies a prime $r$ with $m<r\\le2m$.", PRIME_TRANSFER)
    return "".join("".join(difflib.unified_diff(originals[n].splitlines(keepends=True),
        changed[n].splitlines(keepends=True), fromfile="a/build/sections/"+n,
        tofile="b/build/sections/"+n)) for n in originals)


def main():
    states, lower, upper = count_states()
    path = "certificates/eighteen.json"
    previous = json.loads((ROOT/path).read_text(encoding="utf-8"))
    rho = 498*K+6
    beta, gamma = Fraction(83*K+1, 2), Fraction(rho, 2*rho+1)
    alpha, eta = rho+gamma, Fraction(1, rho+1)
    prior_eta = Fraction(int(previous["eta"]["numerator"]), int(previous["eta"]["denominator"]))
    c = {"schema": "heilbronn-trimmed-v1", "upstream_commit": PIN,
         "status": previous["status"], "scope": previous["scope"],
         "previous_certificate": path, "previous_sha256": sha256((ROOT/path).read_bytes()).hexdigest(),
         "d": 13, "T": str(TARGET), "k": str(K),
         "decomposition": previous["decomposition"], "prime_transfer": previous["prime_transfer"],
         "packing": {"half_alphabets_low_first": ALPHABETS, "radices_low_first": [4*a-1 for a in ALPHABETS],
             "energy_index": ENERGY, "squared_norm": 267, "full_layer_count": "872130560",
             "source_box_k": str(15**7*19**4), "lower_inclusive": str(LOWER), "upper_exclusive": str(UPPER),
             "count_below_lower": str(states[lower]["counts"][ENERGY]),
             "count_below_upper": str(states[upper]["counts"][ENERGY]), "interval_count": str(TARGET),
             "lower_state": lower, "upper_state": upper, "count_states": states},
         "cap": previous["cap"], "scales": previous["scales"], "rho": str(rho),
         "beta": rational(beta), "gamma": rational(gamma), "alpha": rational(alpha), "eta": rational(eta),
         "gain_from_eighteen": rational(eta/prior_eta),
         "constraints": {"zero_case_h_powers": [0,-2,-6],
             "collision_r_power": rational(2*gamma-1), "pair_r_power": rational(gamma-6*(K-1))},
         "formal_scope": {"inherited": "18-form norm decomposition and split-prime specialization",
             "new_proved": ["exact counts below both encoded cutoffs", "exact interval count",
                 "complete translated packing", "gain from the eighteen-form checkpoint greater than 1.0249"],
             "written_not_formalized": previous["formal_scope"]["written_not_formalized"]},
         "parameter_choice": "explicit feasible witness; no optimality claim"}
    for path, text in [("certificates/trimmed.json", json.dumps(c, indent=2)+"\n"),
                       ("lean/TrimmedLayerData.lean", data_source(states)),
                       ("lean/TrimmedLayer.lean", proof_source(states, lower, upper)),
                       ("patches/trimmed-sphere.patch", patch_source())]:
        (ROOT/path).write_text(text, encoding="utf-8", newline="\n")
    print(f"Generated interval certificate, {len(states)} count rows, recurrence proof and source patch.")


if __name__ == "__main__":
    main()
