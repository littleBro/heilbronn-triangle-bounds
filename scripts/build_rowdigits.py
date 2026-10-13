"""Degree-seven checkpoint using different digit ranges in the three rows."""
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import difflib
import json

from build_eighteen import DECOMPOSITION, POSITIONS, norm_sections
from build_sphere import PIN, rational
from build_tuned import replace_once

ROOT = Path(__file__).resolve().parents[1]
ALPHABETS = [3]+[2]*8
ENERGY = 5

POSITIONS_SEVEN = r"""Use nine coordinates with half-alphabets $(3,2,2,2,2,2,2,2,2)$
and radices $b_j=4A_j-1$. Put
\[
 u(x)=\sum_jx_j\prod_{h<j}b_h,\qquad
 k=11\cdot7^8=63\,412\,811.
\]
Writing $y_j=2x_j-(2A_j-1)$, the energy layer
$\sum_j(y_j^2-1)/8=5$ has exactly
\[
 [z^5]2^9(1+z+z^3)(1+z)^8
 =2^9\left(\binom85+\binom84+\binom82\right)=78\,848>T
\]
words, all of squared norm $9+8\cdot5=49$.
Choose $T$ distinct words and put $v(x)=k-1-2u(x)$.
Use the row positions
\begin{equation}\label{norm:positions}
 i_a=j_a=u(x_a),\qquad \ell_a=v(x_a).
\end{equation}
They are in $\{0,\ldots,k-1\}$ and distinct within each row.
Since digit sums are below the radices, encoded midpoints are coordinatewise
midpoints. Equal squared norms then force equality. Consequently
\begin{equation}\label{norm:matching}
 i_a+j_{a'}+\ell_{a''}=k-1\quad\Longleftrightarrow\quad a=a'=a''.
\end{equation}
Lean checks the exact layer recurrence and proves the full packing.
"""

CONDITIONAL = r"""\begin{lemma}[Conditional digit estimate with row-dependent ranges]
\label{orb:conditional}
Let $r,L_1,L_2,L_3$ be positive integers with $r\ge2$,
$r\mid L_i$, and $L_i<B$ for $1\le i\le3$.
Let $\mathscr L$ be a label set. For each label $\lambda$, row $i$,
and position $0\le u<k$, prescribe a residue
$a_{iu}(\lambda)\in\mathbb Z/r\mathbb Z$.
Fix any three labels $\lambda_1,\lambda_2,\lambda_3$, allowing repetitions.
Independently for every $i,j,u$, choose $d_{iju}$ uniformly from
\[
 \{a\in\{1,\ldots,L_i\}:a\equiv a_{iu}(\lambda_j)\pmod r\},
 \qquad C_{ij}=\sum_{u=0}^{k-1}d_{iju}B^u\pmod h.
\]
Let $b$ and $D=B^b$ be as in Lemma~\ref{orb:diagonal}, and put
$p_*=(r/L_2)^2(r/L_3)^2$ and $\theta=Bp_*$.
For every $1\le j\le k$,
\begin{equation}\label{orb:tail}
 \Pr(b\ge j\mid\lambda_1,\lambda_2,\lambda_3)\le p_*^j.
\end{equation}
If $\theta<1$, then
\begin{equation}\label{orb:moment}
 \mathbb E[D\mid\lambda_1,\lambda_2,\lambda_3]
 \le1+\sum_{j=1}^k\theta^j\le\frac1{1-\theta}.
\end{equation}
\end{lemma}
\begin{proof}
Each digit in row $i$ has exactly $L_i/r$ choices. Positive low digits
smaller than $B$ make every entry of $C$ a unit. In addition to the labels,
condition on the complete first column and the first entries of the
other two columns. If $b\ge j$, the minor criterion gives
\[
 C_{iv}\equiv C_{i1}C_{11}^{-1}C_{1v}\pmod{B^j},\qquad i,v\in\{2,3\}.
\]
Each right side is fixed. The first $j$ base-$B$ digits of each remaining
entry are therefore fixed, with probability zero or $(r/L_i)^j$.
The four entries use disjoint independent draws, so the joint probability
is at most $(r/L_2)^{2j}(r/L_3)^{2j}=p_*^j$.
This remains valid when $L_i=r$: those digits are deterministic,
and their factors are one. Repeated labels impose no equality between
independent draws in the third row. Averaging the conditioning proves
\eqref{orb:tail}, including $j=k$. Finally use the pointwise identity
\[
 B^b=1+\sum_{j=1}^k(B^j-B^{j-1})\mathbf1_{\{b\ge j\}}
\]
and $B^j-B^{j-1}\le B^j$ to obtain \eqref{orb:moment}.
\end{proof}

For $L_1=L_2=r$, $L_3=400k^2r^4$, and
$B\le200k^2L_1L_2L_3$, we have
\[
 \theta=B(r/L_3)^2\le200k^2r^4/L_3=\frac12.
\]
Thus, uniformly for every allowed $r$,
"""


def rows():
    table = [[1]+[0]*ENERGY]
    for a in reversed(ALPHABETS):
        table.append([sum(2*table[-1][e-j*(j+1)//2] for j in range(a)
                          if j*(j+1)//2 <= e) for e in range(ENERGY+1)])
    return table


def table_source(table):
    text = "import Lean\n\nnamespace HeilbronnSevenLayer\n\n"
    for i, row in enumerate(table):
        text += f"def row{i} : Array Nat := #["+", ".join(map(str, row))+"]\n\n"
    return text+"end HeilbronnSevenLayer\n"


def patch_sections():
    originals, changed = norm_sections()
    name = "03-norm-digits.tex"
    text = changed[name]
    dec = (DECOMPOSITION.replace("d=13", "d=7").replace("25\\cdot18^6=850\\,305\\,600", "13\\cdot18^3=75\\,816")
           .replace("degree-$13$", "degree-$7$").replace("thirteen conjugates", "seven conjugates")
           .replace("six\npairs", "three\npairs").replace("\\}^6", "\\}^3")
           .replace("v=1}^6", "v=1}^3").replace("3^6", "3^3").replace("thirteen.", "seven.")
           .replace("$25$ distinct", "$13$ distinct").replace("3^{-6}", "3^{-3}")
           .replace("25\\cdot18^6", "13\\cdot18^3"))
    text = replace_once(text, DECOMPOSITION, dec)
    text = text.replace("d=13", "d=7").replace("T=25\\cdot18^6", "T=13\\cdot18^3")
    text = text.replace(r"m=11,\qquad k=15^7\cdot19^4", r"m=9,\qquad k=11\cdot7^8")
    text = text.replace(r"1\le\nu\le13", r"1\le\nu\le7")
    text = replace_once(text, POSITIONS, POSITIONS_SEVEN)
    text = replace_once(text, "Set $L=400k^2r^4$.",
        "Set $L_1=L_2=r$, $L_3=400k^2r^4$, and $P=L_1L_2L_3=400k^2r^6$.")
    text = text.replace("k^2L^3", "k^2P").replace(r"\{1,\ldots,L\}", r"\{1,\ldots,L_i\}")
    text = replace_once(text, "Every required residue has exactly $L/r=400k^2r^3$ possible digits, including",
        "In row $i$, every required residue has exactly $L_i/r$ possible digits, including")
    text = replace_once(text, "Since $L<B$", "Since $L_i<B$ for each row")
    text = replace_once(text, "choosing the first two digit positions determines the third.  Therefore",
        "choosing the first two digit positions determines the third. Each product\n"
        "uses one digit from each row, so its size is at most $P$. Therefore")
    changed[name] = text
    name = "04-orbits.tex"
    text = changed[name]
    start = text.index(r"\begin{lemma}[Conditional digit estimate]")
    stop = text.index(r"\begin{equation}", text.index("Thus, uniformly", start))
    changed[name] = text[:start]+CONDITIONAL+text[stop:]
    name = "08-alteration.tex"
    text = changed[name].replace("d=13", "d=7").replace("498k+6", "249k+3").replace("498k+7", "249k+4")
    text = text.replace(r"r^{12}", "r^6").replace(r"\gamma-6(k-1)", r"\gamma-3(k-1)")
    text = text.replace(r"r^{13}", "r^7").replace(r"2\gamma-13", r"2\gamma-7")
    text = text.replace(r"100k^2(400k^2)^3r^6<B\le200k^2(400k^2)^3r^6",
                        r"40000k^4r^6<B\le80000k^4r^6")
    text = replace_once(text, r"\gamma+12\beta", r"\gamma+6\beta")
    changed[name] = text
    return "".join("".join(difflib.unified_diff(
        originals[n].splitlines(keepends=True), changed[n].splitlines(keepends=True),
        fromfile="a/build/sections/"+n, tofile="b/build/sections/"+n)) for n in originals)


def main():
    k, term_count = 11*7**8, 13*18**3
    beta, rho = Fraction(83*k+1, 2), 249*k+3
    gamma = Fraction(rho, 2*rho+1)
    alpha = rho+gamma
    eta = 2*gamma/alpha
    path = "certificates/trimmed.json"
    previous = json.loads((ROOT/path).read_text(encoding="utf-8"))
    old_eta = Fraction(int(previous["eta"]["numerator"]), int(previous["eta"]["denominator"]))
    main_eta = Fraction(1, 498*(15**7*19**4)+7)
    decomposition = dict(previous["decomposition"])
    decomposition.update(pairs=3, extension_determinants=str(18**3), nodes_per_term=13,
        normalization_denominator=27, formal_base_field_minimum=13,
        row_maps=["3^(-3) * eval_t", "eval_t", "constantCoord(c_t * input)"])
    scales = {key: value for key, value in previous["scales"].items() if key not in ("L", "B")}
    scales.update(L1="r", L2="r", L3="400*k^2*r^4", P="L1*L2*L3",
                  B="100*k^2*P < B <= 200*k^2*P; B prime")
    c = {"schema": "heilbronn-rowdigits-v1", "upstream_commit": PIN,
        "status": "conditional-on-upstream-estimates", "scope": previous["scope"],
        "previous_certificate": path, "previous_sha256": sha256((ROOT/path).read_bytes()).hexdigest(),
        "d": 7, "T": str(term_count), "k": str(k), "decomposition": decomposition,
        "packing": {"half_alphabets_low_first": ALPHABETS, "radices_low_first": [4*a-1 for a in ALPHABETS],
            "energy_index": ENERGY, "squared_norm": 49, "layer_count": str(rows()[-1][ENERGY]),
            "count_table": rows()},
        "row_digits": {"coefficient_bound": "6*k^2*L1*L2*L3",
            "general_tail": "((r/L2)^2*(r/L3)^2)^j", "chosen_tail": "(r/L3)^(2*j)",
            "theta": "B*(r/L3)^2", "theta_upper": rational(Fraction(1, 2)),
            "conditional_moment_upper": 2, "base_r_power": 6,
            "conditional_probability_proof": "written; not formalized in Lean"},
        "prime_transfer": previous["prime_transfer"], "cap": previous["cap"], "scales": scales,
        "rho": str(rho), "beta": rational(beta), "gamma": rational(gamma), "alpha": rational(alpha),
        "eta": rational(eta), "gain_from_trimmed": rational(eta/old_eta),
        "gain_from_eighteen": rational(eta/main_eta),
        "constraints": {"zero_case_h_powers": [0, -2, -6],
            "collision_r_power": rational(2*gamma+6-7), "pair_r_power": rational(gamma-3*(k-1))},
        "formal_scope": {"proved": ["degree-7 norm decomposition into 13*18^3 determinants",
            "homogeneous coordinates and distinct-label criterion over split primes",
            "exact energy-5 layer and complete mixed-radix packing",
            "row-digit divisibility, moment-bound arithmetic and base scale identity",
            "cleared-denominator alteration inequalities and exponent identity",
            "gain from trimmed checkpoint greater than 680000"],
            "written_not_formalized": ["conditional divisor tail and expectation with row-dependent digit ranges",
                "upstream lattice, orbit, slab geometry and weighted counting arguments",
                "probability, asymptotic deletion and interpolation",
                "prime number theorem in the progression 1 mod 3"]},
        "parameter_choice": "explicit feasible witness; no optimality claim"}
    for path, text in [("certificates/rowdigits.json", json.dumps(c, indent=2)+"\n"),
                       ("patches/row-digits.patch", patch_sections()),
                       ("lean/SevenLayerData.lean", table_source(rows()))]:
        (ROOT/path).write_text(text, encoding="utf-8", newline="\n")
    print("Generated row-digit certificate, exact layer table and source patch.")


if __name__ == "__main__":
    main()
