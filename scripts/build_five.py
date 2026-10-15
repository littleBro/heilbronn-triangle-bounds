"""Degree five via low-position label tags and a fresh third-row digit."""
from fractions import Fraction
from hashlib import sha256
from math import prod
from pathlib import Path
import difflib
import json

from build_rowdigits import POSITIONS_SEVEN, row_sections
from build_sphere import PIN, rational
from build_tuned import replace_once

ROOT = Path(__file__).resolve().parents[1]
ALPHABETS = [2]*4+[1]*5
ENERGY = 2
K0 = 3**5*7**4
SHIFT = (K0-1)//2+5
K = K0+2*SHIFT

POSITIONS = r"""Use nine coordinates with half-alphabets $(2,2,2,2,1,1,1,1,1)$
and radices $b_j=4A_j-1$. Write
\[
 u(x)=\sum_jx_j\prod_{h<j}b_h,\quad
 K_0=3^5\cdot7^4=583\,443,\quad v(x)=K_0-1-2u(x).
\]
The energy layer $\sum_j((2x_j-(2A_j-1))^2-1)/8=2$ has
\[
 2^9\binom42=3\,072>T=2\,916
\]
words of squared norm $25$. Choose $T$ distinct words. No carries and
strict convexity give $u(x)+u(y)+v(z)=K_0-1$ exactly when $x=y=z$.
Also $0\le u(x)\le(K_0-1)/2$ and $0\le v(x)<K_0$.
Set
\[
 S=(K_0-1)/2+d=291\,726,\qquad
 k=K_0+2S=1\,166\,895.
\]
The norm positions are
\begin{equation}\label{norm:positions}
 i_a=j_a=S+u(x_a),\qquad \ell_a=v(x_a).
\end{equation}
They are distinct within each row and lie in $[0,k)$; moreover
\begin{equation}\label{norm:matching}
 i_a+j_{a'}+\ell_{a''}=k-1\quad\Longleftrightarrow\quad a=a'=a''.
\end{equation}
Reserve positions $0,\ldots,d-1$ in the first two rows for label tags.
A triple using a tag in either of these rows has total position at most
\[
 (d-1)+(S+(K_0-1)/2)+(K_0-1)=k-2.
\]
This also bounds triples with two tags. Thus tags do not contribute to
the coefficient at $k-1$. Lean proves the layer count, shifted matching,
and tag separation inequalities.
"""

COLLISION = r"""
\begin{lemma}[A fresh digit for two equal labels]\label{orb:tagged-moment}
Use the tagged construction in Section~\ref{norm:section}, with $k\ge2d$,
$L_1=L_2=r$, $M=L_3/r$, and $\theta=B/M^2\le1/2$.
Let $J$ be the event that $\det C$ has a representative in $[-\tau,\tau]$.
For each fixed label triple with exactly two equal labels,
\begin{equation}\label{orb:tagged-pair}
 \mathbb E[D\mathbf1_J\mid\text{labels}]\le\frac2M.
\end{equation}
Consequently, for three independent uniform labels in $\mathbb F_{r^d}$,
\begin{equation}\label{orb:tagged-total}
 \mathbb E[D\mathbf1_J]\le\frac6{Mr^d}+\frac2{r^{2d}}.
\end{equation}
\end{lemma}
\begin{proof}
Permute columns so the labels are $(\lambda,\lambda,\mu)$ with
$\lambda\ne\mu$. This preserves $D$ and $J$. The first two digit rows
are deterministic functions of the label because $L_1=L_2=r$.
Write their integer digit polynomials as $A_\lambda,Q_\lambda$ and
$A_\mu,Q_\mu$, and the three random third-row polynomials as $Z_1,Z_2,Z_3$.
The determinant polynomial factors as
\[
 F(Y)=U(Y)(Z_1(Y)-Z_2(Y)),\qquad
 U=A_\lambda Q_\mu-A_\mu Q_\lambda.
\]
Let $a<d$ be the first coordinate where the two label vectors differ.
For degrees below $d$, both $A$ polynomials have constant coefficient $1$
and all other coefficients $r$. The coefficients of $Q$ there are the
unique positive representatives in $\{1,\ldots,r\}$ of label coordinates.
Therefore $U_0=\cdots=U_{a-1}=0$ and $0<|U_a|<r<B$.
It follows that the top-row minor $U(B)$ has $B$-adic valuation exactly
$a$. The minor criterion in Lemma~\ref{orb:diagonal} gives $b\le a$.

Let $F_u$ denote the integer coefficient of $Y^u$ in $F$.
The bounds \eqref{norm:centered} and \eqref{norm:lower-carry} imply
\[
 J\ \Longrightarrow\ F_{k-1}=0:
\]
if this coefficient is a nonzero integer, the same $47/50$ lower bound
used in the determinant obstruction excludes $J$, irrespective of labels.
Put $v=k-1-a$. Since $a<d$ and $k\ge2d$, we have $v\ge d>a$.
Conditional on all third-row digits except the digit of $Z_2$ at position
$v$, the equation $F_{k-1}=0$ determines that digit uniquely: its
coefficient is the nonzero integer $-U_a$. Each allowed digit has
probability $1/M$. In particular $\Pr(J\mid\text{labels})\le1/M$.

For $1\le j\le a$, first condition on the complete column 1, on the
deterministic top two rows, and on all digits of $Z_2,Z_3$ at positions
at least $j$, except the digit of $Z_2$ at $v$. If $b\ge j$, the two
third-row Schur congruences force the first $j$ digits of both $Z_2,Z_3$.
Their joint conditional probability is at most $M^{-2j}$. After these
low digits are exposed, the untouched digit at $v\ge j$ still has $M$
independent choices, and $F_{k-1}=0$ permits at most one. Hence
\[
 \Pr(b\ge j,\ J\mid\text{labels})\le M^{-(2j+1)}.
\]
Use $b\le a$ and the tail identity for $B^b$ to obtain
\[
 \mathbb E[D\mathbf1_J\mid\text{labels}]
 \le\frac1M\left(1+\sum_{j=1}^a\theta^j\right)\le\frac2M.
\]
The probability of exactly two equal labels is at most $3r^{-d}$.
All three equal labels have probability $r^{-2d}$; in that case the
top two rows have identical columns, so $\det C=0$, but the uniform
moment bound still gives $\mathbb E[D\mid\text{labels}]\le2$.
Distinct labels make $J$ impossible. These three disjoint cases prove
\eqref{orb:tagged-total}.
\end{proof}

The finite digit argument is formalized in \texttt{FiveTagged.lean},
with column reindexing in \texttt{FiveReindex.lean} and label averaging
in \texttt{FiveFiniteTheorem.lean}. The latter takes explicit tag data
and the distinct-label exclusion interface. Instantiating these from
the norm packing, and identifying the minor exponent with the Smith
divisor in Lemma~\ref{orb:diagonal}, remain written connections.

The fresh-position condition matters: a digit already fixed by the
Schur congruences cannot supply the extra factor $1/M$. Likewise a
label pair whose top rows agree supplies no nonzero $U_a$. The tags
and $k\ge2d$ establish both requirements uniformly, not just on average.
"""

BAD_PROOF = r"""\begin{proof}
Conditional on the labels and $C$, the bad-triple probability is zero
unless $J$ holds, because special-linear multiplication preserves
the determinant residue. If $J$ holds, there is at most one possible
integer determinant in $[-\tau,\tau]$. The exact lifting identity,
weighted count and orbit bound give
\[
 \Pr(\text{bad}\mid C,\text{labels})
 \ll(\log(2N))^2\frac{hD}{N^3}\mathbf1_J.
\]
Average using Lemma~\ref{orb:tagged-moment}. Since
$M=400k^2r^3$ and $d=5$, its two terms are $O_k(r^{-8})$ and
$O(r^{-10})$, respectively. This proves the stated bound.
\end{proof}
"""

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


def rows():
    table = [[1]+[0]*ENERGY]
    for a in reversed(ALPHABETS):
        table.append([sum(2*table[-1][e-j*(j+1)//2] for j in range(a)
                         if j*(j+1)//2 <= e) for e in range(ENERGY+1)])
    return table


def table_source(table):
    text = "import Lean\n\nnamespace HeilbronnFiveLayer\n\n"
    for i, row in enumerate(table):
        text += f"def row{i} : Array Nat := #["+", ".join(map(str, row))+"]\n\n"
    return text+"end HeilbronnFiveLayer\n"


def five_sections():
    originals, changed = row_sections()
    name = "03-norm-digits.tex"
    text = changed[name]
    for old, new in [("d=7", "d=5"), ("13\\cdot18^3", "9\\cdot18^2"),
                     ("75\\,816", "2\\,916"), ("degree-$7$", "degree-$5$"),
                     ("seven conjugates", "five conjugates"), ("and three\npairs", "and two\npairs"),
                     ("\\}^3", "\\}^2"), ("v=1}^3", "v=1}^2"),
                     ("3^3\\mathcal N", "3^2\\mathcal N"), ("degree seven.", "degree five."),
                     ("$13$ distinct", "$9$ distinct"), ("3^{-3}", "3^{-2}"),
                     ("1\\le\\nu\\le7", "1\\le\\nu\\le5"),
                     ("m=9,\\qquad k=11\\cdot7^8", "m=9,\\qquad k=1\\,166\\,895")]:
        text = text.replace(old, new)
    text = replace_once(text, POSITIONS_SEVEN, POSITIONS)
    text = replace_once(text, "At every other position its required residue is zero.",
        r"""In addition, prescribe residue $1$ in row 1 at position $0$.
Write $\xi=\sum_{s=0}^{d-1}\lambda_s\beta_{s+1}$ and prescribe
residue $\lambda_s$ in row 2 at position $s$, for $0\le s<d$.
These tag positions are disjoint from the norm positions in their rows.
At every remaining position the residue is zero.""")
    text = replace_once(text, "Modulo $r$, all terms with an undesignated position vanish.",
        "Modulo $r$, positions outside the norm support and the tags vanish.\n"
        "The tag separation inequality excludes every tag from a triple\n"
        "of positions with sum $k-1$.")
    changed[name] = text
    changed["04-orbits.tex"] += COLLISION
    name = "06-sampling.tex"
    text = changed[name]
    start = text.index(r"\begin{corollary}[Probability of a bad triple]")
    text = text[:start]+text[start:].replace(r"\frac{h}{N^3r^d}", r"\frac{h}{N^3r^8}")
    start = text.index(r"\begin{proof}", start)
    stop = text.index(r"\end{proof}", start)+len(r"\end{proof}")
    changed[name] = text[:start]+BAD_PROOF+text[stop:]
    name = "08-alteration.tex"
    text = changed[name].replace("d=7", "d=5")
    text = replace_once(text, r"\gamma=\frac{\rho}{2\rho+1}", r"\gamma=\frac{\rho}{\rho+1}")
    text = replace_once(text, r"$0<\gamma<1/2$ and $2\gamma-1=-1/(2\rho+1)<0$",
                              r"$0<\gamma<1$ and $2\gamma-2=-2/(\rho+1)<0$")
    text = text.replace(r"\frac{h}{N^3r^d}", r"\frac{h}{N^3r^8}")
    text = text.replace(r"\frac{h}{N^3r^7}", r"\frac{h}{N^3r^8}")
    text = text.replace(r"2\gamma-7", r"2\gamma-8").replace(r"2\gamma-1", r"2\gamma-2")
    text = replace_once(text, r"\frac1{\rho+1}=\frac1{249k+4}",
                              r"\frac2{\rho+2}=\frac2{249k+5}=\frac1{145\,278\,430}")
    changed[name] = text
    return originals, changed


def patch_sections():
    originals, changed = five_sections()
    return "".join("".join(difflib.unified_diff(
        originals[n].splitlines(keepends=True), changed[n].splitlines(keepends=True),
        fromfile="a/build/sections/"+n, tofile="b/build/sections/"+n)) for n in originals)


def main():
    previous_path = "certificates/rowdigits.json"
    previous = json.loads((ROOT/previous_path).read_text(encoding="utf-8"))
    rho = 249*K+3
    gamma = Fraction(rho, rho+1)
    alpha = rho+gamma
    eta = 2*gamma/alpha
    old = Fraction(int(previous["eta"]["numerator"]), int(previous["eta"]["denominator"]))
    decomposition = dict(previous["decomposition"])
    decomposition.update(pairs=2, extension_determinants="324", nodes_per_term=9,
        normalization_denominator=9, formal_base_field_minimum=9,
        row_maps=["3^(-2) * eval_t", "eval_t", "constantCoord(c_t * input)"])
    c = {"schema":"heilbronn-five-v1", "upstream_commit":PIN,
        "status":previous["status"], "scope":previous["scope"],
        "previous_certificate":previous_path, "previous_sha256":sha256((ROOT/previous_path).read_bytes()).hexdigest(),
        "d":5, "T":"2916", "k":str(K), "decomposition":decomposition,
        "packing":{"half_alphabets_low_first":ALPHABETS, "radices_low_first":[4*a-1 for a in ALPHABETS],
            "unshifted_base":str(K0), "shift":str(SHIFT), "energy_index":ENERGY,
            "squared_norm":25, "layer_count":"3072", "count_table":rows(),
            "positions":["S+u", "S+u", "K0-1-2*u"]},
        "tags":{"row1":{"0":"1"}, "row2":"basis coordinates of the label at positions 0..d-1",
            "top_row_digit_choices":1, "minor_valuation_max":4, "fresh_digit_index_min":K-5,
            "required_k_min":10, "largest_tagged_position_sum":K-2},
        "scales":previous["scales"], "row_digits":previous["row_digits"],
        "collision":{"M":"L3/r = 400*k^2*r^3", "exactly_two_equal_moment":"2/M",
            "joint_tail":"Pr(b>=j and J | labels) <= M^(-2*j-1), 1<=j<=a<d",
            "all_three_equal_moment":2, "total":"6/(M*r^d)+2/r^(2*d)",
            "r_powers":[-8,-10], "proof_status":"Lean; explicit tag and distinct-label interfaces",
        "pair_theorem":"HeilbronnFive.DigitModel.tagged_small_residue_moment",
        "total_theorem":"HeilbronnFive.total_small_residue_moment"},
        "prime_transfer":previous["prime_transfer"], "cap":previous["cap"],
        "rho":str(rho), "beta":rational(Fraction(83*K+1,2)),
        "gamma":rational(gamma), "alpha":rational(alpha), "eta":rational(eta),
        "gain_from_rowdigits":rational(eta/old),
        "constraints":{"zero_case_h_powers":[0,-2,-6],
            "two_equal_r_power":rational(2*gamma+6-8),
            "three_equal_r_power":rational(2*gamma+6-10),
            "pair_r_power":rational(gamma-3*(K-1))},
        "formal_scope":{"proved":PROVED,"written_not_formalized":WRITTEN},
        "parameter_choice":"explicit feasible witness; no optimality claim"}
    assert prod(4*a-1 for a in ALPHABETS) == K0
    for path, text in [("certificates/five.json",json.dumps(c,indent=2)+"\n"),
                       ("patches/degree-five.patch",patch_sections()),
                       ("lean/FiveLayerData.lean",table_source(rows()))]:
        (ROOT/path).write_text(text,encoding="utf-8",newline="\n")
    print("Generated degree-five certificate, layer table and tagged source patch.")


if __name__ == "__main__":
    main()
