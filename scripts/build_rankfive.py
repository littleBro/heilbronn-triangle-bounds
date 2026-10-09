"""Generate the rank-five norm / mixed-radix checkpoint and manuscript patch."""
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import difflib
import json

from build_slab import slab_sections
from build_sphere import PIN, rational
from build_tuned import replace_once

ROOT = Path(__file__).resolve().parents[1]

DECOMPOSITION = r"""\begin{lemma}\label{norm:decomposition}
For $d=13$ there exist homogeneous degree-$d$ polynomials
$f_{ia}\in\mathbb F_r[X]$ (allowing zero), for $1\le i\le3$ and
$0\le a<T=25(5^{13}+60)/13=2\,347\,506\,125$, such that
\begin{equation}\label{norm:determinant-sum}
 \mathcal N(X^{(1)},X^{(2)},X^{(3)})
 =\sum_{a=0}^{T-1}\det\bigl(f_{ia}(X^{(j)})\bigr)_{1\le i,j\le3}.
\end{equation}
\end{lemma}
\begin{proof}
Use the integral five-term determinant formula of Krishna--Makam,
\emph{On the tensor rank of $3\times3$ permanent and determinant},
arXiv:1801.00496, Section 3.1. Write its three linear forms as rows:
\[
\begin{array}{c|ccc}
t&l_{t1}(Z)&l_{t2}(Z)&l_{t3}(Z)\\\hline
0&Z_2+Z_3&Z_1&Z_2\\
1&-Z_1-Z_3&Z_2&Z_1\\
2&-Z_2&Z_1+Z_3&Z_2+Z_3\\
3&Z_2-Z_1&Z_3&Z_1+Z_2+Z_3\\
4&Z_1&Z_2+Z_3&Z_1+Z_3
\end{array}
\]
Then $\det(Z^{(1)},Z^{(2)},Z^{(3)})
=\sum_{t=0}^4\prod_{i=1}^3 l_{ti}(Z^{(i)})$.
Let $G=\operatorname{Gal}(K/\mathbb F_r)$ and $W=\{0,\ldots,4\}^G$.
Put $H_{i,w}(X)=\prod_{g\in G}g(l_{w(g),i}(Z(X)))$.
Expand the product of the thirteen conjugate determinants with the
five-term formula, and antisymmetrize the three columns. Since $13$
is odd, the norm changes by the sign of the column permutation.
Consequently the exact identity is
\[
 6\mathcal N=\sum_{w\in W}D_w,\qquad
 D_w=\det(H_{i,w}(X^{(j)}))_{i,j=1}^3.
\]
The factor $6$ is essential. All divisions below are valid for prime
$r\ge37$. Rotate words by $(a\cdot w)(g)=w(a^{-1}g)$.
Reindexing the product gives $D_{a\cdot w}=a(D_w)$.
A fixed word is constant. Thus exactly five words are fixed, and
every other orbit has size $13$, giving
\[
 Q=5+\frac{5^{13}-5}{13}=93\,900\,245.
\]
For the constant-coordinate functional $\ell$ of a power basis,
$L(z)=13^{-1}\sum_{a\in G}\ell(a(z))$ fixes the base field and is
$G$-invariant. With representatives $w_q$ and orbit sizes $n_q$,
\[
 \mathcal N=\sum_q \frac{n_q}{6}L(D_{w_q}).
\]
Let $\widehat x(Y)$ be the degree-less-than-$13$ representative of
$x\in K=\mathbb F_r[\vartheta]$. Interpolation at the $25$ distinct
nodes $t=0,\ldots,24$, with $c_t=L_t(\vartheta)$, gives
$xy=\sum_t\widehat x(t)\widehat y(t)c_t$.
Hence $L(xyz)=\sum_t\widehat x(t)\widehat y(t)L(c_tz)$.
Apply this to the six products in each determinant. For each $(q,t)$,
the coordinate rows are
\[
 \frac{n_q}{6}\widehat H_{1,w_q}(t,X),\qquad
 \widehat H_{2,w_q}(t,X),\qquad L(c_tH_{3,w_q}(X)).
\]
Every coordinate is homogeneous of degree $13$. All $Q$ classes,
including the five singletons, receive $25$ nodes, proving the claim.
\end{proof}

"""

POSITIONS = r"""Use a sphere with nine coordinates: one has alphabet
$\{0,\ldots,19\}$ and radix $39$, and eight have alphabet
$\{0,\ldots,17\}$ and radix $35$. For half-alphabets
$(A_0,\ldots,A_8)=(10,9,\ldots,9)$, set
\[
 b_j=4A_j-1,\quad u(x)=\sum_{j=0}^8 x_j\prod_{h<j}b_h,
 \quad k=\prod_j b_j=39\cdot35^8=87\,823\,140\,234\,375.
\]
Center the coordinates as $y_j=2x_j-(2A_j-1)$ and let
$J(x)=\sum_j (y_j^2-1)/8$. The exact coefficient is
\[
 [z^{119}]\left(2\sum_{a=0}^9z^{a(a+1)/2}\right)
 \left(2\sum_{a=0}^8z^{a(a+1)/2}\right)^8
 =2\,365\,025\,280>T.
\]
This is checked by the recurrence $C_{A::S}(e)=
2\sum_{a=0}^{A-1}C_S(e-a(a+1)/2)$, with negative indices zero
and $C_{[]}(e)=\mathbf1_{e=0}$. Nine transitions of a table with
$0\le e\le119$ are checked by the Lean kernel. Select any $T$ distinct
words in the layer $J=119$, whose common squared norm is $9+8\cdot119=961$.
For each selected word put $v(x)=k-1-2u(x)$. Then
$0\le u(x),v(x)<k$, both maps are injective, and
\[
 u(x)+u(y)+v(z)=k-1\quad\Longleftrightarrow\quad x=y=z.
\]
Indeed, the left side gives $u(x)+u(y)=2u(z)$. Reduction modulo the
first radix, then division and induction, gives coordinatewise
$x_j+y_j=2z_j$, since both digit sums are less than $b_j$.
Equal squared norms imply $x=y=z$ by strict convexity. The bound
$2u(x)+1\le k$ and injectivity follow by the same radix induction.
All these finite packing claims, including selection from the exact
layer count, are proved in Lean. Enumerate the selected words by
$0\le a<T$ and write their two positions as $u_a,v_a$.
"""


def rows():
    table = [[1]+[0]*119]
    for a in [9]*8+[10]:
        table.append([sum(2*table[-1][e-j*(j+1)//2] for j in range(a)
                          if j*(j+1)//2 <= e) for e in range(120)])
    return table


def table_source(table):
    text = "import Lean\n\nnamespace HeilbronnMixedLayer\n\n"
    for i, row in enumerate(table):
        text += f"def row{i} : Array Nat := #[\n"
        text += ",\n".join("  "+", ".join(map(str, row[j:j+8])) for j in range(0, 120, 8))+"\n]\n\n"
    return text+"def table : Array (Array Nat) := #["+", ".join("row"+str(i) for i in range(10))+\
        "]\n\nend HeilbronnMixedLayer\n"


def patch_sections():
    originals, changed = slab_sections()
    name = "03-norm-digits.tex"
    text = replace_once(changed[name],
        "M=\\binom{4d-1}{d},\\qquad\n T=\\binom{M}{3}", "T=25(5^{13}+60)/13")
    text = replace_once(text, r"m=17,\qquad A=101,\qquad k=403^{17}",
                        r"m=9,\qquad k=39\cdot35^8")
    text = replace_once(text, "Let $r$ be an odd prime.", "Let $r\\ge37$ be prime.")
    text = replace_once(text, r"Choose an $\mathbb F_r$-basis $\beta_1,\ldots,\beta_d$ of $K$.",
        r"Choose a power basis $1,\vartheta,\ldots,\vartheta^{12}$ of $K/\mathbb F_r$.")
    start = text.index(r"\begin{lemma}\label{norm:decomposition}")
    stop = text.index("For a label", start)
    text = text[:start]+DECOMPOSITION+text[stop:]
    text = replace_once(text, "numbers $d,M,T,k$", "numbers $d,T,k$")
    start = text.index("We use a finite centered-sphere")
    stop = text.index("A random column", start)
    changed[name] = text[:start]+POSITIONS+"\n\n"+text[stop:]
    return "".join("".join(difflib.unified_diff(
        originals[n].splitlines(keepends=True), changed[n].splitlines(keepends=True),
        fromfile="a/build/sections/"+n, tofile="b/build/sections/"+n)) for n in originals)


def main():
    k, q = 39*35**8, (5**13+60)//13
    rho = 498*k+6
    beta = Fraction(83*k+1, 2)
    gamma = Fraction(rho, 2*rho+1)
    alpha = rho+gamma
    eta = 2*gamma/alpha
    path = "certificates/frobenius.json"
    previous = json.loads((ROOT/path).read_text(encoding="utf-8"))
    old_eta = Fraction(int(previous["eta"]["numerator"]), int(previous["eta"]["denominator"]))
    c = {"schema": "heilbronn-rank-five-v1", "upstream_commit": PIN,
         "status": "conditional-on-upstream-estimates",
         "scope": "paper exponent; not the upstream Lean comparator exponent",
         "previous_certificate": path, "previous_sha256": sha256((ROOT/path).read_bytes()).hexdigest(),
         "d": 13, "T": str(25*q), "k": str(k),
         "decomposition": {"patterns": str(5**13), "fixed_patterns": 5,
             "nontrivial_orbit_size": 13, "classes": str(q), "nodes_per_class": 25,
             "antisymmetrization_divisor": 6, "base_characteristic_excludes": [2, 3, 13],
             "formal_base_field_minimum": 25, "retained_manuscript_prime_minimum": 37,
             "formula_source": "https://arxiv.org/abs/1801.00496",
             "row_maps": ["orbit_size / 6 * eval_t", "eval_t", "L(c_t * input)"]},
         "packing": {"half_alphabets_low_first": [10]+[9]*8, "radices_low_first": [39]+[35]*8,
             "energy_index": 119, "squared_norm": 961, "layer_count": str(rows()[9][119]),
             "count_table": rows()},
         "cap": previous["cap"], "scales": previous["scales"], "rho": str(rho),
         "beta": rational(beta), "gamma": rational(gamma), "alpha": rational(alpha), "eta": rational(eta),
         "gain_from_frobenius": rational(eta/old_eta),
         "constraints": {"zero_case_h_powers": [0, -2, -6],
             "collision_r_power": rational(2*gamma-1), "pair_r_power": rational(gamma-6*(k-1))},
         "formal_scope": {"proved": [
             "integral five-term determinant formula and degree-thirteen antisymmetrization",
             "five-letter rotation action, five fixed patterns and exact orbit count",
             "degree-13 field-norm identity with homogeneous polynomial coordinates",
             "nonzero residue exactly for distinct labels for every prime >= 37",
             "exact mixed-sphere energy-119 count and complete finite packing",
             "inherited integer scale inequalities and exponent identity",
             "gain from Frobenius checkpoint greater than 2.34"],
             "written_not_formalized": previous["formal_scope"]["written_not_formalized"]},
         "parameter_choice": "explicit feasible witness; no optimality claim"}
    for path, text in [("certificates/rankfive.json", json.dumps(c, indent=2)+"\n"),
                       ("patches/rank-five.patch", patch_sections()),
                       ("lean/MixedLayerData.lean", table_source(rows()))]:
        (ROOT/path).write_text(text, encoding="utf-8", newline="\n")
    print("Generated rank-five certificate, mixed-layer table and source patch.")


if __name__ == "__main__":
    main()
