"""Generate the paired-determinant certificate, count table and manuscript patch."""
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
For $d=13$ there are $T=25\cdot20^6=1\,600\,000\,000$ triples of
homogeneous degree-$13$ polynomials $f_{ia}\in\mathbb F_r[X]$ (allowing zero),
such that
\begin{equation}\label{norm:determinant-sum}
 \mathcal N(X^{(1)},X^{(2)},X^{(3)})
 =\sum_{a=0}^{T-1}\det(f_{ia}(X^{(j)}))_{i,j=1}^3.
\end{equation}
\end{lemma}
\begin{proof}
Start with the five-term integral determinant formula of Krishna--Makam,
arXiv:1801.00496, Section 3.1. Its coefficient arrays $c_{tir}$ satisfy
$\det Z=\sum_{t=0}^4\prod_{i=1}^3\sum_r c_{tir}Z_{ri}$ and are
\[
\begin{array}{c|ccc}
t&\sum_r c_{t1r}Z_r&\sum_r c_{t2r}Z_r&\sum_r c_{t3r}Z_r\\\hline
0&Z_2+Z_3&Z_1&Z_2\\
1&-Z_1-Z_3&Z_2&Z_1\\
2&-Z_2&Z_1+Z_3&Z_2+Z_3\\
3&Z_2-Z_1&Z_3&Z_1+Z_2+Z_3\\
4&Z_1&Z_2+Z_3&Z_1+Z_3
\end{array}
\]
Let $E=\{(1,1,1),(1,-1,-1),(-1,1,-1),(-1,-1,1)\}$ and put
\[
 h_{t,\epsilon}(x,y)=\sum_{i,r}\epsilon_i c_{tir}x_ry_i.
\]
Polarization, $24abc=\sum_{\epsilon\in E}(\epsilon_1a+
\epsilon_2b+\epsilon_3c)^3$, gives the integral identity
\[
 4\det A\det B=\sum_{t,\epsilon}\prod_{j=1}^3
                   h_{t,\epsilon}(A_{\cdot j},B_{\cdot j}).
\]
Indeed compare the coefficient of $z_1z_2z_3$ in the five-term formula
for $\det(A\operatorname{diag}(z)B^{\mathsf T})$. Equivalently the displayed
identity can be checked directly over the integers; Lean proves it over
every commutative ring. The identical form in all three columns is essential.

Enumerate the thirteen conjugates as one singleton $g_0$ and six pairs
$(a_v,b_v)$. Write $M_g=(g(Z_i(X^{(j)})))_{i,j}$. For each of the $20^6$
choices $w=((t_v,\epsilon_v))_{v=1}^6$, set
\[
 H_w(X)=\prod_{v=1}^6h_{t_v,\epsilon_v}(a_v(Z(X)),b_v(Z(X))),
 \qquad F_{iw}(X)=g_0(Z_i(X))H_w(X).
\]
Every $F_{iw}$ is homogeneous of degree $13$, and column scaling gives
\[
 4^6\mathcal N=\sum_w\det(F_{iw}(X^{(j)}))_{i,j}.
\]
There is no additional factor of five for the unpaired determinant.
Let $\ell:K\to\mathbb F_r$ be the constant-coordinate functional of a
power basis, so that $\ell$ fixes the base field. At $25$ distinct nodes
$s=0,\ldots,24$, polynomial interpolation gives
$xy=\sum_s\widehat x(s)\widehat y(s)c_s$ for degree-less-than-$13$
representatives. Thus $\ell(xyz)=\sum_s\widehat x(s)\widehat y(s)\ell(c_sz)$.
Apply this identity to each determinant, using rows
$4^{-6}\widehat F_{1w}(s)$, $\widehat F_{2w}(s)$, and $\ell(c_sF_{3w})$.
This gives $25\cdot20^6$ base-field determinants. The only characteristic
restriction of this construction is that $2$ is invertible; prime $r\ge37$
also supplies the interpolation nodes. No Galois-orbit division is used.
\end{proof}

"""

POSITIONS = r"""Use ten coordinates with half-alphabets
$(A_0,\ldots,A_9)=(7,6,\ldots,6)$: one alphabet has $14$ digits and nine
have $12$. Set $b_j=4A_j-1$ and
\[
 u(x)=\sum_jx_j\prod_{h<j}b_h,\qquad
 k=\prod_jb_j=27\cdot23^9=48\,631\,121\,859\,501.
\]
With $y_j=2x_j-(2A_j-1)$, take the layer
$J=\sum_j(y_j^2-1)/8=59$. Its exact cardinality is
\[
 [z^{59}]\left(2\sum_{a=0}^6z^{a(a+1)/2}\right)
 \left(2\sum_{a=0}^5z^{a(a+1)/2}\right)^9
 =1\,641\,775\,104>T.
\]
Ten transitions of the recurrence $C_{A::S}(e)=
2\sum_{a=0}^{A-1}C_S(e-a(a+1)/2)$, truncated at $e=59$, are checked
by the Lean kernel. Negative indices are zero and $C_{[]}(e)=\mathbf1_{e=0}$.
The layer has squared norm $10+8\cdot59=482$. Select $T$ distinct words
and put $v(x)=k-1-2u(x)$. Digit sums are below their respective radices,
so an encoded midpoint is a coordinatewise midpoint. Equal squared norms
force all three words to coincide. Therefore
\[
 0\le u(x),v(x)<k,\qquad
 u(x)+u(y)+v(z)=k-1\quad\Longleftrightarrow\quad x=y=z.
\]
Both position maps are injective. Lean proves selection, bounds, injectivity
and matching. Enumerate the selected words by $0\le a<T$ and denote their
positions by $u_a,v_a$. This is a feasible witness, with no optimality claim.
"""


def rows():
    table = [[1]+[0]*59]
    for a in [6]*9+[7]:
        table.append([sum(2*table[-1][e-j*(j+1)//2] for j in range(a)
                          if j*(j+1)//2 <= e) for e in range(60)])
    return table


def table_source(table):
    text = "import Lean\n\nnamespace HeilbronnPairedLayer\n\n"
    for i, row in enumerate(table):
        text += f"def row{i} : Array Nat := #[\n"
        text += ",\n".join("  "+", ".join(map(str, row[j:j+8])) for j in range(0, 60, 8))+"\n]\n\n"
    return text+"def table : Array (Array Nat) := #["+", ".join("row"+str(i) for i in range(11))+\
        "]\n\nend HeilbronnPairedLayer\n"


def patch_sections():
    originals, changed = slab_sections()
    name = "03-norm-digits.tex"
    text = replace_once(changed[name],
        "M=\\binom{4d-1}{d},\\qquad\n T=\\binom{M}{3}", "T=25\\cdot20^6")
    text = replace_once(text, r"m=17,\qquad A=101,\qquad k=403^{17}",
                        r"m=10,\qquad k=27\cdot23^9")
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
    k = 27*23**9
    rho = 498*k+6
    beta = Fraction(83*k+1, 2)
    gamma = Fraction(rho, 2*rho+1)
    alpha = rho+gamma
    eta = 2*gamma/alpha
    path = "certificates/rankfive.json"
    previous = json.loads((ROOT/path).read_text(encoding="utf-8"))
    old_eta = Fraction(int(previous["eta"]["numerator"]), int(previous["eta"]["denominator"]))
    c = {"schema": "heilbronn-paired-v1", "upstream_commit": PIN,
         "status": "conditional-on-upstream-estimates", "scope": previous["scope"],
         "previous_certificate": path, "previous_sha256": sha256((ROOT/path).read_bytes()).hexdigest(),
         "d": 13, "T": str(25*20**6), "k": str(k),
         "decomposition": {"pairs": 6, "unpaired_conjugates": 1, "terms_per_pair": 20,
             "extension_determinants": str(20**6), "nodes_per_term": 25,
             "pair_identity_multiplier": 4, "normalization_denominator": 4**6,
             "base_characteristic_excludes": [2], "formal_base_field_minimum": 25,
             "retained_manuscript_prime_minimum": 37,
             "formula_source": "https://arxiv.org/abs/1801.00496",
             "row_maps": ["4^(-6) * eval_t", "eval_t", "constantCoord(c_t * input)"]},
         "packing": {"half_alphabets_low_first": [7]+[6]*9, "radices_low_first": [27]+[23]*9,
             "energy_index": 59, "squared_norm": 482, "layer_count": str(rows()[10][59]),
             "count_table": rows()},
         "cap": previous["cap"], "scales": previous["scales"], "rho": str(rho),
         "beta": rational(beta), "gamma": rational(gamma), "alpha": rational(alpha), "eta": rational(eta),
         "gain_from_rankfive": rational(eta/old_eta),
         "constraints": {"zero_case_h_powers": [0, -2, -6],
             "collision_r_power": rational(2*gamma-1), "pair_r_power": rational(gamma-6*(k-1))},
         "formal_scope": {"proved": [
             "integral 20-term symmetric identity for a pair of determinants",
             "six paired factors and one unpaired determinant, with normalization 4^6",
             "degree-13 field-norm identity with homogeneous polynomial coordinates",
             "nonzero residue exactly for distinct labels for every prime >= 37",
             "exact mixed-sphere energy-59 count and complete finite packing",
             "inherited integer scale inequalities and exponent identity",
             "gain from rank-five checkpoint greater than 1.80"],
             "written_not_formalized": previous["formal_scope"]["written_not_formalized"]},
         "parameter_choice": "explicit feasible witness; no optimality claim"}
    for path, text in [("certificates/paired.json", json.dumps(c, indent=2)+"\n"),
                       ("patches/paired-norm.patch", patch_sections()),
                       ("lean/PairedLayerData.lean", table_source(rows()))]:
        (ROOT/path).write_text(text, encoding="utf-8", newline="\n")
    print("Generated paired certificate, mixed-layer table and source patch.")


if __name__ == "__main__":
    main()
