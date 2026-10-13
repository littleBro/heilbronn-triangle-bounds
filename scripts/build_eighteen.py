"""Generate the 18-form checkpoint, exact layer table, and source patch."""
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
For $d=13$ and prime $r\ge37$ with $r\equiv1\pmod3$, there are
$T=25\cdot18^6=850\,305\,600$ triples of homogeneous degree-$13$
polynomials over $\mathbb F_r$ (allowing zero) satisfying
\begin{equation}\label{norm:determinant-sum}
 \mathcal N(X^{(1)},X^{(2)},X^{(3)})
 =\sum_{a=0}^{T-1}\det(f_{ia}(X^{(j)}))_{i,j=1}^3.
\end{equation}
\end{lemma}
\begin{proof}
Choose $u\in\mathbb F_r$ with $u^2-u+1=0$. Such a root exists:
Cauchy's theorem gives an element $z$ of order three in $\mathbb F_r^*$,
and $u=-z$ works. Write $v=1-u$. The eighteen forms below are the
Conner--Gesmundo--Landsberg--Ventura decomposition,
arXiv:1909.04785, Theorem 4.1, with the second coefficient column
multiplied by three. For each row permutation $\sigma$, the three
listed coefficient vectors $c$ define $h(x,y)=\sum_i c_i x_{\sigma(i)}y_i$:
\[
\begin{array}{c|ccc}
\sigma & c^{(1)} & c^{(2)} & c^{(3)}\\\hline
(1,2,3)&(-u,-1,v)&(-v,-1,u)&(-v,v,v)\\
(1,3,2)&(-1,-u,-v)&(v,-u,1)&(u,-u,-u)\\
(2,1,3)&(-u,v,1)&(-v,v,-v)&(-v,u,1)\\
(3,1,2)&(-1,-u,v)&(-1,-v,u)&(-1,1,-1)\\
(2,3,1)&(-1,-1,1)&(v,u,1)&(u,v,1)\\
(3,2,1)&(1,-u,v)&(-v,-v,v)&(1,-v,u)
\end{array}
\]
Direct polynomial calculation modulo $u^2-u+1$ gives
\[
 3\det A\det B=\sum_{t=1}^{18}\prod_{j=1}^3
 h_t(A_{\cdot j},B_{\cdot j}).
\]
Lean proves this identity over every commutative ring containing such
a root; the factor is three. The same form occurs in all three columns.
Enumerate the thirteen conjugates as one singleton $g_0$ and six
pairs $(a_v,b_v)$. For $w\in\{1,\ldots,18\}^6$ put
\[
 H_w(X)=\prod_{v=1}^6h_{w_v}(a_v(Z(X)),b_v(Z(X))),\qquad
 F_{iw}(X)=g_0(Z_i(X))H_w(X).
\]
Column scaling gives $3^6\mathcal N=\sum_w\det(F_{iw}(X^{(j)}))$;
each coordinate is homogeneous of degree thirteen.
Apply the power-basis constant-coordinate functional $\ell$, which
fixes $\mathbb F_r$. Interpolation at $25$ distinct nodes gives
$\ell(xyz)=\sum_s\widehat x(s)\widehat y(s)\ell(c_sz)$.
Thus the rows $3^{-6}\widehat F_{1w}(s)$, $\widehat F_{2w}(s)$,
$\ell(c_sF_{3w})$ give $25\cdot18^6$ base-field determinants.
This descent excludes characteristic three; the root condition must
not be dropped. Lean also proves homogeneity and the nonzero criterion
for distinct Vandermonde labels.
\end{proof}

"""

POSITIONS = r"""Use eleven coordinates with half-alphabets
$(5,5,5,5,4,4,4,4,4,4,4)$ and radices $b_j=4A_j-1$. Put
\[
 u(x)=\sum_jx_j\prod_{h<j}b_h,\qquad
 k=19^4\cdot15^7=22\,266\,564\,609\,375.
\]
Writing $y_j=2x_j-(2A_j-1)$, the energy layer
$\sum_j(y_j^2-1)/8=32$ has exactly
\[
 [z^{32}]\left(2\sum_{a=0}^4z^{a(a+1)/2}\right)^4
 \left(2\sum_{a=0}^3z^{a(a+1)/2}\right)^7
 =872\,130\,560>T
\]
words, all of squared norm $11+8\cdot32=267$.
Eleven transitions of the exact counting recurrence are kernel-checked.
Choose $T$ distinct words and put $v(x)=k-1-2u(x)$. Digit sums are
below their radices, so encoded midpoints are coordinatewise midpoints.
Equal squared norms force equality. Therefore both position maps are
injective, take values in $[0,k)$, and satisfy
\[
 u(x)+u(y)+v(z)=k-1\quad\Longleftrightarrow\quad x=y=z.
\]
Lean proves this complete finite packing; no optimality is claimed.
Enumerate the selected words by $0\le a<T$ and set
\begin{equation}\label{norm:positions}
 i_a=j_a=u(x(a)),\qquad \ell_a=v(x(a)).
\end{equation}
The matching property used below is
\begin{equation}\label{norm:matching}
 i_a+j_{a'}+\ell_{a''}=k-1\quad\Longleftrightarrow\quad a=a'=a''.
\end{equation}
"""

PRIME_TRANSFER = r"""For the final label prime, use the prime number theorem in the
fixed progression $1\pmod3$: $\pi(x;3,1)\sim x/(2\log x)$.
See NIST DLMF, Section 27.11, final paragraph,
\url{https://dlmf.nist.gov/27.11}.
It implies $\pi(2m;3,1)-\pi(m;3,1)\sim m/(2\log m)>0$.
Thus for every sufficiently large $m$ there is a prime $r\equiv1\pmod3$
with $m<r\le2m$. This is an unconditional standard theorem, used here
in writing and not formalized in Lean. Mere infinitude of these primes
would not justify the bounded-ratio interpolation step.
The auxiliary primes $B$ and $q$ still use the ordinary Bertrand lemma.
"""


def rows():
    table = [[1]+[0]*32]
    for a in [4]*7+[5]*4:
        table.append([sum(2*table[-1][e-j*(j+1)//2] for j in range(a)
                          if j*(j+1)//2 <= e) for e in range(33)])
    return table


def table_source(table):
    text = "import Lean\n\nnamespace HeilbronnEighteenLayer\n\n"
    for i, row in enumerate(table):
        text += f"def row{i} : Array Nat := #[\n"
        text += ",\n".join("  "+", ".join(map(str, row[j:j+8])) for j in range(0, 33, 8))+"\n]\n\n"
    return text+"end HeilbronnEighteenLayer\n"


def norm_sections():
    originals, changed = slab_sections()
    name = "03-norm-digits.tex"
    text = replace_once(changed[name],
        "M=\\binom{4d-1}{d},\\qquad\n T=\\binom{M}{3}", "T=25\\cdot18^6")
    text = replace_once(text, r"m=17,\qquad A=101,\qquad k=403^{17}",
                        r"m=11,\qquad k=15^7\cdot19^4")
    text = replace_once(text, "Let $r$ be an odd prime.",
                        "Let $r\\ge37$ be prime with $r\\equiv1\\pmod3$.")
    text = replace_once(text, r"Choose an $\mathbb F_r$-basis $\beta_1,\ldots,\beta_d$ of $K$.",
        r"Choose a power basis $\beta_\nu=\vartheta^{\nu-1}$, $1\le\nu\le13$, of $K/\mathbb F_r$.")
    start, stop = text.index(r"\begin{lemma}\label{norm:decomposition}"), text.index("For a label")
    text = text[:start]+DECOMPOSITION+text[stop:]
    text = replace_once(text, "numbers $d,M,T,k$", "numbers $d,T,k$")
    start, stop = text.index("We use a finite centered-sphere"), text.index("A random column")
    changed[name] = text[:start]+POSITIONS+"\n\n"+text[stop:]
    name = "08-alteration.tex"
    changed[name] = replace_once(changed[name],
        "Lemma~\\ref{norm:prime-interval} supplies a prime $r$ with $m<r\\le2m$.", PRIME_TRANSFER)
    changed[name] = replace_once(changed[name], "for every sufficiently large prime $r$.",
        r"for every sufficiently large prime $r\equiv1\pmod3$.")
    return originals, changed


def patch_sections():
    originals, changed = norm_sections()
    return "".join("".join(difflib.unified_diff(
        originals[n].splitlines(keepends=True), changed[n].splitlines(keepends=True),
        fromfile="a/build/sections/"+n, tofile="b/build/sections/"+n)) for n in originals)


def main():
    k, term_count = 15**7*19**4, 25*18**6
    rho = 498*k+6
    beta, gamma = Fraction(83*k+1, 2), Fraction(rho, 2*rho+1)
    alpha = rho+gamma
    eta = 2*gamma/alpha
    path = "certificates/paired.json"
    previous = json.loads((ROOT/path).read_text(encoding="utf-8"))
    old_eta = Fraction(int(previous["eta"]["numerator"]), int(previous["eta"]["denominator"]))
    c = {"schema": "heilbronn-eighteen-v1", "upstream_commit": PIN,
         "status": "conditional-on-upstream-estimates", "scope": previous["scope"],
         "previous_certificate": path, "previous_sha256": sha256((ROOT/path).read_bytes()).hexdigest(),
         "d": 13, "T": str(term_count), "k": str(k),
         "decomposition": {"pairs": 6, "unpaired_conjugates": 1, "terms_per_pair": 18,
             "extension_determinants": str(18**6), "nodes_per_term": 25,
             "pair_identity_multiplier": 3, "normalization_denominator": 3**6,
             "root_equation": "u^2-u+1=0", "base_characteristic_excludes": [3],
             "formal_base_field_minimum": 25, "manuscript_prime_minimum": 37,
             "manuscript_prime_residue": 1, "manuscript_prime_modulus": 3,
             "formula_source": "https://arxiv.org/abs/1909.04785",
             "row_maps": ["3^(-6) * eval_t", "eval_t", "constantCoord(c_t * input)"]},
         "packing": {"half_alphabets_low_first": [5]*4+[4]*7,
             "radices_low_first": [19]*4+[15]*7, "energy_index": 32,
             "squared_norm": 267, "layer_count": str(rows()[11][32]), "count_table": rows()},
         "prime_transfer": {"progression": "1 mod 3", "interval": "m < r <= 2m for all sufficiently large m",
             "theorem": "prime number theorem in a fixed arithmetic progression",
             "source": "https://dlmf.nist.gov/27.11", "lean_formalized": False},
         "cap": previous["cap"], "scales": previous["scales"], "rho": str(rho),
         "beta": rational(beta), "gamma": rational(gamma), "alpha": rational(alpha), "eta": rational(eta),
         "gain_from_paired": rational(eta/old_eta),
         "constraints": {"zero_case_h_powers": [0, -2, -6],
             "collision_r_power": rational(2*gamma-1), "pair_r_power": rational(gamma-6*(k-1))},
         "formal_scope": {"proved": [
             "18-form identity over a commutative ring with u^2-u+1=0, with multiplier 3",
             "six pairs and one unpaired determinant, normalization 3^6",
             "degree-13 field-norm identity with homogeneous polynomial coordinates",
             "root existence and distinct-label criterion for primes >= 37 congruent to 1 mod 3",
             "exact energy-32 layer and complete mixed-radix packing",
             "inherited integer scale inequalities and exponent identity",
             "gain from paired checkpoint greater than 2.18"],
             "written_not_formalized": previous["formal_scope"]["written_not_formalized"]+
                 ["prime number theorem in the progression 1 mod 3 and its interpolation consequence"]},
         "parameter_choice": "explicit feasible witness; no optimality claim"}
    for path, text in [("certificates/eighteen.json", json.dumps(c, indent=2)+"\n"),
                       ("patches/eighteen-norm.patch", patch_sections()),
                       ("lean/EighteenLayerData.lean", table_source(rows()))]:
        (ROOT/path).write_text(text, encoding="utf-8", newline="\n")
    print("Generated eighteen-form certificate, mixed-layer table and source patch.")


if __name__ == "__main__":
    main()
