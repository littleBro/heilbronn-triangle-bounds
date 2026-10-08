"""Compress the norm decomposition before applying the existing sphere packing."""
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import difflib
import json

from build_sphere import NEW_POSITIONS, PIN, rational
from build_slab import slab_sections
from build_tuned import replace_once

ROOT = Path(__file__).resolve().parents[1]

DECOMPOSITION = r"""\begin{lemma}\label{norm:decomposition}
There exist homogeneous degree-$d$ polynomials $f_{ia}\in\mathbb F_r[X]$
(allowing the zero polynomial), for $1\le i\le3$ and
$0\le a<T=(3d-2)6^{d-1}$, such that
\begin{equation}\label{norm:determinant-sum}
 \mathcal N(X^{(1)},X^{(2)},X^{(3)})
 =\sum_{a=0}^{T-1}\det\bigl(f_{ia}(X^{(j)})\bigr)_{1\le i,j\le3}.
\end{equation}
\end{lemma}
\begin{proof}
Write $Z_i(X)$ for the $i$th coordinate of $Z(X)$ and let $S_3$ act
by mapping column indices to row indices. For
$\rho=(\rho_1,\ldots,\rho_{d-1})\in S_3^{d-1}$, set $\rho_0=\mathrm{id}$ and
\[
 F_{i,\rho}(X)=\prod_{v=0}^{d-1}\sigma^v Z_{\rho_v(i)}(X),\qquad
 \epsilon_\rho=\prod_{v=1}^{d-1}\operatorname{sgn}(\rho_v).
\]
Here $\sigma$ acts only on coefficients. Expansion and regrouping give
\begin{equation}\label{norm:orbit-decomposition}
 \mathcal N=\sum_{\rho\in S_3^{d-1}}\epsilon_\rho
       \det\bigl(F_{i,\rho}(X^{(j)})\bigr)_{i,j=1}^3.
\end{equation}
To verify this without division by $6$, a term in the raw product
expansion has permutations $(\pi_0,\ldots,\pi_{d-1})$. Put
$\tau=\pi_0$ and $\rho_v=\pi_v\tau^{-1}$. This is a bijection with
$(\tau,\rho)$, with inverse $\pi_v=\rho_v\tau$.
Its sign is $(\operatorname{sgn}\tau)^d\epsilon_\rho
=\operatorname{sgn}(\tau)\epsilon_\rho$, since $d$ is odd.
For fixed $\rho$, summing over $\tau$ is exactly the determinant in
\eqref{norm:orbit-decomposition}. There are $6^{d-1}$ such terms over $K$.

They must still be expressed over $\mathbb F_r$. In the power basis
$1,\vartheta,\ldots,\vartheta^{d-1}$, write
$F_{i,\rho}(X)=\widehat F_{i,\rho}(\vartheta,X)$ with
$\deg_Y\widehat F_{i,\rho}(Y,X)<d$. Its coefficients are in
$\mathbb F_r[X]$ and remain homogeneous of degree $d$ in $X$.
The polynomial
\[
 H_\rho(Y)=\det\bigl(\widehat F_{i,\rho}(Y,X^{(j)})\bigr)_{i,j=1}^3
\]
has degree at most $3d-3$ in $Y$. Let $\ell:K\to\mathbb F_r$ select
the coefficient of $1$ in the power basis, extending coefficientwise
to polynomials in the $X$ variables. In particular $\ell(c)=c$ for
$c\in\mathbb F_r$.

Use the $3d-2$ distinct nodes $t=0,\ldots,3d-3$ in $\mathbb F_r$;
they exist because $r\ge37=3d-2$. Let
\[
 L_t(Y)=\prod_{\substack{0\le u\le3d-3\\u\ne t}}\frac{Y-u}{t-u},
 \qquad \lambda_t=\ell(L_t(\vartheta)).
\]
Polynomial interpolation, followed by this linear projection, gives
\[
 \ell(H_\rho(\vartheta))
 =\sum_{t=0}^{3d-3}\lambda_t
       \det\bigl(\widehat F_{i,\rho}(t,X^{(j)})\bigr)_{i,j=1}^3.
\]
This projects the whole determinant; it does not project its entries.
Since $\mathcal N$ already has coefficients in $\mathbb F_r$,
applying $\ell$ to \eqref{norm:orbit-decomposition} leaves its left
side unchanged. For the index $a=(\rho,t)$, take
\[
 f_{1a}=\epsilon_\rho\lambda_t\widehat F_{1,\rho}(t,X),\quad
 f_{2a}=\widehat F_{2,\rho}(t,X),\quad
 f_{3a}=\widehat F_{3,\rho}(t,X).
\]
This proves the claimed identity with $(3d-2)6^{d-1}$ summands.
All coefficients and interpolation weights may depend on $r$; their
number and polynomial degree do not. Zero terms need not be removed.
\end{proof}

"""


def patch_sections():
    originals, changed = slab_sections()
    name = "03-norm-digits.tex"
    text = replace_once(changed[name],
        "M=\\binom{4d-1}{d},\\qquad\n T=\\binom{M}{3}", "T=(3d-2)6^{d-1}")
    text = replace_once(text, r"m=17,\qquad A=101,\qquad k=403^{17}",
                        r"m=10,\qquad A=12,\qquad k=47^{10}")
    text = replace_once(text, "Let $r$ be an odd prime.", "Let $r\\ge37$ be prime.")
    text = replace_once(text,
        r"Choose an $\mathbb F_r$-basis $\beta_1,\ldots,\beta_d$ of $K$.",
        r"""Choose $\vartheta\in K\setminus\mathbb F_r$. Since $d=13$ is prime,
its Frobenius orbit has length $d$, so its minimal polynomial $P$ has
degree $d$ and $K=\mathbb F_r[\vartheta]\cong\mathbb F_r[Y]/(P)$.
Use the basis $\beta_\nu=\vartheta^{\nu-1}$, $1\le\nu\le d$.""")
    start = text.index(r"\begin{lemma}\label{norm:decomposition}")
    stop = text.index("For a label", start)
    text = text[:start]+DECOMPOSITION+text[stop:]
    text = replace_once(text, "numbers $d,M,T,k$", "numbers $d,T,k$")
    start = text.index("We use a finite centered-sphere")
    stop = text.index("A random column", start)
    positions = (NEW_POSITIONS.replace("20006", "24").replace("40011", "47")
                 .replace("1450725088", "661").replace("^{29}", "^{10}"))
    text = text[:start]+positions+"\n\n"+text[stop:]
    changed[name] = text
    return "".join("".join(difflib.unified_diff(
        originals[name].splitlines(keepends=True), changed[name].splitlines(keepends=True),
        fromfile="a/build/sections/"+name, tofile="b/build/sections/"+name))
        for name in originals)


def main():
    d, m, A = 13, 10, 12
    orbits, nodes = 6**(d-1), 3*d-2
    T = nodes*orbits
    k = (4*A-1)**m
    Q = m*A*(A-1)//2+1
    rho = 498*k+6
    beta = Fraction(83*k+1, 2)
    gamma = Fraction(rho, 2*rho+1)
    alpha = rho+gamma
    eta = 2*gamma/alpha
    previous_path = "certificates/central.json"
    previous = json.loads((ROOT / previous_path).read_text(encoding="utf-8"))
    previous_eta = Fraction(int(previous["eta"]["numerator"]), int(previous["eta"]["denominator"]))
    certificate = {
        "schema": "heilbronn-norm-compression-v1", "upstream_commit": PIN,
        "status": "conditional-on-upstream-estimates",
        "scope": "paper exponent; not the upstream Lean comparator exponent",
        "previous_certificate": previous_path,
        "previous_sha256": sha256((ROOT / previous_path).read_bytes()).hexdigest(),
        "d": d, "T": str(T),
        "decomposition": {"extension_field_terms": str(orbits),
            "representative_degree_max": d-1, "determinant_degree_max": 3*d-3,
            "interpolation_nodes": nodes, "prime_minimum": 37,
            "preserved_interface": "homogeneous degree-d polynomials over F_r; exact norm identity",
            "proof_status": "Lean proofs of norm regrouping, interpolation descent, homogeneous coordinates and distinct labels"},
        "packing": {"m": m, "A": A, "s": 2*A, "b": 4*A-1,
            "layers": Q, "word_count": str((2*A)**m), "required_words": str(T*Q)},
        "k": str(k), "cap": previous["cap"], "scales": previous["scales"],
        "rho": str(rho), "beta": rational(beta), "gamma": rational(gamma),
        "alpha": rational(alpha), "eta": rational(eta), "gain_from_central": rational(eta/previous_eta),
        "constraints": {"zero_case_h_powers": [0, -2, -6],
            "collision_r_power": rational(2*gamma-1),
            "pair_r_power": rational(gamma-6*(k-1))},
        "formal_scope": {
            "proved": ["permutation composition, exhaustive list, signs and normalization bijection",
                "sign identity for 13 determinant factors",
                "universal field-norm decomposition for degree-13 finite extensions",
                "37-node interpolation descent and homogeneous degree-13 polynomial coordinates",
                "nonzero norm residue exactly for distinct labels for every prime >= 37",
                "complete finite packing for T = 37*6^12, k = 47^10",
                "inherited integer scale inequalities and exponent identity",
                "10^27 < gain from central < 2*10^27"],
            "written_not_formalized": ["slab cap geometry and short-relation exclusion",
                "lattice, orbit and weighted counting estimates",
                "probability, asymptotic deletion and interpolation"]},
        "parameter_choice": "explicit feasible witness; no optimality claim",
    }
    (ROOT / "certificates/norm.json").write_text(
        json.dumps(certificate, indent=2)+"\n", encoding="utf-8", newline="\n")
    (ROOT / "patches/norm-compression.patch").write_text(
        patch_sections(), encoding="utf-8", newline="\n")
    print("Generated certificates/norm.json and patches/norm-compression.patch")


if __name__ == "__main__":
    main()
