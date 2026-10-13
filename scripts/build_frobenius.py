"""Collect signed norm terms into Galois orbits before bilinear descent."""
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import difflib
import json

from build_bilinear import POSITIONS as PREVIOUS_POSITIONS, rows
from build_slab import slab_sections
from build_sphere import PIN, rational
from build_tuned import replace_once

ROOT = Path(__file__).resolve().parents[1]

DECOMPOSITION = r"""\begin{lemma}\label{norm:decomposition}
For $d=13$ there exist homogeneous degree-$d$ polynomials
$f_{ia}\in\mathbb F_r[X]$ (allowing zero), for $1\le i\le3$ and
$0\le a<T=25(6^{12}+12)/13=4\,186\,119\,900$, such that
\begin{equation}\label{norm:determinant-sum}
 \mathcal N(X^{(1)},X^{(2)},X^{(3)})
 =\sum_{a=0}^{T-1}\det\bigl(f_{ia}(X^{(j)})\bigr)_{1\le i,j\le3}.
\end{equation}
\end{lemma}
\begin{proof}
Let $G=\operatorname{Gal}(K/\mathbb F_r)$, of order $13$, and let
$W=\{w:G\to S_3:w(1)=1\}$. For $w\in W$ set
\[
 F_{i,w}(X)=\prod_{g\in G}g(Z_{w(g)i}(X)),\qquad
 \epsilon_w=\prod_{g\in G}\operatorname{sgn}(w(g)),\qquad
 C_w=\epsilon_w\det(F_{i,w}(X^{(j)}))_{i,j=1}^3.
\]
Automorphisms act on coefficients. The raw determinant product has
permutations $\pi_g$; write $\tau=\pi_1$ and $w(g)=\pi_g\tau^{-1}$.
This is a bijection between raw choices and $(w,\tau)$. As $13$ is
odd, its sign is $\epsilon_w\operatorname{sgn}(\tau)$. Summing first
over $\tau$ gives the exact identity, without division by $6$,
\begin{equation}\label{norm:orbit-decomposition}
 \mathcal N=\sum_{w\in W}C_w,\qquad |W|=6^{12}.
\end{equation}
Act on $W$ by $(a\cdot w)(g)=w(a^{-1}g)w(a^{-1})^{-1}$.
Changing $g$ to $ag$ in the coordinate product permutes its rows by
$w(a^{-1})^{-1}$. Its determinant sign cancels the change in
$\epsilon_w$, so $C_{a\cdot w}=a(C_w)$.

Every orbit has size $1$ or $13$. A fixed pattern satisfies
$w(uv)=w(v)w(u)$, hence $w(g)^{13}=w(g^{13})=1$.
Each element of $S_3$ also has sixth power $1$; it follows that
$w(g)=1$. Thus the constant identity pattern is the unique fixed
pattern, and there are
\[
 Q=1+\frac{6^{12}-1}{13}=167\,444\,796
\]
orbits. For the constant-coordinate functional $\ell:K\to\mathbb F_r$
of the power basis, define
\[
 L(z)=13^{-1}\sum_{a\in G}\ell(a(z)).
\]
Here $13$ is invertible since $r\ge37$ is prime. The linear map $L$
fixes $\mathbb F_r$ and is $G$-invariant. Extend it coefficientwise
to polynomials. Choose one representative $w_q$ of each orbit $q$,
and write $n_q=|q|$. Then
\[
 \mathcal N=\sum_q n_q L(C_{w_q}).
\]

For $x\in K$ let $\widehat x(Y)$ have degree less than $13$ and
$\widehat x(\vartheta)=x$. At the $25$ distinct nodes $t=0,\ldots,24$,
let $L_t(Y)$ be the Lagrange basis and $c_t=L_t(\vartheta)$.
Interpolation of a product of degree at most $24$ gives
\[
 xy=\sum_t\widehat x(t)\widehat y(t)c_t,\qquad
 L(xyz)=\sum_t\widehat x(t)\widehat y(t)L(c_tz).
\]
Expanding the six signed products of a determinant therefore gives
\[
 L(\det M)=\sum_t\det\begin{pmatrix}
 \widehat M_{11}(t)&\widehat M_{12}(t)&\widehat M_{13}(t)\\
 \widehat M_{21}(t)&\widehat M_{22}(t)&\widehat M_{23}(t)\\
 L(c_tM_{31})&L(c_tM_{32})&L(c_tM_{33})
 \end{pmatrix}.
\]
For $a=(q,t)$, take the first-row coordinate to be
$n_q\epsilon_{w_q}\widehat F_{1,w_q}(t,X)$, the second to be
$\widehat F_{2,w_q}(t,X)$, and the third to be $L(c_tF_{3,w_q}(X))$.
These polynomials over $\mathbb F_r$ are homogeneous of degree $13$,
and the displayed identities prove the claim with $25Q$ summands.
The singleton orbit also receives $25$ nodes; any zero terms are retained.
\end{proof}

"""

POSITIONS = (PREVIOUS_POSITIONS.replace("$m=11$", "$m=10$")
    .replace("^{11}", "^{10}").replace("v=0}^{10}", "v=0}^{9}")
    .replace("E(x)=11+", "E(x)=10+").replace("z^{86}", "z^{80}")
    .replace(r"67\,169\,169\,408", r"5\,058\,395\,136")
    .replace(r"T=25\cdot6^{12}=54\,419\,558\,400", r"T=4\,186\,119\,900")
    .replace("e\\le86", "e\\le80").replace("n\\le11", "n\\le10")
    .replace("J(x)=86", "J(x)=80").replace("norm $699$", "norm $650$"))


def patch_sections():
    originals, changed = slab_sections()
    name = "03-norm-digits.tex"
    text = replace_once(changed[name],
        "M=\\binom{4d-1}{d},\\qquad\n T=\\binom{M}{3}", "T=25(6^{12}+12)/13")
    text = replace_once(text, r"m=17,\qquad A=101,\qquad k=403^{17}",
                        r"m=10,\qquad A=7,\qquad k=27^{10}")
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
    changed[name] = text[:start]+POSITIONS+"\n\n"+text[stop:]
    return "".join("".join(difflib.unified_diff(
        originals[name].splitlines(keepends=True), changed[name].splitlines(keepends=True),
        fromfile="a/build/sections/"+name, tofile="b/build/sections/"+name)) for name in originals)


def main():
    k, classes = 27**10, (6**12+12)//13
    rho = 498*k+6
    beta = Fraction(83*k+1, 2)
    gamma = Fraction(rho, 2*rho+1)
    alpha = rho+gamma
    eta = 2*gamma/alpha
    previous_path = "certificates/bilinear.json"
    previous = json.loads((ROOT / previous_path).read_text(encoding="utf-8"))
    previous_eta = Fraction(int(previous["eta"]["numerator"]), int(previous["eta"]["denominator"]))
    certificate = {
        "schema": "heilbronn-frobenius-orbits-v1", "upstream_commit": PIN,
        "status": "conditional-on-upstream-estimates",
        "scope": "paper exponent; not the upstream Lean comparator exponent",
        "previous_certificate": previous_path,
        "previous_sha256": sha256((ROOT / previous_path).read_bytes()).hexdigest(),
        "d": 13, "T": str(25*classes), "k": str(k),
        "decomposition": {"normalized_patterns": str(6**12), "fixed_patterns": 1,
            "nontrivial_orbit_size": 13, "classes": str(classes), "nodes_per_class": 25,
            "singleton_uses_full_descent": True, "base_characteristic_not": 13,
            "formal_base_field_minimum": 25, "retained_manuscript_prime_minimum": 37,
            "projection": "L(z) = sum_a ell(a(z)) / 13",
            "row_maps": ["orbit_size * epsilon_w * eval_t", "eval_t", "L(c_t * input)"]},
        "packing": {"m": 10, "A": 7, "s": 14, "b": 27, "energy_index": 80,
            "squared_norm": 650, "layer_count": str(rows()[10][80]),
            "digit_energies": [0, 1, 3, 6, 10, 15, 21], "multiplicity": 2,
            "count_table_source": "certificates/bilinear.json"},
        "cap": previous["cap"], "scales": previous["scales"],
        "rho": str(rho), "beta": rational(beta), "gamma": rational(gamma),
        "alpha": rational(alpha), "eta": rational(eta), "gain_from_bilinear": rational(eta/previous_eta),
        "constraints": {"zero_case_h_powers": [0, -2, -6],
            "collision_r_power": rational(2*gamma-1), "pair_r_power": rational(gamma-6*(k-1))},
        "formal_scope": {"proved": [
            "normalized permutation action, unique fixed pattern and exact orbit count",
            "signed field-norm equivariance and invariant projection fixing the base field",
            "orbit-weighted degree-13 field-norm identity with homogeneous polynomial coordinates",
            "nonzero residue exactly for distinct labels for every prime >= 37",
            "exact energy-80 layer count from the checked recurrence table",
            "complete finite packing for T = 4186119900 and k = 27^10",
            "inherited integer scale inequalities and exponent identity",
            "26.99 < gain from bilinear checkpoint < 27"],
            "written_not_formalized": previous["formal_scope"]["written_not_formalized"]},
        "parameter_choice": "explicit feasible witness; no optimality claim",
    }
    for path, text in [
        ("certificates/frobenius.json", json.dumps(certificate, indent=2)+"\n"),
        ("patches/frobenius-orbits.patch", patch_sections()),
    ]:
        (ROOT / path).write_text(text, encoding="utf-8", newline="\n")
    print("Generated Frobenius-orbit certificate and source patch.")


if __name__ == "__main__":
    main()
