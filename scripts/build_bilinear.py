"""Twenty-five-node descent and an exactly counted sphere layer."""
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import difflib
import json

from build_norm import DECOMPOSITION as PREVIOUS_DECOMPOSITION
from build_slab import slab_sections
from build_sphere import NEW_POSITIONS, PIN, rational
from build_tuned import replace_once

ROOT = Path(__file__).resolve().parents[1]

DECOMPOSITION = PREVIOUS_DECOMPOSITION.split("They must still")[0].replace("(3d-2)", "(2d-1)")+r"""For descent, use the power basis $1,\vartheta,\ldots,\vartheta^{d-1}$.
For $x\in K$, let $\widehat x(Y)$ be its representative of degree less
than $d$, and let $\ell:K\to\mathbb F_r$ select its constant coordinate.
Choose $2d-1$ distinct nodes $t=0,\ldots,2d-2$, with Lagrange
polynomials $L_t(Y)$, and put $c_t=L_t(\vartheta)$. These nodes exist
under the retained assumption $r\ge37$, since $2d-1=25$.
Interpolation of $\widehat x(Y)\widehat y(Y)$, whose degree is at most
$2d-2$, gives
\[
 xy=\sum_{t=0}^{2d-2}\widehat x(t)\widehat y(t)c_t,
 \qquad
 \ell(xyz)=\sum_{t=0}^{2d-2}\widehat x(t)\widehat y(t)\ell(c_tz).
\]
Apply this identity to each of the six signed products in a determinant.
The same three linear maps are used in every product, so
\[
 \ell(\det M)=\sum_{t=0}^{2d-2}
 \det\begin{pmatrix}
  \widehat M_{11}(t)&\widehat M_{12}(t)&\widehat M_{13}(t)\\
  \widehat M_{21}(t)&\widehat M_{22}(t)&\widehat M_{23}(t)\\
  \ell(c_tM_{31})&\ell(c_tM_{32})&\ell(c_tM_{33})
 \end{pmatrix}.
\]
In particular, the third row uses a different linear functional.
For polynomial entries, extend these maps coefficientwise. For the
index $a=(\rho,t)$, set
\[
 f_{1a}=\epsilon_\rho\widehat F_{1,\rho}(t,X),\qquad
 f_{2a}=\widehat F_{2,\rho}(t,X),\qquad
 f_{3a}=\ell(c_tF_{3,\rho}(X)).
\]
All three are homogeneous of degree $d$ over $\mathbb F_r$.
Since $\ell$ fixes the base field, applying it to
\eqref{norm:orbit-decomposition} proves the claimed norm identity
with $(2d-1)6^{d-1}$ summands. Zero terms may be retained.
\end{proof}

"""

POSITIONS = r"""Use a finite centered-sphere form of Behrend's construction with
$m=11$, $s=2A=14$, $b=2s-1=27$. For a word $x$ in
$\{0,\ldots,13\}^{11}$, put
\[
 J(x)=\sum_{v=0}^{10}\frac{(2x_v-13)^2-1}{8},\qquad
 E(x)=11+8J(x),\qquad u(x)=\sum_{v=0}^{10}x_v27^v.
\]
The one-digit energy generating polynomial is
\[
 D(z)=2(1+z+z^3+z^6+z^{10}+z^{15}+z^{21}).
\]
The exact coefficient is
\[
 [z^{86}]D(z)^{11}=67\,169\,169\,408
     \ge T=25\cdot6^{12}=54\,419\,558\,400.
\]
It can be checked with the finite recurrence $c_0(0)=1$,
$c_0(e)=0$ for $e>0$, and
\[
 c_{n+1}(e)=2\sum_{j=0}^6 c_n(e-j(j+1)/2),
 \qquad c_n(e)=0\quad(e<0).
\]
Only energies $0\le e\le86$ and $0\le n\le11$ are needed.
Thus the layer $J(x)=86$ has enough distinct words, all of squared
norm $699$. Select $T$ such words and write them as $x(a)$.
Write $u_a=u(x(a))$ and designate positions by
"""+NEW_POSITIONS.split("Write $u_a=u(x(a))$ and designate positions by\n")[1]


def rows():
    result = [[1]+[0]*86]
    for _ in range(11):
        old = result[-1]
        result.append([2*sum(old[e-j*(j+1)//2] for j in range(7) if j*(j+1)//2 <= e)
                       for e in range(87)])
    return result


def lean_data(table):
    parts = ["import Lean\n\nnamespace HeilbronnExactLayer\n\n"
             "-- Counts for energies 0 through 86; every transition is checked in Lean.\n"]
    for m, row in enumerate(table):
        parts.append(f"def row{m} : Array Nat := #[\n  "+",\n  ".join(
            ", ".join(str(x) for x in row[i:i+8]) for i in range(0, len(row), 8))+"\n]\n\n")
    parts.append("def table : Array (Array Nat) := #["+
                 ", ".join(f"row{m}" for m in range(12))+"]\n\nend HeilbronnExactLayer\n")
    return "".join(parts)


def patch_sections():
    originals, changed = slab_sections()
    name = "03-norm-digits.tex"
    text = replace_once(changed[name],
        "M=\\binom{4d-1}{d},\\qquad\n T=\\binom{M}{3}", "T=(2d-1)6^{d-1}")
    text = replace_once(text, r"m=17,\qquad A=101,\qquad k=403^{17}",
                        r"m=11,\qquad A=7,\qquad k=27^{11}")
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
    table = rows()
    k, T = 27**11, 25*6**12
    rho = 498*k+6
    beta = Fraction(83*k+1, 2)
    gamma = Fraction(rho, 2*rho+1)
    alpha = rho+gamma
    eta = 2*gamma/alpha
    previous_path = "certificates/norm.json"
    previous = json.loads((ROOT / previous_path).read_text(encoding="utf-8"))
    previous_eta = Fraction(int(previous["eta"]["numerator"]), int(previous["eta"]["denominator"]))
    certificate = {
        "schema": "heilbronn-bilinear-layer-v1", "upstream_commit": PIN,
        "status": "conditional-on-upstream-estimates",
        "scope": "paper exponent; not the upstream Lean comparator exponent",
        "previous_certificate": previous_path,
        "previous_sha256": sha256((ROOT / previous_path).read_bytes()).hexdigest(),
        "d": 13, "T": str(T), "k": str(k),
        "decomposition": {"extension_field_terms": str(6**12), "nodes": 25,
            "interpolated_product_degree_max": 24, "formal_base_field_minimum": 25,
            "retained_manuscript_prime_minimum": 37,
            "row_maps": ["epsilon_rho * eval_t", "eval_t", "ell(c_t * input)"]},
        "packing": {"m": 11, "A": 7, "s": 14, "b": 27, "energy_index": 86,
            "squared_norm": 699, "layer_count": str(table[11][86]),
            "digit_energies": [0, 1, 3, 6, 10, 15, 21], "multiplicity": 2,
            "count_table_energies_0_through_86": [[str(x) for x in row] for row in table]},
        "cap": previous["cap"], "scales": previous["scales"],
        "rho": str(rho), "beta": rational(beta), "gamma": rational(gamma),
        "alpha": rational(alpha), "eta": rational(eta), "gain_from_norm": rational(eta/previous_eta),
        "constraints": {"zero_case_h_powers": [0, -2, -6],
            "collision_r_power": rational(2*gamma-1),
            "pair_r_power": rational(gamma-6*(k-1))},
        "formal_scope": {
            "proved": ["25-node bilinear interpolation and determinant descent",
                "degree-13 field-norm identity with homogeneous polynomial coordinates",
                "nonzero residue exactly for distinct labels for every prime >= 25",
                "symbolic layer-count recurrence and all 11 finite table transitions",
                "complete finite packing for T = 25*6^12 and k = 27^11",
                "inherited integer scale inequalities and exponent identity",
                "9.46 < gain from 37-node norm checkpoint < 9.47"],
            "written_not_formalized": previous["formal_scope"]["written_not_formalized"]},
        "parameter_choice": "explicit feasible witness; no optimality claim",
    }
    for path, text in [
        ("certificates/bilinear.json", json.dumps(certificate, indent=2)+"\n"),
        ("patches/bilinear-layer.patch", patch_sections()),
        ("lean/ExactLayerData.lean", lean_data(table)),
    ]:
        (ROOT / path).write_text(text, encoding="utf-8", newline="\n")
    print("Generated bilinear certificate, source patch and Lean count table.")


if __name__ == "__main__":
    main()
