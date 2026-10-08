"""Exact finite parameter selection and a separate centered-sphere source patch."""
from fractions import Fraction
from math import comb
from pathlib import Path
import difflib
import json

from build_patch import OLD_PARAMETERS, OLD_POSITIONS

ROOT = Path(__file__).resolve().parents[1]
PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"


def rational(value):
    return {"numerator": str(value.numerator), "denominator": str(value.denominator)}


def select_parameters(terms):
    # Only small integer parameter calculations: no sphere-point enumeration.
    candidates = []
    for dimension in range(3, 285):
        def sufficient(a):
            layers = dimension * a * (a - 1) // 2 + 1
            return (2 * a)**dimension >= terms * layers

        lo, hi = 1, 2
        while not sufficient(hi):
            hi *= 2
        while lo + 1 < hi:
            mid = (lo + hi) // 2
            if sufficient(mid):
                hi = mid
            else:
                lo = mid
        candidates.append(((4 * hi - 1)**dimension, dimension, hi))
    return min(candidates)


NEW_PARAMETERS = r"""T=\binom{M}{3},\qquad m=29,\qquad A=10003,\qquad
 k=(4A-1)^m=40011^{29}."""

NEW_POSITIONS = r"""We use a finite centered-sphere form of Behrend's progression-free
construction.  Put $s=2A=20006$ and $b=2s-1=40011$.
For a word $x=(x_0,\ldots,x_{m-1})\in\{0,\ldots,s-1\}^m$, define
\[
 E(x)=\sum_{v=0}^{m-1}(2x_v-(s-1))^2,\qquad
 u(x)=\sum_{v=0}^{m-1}x_vb^v.
\]
Each centered coordinate is odd, so its square is $1$ modulo $8$.
It follows that $E(x)=m+8j$ with
$0\le j\le mA(A-1)/2$.  There are therefore at most
$Q=mA(A-1)/2+1=1450725088$ possible energies.
The exact inequality
\[
 TQ\le 20006^{29}
\]
and the pigeonhole principle give an energy containing at least $T$
words.  Choose such an energy class, and enumerate its first $T$
words in increasing base-$s$ index $\sum_v x_vs^v$
as $x(a)$, $0\le a<T$.
Write $u_a=u(x(a))$ and designate positions by
\begin{equation}\label{norm:positions}
 i_a=u_a,\qquad j_a=u_a,\qquad \ell_a=k-1-2u_a.
\end{equation}
Since $2(s-1)=b-1$, the geometric sum gives $0\le2u_a\le b^m-1$.
Uniqueness of base-$b$ expansion and the distinctness of the selected
words show that the positions are in $\{0,\ldots,k-1\}$ and distinct
within each row.  They satisfy
\begin{equation}\label{norm:matching}
 i_a+j_{a'}+\ell_{a''}=k-1
 \quad\Longleftrightarrow\quad a=a'=a''.
\end{equation}
Indeed, the equality is equivalent to $u_a+u_{a'}=2u_{a''}$.
Each digit on either side is at most $2(s-1)=b-1$, so there are no
carries; hence $x(a)+x(a')=2x(a'')$ coordinatewise.
The centered vectors have the same squared norm, and the identity
\[
 \|X-Y\|^2+4\|Z\|^2=2\|X\|^2+2\|Y\|^2,\qquad X+Y=2Z,
\]
forces $X=Y=Z$.  Thus the selected words and their indices agree.
The converse follows by substitution.
The selection is a finite existence construction; the $T$ words are
not enumerated computationally.  All subsequent uses of the positions
require only the matching identity, their range, and their
distinctness within each row."""


def main():
    monomials = comb(163, 41)
    terms = comb(monomials, 3)
    k, m, a = select_parameters(terms)
    assert (m, a) == (29, 10003)
    layers = m * a * (a - 1) // 2 + 1
    eta = Fraction(2, 45435 * k + 16)
    old_eta = Fraction(2, 45435 * (terms**2 + 1) + 16)
    ternary_eta = Fraction(2, 45435 * 3**384 + 16)
    certificate = {
        "schema": "heilbronn-centered-sphere-v1",
        "upstream_commit": PIN,
        "status": "conditional-on-upstream-estimates",
        "scope": "paper exponent; not the upstream Lean comparator exponent",
        "d": 41, "M": str(monomials), "T": str(terms),
        "dimension": m, "half_alphabet": a,
        "alphabet": 2 * a, "base": 4 * a - 1,
        "energy_layers": layers,
        "cube_size": str((2 * a)**m),
        "required_capacity": str(terms * layers),
        "k_sphere": str(k),
        "eta_sphere": rational(eta),
        "gain_from_original": rational(eta / old_eta),
        "gain_from_ternary": rational(eta / ternary_eta),
        "selection": "a qualifying energy class, then first T words in increasing base-s index",
        "placement": ["u_a", "u_a", "k-1-2*u_a"],
        "parameter_comparison": {
            "dimensions_inclusive": [3, 284],
            "criterion": "(2*A)^m >= T*(m*A*(A-1)/2+1)",
            "objective": "minimize (4*A-1)^m",
            "claim": "best of this bounded comparison; no unrestricted optimality claim",
        },
        "formal_scope": {
            "proved": ["sphere midpoint rigidity", "carry-free encoding",
                       "position bounds and injectivity", "matching for equal-energy words",
                       "numeric capacity and exponent ratio", "finite pigeonhole principle",
                       "energy-layer bound and selection of T distinct words",
                       "closed-form binomial calculation of T", "complete finite paper packing"],
            "written_not_formalized": ["geometric transfer", "parameter comparison monotonicity"],
        },
    }
    path = ROOT / "certificates/sphere.json"
    path.write_text(json.dumps(certificate, indent=2) + "\n", encoding="utf-8", newline="\n")
    source = ROOT / "upstream/manuscript/build/sections/03-norm-digits.tex"
    before = source.read_text(encoding="utf-8")
    assert before.count(OLD_PARAMETERS) == before.count(OLD_POSITIONS) == 1
    after = before.replace(OLD_PARAMETERS, NEW_PARAMETERS).replace(OLD_POSITIONS, NEW_POSITIONS)
    relative = "build/sections/03-norm-digits.tex"
    patch = "".join(difflib.unified_diff(
        before.splitlines(keepends=True), after.splitlines(keepends=True),
        fromfile="a/" + relative, tofile="b/" + relative))
    (ROOT / "patches/sphere-packing.patch").write_text(patch, encoding="utf-8", newline="\n")
    print("Generated certificates/sphere.json and patches/sphere-packing.patch")


if __name__ == "__main__":
    main()
