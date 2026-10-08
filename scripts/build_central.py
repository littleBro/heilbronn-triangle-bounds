"""Certify an explicit central energy window; preserve earlier checkpoints."""
from fractions import Fraction
from hashlib import sha256
from math import comb
from pathlib import Path
import difflib
import json

from build_sphere import PIN, rational
from build_slab import slab_sections

ROOT = Path(__file__).resolve().parents[1]

CENTRAL_COUNT = r"""Each centered coordinate is odd. Write $E(x)=17+8J(x)$, where
\[
 J(x)=\sum_{v=0}^{16} j(x_v),\qquad
 j(t)=\frac{(2t-189)^2-1}{8}.
\]
The $190$ digits give each triangular number $a(a+1)/2$, $0\le a<95$,
twice. Direct finite sums give
\[
 \sum_{t=0}^{189}(j(t)-1504)=0,\qquad
 \sum_{t=0}^{189}(j(t)-1504)^2=343855008.
\]
Put $N_0=190^{17}$ and $Z(x)=J(x)-25568$. Expanding the square over
all words, the cross terms vanish, so
\[
 V:=\sum_x Z(x)^2=17\cdot190^{16}\cdot343855008.
\]
If $J(x)$ is outside $[15568,35568]$, then $|Z(x)|\ge10001$.
Consequently at most $\lfloor V/10001^2\rfloor$ words lie outside.
The exact integer inequality
\[
 V+20001T\cdot10001^2\le N_0\cdot10001^2
\]
proves that the interval contains at least $20001T$ words.
There are at most $20001$ integer energies in it; the pigeonhole
principle therefore supplies $T$ distinct words $x(a)$ of one energy.
"""


def patch_sections():
    originals, changed = slab_sections()
    name = "03-norm-digits.tex"
    text = changed[name].replace("A=101", "A=95").replace("403", "379").replace("202", "190")
    start = text.index("Each centered coordinate is odd")
    stop = text.index("Write $u_a=u(x(a))$", start)
    changed[name] = text[:start] + CENTRAL_COUNT + text[stop:]
    # All remaining scale arguments are already uniform in the fixed k.
    return "".join("".join(difflib.unified_diff(
        originals[name].splitlines(keepends=True), changed[name].splitlines(keepends=True),
        fromfile="a/build/sections/" + name, tofile="b/build/sections/" + name))
        for name in originals)


def main():
    m, A, R = 17, 95, 10000
    s, b = 2 * A, 4 * A - 1
    M = comb(51, 13)
    T = comb(M, 3)
    digit_mean = (A*A - 1) // 6
    one_digit_second = 2 * sum((a*(a+1)//2 - digit_mean)**2 for a in range(A))
    total_words = s**m
    second = m * s**(m-1) * one_digit_second
    center = m * digit_mean
    width, distance = 2 * R + 1, R + 1
    lower = total_words - second // distance**2
    k = b**m
    beta = Fraction(83*k + 1, 2)
    rho = 12 * beta
    gamma = rho / (2*rho + 1)
    alpha = rho + gamma
    eta = 2*gamma / alpha
    previous_path = "certificates/slab.json"
    previous = json.loads((ROOT / previous_path).read_text(encoding="utf-8"))
    certificate = {
        "schema": "heilbronn-central-sphere-v1", "upstream_commit": PIN,
        "status": "conditional-on-upstream-estimates",
        "scope": "paper exponent; not the upstream Lean comparator exponent",
        "previous_certificate": previous_path,
        "previous_sha256": sha256((ROOT / previous_path).read_bytes()).hexdigest(),
        "d": 13, "M": str(M), "T": str(T), "m": m, "A": A, "s": s, "b": b, "k": str(k),
        "energy": {"digit_mean": digit_mean, "digit_centered_sum": "0",
            "digit_centered_square_sum": str(one_digit_second), "center": center,
            "radius": R, "lower": center-R, "upper": center+R,
            "layer_count": width, "outside_distance": distance,
            "word_count": str(total_words), "centered_square_sum": str(second),
            "central_word_lower_bound": str(lower), "required_words": str(width*T),
            "capacity_margin": str(total_words*distance**2-second-width*T*distance**2)},
        "cap": previous["cap"], "scales": previous["scales"],
        "rho": str(rho.numerator), "beta": rational(beta), "gamma": rational(gamma),
        "alpha": rational(alpha), "eta": rational(eta),
        "gain_from_slab": rational(eta * (498*403**17+7)),
        "constraints": {"zero_case_h_powers": [0, -2, -6],
            "collision_r_power": rational(2*gamma-1),
            "pair_r_power": rational(gamma-6*(k-1))},
        "formal_scope": {
            "proved": ["symbolic word count, distinctness, first and second moments",
                "central-window count and finite pigeonhole selection",
                "complete finite packing for T = binom(binom(51,13),3), k = 379^17",
                "inherited integer scale inequalities and exponent identity",
                "284/100 < gain from slab < 285/100"],
            "written_not_formalized": ["slab cap geometry and short-relation exclusion",
                "field norm, lattice, orbit and weighted counting estimates",
                "probability, asymptotic deletion and interpolation"],
        },
        "parameter_choice": "explicit feasible witness; no optimality claim",
    }
    (ROOT / "certificates/central.json").write_text(
        json.dumps(certificate, indent=2) + "\n", encoding="utf-8", newline="\n")
    (ROOT / "patches/central-sphere.patch").write_text(
        patch_sections(), encoding="utf-8", newline="\n")
    print("Generated certificates/central.json and patches/central-sphere.patch")


if __name__ == "__main__":
    main()
