"""Retune the original six manuscript sections; preserve all earlier variants."""
from fractions import Fraction
from math import comb
from pathlib import Path
import difflib
import json

from build_patch import OLD_PARAMETERS, OLD_POSITIONS
from build_sphere import NEW_POSITIONS, PIN, rational, select_parameters

ROOT = Path(__file__).resolve().parents[1]


def replace_once(text, old, new):
    assert text.count(old) == 1, repr(old)
    return text.replace(old, new)


def patch_sections():
    sections = ROOT / "upstream/manuscript/build/sections"
    originals = {p.name: p.read_text(encoding="utf-8")
                 for p in sorted(sections.glob("*.tex")) if p.name[:2] in
                 {"03", "04", "05", "06", "07", "08"}}
    changed = dict(originals)
    name = "03-norm-digits.tex"
    text = replace_once(changed[name], "d=41", "d=13")
    text = replace_once(text, OLD_PARAMETERS,
                        r"T=\binom{M}{3},\qquad m=17,\qquad A=101,\qquad k=403^{17}.")
    positions = (NEW_POSITIONS.replace("20006", "202").replace("40011", "403")
                 .replace("1450725088", "85851").replace("^{29}", "^{17}"))
    text = replace_once(text, OLD_POSITIONS, positions)
    text = replace_once(text, r"Set $L=r^{10}$.", r"Set $L=400k^2r^4$.")
    changed[name] = replace_once(text, r"$L/r=r^9$", r"$L/r=400k^2r^3$")

    name = "04-orbits.tex"
    text = replace_once(changed[name], r"$L=r^{10}$", r"$L=400k^2r^4$")
    text = replace_once(text, r"\theta\leq200k^2r^{-6}.",
                        r"\theta\leq200k^2r^4/L=\frac12.")
    changed[name] = replace_once(text, "Thus, for fixed $k$ and all sufficiently large $r$,",
                                "Thus, uniformly for every allowed $r$,")

    name = "05-auxiliary-cap.tex"
    text = replace_once(changed[name], r"$h\ge 2$", r"$h\ge 3$")
    changed[name] = replace_once(text, r"H=h^2,\qquad h^{100}<q\le 2h^{100}",
                                r"H=2h,\qquad h^{14}<q\le 2h^{14}")

    name = "06-sampling.tex"
    changed[name] = replace_once(changed[name], r"N=(hq)^{10}", r"N=(hq)^4")

    name = "07-zero-determinants.tex"
    text = replace_once(changed[name], r"Recall also $H=h^2$, $q>h^{100}$",
                        r"Recall also $H=2h$, $q>h^{14}$")
    text = replace_once(text, "Finally, $h\\ge2$ implies\n$H/2=h^2/2\\ge h$.",
                        "Finally, $H/2=h$ by the choice $H=2h$.")
    # First change the old rank-two loss, then the two old h^26 losses.
    text = replace_once(text, r"\frac{h^{14}}q", r"\frac{h^8}q")
    text = replace_once(text, r"\frac{h^{26}}q", r"\frac{h^{14}}q")
    text = replace_once(text, r"\frac{h^{26}}{q^2}", r"\frac{h^{14}}{q^2}")
    changed[name] = replace_once(text, r"$q^3/s\ll qH^6=qh^{12}$ and $q>h^{100}$",
                                r"$q^3/s\ll qH^6=64qh^6$ and $q>h^{14}$")

    name = "08-alteration.tex"
    text = replace_once(changed[name],
        r"Keep the parameters constructed above, with $d=41$, and set",
        r"""Keep the parameters constructed above, with $d=13$.  Define
\[
 \rho=1074k+6,\qquad \gamma=\frac{\rho}{2\rho+1}.
\]
Thus $0<\gamma<1/2$ and $2\gamma-1=-1/(2\rho+1)<0$.  Set""")
    text = replace_once(text, r"a_r=r\sqrt", r"a_r=r^\gamma\sqrt")
    start = text.index("Both terms tend to zero.")
    stop = text.index(r"Thus $\mathbb EZ=o(n_r)$.", start)
    text = text[:start] + r"""Both terms tend to zero.  Indeed, $N=(hq)^4$ gives
\[
 n_r(hq)^6N^{-3}\le r^\gamma\tau^{-1/2}.
\]
Since $B^{k-1}\ge3$, we have $\tau\ge B^{k-1}/3$.
Also $B\asymp_k r^{12}$ and $k\ge2$, so the last bound is
$O_k(r^{\gamma-6(k-1)})=o(1)$.
For the other term, the definition of $n_r$ gives
\[
 n_r^2(\log(2N))^2\frac{h}{N^3r^{13}}
 \le(\log(2N))^2\frac{h}{\tau}r^{2\gamma-13}.
\]
Here $h/\tau\le3B=O_k(r^{12})$.
The bounds $q\le2h^{14}$ and $N=(hq)^4$ give
$\log(2N)=O_k(\log r)$.  Thus the second term is
$O_k((\log r)^2r^{2\gamma-1})=o(1)$.
The negative exponent is fixed independently of $r$, although very small.
""" + text[stop:]
    text = replace_once(text, r"Also $\tau<h$ and $N\ge h^{10}$ give",
                        r"Also $\tau<h$ and $N\ge h^4$ give")
    text = replace_once(text, r"$a_r>rh^{29/2}\to\infty$",
                        r"$a_r>r^\gamma h^{11/2}\to\infty$")
    text = replace_once(text, r"\ge\frac{r^2}{64}", r"\ge\frac{r^{2\gamma}}{64}")
    text = replace_once(text, r"100k^2r^{30}<B\le200k^2r^{30}",
                        r"100k^2(400k^2)^3r^{12}<B\le200k^2(400k^2)^3r^{12}")
    text = replace_once(text, r"h^{100}<q\le2h^{100},\qquad N^{3/2}=(hq)^{15}",
                        r"h^{14}<q\le2h^{14},\qquad N^{3/2}=(hq)^6")
    text = replace_once(text, r"\beta=1515k-\frac{k-1}{2}=\frac{3029k+1}{2}",
                        r"\beta=90k-\frac{k-1}{2}=\frac{179k+1}{2}")
    text = replace_once(text, r"\sqrt{2}\,rB^\beta<a_r\le2^{15}\sqrt{3}\,rB^\beta.",
                        r"\sqrt{2}\,r^\gamma B^\beta<a_r\le2^6\sqrt{3}\,r^\gamma B^\beta.")
    text = replace_once(text, r"\alpha=1+30\beta=45435k+16",
                        r"\alpha=\gamma+12\beta=\rho+\gamma")
    text = replace_once(text, r"\eta=\frac2\alpha=\frac{2}{45435k+16}.",
                        r"\eta=\frac{2\gamma}{\alpha}=\frac1{\rho+1}=\frac1{1074k+7}.")
    text = replace_once(text, r"$r^2\ge D_k^{-\eta}n_r^\eta$",
                        r"$r^{2\gamma}\ge D_k^{-\eta}n_r^\eta$")
    text = replace_once(text, r"converts the factor $r^2$", r"converts the factor $r^{2\gamma}$")
    text = replace_once(text,
        "The formula \\eqref{alt:exponent} is explicit; no attempt has been\nmade to optimize the construction parameters.",
        "The formula \\eqref{alt:exponent} is explicit.  These choices improve\n"
        "the earlier scales; no unrestricted optimality claim is made.")
    changed[name] = text

    return "".join("".join(difflib.unified_diff(
        originals[name].splitlines(keepends=True), changed[name].splitlines(keepends=True),
        fromfile="a/build/sections/" + name, tofile="b/build/sections/" + name))
        for name in originals)


def main():
    d = 13
    monomials = comb(4 * d - 1, d)
    terms = comb(monomials, 3)
    k, dimension, a = select_parameters(terms)
    assert (dimension, a) == (17, 101)
    rho = 1074 * k + 6
    gamma = Fraction(rho, 2 * rho + 1)
    beta = 6 * 15 * k - Fraction(k - 1, 2)
    alpha = 12 * beta + gamma
    eta = 2 * gamma / alpha
    previous_eta = Fraction(2, 45435 * 40011**29 + 16)
    original_terms = comb(comb(163, 41), 3)
    original_eta = Fraction(2, 45435 * (original_terms**2 + 1) + 16)
    layers = dimension * a * (a - 1) // 2 + 1
    certificate = {
        "schema": "heilbronn-tuned-scales-v1",
        "upstream_commit": PIN,
        "status": "conditional-on-upstream-estimates",
        "scope": "paper exponent; not the upstream Lean comparator exponent",
        "d": d, "M": str(monomials), "T": str(terms),
        "dimension": dimension, "half_alphabet": a,
        "alphabet": 2 * a, "base": 4 * a - 1,
        "energy_layers": layers, "cube_size": str((2 * a)**dimension),
        "required_capacity": str(terms * layers), "k": str(k),
        "scales": {
            "L": "400*k^2*r^4", "B": "100*k^2*L^3 < B <= 200*k^2*L^3; B prime",
            "h": "B^k", "tau": "floor(B^(k-1)/2)",
            "H": "2*h", "q": "h^14 < q <= 2*h^14; q prime",
            "N": "(h*q)^4", "n_r": "floor(r^gamma*sqrt(N^3/tau))",
        },
        "rho": str(rho), "gamma": rational(gamma), "beta": rational(beta),
        "alpha": rational(alpha), "eta": rational(eta),
        "gain_from_previous_sphere": rational(eta / previous_eta),
        "gain_from_original": rational(eta / original_eta),
        "constraints": {
            "theta_upper": rational(Fraction(1, 2)),
            "collision_r_power": rational(2 * gamma + 12 - d),
            "pair_r_power": rational(gamma - 6 * (k - 1)),
            "zero_case_h_powers": [14 - 14, 8 - 14, 14 - 2 * 14],
            "cap_condition": "h >= 3 implies 2000*(2*h)^2 <= h^14 < q",
        },
        "parameter_comparison": {"dimensions_inclusive": [3, 284],
                                 "claim": "bounded sphere comparison only"},
        "formal_scope": {
            "proved": ["complete finite packing with binomial T for d=13",
                       "digit divisibility and moment inequality",
                       "shell threshold, cap modulus and three zero-case inequalities",
                       "cleared-denominator alteration inequalities and exponent identity",
                       "exact gain enclosure"],
            "written_not_formalized": ["field norm and determinant decomposition",
                "upstream lattice, orbit, auxiliary and weighted counting arguments",
                "probability, asymptotic deletion and interpolation",
                "parameter comparison monotonicity"],
        },
    }
    (ROOT / "certificates/tuned.json").write_text(
        json.dumps(certificate, indent=2) + "\n", encoding="utf-8", newline="\n")
    (ROOT / "patches/tuned-parameters.patch").write_text(
        patch_sections(), encoding="utf-8", newline="\n")
    print("Generated certificates/tuned.json and patches/tuned-parameters.patch")


if __name__ == "__main__":
    main()
