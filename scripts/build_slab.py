"""Add the slab cap variant; earlier certificates and patches remain checkpoints."""
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import difflib
import json

from build_sphere import PIN, rational
from build_tuned import replace_once, tuned_sections

ROOT = Path(__file__).resolve().parents[1]


def patch_sections():
    originals, changed = tuned_sections()
    name = "05-auxiliary-cap.tex"
    text = replace_once(changed[name], r"$h\ge 3$", r"$h\ge 10$")
    text = replace_once(text, r"h^{14}<q\le 2h^{14}", r"h^6<q\le 2h^6")
    text = replace_once(text, "intersection with a small box.",
        "restriction to a slab. Only the first coordinate is restricted,\n"
        "as required by the short-relation argument below.")
    text = replace_once(text,
        r"$S\subset\{0,\ldots,w-1\}^3\subset\mathbb F_q^3$ with",
        r"$S\subset\{0,\ldots,w-1\}\times\mathbb F_q^2$ with")
    text = replace_once(text, r"$|S|\ge w^3/q$", r"$|S|=wq$")
    start = text.index(r"For a uniform $b\in\mathbb F_q^3$")
    stop = text.index(r"\end{proof}", start)
    text = text[:start] + r"""Take the following subset of the same paraboloid:
\[
 S=\{(x,y,Q(x,y)):0\le x<w,\ y\in\mathbb F_q\}.
\]
The first two coordinates distinguish its $wq$ points. As a subset of
$\Gamma$, it has no three distinct collinear points. The second and
third coordinates need no small integer representatives.
""" + text[stop:]
    text = replace_once(text,
        r"s\ge\frac{w^3}{q}\ge\frac{q^2}{2000^3H^6}.",
        r"s=wq\ge\frac{q^2}{2000H^2}.")
    text = replace_once(text,
        r"$S\subset\{0,\ldots,w-1\}^3$ contains no three distinct collinear",
        r"$S\subset\{0,\ldots,w-1\}\times\mathbb F_q^2$ contains no three distinct collinear")
    changed[name] = text

    name = "07-zero-determinants.tex"
    text = changed[name].replace("h^{14}", "h^6").replace("h^8", "h^4")
    changed[name] = replace_once(text, r"qH^6=64qh^6", r"qH^2=4qh^2")

    name = "08-alteration.tex"
    text = changed[name].replace("1074k", "498k").replace("h^{14}", "h^6")
    changed[name] = replace_once(text,
        r"\beta=90k-\frac{k-1}{2}=\frac{179k+1}{2}",
        r"\beta=42k-\frac{k-1}{2}=\frac{83k+1}{2}")

    return "".join("".join(difflib.unified_diff(
        originals[name].splitlines(keepends=True), changed[name].splitlines(keepends=True),
        fromfile="a/build/sections/" + name, tofile="b/build/sections/" + name))
        for name in originals)


def main():
    k = 403**17
    rho = 498 * k + 6
    gamma = Fraction(rho, 2 * rho + 1)
    beta = 42 * k - Fraction(k - 1, 2)
    alpha = 12 * beta + gamma
    eta = 2 * gamma / alpha
    previous = Fraction(1, 1074 * k + 7)
    packing_path = "certificates/tuned.json"
    certificate = {
        "schema": "heilbronn-slab-cap-v1",
        "upstream_commit": PIN,
        "status": "conditional-on-upstream-estimates",
        "scope": "paper exponent; not the upstream Lean comparator exponent",
        "packing_certificate": packing_path,
        "packing_sha256": sha256((ROOT / packing_path).read_bytes()).hexdigest(),
        "d": 13, "k": str(k),
        "cap": {
            "set": "{(x,y,x^2-nu*y^2): 0 <= x < w, y in F_q}; nu nonsquare",
            "width": "w = floor(q/(1000*H^2))",
            "cardinality": "s = w*q",
            "density_bound": "s >= q^2/(2000*H^2)",
            "short_relation_change": "only first-coordinate bounds are required",
            "proof_status": "written finite-field argument; not formalized in Lean",
        },
        "scales": {
            "L": "400*k^2*r^4", "B": "100*k^2*L^3 < B <= 200*k^2*L^3; B prime",
            "h": "B^k", "tau": "floor(B^(k-1)/2)", "H": "2*h",
            "q": "h^6 < q <= 2*h^6; q prime", "N": "(h*q)^4",
            "n_r": "floor(r^gamma*sqrt(N^3/tau))",
        },
        "rho": str(rho), "beta": rational(beta), "gamma": rational(gamma),
        "alpha": rational(alpha), "eta": rational(eta),
        "gain_from_tuned": rational(eta / previous),
        "constraints": {
            "cap_condition": "h >= 10 implies 2000*(2*h)^2 <= h^6 < q",
            "zero_case_h_powers": [6 - 6, 4 - 6, 6 - 2 * 6],
            "collision_r_power": rational(2 * gamma - 1),
            "pair_r_power": rational(gamma - 6 * (k - 1)),
        },
        "formal_scope": {
            "proved": ["existing finite packing and digit-moment inequalities via Tuned",
                "floor-width and slab-cardinality lower-bound arithmetic",
                "cap modulus and three zero-case inequalities",
                "cleared-denominator deletion inequalities and exponent identity",
                "215/100 < gain from tuned < 216/100"],
            "written_not_formalized": ["slab cap geometry and short-relation exclusion",
                "field norm, lattice, orbit and weighted counting estimates",
                "probability, asymptotic deletion and interpolation"],
        },
    }
    (ROOT / "certificates/slab.json").write_text(
        json.dumps(certificate, indent=2) + "\n", encoding="utf-8", newline="\n")
    (ROOT / "patches/slab-cap.patch").write_text(
        patch_sections(), encoding="utf-8", newline="\n")
    print("Generated certificates/slab.json and patches/slab-cap.patch")


if __name__ == "__main__":
    main()
