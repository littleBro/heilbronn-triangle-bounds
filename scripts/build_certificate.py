"""Generate only the finite arithmetic certificate; no search or sampling."""
from fractions import Fraction
from math import comb
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]


def rational(value):
    return {"numerator": str(value.numerator), "denominator": str(value.denominator)}


def main():
    d = 41
    monomials = comb(4 * d - 1, d)
    terms = comb(monomials, 3)
    bits = (terms - 1).bit_length()
    old_k = terms**2 + 1
    new_k = 3**bits
    old_eta = Fraction(2, 45435 * old_k + 16)
    new_eta = Fraction(2, 45435 * new_k + 16)
    certificate = {
        "schema": "heilbronn-ternary-packing-v1",
        "upstream_commit": "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb",
        "status": "conditional-on-upstream-estimates",
        "scope": "paper exponent; not the upstream Lean comparator exponent",
        "d": d,
        "M": str(monomials),
        "T": str(terms),
        "m": bits,
        "k_original": str(old_k),
        "k_ternary": str(new_k),
        "eta_original": rational(old_eta),
        "eta_ternary": rational(new_eta),
        "gain": rational(new_eta / old_eta),
        "placement": {
            "u_a": "binary digits of a interpreted in base 3, padded to m digits",
            "i_a": "u_a",
            "j_a": "u_a",
            "ell_a": "3^m - 1 - 2*u_a",
            "target": "3^m - 1",
            "index_range": "0 <= a < T",
        },
        "unchanged_parameters": {
            "L": "r^10",
            "B": "100*k^2*r^30 < B <= 200*k^2*r^30, B prime",
            "h": "B^k",
            "tau": "floor(B^(k-1)/2)",
            "q": "h^100 < q <= 2*h^100, q prime",
            "N": "(h*q)^10",
            "alpha": "45435*k + 16",
        },
    }
    destination = ROOT / "certificates" / "ternary.json"
    destination.parent.mkdir(exist_ok=True)
    destination.write_text(json.dumps(certificate, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(f"Generated {destination.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
