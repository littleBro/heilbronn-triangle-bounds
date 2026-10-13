"""Rebuild every local algebra proof and audit the exported theorems."""
from hashlib import sha256
from functools import cache
from pathlib import Path
import json
import os
import re
import subprocess

from prepare_mathlib import PINS, check_dependencies
from verify import require

ROOT = Path(__file__).resolve().parents[1]
THEOREMS = {
    "NormExpansion": ["determinant_product_compression", "orbit_card"],
    "NormDescent": ["determinant_descent"],
    "NormAlgebra": ["norm_orbit_expansion", "norm_decomposition", "finite_field_norm_decomposition"],
    "NormPolynomials": ["polynomial_norm_decomposition", "finite_field_polynomial_norm_decomposition"],
    "NormVandermonde": ["finite_field_label_decomposition", "prime_field_label_decomposition"],
    "BilinearDescent": ["bilinear_interpolation", "bilinear_determinant_descent"],
    "BilinearNorm": ["bilinear_term_card", "bilinear_norm_decomposition", "finite_field_bilinear_norm",
                     "finite_field_bilinear_polynomials", "prime_field_bilinear_labels"],
    "FrobeniusOrbits": ["fixed_pattern", "orbit_size", "class_card", "invariant_sum"],
    "FrobeniusNorm": ["patternTerm_rotate", "norm_pattern_sum", "averagedCoord_invariant"],
    "FrobeniusDescent": ["projected_determinant", "norm_class_sum", "trace_term_card",
                         "trace_norm_decomposition", "finite_field_trace_norm"],
    "FrobeniusPolynomials": ["finite_field_trace_polynomials", "prime_field_trace_labels"],
    "RankFiveExpansion": ["rank_five", "antisymmetrized_product"],
    "RankFiveOrbits": ["fixed_pattern", "orbit_size", "class_card", "invariant_sum"],
    "RankFiveNorm": ["patternTerm_rotate", "norm_pattern_sum", "norm_class_sum", "trace_term_card",
                     "trace_norm_decomposition", "finite_field_trace_norm"],
    "RankFivePolynomials": ["finite_field_trace_polynomials", "prime_field_trace_labels"],
    "PairedExpansion": ["pair_identity", "paired_product"],
    "PairedNorm": ["term_card", "norm_expansion", "norm_decomposition", "finite_field_norm"],
    "PairedPolynomials": ["finite_field_polynomials", "prime_field_labels"],
    "EighteenExpansion": ["pair_identity", "paired_product"],
    "EighteenNorm": ["term_card", "norm_expansion", "norm_decomposition", "finite_field_norm"],
    "EighteenPolynomials": ["root_exists", "finite_field_polynomials", "prime_field_labels"],
    "SevenDescent": ["bilinear_interpolation", "bilinear_determinant_descent"],
    "SevenNorm": ["term_card", "norm_expansion", "norm_decomposition", "finite_field_norm"],
    "SevenPolynomials": ["finite_field_polynomials", "prime_field_labels"],
    "FiveDescent": ["bilinear_interpolation", "bilinear_determinant_descent"],
    "FiveNorm": ["term_card", "norm_expansion", "norm_decomposition", "finite_field_norm"],
    "FivePolynomials": ["finite_field_polynomials", "prime_field_labels"],
    "FiveCollision": ["repeated_top_factorization", "all_equal_top_determinant"],
    "FiveProbability": ["probability_le_of_completion", "average_product", "divisor_moment_of_joint_tails"],
    "FiveDigits": ["radix_prefix", "tag_unit", "residueAlphabet_injective", "residueAlphabet_bounds", "residueAlphabet_complete", "DigitModel.schur_prefix", "linear_fresh_unique"],
    "FiveJointTail": ["DigitModel.lowPositions_card", "DigitModel.schur_probability", "DigitModel.fresh_joint_tail", "DigitModel.uniform_divisor_moment", "DigitModel.fresh_divisor_moment"],
    "FiveTags": ["first_differing_tag", "tagged_minor_first", "eval_first_valuation", "DigitModel.minorExponent_spec", "DigitModel.minorExponent_schur", "DigitModel.actual_uniform_moment"],
    "FiveMoment": ["DigitModel.weighted_coefficient", "DigitModel.tagged_pair_moment", "DigitModel.tagged_pair_moment_from_tags"],
    "FiveCarry": ["truncEval_bound", "eval_sub_trunc_dvd", "small_residue_coefficient"],
    "FiveCoefficientBounds": ["determinant_coefficient_bound", "determinant_balanced_coefficients"],
    "FiveLabels": ["label_pair_probability", "label_all_equal_probability", "label_mixture_moment"],
    "FiveTagged": ["five_probability_scale", "DigitModel.smallMoment_le_uniform", "DigitModel.tagged_small_residue_moment"],
    "FiveReindex": ["DigitModel.minorExponent_permute", "DigitModel.smallResidue_permute", "DigitModel.smallMoment_permute"],
    "FiveFiniteTheorem": ["TaggedData.moment", "total_small_residue_moment"],
}


@cache
def verify_algebra():
    check_dependencies()
    env = {**os.environ, "LEAN_NUM_THREADS": "1"}
    env.pop("LEAN_PATH", None)
    version = subprocess.check_output(["lake", "env", "lean", "--version"],
        cwd=ROOT, env=env, text=True, timeout=30).strip()
    require("version 4.11.0," in version, "Lean version")
    output_dir = ROOT / ".lake/build/lib"
    output_dir.mkdir(parents=True, exist_ok=True)
    audit = []
    for module, names in THEOREMS.items():
        source = (ROOT / f"lean/{module}.lean").read_text(encoding="utf-8")
        require(not re.search(r"\b(sorry|admit|axiom|unsafe|native_decide)\b", source),
                "proof escape: " + module)
        result = subprocess.run(["lake", "env", "lean", "-j", "1", "-M", "2048",
            "-o", f".lake/build/lib/{module}.olean", f"lean/{module}.lean"],
            cwd=ROOT, env=env, text=True, encoding="utf-8", errors="replace",
            capture_output=True, timeout=120)
        output = result.stdout + result.stderr
        require(result.returncode == 0 and "error:" not in output and "sorryAx" not in output,
                "Lean failure: " + module + "\n" + output)
        for name in names:
            namespace = ("HeilbronnFive" if module.startswith("Five") else
                         "HeilbronnSeven" if module.startswith("Seven") else
                         "HeilbronnEighteen" if module.startswith("Eighteen") else
                         "HeilbronnPaired" if module.startswith("Paired") else
                         "HeilbronnRankFive" if module.startswith("RankFive") else
                         "HeilbronnFrobenius" if module.startswith("Frobenius") else "HeilbronnNorm")
            matches = re.findall("'" + namespace + r"\." + name +
                                 r"' depends on axioms: \[([^]]*)\]", output)
            require(len(matches) == 1, "missing or duplicate audit: " + name)
            actual = {a.strip() for a in matches[0].split(",") if a.strip()}
            require(actual <= {"propext", "Classical.choice", "Quot.sound"},
                    "unexpected axiom: " + name)
        audit.extend(output.splitlines())
    evidence = [f"lean/{module}.lean" for module in THEOREMS] + [
        "lakefile.lean", "lake-manifest.json", "lean-toolchain",
        "scripts/prepare_mathlib.py", "scripts/verify_algebra.py",
    ]
    report = {
        "status": "pass", "lean": version,
        "dependencies": {name: {"url": url, "revision": rev} for name, (url, rev) in PINS.items()},
        "compiled_modules": list(THEOREMS),
        "audited_theorems": sum(len(names) for names in THEOREMS.values()),
        "lean_axiom_audit": audit,
        "compilation_limits": {"threads": 1, "memory_mb_per_process": 2048,
                               "timeout_seconds_per_module": 120},
        "scope": "Universal degree-13 field-norm decomposition, homogeneous polynomial "
                 "coordinates and nonzero residue exactly for distinct labels; "
                 "37-node and 25-node descents, plus Galois-orbit compression "
                 "the five-term tensor formula and paired determinants, giving 1600000000 base-field "
                 "determinants for every prime >= 37. The 18-form checkpoint gives 850305600 "
                 "determinants for primes >= 37 congruent to 1 mod 3, with root existence proved. "
                 "The degree-7 checkpoint gives 75816 determinants over the same primes, "
                 "with homogeneous coordinates and the distinct-label criterion. "
                 "The degree-5 checkpoint gives 2916 determinants, with the same interfaces; "
                 "the two-repeated-column determinant factorization is also checked. "
                 "The finite tagged digit model, exact joint tails, carry implication, tag valuation, "
                 "minor-exponent moment, column reindexing and label-mixture bound are kernel-checked.",
        "not_established": ["slab cap geometry", "lattice and orbit estimates",
                            "norm-packing instantiation and Smith-divisor identification",
                            "prime number theorem in arithmetic progressions", "full Heilbronn theorem"],
        "evidence_sha256": {p: sha256((ROOT / p).read_bytes()).hexdigest() for p in evidence},
    }
    (ROOT / "artifacts/algebra-verification.json").write_text(
        json.dumps(report, indent=2) + "\n", encoding="utf-8", newline="\n")
    return report


if __name__ == "__main__":
    report = verify_algebra()
    print(f"PASS: {len(THEOREMS)} algebra modules; {report['audited_theorems']} theorem audits.")
