"""Rebuild every local algebra proof and audit the exported theorems."""
from hashlib import sha256
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
}


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
            namespace = "HeilbronnFrobenius" if module.startswith("Frobenius") else "HeilbronnNorm"
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
                 "to 4186119900 base-field determinants for every prime >= 37.",
        "not_established": ["slab cap geometry", "lattice and probability estimates",
                            "full Heilbronn theorem"],
        "evidence_sha256": {p: sha256((ROOT / p).read_bytes()).hexdigest() for p in evidence},
    }
    (ROOT / "artifacts/algebra-verification.json").write_text(
        json.dumps(report, indent=2) + "\n", encoding="utf-8", newline="\n")
    return report


if __name__ == "__main__":
    report = verify_algebra()
    print(f"PASS: {len(THEOREMS)} algebra modules; {report['audited_theorems']} theorem audits.")
