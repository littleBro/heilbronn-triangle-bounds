"""Install the locked Mathlib sources and only the required compiled imports."""
from pathlib import Path
import json
import os
import subprocess

ROOT = Path(__file__).resolve().parents[1]
MATHLIB = "20c73142afa995ac9c8fb80a9bb585a55ca38308"
PINS = {
    "mathlib": ("https://github.com/leanprover-community/mathlib4.git", MATHLIB),
    "batteries": ("https://github.com/leanprover-community/batteries",
                  "9c6c2d647e57b2b7a0b42dd8080c698bd33a1b6f"),
    "Qq": ("https://github.com/leanprover-community/quote4",
           "9d0bdd07bdfe53383567509348b1fe917fc08de4"),
    "aesop": ("https://github.com/leanprover-community/aesop",
              "deb279eb7be16848d0bc8387f80d6e41bcdbe738"),
    "proofwidgets": ("https://github.com/leanprover-community/ProofWidgets4",
                     "a96aee5245720f588876021b6a0aa73efee49c76"),
    "Cli": ("https://github.com/leanprover/lean4-cli",
            "2cf1030dc2ae6b3632c84a09350b675ef3e347d0"),
    "importGraph": ("https://github.com/leanprover-community/import-graph",
                    "1ef0b288623337cb37edd1222b9c26b4b77c6620"),
}
IMPORTS = [
    "Mathlib/RingTheory/Norm/Basic.lean",
    "Mathlib/LinearAlgebra/Lagrange.lean",
    "Mathlib/FieldTheory/Finite/GaloisField.lean",
    "Mathlib/RingTheory/MvPolynomial/Homogeneous.lean",
    "Mathlib/LinearAlgebra/Vandermonde.lean",
    "Mathlib/GroupTheory/GroupAction/Quotient.lean",
    "Mathlib/Tactic/NormNum.lean",
    "Mathlib/Tactic/Ring.lean",
    "Mathlib/Tactic/Group.lean",
]


def check_lock():
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    packages = manifest["packages"]
    actual = {p["name"]: (p["url"], p["rev"]) for p in packages}
    if actual != PINS or len(packages) != len(PINS):
        raise RuntimeError("Lake dependency pins differ from the reviewed lock.")
    if any(p["type"] != "git" or p["subDir"] is not None for p in packages):
        raise RuntimeError("Unexpected dependency source type.")
    if MATHLIB not in (ROOT / "lakefile.lean").read_text(encoding="utf-8"):
        raise RuntimeError("Mathlib root revision differs from the lock.")


def check_checkout(name, revision):
    path = ROOT / ".lake/packages" / name
    if not path.is_dir():
        raise RuntimeError("Missing dependency; run python scripts/prepare_mathlib.py: " + name)
    head = subprocess.check_output(["git", "-C", str(path), "rev-parse", "HEAD"],
                                   text=True, timeout=30).strip()
    if head != revision:
        raise RuntimeError("Dependency checkout differs from the lock: " + name)
    subprocess.run(["git", "-C", str(path), "diff", "--exit-code", "--quiet", "HEAD", "--"],
                   check=True, timeout=30)


def check_dependencies():
    check_lock()
    for name, (_, revision) in PINS.items():
        check_checkout(name, revision)


def main():
    check_lock()
    package = ROOT / ".lake/packages/mathlib"
    if not package.exists():
        package.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(["git", "clone", "--depth", "1", "--branch", "v4.11.0",
                        PINS["mathlib"][0], str(package)], check=True, timeout=300)
    # Verify the tag's immutable revision before any dependency code runs.
    check_checkout("mathlib", MATHLIB)
    for name, (_, revision) in PINS.items():
        if (ROOT / ".lake/packages" / name).exists():
            check_checkout(name, revision)
    env = {**os.environ, "LEAN_NUM_THREADS": "1", "MATHLIB_NO_CACHE_ON_UPDATE": "1"}
    env.pop("LEAN_PATH", None)
    subprocess.run(["lake", "exe", "cache", "get", *IMPORTS], cwd=ROOT,
                   env=env, check=True, timeout=600)
    check_dependencies()
    print("PASS: seven pinned dependencies and required Mathlib imports prepared.")


if __name__ == "__main__":
    main()
