"""Check every retained result and exact regeneration with one portable command."""
from hashlib import sha256
from pathlib import Path
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
GENERATED = [
    "certificates/ternary.json", "certificates/sphere.json", "certificates/tuned.json",
    "patches/ternary-packing.patch", "patches/sphere-packing.patch",
    "patches/tuned-parameters.patch",
]


def run(script):
    print(f"Checking {script}", flush=True)
    subprocess.run([sys.executable, str(ROOT / "scripts" / script)],
                   cwd=ROOT, check=True, timeout=60)


def main():
    if sys.version_info < (3, 11):
        raise SystemExit("Python 3.11 or newer is required.")
    saved = {name: (ROOT / name).read_bytes() for name in GENERATED}
    # Validate supplied certificates before allowing their generators to write.
    for script in ["verify.py", "verify_sphere.py", "verify_tuned.py"]:
        run(script)
    for script in ["build_certificate.py", "build_patch.py", "build_sphere.py", "build_tuned.py"]:
        run(script)
    changed = [name for name, before in saved.items() if (ROOT / name).read_bytes() != before]
    if changed:
        raise SystemExit("Regeneration changed these files; review them and rerun:\n" +
                         "\n".join(changed))
    reports = ["artifacts/verification.json", "artifacts/sphere-verification.json",
               "artifacts/tuned-verification.json"]
    for name in reports:
        report = json.loads((ROOT / name).read_text(encoding="utf-8"))
        if report["status"] != "pass":
            raise SystemExit("Verification failed: " + name)
        for path, expected in report["evidence_sha256"].items():
            if sha256((ROOT / path).read_bytes()).hexdigest() != expected:
                raise SystemExit("Stale report evidence: " + path)
    evidence = reports + [
        "scripts/verify_all.py", "Makefile", ".github/workflows/verify.yml",
        "README.md", "CONTRIBUTING.md", "CITATION.cff", "NOTICE", "LICENSE",
        "docs/reproducibility.md", "docs/review.md", "docs/security.md",
        "SECURITY.md", ".github/dependabot.yml", ".github/CODEOWNERS",
    ]
    summary = {
        "status": "pass",
        "checked_results": ["ternary", "sphere", "tuned"],
        "generated_files_unchanged": GENERATED,
        "environment": "local invocation; see individual reports for runtime versions",
        "evidence_sha256": {p: sha256((ROOT / p).read_bytes()).hexdigest() for p in evidence},
        "scope": "Local proofs, exact certificates, finite controls and source patches; "
                 "the full geometric theorem remains conditional.",
    }
    (ROOT / "artifacts/repository-verification.json").write_text(
        json.dumps(summary, indent=2) + "\n", encoding="utf-8", newline="\n")
    print("PASS: all three results checked; all six generated files reproduced exactly.")


if __name__ == "__main__":
    main()
