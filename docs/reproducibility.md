# Reproducing the results

Install Python 3.11 or newer, Git, and
[elan](https://github.com/leanprover/elan), the Lean toolchain manager.
The checked-in lean-toolchain selects Lean 4.11.0. No Mathlib or third-party
Python packages are used. Toolchain installation needs network access;
the proof and certificate checks use the bundled sources and run locally.

From the repository root, install the pinned toolchain if necessary:

    elan toolchain install leanprover/lean4:v4.11.0

Then run the same command on Windows, Linux or macOS:

    python scripts/verify_all.py

Where Python is named python3, use that name instead. With Make available,
make verify runs the same entry point.

The command first verifies the supplied ternary, sphere and retuned certificates.
It checks all saved upstream hashes, compiles the local Lean proofs, audits their
logical axioms, exercises finite and negative controls, and checks each patch
against the pinned original manuscript without applying it.
It then regenerates all certificates and patches and requires exact byte equality
with the supplied files. Generated text uses UTF-8 with LF line endings.
A regeneration mismatch is a failure even when the resulting certificate would pass.

The tuned check rebuilds Sphere.olean from its source before importing it.
All Lean checks are bounded subprocesses. Proof compilation does not enumerate
the enormous sphere or produce planar point configurations.
The scripts run sequentially and need no WSL, container or parallel search.

Successful runs refresh the reports under artifacts/, including
repository-verification.json. These contain runtime details and hashes of
the actual checked files; changes to runtime versions or source files can change
the reports. Certificates and patches are deterministic.
Compiled Lean files and Python caches are ignored by Git.

The local checks have passed on native Windows with Python 3.14.4 and Lean 4.11.0.
The included GitHub Actions workflow targets Ubuntu 24.04 and Python 3.11.
Its first remote run is still pending; the workflow file alone is not evidence
that Linux reproduction has passed. It pins action commits and the elan installer,
installs the exact Lean version, runs the same verifier and saves the reports.

## Individual checkpoints

| Result | Generator | Checker |
| --- | --- | --- |
| Ternary baseline | scripts/build_certificate.py and scripts/build_patch.py | scripts/verify.py |
| Sphere at d = 41 | scripts/build_sphere.py | scripts/verify_sphere.py |
| Retuned scales at d = 13 | scripts/build_tuned.py | scripts/verify_tuned.py |

After intentionally changing a generator, run it, inspect the changed certificate
and patch, then run the complete verification command.
The three source patches are alternatives against the same original manuscript.

## Proof notes

The current note is notes/sphere-packing.tex; the earlier ternary argument is
notes/packing.tex. Neither is needed by the executable proof checks.
The local built-in document compiler could not download its missing TeX bundle,
so this draft does not include freshly compiled note PDFs.
The two LaTeX status files record that environment limitation.
The PDF under upstream/ is the unchanged original manuscript.
