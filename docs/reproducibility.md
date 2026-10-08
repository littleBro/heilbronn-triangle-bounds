# Reproducing the results

Install Python 3.11 or newer, Git, and
[elan](https://github.com/leanprover/elan), the Lean toolchain manager.
The checked-in lean-toolchain selects Lean 4.11.0. The algebra proof uses
Mathlib v4.11.0 at commit 20c73142afa995ac9c8fb80a9bb585a55ca38308;
lake-manifest.json locks all seven dependency revisions. The earlier packing
and scale proofs use core Lean. No third-party Python packages are used.
Toolchain and dependency preparation need network access; subsequent proof
and certificate checks run locally.

From the repository root, install the pinned toolchain if necessary:

    elan toolchain install leanprover/lean4:v4.11.0

Prepare the dependencies once per fresh checkout, then verify on Windows,
Linux or macOS:

    python scripts/prepare_mathlib.py
    python scripts/verify_all.py

Preparation checks the Mathlib revision before running its cache tool and
fetches compiled imports for the required modules. It does not run lake update.
Dependencies and compiled files stay in the ignored .lake/ directory.
The verifier checks all dependency revisions and rejects modified tracked
dependency sources before rebuilding each local algebra proof.

Where Python is named python3, use that name instead. With Make available,
make verify runs the same entry point.

The command first verifies the supplied ternary, sphere, retuned, slab,
central-layer and norm-compression certificates.
It checks all saved upstream hashes, compiles the local Lean proofs, audits their
logical axioms, exercises finite and negative controls, and checks each patch
against the pinned original manuscript without applying it.
It then regenerates all certificates and patches and requires exact byte equality
with the supplied files. Generated text uses UTF-8 with LF line endings.
A regeneration mismatch is a failure even when the resulting certificate would pass.

The tuned check rebuilds Sphere.olean from its source before importing it.
The slab check rebuilds both Sphere.olean and Tuned.olean before importing them.
The central-layer check rebuilds Sphere.olean, Tuned.olean and Slab.olean.
The norm-compression check rebuilds the same three dependencies before its
permutation and packing proofs. It also rebuilds NormExpansion, NormDescent,
NormAlgebra, NormPolynomials and NormVandermonde in order, using pinned Mathlib
imports. Each algebra compilation uses one thread, a 2048 MB Lean memory limit
and a 120-second timeout. Ten exported theorems are audited, including the
prime-field specialization and homogeneous polynomial form. Run this part
alone with python scripts/verify_algebra.py.
Independent field controls use small explicit quotients; the degree-13 norm
expansion is proved symbolically and is not enumerated.
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
It first scans Git history and checked-out files with a pinned Gitleaks release.
It pins action commits and the elan installer, installs the exact Lean version,
prepares the locked Mathlib imports, runs the same verifier and saves the reports
for 14 days. The secret scan is a
separate CI check, not part of the local mathematical verification command.
See [the security review](security.md) before running untrusted contributions.
Check
[the Actions runs](https://github.com/littleBro/heilbronn-triangle-bounds/actions/workflows/verify.yml)
for the result on the commit you use; the workflow file alone is not evidence
that a remote run passed.

## Individual checkpoints

| Result | Generator | Checker |
| --- | --- | --- |
| Ternary baseline | scripts/build_certificate.py and scripts/build_patch.py | scripts/verify.py |
| Sphere at d = 41 | scripts/build_sphere.py | scripts/verify_sphere.py |
| Retuned scales at d = 13 | scripts/build_tuned.py | scripts/verify_tuned.py |
| Slab cap at d = 13 | scripts/build_slab.py | scripts/verify_slab.py |
| Central energy interval at d = 13 | scripts/build_central.py | scripts/verify_central.py |
| Compressed norm at d = 13 | scripts/build_norm.py | scripts/verify_norm.py |

After intentionally changing a generator, run it, inspect the changed certificate
and patch, then run the complete verification command.
The six source patches are alternatives against the same original manuscript.

## Proof notes

The current note is notes/sphere-packing.tex; the earlier ternary argument is
notes/packing.tex. Neither is needed by the executable proof checks.
The current note, including norm compression, compiled successfully in the desktop editor with
Tectonic 0.17.0+20260731. Its source hash and bundle identity are recorded in
[artifacts/sphere-latex-status.json](../artifacts/sphere-latex-status.json).
The initial download failure was resolved by using the
[official v33 redirect target](https://github.com/tectonic-typesetting/tectonic-relay-service/blob/main/temporary_redirects.map),
https://data1b.fullyjustified.net/tlextras-2022.0r0.tar, as the user-level default
bundle. Support files are cached locally. No compiler binaries or bundles are
stored in this repository, and generated note PDFs are not included.
The separate artifacts/latex-status.json is the historical ternary-note attempt.
Document compilation is not part of verify_all.py or the current CI workflow.
The PDF under upstream/ is the unchanged original manuscript.
