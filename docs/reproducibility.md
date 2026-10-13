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
central-layer, norm-compression, bilinear-layer, Frobenius-orbit, rank-five, paired-determinant, eighteen-form and interval certificates.
It checks all saved upstream hashes, compiles the local Lean proofs, audits their
logical axioms, exercises finite and negative controls, and checks each patch
against the pinned original manuscript without applying it.
It then regenerates all certificates, patches, all five Lean count tables and the interval-count proof source, and requires exact byte equality
with the supplied files. Generated text uses UTF-8 with LF line endings.
A regeneration mismatch is a failure even when the resulting certificate would pass.

The tuned check rebuilds Sphere.olean from its source before importing it.
The slab check rebuilds both Sphere.olean and Tuned.olean before importing them.
The central-layer check rebuilds Sphere.olean, Tuned.olean and Slab.olean.
The norm-compression check rebuilds the same three dependencies before its
permutation and packing proofs. It also rebuilds NormExpansion, NormDescent,
NormAlgebra, NormPolynomials and NormVandermonde in order, using pinned Mathlib
imports. Each algebra compilation uses one thread, a 2048 MB Lean memory limit
and a 120-second timeout. The shared algebra checker also rebuilds BilinearDescent and
BilinearNorm, four Frobenius modules, four rank-five modules and three paired modules and three eighteen-form modules, for 62 exported theorem audits in total, including the
prime-field specialization and homogeneous polynomial form. Run this part
alone with python scripts/verify_algebra.py.
The complete verifier runs its algebra-dependent checkers in one process,
sharing one fresh algebra rebuild. Standalone checkers still rebuild algebra;
no saved verification report or compiled local proof is trusted as a cache.
Independent field controls use small explicit quotients; the degree-13 norm
expansion is proved symbolically and is not enumerated.
The bilinear-layer check also rebuilds Sphere, ExactLayerData and ExactLayer.
Its core Lean proof checks eleven complete histogram transitions, then proves
the symbolic recurrence, selection and packing; no table entry is trusted as a premise.
These compilations use the same one-thread, 2048 MB and 120-second limits.
The Frobenius checkpoint also rebuilds FrobeniusPacking after those core modules.
It uses the already checked table entry at length 10, energy 80, and independently
counts that layer by a multinomial sum. Its field controls enumerate the rotation
classes only in degrees 3 and 5; degree 13 uses sampled patterns and all basis vectors.
All Lean checks are bounded subprocesses. Proof compilation does not enumerate
the enormous sphere or produce planar point configurations.
The scripts run sequentially and need no WSL, container or parallel search.

The rank-five checkpoint adds the general mixed-radix sphere proof and a
120-entry table. Nine kernel-checked transitions are divided across three
small modules to stay within the same per-process limits. The symbolic
recurrence connects the table to actual word counting before selection and
packing. Independent convolution and multinomial counts agree. Degree-3 and
degree-5 norm expansions are enumerated; degree 13 remains a symbolic Lean proof
with sampled finite controls. The factor 1/6 is covered by a negative control.

The paired checkpoint adds ten transitions of a 60-entry table. Its three
algebra modules prove the 20-term pair identity, the full field norm,
homogeneous coordinates and distinct-label specialization. Small degrees
3 and 5 are fully enumerated by independent controls; degree 13 has
factorized checks and sampled descended terms. Normalization and duplicated
conjugates have negative controls. The optional python scripts/search_packing.py
reproduces the recorded finite alphabet/weight search; it is not required by
verification, which checks the exact witness independently.

The eighteen-form checkpoint adds eleven transitions of a 33-entry table,
the universal pair identity with its root condition, root existence for primes
congruent to 1 mod 3, norm descent and polynomial coordinates. Independent
checks verify all 729 tensor coefficients exactly. The prime number theorem
and its all-cardinalities transfer remain written arguments. The optional
python scripts/search_eighteen.py reproduces the bounded alphabet search.
The checker also applies the rank-five, paired and eighteen-form patches
to ignored text snapshots under .lake/patch-reference-checks and checks
that every referenced label exists exactly once. It does not compile or
export another PDF. Removing the matching label is a negative control.

The interval checkpoint adds a general encoded-cutoff recurrence and 44 rows
of 33 exact counts. TrimmedLayer.lean is generated with the table: its finite
transitions use kernel evaluation and its recurrence proof connects the counts
to actual words. TrimmedPacking.lean proves selection and the translated
packing. The independent checker reads high digits first, compares all 1,452
table entries, exhausts 13,583 small cutoff counts and checks 42,216 matching
triples. Both endpoint omissions and a missing translation have negative
controls. The algebra remains the verified eighteen-form construction.
The optional python scripts/search_trimmed.py reproduces the finite rank-window
branch-and-bound search. Its interval bounds cover all ranks in the listed
family, evaluating 8,922 windows directly. The complete search is not required
by verification; 342 small search problems are checked against enumeration.
Search optimality is not formalized and no global packing optimum is claimed.
The interval source patch also receives the full reference check.

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
| Bilinear descent and exact layer | scripts/build_bilinear.py | scripts/verify_bilinear.py |
| Galois-orbit compression and ten-digit layer | scripts/build_frobenius.py | scripts/verify_frobenius.py |
| Five-term determinant and mixed sphere | scripts/build_rankfive.py | scripts/verify_rankfive.py |
| Paired determinants and mixed sphere | scripts/build_paired.py | scripts/verify_paired.py |
| Eighteen forms over split primes | scripts/build_eighteen.py | scripts/verify_eighteen.py |
| Translated interval of the mixed sphere | scripts/build_trimmed.py | scripts/verify_trimmed.py |

After intentionally changing a generator, run it, inspect the changed certificate
and patch, then run the complete verification command.
The twelve source patches are alternatives against the same original manuscript.

## Proof notes

The current note is notes/sphere-packing.tex; the earlier ternary argument is
notes/packing.tex. Neither is needed by the executable proof checks.
The current note, including eighteen-form determinants, the translated interval and prime-progression transfer, compiled successfully in the desktop editor with
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
