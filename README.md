# Heilbronn triangle bounds: finite packings and improved scales

A conditional research draft by **[Ivan Blinov (@littleBro)](https://github.com/littleBro)**, extending [OpenAI math family 191](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-power-improvement-in-the-Heilbronn-triangle-lower-bound-September-25-2026), with OpenAI Codex assistance.

The current version combines centered-sphere packing with dimension d = 13 and smaller auxiliary scales. It gives the **conditional paper exponent**

$$
\Delta(n)\ge c\,n^{-2+\eta},\qquad
\boxed{\eta=\frac{1}{1074\cdot403^{17}+7}\approx4.77320332233169\cdot10^{-48}}.
$$

The claim is for every sufficiently large n, conditional on the pinned manuscript's geometric estimates. The complete finite packing and selected scale inequalities are proved in Lean; the full geometric theorem is not.

[Proof and review guide](docs/review.md) · [Current certificate](certificates/tuned.json) · [Lean proof](lean/Tuned.lean) · [Reproduction guide](docs/reproducibility.md)

Run all retained results with Python 3.11+, Git and the pinned Lean 4.11.0 toolchain:

    python scripts/verify_all.py

On systems with Make, make verify runs the same checks. The command also requires all six certificates and patches to regenerate byte for byte.

| Packing | k | Conditional paper exponent |
| --- | --- | --- |
| Pinned manuscript | T² + 1 | ≈ 3.17571403643291e-236 |
| Preserved ternary baseline | 3^384 | ≈ 2.68582462243153e-188 |
| Centered sphere | 40011^29 | ≈ 1.51508393214748e-138 |
| Retuned scales, d = 13 | 403^17 | ≈ 4.77320332233169e-48 |

The retuned exponent is approximately 3.15045471808690e90 times the previous sphere exponent, and 1.50303310297206e188 times the pinned manuscript exponent. These are comparisons of exponents in asymptotic lower bounds for minimum triangle area; thresholds and constants remain unspecified.

The current construction selects words of length 17 over 202 digits with the same centered squared norm, then encodes them in base 403. There are at most 85,851 energies, and Lean proves that one class contains at least the required T = binom(binom(51,13),3) words. The actual sphere is not enumerated.

## Current result: retuned scales

- [Proof and parameter transfer in the existing note](notes/sphere-packing.tex)
- [Lean proof of the new packing and integer scale inequalities](lean/Tuned.lean)
- [Exact certificate](certificates/tuned.json)
- [Patch for original manuscript Sections 3–8](patches/tuned-parameters.patch)
- [Verification report](artifacts/tuned-verification.json)

Regenerate and verify:

    python scripts/build_tuned.py
    python scripts/verify_tuned.py

The main changes are L = 400 k² r⁴, H = 2h, q between h¹⁴ and 2h¹⁴, and N = (hq)⁴. The conditional digit moment remains at most 2. All three degenerate zero-determinant cases still have bounded contributions. Taking rho = 1074k + 6 and sample growth r^gamma with gamma = rho/(2rho + 1) permits d = 13 and yields the displayed exponent.

Lean checks the complete new finite packing, the binomial formula for T, the capacity inequality, integer scale bounds, cleared-denominator deletion constraints, the exponent identity, and the gain enclosure. The verifier rebuilds the imported sphere proof, checks source hashes and patch applicability, and rejects four corrupted certificates and five parameter changes that break the stated sufficient bounds.

The field-norm, lattice, probability, asymptotic deletion, and interpolation arguments remain written conditional mathematics. They are not a complete Lean proof of the geometric theorem. The very small negative collision exponent can require enormous thresholds; no practical finite-size improvement is claimed.

## Preserved centered-sphere baseline, d = 41

- [Proof, transfer, and geometric interface review](notes/sphere-packing.tex)
- [Lean proof of the complete finite packing](lean/Sphere.lean)
- [Exact sphere certificate](certificates/sphere.json)
- [Sphere source patch](patches/sphere-packing.patch)
- [Sphere verification report](artifacts/sphere-verification.json)

Regenerate and verify the sphere-only baseline:

    python scripts/build_sphere.py
    python scripts/verify_sphere.py

**The complete finite sphere packing is now proved in Lean.** This includes the energy-layer bound, a finite pigeonhole theorem, selection of T distinct words from one layer, encoding, bounds, injectivity, and matching. The final theorem also checks T using the falling-factorial quotient definition of binomial coefficients. No sufficiently large sphere is assumed as a precondition, and the enormous set is never enumerated during proof checking.

The baseline theorem is paper_packing_binomial in Sphere.lean; the current specialization is tuned_packing in Tuned.lean. They use only standard Lean logical axioms; the numeric comparisons use no axioms. None of these versions formally proves the complete geometric theorem or parameter-comparison optimality.

The sphere idea is classical Behrend; stronger progression-free-set constructions are known ([Elsholtz, Hunter, Proske, Sauermann](https://arxiv.org/abs/2406.12290)). We claim neither a new sphere method nor unrestricted optimality. The certificate records a bounded comparison of dimensions 3–284 under its sufficient-capacity criterion.

All three source patches apply directly to the original manuscript and are alternatives; do not apply them cumulatively.

## Preserved ternary baseline

- A universal Lean proof of the replacement packing, including bounds, row injectivity, and the actual binary-index producer.
- Exact arithmetic for the manuscript's parameters, computed independently in two ways; Lean also checks capacity and denominator comparisons for the copied T literal.
- A written conditional transfer through the determinant coefficient, carries, conditional digit distribution, orbit inputs, deletion, and interpolation.
- A separate patch against the pinned manuscript. Original sources remain unchanged.

The full geometric theorem is conditional on the upstream estimates listed in the note. Our Lean file does not prove those estimates or the complete Heilbronn result. The original upstream Lean comparator uses a different exponent and a subsequence statement; it has not been rerun or modified.

The ternary progression-free construction is classical ([Moy and Rolnick, Section 4](https://arxiv.org/abs/1502.06013)). Novelty of this application, optimality, and independent mathematical review are not established.

## Read and review

- [Proof and dependency audit](notes/packing.tex)
- [Universal Lean proof](lean/Packing.lean)
- [Exact certificate](certificates/ternary.json)
- [Source patch](patches/ternary-packing.patch)
- [Verification results](artifacts/verification.json)
- [Source provenance and hashes](upstream/manifest.json)

The key substitution is m = ceil(log2(T)), k = 3^m. Write the binary digits of a as a ternary number u(a), and use positions u(a), u(a), k−1−2u(a) in the three rows. Their sum equals k−1 exactly when all three indices agree. At the manuscript's T, m = 384.

## Reproduce

Requirements: Python 3.11 or later (standard library only), Git, and native Lean 4.11.0. The local run used Python 3.14.4 on Windows. No Mathlib, WSL, parallel search, or geometric sampling workload is required. Install the pinned toolchain with elan before verification; see the [reproduction guide](docs/reproducibility.md).

From this directory:

    python scripts/verify_all.py

To regenerate the deterministic certificate and patch:

    python scripts/build_certificate.py
    python scripts/build_patch.py
    python scripts/verify.py

The verifier preserves upstream files, compiles only the local proof, rejects changed source hashes, and checks patch applicability. Its finite tests cover 21 packing sizes, 12 coefficient/carry examples, and six negative controls. Finite coverage is separate from the universal Lean theorem.

The arithmetic and packing checks do not independently validate the upstream paper. The preserved ternary proof uses a copied T literal checked by Python; the current sphere proof additionally checks its binomial formula inside Lean. See the respective proof notes for their scopes.

The proof notes are supplied as TeX. The local Codex compiler could not download its missing TeX bundle for either note, so compiled PDFs are not included. The environment failures are recorded in the two LaTeX status files under artifacts. They did not affect the Lean or Python checks.

The [GitHub Actions workflow](.github/workflows/verify.yml) runs the same checks on Ubuntu and saves verification reports. See [Actions](https://github.com/littleBro/heilbronn-triangle-bounds/actions/workflows/verify.yml) for the result on a particular commit. Local reports and remote runs record their own environments.

CI also scans Git history and checked-out files for exposed secrets before proof verification. See [the security controls and publication checklist](docs/security.md) and [security reporting](SECURITY.md).

## Review and citation

Corrections, independent reproduction and improvements are welcome; see [CONTRIBUTING.md](CONTRIBUTING.md). [The review guide](docs/review.md) maps each claim to its evidence and lists the remaining proof obligations. Use [CITATION.cff](CITATION.cff) and include the repository commit when citing a result.

## Attribution

Author: Ivan Blinov (@littleBro). Research, implementation and drafting used substantial OpenAI Codex assistance. The original manuscript is by OpenAI and is pinned at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. The classical constructions and upstream sources retain their attribution in the notes and [NOTICE](NOTICE).

The repository format was informed by [Swapnil Jain's integer-mult-kappa](https://github.com/Swapnil-jain/integer-mult-kappa) and [CrocSwap's integer-mult-bounds](https://github.com/CrocSwap/integer-mult-bounds). Their integer-multiplication results are not mathematical dependencies of this project.

Licensed under [Apache-2.0](LICENSE). This draft has no independent peer review, priority claim or OpenAI endorsement.
