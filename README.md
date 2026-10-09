# Heilbronn triangle bounds: finite packings and improved scales

A conditional research draft by **[Ivan Blinov (@littleBro)](https://github.com/littleBro)**, extending [OpenAI math family 191](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-power-improvement-in-the-Heilbronn-triangle-lower-bound-September-25-2026), with OpenAI Codex assistance.

The current version applies a classical five-term determinant formula, groups its norm expansion into Galois orbits, and uses a mixed-radix sphere. With the retained slab scales at d = 13, this gives the **conditional paper exponent**

$$
\Delta(n)\ge c\,n^{-2+\eta},\qquad
\boxed{\eta=\frac{1}{498\cdot39\cdot35^8+7}\approx2.28644993011544\cdot10^{-17}}.
$$

The claim is for every sufficiently large n, conditional on the pinned manuscript's geometric estimates. Lean proves the complete new norm decomposition, interpolation descent, homogeneous polynomial coordinates and nonzero residue for distinct labels. It also proves the finite packing and selected scale inequalities. The slab geometry, lattice and probability estimates, and full Heilbronn theorem remain outside the formal proof.

[Proof and review guide](docs/review.md) · [Current certificate](certificates/rankfive.json) · [Lean algebra proof](lean/RankFivePolynomials.lean) · [Lean packing proof](lean/RankFivePacking.lean) · [Reproduction guide](docs/reproducibility.md)

Run all retained results with Python 3.11+, Git and the pinned Lean 4.11.0 toolchain:

    python scripts/prepare_mathlib.py
    python scripts/verify_all.py

The first command prepares pinned Mathlib dependencies and compiled imports; run it once per fresh checkout. On systems with Make, make verify runs the checks after this setup. Verification also requires all twenty generated certificates, patches and count-table files to regenerate byte for byte.

| Packing | k | Conditional paper exponent |
| --- | --- | --- |
| Pinned manuscript | T² + 1 | ≈ 3.17571403643291e-236 |
| Preserved ternary baseline | 3^384 | ≈ 2.68582462243153e-188 |
| Centered sphere | 40011^29 | ≈ 1.51508393214748e-138 |
| Retuned scales, d = 13 | 403^17 | ≈ 4.77320332233169e-48 |
| Slab cap, d = 13 | 403^17 | ≈ 1.02940168035828e-47 |
| Central energy interval, d = 13 | 379^17 | ≈ 2.92350666167202e-47 |
| Compressed norm, d = 13 | 47^10 | ≈ 3.81761455590365e-20 |
| Bilinear descent and exact layer, d = 13 | 27^11 | ≈ 3.61217890050488e-19 |
| Galois-orbit compression, d = 13 | 27^10 | ≈ 9.75288303136317e-18 |
| Five-term determinant and mixed sphere, d = 13 | 39 * 35^8 | ≈ 2.28644993011544e-17 |

The current exponent is **about 2.344 times** the preceding Galois-orbit exponent. These compare exponents in asymptotic lower bounds for minimum triangle area; thresholds and constants remain unspecified.

## Current result: five-term determinant and mixed sphere

The [Krishna–Makam integral formula](https://arxiv.org/abs/1801.00496), Section 3.1, writes a 3-by-3 determinant as five products of linear forms. Expand the thirteen conjugate determinants with this formula, then antisymmetrize the three columns. Because thirteen is odd, the resulting sum of determinants is **six times** the norm. Lean proves the formula and this normalization over any commutative ring.

The five-letter words have five constant fixed patterns. All other Galois orbits have size 13, giving **Q = (5^13 + 60)/13 = 93,900,245** classes. Invariant projection and the existing 25-node descent give **T = 25Q = 2,347,506,125** base-field determinants. Each class is weighted by its size divided by six. The full norm identity, homogeneous degree-13 polynomial coordinates and distinct-label criterion are proved in Lean for every prime r >= 37. The general theorem excludes characteristics 2, 3 and 13.

For packing, use one coordinate with 20 digits and eight with 18 digits, encoded with radices 39 and 35. The energy-119 layer has exactly **2,365,025,280** words and common squared norm 961. Lean checks the counting recurrence and proves selection, bounds, injectivity and matching for this mixed-radix sphere. Thus **k = 39 * 35^8 = 87,823,140,234,375** and **eta = 1/43,735,923,836,718,757**.

- [Five-term identity and antisymmetrization](lean/RankFiveExpansion.lean)
- [Five-letter orbits and their exact count](lean/RankFiveOrbits.lean)
- [Universal norm identity](lean/RankFiveNorm.lean) and [homogeneous coordinates](lean/RankFivePolynomials.lean)
- [Mixed-radix sphere](lean/MixedSphere.lean), [exact layer](lean/MixedLayer.lean) and [complete packing](lean/RankFivePacking.lean)
- [Certificate](certificates/rankfive.json), [alternative manuscript patch](patches/rank-five.patch) and [verification report](artifacts/rankfive-verification.json)

    python scripts/build_rankfive.py
    python scripts/verify_rankfive.py

Independent controls enumerate the full expansion in degrees 3 and 5, sample degree 13, and reject a missing factor 1/6, omitted orbit weights and a non-invariant projection. A separate multinomial count agrees with the sphere coefficient. Small mixed spheres are exhaustively checked; an explicit counterexample rejects reducing radix 27 to 26 without a new argument. The shared algebra audit now rebuilds fifteen modules and checks 45 exported theorems once per complete verification run. The five-term formula is prior work; novelty and global optimality of this application are not claimed.

## Preserved Galois-orbit compression

The 6^12 normalized determinant terms have a Galois action. Their signed values transform by the corresponding field automorphism. Exactly one pattern is fixed, and every other orbit has size 13, giving (6^12 + 12)/13 = 167,444,796 classes. Lean proves both the action and this count symbolically.

Average the power-basis constant-coordinate functional over the 13 automorphisms. This invariant linear map fixes the base field, so the norm is the sum of one projected representative per class, weighted by the class size. Applying 25-node bilinear descent gives **T = 4,186,119,900** base-field determinants. The singleton also receives 25 nodes. The exact norm identity, homogeneous degree-13 coordinates and distinct-label criterion are all proved in Lean for every prime r >= 37. The general finite-field theorem explicitly excludes characteristic 13, where this averaging would require division by zero.

The energy-80 layer of 10-digit words over 14 digits contains **5,058,395,136** words, with squared centered norm 650. The existing kernel-checked recurrence table supplies this count. It is enough for T and gives k = 27^10 = 205,891,132,094,649, so the exponent is exactly **1/102,533,783,783,135,209**. The slab scales and remaining geometric assumptions are unchanged.

- [Written proof and retained parameter transfer](notes/sphere-packing.tex)
- [Group action, fixed patterns and exact class count](lean/FrobeniusOrbits.lean)
- [Signed equivariance and invariant projection](lean/FrobeniusNorm.lean)
- [Orbit-weighted norm descent](lean/FrobeniusDescent.lean)
- [Homogeneous coordinates and distinct-label theorem](lean/FrobeniusPolynomials.lean)
- [Exact layer, complete finite packing and gain](lean/FrobeniusPacking.lean)
- [Exact certificate](certificates/frobenius.json)
- [Alternative patch for original manuscript Sections 3–8](patches/frobenius-orbits.patch)
- [Verification report](artifacts/frobenius-verification.json)

Regenerate and verify:

    python scripts/build_frobenius.py
    python scripts/verify_frobenius.py

Independent controls enumerate all patterns in degrees 3 and 5, test signed equivariance and orbit-weighted norm sums, and check sampled patterns and all basis vectors in degree 13. Negative controls reject omitted orbit weights and a non-invariant projection; degree 3 correctly has three fixed patterns. The layer is also counted by an independent multinomial sum. At this checkpoint the algebra audit covered eleven modules and 31 exported theorems, with no additional mathematical assumptions admitted. Novelty and unrestricted optimality are not claimed.

## Preserved bilinear descent and exact layer

The determinant expansion still gives 6^12 terms over the extension field. To descend a term to the base field, interpolate the product of its first two rows' representatives, each of degree at most 12. That product has degree at most 24, so 25 nodes suffice. The third row uses the linear functional z -> ell(L_t(theta) z). Expanding the six signed products proves the determinant identity with different linear maps in the rows.

This gives T = 25 * 6^12 = 54,419,558,400. The new Lean theorem preserves the exact field norm, homogeneous degree-13 coordinates and the nonzero criterion for three distinct labels. It holds for every prime r >= 25; the manuscript patch retains r >= 37 and all previous slab scales.

For packing, use 11-digit words over 14 digits, encoded in base 27. The layer with energy index 86, or squared centered norm 699, contains exactly 67,169,169,408 words, enough for T. Lean proves the symbolic counting recurrence, checks eleven transitions of an 87-entry table, selects distinct words and proves the complete packing at k = 27^11. It never enumerates the 14^11 words.

- [Written proof and retained parameter transfer](notes/sphere-packing.tex)
- [25-node interpolation and determinant descent](lean/BilinearDescent.lean)
- [Universal norm, homogeneous coordinates and distinct-label proofs](lean/BilinearNorm.lean)
- [Exact layer and complete finite packing](lean/ExactLayer.lean)
- [Exact certificate](certificates/bilinear.json)
- [Alternative patch for original manuscript Sections 3–8](patches/bilinear-layer.patch)
- [Verification report](artifacts/bilinear-verification.json)

Regenerate and verify:

    python scripts/build_bilinear.py
    python scripts/verify_bilinear.py

The independent checker counts the layer both by a full energy distribution and by a multinomial sum over digit multiplicities. It checks exhaustive products of lengths 0 through 3. Field controls check all basis products and five determinants in each of three extensions of degrees 3, 5 and 13; negative controls detect insufficient nodes, a corrupted interpolation element and an incorrect third-row map. This checkpoint contributes two algebra modules with seven exported theorems to the shared audit.

The descent uses elementary polynomial interpolation for multiplication, within the classical framework of [bilinear complexity](https://arxiv.org/abs/1107.0336). The chosen packing is a feasible witness; novelty and unrestricted optimality are not claimed.

## Preserved 37-node norm compression

The norm polynomial is a product of d conjugate 3-by-3 determinants. In its permutation expansion, normalize the first permutation to the identity. Because d = 13 is odd, each group of six terms is a determinant, leaving 6^12 determinants over the extension field.

To express them over the base field, represent coefficients in a power basis of degree 13. Each resulting determinant is a polynomial of degree at most 36 in the basis variable. Interpolation at 37 distinct base-field nodes, followed by a linear projection fixing the base field, expresses it as at most 37 base-field determinants. This projects the whole determinant, rather than assuming that entrywise projection preserves it. It requires only primes r >= 37.

The result is the same exact norm identity with T = 37 * 6^12 homogeneous polynomials per row. The distinct-label obstruction and the conditional digit estimate retain their original interfaces; the latter already permits arbitrary functions of the labels. With the existing slab scales, eta remains 1/(498k + 7), now at k = 47^10.

- [Written algebraic proof and downstream interface review](notes/sphere-packing.tex)
- [Universal field-norm decomposition](lean/NormAlgebra.lean)
- [Homogeneous polynomial coordinates](lean/NormPolynomials.lean)
- [Distinct-label theorem for every prime r >= 37](lean/NormVandermonde.lean)
- [Lean permutation bookkeeping and complete finite packing](lean/NormCompression.lean)
- [Exact certificate](certificates/norm.json)
- [Alternative patch for original manuscript Sections 3–8](patches/norm-compression.patch)
- [Verification report](artifacts/norm-verification.json)
- [Algebra proof and dependency audit](artifacts/algebra-verification.json)

Regenerate and verify:

    python scripts/build_norm.py
    python scripts/verify_norm.py

The original decomposition occupies five algebra modules with ten exported theorems; the shared checker also rebuilds and audits the bilinear and Galois-orbit modules against the pinned Mathlib version. The final theorem uses Mathlib's actual field norm and supplies the power basis, automorphisms and interpolation nodes from finite-field hypotheses. It proves one family of coordinates works for every label triple. The corresponding polynomials are homogeneous of degree 13.

Independent finite controls test the full decomposition on four matrices each over F_(11^3) and F_(17^5), including distinct Vandermonde labels. They check descent on all 37 basis monomials and four matrices over F_(41^13), without enumerating the degree-13 norm expansion. Negative controls detect omitted signs, entrywise projection, insufficient nodes, corrupted weights and the even-degree sign error. These controls supplement the universal Lean proof. No novelty or optimality claim is made.

## Preserved second-moment count

For each digit t, put j(t) = ((2t − 189)² − 1)/8. Its mean is 1504, so the energy index J of a word has mean 25,568. The sum of squared centered digit scores is 343,855,008. Over all 190^17 words, the second moment is

    V = 17 * 190^16 * 343855008.

Outside 15,568 <= J <= 35,568, the centered score has absolute value at least 10,001. At most floor(V/10001²) words lie outside. The exact inequality

    V + 20001 * T * 10001² <= 190^17 * 10001²

therefore supplies a large enough energy layer. The existing carry-free encoding and slab scales give k = 379^17 and eta = 1/(498k + 7).

- [Written proof and parameter transfer](notes/sphere-packing.tex)
- [Lean proof from symbolic moments through complete packing](lean/Central.lean)
- [Exact certificate](certificates/central.json)
- [Patch for original manuscript Sections 3–8](patches/central-sphere.patch)
- [Verification report](artifacts/central-verification.json)

Regenerate and verify:

    python scripts/build_central.py
    python scripts/verify_central.py

The checker independently propagates moments, tests six small Cartesian products, rejects six corrupted certificates, rebuilds the Lean dependencies, audits logical axioms and checks patch applicability. Lean evaluates only the 190 digit scores and a 17-step recurrence. The parameter choice is an explicit feasible witness; no optimality claim is made.

## Preserved slab cap

The short-relation exclusion in upstream Section 5 only bounds the first coordinate. Take

    S = {(x, y, x² − νy²): 0 <= x < w, y in F_q},

where ν is a nonsquare and w = floor(q/(1000 H²)). This is a subset of the same elliptic paraboloid, with no three collinear points and exactly wq points. The allowed shifts and inclusion-probability argument still apply. Thus s >= q²/(2000 H²), improving the previous q²/(2000³ H⁶) bound.

With H = 2h, the three degenerate losses become h⁶/q, h⁴/q and h⁶/q². They stay bounded for h⁶ < q <= 2h⁶. Keeping the digit scale and N = (hq)⁴ gives rho = 498k + 6 and eta = 1/(498k + 7). This checkpoint uses k = 403^17; the current version retains the slab argument with the smaller packing.

- [Written cap proof and full parameter transfer](notes/sphere-packing.tex)
- [Lean proofs of the new integer inequalities](lean/Slab.lean)
- [Exact certificate, referencing the retained packing](certificates/slab.json)
- [Patch for original manuscript Sections 3–8](patches/slab-cap.patch)
- [Verification report](artifacts/slab-verification.json)

Regenerate and verify:

    python scripts/build_slab.py
    python scripts/verify_slab.py

The checker independently derives the rational exponent, checks small caps and allowed shifts, rejects corrupted certificates and invalid scale choices, rebuilds the Lean dependencies and checks the patch against the original sources. Lean proves the floor-width and cardinality bounds, the modulus and zero-case inequalities, the deletion arithmetic, and an exact gain between 2.15 and 2.16. The cap geometry itself is a written proof, with finite checks as supporting evidence.

## Preserved retuned scales, d = 13

- [Proof and parameter transfer in the existing note](notes/sphere-packing.tex)
- [Lean proof of the new packing and integer scale inequalities](lean/Tuned.lean)
- [Exact certificate](certificates/tuned.json)
- [Patch for original manuscript Sections 3–8](patches/tuned-parameters.patch)
- [Verification report](artifacts/tuned-verification.json)

Regenerate and verify:

    python scripts/build_tuned.py
    python scripts/verify_tuned.py

The checkpoint changes are L = 400 k² r⁴, H = 2h, q between h¹⁴ and 2h¹⁴, and N = (hq)⁴. The conditional digit moment remains at most 2. All three degenerate zero-determinant cases have bounded contributions. Taking rho = 1074k + 6 and sample growth r^gamma with gamma = rho/(2rho + 1) permits d = 13 and yields the retained exponent 1/(1074k + 7).

Lean checks the complete new finite packing, the binomial formula for T, the capacity inequality, integer scale bounds, cleared-denominator deletion constraints, the exponent identity, and the gain enclosure. The verifier rebuilds the imported sphere proof, checks source hashes and patch applicability, and rejects four corrupted certificates and five parameter changes that break the stated sufficient bounds.

This checkpoint's transfer of the original decomposition, lattice, probability, asymptotic deletion and interpolation estimates remains a written conditional argument. The current compressed decomposition has the separate Lean proof described above; the full geometric theorem is still not formalized. The very small negative collision exponent can require enormous thresholds; no practical finite-size improvement is claimed.

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

The baseline theorem is paper_packing_binomial in Sphere.lean; the retuned specialization is tuned_packing in Tuned.lean. The central-layer checkpoint is central_packing_binomial in Central.lean. The 37-node checkpoint is norm_packing in NormCompression.lean; the bilinear checkpoint is bilinear_packing in ExactLayer.lean. The Frobenius checkpoint is trace_packing in FrobeniusPacking.lean; the current theorem is trace_packing in RankFivePacking.lean. They use only standard Lean logical axioms; the numeric comparisons use no axioms. None of these versions formally proves the complete geometric theorem or parameter-comparison optimality.

The sphere idea is classical Behrend; stronger progression-free-set constructions are known ([Elsholtz, Hunter, Proske, Sauermann](https://arxiv.org/abs/2406.12290)). We claim neither a new sphere method nor unrestricted optimality. The certificate records a bounded comparison of dimensions 3–284 under its sufficient-capacity criterion.

All eight source patches apply directly to the original manuscript and are alternatives; do not apply them cumulatively.

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

Requirements: Python 3.11 or later (standard library only), Git, and native Lean 4.11.0. The algebra proof uses Mathlib at commit 20c73142afa995ac9c8fb80a9bb585a55ca38308 (v4.11.0), with all seven dependency revisions locked. The earlier packing and scale proofs still use core Lean. The local run used Python 3.14.4 on Windows; no WSL, parallel search or geometric sampling workload is required. See the [reproduction guide](docs/reproducibility.md).

From this directory:

    python scripts/prepare_mathlib.py
    python scripts/verify_all.py

To regenerate the deterministic certificate and patch:

    python scripts/build_certificate.py
    python scripts/build_patch.py
    python scripts/verify.py

The verifier preserves upstream files, compiles only the local proof, rejects changed source hashes, and checks patch applicability. Its finite tests cover 21 packing sizes, 12 coefficient/carry examples, and six negative controls. Finite coverage is separate from the universal Lean theorem.

The arithmetic and packing checks do not independently validate the upstream paper. The preserved ternary proof uses a copied T literal checked by Python; the earlier sphere proofs check their binomial counts inside Lean. The current packing uses T = 25 * (5^13 + 60)/13 with an exactly counted mixed-radix layer. See the respective proof notes for their scopes.

The proof notes are supplied as TeX. The current note, including norm compression, compiled successfully with the built-in Tectonic 0.17.0+20260731 after installing its support bundle from the [official v33 mirror](https://github.com/tectonic-typesetting/tectonic-relay-service/blob/main/temporary_redirects.map). The source hash and bundle identity are recorded in [the compilation report](artifacts/sphere-latex-status.json). Generated note PDFs are not included. The separate artifacts/latex-status.json retains the earlier ternary-note attempt. Note compilation is separate from the Lean and Python checks.

The [GitHub Actions workflow](.github/workflows/verify.yml) runs the same checks on Ubuntu and saves verification reports. See [Actions](https://github.com/littleBro/heilbronn-triangle-bounds/actions/workflows/verify.yml) for the result on a particular commit. Local reports and remote runs record their own environments.

CI also scans Git history and checked-out files for exposed secrets before proof verification. See [the security controls and publication checklist](docs/security.md) and [security reporting](SECURITY.md).

## Review and citation

Corrections, independent reproduction and improvements are welcome; see [CONTRIBUTING.md](CONTRIBUTING.md). [The review guide](docs/review.md) maps each claim to its evidence and lists the remaining proof obligations. Use [CITATION.cff](CITATION.cff) and include the repository commit when citing a result.

## Attribution

Author: Ivan Blinov (@littleBro). Research, implementation and drafting used substantial OpenAI Codex assistance. The original manuscript is by OpenAI and is pinned at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. The classical constructions and upstream sources retain their attribution in the notes and [NOTICE](NOTICE).

The repository format was informed by [Swapnil Jain's integer-mult-kappa](https://github.com/Swapnil-jain/integer-mult-kappa) and [CrocSwap's integer-mult-bounds](https://github.com/CrocSwap/integer-mult-bounds). Their integer-multiplication results are not mathematical dependencies of this project.

Licensed under [Apache-2.0](LICENSE). This draft has no independent peer review, priority claim or OpenAI endorsement.
