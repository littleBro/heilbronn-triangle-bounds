# Reviewing the current conditional result

The current target is

    Delta(n) >= c n^(-2 + eta), for every sufficiently large n,
    eta = 1 / (498 * 39 * 35^8 + 7) = 1 / 43735923836718757.

This is a conditional refinement of the pinned OpenAI family 191 argument.
Read the five-term determinant and mixed-radix section of [the note](../notes/sphere-packing.tex)
and the [six-section source patch](../patches/rank-five.patch).
All original manuscript files remain pinned at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.

## Evidence for each claim

| Claim | Evidence | Boundary |
| --- | --- | --- |
| Integral five-term formula | RankFiveExpansion.rank_five | Known Krishna--Makam identity; proved over any commutative ring |
| Antisymmetrized product is six times the norm | RankFiveExpansion.antisymmetrized_product and RankFiveNorm.norm_pattern_sum | Odd degree 13 is essential; the factor six is retained |
| Five fixed words and 93,900,245 orbits | RankFiveOrbits.fixed_pattern, orbit_size, class_card | Plain rotation of five-letter words indexed by a group of order 13 |
| T = 2,347,506,125 norm determinants | RankFiveNorm.finite_field_trace_norm | Degree 13, at least 25 base-field elements, characteristics 2, 3 and 13 excluded |
| Homogeneous coordinates and distinct-label criterion | RankFivePolynomials.finite_field_trace_polynomials and prime_field_trace_labels | Proved for every prime r >= 37, using the actual Mathlib field norm |
| Exact energy-119 coefficient 2,365,025,280 | MixedLayer.exact_layer_count | Nine kernel-checked histogram transitions tied to symbolic counting |
| Mixed-radix rigidity and bounds | MixedSphere.sphere_matching and position_bounds | Radix 4A-1 separately in each coordinate |
| Selection, injections and matching | RankFivePacking.trace_packing | T specified above, k = 39 * 35^8; layer capacity is proved |
| Gain greater than 2.34 | RankFivePacking.trace_gain | Exact integer comparison against the preceding Frobenius checkpoint |
| Scale inequalities | Tuned.lean, Slab.lean, certificates/rankfive.json | Uniform integer bounds; lattice and probability arguments remain separate |
| Slab geometry and weighted counts | Written note, pinned manuscript Sections 2 and 4--7 | Not formalized in Lean; no complete independent audit of all upstream estimates |
| Deletion and all sufficiently large n | Written transfer and patched Section 8 | Conditional geometric consequence; no practical threshold |
| Reproduction | artifacts/repository-verification.json and linked reports | Specific to the recorded sources and environment |

New declarations use HeilbronnRankFive, HeilbronnMixedSphere,
HeilbronnMixedLayer and HeilbronnRankFivePacking. The shared algebra audit
covers fifteen Mathlib-based modules and 45 exported theorems. Only propext,
Classical.choice and Quot.sound are permitted; no mathematical assumptions
are introduced to stand in for the claimed norm or packing identities.

## The steps most useful to review

- Check the five explicit products against the determinant. The formula is
  from [Krishna and Makam, Section 3.1](https://arxiv.org/abs/1801.00496).
- Expand the thirteen conjugates, then antisymmetrize columns. Odd degree
  makes each signed permuted norm equal to the original norm, giving six
  copies. Division by six is required and is covered by a negative control.
- Rotate w by (a.w)(g) = w(a^-1 g). The determinant value transforms by a.
  Exactly five words are constant; every other orbit has size thirteen.
- Use the invariant projection L(z) = sum_a ell(a(z))/13 and weight each
  representative by its orbit size divided by six. The general field theorem
  explicitly assumes 6 and 13 nonzero. Cardinality alone would not imply this.
- Reuse 25-node interpolation of the first two power-basis representatives,
  followed by L(c_t z) in the third row. All five singleton classes also use
  25 nodes. Coefficientwise linear maps retain degree-thirteen homogeneity.
- Count the coefficient of z^119 in
  (2 sum_{j=0}^9 z^(j(j+1)/2)) * (2 sum_{j=0}^8 z^(j(j+1)/2))^8.
  Truncation above 119 is valid because every digit energy is nonnegative.
  The independent multinomial calculation gives the same integer.
- With half-alphabets [10,9,9,9,9,9,9,9,9], use radices [39,35,35,35,35,35,35,35,35].
  Each digit sum stays below its own radix. Equal norms then force equality
  of all three words. Selection and injectivity are proved, not assumed.

The mixed sphere has squared norm 961 and enough words for T. Its parameters
are an explicit feasible witness, without a global optimality claim.

The retained slab transfer is unchanged:

1. The conditional digit moment only needs theta <= 1/2. With
   L = 400 k^2 r^4, B is of order r^12 with fixed k-dependent constants.
2. The explicit slab of the elliptic paraboloid has exactly wq points.
   The allowed shifts, zero exclusion and nonzero-sum short-relation argument
   use only the first coordinate; the zero-sum case uses the cap property.
   Check that the three inclusion-probability bounds need no other box constraint.
3. H = 2h puts every affine-residue shell in the unchanged R >= h moment range.
   The cap has q >= 2000 H^2 when h >= 10 and q > h^6. Its size bound gives
   zero-determinant losses h^6/q, h^4/q and h^6/q^2. Boundedness is sufficient.
4. For N = (hq)^4 and gamma = rho/(2 rho + 1), rho = 498k + 6,
   pair and triple deletion have negative powers gamma - 6(k - 1) and
   2 gamma - 1. The latter is extremely close to zero.
5. Cardinality grows as r^(rho + gamma). The two-sided bound, Bertrand's
   interval and taking subsets give every sufficiently large n without
   assuming that the sampled cardinalities are monotone.

The exponent comparison does not control the hidden constants or the threshold
for n. It does not establish a practical finite-size configuration, priority,
independent peer review or unrestricted optimality.

## Previous results and attribution

The ternary, d = 41 sphere, d = 13 retuning, slab, central-layer, 37-node norm
and bilinear-layer variants retain their own
certificates, Lean files, patches and checkers. They are useful checkpoints and
use their own parameters. The sphere method is classical Behrend, the moment
count is elementary, and the slab is a subset of the classical elliptic
paraboloid already used upstream. The norm regrouping and interpolation use
elementary algebra. The new descent uses classical polynomial-interpolation
multiplication, within the framework of [bilinear complexity](https://arxiv.org/abs/1107.0336);
novelty of this application is not established.

The repository format was informed by
[Swapnil Jain's integer-mult-kappa](https://github.com/Swapnil-jain/integer-mult-kappa)
and [CrocSwap's integer-mult-bounds](https://github.com/CrocSwap/integer-mult-bounds).
Those projects concern a different problem; their multiplication estimates are
not assumptions of this Heilbronn construction.

The unchanged upstream Lean comparator has a different exponent and a subsequence
target. This repository's certificates concern the manuscript exponent; they do
not constitute a completed proof of that comparator.
