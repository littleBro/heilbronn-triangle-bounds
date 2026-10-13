# Reviewing the current conditional result

The current target is

    Delta(n) >= c n^(-2 + eta), for every sufficiently large n,
    eta = 1 / (498 * 21725503513263 + 7) = 1 / 10819300749604981.

Read the translated-interval and eighteen-form sections of [the note](../notes/sphere-packing.tex)
and the [six-section source patch](../patches/trimmed-sphere.patch).
All original manuscript files remain pinned at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.

## Evidence for each claim

| Claim | Evidence | Boundary |
| --- | --- | --- |
| Eighteen symmetric products for a determinant pair | EighteenExpansion.pair_identity | Every commutative ring with u² − u + 1 = 0; multiplier 3 |
| Six pairs with one unpaired determinant | EighteenExpansion.paired_product, EighteenNorm.norm_expansion | Normalization 3^6 |
| T = 25 * 18^6 = 850,305,600 | EighteenNorm.finite_field_norm | Degree 13, at least 25 base-field elements, characteristic 3 excluded, required root |
| Homogeneous degree-13 coordinates | EighteenPolynomials.finite_field_polynomials | Coefficientwise descent preserves degree |
| Root existence and distinct-label criterion | EighteenPolynomials.root_exists, prime_field_labels | Every prime r >= 37 congruent to 1 mod 3 |
| Counting below an encoded cutoff | IntervalCounting.below_cons | Universal recurrence on actual finite words |
| Exact cutoff counts 10,596,664 and 860,902,264 | TrimmedLayer.below_lower, below_upper | 44 rows of 33 kernel-checked counts |
| Exactly T words in the interval | TrimmedLayer.exact_interval_count | Difference of the two cutoff counts |
| Selection, bounds, injections and matching | TrimmedPacking.translated_packing | k = 21,725,503,513,263; original digit radices retained |
| Gain greater than 1.0249 | TrimmedPacking.trimmed_gain | Integer comparison against the preserved eighteen-form checkpoint |
| Scale inequalities | Tuned.lean, Slab.lean, certificates/trimmed.json | Uniform arithmetic; geometry remains separate |
| Allowed prime in (m, 2m] eventually | PNT in arithmetic progressions, written derivation | Standard unconditional theorem; not formalized here |
| Slab, lattice, probability and deletion estimates | Written note and pinned manuscript | Not all formalized; no practical threshold or complete independent upstream audit |
| Reproduction | artifacts/repository-verification.json and individual reports | Applies to the recorded sources and environment |

The shared algebra audit covers 21 modules and 62 exported theorems. Only
propext, Classical.choice and Quot.sound are permitted. The root condition
is a hypothesis of the general algebraic identity; root existence is proved
for the prime progression in the exported specialization.
The interval checker additionally audits nine counting and packing theorems.
The generated finite table is connected to symbolic word counting; its
entries are checked in the kernel and are not assumed as hypotheses.

## The steps most useful to review

- Compare the explicit forms to [CGLV, Theorem 4.1](https://arxiv.org/abs/1909.04785).
  The second coefficient column is multiplied by three. Check the resulting
  pair multiplier 3 directly; do not infer normalization from tensor notation.
- Check all 729 tensor coefficients over Z[u]/(u² − u + 1). For the Lean
  identity the same bilinear form appears in every column.
- Enumerate one singleton and six disjoint pairs, then apply 25-node descent.
  Include 3^(-6) in one row only.
- Verify Cauchy's order-three element gives u = -z. The prime restriction
  cannot be removed: for example r = 41 has no root in its degree-13 extension.
- Count the coefficient of z^32 in
  (2 sum_{j=0}^4 z^(j(j+1)/2))^4 * (2 sum_{j=0}^3 z^(j(j+1)/2))^7.
  The full histogram and a separate multinomial count agree.
- Read the half-alphabets in the current order [4,4,4,4,4,4,5,4,5,5,5].
  With the original radices 4A - 1, no digit sums carry and equal norm 267
  forces midpoint rigidity.
- For the interval [133966008273, 10996717764905), check both cutoff counts.
  After choosing the low digit d in radix b, the remaining cutoff is
  floor(B/b) + 1_{d < B mod b}. The independent checker reads high digits first.
- Subtract the lower endpoint before setting v = k - 1 - 2u.
  The upper cutoff is exclusive, so k = 2(upper - lower) - 1.
  Omitting either endpoint loses a word; omitting the translation breaks
  the right-position bound. The final k is not the digit radix product.
- For all-cardinalities interpolation, use pi(x;3,1) ~ x/(2 log x).
  Then pi(2m;3,1) - pi(m;3,1) ~ m/(2 log m) > 0 eventually.
  This written use of the [standard theorem](https://dlmf.nist.gov/27.11)
  is separate from the Lean proof. B and q use ordinary Bertrand intervals.

The new bounded search evaluates 313,427 intervals on finite grids over
330 coordinate orders and energies 32, 33 and 34. It does not check every
possible interval. The proof checker validates the exact witness independently;
no interval optimum, global packing optimum or new determinant formula is claimed.
Independent controls compare 13,583 small cutoff counts with enumeration
and check 42,216 matching triples. All 1,452 saved count entries are also
recomputed by the separate lexicographic algorithm.

The checkers apply the rank-five, paired, eighteen-form and interval patches to
separate ignored text copies, then checks all 58 referenced labels in each
manuscript. A negative control removes the matching label and must fail.
The two earlier patches now explicitly restore the row-position definitions
and name the power-basis coordinates used by the retained source.

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
5. Cardinality grows as r^(rho + gamma). The two-sided bound, the prime
   interval for r = 1 mod 3 and taking subsets give every sufficiently large n without
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
