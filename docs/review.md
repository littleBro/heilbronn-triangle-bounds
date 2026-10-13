# Reviewing the current conditional result

The current target is

    Delta(n) >= c n^(-2 + eta), for every sufficiently large n,
    eta = 1 / (498 * 27 * 23^9 + 7) = 1 / 24218298686031505.

This is a conditional refinement of the pinned OpenAI family 191 argument.
Read the paired-determinant section of [the note](../notes/sphere-packing.tex)
and the [six-section source patch](../patches/paired-norm.patch).
All original manuscript files remain pinned at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.

## Evidence for each claim

| Claim | Evidence | Boundary |
| --- | --- | --- |
| Twenty symmetric products for a determinant pair | PairedExpansion.pair_identity | Integral identity over every commutative ring, from the classical five-term formula and polarization |
| Six pairs with one unpaired determinant | PairedExpansion.paired_product, PairedNorm.norm_expansion | Normalization 4^6; no extra factor five for the singleton |
| T = 25 * 20^6 = 1,600,000,000 base-field terms | PairedNorm.finite_field_norm | Degree 13, at least 25 base-field elements, characteristic two excluded |
| Homogeneous degree-13 coordinates | PairedPolynomials.finite_field_polynomials | Coefficientwise descent preserves degree |
| Nonzero residue precisely for distinct labels | PairedPolynomials.prime_field_labels | Actual Mathlib field norm; every prime r >= 37 |
| Exact energy-59 count 1,641,775,104 | PairedLayer.exact_layer_count | Ten kernel-checked histogram transitions tied to symbolic counting |
| Selection, bounds, injections and matching | PairedPacking.trace_packing | k = 27 * 23^9; uses the general MixedSphere proof |
| Gain greater than 1.80 | PairedPacking.trace_gain | Exact integer comparison against the preserved rank-five checkpoint |
| Scale inequalities | Tuned.lean, Slab.lean, certificates/paired.json | Uniform arithmetic; geometric estimates remain separate |
| Slab, lattice, probability and deletion estimates | Written note and pinned manuscript | Not all formalized; no practical threshold or complete independent upstream audit |
| Reproduction | artifacts/repository-verification.json and individual reports | Applies to the recorded sources and environment |

The shared algebra audit covers eighteen Mathlib-based modules and 53 exported
theorems. Only propext, Classical.choice and Quot.sound are permitted. No
assumption stands in for a claimed norm or finite packing identity.

## The steps most useful to review

- Expand the 20 bilinear forms using the coefficient arrays of the
  [Krishna–Makam formula](https://arxiv.org/abs/1801.00496).
  Check that the same form is used in all three columns and that the
  normalization is four, not six.
- Enumerate the automorphisms by one singleton and six disjoint pairs.
  Every conjugate occurs once. A common factor in each column scales the
  unpaired determinant directly; it need not be expanded into five products.
- Apply the constant-coordinate functional, which fixes the base field,
  and 25-node interpolation of the first two rows. The third row is
  constantCoord(c_t * input). Include the factor 4^(-6) in one row only.
- Count the coefficient of z^59 in
  (2 sum_{j=0}^6 z^(j(j+1)/2)) * (2 sum_{j=0}^5 z^(j(j+1)/2))^9.
  The full digit histogram and a separate multinomial calculation agree.
- With half-alphabets [7,6,6,6,6,6,6,6,6,6], use radices [27,23,23,23,23,23,23,23,23,23].
  Each digit sum is below its radix; equal norm 482 forces midpoint rigidity.
  Selection, both injections and matching are proved in Lean.

The bounded search in artifacts/packing-search.json is not an optimality proof.
The proof checker validates the chosen witness independently of that search.

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
