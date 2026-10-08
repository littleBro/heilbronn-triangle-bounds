# Reviewing the current conditional result

The current target is

    Delta(n) >= c n^(-2 + eta), for every sufficiently large n,
    eta = 1 / (498 * 27^10 + 7) ≈ 9.75288303136317e-18.

This is a conditional refinement of the pinned OpenAI family 191 argument.
Read the Galois-orbit and invariant-projection section of [the note](../notes/sphere-packing.tex)
and its retained slab transfer, together with the
[six-section source patch](../patches/frobenius-orbits.patch).
The original manuscript and comparator are retained in upstream/ at commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.

## Evidence for each claim

| Claim | Evidence | Boundary |
| --- | --- | --- |
| Galois action and 167,444,796 classes | FrobeniusOrbits.fixed_pattern, orbit_size and class_card | Exactly one fixed pattern; all other orbits have size 13 |
| Signed equivariance and invariant projection | FrobeniusNorm.patternTerm_rotate and averagedCoord_invariant | Row-permutation signs cancel; the average fixes the base field when 13 is invertible |
| Norm decomposition with T = 4,186,119,900 | FrobeniusDescent.finite_field_trace_norm | Degree-13 finite extension, at least 25 base-field elements, characteristic different from 13; uses Mathlib's field norm |
| Bilinear descent using 25 nodes | FrobeniusDescent.projected_determinant | Arbitrary linear functional L; applies L(c_t z) in the third row |
| Homogeneous degree-13 base-field polynomials | FrobeniusPolynomials.finite_field_trace_polynomials | Fully proved homogeneity and exact norm identity for all coordinate triples; supplies basis and nodes |
| Exact number of words at energy index 80 | FrobeniusPacking.exact_layer_count | Uses the existing kernel-checked recurrence table; 5,058,395,136 words |
| Positions, row injections and exact matching | FrobeniusPacking.trace_packing | Fully proved for T = 4,186,119,900 and k = 27^10, including selection of distinct equal-energy words |
| Count and gain | FrobeniusDescent.trace_term_card and FrobeniusPacking.trace_gain | Exact term count and 26.99 < gain over the bilinear checkpoint < 27 |
| Digit and auxiliary scale inequalities | Tuned.lean, Slab.lean, certificates/frobenius.json | Integer inequalities uniform in k; probability and lattice arguments are separate |
| Slab cap size and short-relation exclusion | New written lemma and proof in the note and patched Section 5 | Finite-field geometry is not in Lean; small cases are independently checked |
| Nonzero norm for distinct labels at d = 13 | FrobeniusPolynomials.prime_field_trace_labels | Fully proved for every prime r >= 37; nonzero if and only if the three labels are distinct |
| Lattice, orbit and weighted counts | Pinned Sections 2 and 4–7, with the slab lemma and changed scale checks | Relied upon; no complete independent theorem audit |
| Deletion and all sufficiently large cardinalities | Written note and patched Section 8 | The asymptotic and geometric proof is not in Lean |
| Current sphere parameters | Explicit A = 7, m = 10, energy index 80 | Feasible witness only; no parameter optimality claim |
| Fresh reproduction | artifacts/repository-verification.json and its linked reports | Evidence is specific to the recorded sources and environment |

Lean declarations use the namespaces HeilbronnSphere, HeilbronnTuned,
HeilbronnSlab, HeilbronnCentral, HeilbronnNormCompression, HeilbronnExactLayer,
HeilbronnNorm, HeilbronnFrobenius and HeilbronnFrobeniusPacking. The algebra
audit covers eleven Mathlib-based modules and 31 exported theorems.
Only the standard logical axioms propext, Classical.choice and Quot.sound are
permitted in these local proofs. Pure numerical comparisons use no axioms.

The algebra theorem assumes fields, a degree-13 finite extension, and at least
25 base-field elements, and characteristic different from 13. It does not assume a compressed norm identity or a
descent theorem. Its final prime-field specialization constructs the extension
as GaloisField r 13. The polynomial theorem proves homogeneity and a universally
quantified evaluation identity; the functional theorem applies to arbitrary
one-label functions, the interface permitted by upstream Section 4.

## The steps most useful to review

The new algebraic step deserves review before the retained scale argument:

- In the product expansion, normalize pi_v = rho_v tau with rho_0 = id.
  Odd d makes the common sign (sgn tau)^d equal to sgn tau, leaving
  6^(d-1) determinants over K. No division by 6 is used.
- On normalized patterns, use (a.w)(g) = w(a^-1 g) w(a^-1)^-1. Check the
  row-permutation sign against the product of the 13 permutation signs.
  Together they give C_(a.w) = a(C_w).
- Orbit-stabilizer gives sizes 1 or 13. A fixed pattern is an antihomomorphism
  to S_3, and its values have both sixth and thirteenth power equal to one.
  Thus only the constant identity pattern is fixed. The same conclusion
  would be false in degree 3.
- Replace ell by its invariant average L(z) = sum_a ell(a(z))/13. A cardinality
  bound on a general base field does not suffice: explicitly exclude characteristic 13.
  Group the invariant sum with the orbit sizes as weights.
- The product of two power-basis representatives has degree at most 2d-2.
  Interpolate it at 2d-1 nodes and evaluate the identity at the basis generator.
  Multiplying by the third factor and applying a linear projection gives
  L(xyz) = sum_t eval_t(x) eval_t(y) L(c_t z).
- Apply the same three row maps to all six signed determinant terms. The third
  row must use L(c_t z); using the old third-row evaluation map with only
  25 nodes is incorrect and is rejected by explicit negative controls.
- Coefficientwise linear maps preserve degree-d homogeneity. The exact norm
  and the distinct-label obstruction are unchanged. Section 4's conditional
  digit lemma explicitly allows arbitrary label functions.
- For the sphere layer, count the coefficient of z^80 in
  [2(1+z+z^3+z^6+z^10+z^15+z^21)]^10. The Lean table is linked to the actual
  symbolic word list by induction, with no assumed layer capacity. Truncating
  counts above 86 is valid because digit energies are nonnegative.

The count exceeds 25 * (6^12 + 12)/13. All classes, including the singleton,
receive 25 nodes. The formal proof then selects distinct words
and reuses sphere rigidity and carry-free encoding. The independent checker
also computes the count by a multinomial sum. The slab transfer is unchanged:

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
