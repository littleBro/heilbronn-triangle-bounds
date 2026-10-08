# Reviewing the current conditional result

The current target is

    Delta(n) >= c n^(-2 + eta), for every sufficiently large n,
    eta = 1 / (498 * 403^17 + 7) ≈ 1.02940168035828e-47.

This is a conditional refinement of the pinned OpenAI family 191 argument.
Read the retuning and slab-cap sections of [the note](../notes/sphere-packing.tex)
together with the [six-section source patch](../patches/slab-cap.patch).
The original manuscript and comparator are retained in upstream/ at commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.

## Evidence for each claim

| Claim | Evidence | Boundary |
| --- | --- | --- |
| Enough distinct equal-energy words | Sphere.sphere_family and finite pigeonhole proof | Fully proved in Lean; no enumerated giant sphere |
| Positions, row injections and exact matching | Tuned.tuned_packing, importing Sphere.packing_exists | Fully proved in Lean for T = binom(binom(51,13),3), k = 403^17 |
| The exact T, capacity and gain | Tuned.lean, Slab.slab_gain and independent integer arithmetic | Local falling-factorial definition of binomial coefficients |
| Digit and auxiliary scale inequalities | Tuned.lean, Slab.lean, certificates/slab.json | Integer inequalities; probability and lattice arguments are separate |
| Slab cap size and short-relation exclusion | New written lemma and proof in the note and patched Section 5 | Finite-field geometry is not in Lean; small cases are independently checked |
| Field norm and determinant summands for odd d = 13 | Pinned Section 3 and the written transfer | Not formalized here |
| Lattice, orbit and weighted counts | Pinned Sections 2 and 4–7, with the slab lemma and changed scale checks | Relied upon; no complete independent theorem audit |
| Deletion and all sufficiently large cardinalities | Written note and patched Section 8 | The asymptotic and geometric proof is not in Lean |
| Bounded choice of sphere parameters | Independent comparison for dimensions 3–284 | Sufficient-capacity criterion only; no global optimality |
| Fresh reproduction | artifacts/repository-verification.json and its linked reports | Evidence is specific to the recorded sources and environment |

Lean declarations use the namespaces HeilbronnSphere, HeilbronnTuned and HeilbronnSlab.
Only the standard logical axioms propext, Classical.choice and Quot.sound are
permitted in these local proofs. Pure numerical comparisons use no axioms.

## The steps most useful to review

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

The ternary, d = 41 sphere and previous d = 13 retuning retain their own
certificates, Lean files, patches and checkers. They are useful checkpoints and
do not describe the current auxiliary cap. The sphere method is classical Behrend;
the slab is a subset of the classical elliptic paraboloid already used upstream.

The repository format was informed by
[Swapnil Jain's integer-mult-kappa](https://github.com/Swapnil-jain/integer-mult-kappa)
and [CrocSwap's integer-mult-bounds](https://github.com/CrocSwap/integer-mult-bounds).
Those projects concern a different problem; their multiplication estimates are
not assumptions of this Heilbronn construction.

The unchanged upstream Lean comparator has a different exponent and a subsequence
target. This repository's certificates concern the manuscript exponent; they do
not constitute a completed proof of that comparator.
