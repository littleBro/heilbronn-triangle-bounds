# Reviewing the current conditional result

The current target is

    Delta(n) >= c n^(-2 + eta), for every sufficiently large n,
    eta = 1 / (498 * 47^10 + 7) ≈ 3.81761455590365e-20.

This is a conditional refinement of the pinned OpenAI family 191 argument.
Read the norm-compression section of [the note](../notes/sphere-packing.tex)
and its retained slab transfer, together with the
[six-section source patch](../patches/norm-compression.patch).
The original manuscript and comparator are retained in upstream/ at commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.

## Evidence for each claim

| Claim | Evidence | Boundary |
| --- | --- | --- |
| Norm decomposition with T = 37 * 6^12 | New written lemma, two-stage proof and patched Section 3 | Permutation normalization and signs in Lean; determinant expansion and field descent are not fully formalized |
| Interpolation descent using 37 nodes | Written degree bound and Lagrange identity; finite field controls | Universal written proof; no universal Lean interpolation theorem |
| Enough distinct equal-energy words | NormCompression.norm_capacity and Sphere.sphere_family | Fully proved in Lean by the full-range bound and finite pigeonhole |
| Positions, row injections and exact matching | NormCompression.norm_packing, using Sphere.packing_exists | Fully proved in Lean for T = 37 * 6^12, k = 47^10 |
| The exact T formula, capacity and gain | NormCompression.lean and independent integer arithmetic | The count formula is numerical; its field-algebra justification is written |
| Digit and auxiliary scale inequalities | Tuned.lean, Slab.lean, certificates/norm.json | Integer inequalities uniform in k; probability and lattice arguments are separate |
| Slab cap size and short-relation exclusion | New written lemma and proof in the note and patched Section 5 | Finite-field geometry is not in Lean; small cases are independently checked |
| Nonzero norm for distinct labels at d = 13 | Pinned Vandermonde identity and new exact norm decomposition | Written field-algebra argument; not fully formalized here |
| Lattice, orbit and weighted counts | Pinned Sections 2 and 4–7, with the slab lemma and changed scale checks | Relied upon; no complete independent theorem audit |
| Deletion and all sufficiently large cardinalities | Written note and patched Section 8 | The asymptotic and geometric proof is not in Lean |
| Current sphere parameters | Explicit A = 12, m = 10, Q = 661 | Feasible witness only; no parameter optimality claim |
| Fresh reproduction | artifacts/repository-verification.json and its linked reports | Evidence is specific to the recorded sources and environment |

Lean declarations use the namespaces HeilbronnSphere, HeilbronnTuned,
HeilbronnSlab, HeilbronnCentral and HeilbronnNormCompression.
Only the standard logical axioms propext, Classical.choice and Quot.sound are
permitted in these local proofs. Pure numerical comparisons use no axioms.

## The steps most useful to review

The new algebraic step deserves review before the retained scale argument:

- In the product expansion, normalize pi_v = rho_v tau with rho_0 = id.
  Odd d makes the common sign (sgn tau)^d equal to sgn tau, leaving
  6^(d-1) determinants over K. No division by 6 is used.
- Reduce each coefficient in a power basis. Each representative has degree
  at most d-1, so its 3-by-3 determinant has degree at most 3d-3.
  Interpolate at 3d-2 distinct nodes, possible for r >= 37.
- Apply a linear projection fixing the base field to the entire interpolated
  determinant. Entrywise projection does not preserve a determinant; the
  checker includes counterexamples to that incorrect shortcut.
- The resulting polynomials remain homogeneous of degree d over F_r and
  give the exact original norm. The distinct-label obstruction is unchanged.
  Section 4's conditional digit lemma explicitly allows arbitrary label functions.

The new packing then uses 24^10 >= 661 * (37 * 6^12). Its Lean proof
includes the existence of the layer and does not take that as a hypothesis.

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

The ternary, d = 41 sphere, d = 13 retuning, slab and central-layer variants retain their own
certificates, Lean files, patches and checkers. They are useful checkpoints and
use their own parameters. The sphere method is classical Behrend, the moment
count is elementary, and the slab is a subset of the classical elliptic
paraboloid already used upstream. The norm regrouping and interpolation use
elementary algebra; novelty of this application is not established.

The repository format was informed by
[Swapnil Jain's integer-mult-kappa](https://github.com/Swapnil-jain/integer-mult-kappa)
and [CrocSwap's integer-mult-bounds](https://github.com/CrocSwap/integer-mult-bounds).
Those projects concern a different problem; their multiplication estimates are
not assumptions of this Heilbronn construction.

The unchanged upstream Lean comparator has a different exponent and a subsequence
target. This repository's certificates concern the manuscript exponent; they do
not constitute a completed proof of that comparator.
