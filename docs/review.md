# Reviewing the current conditional result

The target is

    Delta(n) >= c n^(-2 + eta), for every sufficiently large n,
    eta = 1 / (249 * 63412811 + 4) = 1 / 15789789943.

Read the row-dependent-digits section of [the note](../notes/sphere-packing.tex)
and the [six-section source patch](../patches/row-digits.patch).
The source remains pinned at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Earlier checkpoints, including the small interval refinement, remain reproducible.

## Evidence for each claim

| Claim | Evidence | Boundary |
| --- | --- | --- |
| Eighteen symmetric products for a determinant pair | EighteenExpansion.pair_identity | Root u^2 - u + 1 = 0; multiplier 3 |
| Three pairs and one singleton | SevenNorm.norm_expansion | Degree seven; normalization 3^3 |
| T = 13 * 18^3 = 75,816 | SevenNorm.finite_field_norm | At least 13 base-field elements, characteristic 3 excluded, required root |
| Homogeneous degree-seven coordinates | SevenPolynomials.finite_field_polynomials | Coefficientwise descent preserves degree |
| Distinct-label criterion | SevenPolynomials.prime_field_labels | Every prime r >= 37 congruent to 1 mod 3; root existence reused |
| Exact energy-five count 78,848 | SevenLayer.exact_layer_count | Nine kernel-checked recurrence transitions |
| Selection, bounds, injections and matching | SevenPacking.trace_packing | k = 11 * 7^8 = 63,412,811 |
| Conditional tail with different row ranges | Written lemma in note and patch | Not a Lean probability theorem |
| Divisibility, moment-bound arithmetic and base growth | RowDigits.long_digits_divisible, digit_moment_bound, base_scale | Integer inequalities; separate from the probability proof |
| Alteration inequalities and exponent identity | RowDigits.alteration_constraints, exponent_identity | Positive denominators cleared |
| Gain greater than 680,000 against interval checkpoint | SevenPacking.trace_gain | Kernel-checked integer comparison |
| Retained slab and zero-case bounds | Slab.lean and source patch | Arithmetic formalized; geometry remains written |
| Allowed prime in (m, 2m] eventually | PNT in arithmetic progressions, written derivation | Standard theorem; not formalized here |
| Lattice, orbit, weighted count and deletion | Pinned manuscript and written transfer | No complete independent upstream audit or practical threshold |
| Reproduction | repository-verification.json and individual reports | Applies to recorded sources and runtime versions |

The shared algebra audit covers 24 modules and 70 exported theorems. Only
propext, Classical.choice and Quot.sound are permitted. The new core checker
additionally audits five row-scale and five packing theorems. No count-table
entry is assumed: kernel evaluation and symbolic recurrence connect it to
actual finite words.

## The most useful mathematical review

1. Check the row-product coefficient bound. Every determinant product uses
   one digit in each row, so 6k^2 L1 L2 L3 replaces 6k^2 L^3. All low digits
   remain positive and smaller than B, including digits with residue zero.
2. Check the new conditional tail for arbitrary fixed labels, with repetitions.
   Condition on the first column and first entries of the other columns.
   The four Schur congruences force j digits each, with probabilities
   (r/L2)^j, (r/L2)^j, (r/L3)^j, (r/L3)^j. A row with Li = r is deterministic;
   its probability factors are zero or one. Do not reuse a fourth-power
   bound involving the long row alone.
3. With L1 = L2 = r and L3 = 400k^2r^4, check
   theta = B(r/L3)^2 <= 200k^2r^4/L3 = 1/2. The pointwise tail-sum identity
   then proves E[D | labels] <= 2. This probabilistic step is written,
   while its integer scale bound is formalized.
4. Check every subsequent use of the digit distribution. The orbit and
   weighted counts condition on C; their interfaces require units, the
   determinant obstruction, and the uniform conditional moment. They do
   not require equal row ranges or randomness in all three rows.
5. Recompute the sample exponents. B grows as r^6, so collision loss is
   r^(2 gamma + 6 - d). Degree seven and gamma < 1/2 suffice. With the
   retained q and N, beta = (83k+1)/2 and rho = 6 beta = 249k+3.
   Proportional-pair loss is r^(gamma - 3(k-1)); the three zero-case losses
   remain h^6/q, h^4/q and h^6/q^2.
6. Enumerate the seven conjugates as one singleton and three disjoint pairs,
   apply the known [CGLV formula](https://arxiv.org/abs/1909.04785), and include
   3^(-3) in one row. Thirteen interpolation nodes suffice for products of
   degree-at-most-six representatives. Lean proves the universal identity.
7. Verify the layer coefficient
   2^9 * (choose(8,5) + choose(8,4) + choose(8,2)) = 78,848.
   The complete packing uses radices 11,7,7,7,7,7,7,7,7. Equal squared norm
   49 forces midpoint rigidity; all digit sums are below their radices.
8. For all-cardinalities interpolation use the
   [prime number theorem in arithmetic progressions](https://dlmf.nist.gov/27.11).
   Mere infinitude of split primes would not suffice. B and q use ordinary
   Bertrand intervals. This part remains a written argument.

## Independent controls and retained checkpoints

The new controls enumerate every one of 5,832 extension-field terms for one
matrix over a verified degree-seven quotient of F37. They check 24 descents
and reject omitted normalization and an omitted node. Universal identities
are proved separately in Lean; this enumeration is a finite implementation check.

Three small row-digit fixtures enumerate 163,840 matrices and check 2,560
conditional tail inequalities. The one-digit cases enumerate every matrix.
The two-digit case fixes twelve reproducible top-row configurations and
exhausts bottom-row draws. Every checked conditional residue group is complete.
An incorrectly retained fourth-power bound has 496 counterexamples in these
fixtures. The full probability lemma is the written argument above.

An independent full histogram agrees with all 60 saved count entries; a
binomial calculation gives the layer coefficient. Small spheres exercise
6,528 matching triples. Ten corrupted certificates must be rejected.
The patch checker applies the actual patch to ignored text snapshots and
checks all 58 referenced labels; removing the matching label must fail.

The interval checkpoint retains its general cutoff proof, 44 rows of 33
counts, 13,583 enumeration comparisons, 42,216 matching triples, and 342
small search comparisons. Its branch-and-bound search concerns only the
listed coordinate orders and energies; no global packing optimum is claimed.
All thirteen checkpoints are verified by python scripts/verify_all.py.

The full geometric Heilbronn theorem, the new probability lemma, and prime
progression theorem are not formalized here. The exponent comparison does
not give a practical finite-n improvement. Novelty and unrestricted optimality
are not established.
