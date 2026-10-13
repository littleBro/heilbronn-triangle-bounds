# Reviewing the current conditional result

The target is

    Delta(n) >= c n^(-2 + eta), for every sufficiently large n,
    eta = 2 / (249 * 1166895 + 5) = 1 / 145278430.

Read the label-tags section of [the note](../notes/sphere-packing.tex)
and the [six-section source patch](../patches/degree-five.patch).
The source remains pinned at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
The degree-seven result and every earlier checkpoint remain reproducible.

## Evidence for each claim

| Claim | Evidence | Boundary |
| --- | --- | --- |
| Eighteen symmetric products for a determinant pair | EighteenExpansion.pair_identity | Root u² − u + 1 = 0; multiplier 3 |
| Two pairs and one singleton | FiveNorm.norm_expansion | Degree five; normalization 3² |
| T = 9 * 18² = 2,916 | FiveNorm.finite_field_norm | At least nine base-field elements; characteristic 3 excluded; required root |
| Homogeneous norm coordinates | FivePolynomials.finite_field_polynomials | Degree five; tags are separately prescribed residues |
| Distinct-label norm criterion | FivePolynomials.prime_field_labels | Every prime r >= 37 congruent to 1 mod 3 |
| Exact energy-two count 3,072 | FiveLayer.exact_layer_count | Nine kernel-checked recurrence transitions |
| Selection, bounds, injections and shifted matching | FivePacking.tagged_packing | k = 1,166,895; shift 291,726 |
| Tags do not reach the target coefficient | FivePacking.tag_separation | Support inequality; coefficient transfer is written |
| Repeated-column determinant factorization | FiveCollision.repeated_top_factorization | Universal over commutative rings |
| Tag minor valuation and fresh-digit joint tail | FiveTags and FiveJointTail | Universal finite digit model; exact rational probabilities |
| Small-residue pair moment | FiveTagged.tagged_small_residue_moment (under DigitModel) | Explicit digit/tag bounds; actual determinant residue and minor exponent |
| Column relabelling and total label mixture | FiveReindex and FiveFiniteTheorem.total_small_residue_moment | Tag data for each repeated pair; distinct-label exclusion interface |
| Fresh position lies beyond Schur prefixes | FiveScales.fresh_position | Requires a < d and k >= 2d |
| Uniform minor-divisor moment and scale | FiveTags.actual_uniform_moment (under DigitModel), FiveTagged.five_probability_scale | Third-row digit model, arbitrary fixed top rows with a unit pivot |
| Norm-packing instantiation and Smith-divisor identification | Written construction and pinned diagonal-form lemma | Not an end-to-end Lean instantiation |
| Deletion inequalities and exponent identity | FiveScales.lean | Positive denominators cleared |
| Gain greater than 108 over degree seven | FivePacking.trace_gain | Kernel-checked integer comparison |
| Slab, lattice, orbit, weighted count and deletion | Pinned manuscript and written transfer | No complete independent upstream audit or practical threshold |
| Allowed prime in (m, 2m] eventually | Written PNT progression argument | Standard theorem; not formalized here |

The shared algebra and finite probability audit covers 39 modules and 120 exported theorems. Only
propext, Classical.choice and Quot.sound are permitted. The new core checker
also audits four scale theorems and seven packing theorems. No count-table
entry is assumed: kernel evaluation and symbolic recurrence connect it to
actual finite words.

## Finite probability theorem and its inputs

The probability files use rational averages over the complete product of finite
digit alphabets. `residueAlphabet_complete` proves that the parameterization
exhausts the positive representatives of a prescribed residue.
`probability_le_of_completion` bounds events by an injective restriction to
the remaining digits. Schur-prefix uniqueness and the fresh coefficient
equation establish that injection; their joint tail is not an assumption.

`tagged_small_residue_moment` derives the bound 2/M for the actual determinant
residue and the exponent defined by divisibility of all 2-by-2 minors. It
also proves the carry implication from the coefficient range bounds.
`smallMoment_permute` proves invariance under any allowed column permutation.
`total_small_residue_moment` derives 6/(M*N)+2/N^2 from explicit tag data for
the repeated-label cases and exclusion of small residues for distinct labels.
`average_product` identifies the iterated average with the joint product
average. No probability bound is an input of either final theorem.

The public construction supplies N=r^d and these structural hypotheses in
writing. The norm-packing/tag instantiation, including the distinct-label
exclusion, and the identification of the minor exponent with the upstream
Smith divisor remain explicit interfaces. No Smith normal-form or complete
geometric theorem is claimed as part of this finite formalization.

## The most useful mathematical review

1. Check the tag layout. Put residue 1 at row 1, position 0; put all five
   basis coordinates of the label at row 2, positions 0 through 4. Norm
   positions in the top rows start at S = 291,726. Their maximum is
   S + (K0 − 1)/2, and the third-row support is below K0. A triple using
   any tag has position sum at most k − 2. The target coefficient still
   equals the field norm modulo r. Unspecified residues remain zero,
   represented by positive digits, not integer zeros.
2. For labels (lambda, lambda, mu), the top two digit rows are deterministic.
   Expand the determinant polynomial as U(Y)(Z1(Y) − Z2(Y)). Let a be the
   first distinct label coordinate. Below the norm positions, the first
   row has coefficients 1,r,r,..., so U vanishes below a and its coefficient
   at a is the difference of two distinct positive residue representatives.
   It is nonzero with absolute value below r < B. Thus U(B) has valuation
   exactly a < d, and the smaller Smith exponent b is at most a.
3. Retain the actual event J that the determinant residue is small, rather
   than replacing it by a label collision. The carry bound implies
   J => F_(k−1) = 0 over the integers. In the factorization this coefficient
   is linear, with nonzero slope, in the digit of Z2 at v = k − 1 − a.
4. Check the joint conditioning carefully. For 1 <= j <= a, condition on
   column 1 and the high digits of columns 2 and 3 except the digit at v.
   The two third-row Schur congruences cost at most M^(-2j), where M=L3/r.
   Since k >= 2d, v > a >= j, and the final coefficient equation uses an
   untouched digit, costing another 1/M. This proves the joint bound
   Pr(b >= j and J | labels) <= M^(-2j−1). Multiplying separate marginal
   bounds without this conditioning would not justify the argument.
5. Sum the finite divisor tails using b <= a and theta=B/M²<=1/2.
   Exactly two equal labels give E[D 1_J | labels] <= 2/M. All three equal
   labels have probability r^(-2d); their determinant is zero and their
   contribution cannot be omitted. Use the retained bound E[D | labels]<=2.
   The total is at most 6/(M r^d)+2/r^(2d).
6. The lifting and orbit estimates condition on C and give an upper bound
   proportional to D 1_J. With d=5 and M=400k²r³, the two collision losses
   are r^(2 gamma−2) and r^(2 gamma−4). Choose gamma=rho/(rho+1),
   rho=249k+3. Proportional-pair loss remains r^(gamma−3(k−1)); all three
   zero-case losses retain their previous bounds.
7. Check the two conjugate pairs, normalization 3^(-2), nine-node descent,
   and the layer count 2^9 * choose(4,2) = 3,072. Shifting the first two
   norm supports gives k=2*(3^5*7^4)+9, including the tag padding.
8. Retain the prime number theorem in the fixed progression 1 mod 3 for
   all-cardinalities interpolation. Mere infinitude of split primes is
   insufficient. The auxiliary primes B and q use ordinary Bertrand intervals.

## Independent controls and retained checkpoints

The new digit controls enumerate 147,456 matrices in all 36 ordered label
groups with exactly two equal labels in a two-coordinate toy label space.
Every bottom-row draw is enumerated for each group. They check 12 nonempty
joint-tail bounds and 36 weighted moment bounds. These fixtures test the
finite geometric sum before the theta <= 1/2 simplification; their small
digit alphabets do not satisfy the final asymptotic scale choices.

When k=2 and a=1, the candidate fresh position is already a low digit.
The measured joint probability is 1/4, contradicting the invalid 1/8 bound.
Omitting a distinguishing tag also breaks the proposed suppression. Small
support tests verify 32 coefficient identities; omitting the shift corrupts
28 of them. The independent histogram checks all 30 table entries.

Field controls enumerate all 324 extension terms for each of two matrices
over a verified degree-five quotient of F37. They test 32 nine-node descents;
omitting a node breaks 31 of them. Omitting normalization is also rejected.
Universal norm identities are proved separately in Lean.

Thirteen corrupted certificates must fail. The actual patch is applied to
ignored text snapshots and all 59 referenced labels are checked, with a
missing-reference negative control. All fourteen checkpoints are verified
by python scripts/verify_all.py; all thirty-six generated files must reproduce
exactly. The upstream files are never modified.

The finite fresh-digit probability theorem is formalized. The full geometric
Heilbronn theorem, its norm-packing instantiation and Smith-divisor connection,
and the prime progression theorem are not formalized here. The exponent comparison
does not give a practical finite-n improvement. Novelty and unrestricted
optimality are not established.
