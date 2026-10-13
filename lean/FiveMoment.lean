import FiveTags
import FiveCollision

/-! Connect the counting estimate to the coefficient of the determinant polynomial
and to the minor exponent of the actual digit matrix. -/

namespace HeilbronnFive
open Finset Polynomial

noncomputable def digitPolynomial {k : ℕ} (z : Fin k → ℤ) : ℤ[X] :=
  ∑ p, Polynomial.monomial p.val (z p)

theorem digitPolynomial_coeff {k : ℕ} (z : Fin k → ℤ) (p : Fin k) :
    (digitPolynomial z).coeff p.val = z p := by
  classical
  simp only [digitPolynomial, finset_sum_coeff, coeff_monomial]
  rw [Finset.sum_eq_single p]
  · simp
  · intro q _ hq
    rw [if_neg (by intro h; exact hq (Fin.ext h))]
  · simp

theorem digitPolynomial_eval {k : ℕ} (z : Fin k → ℕ) (B : ℕ) :
    (digitPolynomial (fun p => (z p : ℤ))).eval (B : ℤ) = radix B z := by
  simp only [digitPolynomial, eval_finset_sum, eval_monomial, radix,
    Nat.cast_sum, Nat.cast_mul, Nat.cast_pow]

theorem product_digit_coefficient {k : ℕ} (U : ℤ[X]) (z : Fin k → ℤ) :
    (U * digitPolynomial z).coeff (k-1) =
      ∑ p, U.coeff (k-1-p.val) * z p := by
  rw [digitPolynomial, Finset.mul_sum, finset_sum_coeff]
  apply Finset.sum_congr rfl
  intro p _
  have hp : p.val ≤ k-1 := by have := p.isLt; omega
  simpa only [Nat.sub_add_cancel hp] using
    Polynomial.coeff_mul_monomial U p.val (k-1-p.val) (z p)

namespace DigitModel
variable {k M : ℕ} (m : DigitModel k M)

noncomputable def poly (x : (Fin 3 × Fin k) → Fin M) (c : Fin 3) : ℤ[X] :=
  digitPolynomial (fun p => (m.alphabet (c,p) (x (c,p))).val)

theorem poly_eval (x : (Fin 3 × Fin k) → Fin M) (c : Fin 3) :
    (m.poly x c).eval (m.base : ℤ) = m.entry x c :=
  digitPolynomial_eval _ _

def weights (U : ℤ[X]) (i : Fin 3 × Fin k) : ℤ :=
  if i.1 = 0 then U.coeff (k-1-i.2.val)
  else if i.1 = 1 then -U.coeff (k-1-i.2.val) else 0

theorem weighted_coefficient (U : ℤ[X]) (x : (Fin 3 × Fin k) → Fin M) :
    (∑ i, weights U i * (m.alphabet i (x i)).val) =
      (U * (m.poly x 0 - m.poly x 1)).coeff (k-1) := by
  rw [mul_sub, coeff_sub, poly, poly, product_digit_coefficient, product_digit_coefficient]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, weights]
  norm_num
  simp only [neg_mul, Finset.sum_neg_distrib, Finset.sum_sub_distrib, sub_eq_add_neg]
  norm_num [Fin.ext_iff]

/-- Uniform over every allowed alphabet at every position. `U` is the top minor;
the conclusion is stronger than restricting to small determinant residues. -/
theorem tagged_pair_moment (hM : 0 < M) (hB : 0 < m.base)
    (second : Fin 3 → ℕ) (U : ℤ[X]) (a d : ℕ) (ha : a < d) (hk : 2*d ≤ k)
    (hlo : ∀ i, i < a → U.coeff i = 0) (hne : U.coeff a ≠ 0)
    (hsmall : |U.coeff a| < m.base)
    (heval : U.eval (m.base : ℤ) = (m.top 0 : ℤ)*second 2 - (m.top 2 : ℤ)*second 0)
    (hscale : (m.base : ℚ)/(M : ℚ)^2 ≤ 1/2) :
    average (fun x => if (U * (m.poly x 0 - m.poly x 1)).coeff (k-1) = 0
      then (m.base : ℚ)^(m.minorExponent second x) else 0) ≤ 2/(M : ℚ) := by
  classical
  let v : Fin k := ⟨k-1-a, by omega⟩
  have hv : a ≤ v.val := by dsimp [v]; omega
  have hw : weights U (1,v) ≠ 0 := by
    have hindex : k-1-v.val = a := by dsimp [v]; omega
    simp only [weights, show (1 : Fin 3) ≠ 0 by decide, if_false, if_true, hindex]
    exact neg_ne_zero.mpr hne
  have hnext := (eval_first_valuation U hB hlo hne hsmall).2
  rw [heval] at hnext
  have hb (x) : m.minorExponent second x ≤ a :=
    exponent_le_of_minor hnext (m.minorExponent_top second x)
  have h := m.fresh_divisor_moment hM a (by omega) v hv (weights U) hw 0
    (m.minorExponent second) hb (m.minorExponent_schur second) hscale
  simpa only [weighted_coefficient] using h

/-- The complete coefficient-event estimate from the tag hypotheses. -/
theorem tagged_pair_moment_from_tags (hM : 0 < M) (hB : 0 < m.base)
    (second : Fin 3 → ℕ) (A A' Q Q' : ℤ[X]) (a d r : ℕ)
    (ha : a < d) (hk : 2*d ≤ k) (hrB : r ≤ m.base)
    (hA : ∀ i, i ≤ a → A.coeff i = A'.coeff i) (hA0 : A.coeff 0 = 1)
    (hQ : ∀ i, i < a → Q.coeff i = Q'.coeff i) (hne : Q.coeff a ≠ Q'.coeff a)
    (hQpos : 1 ≤ Q.coeff a) (hQ'pos : 1 ≤ Q'.coeff a)
    (hQle : Q.coeff a ≤ r) (hQ'le : Q'.coeff a ≤ r)
    (hAeval : A.eval (m.base : ℤ) = m.top 0)
    (hA'eval : A'.eval (m.base : ℤ) = m.top 2)
    (hQeval : Q.eval (m.base : ℤ) = second 0)
    (hQ'eval : Q'.eval (m.base : ℤ) = second 2)
    (hscale : (m.base : ℚ)/(M : ℚ)^2 ≤ 1/2) :
    average (fun x => if (Matrix.det
      !![A,A,A'; Q,Q,Q'; m.poly x 0,m.poly x 1,m.poly x 2]).coeff (k-1) = 0
      then (m.base : ℚ)^(m.minorExponent second x) else 0) ≤ 2/(M : ℚ) := by
  have ht := tagged_minor_first A A' Q Q' hA hA0 hQ hne hQpos hQ'pos hQle hQ'le
  simp_rw [repeated_top_factorization]
  apply m.tagged_pair_moment hM hB second (A*Q'-A'*Q) a d ha hk ht.1 ht.2.1
    (lt_of_lt_of_le ht.2.2 (by exact_mod_cast hrB)) _ hscale
  simp only [eval_sub, eval_mul, hAeval, hA'eval, hQeval, hQ'eval]

end DigitModel
#print axioms DigitModel.weighted_coefficient
#print axioms DigitModel.tagged_pair_moment
#print axioms DigitModel.tagged_pair_moment_from_tags

end HeilbronnFive
