import FiveJointTail
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Nat.Find

/-! The low tags force the first nonzero minor coefficient and its exact
base valuation. The minor exponent is defined from all actual 2 by 2 minors. -/

namespace HeilbronnFive
open Finset Polynomial

theorem first_differing_tag (Q Q' : ℤ[X]) {d : ℕ}
    (h : ∃ i, i < d ∧ Q.coeff i ≠ Q'.coeff i) :
    ∃ a, a < d ∧ Q.coeff a ≠ Q'.coeff a ∧
      ∀ i, i < a → Q.coeff i = Q'.coeff i := by
  classical
  refine ⟨Nat.find h, (Nat.find_spec h).1, (Nat.find_spec h).2, ?_⟩
  intro i hi
  by_contra hne
  exact Nat.find_min h hi ⟨lt_trans hi (Nat.find_spec h).1, hne⟩

theorem tagged_minor_coefficient (A A' Q Q' : ℤ[X]) {a n : ℕ}
    (hn : n ≤ a) (hA : ∀ i, i ≤ a → A.coeff i = A'.coeff i)
    (hA0 : A.coeff 0 = 1) (hQ : ∀ i, i < a → Q.coeff i = Q'.coeff i) :
    (A*Q' - A'*Q).coeff n = Q'.coeff n - Q.coeff n := by
  have he : (A'*Q).coeff n = (A*Q).coeff n := by
    rw [coeff_mul, coeff_mul]
    apply Finset.sum_congr rfl
    intro p hp
    rw [← hA p.1 (by have := Finset.mem_antidiagonal.mp hp; omega)]
  rw [coeff_sub, he, ← coeff_sub, ← mul_sub, coeff_mul]
  have hs : (∑ p ∈ Finset.antidiagonal n, A.coeff p.1 * (Q'-Q).coeff p.2) =
      A.coeff 0 * (Q'-Q).coeff n := by
    apply Finset.sum_eq_single (0,n)
    · intro p hp hpne
      have hp' := Finset.mem_antidiagonal.mp hp
      have hlt : p.2 < a := by
        have : p.1 ≠ 0 := by
          intro hz
          apply hpne
          exact Prod.ext hz (by omega)
        omega
      simp only [coeff_sub, ← hQ p.2 hlt, sub_self, mul_zero]
    · simp
  rw [hs, hA0, one_mul, coeff_sub]

theorem tagged_minor_first (A A' Q Q' : ℤ[X]) {a r : ℕ}
    (hA : ∀ i, i ≤ a → A.coeff i = A'.coeff i) (hA0 : A.coeff 0 = 1)
    (hQ : ∀ i, i < a → Q.coeff i = Q'.coeff i)
    (hne : Q.coeff a ≠ Q'.coeff a)
    (hQpos : 1 ≤ Q.coeff a) (hQ'pos : 1 ≤ Q'.coeff a)
    (hQle : Q.coeff a ≤ r) (hQ'le : Q'.coeff a ≤ r) :
    (∀ i, i < a → (A*Q'-A'*Q).coeff i = 0) ∧
    (A*Q'-A'*Q).coeff a ≠ 0 ∧ |(A*Q'-A'*Q).coeff a| < r := by
  constructor
  · intro i hi
    rw [tagged_minor_coefficient A A' Q Q' (Nat.le_of_lt hi) hA hA0 hQ, hQ i hi,
      sub_self]
  · rw [tagged_minor_coefficient A A' Q Q' (le_refl a) hA hA0 hQ]
    constructor
    · exact sub_ne_zero.mpr hne.symm
    · rw [abs_lt]; omega

theorem eval_first_valuation (U : ℤ[X]) {a B : ℕ} (hB : 0 < B)
    (hlo : ∀ i, i < a → U.coeff i = 0) (hne : U.coeff a ≠ 0)
    (hsmall : |U.coeff a| < B) :
    (B : ℤ)^a ∣ U.eval (B : ℤ) ∧ ¬ (B : ℤ)^(a+1) ∣ U.eval (B : ℤ) := by
  obtain ⟨V, hV⟩ := Polynomial.X_pow_dvd_iff.mpr hlo
  have hev : U.eval (B : ℤ) = (B : ℤ)^a * V.eval (B : ℤ) := by
    rw [hV, eval_mul, eval_pow, eval_X]
  have hc : U.coeff a = V.coeff 0 := by
    rw [hV]
    simpa only [zero_add] using coeff_X_pow_mul V a 0
  refine ⟨by rw [hev]; exact dvd_mul_right _ _, ?_⟩
  intro hd
  rw [hev, pow_succ] at hd
  have hb0 : (B : ℤ)^a ≠ 0 := pow_ne_zero _ (by exact_mod_cast Nat.ne_of_gt hB)
  have hdiv : (B : ℤ) ∣ V.eval (B : ℤ) := (mul_dvd_mul_iff_left hb0).mp hd
  have hdiff : (B : ℤ) ∣ V.eval (B : ℤ) - V.coeff 0 := by
    simpa only [sub_zero, ← Polynomial.coeff_zero_eq_eval_zero] using
      Polynomial.sub_dvd_eval_sub (B : ℤ) 0 V
  have hcoeff : (B : ℤ) ∣ U.coeff a := by
    rw [hc]
    have := dvd_sub hdiv hdiff
    simpa only [sub_sub_cancel] using this
  exact hne (Int.eq_zero_of_abs_lt_dvd hcoeff hsmall)

theorem exponent_le_of_minor {B a b : ℕ} {u : ℤ}
    (hnext : ¬ (B : ℤ)^(a+1) ∣ u) (hb : (B : ℤ)^b ∣ u) : b ≤ a := by
  by_contra h
  exact hnext ((pow_dvd_pow (B : ℤ) (by omega : a+1 ≤ b)).trans hb)

namespace DigitModel
variable {k M : ℕ} (m : DigitModel k M)

def matrix (second : Fin 3 → ℕ) (x : (Fin 3 × Fin k) → Fin M) :
    Fin 3 → Fin 3 → ℤ :=
  fun row col => if row = 0 then m.top col else if row = 1 then second col
    else m.entry x col

def allMinors (second : Fin 3 → ℕ) (x : (Fin 3 × Fin k) → Fin M) (j : ℕ) : Prop :=
  ∀ s t c e : Fin 3, (m.base : ℤ)^j ∣
    m.matrix second x s c * m.matrix second x t e -
    m.matrix second x s e * m.matrix second x t c

instance (second : Fin 3 → ℕ) (x : (Fin 3 × Fin k) → Fin M) :
    DecidablePred (m.allMinors second x) := by
  unfold allMinors
  infer_instance

def minorExponent (second : Fin 3 → ℕ) (x : (Fin 3 × Fin k) → Fin M) : ℕ :=
  Nat.findGreatest (m.allMinors second x) k

theorem minorExponent_le (second : Fin 3 → ℕ) (x : (Fin 3 × Fin k) → Fin M) :
    m.minorExponent second x ≤ k := Nat.findGreatest_le k

theorem minorExponent_spec (second : Fin 3 → ℕ) (x : (Fin 3 × Fin k) → Fin M) :
    m.allMinors second x (m.minorExponent second x) := by
  apply Nat.findGreatest_spec (Nat.zero_le k)
  intro s t c e
  simp only [pow_zero, one_dvd]

theorem minorExponent_schur (second : Fin 3 → ℕ) (x : (Fin 3 × Fin k) → Fin M)
    (j : ℕ) (hj : j ≤ m.minorExponent second x) : m.schur j x := by
  intro c _
  have hd := (pow_dvd_pow (m.base : ℤ) hj).trans (m.minorExponent_spec second x 0 2 0 c)
  simp only [matrix, if_true, show (2 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 1 by decide, if_false] at hd
  apply Nat.modEq_iff_dvd.mpr
  simp only [Nat.cast_pow, Nat.cast_mul]
  simpa only [neg_sub] using (dvd_neg.mpr hd)

theorem minorExponent_top (second : Fin 3 → ℕ) (x : (Fin 3 × Fin k) → Fin M) :
    (m.base : ℤ)^(m.minorExponent second x) ∣
      (m.top 0 : ℤ)*second 2 - (m.top 2 : ℤ)*second 0 := by
  have h := m.minorExponent_spec second x 0 1 0 2
  simpa [matrix] using h

theorem actual_uniform_moment (hM : 0 < M) (second : Fin 3 → ℕ)
    (hscale : (m.base : ℚ)/(M : ℚ)^2 ≤ 1/2) :
    average (fun x => (m.base : ℚ)^(m.minorExponent second x)) ≤ 2 :=
  m.uniform_divisor_moment hM (m.minorExponent second) (m.minorExponent_le second)
    (m.minorExponent_schur second) hscale

end DigitModel
#print axioms first_differing_tag
#print axioms tagged_minor_first
#print axioms eval_first_valuation
#print axioms DigitModel.minorExponent_spec
#print axioms DigitModel.minorExponent_schur
#print axioms DigitModel.actual_uniform_moment

end HeilbronnFive
