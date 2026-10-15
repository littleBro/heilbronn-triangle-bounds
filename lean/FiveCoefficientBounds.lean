import FiveMoment
import FiveCarry

/-! The balanced-coefficient hypotheses follow from the digit range bounds. -/

namespace HeilbronnFive
open Finset Polynomial

theorem product_coefficient_bound (P Q : ℤ[X]) (n : ℕ) (L K : ℤ)
    (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hP : ∀ i, i ≤ n → |P.coeff i| ≤ L)
    (hQ : ∀ i, i ≤ n → |Q.coeff i| ≤ K) :
    |(P*Q).coeff n| ≤ (n+1)*L*K := by
  rw [coeff_mul]
  calc
    _ ≤ ∑ p ∈ Finset.antidiagonal n, |P.coeff p.1 * Q.coeff p.2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ Finset.antidiagonal n, L*K := by
      apply Finset.sum_le_sum
      intro p hp
      have hp' := Finset.mem_antidiagonal.mp hp
      rw [abs_mul]
      exact mul_le_mul (hP p.1 (by omega)) (hQ p.2 (by omega)) (abs_nonneg _) hL
    _ = _ := by simp only [Finset.sum_const, Finset.Nat.card_antidiagonal,
        nsmul_eq_mul, Nat.cast_add, Nat.cast_one]; ring

theorem triple_coefficient_bound (P Q R : ℤ[X]) (n : ℕ) (L1 L2 L3 : ℤ)
    (hL1 : 0 ≤ L1) (hL2 : 0 ≤ L2) (hL3 : 0 ≤ L3)
    (hP : ∀ i, i ≤ n → |P.coeff i| ≤ L1)
    (hQ : ∀ i, i ≤ n → |Q.coeff i| ≤ L2)
    (hR : ∀ i, i ≤ n → |R.coeff i| ≤ L3) :
    |(P*Q*R).coeff n| ≤ (n+1)^2*L1*L2*L3 := by
  have hpq : ∀ i, i ≤ n → |(P*Q).coeff i| ≤ (n+1)*L1*L2 := by
    intro i hi
    apply (product_coefficient_bound P Q i L1 L2 hL1 hL2
      (fun j hj => hP j (le_trans hj hi)) (fun j hj => hQ j (le_trans hj hi))).trans
    have hcast : (i : ℤ) ≤ n := by exact_mod_cast hi
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by omega : (i : ℤ)+1 ≤ n+1) hL1) hL2
  have h := product_coefficient_bound (P*Q) R n ((n+1)*L1*L2) L3
    (by positivity) hL3 hpq hR
  convert h using 1 <;> ring

theorem six_term_abs (a b c d e f C : ℤ)
    (ha : |a| ≤ C) (hb : |b| ≤ C) (hc : |c| ≤ C)
    (hd : |d| ≤ C) (he : |e| ≤ C) (hf : |f| ≤ C) :
    |a-b-c+d+e-f| ≤ 6*C := by
  have h1 := abs_sub a b
  have h2 := abs_sub (a-b) c
  have h3 := abs_add (a-b-c) d
  have h4 := abs_add (a-b-c+d) e
  have h5 := abs_sub (a-b-c+d+e) f
  linarith

theorem determinant_coefficient_bound (P : Matrix (Fin 3) (Fin 3) ℤ[X])
    (L : Fin 3 → ℤ) (hL : ∀ r, 0 ≤ L r) (k n : ℕ) (hn : n < k)
    (hP : ∀ r c i, i < k → |(P r c).coeff i| ≤ L r) :
    |(Matrix.det P).coeff n| ≤ 6*(k : ℤ)^2*L 0*L 1*L 2 := by
  have hterm (c0 c1 c2 : Fin 3) :
      |(P 0 c0 * P 1 c1 * P 2 c2).coeff n| ≤ (k : ℤ)^2*L 0*L 1*L 2 := by
    have ht := triple_coefficient_bound (P 0 c0) (P 1 c1) (P 2 c2) n
      (L 0) (L 1) (L 2) (hL 0) (hL 1) (hL 2)
      (fun i hi => hP 0 c0 i (lt_of_le_of_lt hi hn))
      (fun i hi => hP 1 c1 i (lt_of_le_of_lt hi hn))
      (fun i hi => hP 2 c2 i (lt_of_le_of_lt hi hn))
    apply ht.trans
    have hk : (n : ℤ)+1 ≤ k := by exact_mod_cast hn
    have hsq : ((n : ℤ)+1)^2 ≤ (k : ℤ)^2 := by nlinarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsq (hL 0)) (hL 1)) (hL 2)
  rw [Matrix.det_fin_three]
  simp only [coeff_add, coeff_sub]
  convert six_term_abs _ _ _ _ _ _ _ (hterm 0 1 2) (hterm 0 2 1)
    (hterm 1 0 2) (hterm 1 2 0) (hterm 2 0 1) (hterm 2 1 0) using 1 <;> ring

/-- The manuscript's lower bound on B is more than sufficient for balanced digits. -/
theorem determinant_balanced_coefficients (P : Matrix (Fin 3) (Fin 3) ℤ[X])
    (L : Fin 3 → ℕ) (k B : ℕ) (hB : 100*k^2*L 0*L 1*L 2 < B)
    (hP : ∀ r c i, i < k → |(P r c).coeff i| ≤ L r) :
    ∀ i, i < k → 2*|(Matrix.det P).coeff i| ≤ (B : ℤ)-1 := by
  intro i hi
  have hb : 100*(k : ℤ)^2*L 0*L 1*L 2 < B := by exact_mod_cast hB
  have h := determinant_coefficient_bound P (fun r => (L r : ℤ))
    (fun _ => by positivity) k i hi hP
  have hp : 0 ≤ (k : ℤ)^2 * L 0 * L 1 * L 2 := by positivity
  nlinarith

#print axioms determinant_coefficient_bound
#print axioms determinant_balanced_coefficients

end HeilbronnFive
