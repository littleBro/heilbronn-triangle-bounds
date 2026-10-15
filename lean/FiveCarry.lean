import FiveTags

/-! Balanced base coefficients turn a small determinant residue into the
integer coefficient equation used in the finite probability theorem. -/

namespace HeilbronnFive
open Finset Polynomial

def truncEval (F : ℤ[X]) (B n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range n, F.coeff i * (B : ℤ)^i

theorem truncEval_bound (F : ℤ[X]) {B n : ℕ} (hB : 1 ≤ B)
    (hc : ∀ i, i < n → 2*|F.coeff i| ≤ (B : ℤ)-1) :
    2*|truncEval F B n| ≤ (B : ℤ)^n-1 := by
  induction n with
  | zero => simp [truncEval]
  | succ n ih =>
    have hprev := ih (fun i hi => hc i (by omega))
    have hlast := hc n (by omega)
    have hpow : 0 ≤ (B : ℤ)^n := by positivity
    have hm := mul_le_mul_of_nonneg_right hlast hpow
    have habs := abs_add (truncEval F B n) (F.coeff n * (B : ℤ)^n)
    rw [abs_mul, abs_of_nonneg hpow] at habs
    change 2*|∑ i ∈ range (n+1), F.coeff i * (B : ℤ)^i| ≤ _
    rw [Finset.sum_range_succ, pow_succ]
    change 2*|truncEval F B n + F.coeff n * (B : ℤ)^n| ≤ _
    nlinarith

theorem eval_sub_trunc_dvd (F : ℤ[X]) (B k : ℕ) :
    (B : ℤ)^k ∣ F.eval (B : ℤ) - truncEval F B k := by
  rw [Polynomial.eval_eq_sum_range' (n := k+(F.natDegree+1)) (by omega),
    Finset.sum_range_add]
  simp only [truncEval, add_sub_cancel_left]
  apply Finset.dvd_sum
  intro i _
  exact (pow_dvd_pow (B : ℤ) (Nat.le_add_right k i)).mul_left _

/-- Small residues cannot be produced by a nonzero next-to-leading base digit.
`2*abs(t) ≤ B^(k-1)` includes the manuscript's floor threshold exactly. -/
theorem small_residue_coefficient (F : ℤ[X]) {B k : ℕ}
    (hB : 1 ≤ B) (hk : 0 < k)
    (hc : ∀ i, i < k → 2*|F.coeff i| ≤ (B : ℤ)-1)
    (ht : ∃ t : ℤ, (B : ℤ)^k ∣ F.eval (B : ℤ)-t ∧
      2*|t| ≤ (B : ℤ)^(k-1)) : F.coeff (k-1) = 0 := by
  obtain ⟨t, hd, ht⟩ := ht
  have hb : (1 : ℤ) ≤ B := by exact_mod_cast hB
  have hp : 0 < (B : ℤ)^(k-1) := pow_pos (by omega) _
  have hcenter := truncEval_bound F hB hc
  have hlower := truncEval_bound F hB (fun i hi => hc i (by omega : i < k))
    (n := k-1)
  have hpow : (B : ℤ)^(k-1) ≤ (B : ℤ)^k := by
    calc
      _ ≤ (B : ℤ)^(k-1) * B := le_mul_of_one_le_right (le_of_lt hp) hb
      _ = _ := by rw [← pow_succ]; congr 1; omega
  have hdiv : (B : ℤ)^k ∣ truncEval F B k - t := by
    have := dvd_sub hd (eval_sub_trunc_dvd F B k)
    convert this using 1 <;> ring
  have he : truncEval F B k = t := by
    apply sub_eq_zero.mp
    apply Int.eq_zero_of_abs_lt_dvd hdiv
    have habs := abs_sub (truncEval F B k) t
    omega
  have hsplit : truncEval F B k = truncEval F B (k-1) +
      F.coeff (k-1) * (B : ℤ)^(k-1) := by
    nth_rw 1 [show k = (k-1)+1 by omega]
    exact Finset.sum_range_succ _ _
  by_contra hne
  have habsc : 1 ≤ |F.coeff (k-1)| := by
    have : 0 < |F.coeff (k-1)| := abs_pos.mpr hne
    omega
  have hm := mul_le_mul_of_nonneg_right habsc (le_of_lt hp)
  have habs := abs_sub t (truncEval F B (k-1))
  have heq : t - truncEval F B (k-1) = F.coeff (k-1) * (B : ℤ)^(k-1) := by
    rw [← he, hsplit]; ring
  rw [heq, abs_mul, abs_of_pos hp] at habs
  nlinarith

#print axioms truncEval_bound
#print axioms eval_sub_trunc_dvd
#print axioms small_residue_coefficient

end HeilbronnFive
