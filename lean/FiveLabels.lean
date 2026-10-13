import FiveProbability
import Mathlib.Tactic.FinCases

/-! Averaging the three label cases, including the all-equal contribution. -/

namespace HeilbronnFive
open Finset

theorem label_pair_probability {N : ℕ} (hN : 0 < N) (i j : Fin 3) (hij : i ≠ j) :
    probability (fun x : Fin 3 → Fin N => x i = x j) ≤ 1/(N : ℚ) := by
  have h := probability_le_of_completion hN ({j} : Finset (Fin 3))
    (fun x : Fin 3 → Fin N => x i = x j) (fun x y hx hy hxy => ?_)
  · simpa only [Finset.card_singleton, pow_one] using h
  · funext p
    by_cases hp : p = j
    · subst p
      exact hx.symm.trans ((hxy i (by simpa using hij)).trans hy)
    · exact hxy p (by simpa using hp)

theorem label_all_equal_probability {N : ℕ} (hN : 0 < N) :
    probability (fun x : Fin 3 → Fin N => x 0 = x 1 ∧ x 0 = x 2) ≤ 1/(N : ℚ)^2 := by
  have h := probability_le_of_completion hN ({1,2} : Finset (Fin 3))
    (fun x : Fin 3 → Fin N => x 0 = x 1 ∧ x 0 = x 2) (fun x y hx hy hxy => ?_)
  · have hc : ({1,2} : Finset (Fin 3)).card = 2 := by decide
    simpa only [hc] using h
  · have hz := hxy 0 (by decide)
    funext p
    fin_cases p
    · exact hz
    · exact hx.1.symm.trans (hz.trans hy.1)
    · exact hx.2.symm.trans (hz.trans hy.2)

/-- `f` is the digit-conditional expectation. The result averages all labels;
it does not silently discard triples whose three labels coincide. -/
theorem label_mixture_moment {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (f : (Fin 3 → Fin N) → ℚ)
    (hpair : ∀ x, (x 0 = x 1 ∨ x 0 = x 2 ∨ x 1 = x 2) →
      ¬(x 0 = x 1 ∧ x 0 = x 2) → f x ≤ 2/(M : ℚ))
    (hall : ∀ x, x 0 = x 1 → x 0 = x 2 → f x ≤ 2)
    (hdistinct : ∀ x, x 0 ≠ x 1 → x 0 ≠ x 2 → x 1 ≠ x 2 → f x = 0) :
    average f ≤ 6/((M : ℚ)*N) + 2/(N : ℚ)^2 := by
  have hMq : (0 : ℚ) < M := by exact_mod_cast hM
  have hp : 0 ≤ 2/(M : ℚ) := by positivity
  let g := fun x : Fin 3 → Fin N =>
    2/(M : ℚ) * ((if x 0 = x 1 then 1 else 0) +
      (if x 0 = x 2 then 1 else 0) + (if x 1 = x 2 then 1 else 0)) +
      2*(if x 0 = x 1 ∧ x 0 = x 2 then 1 else 0)
  have hfg : ∀ x, f x ≤ g x := by
    intro x
    have hn01 : (0 : ℚ) ≤ if x 0 = x 1 then 1 else 0 := by split_ifs <;> norm_num
    have hn02 : (0 : ℚ) ≤ if x 0 = x 2 then 1 else 0 := by split_ifs <;> norm_num
    have hn12 : (0 : ℚ) ≤ if x 1 = x 2 then 1 else 0 := by split_ifs <;> norm_num
    have hn := mul_nonneg hp (add_nonneg (add_nonneg hn01 hn02) hn12)
    by_cases ha : x 0 = x 1 ∧ x 0 = x 2
    · dsimp only [g]
      rw [if_pos ha]
      have hh := hall x ha.1 ha.2
      linarith
    · by_cases hc : x 0 = x 1 ∨ x 0 = x 2 ∨ x 1 = x 2
      · have hs : (1 : ℚ) ≤ (if x 0 = x 1 then 1 else 0) +
            (if x 0 = x 2 then 1 else 0) + (if x 1 = x 2 then 1 else 0) := by
          rcases hc with h | h | h
          · rw [if_pos h]; linarith
          · rw [if_pos h]; linarith
          · rw [if_pos h]; linarith
        have hm := mul_le_mul_of_nonneg_left hs hp
        have hh := hpair x hc ha
        dsimp only [g]
        rw [if_neg ha]
        linarith
      · rw [hdistinct x (fun h => hc (Or.inl h))
            (fun h => hc (Or.inr (Or.inl h))) (fun h => hc (Or.inr (Or.inr h)))]
        dsimp only [g]
        rw [if_neg ha]
        linarith
  have hav : average g = 2/(M : ℚ) *
      (probability (fun x : Fin 3 → Fin N => x 0 = x 1) +
       probability (fun x : Fin 3 → Fin N => x 0 = x 2) +
       probability (fun x : Fin 3 → Fin N => x 1 = x 2)) +
       2*probability (fun x : Fin 3 → Fin N => x 0 = x 1 ∧ x 0 = x 2) := by
    simp only [g, average_add, average_mul, average_indicator]
  have h01 := label_pair_probability hN 0 1 (by decide)
  have h02 := label_pair_probability hN 0 2 (by decide)
  have h12 := label_pair_probability hN 1 2 (by decide)
  have ha := label_all_equal_probability hN
  have hs : 2/(M : ℚ) *
      (probability (fun x : Fin 3 → Fin N => x 0 = x 1) +
       probability (fun x : Fin 3 → Fin N => x 0 = x 2) +
       probability (fun x : Fin 3 → Fin N => x 1 = x 2)) ≤
      2/(M : ℚ)*(3/(N : ℚ)) := by
    apply mul_le_mul_of_nonneg_left _ hp
    convert add_le_add (add_le_add h01 h02) h12 using 1 <;> ring
  calc
    average f ≤ average g := average_mono hfg
    _ ≤ 2/(M : ℚ)*(3/(N : ℚ)) + 2/(N : ℚ)^2 := by
      rw [hav]
      convert add_le_add hs (mul_le_mul_of_nonneg_left ha (by norm_num : (0 : ℚ) ≤ 2))
        using 1 <;> ring
    _ = _ := by ring

#print axioms label_pair_probability
#print axioms label_all_equal_probability
#print axioms label_mixture_moment

end HeilbronnFive
