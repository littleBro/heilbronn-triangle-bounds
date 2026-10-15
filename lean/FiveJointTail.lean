import FiveDigits

/-! Joint tails proved by injection into assignments of the remaining digits.
No independence between the minor event and the coefficient event is assumed. -/

namespace HeilbronnFive
open Finset

namespace DigitModel
variable {k M : ℕ} (m : DigitModel k M)

def lowPositions (j : ℕ) : Finset (Fin 3 × Fin k) :=
  ({1,2} : Finset (Fin 3)).product (univ.filter (fun p => p.val < j))

theorem lowPositions_mem {j : ℕ} {c : Fin 3} {p : Fin k} :
    (c,p) ∈ lowPositions (k := k) j ↔ c ≠ 0 ∧ p.val < j := by
  change (c,p) ∈ (({1,2} : Finset (Fin 3)) ×ˢ
    (univ.filter (fun p : Fin k => p.val < j))) ↔ _
  simp only [mem_product, mem_insert, mem_singleton, mem_filter, mem_univ,
    true_and]
  have hc := c.isLt
  constructor
  · rintro ⟨h,hp⟩
    constructor
    · rcases h with h | h <;> subst c <;> decide
    · exact hp
  · rintro ⟨h,hp⟩
    refine ⟨?_, hp⟩
    have : c.val = 1 ∨ c.val = 2 := by
      have : c.val ≠ 0 := by intro he; exact h (Fin.ext he)
      omega
    exact this.imp Fin.ext Fin.ext

theorem lowPositions_card {j : ℕ} (hj : j ≤ k) :
    (lowPositions (k := k) j).card = 2*j := by
  change (({1,2} : Finset (Fin 3)) ×ˢ
    (univ.filter (fun p : Fin k => p.val < j))).card = _
  rw [card_product]
  have hc : ({1,2} : Finset (Fin 3)).card = 2 := by decide
  rw [hc]
  congr 1
  rw [← Fintype.card_subtype]
  exact Fintype.card_fin_lt_of_le hj

/-- The retained (non-fresh) conditional divisor tail, for arbitrary fixed labels. -/
theorem schur_probability (hM : 0 < M) {j : ℕ} (hj : j ≤ k) :
    probability (m.schur j) ≤ 1 / (M : ℚ)^(2*j) := by
  rw [← lowPositions_card hj]
  apply probability_le_of_completion hM
  intro x y hx hy hxy
  have hfirst : ∀ p, x (0,p) = y (0,p) := by
    intro p
    apply hxy
    simp only [lowPositions_mem, ne_eq, not_true_eq_false, false_and, not_false_eq_true]
  have hl := m.schur_prefix hj hx hy hfirst
  funext i
  by_cases hi : i ∈ lowPositions (k := k) j
  · exact hl i.1 i.2 (lowPositions_mem.mp hi).2
  · exact hxy i hi

/-- Two Schur prefixes and one disjoint coefficient equation fix `2*j+1` digits. -/
theorem fresh_joint_tail (hM : 0 < M) {j : ℕ} (hj : j ≤ k)
    (v : Fin k) (hv : j ≤ v.val) (w : (Fin 3 × Fin k) → ℤ)
    (hw : w (1,v) ≠ 0) (target : ℤ) :
    probability (fun x => m.schur j x ∧
      (∑ i, w i * (m.alphabet i (x i)).val) = target) ≤
      1 / (M : ℚ)^(2*j+1) := by
  let s := insert (1,v) (lowPositions (k := k) j)
  have hnot : (1,v) ∉ lowPositions (k := k) j := by
    rw [lowPositions_mem]
    omega
  have hc : s.card = 2*j+1 := by
    change (insert (1,v) (lowPositions (k := k) j)).card = _
    rw [card_insert_of_not_mem hnot, lowPositions_card hj]
  rw [← hc]
  apply probability_le_of_completion hM
  intro x y hx hy hxy
  have hfirst : ∀ p, x (0,p) = y (0,p) := by
    intro p
    apply hxy
    simp [s, lowPositions_mem]
  have hl := m.schur_prefix hj hx.1 hy.1 hfirst
  have hrest : ∀ i, i ≠ (1,v) → x i = y i := by
    intro i hi
    by_cases hi' : i ∈ lowPositions (k := k) j
    · exact hl i.1 i.2 (lowPositions_mem.mp hi').2
    · apply hxy; simpa [s] using And.intro hi hi'
  have hf := linear_fresh_unique m.alphabet m.alphabet_injective w (1,v) hw hrest
    (hx.2.trans hy.2.symm)
  funext i
  by_cases hi : i = (1,v)
  · simpa [hi] using hf
  · exact hrest i hi

/-- The previous uniform moment estimate is now a finite counting theorem too. -/
theorem uniform_divisor_moment (hM : 0 < M)
    (b : ((Fin 3 × Fin k) → Fin M) → ℕ)
    (hb : ∀ x, b x ≤ k)
    (hschur : ∀ x j, j ≤ b x → m.schur j x)
    (hscale : (m.base : ℚ)/(M : ℚ)^2 ≤ 1/2) :
    average (fun x => (m.base : ℚ)^b x) ≤ 2 := by
  have h := divisor_moment_of_joint_tails m.base M hM k 0 b (fun _ => True)
    (fun x _ => hb x) (fun j hj => ?_) hscale
  · simpa only [if_true, pow_zero, div_one] using h
  · simpa only [Nat.add_zero] using
      (probability_mono (fun x hx => hschur x j hx.2)).trans (m.schur_probability hM hj)

/-- Main conditional estimate for two equal labels, with the actual independent
digit sample space and the coefficient equation, not a hypothesized tail bound. -/
theorem fresh_divisor_moment (hM : 0 < M) (a : ℕ) (ha : a ≤ k)
    (v : Fin k) (hv : a ≤ v.val) (w : (Fin 3 × Fin k) → ℤ)
    (hw : w (1,v) ≠ 0) (target : ℤ)
    (b : ((Fin 3 × Fin k) → Fin M) → ℕ) (hb : ∀ x, b x ≤ a)
    (hschur : ∀ x j, j ≤ b x → m.schur j x)
    (hscale : (m.base : ℚ)/(M : ℚ)^2 ≤ 1/2) :
    average (fun x => if (∑ i, w i * (m.alphabet i (x i)).val) = target
      then (m.base : ℚ)^b x else 0) ≤ 2/(M : ℚ) := by
  have h := divisor_moment_of_joint_tails m.base M hM a 1 b
    (fun x => (∑ i, w i * (m.alphabet i (x i)).val) = target)
    (fun x _ => hb x) (fun j hj => ?_) hscale
  · simpa only [pow_one] using h
  · exact (probability_mono (fun x hx => And.intro (hschur x j hx.2) hx.1)).trans
      (m.fresh_joint_tail hM (le_trans hj ha) v (le_trans hj hv) w hw target)

end DigitModel
#print axioms DigitModel.lowPositions_card
#print axioms DigitModel.schur_probability
#print axioms DigitModel.fresh_joint_tail
#print axioms DigitModel.uniform_divisor_moment
#print axioms DigitModel.fresh_divisor_moment

end HeilbronnFive
