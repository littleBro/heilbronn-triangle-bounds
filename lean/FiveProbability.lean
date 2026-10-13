import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.GeomSum
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-! Finite uniform probability, expressed as exact rational averages.
The counting arguments work for every alphabet and every finite set of positions.
-/

namespace HeilbronnFive
open Finset

noncomputable def average {Ω : Type*} [Fintype Ω] (f : Ω → ℚ) : ℚ :=
  (∑ x, f x) / Fintype.card Ω

noncomputable def probability {Ω : Type*} [Fintype Ω] (E : Ω → Prop) : ℚ :=
  by classical exact average (fun x => if E x then 1 else 0)

theorem average_indicator {Ω : Type*} [Fintype Ω] (E : Ω → Prop) [DecidablePred E] :
    average (fun x => if E x then 1 else 0) = probability E := by
  unfold probability
  congr 1
  funext x
  by_cases h : E x <;> simp [h]

theorem probability_card {Ω : Type*} [Fintype Ω] (E : Ω → Prop) [DecidablePred E] :
    probability E = (Fintype.card {x // E x} : ℚ) / Fintype.card Ω := by
  classical
  unfold probability average
  congr 1
  rw [Fintype.card_subtype]
  calc
    _ = ∑ x : Ω, if E x then (1 : ℚ) else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases h : E x <;> simp [h]
    _ = _ := Finset.sum_boole (α := ℚ) E Finset.univ

/-- An event has at most one completion on `s` for every assignment outside `s`.
Its uniform probability is at most one over the number of possible completions. -/
theorem probability_le_of_completion {I : Type*} [Fintype I] [DecidableEq I]
    {M : ℕ} (hM : 0 < M) (s : Finset I) (E : (I → Fin M) → Prop)
    (h : ∀ x y, E x → E y → (∀ i, i ∉ s → x i = y i) → x = y) :
    probability E ≤ 1 / (M : ℚ) ^ s.card := by
  classical
  let f : {x // E x} → (↥sᶜ → Fin M) := fun x i => x.val i.val
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply h x.val y.val x.property y.property
    intro i hi
    exact congrFun hxy ⟨i, by simpa using hi⟩
  have hc := Fintype.card_le_of_injective f hf
  have hc' : Fintype.card {x // E x} ≤ M ^ sᶜ.card := by
    simpa only [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe] using hc
  have hp : M ^ sᶜ.card * M ^ s.card = M ^ Fintype.card I := by
    rw [← pow_add, Finset.card_compl_add_card]
  have hn := Nat.mul_le_mul_right (M ^ s.card) hc'
  rw [hp] at hn
  have hMq : (0 : ℚ) < M := by exact_mod_cast hM
  rw [probability_card]
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  apply (div_le_div_iff (pow_pos hMq _) (pow_pos hMq _)).mpr
  simp only [one_mul]
  exact_mod_cast hn

theorem average_mono {Ω : Type*} [Fintype Ω] {f g : Ω → ℚ}
    (h : ∀ x, f x ≤ g x) : average f ≤ average g := by
  unfold average
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => h x)) (by positivity)

theorem probability_mono {Ω : Type*} [Fintype Ω] {E F : Ω → Prop}
    (h : ∀ x, E x → F x) : probability E ≤ probability F := by
  classical
  unfold probability
  apply average_mono
  intro x
  by_cases he : E x
  · simp [he, h x he]
  · simp [he]; split_ifs <;> norm_num

theorem average_sum {Ω I : Type*} [Fintype Ω] (s : Finset I) (f : I → Ω → ℚ) :
    average (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, average (f i) := by
  simp only [average, Finset.sum_div]
  exact Finset.sum_comm

theorem average_mul {Ω : Type*} [Fintype Ω] (c : ℚ) (f : Ω → ℚ) :
    average (fun x => c * f x) = c * average f := by
  simp only [average, ← Finset.mul_sum, mul_div_assoc]

theorem average_add {Ω : Type*} [Fintype Ω] (f g : Ω → ℚ) :
    average (fun x => f x + g x) = average f + average g := by
  simp only [average, Finset.sum_add_distrib, add_div]

theorem average_equiv {Ω Ψ : Type*} [Fintype Ω] [Fintype Ψ]
    (e : Ω ≃ Ψ) (f : Ψ → ℚ) : average (fun x => f (e x)) = average f := by
  unfold average
  rw [Fintype.card_congr e]
  congr 1
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem average_product {Λ Ω : Type*} [Fintype Λ] [Fintype Ω] (f : Λ → Ω → ℚ) :
    average (fun x : Λ × Ω => f x.1 x.2) = average (fun l => average (f l)) := by
  simp only [average, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    Finset.sum_div, div_div]
  apply Finset.sum_congr rfl
  intro l _
  rw [mul_comm (Fintype.card Ω : ℚ)]

theorem geometric_sum_le_two {q : ℚ} (hq : 0 ≤ q) (hq' : q ≤ 1/2) (n : ℕ) :
    ∑ j ∈ Finset.range n, q ^ j ≤ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ']
    simp only [pow_succ', ← Finset.mul_sum, pow_zero]
    have := mul_le_mul_of_nonneg_left ih hq
    linarith

/-- The tail sum is finite; no convergence or interchange of infinite sums is used. -/
theorem divisor_moment_of_joint_tails {Ω : Type*} [Fintype Ω]
    (B M : ℕ) (hM : 0 < M) (a t : ℕ) (b : Ω → ℕ) (E : Ω → Prop) [DecidablePred E]
    (hb : ∀ x, E x → b x ≤ a)
    (htail : ∀ j, j ≤ a → probability (fun x => E x ∧ j ≤ b x) ≤
      1 / (M : ℚ) ^ (2 * j + t))
    (hscale : (B : ℚ) / (M : ℚ)^2 ≤ 1/2) :
    average (fun x => if E x then (B : ℚ) ^ b x else 0) ≤ 2 / (M : ℚ)^t := by
  classical
  have hMq : (0 : ℚ) < M := by exact_mod_cast hM
  have hBn : (0 : ℚ) ≤ B := by positivity
  have pointwise (x : Ω) :
      (if E x then (B : ℚ)^b x else 0) ≤
        ∑ j ∈ range (a+1), (B : ℚ)^j * (if E x ∧ j ≤ b x then 1 else 0) := by
    by_cases hx : E x
    · rw [if_pos hx]
      have hp := Finset.single_le_sum (f := fun j => (B : ℚ)^j *
          (if E x ∧ j ≤ b x then 1 else 0))
        (fun j _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le (hb x hx)))
      simpa only [hx, le_refl, and_self, if_true, mul_one] using hp
    · simp [hx]
  calc
    _ ≤ average (fun x => ∑ j ∈ range (a+1), (B : ℚ)^j *
        (if E x ∧ j ≤ b x then 1 else 0)) := average_mono pointwise
    _ = ∑ j ∈ range (a+1), (B : ℚ)^j * probability (fun x => E x ∧ j ≤ b x) := by
      rw [average_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [average_mul, average_indicator]
    _ ≤ ∑ j ∈ range (a+1), (B : ℚ)^j * (1 / (M : ℚ)^(2*j+t)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left
        (htail j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))) (pow_nonneg hBn _)
    _ = (1 / (M : ℚ)^t) * ∑ j ∈ range (a+1), ((B : ℚ)/(M : ℚ)^2)^j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [div_pow, pow_add, pow_mul]
      ring
    _ ≤ (1 / (M : ℚ)^t) * 2 :=
      mul_le_mul_of_nonneg_left
        (geometric_sum_le_two (by positivity) hscale _) (by positivity)
    _ = _ := by ring

#print axioms probability_le_of_completion
#print axioms average_product
#print axioms divisor_moment_of_joint_tails

end HeilbronnFive
