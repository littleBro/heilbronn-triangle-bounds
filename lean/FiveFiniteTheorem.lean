import FiveReindex

/-! A complete finite probability interface: the pair premise consists of digit
and tag data, not a probability estimate. Distinct-label exclusion is the
separate norm/packing interface; geometry and orbit bounds are not assumed here. -/

namespace HeilbronnFive

structure TaggedData {k M : ℕ} (m : DigitModel k M) (second : Fin 3 → ℕ) where
  A : Polynomial ℤ
  A' : Polynomial ℤ
  Q : Polynomial ℤ
  Q' : Polynomial ℤ
  a : ℕ
  d : ℕ
  r : ℕ
  L : ℕ
  first_lt : a < d
  room : 2*d ≤ k
  residue_le_base : r ≤ m.base
  top_prefix : ∀ i, i ≤ a → A.coeff i = A'.coeff i
  top_constant : A.coeff 0 = 1
  label_prefix : ∀ i, i < a → Q.coeff i = Q'.coeff i
  differing : Q.coeff a ≠ Q'.coeff a
  positive_left : 1 ≤ Q.coeff a
  positive_right : 1 ≤ Q'.coeff a
  bounded_left : Q.coeff a ≤ r
  bounded_right : Q'.coeff a ≤ r
  top_eval_left : A.eval (m.base : ℤ) = m.top 0
  top_eval_right : A'.eval (m.base : ℤ) = m.top 2
  second_eval_left : Q.eval (m.base : ℤ) = second 0
  second_eval_right : Q'.eval (m.base : ℤ) = second 2
  repeated_top : m.top 1 = m.top 0
  repeated_second : second 1 = second 0
  top_range_left : ∀ i, i < k → |A.coeff i| ≤ r
  top_range_right : ∀ i, i < k → |A'.coeff i| ≤ r
  second_range_left : ∀ i, i < k → |Q.coeff i| ≤ r
  second_range_right : ∀ i, i < k → |Q'.coeff i| ≤ r
  bottom_range : ∀ i x, (m.alphabet i x).val ≤ L
  base_large : 100*k^2*r^2*L < m.base

theorem TaggedData.moment {k M : ℕ} {m : DigitModel k M} {second : Fin 3 → ℕ}
    (t : TaggedData m second) (hM : 0 < M)
    (hscale : (m.base : ℚ)/(M : ℚ)^2 ≤ 1/2) : m.smallMoment second ≤ 2/(M : ℚ) :=
  m.tagged_small_residue_moment hM second t.A t.A' t.Q t.Q' t.a t.d t.r t.L
    t.first_lt t.room t.residue_le_base t.top_prefix t.top_constant t.label_prefix
    t.differing t.positive_left t.positive_right t.bounded_left t.bounded_right
    t.top_eval_left t.top_eval_right t.second_eval_left t.second_eval_right
    t.repeated_top t.repeated_second t.top_range_left t.top_range_right
    t.second_range_left t.second_range_right t.bottom_range t.base_large hscale

/-- The full finite collision estimate for N independent uniform labels.
The all-equal bound and the probabilities of label collisions are derived here.
For every exactly-two label triple the hypothesis supplies only explicit tag data,
possibly after a column permutation. -/
theorem total_small_residue_moment {N k M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (models : (Fin 3 → Fin N) → DigitModel k M)
    (second : (Fin 3 → Fin N) → Fin 3 → ℕ)
    (hscale : ∀ l, ((models l).base : ℚ)/(M : ℚ)^2 ≤ 1/2)
    (htags : ∀ l, (l 0 = l 1 ∨ l 0 = l 2 ∨ l 1 = l 2) →
      ¬(l 0 = l 1 ∧ l 0 = l 2) →
      ∃ σ : Equiv.Perm (Fin 3), ∃ hu : Nat.Coprime (models l).base ((models l).top (σ 0)),
        Nonempty (TaggedData ((models l).permute σ hu) (fun c => second l (σ c))))
    (hdistinct : ∀ l, l 0 ≠ l 1 → l 0 ≠ l 2 → l 1 ≠ l 2 →
      ∀ x, ¬(models l).smallResidue (second l) x) :
    average (fun l => (models l).smallMoment (second l)) ≤
      6/((M : ℚ)*N) + 2/(N : ℚ)^2 := by
  classical
  apply label_mixture_moment hN hM
  · intro l hp hn
    obtain ⟨σ,hu,⟨data⟩⟩ := htags l hp hn
    rw [← (models l).smallMoment_permute σ hu (second l)]
    exact data.moment hM (hscale l)
  · intro l _ _
    exact (models l).smallMoment_le_uniform hM (second l) (hscale l)
  · intro l h01 h02 h12
    unfold DigitModel.smallMoment average
    have he : (fun x => if (models l).smallResidue (second l) x then
        ((models l).base : ℚ)^((models l).minorExponent (second l) x) else 0) =
        fun _ => (0 : ℚ) := by
      funext x
      rw [if_neg (hdistinct l h01 h02 h12 x)]
    rw [he]
    simp only [Finset.sum_const_zero, zero_div]

#print axioms TaggedData.moment
#print axioms total_small_residue_moment

end HeilbronnFive
