import FrobeniusOrbits

/-! Rotation orbits of five-letter words indexed by a group of order thirteen.
    Five constant words are fixed; all other orbits have size thirteen. -/

open Finset Equiv MulAction

namespace HeilbronnRankFive

variable (G : Type*) [Group G]

-- A wrapper keeps this translation action separate from the pointwise action.
structure Pattern where
  word : G → Fin 5

omit [Group G] in
theorem Pattern.ext {u v : Pattern G} (h : u.word = v.word) : u = v := by
  cases u
  cases v
  cases h
  rfl

def constantPattern (i : Fin 5) : Pattern G := ⟨fun _ => i⟩

instance : MulAction G (Pattern G) where
  smul a w := ⟨fun g => w.word (a⁻¹ * g)⟩
  one_smul w := by
    apply Pattern.ext
    funext g
    change w.word (1⁻¹ * g) = w.word g
    simp
  mul_smul a b w := by
    apply Pattern.ext
    funext g
    change w.word ((a * b)⁻¹ * g) = w.word (b⁻¹ * (a⁻¹ * g))
    simp [mul_assoc]

lemma rotate_apply (a : G) (w : Pattern G) (g : G) :
    (a • w).word g = w.word (a⁻¹ * g) := rfl

lemma constant_fixed (i : Fin 5) (a : G) : a • constantPattern G i = constantPattern G i := rfl

def patternEquiv : Pattern G ≃ (G → Fin 5) where
  toFun := Pattern.word
  invFun := Pattern.mk
  left_inv w := by cases w; rfl
  right_inv _ := rfl

variable [Fintype G]

noncomputable instance : Fintype (Pattern G) := by
  classical
  exact Fintype.ofEquiv _ (patternEquiv G).symm

omit [Group G] in
theorem pattern_card (hc : Fintype.card G = 13) : Fintype.card (Pattern G) = 5 ^ 13 := by
  classical
  rw [Fintype.card_congr (patternEquiv G), Fintype.card_fun, Fintype.card_fin, hc]

omit [Fintype G] in
theorem fixed_pattern (w : Pattern G) (hw : ∀ a : G, a • w = w) :
    w = constantPattern G (w.word 1) := by
  apply Pattern.ext
  funext g
  have h := congrArg (fun z : Pattern G => z.word g) (hw g)
  simpa [rotate_apply, constantPattern] using h.symm

noncomputable instance (w : Pattern G) : Fintype (orbit G w) := Fintype.ofFinite _
noncomputable instance (w : Pattern G) : Fintype (stabilizer G w) := Fintype.ofFinite _

abbrev Classes := MulAction.orbitRel.Quotient G (Pattern G)

noncomputable instance : Fintype (Classes G) := by
  classical
  infer_instance

noncomputable instance : DecidableEq (Classes G) := Classical.decEq _

def constantClass (i : Fin 5) : Classes G := Quotient.mk'' (constantPattern G i)

omit [Fintype G] in
lemma constantClass_injective : Function.Injective (constantClass G) := by
  intro i j h
  obtain ⟨_, ha⟩ := Quotient.exact' h
  have he : constantPattern G j = constantPattern G i := ha
  exact (congrArg (fun w : Pattern G => w.word 1) he).symm

noncomputable def constantClasses : Finset (Classes G) := by
  classical
  exact Finset.univ.image (constantClass G)

lemma constantClasses_card : (constantClasses G).card = 5 := by
  classical
  rw [constantClasses, Finset.card_image_of_injective _ (constantClass_injective G)]
  rfl

omit [Fintype G] in
lemma out_constant_iff (q : Classes G) :
    (∃ i, q.out' = constantPattern G i) ↔ q ∈ constantClasses G := by
  classical
  constructor
  · rintro ⟨i, hi⟩
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_univ _, ?_⟩
    rw [← Quotient.out_eq' q, hi]
    rfl
  · intro h
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    refine ⟨i, ?_⟩
    have he : (Quotient.mk'' q.out' : Classes G) = Quotient.mk'' (constantPattern G i) :=
      (Quotient.out_eq' q).trans hi.symm
    obtain ⟨a, ha⟩ := Quotient.exact' he
    exact ha.symm.trans (constant_fixed G i a)

theorem orbit_size (hc : Fintype.card G = 13) (q : Classes G) :
    Fintype.card (orbit G q.out') = if q ∈ constantClasses G then 1 else 13 := by
  classical
  by_cases hq : q ∈ constantClasses G
  · rw [if_pos hq]
    obtain ⟨i, hi⟩ := (out_constant_iff G q).mpr hq
    rw [hi]
    exact mem_fixedPoints_iff_card_orbit_eq_one.mp (constant_fixed G i)
  · rw [if_neg hq]
    have hdiv : Fintype.card (orbit G q.out') ∣ 13 :=
      ⟨Fintype.card (stabilizer G q.out'), by
        rw [← hc, card_orbit_mul_card_stabilizer_eq_card_group]⟩
    rcases (show Nat.Prime 13 by decide).eq_one_or_self_of_dvd _ hdiv with h | h
    · exfalso
      apply hq
      apply (out_constant_iff G q).mp
      exact ⟨_, fixed_pattern G q.out' (mem_fixedPoints_iff_card_orbit_eq_one.mpr h)⟩
    · exact h

theorem class_card (hc : Fintype.card G = 13) : Fintype.card (Classes G) = 93900245 := by
  classical
  have h := Fintype.card_congr (selfEquivSigmaOrbits G (Pattern G))
  rw [pattern_card G hc, Fintype.card_sigma] at h
  simp_rw [orbit_size G hc] at h
  have hr (q : Classes G) :
      (if q ∈ constantClasses G then 1 else 13) +
        (if q ∈ constantClasses G then 12 else 0) = 13 := by split <;> simp_all
  have hs := congrArg (fun f : Classes G → ℕ => ∑ q, f q) (funext hr)
  simp only [Finset.sum_add_distrib] at hs
  rw [← h] at hs
  simp [constantClasses_card, Finset.sum_ite_mem] at hs
  omega

theorem invariant_sum {F : Type*} [CommRing F] (f : Pattern G → F)
    (hf : ∀ (a : G) (w : Pattern G), f (a • w) = f w) :
    (∑ w, f w) = ∑ q : Classes G, (Fintype.card (orbit G q.out') : F) * f q.out' := by
  classical
  let e := selfEquivSigmaOrbits G (Pattern G)
  calc
    (∑ w, f w) = ∑ s : Σ q : Classes G, orbit G q.out', f s.2.1 := by
      apply Fintype.sum_equiv e
      intro w
      rfl
    _ = _ := by
      rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro q _
      have he (v : orbit G q.out') : f v.1 = f q.out' := by
        obtain ⟨a, ha⟩ := v.property
        rw [← ha]
        exact hf a q.out'
      simp_rw [he]
      simp [nsmul_eq_mul]

#print axioms fixed_pattern
#print axioms orbit_size
#print axioms class_card
#print axioms invariant_sum

end HeilbronnRankFive
