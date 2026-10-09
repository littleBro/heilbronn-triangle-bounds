import NormExpansion
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Tactic.Group

/-! Normalized permutation patterns under the degree-thirteen Galois action.
    The identity pattern is the only fixed point; every other orbit has size 13. -/

open Finset Equiv MulAction

namespace HeilbronnFrobenius
open HeilbronnNorm

variable (G : Type*) [Group G]

abbrev Pattern := {w : G → Equiv.Perm Row // w 1 = 1}

def trivialPattern : Pattern G := ⟨fun _ => 1, rfl⟩

def rotate (a : G) (w : Pattern G) : Pattern G :=
  ⟨fun g => w.1 (a⁻¹ * g) * (w.1 a⁻¹)⁻¹, by simp⟩

instance patternAction : MulAction G (Pattern G) where
  smul := rotate G
  one_smul w := by
    apply Subtype.ext
    funext g
    change (rotate G 1 w).1 g = w.1 g
    simp [rotate, w.property]
  mul_smul a b w := by
    apply Subtype.ext
    funext g
    change (rotate G (a * b) w).1 g = (rotate G a (rotate G b w)).1 g
    simp only [rotate, mul_inv_rev, mul_assoc]
    group

lemma rotate_apply (a : G) (w : Pattern G) (g : G) :
    (a • w).1 g = w.1 (a⁻¹ * g) * (w.1 a⁻¹)⁻¹ := rfl

lemma trivial_fixed (a : G) : a • trivialPattern G = trivialPattern G := by
  apply Subtype.ext
  funext _
  simp [rotate_apply, trivialPattern]

variable [Fintype G]

noncomputable instance : Fintype (Pattern G) := Fintype.ofFinite _

def patternEquiv (e : Fin 13 ≃ G) (he : e 0 = 1) : Pattern G ≃ Orbit where
  toFun w v := w.1 (e v.succ)
  invFun ρ := ⟨fun g => Fin.cases 1 ρ (e.symm g), by rw [← he]; simp⟩
  left_inv w := by
    apply Subtype.ext
    funext g
    obtain ⟨v, rfl⟩ := e.surjective g
    cases v using Fin.cases with
    | zero =>
      have hs : e.symm 1 = 0 := by rw [← he, e.symm_apply_apply]
      simp [he, hs, w.property]
    | succ v => simp
  right_inv ρ := by funext v; simp

noncomputable def identityEnumeration (hc : Fintype.card G = 13) : Fin 13 ≃ G :=
  let e := (Fintype.equivFinOfCardEq hc).symm
  e.trans (Equiv.mulRight ((e 0)⁻¹))

lemma identityEnumeration_zero (hc : Fintype.card G = 13) :
    identityEnumeration G hc 0 = 1 := by simp [identityEnumeration]

theorem pattern_card (hc : Fintype.card G = 13) : Fintype.card (Pattern G) = 6 ^ 12 := by
  rw [Fintype.card_congr (patternEquiv G (identityEnumeration G hc)
    (identityEnumeration_zero G hc)), orbit_card]

theorem fixed_pattern (hc : Fintype.card G = 13) (w : Pattern G)
    (hw : ∀ a : G, a • w = w) : w = trivialPattern G := by
  have hm (u v : G) : w.1 (u * v) = w.1 v * w.1 u := by
    have h := congrArg (fun z : Pattern G => z.1 v) (hw u⁻¹)
    simp only [rotate_apply, inv_inv] at h
    exact (mul_inv_eq_iff_eq_mul).mp h
  have hp (g : G) (n : ℕ) : w.1 (g ^ n) = w.1 g ^ n := by
    induction n with
    | zero => simp [w.property]
    | succ n ih => rw [pow_succ, hm, ih, ← pow_succ']
  apply Subtype.ext
  funext g
  have hg : g ^ 13 = 1 := by simpa [hc] using (pow_card_eq_one (x := g))
  have h6 : w.1 g ^ 6 = 1 := by
    simpa [Row, Fintype.card_perm, Nat.factorial] using (pow_card_eq_one (x := w.1 g))
  have h13 : w.1 g ^ 13 = w.1 g := by
    rw [show 13 = 6 * 2 + 1 from rfl, pow_succ, pow_mul, h6]
    simp
  have h := hp g 13
  rw [hg, w.property, h13] at h
  exact h.symm

noncomputable instance (w : Pattern G) : Fintype (MulAction.orbit G w) := Fintype.ofFinite _
noncomputable instance (w : Pattern G) : Fintype (MulAction.stabilizer G w) := Fintype.ofFinite _

theorem orbit_size (hc : Fintype.card G = 13) (w : Pattern G) :
    Fintype.card (MulAction.orbit G w) = if w = trivialPattern G then 1 else 13 := by
  classical
  by_cases hw : w = trivialPattern G
  · rw [if_pos hw, hw]
    exact (MulAction.mem_fixedPoints_iff_card_orbit_eq_one).mp (trivial_fixed G)
  · rw [if_neg hw]
    have hdiv : Fintype.card (MulAction.orbit G w) ∣ 13 :=
      ⟨Fintype.card (stabilizer G w), by
        rw [← hc, card_orbit_mul_card_stabilizer_eq_card_group]⟩
    rcases (show Nat.Prime 13 by decide).eq_one_or_self_of_dvd _ hdiv with h | h
    · exact False.elim (hw (fixed_pattern G hc w
        ((mem_fixedPoints_iff_card_orbit_eq_one).mpr h)))
    · exact h

abbrev Classes := MulAction.orbitRel.Quotient G (Pattern G)

noncomputable instance : Fintype (Classes G) := by
  classical
  infer_instance

def trivialClass : Classes G := Quotient.mk'' (trivialPattern G)

omit [Fintype G] in
lemma out_trivial_iff (q : Classes G) : q.out' = trivialPattern G ↔ q = trivialClass G := by
  constructor
  · intro h
    rw [← Quotient.out_eq' q, h]
    rfl
  · intro h
    have he : (Quotient.mk'' q.out' : Classes G) = Quotient.mk'' (trivialPattern G) :=
      (Quotient.out_eq' q).trans h
    have horb := Quotient.exact' he
    obtain ⟨a, ha⟩ := horb
    exact ha.symm.trans (trivial_fixed G a)

theorem class_card (hc : Fintype.card G = 13) : Fintype.card (Classes G) = 167444796 := by
  classical
  have h := Fintype.card_congr (selfEquivSigmaOrbits G (Pattern G))
  rw [pattern_card G hc, Fintype.card_sigma] at h
  simp_rw [orbit_size G hc, out_trivial_iff G] at h
  rw [show (6 : ℕ) ^ 12 = 2176782336 by decide] at h
  have hh : (∑ q : Classes G, if q = trivialClass G then 1 else 13) + 12 =
      13 * Fintype.card (Classes G) := by
    have hr (q : Classes G) :
        (if q = trivialClass G then 1 else 13) + (if q = trivialClass G then 12 else 0) = 13 := by
      split <;> simp_all
    have hs := congrArg (fun f : Classes G → ℕ => ∑ q, f q) (funext hr)
    simpa [Finset.sum_add_distrib, Nat.mul_comm] using hs
  rw [← h] at hh
  omega

theorem invariant_sum {F : Type*} [CommRing F] (f : Pattern G → F)
    (hf : ∀ (a : G) (w : Pattern G), f (a • w) = f w) :
    (∑ w, f w) = ∑ q : Classes G, (Fintype.card (MulAction.orbit G q.out') : F) * f q.out' := by
  classical
  let e := selfEquivSigmaOrbits G (Pattern G)
  calc
    (∑ w, f w) = ∑ s : Σ q : Classes G, MulAction.orbit G q.out', f s.2.1 := by
      apply Fintype.sum_equiv e
      intro w
      rfl
    _ = _ := by
      rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro q _
      have he (v : MulAction.orbit G q.out') : f v.1 = f q.out' := by
        obtain ⟨a, ha⟩ := v.property
        rw [← ha]
        exact hf a q.out'
      simp_rw [he]
      simp [nsmul_eq_mul]

#print axioms fixed_pattern
#print axioms orbit_size
#print axioms class_card
#print axioms invariant_sum

end HeilbronnFrobenius
