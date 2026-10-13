import TrimmedLayer

/-! Translate an exactly counted part of the sphere into a shorter range. -/

namespace HeilbronnTrimmedPacking
open HeilbronnMixedSphere HeilbronnTrimmedLayer HeilbronnInterval
open HeilbronnMixedLayer (words words_nodup)

def termCount : Nat := 850305600
def packingSize : Nat := 21725500154463

theorem interval_family : ∃ w : Fin termCount → Word alphabets,
    (∀ a b, w a = w b → a = b) ∧
    (∀ a, energy (w a) = 32 ∧ lower ≤ encode (w a) ∧ encode (w a) < upper) := by
  let l := (words alphabets).filter fun w =>
    decide (energy w = 32 ∧ lower ≤ encode w ∧ encode w < upper)
  have hlen : termCount ≤ l.length := by
    change termCount ≤ intervalCount alphabets 32 lower upper
    rw [exact_interval_count]
    exact Nat.le_refl _
  let rank : Fin termCount → Fin l.length := fun a => ⟨a.val, Nat.lt_of_lt_of_le a.isLt hlen⟩
  let w : Fin termCount → Word alphabets := fun a => l.get (rank a)
  have hnd : l.Nodup := (List.filter_sublist (words alphabets)).nodup (words_nodup alphabets)
  refine ⟨w, ?_, ?_⟩
  · intro a b h
    apply Fin.ext
    have heq : l[(rank a).val]? = l[(rank b).val]? := by
      rw [List.getElem?_eq_getElem (rank a).isLt, List.getElem?_eq_getElem (rank b).isLt]
      exact congrArg some h
    exact List.getElem?_inj (rank a).isLt hnd heq
  · intro a
    have hmem : w a ∈ l := List.get_mem l (rank a).val (rank a).isLt
    exact of_decide_eq_true (List.mem_filter.mp hmem).2

theorem translated_packing :
    ∃ u v : Fin 850305600 → Nat,
      (∀ a, u a < packingSize ∧ v a < packingSize) ∧
      (∀ a c, u a = u c → a = c) ∧
      (∀ a c, v a = v c → a = c) ∧
      (∀ a c e, u a + u c + v e = packingSize - 1 ↔ a = c ∧ c = e) := by
  obtain ⟨w, hi, hw⟩ := interval_family
  let u := fun a => encode (w a) - lower
  let v := fun a => packingSize - 1 - 2 * u a
  have hb (a : Fin termCount) : 2 * u a < packingSize := by
    have ha := hw a
    dsimp [u, lower, upper, packingSize] at *
    omega
  have hu (a c : Fin termCount) (h : u a = u c) : a = c := by
    apply hi a c
    apply encode_injective
    have ha := hw a
    have hc := hw c
    dsimp [u] at h
    omega
  have hn (a c : Fin termCount) : norm (w a) = norm (w c) := by
    rw [norm_energy, norm_energy, (hw a).1, (hw c).1]
  refine ⟨u, v, ?_, hu, ?_, ?_⟩
  · intro a
    have h := hb a
    dsimp [v]
    omega
  · intro a c h
    apply hu a c
    have ha := hb a
    have hc := hb c
    dsimp [v] at h
    omega
  · intro a c e
    have he := hb e
    constructor
    · intro h
      have ha := hw a
      have hc := hw c
      have hg := hw e
      have hm : encode (w a) + encode (w c) = 2 * encode (w e) := by
        dsimp [v, u] at h he
        omega
      obtain ⟨hac, hce⟩ := midpoint_equal (w a) (w c) (w e)
        (no_carries _ _ _ hm) (hn a e) (hn c e)
      exact ⟨hi a c hac, hi c e hce⟩
    · rintro ⟨rfl, rfl⟩
      dsimp [v]
      omega

theorem trimmed_gain :
    10249 * (498 * packingSize + 7) < 10000 * (498 * (15 ^ 7 * 19 ^ 4) + 7) := by decide

#print axioms interval_family
#print axioms translated_packing
#print axioms trimmed_gain

end HeilbronnTrimmedPacking
