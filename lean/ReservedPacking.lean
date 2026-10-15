import ReservedLayer
import FiveScales

/-! The tags and the norm positions belong to the same midpoint-free cube.
Five low words are reserved; no translation of the norm support is needed. -/

namespace HeilbronnReservedPacking
open HeilbronnMixedSphere HeilbronnReservedLayer HeilbronnInterval
open HeilbronnMixedLayer (words words_nodup)

def packingSize : Nat := 408781

def binaryWord : (m : Nat) → Nat → Word (List.replicate m 1)
  | 0, _ => .nil
  | m+1, n => .cons ⟨n % 2, Nat.mod_lt _ (by decide)⟩ (binaryWord m (n/2))

def tagWord (s : Fin 5) : Word alphabets := binaryWord 12 s.val
def tag (s : Fin 5) : Nat := encode (tagWord s)

theorem tag_values :
    tag ⟨0,by decide⟩ = 0 ∧ tag ⟨1,by decide⟩ = 1 ∧
    tag ⟨2,by decide⟩ = 3 ∧ tag ⟨3,by decide⟩ = 4 ∧
    tag ⟨4,by decide⟩ = 9 := by decide

theorem tag_bounds (s : Fin 5) : tag s < 10 := by
  have h : ∀ s : Fin 5, tag s < 10 := by decide
  exact h s

theorem tag_injective (s t : Fin 5) (h : tag s = tag t) : s = t := by
  have hi : ∀ s t : Fin 5, tag s = tag t → s = t := by decide
  exact hi s t h

theorem tag_energy (s : Fin 5) : energy (tagWord s) = 0 := by
  have h : ∀ s : Fin 5, energy (tagWord s) = 0 := by decide
  exact h s

theorem interval_family : ∃ w : Fin 2916 → Word alphabets,
    (∀ a b, w a = w b → a = b) ∧
    (∀ a, energy (w a) = 0 ∧ 10 ≤ encode (w a) ∧ encode (w a) < 204391) := by
  let l := (words alphabets).filter fun w =>
    decide (energy w = 0 ∧ lower ≤ encode w ∧ encode w < upper)
  have hlen : 2916 ≤ l.length := by
    change 2916 ≤ intervalCount alphabets 0 lower upper
    rw [exact_interval_count]
    exact Nat.le_refl _
  let rank : Fin 2916 → Fin l.length := fun a => ⟨a.val,Nat.lt_of_lt_of_le a.isLt hlen⟩
  let w : Fin 2916 → Word alphabets := fun a => l.get (rank a)
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

theorem zero_energy_midpoint (x y z : Word alphabets)
    (hx : energy x = 0) (hy : energy y = 0) (hz : energy z = 0)
    (h : encode x + encode y = 2 * encode z) : x = y ∧ y = z := by
  exact midpoint_equal x y z (no_carries x y z h)
    (by rw [norm_energy, norm_energy, hx, hz])
    (by rw [norm_energy, norm_energy, hy, hz])

/-- Matching includes both exclusions needed when one or both top rows use tags. -/
theorem reserved_packing :
    ∃ u v : Fin 2916 → Nat,
      (∀ a, 10 ≤ u a ∧ u a < packingSize ∧ v a < packingSize) ∧
      (∀ a b, u a = u b → a = b) ∧
      (∀ a b, v a = v b → a = b) ∧
      (∀ a b c, u a + u b + v c = packingSize-1 ↔ a = b ∧ b = c) ∧
      (∀ s a b, tag s + u a + v b ≠ packingSize-1) ∧
      (∀ s t a, tag s + tag t + v a ≠ packingSize-1) := by
  obtain ⟨w, hi, hw⟩ := interval_family
  let u := fun a => encode (w a)
  let v := fun a => packingSize-1-2*u a
  have hb (a : Fin 2916) : 2*u a < packingSize := by
    have h := hw a
    dsimp [u,packingSize] at *
    omega
  have hu (a b : Fin 2916) (h : u a = u b) : a = b :=
    hi a b (encode_injective (w a) (w b) h)
  refine ⟨u,v,?_,hu,?_,?_,?_,?_⟩
  · intro a
    have ha := hw a
    have h := hb a
    dsimp [u] at h
    dsimp [v,u]
    omega
  · intro a b h
    apply hu a b
    have ha := hb a
    have hh := hb b
    dsimp [v] at h
    omega
  · intro a b c
    have hc := hb c
    constructor
    · intro h
      have hm : encode (w a)+encode (w b)=2*encode (w c) := by
        dsimp [v,u] at *
        omega
      obtain ⟨hab,hbc⟩ := zero_energy_midpoint _ _ _ (hw a).1 (hw b).1 (hw c).1 hm
      exact ⟨hi a b hab,hi b c hbc⟩
    · rintro ⟨rfl,rfl⟩
      dsimp [v]
      omega
  · intro s a b h
    have hb' := hb b
    have hm : encode (tagWord s)+encode (w a)=2*encode (w b) := by
      dsimp [v,u,tag] at *
      omega
    have he := (zero_energy_midpoint _ _ _ (tag_energy s) (hw a).1 (hw b).1 hm).1
    have ht := tag_bounds s
    have ha := (hw a).2.1
    have he' := congrArg encode he
    change tag s = encode (w a) at he'
    omega
  · intro s t a h
    have ha := hb a
    have hm : encode (tagWord s)+encode (tagWord t)=2*encode (w a) := by
      dsimp [v,u,tag] at *
      omega
    have he := (zero_energy_midpoint _ _ _ (tag_energy s) (tag_energy t) (hw a).1 hm).2
    have ht := tag_bounds t
    have ha' := (hw a).2.1
    have he' := congrArg encode he
    change tag t = encode (w a) at he'
    omega

/-- Distinct five-coordinate labels differ at a position below ten.
The existing first-difference/minor theorem can therefore use tag span ten. -/
theorem sparse_tag_distinction {α : Type} (l l' : Fin 5 → α) (hne : l ≠ l')
    (Q Q' : Nat → α)
    (hq : ∀ s, Q (tag s) = l s) (hq' : ∀ s, Q' (tag s) = l' s) :
    ∃ a, a < 10 ∧ Q a ≠ Q' a := by
  apply Classical.byContradiction
  intro hn
  apply hne
  funext s
  apply Classical.byContradiction
  intro hs
  apply hn
  refine ⟨tag s,tag_bounds s,?_⟩
  intro h
  exact hs ((hq s).symm.trans (h.trans (hq' s)))

theorem fresh_position {a j : Nat} (ha : a < 10) (hj : j ≤ a) :
    j < packingSize-1-a ∧ packingSize-1-a < packingSize :=
  HeilbronnFiveScales.fresh_position ha (by decide) hj

theorem exact_exponent : 249*packingSize+5 = 2*50893237 := by decide
theorem gain_from_five : 285*(249*packingSize+5) < 100*(249*1166895+5) := by decide

#print axioms tag_values
#print axioms tag_bounds
#print axioms tag_injective
#print axioms tag_energy
#print axioms interval_family
#print axioms zero_energy_midpoint
#print axioms reserved_packing
#print axioms sparse_tag_distinction
#print axioms fresh_position
#print axioms exact_exponent
#print axioms gain_from_five

end HeilbronnReservedPacking
