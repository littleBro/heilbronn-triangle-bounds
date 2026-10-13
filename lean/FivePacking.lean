import FiveLayer

/-! A mixed-radix sphere packing for the paired determinant expansion. -/

namespace HeilbronnFivePacking
open HeilbronnMixedSphere HeilbronnFiveLayer
open HeilbronnMixedLayer (count words words_nodup)

def traceT : Nat := 2916

theorem exact_layer_count : count alphabets 2 = 3072 := by
  exact HeilbronnFiveLayer.exact_layer_count

theorem layer_capacity : traceT ≤ 3072 := by decide

theorem exact_layer_family : ∃ w : Fin traceT → Word alphabets,
    (∀ a b, w a = w b → a = b) ∧ (∀ a b, norm (w a) = norm (w b)) := by
  let l := (words alphabets).filter fun w => decide (energy w = 2)
  have hlen : traceT ≤ l.length := by
    change traceT ≤ count alphabets 2
    rw [exact_layer_count]
    exact layer_capacity
  let rank : Fin traceT → Fin l.length := fun a => ⟨a.val, Nat.lt_of_lt_of_le a.isLt hlen⟩
  let w : Fin traceT → Word alphabets := fun a => l.get (rank a)
  have he (a : Fin traceT) : energy (w a) = 2 := by
    have hmem : w a ∈ l := List.get_mem l (rank a).val (rank a).isLt
    exact of_decide_eq_true (List.mem_filter.mp hmem).2
  have hnd : l.Nodup := (List.filter_sublist (words alphabets)).nodup (words_nodup alphabets)
  refine ⟨w, ?_, ?_⟩
  · intro a b h
    apply Fin.ext
    have heq : l[(rank a).val]? = l[(rank b).val]? := by
      rw [List.getElem?_eq_getElem (rank a).isLt, List.getElem?_eq_getElem (rank b).isLt]
      exact congrArg some h
    exact List.getElem?_inj (rank a).isLt hnd heq
  · intro a b
    rw [norm_energy, norm_energy, he, he]

theorem trace_packing :
    ∃ u v : Fin 2916 → Nat,
      (∀ a, 2 * u a + 1 ≤ (3 ^ 5 * 7 ^ 4) ∧ v a < (3 ^ 5 * 7 ^ 4)) ∧
      (∀ a c, u a = u c → a = c) ∧
      (∀ a c, v a = v c → a = c) ∧
      (∀ a c e, u a + u c + v e = (3 ^ 5 * 7 ^ 4) - 1 ↔ a = c ∧ c = e) := by
  obtain ⟨w, hi, hn⟩ := exact_layer_family
  let u := fun a => encode (w a)
  let v := fun a => (3 ^ 5 * 7 ^ 4) - 1 - 2 * u a
  refine ⟨u, v, ?_, ?_, ?_, ?_⟩
  · intro a
    exact ⟨encode_bound (w a), (position_bounds (w a)).2⟩
  · intro a c h
    exact hi a c (encode_injective (w a) (w c) h)
  · intro a c h
    exact hi a c (right_injective (w a) (w c) h)
  · intro a c e
    have hm := sphere_matching (w a) (w c) (w e)
      (hn a e) (hn c e)
    constructor
    · intro h
      obtain ⟨hac, hce⟩ := hm.mp h
      exact ⟨hi a c hac, hi c e hce⟩
    · rintro ⟨rfl, rfl⟩
      exact hm.mpr ⟨rfl, rfl⟩

theorem tagged_packing :
    ∃ i l : Fin 2916 → Nat,
      (∀ a, 291726 ≤ i a ∧ i a ≤ 583447 ∧ l a < 583443) ∧
      (∀ a c, i a = i c → a = c) ∧
      (∀ a c, l a = l c → a = c) ∧
      (∀ a c e, i a + i c + l e = 1166894 ↔ a = c ∧ c = e) := by
  obtain ⟨u, v, hb, hu, hv, hm⟩ := trace_packing
  refine ⟨fun a => 291726 + u a, v, ?_, ?_, hv, ?_⟩
  · intro a
    have h := hb a
    change 2 * u a + 1 ≤ 583443 ∧ v a < 583443 at h
    dsimp only
    omega
  · intro a c h
    dsimp only at h
    exact hu a c (by omega)
  · intro a c e
    have h := hm a c e
    change u a + u c + v e = 583442 ↔ a = c ∧ c = e at h
    exact (show 291726 + u a + (291726 + u c) + v e = 1166894 ↔
      u a + u c + v e = 583442 by omega).trans h

theorem tag_separation {t i l : Nat} (ht : t < 5) (hi : i ≤ 583447)
    (hl : l < 583443) : t + i + l < 1166894 := by omega

theorem trace_gain :
    108 * (249 * 1166895 + 5) < 2 * (249 * (11 * 7 ^ 8) + 4) := by decide

#print axioms exact_layer_count
#print axioms layer_capacity
#print axioms exact_layer_family
#print axioms trace_packing
#print axioms tagged_packing
#print axioms tag_separation
#print axioms trace_gain

end HeilbronnFivePacking
