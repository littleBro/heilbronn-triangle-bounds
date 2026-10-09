import MixedLayer

/-! A mixed-radix sphere packing for the five-term norm expansion. -/

namespace HeilbronnRankFivePacking
open HeilbronnMixedSphere HeilbronnMixedLayer

def traceT : Nat := 2347506125

theorem exact_layer_count : count alphabets 119 = 2365025280 := by
  exact HeilbronnMixedLayer.exact_layer_count

theorem layer_capacity : traceT ≤ 2365025280 := by decide

theorem exact_layer_family : ∃ w : Fin traceT → Word alphabets,
    (∀ a b, w a = w b → a = b) ∧ (∀ a b, norm (w a) = norm (w b)) := by
  let l := (words alphabets).filter fun w => decide (energy w = 119)
  have hlen : traceT ≤ l.length := by
    change traceT ≤ count alphabets 119
    rw [exact_layer_count]
    exact layer_capacity
  let rank : Fin traceT → Fin l.length := fun a => ⟨a.val, Nat.lt_of_lt_of_le a.isLt hlen⟩
  let w : Fin traceT → Word alphabets := fun a => l.get (rank a)
  have he (a : Fin traceT) : energy (w a) = 119 := by
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
    ∃ u v : Fin 2347506125 → Nat,
      (∀ a, u a < (39 * 35 ^ 8) ∧ v a < (39 * 35 ^ 8)) ∧
      (∀ a c, u a = u c → a = c) ∧
      (∀ a c, v a = v c → a = c) ∧
      (∀ a c e, u a + u c + v e = (39 * 35 ^ 8) - 1 ↔ a = c ∧ c = e) := by
  obtain ⟨w, hi, hn⟩ := exact_layer_family
  let u := fun a => encode (w a)
  let v := fun a => (39 * 35 ^ 8) - 1 - 2 * u a
  refine ⟨u, v, ?_, ?_, ?_, ?_⟩
  · intro a
    exact position_bounds (w a)
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

theorem trace_gain :
    234 * (498 * (39 * 35 ^ 8) + 7) < 100 * (498 * 27 ^ 10 + 7) := by decide

#print axioms exact_layer_count
#print axioms layer_capacity
#print axioms exact_layer_family
#print axioms trace_packing
#print axioms trace_gain

end HeilbronnRankFivePacking
