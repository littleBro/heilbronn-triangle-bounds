import ExactLayer

/-! A ten-digit packing for the orbit-averaged norm decomposition. The existing
    checked recurrence table already contains the required energy coefficient. -/

namespace HeilbronnFrobeniusPacking
open HeilbronnSphere HeilbronnExactLayer

def traceT : Nat := 4186119900

theorem exact_layer_count : count 10 80 = 5058395136 := by
  rw [table_sound 10 (by decide) 80 (by decide)]
  rfl

theorem layer_capacity : traceT ≤ 5058395136 := by decide

theorem exact_layer_family : ∃ w : Fin traceT → Word 14 10,
    (∀ a b, w a = w b → a = b) ∧ (∀ a b, norm (w a) = norm (w b)) := by
  let l := (words 10).filter fun w => decide (energyIndex (A := 7) w = 80)
  have hlen : traceT ≤ l.length := by
    change traceT ≤ count 10 80
    rw [exact_layer_count]
    exact layer_capacity
  let rank : Fin traceT → Fin l.length := fun a => ⟨a.val, Nat.lt_of_lt_of_le a.isLt hlen⟩
  let w : Fin traceT → Word 14 10 := fun a => l.get (rank a)
  have he (a : Fin traceT) : energyIndex (A := 7) (w a) = 80 := by
    have hmem : w a ∈ l := List.get_mem l (rank a).val (rank a).isLt
    exact of_decide_eq_true (List.mem_filter.mp hmem).2
  have hnd : l.Nodup := (List.filter_sublist (words 10)).nodup (words_nodup 10)
  refine ⟨w, ?_, ?_⟩
  · intro a b h
    apply Fin.ext
    have heq : l[(rank a).val]? = l[(rank b).val]? := by
      rw [List.getElem?_eq_getElem (rank a).isLt, List.getElem?_eq_getElem (rank b).isLt]
      exact congrArg some h
    exact List.getElem?_inj (rank a).isLt hnd heq
  · intro a b
    rw [norm_energy (by decide : 0 < 7), norm_energy (by decide : 0 < 7), he, he]

theorem trace_packing :
    ∃ u v : Fin 4186119900 → Nat,
      (∀ a, u a < 27 ^ 10 ∧ v a < 27 ^ 10) ∧
      (∀ a c, u a = u c → a = c) ∧
      (∀ a c, v a = v c → a = c) ∧
      (∀ a c e, u a + u c + v e = 27 ^ 10 - 1 ↔ a = c ∧ c = e) := by
  obtain ⟨w, hi, hn⟩ := exact_layer_family
  let u := fun a => encode 27 (w a)
  let v := fun a => 27 ^ 10 - 1 - 2 * u a
  refine ⟨u, v, ?_, ?_, ?_, ?_⟩
  · intro a
    exact position_bounds (w a) (by decide) (by decide)
  · intro a c h
    exact hi a c (encode_injective (w a) (w c) (by decide) (by decide) h)
  · intro a c h
    exact hi a c (right_injective (w a) (w c) (by decide) (by decide) h)
  · intro a c e
    have hm := sphere_matching (b := 27) (w a) (w c) (w e) (by decide) (by decide)
      (hn a e) (hn c e)
    constructor
    · intro h
      obtain ⟨hac, hce⟩ := hm.mp h
      exact ⟨hi a c hac, hi c e hce⟩
    · rintro ⟨rfl, rfl⟩
      exact hm.mpr ⟨rfl, rfl⟩

theorem trace_gain :
    2699 * (498 * 27 ^ 10 + 7) < 100 * (498 * 27 ^ 11 + 7) ∧
    498 * 27 ^ 11 + 7 < 27 * (498 * 27 ^ 10 + 7) := by decide

#print axioms exact_layer_count
#print axioms layer_capacity
#print axioms exact_layer_family
#print axioms trace_packing
#print axioms trace_gain

end HeilbronnFrobeniusPacking
