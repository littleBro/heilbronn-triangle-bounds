import ExactLayerRows0
import ExactLayerRows1
import ExactLayerRows2
import ExactLayerRows3

set_option maxRecDepth 4096

namespace HeilbronnExactLayer
open HeilbronnSphere

theorem table_next (m : Fin 11) :
    nextList (table[m.val]!.toList) = table[m.val+1]!.toList := by
  by_cases h0 : m.val = 0
  · simpa only [h0] using recurrence_0
  by_cases h1 : m.val = 1
  · simpa only [h1] using recurrence_1
  by_cases h2 : m.val = 2
  · simpa only [h2] using recurrence_2
  by_cases h3 : m.val = 3
  · simpa only [h3] using recurrence_3
  by_cases h4 : m.val = 4
  · simpa only [h4] using recurrence_4
  by_cases h5 : m.val = 5
  · simpa only [h5] using recurrence_5
  by_cases h6 : m.val = 6
  · simpa only [h6] using recurrence_6
  by_cases h7 : m.val = 7
  · simpa only [h7] using recurrence_7
  by_cases h8 : m.val = 8
  · simpa only [h8] using recurrence_8
  by_cases h9 : m.val = 9
  · simpa only [h9] using recurrence_9
  have h10 : m.val = 10 := by omega
  simpa only [h10] using recurrence_10

theorem nextList_get (row : List Nat) (e : Nat) (he : e < 87) :
    (nextList row).getD e 0 = step (fun j => row.getD j 0) e := by
  simp [nextList, List.getD, List.getElem?_range, he]

theorem table_recurrence (m : Fin 11) (e : Fin 87) :
    value (m.val + 1) e = step (value m) e := by
  unfold value
  rw [← table_next m, nextList_get _ _ e.isLt]

theorem table_sound (m : Nat) (hm : m ≤ 11) : ∀ e, e < 87 → count m e = value m e := by
  induction m with
  | zero =>
    intro e he
    rw [initial_row ⟨e, he⟩]
    by_cases h : e = 0 <;> simp [count, words, List.filter, energyIndex, h, eq_comm]
  | succ m ih =>
    intro e he
    rw [count_succ, table_recurrence ⟨m, by omega⟩ ⟨e, he⟩]
    exact step_congr _ _ _ (fun j hj => ih (by omega) j (by omega))

theorem exact_layer_count : count 11 86 = 67169169408 := by
  rw [table_sound 11 (by decide) 86 (by decide)]
  rfl

#print axioms table_recurrence
#print axioms exact_layer_count

def bilinearT : Nat := 25 * 6 ^ 12

theorem layer_capacity : bilinearT ≤ 67169169408 := by decide

theorem exact_layer_family : ∃ w : Fin bilinearT → Word 14 11,
    (∀ a b, w a = w b → a = b) ∧ (∀ a b, norm (w a) = norm (w b)) := by
  let l := (words 11).filter fun w => decide (energyIndex (A := 7) w = 86)
  have hlen : bilinearT ≤ l.length := by
    change bilinearT ≤ count 11 86
    rw [exact_layer_count]
    exact layer_capacity
  let rank : Fin bilinearT → Fin l.length := fun a => ⟨a.val, Nat.lt_of_lt_of_le a.isLt hlen⟩
  let w : Fin bilinearT → Word 14 11 := fun a => l.get (rank a)
  have he (a : Fin bilinearT) : energyIndex (A := 7) (w a) = 86 := by
    have hmem : w a ∈ l := List.get_mem l (rank a).val (rank a).isLt
    exact of_decide_eq_true (List.mem_filter.mp hmem).2
  have hnd : l.Nodup := (List.filter_sublist (words 11)).nodup (words_nodup 11)
  refine ⟨w, ?_, ?_⟩
  · intro a b h
    apply Fin.ext
    have heq : l[(rank a).val]? = l[(rank b).val]? := by
      rw [List.getElem?_eq_getElem (rank a).isLt, List.getElem?_eq_getElem (rank b).isLt]
      exact congrArg some h
    exact List.getElem?_inj (rank a).isLt hnd heq
  · intro a b
    rw [norm_energy (by decide : 0 < 7), norm_energy (by decide : 0 < 7), he, he]

theorem bilinear_packing :
    ∃ u v : Fin (25 * 6 ^ 12) → Nat,
      (∀ a, u a < 27 ^ 11 ∧ v a < 27 ^ 11) ∧
      (∀ a c, u a = u c → a = c) ∧
      (∀ a c, v a = v c → a = c) ∧
      (∀ a c e, u a + u c + v e = 27 ^ 11 - 1 ↔ a = c ∧ c = e) := by
  obtain ⟨w, hi, hn⟩ := exact_layer_family
  let u := fun a => encode 27 (w a)
  let v := fun a => 27 ^ 11 - 1 - 2 * u a
  refine ⟨u, v, ?_, ?_, ?_, ?_⟩
  · intro a
    exact position_bounds (w a) (by decide) (by decide)
  · intro a c h
    exact hi a c (encode_injective (w a) (w c) (by decide) (by decide) h)
  · intro a c h
    exact hi a c (right_injective (w a) (w c) (by decide) (by decide) h)
  · intro a c e
    have hm := sphere_matching (b := 27) (w a) (w c) (w e) (by decide) (by decide) (hn a e) (hn c e)
    constructor
    · intro h
      obtain ⟨hac, hce⟩ := hm.mp h
      exact ⟨hi a c hac, hi c e hce⟩
    · rintro ⟨rfl, rfl⟩
      exact hm.mpr ⟨rfl, rfl⟩

theorem bilinear_gain :
    946 * (498 * 27 ^ 11 + 7) < 100 * (498 * 47 ^ 10 + 7) ∧
    100 * (498 * 47 ^ 10 + 7) < 947 * (498 * 27 ^ 11 + 7) := by decide

#print axioms layer_capacity
#print axioms exact_layer_family
#print axioms bilinear_packing
#print axioms bilinear_gain

end HeilbronnExactLayer
