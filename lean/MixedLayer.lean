import MixedLayerRows2

namespace HeilbronnMixedLayer
open HeilbronnMixedSphere

theorem table_next (m : Fin 8) : nextList 9 (table[m.val]!.toList) = table[m.val+1]!.toList := by
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
  have h7 : m.val = 7 := by omega
  simpa only [h7] using recurrence_7

theorem nextList_get (A : Nat) (row : List Nat) (e : Nat) (he : e < 120) :
    (nextList A row).getD e 0 = step A (fun j => row.getD j 0) e := by
  simp [nextList, List.getD, List.getElem?_range, he]

theorem table_recurrence (m : Fin 8) (e : Fin 120) : value (m.val + 1) e = step 9 (value m) e := by
  unfold value
  rw [← table_next m, nextList_get _ _ _ e.isLt]

theorem table_sound (m : Nat) (hm : m ≤ 8) :
    ∀ e, e < 120 → count (List.replicate m 9) e = value m e := by
  induction m with
  | zero =>
    intro e he
    rw [initial_row ⟨e, he⟩]
    by_cases h : e = 0 <;> simp [count, words, List.filter, energy, h, eq_comm]
  | succ m ih =>
    intro e he
    rw [List.replicate_succ, count_cons, table_recurrence ⟨m, by omega⟩ ⟨e, he⟩]
    exact step_congr _ _ _ _ (fun j hj => ih (by omega) j (by omega))

def alphabets : List Nat := 10 :: List.replicate 8 9

theorem exact_layer_count : count alphabets 119 = 2365025280 := by
  rw [alphabets, count_cons]
  have h := step_congr 10 (count (List.replicate 8 9)) (value 8) 119
    (fun j hj => table_sound 8 (by decide) j (by omega))
  rw [h]
  change step 10 (fun j => row8.toList.getD j 0) 119 = 2365025280
  rw [← nextList_get 10 row8.toList 119 (by decide), recurrence_8]
  rfl

#print axioms table_recurrence
#print axioms exact_layer_count

end HeilbronnMixedLayer
