import MixedLayerCounting
import FiveLayerData

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace HeilbronnFiveLayer
open HeilbronnMixedLayer (count step step_congr count_cons words)
open HeilbronnMixedSphere

def nextList (A : Nat) (row : List Nat) : List Nat :=
  (List.range 3).map (fun e => step A (fun j => row.getD j 0) e)

theorem nextList_get (A : Nat) (row : List Nat) (e : Nat) (he : e < 3) :
    (nextList A row).getD e 0 = step A (fun j => row.getD j 0) e := by
  simp [nextList, List.getD, List.getElem?_range, he]

theorem prefix_0 (e : Nat) (he : e < 3) :
    count [] e = row0.toList.getD e 0 := by
  rw [show row0.toList = 1 :: List.replicate 2 0 by decide]
  cases e with
  | zero => rfl
  | succ e =>
    have h : e < 2 := by omega
    change 0 = (List.replicate 2 0).getD e 0
    simp only [List.getD, List.get?_eq_getElem?, List.getElem?_replicate, h,
      if_true, Option.getD_some]

theorem recurrence_0 : nextList 1 row0.toList = row1.toList := by decide

theorem prefix_1 (e : Nat) (he : e < 3) :
    count [1] e = row1.toList.getD e 0 := by
  rw [count_cons]
  have h := step_congr 1 (count []) (fun j => row0.toList.getD j 0) e
    (fun j hj => prefix_0 j (by omega))
  rw [h, ← nextList_get 1 row0.toList e he, recurrence_0]

theorem recurrence_1 : nextList 1 row1.toList = row2.toList := by decide

theorem prefix_2 (e : Nat) (he : e < 3) :
    count [1, 1] e = row2.toList.getD e 0 := by
  rw [count_cons]
  have h := step_congr 1 (count [1]) (fun j => row1.toList.getD j 0) e
    (fun j hj => prefix_1 j (by omega))
  rw [h, ← nextList_get 1 row1.toList e he, recurrence_1]

theorem recurrence_2 : nextList 1 row2.toList = row3.toList := by decide

theorem prefix_3 (e : Nat) (he : e < 3) :
    count [1, 1, 1] e = row3.toList.getD e 0 := by
  rw [count_cons]
  have h := step_congr 1 (count [1, 1]) (fun j => row2.toList.getD j 0) e
    (fun j hj => prefix_2 j (by omega))
  rw [h, ← nextList_get 1 row2.toList e he, recurrence_2]

theorem recurrence_3 : nextList 1 row3.toList = row4.toList := by decide

theorem prefix_4 (e : Nat) (he : e < 3) :
    count [1, 1, 1, 1] e = row4.toList.getD e 0 := by
  rw [count_cons]
  have h := step_congr 1 (count [1, 1, 1]) (fun j => row3.toList.getD j 0) e
    (fun j hj => prefix_3 j (by omega))
  rw [h, ← nextList_get 1 row3.toList e he, recurrence_3]

theorem recurrence_4 : nextList 1 row4.toList = row5.toList := by decide

theorem prefix_5 (e : Nat) (he : e < 3) :
    count [1, 1, 1, 1, 1] e = row5.toList.getD e 0 := by
  rw [count_cons]
  have h := step_congr 1 (count [1, 1, 1, 1]) (fun j => row4.toList.getD j 0) e
    (fun j hj => prefix_4 j (by omega))
  rw [h, ← nextList_get 1 row4.toList e he, recurrence_4]

theorem recurrence_5 : nextList 2 row5.toList = row6.toList := by decide

theorem prefix_6 (e : Nat) (he : e < 3) :
    count [2, 1, 1, 1, 1, 1] e = row6.toList.getD e 0 := by
  rw [count_cons]
  have h := step_congr 2 (count [1, 1, 1, 1, 1]) (fun j => row5.toList.getD j 0) e
    (fun j hj => prefix_5 j (by omega))
  rw [h, ← nextList_get 2 row5.toList e he, recurrence_5]

theorem recurrence_6 : nextList 2 row6.toList = row7.toList := by decide

theorem prefix_7 (e : Nat) (he : e < 3) :
    count [2, 2, 1, 1, 1, 1, 1] e = row7.toList.getD e 0 := by
  rw [count_cons]
  have h := step_congr 2 (count [2, 1, 1, 1, 1, 1]) (fun j => row6.toList.getD j 0) e
    (fun j hj => prefix_6 j (by omega))
  rw [h, ← nextList_get 2 row6.toList e he, recurrence_6]

theorem recurrence_7 : nextList 2 row7.toList = row8.toList := by decide

theorem prefix_8 (e : Nat) (he : e < 3) :
    count [2, 2, 2, 1, 1, 1, 1, 1] e = row8.toList.getD e 0 := by
  rw [count_cons]
  have h := step_congr 2 (count [2, 2, 1, 1, 1, 1, 1]) (fun j => row7.toList.getD j 0) e
    (fun j hj => prefix_7 j (by omega))
  rw [h, ← nextList_get 2 row7.toList e he, recurrence_7]

theorem recurrence_8 : nextList 2 row8.toList = row9.toList := by decide

theorem prefix_9 (e : Nat) (he : e < 3) :
    count [2, 2, 2, 2, 1, 1, 1, 1, 1] e = row9.toList.getD e 0 := by
  rw [count_cons]
  have h := step_congr 2 (count [2, 2, 2, 1, 1, 1, 1, 1]) (fun j => row8.toList.getD j 0) e
    (fun j hj => prefix_8 j (by omega))
  rw [h, ← nextList_get 2 row8.toList e he, recurrence_8]

def alphabets : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 1]

theorem exact_layer_count : count alphabets 2 = 3072 := by
  exact prefix_9 2 (by decide)

#print axioms exact_layer_count

end HeilbronnFiveLayer
