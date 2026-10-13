import MixedLayerCounting
import EighteenLayerData

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace HeilbronnEighteenLayer
open HeilbronnMixedLayer (count step step_congr count_cons words)
open HeilbronnMixedSphere

def nextList (A : Nat) (row : List Nat) : List Nat :=
  (List.range 33).map (fun e => step A (fun j => row.getD j 0) e)

theorem nextList_get (A : Nat) (row : List Nat) (e : Nat) (he : e < 33) :
    (nextList A row).getD e 0 = step A (fun j => row.getD j 0) e := by
  simp [nextList, List.getD, List.getElem?_range, he]

theorem prefix_0 (e : Nat) (he : e < 33) :
    count [] e = row0.toList.getD e 0 := by
  rw [show row0.toList = 1 :: List.replicate 32 0 by decide]
  cases e with
  | zero => rfl
  | succ e =>
    have h : e < 32 := by omega
    change 0 = (List.replicate 32 0).getD e 0
    simp only [List.getD, List.get?_eq_getElem?, List.getElem?_replicate, h,
      if_true, Option.getD_some]

theorem recurrence_0 : nextList 4 row0.toList = row1.toList := by decide

theorem prefix_1 (e : Nat) (he : e < 33) :
    count [4] e = row1.toList.getD e 0 := by
  rw [count_cons]
  have h := step_congr 4 (count []) (fun j => row0.toList.getD j 0) e
    (fun j hj => prefix_0 j (by omega))
  rw [h, ← nextList_get 4 row0.toList e he, recurrence_0]

theorem recurrence_1 : nextList 4 row1.toList = row2.toList := by decide

theorem prefix_2 (e : Nat) (he : e < 33) :
    count [4, 4] e = row2.toList.getD e 0 := by
  rw [count_cons]
  have h := step_congr 4 (count [4]) (fun j => row1.toList.getD j 0) e
    (fun j hj => prefix_1 j (by omega))
  rw [h, ← nextList_get 4 row1.toList e he, recurrence_1]

theorem recurrence_2 : nextList 4 row2.toList = row3.toList := by decide

theorem prefix_3 (e : Nat) (he : e < 33) :
    count [4, 4, 4] e = row3.toList.getD e 0 := by
  rw [count_cons]
  have h := step_congr 4 (count [4, 4]) (fun j => row2.toList.getD j 0) e
    (fun j hj => prefix_2 j (by omega))
  rw [h, ← nextList_get 4 row2.toList e he, recurrence_2]

theorem recurrence_3 : nextList 4 row3.toList = row4.toList := by decide

theorem prefix_4 (e : Nat) (he : e < 33) :
    count [4, 4, 4, 4] e = row4.toList.getD e 0 := by
  rw [count_cons]
  have h := step_congr 4 (count [4, 4, 4]) (fun j => row3.toList.getD j 0) e
    (fun j hj => prefix_3 j (by omega))
  rw [h, ← nextList_get 4 row3.toList e he, recurrence_3]

theorem recurrence_4 : nextList 4 row4.toList = row5.toList := by decide

theorem prefix_5 (e : Nat) (he : e < 33) :
    count [4, 4, 4, 4, 4] e = row5.toList.getD e 0 := by
  rw [count_cons]
  have h := step_congr 4 (count [4, 4, 4, 4]) (fun j => row4.toList.getD j 0) e
    (fun j hj => prefix_4 j (by omega))
  rw [h, ← nextList_get 4 row4.toList e he, recurrence_4]

theorem recurrence_5 : nextList 4 row5.toList = row6.toList := by decide

theorem prefix_6 (e : Nat) (he : e < 33) :
    count [4, 4, 4, 4, 4, 4] e = row6.toList.getD e 0 := by
  rw [count_cons]
  have h := step_congr 4 (count [4, 4, 4, 4, 4]) (fun j => row5.toList.getD j 0) e
    (fun j hj => prefix_5 j (by omega))
  rw [h, ← nextList_get 4 row5.toList e he, recurrence_5]

theorem recurrence_6 : nextList 4 row6.toList = row7.toList := by decide

theorem prefix_7 (e : Nat) (he : e < 33) :
    count [4, 4, 4, 4, 4, 4, 4] e = row7.toList.getD e 0 := by
  rw [count_cons]
  have h := step_congr 4 (count [4, 4, 4, 4, 4, 4]) (fun j => row6.toList.getD j 0) e
    (fun j hj => prefix_6 j (by omega))
  rw [h, ← nextList_get 4 row6.toList e he, recurrence_6]

theorem recurrence_7 : nextList 5 row7.toList = row8.toList := by decide

theorem prefix_8 (e : Nat) (he : e < 33) :
    count [5, 4, 4, 4, 4, 4, 4, 4] e = row8.toList.getD e 0 := by
  rw [count_cons]
  have h := step_congr 5 (count [4, 4, 4, 4, 4, 4, 4]) (fun j => row7.toList.getD j 0) e
    (fun j hj => prefix_7 j (by omega))
  rw [h, ← nextList_get 5 row7.toList e he, recurrence_7]

theorem recurrence_8 : nextList 5 row8.toList = row9.toList := by decide

theorem prefix_9 (e : Nat) (he : e < 33) :
    count [5, 5, 4, 4, 4, 4, 4, 4, 4] e = row9.toList.getD e 0 := by
  rw [count_cons]
  have h := step_congr 5 (count [5, 4, 4, 4, 4, 4, 4, 4]) (fun j => row8.toList.getD j 0) e
    (fun j hj => prefix_8 j (by omega))
  rw [h, ← nextList_get 5 row8.toList e he, recurrence_8]

theorem recurrence_9 : nextList 5 row9.toList = row10.toList := by decide

theorem prefix_10 (e : Nat) (he : e < 33) :
    count [5, 5, 5, 4, 4, 4, 4, 4, 4, 4] e = row10.toList.getD e 0 := by
  rw [count_cons]
  have h := step_congr 5 (count [5, 5, 4, 4, 4, 4, 4, 4, 4]) (fun j => row9.toList.getD j 0) e
    (fun j hj => prefix_9 j (by omega))
  rw [h, ← nextList_get 5 row9.toList e he, recurrence_9]

theorem recurrence_10 : nextList 5 row10.toList = row11.toList := by decide

theorem prefix_11 (e : Nat) (he : e < 33) :
    count [5, 5, 5, 5, 4, 4, 4, 4, 4, 4, 4] e = row11.toList.getD e 0 := by
  rw [count_cons]
  have h := step_congr 5 (count [5, 5, 5, 4, 4, 4, 4, 4, 4, 4]) (fun j => row10.toList.getD j 0) e
    (fun j hj => prefix_10 j (by omega))
  rw [h, ← nextList_get 5 row10.toList e he, recurrence_10]

def alphabets : List Nat := [5, 5, 5, 5, 4, 4, 4, 4, 4, 4, 4]

theorem exact_layer_count : count alphabets 32 = 872130560 := by
  exact prefix_11 32 (by decide)

#print axioms exact_layer_count

end HeilbronnEighteenLayer
