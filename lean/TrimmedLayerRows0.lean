import IntervalCounting
import TrimmedLayerData

/-! Generated recurrence proof; every finite transition is kernel-checked. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace HeilbronnTrimmedLayer
open HeilbronnInterval HeilbronnTrimmedData

theorem row_0_correct (e : Nat) (_he : e < 33) :
    belowCount [] e 0 = row0.toList.getD e 0 := by
  rw [show row0.toList = List.replicate 33 0 by decide, zero_row, below_nil]
  simp

theorem row_1_correct (e : Nat) (_he : e < 33) :
    belowCount [] e 1 = row1.toList.getD e 0 := by
  rw [show row1.toList = 1 :: List.replicate 32 0 by decide, unit_row, below_nil]
  simp

theorem transition_2 : tableAdvance 33 5 0 row0.toList row1.toList = row2.toList := by decide

theorem row_2_correct (e : Nat) (he : e < 33) :
    belowCount [5] e 0 = row2.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 5 0 e (belowCount [])
    (fun j => row0.toList.getD j 0) (fun j => row1.toList.getD j 0)
    (fun j hj => row_0_correct j (by omega))
    (fun j hj => row_1_correct j (by omega))
  rw [h, ← tableAdvance_get 33 5 0 row0.toList row1.toList e he, transition_2]

theorem transition_3 : tableAdvance 33 5 1 row0.toList row1.toList = row3.toList := by decide

theorem row_3_correct (e : Nat) (he : e < 33) :
    belowCount [5] e 1 = row3.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 5 1 e (belowCount [])
    (fun j => row0.toList.getD j 0) (fun j => row1.toList.getD j 0)
    (fun j hj => row_0_correct j (by omega))
    (fun j hj => row_1_correct j (by omega))
  rw [h, ← tableAdvance_get 33 5 1 row0.toList row1.toList e he, transition_3]

theorem transition_4 : tableAdvance 33 5 2 row2.toList row3.toList = row4.toList := by decide

theorem row_4_correct (e : Nat) (he : e < 33) :
    belowCount [5, 5] e 2 = row4.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 5 2 e (belowCount [5])
    (fun j => row2.toList.getD j 0) (fun j => row3.toList.getD j 0)
    (fun j hj => row_2_correct j (by omega))
    (fun j hj => row_3_correct j (by omega))
  rw [h, ← tableAdvance_get 33 5 2 row2.toList row3.toList e he, transition_4]

theorem transition_5 : tableAdvance 33 5 3 row2.toList row3.toList = row5.toList := by decide

theorem row_5_correct (e : Nat) (he : e < 33) :
    belowCount [5, 5] e 3 = row5.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 5 3 e (belowCount [5])
    (fun j => row2.toList.getD j 0) (fun j => row3.toList.getD j 0)
    (fun j hj => row_2_correct j (by omega))
    (fun j hj => row_3_correct j (by omega))
  rw [h, ← tableAdvance_get 33 5 3 row2.toList row3.toList e he, transition_5]

theorem transition_6 : tableAdvance 33 5 41 row4.toList row5.toList = row6.toList := by decide

theorem row_6_correct (e : Nat) (he : e < 33) :
    belowCount [5, 5, 5] e 41 = row6.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 5 41 e (belowCount [5, 5])
    (fun j => row4.toList.getD j 0) (fun j => row5.toList.getD j 0)
    (fun j hj => row_4_correct j (by omega))
    (fun j hj => row_5_correct j (by omega))
  rw [h, ← tableAdvance_get 33 5 41 row4.toList row5.toList e he, transition_6]

theorem transition_7 : tableAdvance 33 5 42 row4.toList row5.toList = row7.toList := by decide

theorem row_7_correct (e : Nat) (he : e < 33) :
    belowCount [5, 5, 5] e 42 = row7.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 5 42 e (belowCount [5, 5])
    (fun j => row4.toList.getD j 0) (fun j => row5.toList.getD j 0)
    (fun j hj => row_4_correct j (by omega))
    (fun j hj => row_5_correct j (by omega))
  rw [h, ← tableAdvance_get 33 5 42 row4.toList row5.toList e he, transition_7]

theorem transition_8 : tableAdvance 33 4 617 row6.toList row7.toList = row8.toList := by decide

theorem row_8_correct (e : Nat) (he : e < 33) :
    belowCount [4, 5, 5, 5] e 617 = row8.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 617 e (belowCount [5, 5, 5])
    (fun j => row6.toList.getD j 0) (fun j => row7.toList.getD j 0)
    (fun j hj => row_6_correct j (by omega))
    (fun j hj => row_7_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 617 row6.toList row7.toList e he, transition_8]

theorem transition_9 : tableAdvance 33 4 618 row6.toList row7.toList = row9.toList := by decide

theorem row_9_correct (e : Nat) (he : e < 33) :
    belowCount [4, 5, 5, 5] e 618 = row9.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 618 e (belowCount [5, 5, 5])
    (fun j => row6.toList.getD j 0) (fun j => row7.toList.getD j 0)
    (fun j hj => row_6_correct j (by omega))
    (fun j hj => row_7_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 618 row6.toList row7.toList e he, transition_9]

theorem transition_10 : tableAdvance 33 5 11723 row8.toList row9.toList = row10.toList := by decide

theorem row_10_correct (e : Nat) (he : e < 33) :
    belowCount [5, 4, 5, 5, 5] e 11723 = row10.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 5 11723 e (belowCount [4, 5, 5, 5])
    (fun j => row8.toList.getD j 0) (fun j => row9.toList.getD j 0)
    (fun j hj => row_8_correct j (by omega))
    (fun j hj => row_9_correct j (by omega))
  rw [h, ← tableAdvance_get 33 5 11723 row8.toList row9.toList e he, transition_10]

end HeilbronnTrimmedLayer
