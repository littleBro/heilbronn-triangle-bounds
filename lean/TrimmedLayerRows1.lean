import TrimmedLayerRows0

/-! Generated recurrence proof; every finite transition is kernel-checked. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace HeilbronnTrimmedLayer
open HeilbronnInterval HeilbronnTrimmedData

theorem transition_11 : tableAdvance 33 5 11724 row8.toList row9.toList = row11.toList := by decide

theorem row_11_correct (e : Nat) (he : e < 33) :
    belowCount [5, 4, 5, 5, 5] e 11724 = row11.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 5 11724 e (belowCount [4, 5, 5, 5])
    (fun j => row8.toList.getD j 0) (fun j => row9.toList.getD j 0)
    (fun j hj => row_8_correct j (by omega))
    (fun j hj => row_9_correct j (by omega))
  rw [h, ← tableAdvance_get 33 5 11724 row8.toList row9.toList e he, transition_11]

theorem transition_12 : tableAdvance 33 4 175849 row10.toList row11.toList = row12.toList := by decide

theorem row_12_correct (e : Nat) (he : e < 33) :
    belowCount [4, 5, 4, 5, 5, 5] e 175849 = row12.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 175849 e (belowCount [5, 4, 5, 5, 5])
    (fun j => row10.toList.getD j 0) (fun j => row11.toList.getD j 0)
    (fun j hj => row_10_correct j (by omega))
    (fun j hj => row_11_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 175849 row10.toList row11.toList e he, transition_12]

theorem transition_13 : tableAdvance 33 4 175850 row10.toList row11.toList = row13.toList := by decide

theorem row_13_correct (e : Nat) (he : e < 33) :
    belowCount [4, 5, 4, 5, 5, 5] e 175850 = row13.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 175850 e (belowCount [5, 4, 5, 5, 5])
    (fun j => row10.toList.getD j 0) (fun j => row11.toList.getD j 0)
    (fun j hj => row_10_correct j (by omega))
    (fun j hj => row_11_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 175850 row10.toList row11.toList e he, transition_13]

theorem transition_14 : tableAdvance 33 4 2637738 row12.toList row13.toList = row14.toList := by decide

theorem row_14_correct (e : Nat) (he : e < 33) :
    belowCount [4, 4, 5, 4, 5, 5, 5] e 2637738 = row14.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 2637738 e (belowCount [4, 5, 4, 5, 5, 5])
    (fun j => row12.toList.getD j 0) (fun j => row13.toList.getD j 0)
    (fun j hj => row_12_correct j (by omega))
    (fun j hj => row_13_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 2637738 row12.toList row13.toList e he, transition_14]

theorem transition_15 : tableAdvance 33 4 2637739 row12.toList row13.toList = row15.toList := by decide

theorem row_15_correct (e : Nat) (he : e < 33) :
    belowCount [4, 4, 5, 4, 5, 5, 5] e 2637739 = row15.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 2637739 e (belowCount [4, 5, 4, 5, 5, 5])
    (fun j => row12.toList.getD j 0) (fun j => row13.toList.getD j 0)
    (fun j hj => row_12_correct j (by omega))
    (fun j hj => row_13_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 2637739 row12.toList row13.toList e he, transition_15]

theorem transition_16 : tableAdvance 33 4 39566072 row14.toList row15.toList = row16.toList := by decide

theorem row_16_correct (e : Nat) (he : e < 33) :
    belowCount [4, 4, 4, 5, 4, 5, 5, 5] e 39566072 = row16.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 39566072 e (belowCount [4, 4, 5, 4, 5, 5, 5])
    (fun j => row14.toList.getD j 0) (fun j => row15.toList.getD j 0)
    (fun j hj => row_14_correct j (by omega))
    (fun j hj => row_15_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 39566072 row14.toList row15.toList e he, transition_16]

theorem transition_17 : tableAdvance 33 4 39566073 row14.toList row15.toList = row17.toList := by decide

theorem row_17_correct (e : Nat) (he : e < 33) :
    belowCount [4, 4, 4, 5, 4, 5, 5, 5] e 39566073 = row17.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 39566073 e (belowCount [4, 4, 5, 4, 5, 5, 5])
    (fun j => row14.toList.getD j 0) (fun j => row15.toList.getD j 0)
    (fun j hj => row_14_correct j (by omega))
    (fun j hj => row_15_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 39566073 row14.toList row15.toList e he, transition_17]

theorem transition_18 : tableAdvance 33 4 593491080 row16.toList row17.toList = row18.toList := by decide

theorem row_18_correct (e : Nat) (he : e < 33) :
    belowCount [4, 4, 4, 4, 5, 4, 5, 5, 5] e 593491080 = row18.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 593491080 e (belowCount [4, 4, 4, 5, 4, 5, 5, 5])
    (fun j => row16.toList.getD j 0) (fun j => row17.toList.getD j 0)
    (fun j hj => row_16_correct j (by omega))
    (fun j hj => row_17_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 593491080 row16.toList row17.toList e he, transition_18]

theorem transition_19 : tableAdvance 33 4 593491081 row16.toList row17.toList = row19.toList := by decide

theorem row_19_correct (e : Nat) (he : e < 33) :
    belowCount [4, 4, 4, 4, 5, 4, 5, 5, 5] e 593491081 = row19.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 593491081 e (belowCount [4, 4, 4, 5, 4, 5, 5, 5])
    (fun j => row16.toList.getD j 0) (fun j => row17.toList.getD j 0)
    (fun j hj => row_16_correct j (by omega))
    (fun j hj => row_17_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 593491081 row16.toList row17.toList e he, transition_19]

theorem transition_20 : tableAdvance 33 4 8902366203 row18.toList row19.toList = row20.toList := by decide

theorem row_20_correct (e : Nat) (he : e < 33) :
    belowCount [4, 4, 4, 4, 4, 5, 4, 5, 5, 5] e 8902366203 = row20.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 8902366203 e (belowCount [4, 4, 4, 4, 5, 4, 5, 5, 5])
    (fun j => row18.toList.getD j 0) (fun j => row19.toList.getD j 0)
    (fun j hj => row_18_correct j (by omega))
    (fun j hj => row_19_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 8902366203 row18.toList row19.toList e he, transition_20]

theorem transition_21 : tableAdvance 33 4 8902366204 row18.toList row19.toList = row21.toList := by decide

theorem row_21_correct (e : Nat) (he : e < 33) :
    belowCount [4, 4, 4, 4, 4, 5, 4, 5, 5, 5] e 8902366204 = row21.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 8902366204 e (belowCount [4, 4, 4, 4, 5, 4, 5, 5, 5])
    (fun j => row18.toList.getD j 0) (fun j => row19.toList.getD j 0)
    (fun j hj => row_18_correct j (by omega))
    (fun j hj => row_19_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 8902366204 row18.toList row19.toList e he, transition_21]

end HeilbronnTrimmedLayer
