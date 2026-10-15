import TrimmedLayerRows1

/-! Generated recurrence proof; every finite transition is kernel-checked. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace HeilbronnTrimmedLayer
open HeilbronnInterval HeilbronnTrimmedData

theorem transition_22 : tableAdvance 33 4 133535493048 row20.toList row21.toList = row22.toList := by decide

theorem row_22_correct (e : Nat) (he : e < 33) :
    belowCount [4, 4, 4, 4, 4, 4, 5, 4, 5, 5, 5] e 133535493048 = row22.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 133535493048 e (belowCount [4, 4, 4, 4, 4, 5, 4, 5, 5, 5])
    (fun j => row20.toList.getD j 0) (fun j => row21.toList.getD j 0)
    (fun j hj => row_20_correct j (by omega))
    (fun j hj => row_21_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 133535493048 row20.toList row21.toList e he, transition_22]

theorem transition_23 : tableAdvance 33 5 9 row0.toList row1.toList = row23.toList := by decide

theorem row_23_correct (e : Nat) (he : e < 33) :
    belowCount [5] e 9 = row23.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 5 9 e (belowCount [])
    (fun j => row0.toList.getD j 0) (fun j => row1.toList.getD j 0)
    (fun j hj => row_0_correct j (by omega))
    (fun j hj => row_1_correct j (by omega))
  rw [h, ← tableAdvance_get 33 5 9 row0.toList row1.toList e he, transition_23]

theorem transition_24 : tableAdvance 33 5 10 row0.toList row1.toList = row24.toList := by decide

theorem row_24_correct (e : Nat) (he : e < 33) :
    belowCount [5] e 10 = row24.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 5 10 e (belowCount [])
    (fun j => row0.toList.getD j 0) (fun j => row1.toList.getD j 0)
    (fun j hj => row_0_correct j (by omega))
    (fun j hj => row_1_correct j (by omega))
  rw [h, ← tableAdvance_get 33 5 10 row0.toList row1.toList e he, transition_24]

theorem transition_25 : tableAdvance 33 5 178 row23.toList row24.toList = row25.toList := by decide

theorem row_25_correct (e : Nat) (he : e < 33) :
    belowCount [5, 5] e 178 = row25.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 5 178 e (belowCount [5])
    (fun j => row23.toList.getD j 0) (fun j => row24.toList.getD j 0)
    (fun j hj => row_23_correct j (by omega))
    (fun j hj => row_24_correct j (by omega))
  rw [h, ← tableAdvance_get 33 5 178 row23.toList row24.toList e he, transition_25]

theorem transition_26 : tableAdvance 33 5 179 row23.toList row24.toList = row26.toList := by decide

theorem row_26_correct (e : Nat) (he : e < 33) :
    belowCount [5, 5] e 179 = row26.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 5 179 e (belowCount [5])
    (fun j => row23.toList.getD j 0) (fun j => row24.toList.getD j 0)
    (fun j hj => row_23_correct j (by omega))
    (fun j hj => row_24_correct j (by omega))
  rw [h, ← tableAdvance_get 33 5 179 row23.toList row24.toList e he, transition_26]

theorem transition_27 : tableAdvance 33 5 3387 row25.toList row26.toList = row27.toList := by decide

theorem row_27_correct (e : Nat) (he : e < 33) :
    belowCount [5, 5, 5] e 3387 = row27.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 5 3387 e (belowCount [5, 5])
    (fun j => row25.toList.getD j 0) (fun j => row26.toList.getD j 0)
    (fun j hj => row_25_correct j (by omega))
    (fun j hj => row_26_correct j (by omega))
  rw [h, ← tableAdvance_get 33 5 3387 row25.toList row26.toList e he, transition_27]

theorem transition_28 : tableAdvance 33 5 3388 row25.toList row26.toList = row28.toList := by decide

theorem row_28_correct (e : Nat) (he : e < 33) :
    belowCount [5, 5, 5] e 3388 = row28.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 5 3388 e (belowCount [5, 5])
    (fun j => row25.toList.getD j 0) (fun j => row26.toList.getD j 0)
    (fun j hj => row_25_correct j (by omega))
    (fun j hj => row_26_correct j (by omega))
  rw [h, ← tableAdvance_get 33 5 3388 row25.toList row26.toList e he, transition_28]

theorem transition_29 : tableAdvance 33 4 50809 row27.toList row28.toList = row29.toList := by decide

theorem row_29_correct (e : Nat) (he : e < 33) :
    belowCount [4, 5, 5, 5] e 50809 = row29.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 50809 e (belowCount [5, 5, 5])
    (fun j => row27.toList.getD j 0) (fun j => row28.toList.getD j 0)
    (fun j hj => row_27_correct j (by omega))
    (fun j hj => row_28_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 50809 row27.toList row28.toList e he, transition_29]

theorem transition_30 : tableAdvance 33 4 50810 row27.toList row28.toList = row30.toList := by decide

theorem row_30_correct (e : Nat) (he : e < 33) :
    belowCount [4, 5, 5, 5] e 50810 = row30.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 50810 e (belowCount [5, 5, 5])
    (fun j => row27.toList.getD j 0) (fun j => row28.toList.getD j 0)
    (fun j hj => row_27_correct j (by omega))
    (fun j hj => row_28_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 50810 row27.toList row28.toList e he, transition_30]

theorem transition_31 : tableAdvance 33 5 965380 row29.toList row30.toList = row31.toList := by decide

theorem row_31_correct (e : Nat) (he : e < 33) :
    belowCount [5, 4, 5, 5, 5] e 965380 = row31.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 5 965380 e (belowCount [4, 5, 5, 5])
    (fun j => row29.toList.getD j 0) (fun j => row30.toList.getD j 0)
    (fun j hj => row_29_correct j (by omega))
    (fun j hj => row_30_correct j (by omega))
  rw [h, ← tableAdvance_get 33 5 965380 row29.toList row30.toList e he, transition_31]

theorem transition_32 : tableAdvance 33 5 965381 row29.toList row30.toList = row32.toList := by decide

theorem row_32_correct (e : Nat) (he : e < 33) :
    belowCount [5, 4, 5, 5, 5] e 965381 = row32.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 5 965381 e (belowCount [4, 5, 5, 5])
    (fun j => row29.toList.getD j 0) (fun j => row30.toList.getD j 0)
    (fun j hj => row_29_correct j (by omega))
    (fun j hj => row_30_correct j (by omega))
  rw [h, ← tableAdvance_get 33 5 965381 row29.toList row30.toList e he, transition_32]

end HeilbronnTrimmedLayer
