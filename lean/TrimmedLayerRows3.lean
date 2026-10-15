import TrimmedLayerRows2

/-! Generated recurrence proof; every finite transition is kernel-checked. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace HeilbronnTrimmedLayer
open HeilbronnInterval HeilbronnTrimmedData

theorem transition_33 : tableAdvance 33 4 14480705 row31.toList row32.toList = row33.toList := by decide

theorem row_33_correct (e : Nat) (he : e < 33) :
    belowCount [4, 5, 4, 5, 5, 5] e 14480705 = row33.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 14480705 e (belowCount [5, 4, 5, 5, 5])
    (fun j => row31.toList.getD j 0) (fun j => row32.toList.getD j 0)
    (fun j hj => row_31_correct j (by omega))
    (fun j hj => row_32_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 14480705 row31.toList row32.toList e he, transition_33]

theorem transition_34 : tableAdvance 33 4 14480706 row31.toList row32.toList = row34.toList := by decide

theorem row_34_correct (e : Nat) (he : e < 33) :
    belowCount [4, 5, 4, 5, 5, 5] e 14480706 = row34.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 14480706 e (belowCount [5, 4, 5, 5, 5])
    (fun j => row31.toList.getD j 0) (fun j => row32.toList.getD j 0)
    (fun j hj => row_31_correct j (by omega))
    (fun j hj => row_32_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 14480706 row31.toList row32.toList e he, transition_34]

theorem transition_35 : tableAdvance 33 4 217210579 row33.toList row34.toList = row35.toList := by decide

theorem row_35_correct (e : Nat) (he : e < 33) :
    belowCount [4, 4, 5, 4, 5, 5, 5] e 217210579 = row35.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 217210579 e (belowCount [4, 5, 4, 5, 5, 5])
    (fun j => row33.toList.getD j 0) (fun j => row34.toList.getD j 0)
    (fun j hj => row_33_correct j (by omega))
    (fun j hj => row_34_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 217210579 row33.toList row34.toList e he, transition_35]

theorem transition_36 : tableAdvance 33 4 217210580 row33.toList row34.toList = row36.toList := by decide

theorem row_36_correct (e : Nat) (he : e < 33) :
    belowCount [4, 4, 5, 4, 5, 5, 5] e 217210580 = row36.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 217210580 e (belowCount [4, 5, 4, 5, 5, 5])
    (fun j => row33.toList.getD j 0) (fun j => row34.toList.getD j 0)
    (fun j hj => row_33_correct j (by omega))
    (fun j hj => row_34_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 217210580 row33.toList row34.toList e he, transition_36]

theorem transition_37 : tableAdvance 33 4 3258158687 row35.toList row36.toList = row37.toList := by decide

theorem row_37_correct (e : Nat) (he : e < 33) :
    belowCount [4, 4, 4, 5, 4, 5, 5, 5] e 3258158687 = row37.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 3258158687 e (belowCount [4, 4, 5, 4, 5, 5, 5])
    (fun j => row35.toList.getD j 0) (fun j => row36.toList.getD j 0)
    (fun j hj => row_35_correct j (by omega))
    (fun j hj => row_36_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 3258158687 row35.toList row36.toList e he, transition_37]

theorem transition_38 : tableAdvance 33 4 3258158688 row35.toList row36.toList = row38.toList := by decide

theorem row_38_correct (e : Nat) (he : e < 33) :
    belowCount [4, 4, 4, 5, 4, 5, 5, 5] e 3258158688 = row38.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 3258158688 e (belowCount [4, 4, 5, 4, 5, 5, 5])
    (fun j => row35.toList.getD j 0) (fun j => row36.toList.getD j 0)
    (fun j hj => row_35_correct j (by omega))
    (fun j hj => row_36_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 3258158688 row35.toList row36.toList e he, transition_38]

theorem transition_39 : tableAdvance 33 4 48872380312 row37.toList row38.toList = row39.toList := by decide

theorem row_39_correct (e : Nat) (he : e < 33) :
    belowCount [4, 4, 4, 4, 5, 4, 5, 5, 5] e 48872380312 = row39.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 48872380312 e (belowCount [4, 4, 4, 5, 4, 5, 5, 5])
    (fun j => row37.toList.getD j 0) (fun j => row38.toList.getD j 0)
    (fun j hj => row_37_correct j (by omega))
    (fun j hj => row_38_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 48872380312 row37.toList row38.toList e he, transition_39]

theorem transition_40 : tableAdvance 33 4 48872380313 row37.toList row38.toList = row40.toList := by decide

theorem row_40_correct (e : Nat) (he : e < 33) :
    belowCount [4, 4, 4, 4, 5, 4, 5, 5, 5] e 48872380313 = row40.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 48872380313 e (belowCount [4, 4, 4, 5, 4, 5, 5, 5])
    (fun j => row37.toList.getD j 0) (fun j => row38.toList.getD j 0)
    (fun j hj => row_37_correct j (by omega))
    (fun j hj => row_38_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 48872380313 row37.toList row38.toList e he, transition_40]

theorem transition_41 : tableAdvance 33 4 733085704685 row39.toList row40.toList = row41.toList := by decide

theorem row_41_correct (e : Nat) (he : e < 33) :
    belowCount [4, 4, 4, 4, 4, 5, 4, 5, 5, 5] e 733085704685 = row41.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 733085704685 e (belowCount [4, 4, 4, 4, 5, 4, 5, 5, 5])
    (fun j => row39.toList.getD j 0) (fun j => row40.toList.getD j 0)
    (fun j hj => row_39_correct j (by omega))
    (fun j hj => row_40_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 733085704685 row39.toList row40.toList e he, transition_41]

theorem transition_42 : tableAdvance 33 4 733085704686 row39.toList row40.toList = row42.toList := by decide

theorem row_42_correct (e : Nat) (he : e < 33) :
    belowCount [4, 4, 4, 4, 4, 5, 4, 5, 5, 5] e 733085704686 = row42.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 733085704686 e (belowCount [4, 4, 4, 4, 5, 4, 5, 5, 5])
    (fun j => row39.toList.getD j 0) (fun j => row40.toList.getD j 0)
    (fun j hj => row_39_correct j (by omega))
    (fun j hj => row_40_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 733085704686 row39.toList row40.toList e he, transition_42]

theorem transition_43 : tableAdvance 33 4 10996285570280 row41.toList row42.toList = row43.toList := by decide

theorem row_43_correct (e : Nat) (he : e < 33) :
    belowCount [4, 4, 4, 4, 4, 4, 5, 4, 5, 5, 5] e 10996285570280 = row43.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 10996285570280 e (belowCount [4, 4, 4, 4, 4, 5, 4, 5, 5, 5])
    (fun j => row41.toList.getD j 0) (fun j => row42.toList.getD j 0)
    (fun j hj => row_41_correct j (by omega))
    (fun j hj => row_42_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 10996285570280 row41.toList row42.toList e he, transition_43]

end HeilbronnTrimmedLayer
