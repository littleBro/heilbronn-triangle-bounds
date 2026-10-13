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

theorem transition_8 : tableAdvance 33 4 619 row6.toList row7.toList = row8.toList := by decide

theorem row_8_correct (e : Nat) (he : e < 33) :
    belowCount [4, 5, 5, 5] e 619 = row8.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 619 e (belowCount [5, 5, 5])
    (fun j => row6.toList.getD j 0) (fun j => row7.toList.getD j 0)
    (fun j hj => row_6_correct j (by omega))
    (fun j hj => row_7_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 619 row6.toList row7.toList e he, transition_8]

theorem transition_9 : tableAdvance 33 4 620 row6.toList row7.toList = row9.toList := by decide

theorem row_9_correct (e : Nat) (he : e < 33) :
    belowCount [4, 5, 5, 5] e 620 = row9.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 620 e (belowCount [5, 5, 5])
    (fun j => row6.toList.getD j 0) (fun j => row7.toList.getD j 0)
    (fun j hj => row_6_correct j (by omega))
    (fun j hj => row_7_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 620 row6.toList row7.toList e he, transition_9]

theorem transition_10 : tableAdvance 33 5 11761 row8.toList row9.toList = row10.toList := by decide

theorem row_10_correct (e : Nat) (he : e < 33) :
    belowCount [5, 4, 5, 5, 5] e 11761 = row10.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 5 11761 e (belowCount [4, 5, 5, 5])
    (fun j => row8.toList.getD j 0) (fun j => row9.toList.getD j 0)
    (fun j hj => row_8_correct j (by omega))
    (fun j hj => row_9_correct j (by omega))
  rw [h, ← tableAdvance_get 33 5 11761 row8.toList row9.toList e he, transition_10]

theorem transition_11 : tableAdvance 33 5 11762 row8.toList row9.toList = row11.toList := by decide

theorem row_11_correct (e : Nat) (he : e < 33) :
    belowCount [5, 4, 5, 5, 5] e 11762 = row11.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 5 11762 e (belowCount [4, 5, 5, 5])
    (fun j => row8.toList.getD j 0) (fun j => row9.toList.getD j 0)
    (fun j hj => row_8_correct j (by omega))
    (fun j hj => row_9_correct j (by omega))
  rw [h, ← tableAdvance_get 33 5 11762 row8.toList row9.toList e he, transition_11]

theorem transition_12 : tableAdvance 33 4 176416 row10.toList row11.toList = row12.toList := by decide

theorem row_12_correct (e : Nat) (he : e < 33) :
    belowCount [4, 5, 4, 5, 5, 5] e 176416 = row12.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 176416 e (belowCount [5, 4, 5, 5, 5])
    (fun j => row10.toList.getD j 0) (fun j => row11.toList.getD j 0)
    (fun j hj => row_10_correct j (by omega))
    (fun j hj => row_11_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 176416 row10.toList row11.toList e he, transition_12]

theorem transition_13 : tableAdvance 33 4 176417 row10.toList row11.toList = row13.toList := by decide

theorem row_13_correct (e : Nat) (he : e < 33) :
    belowCount [4, 5, 4, 5, 5, 5] e 176417 = row13.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 176417 e (belowCount [5, 4, 5, 5, 5])
    (fun j => row10.toList.getD j 0) (fun j => row11.toList.getD j 0)
    (fun j hj => row_10_correct j (by omega))
    (fun j hj => row_11_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 176417 row10.toList row11.toList e he, transition_13]

theorem transition_14 : tableAdvance 33 4 2646242 row12.toList row13.toList = row14.toList := by decide

theorem row_14_correct (e : Nat) (he : e < 33) :
    belowCount [4, 4, 5, 4, 5, 5, 5] e 2646242 = row14.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 2646242 e (belowCount [4, 5, 4, 5, 5, 5])
    (fun j => row12.toList.getD j 0) (fun j => row13.toList.getD j 0)
    (fun j hj => row_12_correct j (by omega))
    (fun j hj => row_13_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 2646242 row12.toList row13.toList e he, transition_14]

theorem transition_15 : tableAdvance 33 4 2646243 row12.toList row13.toList = row15.toList := by decide

theorem row_15_correct (e : Nat) (he : e < 33) :
    belowCount [4, 4, 5, 4, 5, 5, 5] e 2646243 = row15.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 2646243 e (belowCount [4, 5, 4, 5, 5, 5])
    (fun j => row12.toList.getD j 0) (fun j => row13.toList.getD j 0)
    (fun j hj => row_12_correct j (by omega))
    (fun j hj => row_13_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 2646243 row12.toList row13.toList e he, transition_15]

theorem transition_16 : tableAdvance 33 4 39693632 row14.toList row15.toList = row16.toList := by decide

theorem row_16_correct (e : Nat) (he : e < 33) :
    belowCount [4, 4, 4, 5, 4, 5, 5, 5] e 39693632 = row16.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 39693632 e (belowCount [4, 4, 5, 4, 5, 5, 5])
    (fun j => row14.toList.getD j 0) (fun j => row15.toList.getD j 0)
    (fun j hj => row_14_correct j (by omega))
    (fun j hj => row_15_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 39693632 row14.toList row15.toList e he, transition_16]

theorem transition_17 : tableAdvance 33 4 39693633 row14.toList row15.toList = row17.toList := by decide

theorem row_17_correct (e : Nat) (he : e < 33) :
    belowCount [4, 4, 4, 5, 4, 5, 5, 5] e 39693633 = row17.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 39693633 e (belowCount [4, 4, 5, 4, 5, 5, 5])
    (fun j => row14.toList.getD j 0) (fun j => row15.toList.getD j 0)
    (fun j hj => row_14_correct j (by omega))
    (fun j hj => row_15_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 39693633 row14.toList row15.toList e he, transition_17]

theorem transition_18 : tableAdvance 33 4 595404481 row16.toList row17.toList = row18.toList := by decide

theorem row_18_correct (e : Nat) (he : e < 33) :
    belowCount [4, 4, 4, 4, 5, 4, 5, 5, 5] e 595404481 = row18.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 595404481 e (belowCount [4, 4, 4, 5, 4, 5, 5, 5])
    (fun j => row16.toList.getD j 0) (fun j => row17.toList.getD j 0)
    (fun j hj => row_16_correct j (by omega))
    (fun j hj => row_17_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 595404481 row16.toList row17.toList e he, transition_18]

theorem transition_19 : tableAdvance 33 4 595404482 row16.toList row17.toList = row19.toList := by decide

theorem row_19_correct (e : Nat) (he : e < 33) :
    belowCount [4, 4, 4, 4, 5, 4, 5, 5, 5] e 595404482 = row19.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 595404482 e (belowCount [4, 4, 4, 5, 4, 5, 5, 5])
    (fun j => row16.toList.getD j 0) (fun j => row17.toList.getD j 0)
    (fun j hj => row_16_correct j (by omega))
    (fun j hj => row_17_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 595404482 row16.toList row17.toList e he, transition_19]

theorem transition_20 : tableAdvance 33 4 8931067218 row18.toList row19.toList = row20.toList := by decide

theorem row_20_correct (e : Nat) (he : e < 33) :
    belowCount [4, 4, 4, 4, 4, 5, 4, 5, 5, 5] e 8931067218 = row20.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 8931067218 e (belowCount [4, 4, 4, 4, 5, 4, 5, 5, 5])
    (fun j => row18.toList.getD j 0) (fun j => row19.toList.getD j 0)
    (fun j hj => row_18_correct j (by omega))
    (fun j hj => row_19_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 8931067218 row18.toList row19.toList e he, transition_20]

theorem transition_21 : tableAdvance 33 4 8931067219 row18.toList row19.toList = row21.toList := by decide

theorem row_21_correct (e : Nat) (he : e < 33) :
    belowCount [4, 4, 4, 4, 4, 5, 4, 5, 5, 5] e 8931067219 = row21.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 8931067219 e (belowCount [4, 4, 4, 4, 5, 4, 5, 5, 5])
    (fun j => row18.toList.getD j 0) (fun j => row19.toList.getD j 0)
    (fun j hj => row_18_correct j (by omega))
    (fun j hj => row_19_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 8931067219 row18.toList row19.toList e he, transition_21]

theorem transition_22 : tableAdvance 33 4 133966008273 row20.toList row21.toList = row22.toList := by decide

theorem row_22_correct (e : Nat) (he : e < 33) :
    belowCount [4, 4, 4, 4, 4, 4, 5, 4, 5, 5, 5] e 133966008273 = row22.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 133966008273 e (belowCount [4, 4, 4, 4, 4, 5, 4, 5, 5, 5])
    (fun j => row20.toList.getD j 0) (fun j => row21.toList.getD j 0)
    (fun j hj => row_20_correct j (by omega))
    (fun j hj => row_21_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 133966008273 row20.toList row21.toList e he, transition_22]

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

theorem transition_29 : tableAdvance 33 4 50811 row27.toList row28.toList = row29.toList := by decide

theorem row_29_correct (e : Nat) (he : e < 33) :
    belowCount [4, 5, 5, 5] e 50811 = row29.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 50811 e (belowCount [5, 5, 5])
    (fun j => row27.toList.getD j 0) (fun j => row28.toList.getD j 0)
    (fun j hj => row_27_correct j (by omega))
    (fun j hj => row_28_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 50811 row27.toList row28.toList e he, transition_29]

theorem transition_30 : tableAdvance 33 4 50812 row27.toList row28.toList = row30.toList := by decide

theorem row_30_correct (e : Nat) (he : e < 33) :
    belowCount [4, 5, 5, 5] e 50812 = row30.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 50812 e (belowCount [5, 5, 5])
    (fun j => row27.toList.getD j 0) (fun j => row28.toList.getD j 0)
    (fun j hj => row_27_correct j (by omega))
    (fun j hj => row_28_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 50812 row27.toList row28.toList e he, transition_30]

theorem transition_31 : tableAdvance 33 5 965418 row29.toList row30.toList = row31.toList := by decide

theorem row_31_correct (e : Nat) (he : e < 33) :
    belowCount [5, 4, 5, 5, 5] e 965418 = row31.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 5 965418 e (belowCount [4, 5, 5, 5])
    (fun j => row29.toList.getD j 0) (fun j => row30.toList.getD j 0)
    (fun j hj => row_29_correct j (by omega))
    (fun j hj => row_30_correct j (by omega))
  rw [h, ← tableAdvance_get 33 5 965418 row29.toList row30.toList e he, transition_31]

theorem transition_32 : tableAdvance 33 5 965419 row29.toList row30.toList = row32.toList := by decide

theorem row_32_correct (e : Nat) (he : e < 33) :
    belowCount [5, 4, 5, 5, 5] e 965419 = row32.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 5 965419 e (belowCount [4, 5, 5, 5])
    (fun j => row29.toList.getD j 0) (fun j => row30.toList.getD j 0)
    (fun j hj => row_29_correct j (by omega))
    (fun j hj => row_30_correct j (by omega))
  rw [h, ← tableAdvance_get 33 5 965419 row29.toList row30.toList e he, transition_32]

theorem transition_33 : tableAdvance 33 4 14481274 row31.toList row32.toList = row33.toList := by decide

theorem row_33_correct (e : Nat) (he : e < 33) :
    belowCount [4, 5, 4, 5, 5, 5] e 14481274 = row33.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 14481274 e (belowCount [5, 4, 5, 5, 5])
    (fun j => row31.toList.getD j 0) (fun j => row32.toList.getD j 0)
    (fun j hj => row_31_correct j (by omega))
    (fun j hj => row_32_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 14481274 row31.toList row32.toList e he, transition_33]

theorem transition_34 : tableAdvance 33 4 14481275 row31.toList row32.toList = row34.toList := by decide

theorem row_34_correct (e : Nat) (he : e < 33) :
    belowCount [4, 5, 4, 5, 5, 5] e 14481275 = row34.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 14481275 e (belowCount [5, 4, 5, 5, 5])
    (fun j => row31.toList.getD j 0) (fun j => row32.toList.getD j 0)
    (fun j hj => row_31_correct j (by omega))
    (fun j hj => row_32_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 14481275 row31.toList row32.toList e he, transition_34]

theorem transition_35 : tableAdvance 33 4 217219116 row33.toList row34.toList = row35.toList := by decide

theorem row_35_correct (e : Nat) (he : e < 33) :
    belowCount [4, 4, 5, 4, 5, 5, 5] e 217219116 = row35.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 217219116 e (belowCount [4, 5, 4, 5, 5, 5])
    (fun j => row33.toList.getD j 0) (fun j => row34.toList.getD j 0)
    (fun j hj => row_33_correct j (by omega))
    (fun j hj => row_34_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 217219116 row33.toList row34.toList e he, transition_35]

theorem transition_36 : tableAdvance 33 4 217219117 row33.toList row34.toList = row36.toList := by decide

theorem row_36_correct (e : Nat) (he : e < 33) :
    belowCount [4, 4, 5, 4, 5, 5, 5] e 217219117 = row36.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 217219117 e (belowCount [4, 5, 4, 5, 5, 5])
    (fun j => row33.toList.getD j 0) (fun j => row34.toList.getD j 0)
    (fun j hj => row_33_correct j (by omega))
    (fun j hj => row_34_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 217219117 row33.toList row34.toList e he, transition_36]

theorem transition_37 : tableAdvance 33 4 3258286745 row35.toList row36.toList = row37.toList := by decide

theorem row_37_correct (e : Nat) (he : e < 33) :
    belowCount [4, 4, 4, 5, 4, 5, 5, 5] e 3258286745 = row37.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 3258286745 e (belowCount [4, 4, 5, 4, 5, 5, 5])
    (fun j => row35.toList.getD j 0) (fun j => row36.toList.getD j 0)
    (fun j hj => row_35_correct j (by omega))
    (fun j hj => row_36_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 3258286745 row35.toList row36.toList e he, transition_37]

theorem transition_38 : tableAdvance 33 4 3258286746 row35.toList row36.toList = row38.toList := by decide

theorem row_38_correct (e : Nat) (he : e < 33) :
    belowCount [4, 4, 4, 5, 4, 5, 5, 5] e 3258286746 = row38.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 3258286746 e (belowCount [4, 4, 5, 4, 5, 5, 5])
    (fun j => row35.toList.getD j 0) (fun j => row36.toList.getD j 0)
    (fun j hj => row_35_correct j (by omega))
    (fun j hj => row_36_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 3258286746 row35.toList row36.toList e he, transition_38]

theorem transition_39 : tableAdvance 33 4 48874301177 row37.toList row38.toList = row39.toList := by decide

theorem row_39_correct (e : Nat) (he : e < 33) :
    belowCount [4, 4, 4, 4, 5, 4, 5, 5, 5] e 48874301177 = row39.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 48874301177 e (belowCount [4, 4, 4, 5, 4, 5, 5, 5])
    (fun j => row37.toList.getD j 0) (fun j => row38.toList.getD j 0)
    (fun j hj => row_37_correct j (by omega))
    (fun j hj => row_38_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 48874301177 row37.toList row38.toList e he, transition_39]

theorem transition_40 : tableAdvance 33 4 48874301178 row37.toList row38.toList = row40.toList := by decide

theorem row_40_correct (e : Nat) (he : e < 33) :
    belowCount [4, 4, 4, 4, 5, 4, 5, 5, 5] e 48874301178 = row40.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 48874301178 e (belowCount [4, 4, 4, 5, 4, 5, 5, 5])
    (fun j => row37.toList.getD j 0) (fun j => row38.toList.getD j 0)
    (fun j hj => row_37_correct j (by omega))
    (fun j hj => row_38_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 48874301178 row37.toList row38.toList e he, transition_40]

theorem transition_41 : tableAdvance 33 4 733114517660 row39.toList row40.toList = row41.toList := by decide

theorem row_41_correct (e : Nat) (he : e < 33) :
    belowCount [4, 4, 4, 4, 4, 5, 4, 5, 5, 5] e 733114517660 = row41.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 733114517660 e (belowCount [4, 4, 4, 4, 5, 4, 5, 5, 5])
    (fun j => row39.toList.getD j 0) (fun j => row40.toList.getD j 0)
    (fun j hj => row_39_correct j (by omega))
    (fun j hj => row_40_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 733114517660 row39.toList row40.toList e he, transition_41]

theorem transition_42 : tableAdvance 33 4 733114517661 row39.toList row40.toList = row42.toList := by decide

theorem row_42_correct (e : Nat) (he : e < 33) :
    belowCount [4, 4, 4, 4, 4, 5, 4, 5, 5, 5] e 733114517661 = row42.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 733114517661 e (belowCount [4, 4, 4, 4, 5, 4, 5, 5, 5])
    (fun j => row39.toList.getD j 0) (fun j => row40.toList.getD j 0)
    (fun j hj => row_39_correct j (by omega))
    (fun j hj => row_40_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 733114517661 row39.toList row40.toList e he, transition_42]

theorem transition_43 : tableAdvance 33 4 10996717764905 row41.toList row42.toList = row43.toList := by decide

theorem row_43_correct (e : Nat) (he : e < 33) :
    belowCount [4, 4, 4, 4, 4, 4, 5, 4, 5, 5, 5] e 10996717764905 = row43.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 4 10996717764905 e (belowCount [4, 4, 4, 4, 4, 5, 4, 5, 5, 5])
    (fun j => row41.toList.getD j 0) (fun j => row42.toList.getD j 0)
    (fun j hj => row_41_correct j (by omega))
    (fun j hj => row_42_correct j (by omega))
  rw [h, ← tableAdvance_get 33 4 10996717764905 row41.toList row42.toList e he, transition_43]

def alphabets : List Nat := [4, 4, 4, 4, 4, 4, 5, 4, 5, 5, 5]
def lower : Nat := 133966008273
def upper : Nat := 10996717764905

theorem below_lower : belowCount alphabets 32 lower = 10596664 :=
  row_22_correct 32 (by decide)

theorem below_upper : belowCount alphabets 32 upper = 860902264 :=
  row_43_correct 32 (by decide)

theorem exact_interval_count : intervalCount alphabets 32 lower upper = 850305600 := by
  have h := interval_partition alphabets 32 lower upper (by decide)
  rw [below_lower, below_upper] at h
  omega

#print axioms below_lower
#print axioms below_upper
#print axioms exact_interval_count

end HeilbronnTrimmedLayer
