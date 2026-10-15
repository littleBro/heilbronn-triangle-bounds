import IntervalCounting
import ReservedLayerData

/-! Generated exact prefix-count recurrence, checked by the Lean kernel. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace HeilbronnReservedLayer
open HeilbronnInterval HeilbronnReservedData

theorem row_0_correct (e : Nat) (_he : e < 1) :
    belowCount [] e 0 = row0.toList.getD e 0 := by
  rw [show row0.toList = List.replicate 1 0 by decide, zero_row, below_nil]
  simp

theorem row_1_correct (e : Nat) (_he : e < 1) :
    belowCount [] e 1 = row1.toList.getD e 0 := by
  rw [show row1.toList = 1 :: List.replicate 0 0 by decide, unit_row, below_nil]
  simp

theorem transition_2 : tableAdvance 1 1 0 row0.toList row1.toList = row2.toList := by decide

theorem row_2_correct (e : Nat) (he : e < 1) :
    belowCount [1] e 0 = row2.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 1 0 e (belowCount [])
    (fun j => row0.toList.getD j 0) (fun j => row1.toList.getD j 0)
    (fun j hj => row_0_correct j (by omega))
    (fun j hj => row_1_correct j (by omega))
  rw [h, ← tableAdvance_get 1 1 0 row0.toList row1.toList e he, transition_2]

theorem transition_3 : tableAdvance 1 1 1 row0.toList row1.toList = row3.toList := by decide

theorem row_3_correct (e : Nat) (he : e < 1) :
    belowCount [1] e 1 = row3.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 1 1 e (belowCount [])
    (fun j => row0.toList.getD j 0) (fun j => row1.toList.getD j 0)
    (fun j hj => row_0_correct j (by omega))
    (fun j hj => row_1_correct j (by omega))
  rw [h, ← tableAdvance_get 1 1 1 row0.toList row1.toList e he, transition_3]

theorem transition_4 : tableAdvance 1 1 0 row2.toList row3.toList = row4.toList := by decide

theorem row_4_correct (e : Nat) (he : e < 1) :
    belowCount [1, 1] e 0 = row4.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 1 0 e (belowCount [1])
    (fun j => row2.toList.getD j 0) (fun j => row3.toList.getD j 0)
    (fun j hj => row_2_correct j (by omega))
    (fun j hj => row_3_correct j (by omega))
  rw [h, ← tableAdvance_get 1 1 0 row2.toList row3.toList e he, transition_4]

theorem transition_5 : tableAdvance 1 1 1 row2.toList row3.toList = row5.toList := by decide

theorem row_5_correct (e : Nat) (he : e < 1) :
    belowCount [1, 1] e 1 = row5.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 1 1 e (belowCount [1])
    (fun j => row2.toList.getD j 0) (fun j => row3.toList.getD j 0)
    (fun j hj => row_2_correct j (by omega))
    (fun j hj => row_3_correct j (by omega))
  rw [h, ← tableAdvance_get 1 1 1 row2.toList row3.toList e he, transition_5]

theorem transition_6 : tableAdvance 1 1 0 row4.toList row5.toList = row6.toList := by decide

theorem row_6_correct (e : Nat) (he : e < 1) :
    belowCount [1, 1, 1] e 0 = row6.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 1 0 e (belowCount [1, 1])
    (fun j => row4.toList.getD j 0) (fun j => row5.toList.getD j 0)
    (fun j hj => row_4_correct j (by omega))
    (fun j hj => row_5_correct j (by omega))
  rw [h, ← tableAdvance_get 1 1 0 row4.toList row5.toList e he, transition_6]

theorem transition_7 : tableAdvance 1 1 1 row4.toList row5.toList = row7.toList := by decide

theorem row_7_correct (e : Nat) (he : e < 1) :
    belowCount [1, 1, 1] e 1 = row7.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 1 1 e (belowCount [1, 1])
    (fun j => row4.toList.getD j 0) (fun j => row5.toList.getD j 0)
    (fun j hj => row_4_correct j (by omega))
    (fun j hj => row_5_correct j (by omega))
  rw [h, ← tableAdvance_get 1 1 1 row4.toList row5.toList e he, transition_7]

theorem transition_8 : tableAdvance 1 1 0 row6.toList row7.toList = row8.toList := by decide

theorem row_8_correct (e : Nat) (he : e < 1) :
    belowCount [1, 1, 1, 1] e 0 = row8.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 1 0 e (belowCount [1, 1, 1])
    (fun j => row6.toList.getD j 0) (fun j => row7.toList.getD j 0)
    (fun j hj => row_6_correct j (by omega))
    (fun j hj => row_7_correct j (by omega))
  rw [h, ← tableAdvance_get 1 1 0 row6.toList row7.toList e he, transition_8]

theorem transition_9 : tableAdvance 1 1 1 row6.toList row7.toList = row9.toList := by decide

theorem row_9_correct (e : Nat) (he : e < 1) :
    belowCount [1, 1, 1, 1] e 1 = row9.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 1 1 e (belowCount [1, 1, 1])
    (fun j => row6.toList.getD j 0) (fun j => row7.toList.getD j 0)
    (fun j hj => row_6_correct j (by omega))
    (fun j hj => row_7_correct j (by omega))
  rw [h, ← tableAdvance_get 1 1 1 row6.toList row7.toList e he, transition_9]

theorem transition_10 : tableAdvance 1 1 0 row8.toList row9.toList = row10.toList := by decide

theorem row_10_correct (e : Nat) (he : e < 1) :
    belowCount [1, 1, 1, 1, 1] e 0 = row10.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 1 0 e (belowCount [1, 1, 1, 1])
    (fun j => row8.toList.getD j 0) (fun j => row9.toList.getD j 0)
    (fun j hj => row_8_correct j (by omega))
    (fun j hj => row_9_correct j (by omega))
  rw [h, ← tableAdvance_get 1 1 0 row8.toList row9.toList e he, transition_10]

theorem transition_11 : tableAdvance 1 1 1 row8.toList row9.toList = row11.toList := by decide

theorem row_11_correct (e : Nat) (he : e < 1) :
    belowCount [1, 1, 1, 1, 1] e 1 = row11.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 1 1 e (belowCount [1, 1, 1, 1])
    (fun j => row8.toList.getD j 0) (fun j => row9.toList.getD j 0)
    (fun j hj => row_8_correct j (by omega))
    (fun j hj => row_9_correct j (by omega))
  rw [h, ← tableAdvance_get 1 1 1 row8.toList row9.toList e he, transition_11]

theorem transition_12 : tableAdvance 1 1 0 row10.toList row11.toList = row12.toList := by decide

theorem row_12_correct (e : Nat) (he : e < 1) :
    belowCount [1, 1, 1, 1, 1, 1] e 0 = row12.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 1 0 e (belowCount [1, 1, 1, 1, 1])
    (fun j => row10.toList.getD j 0) (fun j => row11.toList.getD j 0)
    (fun j hj => row_10_correct j (by omega))
    (fun j hj => row_11_correct j (by omega))
  rw [h, ← tableAdvance_get 1 1 0 row10.toList row11.toList e he, transition_12]

theorem transition_13 : tableAdvance 1 1 1 row10.toList row11.toList = row13.toList := by decide

theorem row_13_correct (e : Nat) (he : e < 1) :
    belowCount [1, 1, 1, 1, 1, 1] e 1 = row13.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 1 1 e (belowCount [1, 1, 1, 1, 1])
    (fun j => row10.toList.getD j 0) (fun j => row11.toList.getD j 0)
    (fun j hj => row_10_correct j (by omega))
    (fun j hj => row_11_correct j (by omega))
  rw [h, ← tableAdvance_get 1 1 1 row10.toList row11.toList e he, transition_13]

theorem transition_14 : tableAdvance 1 1 0 row12.toList row13.toList = row14.toList := by decide

theorem row_14_correct (e : Nat) (he : e < 1) :
    belowCount [1, 1, 1, 1, 1, 1, 1] e 0 = row14.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 1 0 e (belowCount [1, 1, 1, 1, 1, 1])
    (fun j => row12.toList.getD j 0) (fun j => row13.toList.getD j 0)
    (fun j hj => row_12_correct j (by omega))
    (fun j hj => row_13_correct j (by omega))
  rw [h, ← tableAdvance_get 1 1 0 row12.toList row13.toList e he, transition_14]

theorem transition_15 : tableAdvance 1 1 1 row12.toList row13.toList = row15.toList := by decide

theorem row_15_correct (e : Nat) (he : e < 1) :
    belowCount [1, 1, 1, 1, 1, 1, 1] e 1 = row15.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 1 1 e (belowCount [1, 1, 1, 1, 1, 1])
    (fun j => row12.toList.getD j 0) (fun j => row13.toList.getD j 0)
    (fun j hj => row_12_correct j (by omega))
    (fun j hj => row_13_correct j (by omega))
  rw [h, ← tableAdvance_get 1 1 1 row12.toList row13.toList e he, transition_15]

theorem transition_16 : tableAdvance 1 1 0 row14.toList row15.toList = row16.toList := by decide

theorem row_16_correct (e : Nat) (he : e < 1) :
    belowCount [1, 1, 1, 1, 1, 1, 1, 1] e 0 = row16.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 1 0 e (belowCount [1, 1, 1, 1, 1, 1, 1])
    (fun j => row14.toList.getD j 0) (fun j => row15.toList.getD j 0)
    (fun j hj => row_14_correct j (by omega))
    (fun j hj => row_15_correct j (by omega))
  rw [h, ← tableAdvance_get 1 1 0 row14.toList row15.toList e he, transition_16]

theorem transition_17 : tableAdvance 1 1 1 row14.toList row15.toList = row17.toList := by decide

theorem row_17_correct (e : Nat) (he : e < 1) :
    belowCount [1, 1, 1, 1, 1, 1, 1, 1] e 1 = row17.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 1 1 e (belowCount [1, 1, 1, 1, 1, 1, 1])
    (fun j => row14.toList.getD j 0) (fun j => row15.toList.getD j 0)
    (fun j hj => row_14_correct j (by omega))
    (fun j hj => row_15_correct j (by omega))
  rw [h, ← tableAdvance_get 1 1 1 row14.toList row15.toList e he, transition_17]

theorem transition_18 : tableAdvance 1 1 0 row16.toList row17.toList = row18.toList := by decide

theorem row_18_correct (e : Nat) (he : e < 1) :
    belowCount [1, 1, 1, 1, 1, 1, 1, 1, 1] e 0 = row18.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 1 0 e (belowCount [1, 1, 1, 1, 1, 1, 1, 1])
    (fun j => row16.toList.getD j 0) (fun j => row17.toList.getD j 0)
    (fun j hj => row_16_correct j (by omega))
    (fun j hj => row_17_correct j (by omega))
  rw [h, ← tableAdvance_get 1 1 0 row16.toList row17.toList e he, transition_18]

theorem transition_19 : tableAdvance 1 1 1 row16.toList row17.toList = row19.toList := by decide

theorem row_19_correct (e : Nat) (he : e < 1) :
    belowCount [1, 1, 1, 1, 1, 1, 1, 1, 1] e 1 = row19.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 1 1 e (belowCount [1, 1, 1, 1, 1, 1, 1, 1])
    (fun j => row16.toList.getD j 0) (fun j => row17.toList.getD j 0)
    (fun j hj => row_16_correct j (by omega))
    (fun j hj => row_17_correct j (by omega))
  rw [h, ← tableAdvance_get 1 1 1 row16.toList row17.toList e he, transition_19]

theorem transition_20 : tableAdvance 1 1 1 row18.toList row19.toList = row20.toList := by decide

theorem row_20_correct (e : Nat) (he : e < 1) :
    belowCount [1, 1, 1, 1, 1, 1, 1, 1, 1, 1] e 1 = row20.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 1 1 e (belowCount [1, 1, 1, 1, 1, 1, 1, 1, 1])
    (fun j => row18.toList.getD j 0) (fun j => row19.toList.getD j 0)
    (fun j hj => row_18_correct j (by omega))
    (fun j hj => row_19_correct j (by omega))
  rw [h, ← tableAdvance_get 1 1 1 row18.toList row19.toList e he, transition_20]

theorem transition_21 : tableAdvance 1 1 2 row18.toList row19.toList = row21.toList := by decide

theorem row_21_correct (e : Nat) (he : e < 1) :
    belowCount [1, 1, 1, 1, 1, 1, 1, 1, 1, 1] e 2 = row21.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 1 2 e (belowCount [1, 1, 1, 1, 1, 1, 1, 1, 1])
    (fun j => row18.toList.getD j 0) (fun j => row19.toList.getD j 0)
    (fun j hj => row_18_correct j (by omega))
    (fun j hj => row_19_correct j (by omega))
  rw [h, ← tableAdvance_get 1 1 2 row18.toList row19.toList e he, transition_21]

theorem transition_22 : tableAdvance 1 1 3 row20.toList row21.toList = row22.toList := by decide

theorem row_22_correct (e : Nat) (he : e < 1) :
    belowCount [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] e 3 = row22.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 1 3 e (belowCount [1, 1, 1, 1, 1, 1, 1, 1, 1, 1])
    (fun j => row20.toList.getD j 0) (fun j => row21.toList.getD j 0)
    (fun j hj => row_20_correct j (by omega))
    (fun j hj => row_21_correct j (by omega))
  rw [h, ← tableAdvance_get 1 1 3 row20.toList row21.toList e he, transition_22]

theorem transition_23 : tableAdvance 1 1 4 row20.toList row21.toList = row23.toList := by decide

theorem row_23_correct (e : Nat) (he : e < 1) :
    belowCount [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] e 4 = row23.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 1 4 e (belowCount [1, 1, 1, 1, 1, 1, 1, 1, 1, 1])
    (fun j => row20.toList.getD j 0) (fun j => row21.toList.getD j 0)
    (fun j hj => row_20_correct j (by omega))
    (fun j hj => row_21_correct j (by omega))
  rw [h, ← tableAdvance_get 1 1 4 row20.toList row21.toList e he, transition_23]

theorem transition_24 : tableAdvance 1 1 10 row22.toList row23.toList = row24.toList := by decide

theorem row_24_correct (e : Nat) (he : e < 1) :
    belowCount [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] e 10 = row24.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 1 10 e (belowCount [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])
    (fun j => row22.toList.getD j 0) (fun j => row23.toList.getD j 0)
    (fun j hj => row_22_correct j (by omega))
    (fun j hj => row_23_correct j (by omega))
  rw [h, ← tableAdvance_get 1 1 10 row22.toList row23.toList e he, transition_24]

theorem transition_25 : tableAdvance 1 1 2 row0.toList row1.toList = row25.toList := by decide

theorem row_25_correct (e : Nat) (he : e < 1) :
    belowCount [1] e 2 = row25.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 1 2 e (belowCount [])
    (fun j => row0.toList.getD j 0) (fun j => row1.toList.getD j 0)
    (fun j hj => row_0_correct j (by omega))
    (fun j hj => row_1_correct j (by omega))
  rw [h, ← tableAdvance_get 1 1 2 row0.toList row1.toList e he, transition_25]

theorem transition_26 : tableAdvance 1 1 3 row3.toList row25.toList = row26.toList := by decide

theorem row_26_correct (e : Nat) (he : e < 1) :
    belowCount [1, 1] e 3 = row26.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 1 3 e (belowCount [1])
    (fun j => row3.toList.getD j 0) (fun j => row25.toList.getD j 0)
    (fun j hj => row_3_correct j (by omega))
    (fun j hj => row_25_correct j (by omega))
  rw [h, ← tableAdvance_get 1 1 3 row3.toList row25.toList e he, transition_26]

theorem transition_27 : tableAdvance 1 1 4 row3.toList row25.toList = row27.toList := by decide

theorem row_27_correct (e : Nat) (he : e < 1) :
    belowCount [1, 1] e 4 = row27.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 1 4 e (belowCount [1])
    (fun j => row3.toList.getD j 0) (fun j => row25.toList.getD j 0)
    (fun j hj => row_3_correct j (by omega))
    (fun j hj => row_25_correct j (by omega))
  rw [h, ← tableAdvance_get 1 1 4 row3.toList row25.toList e he, transition_27]

theorem transition_28 : tableAdvance 1 1 10 row26.toList row27.toList = row28.toList := by decide

theorem row_28_correct (e : Nat) (he : e < 1) :
    belowCount [1, 1, 1] e 10 = row28.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 1 10 e (belowCount [1, 1])
    (fun j => row26.toList.getD j 0) (fun j => row27.toList.getD j 0)
    (fun j hj => row_26_correct j (by omega))
    (fun j hj => row_27_correct j (by omega))
  rw [h, ← tableAdvance_get 1 1 10 row26.toList row27.toList e he, transition_28]

theorem transition_29 : tableAdvance 1 1 11 row26.toList row27.toList = row29.toList := by decide

theorem row_29_correct (e : Nat) (he : e < 1) :
    belowCount [1, 1, 1] e 11 = row29.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 1 11 e (belowCount [1, 1])
    (fun j => row26.toList.getD j 0) (fun j => row27.toList.getD j 0)
    (fun j hj => row_26_correct j (by omega))
    (fun j hj => row_27_correct j (by omega))
  rw [h, ← tableAdvance_get 1 1 11 row26.toList row27.toList e he, transition_29]

theorem transition_30 : tableAdvance 1 1 31 row28.toList row29.toList = row30.toList := by decide

theorem row_30_correct (e : Nat) (he : e < 1) :
    belowCount [1, 1, 1, 1] e 31 = row30.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 1 31 e (belowCount [1, 1, 1])
    (fun j => row28.toList.getD j 0) (fun j => row29.toList.getD j 0)
    (fun j hj => row_28_correct j (by omega))
    (fun j hj => row_29_correct j (by omega))
  rw [h, ← tableAdvance_get 1 1 31 row28.toList row29.toList e he, transition_30]

theorem transition_31 : tableAdvance 1 1 32 row28.toList row29.toList = row31.toList := by decide

theorem row_31_correct (e : Nat) (he : e < 1) :
    belowCount [1, 1, 1, 1] e 32 = row31.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 1 32 e (belowCount [1, 1, 1])
    (fun j => row28.toList.getD j 0) (fun j => row29.toList.getD j 0)
    (fun j hj => row_28_correct j (by omega))
    (fun j hj => row_29_correct j (by omega))
  rw [h, ← tableAdvance_get 1 1 32 row28.toList row29.toList e he, transition_31]

theorem transition_32 : tableAdvance 1 1 93 row30.toList row31.toList = row32.toList := by decide

theorem row_32_correct (e : Nat) (he : e < 1) :
    belowCount [1, 1, 1, 1, 1] e 93 = row32.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 1 93 e (belowCount [1, 1, 1, 1])
    (fun j => row30.toList.getD j 0) (fun j => row31.toList.getD j 0)
    (fun j hj => row_30_correct j (by omega))
    (fun j hj => row_31_correct j (by omega))
  rw [h, ← tableAdvance_get 1 1 93 row30.toList row31.toList e he, transition_32]

theorem transition_33 : tableAdvance 1 1 94 row30.toList row31.toList = row33.toList := by decide

theorem row_33_correct (e : Nat) (he : e < 1) :
    belowCount [1, 1, 1, 1, 1] e 94 = row33.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 1 94 e (belowCount [1, 1, 1, 1])
    (fun j => row30.toList.getD j 0) (fun j => row31.toList.getD j 0)
    (fun j hj => row_30_correct j (by omega))
    (fun j hj => row_31_correct j (by omega))
  rw [h, ← tableAdvance_get 1 1 94 row30.toList row31.toList e he, transition_33]

theorem transition_34 : tableAdvance 1 1 280 row32.toList row33.toList = row34.toList := by decide

theorem row_34_correct (e : Nat) (he : e < 1) :
    belowCount [1, 1, 1, 1, 1, 1] e 280 = row34.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 1 280 e (belowCount [1, 1, 1, 1, 1])
    (fun j => row32.toList.getD j 0) (fun j => row33.toList.getD j 0)
    (fun j hj => row_32_correct j (by omega))
    (fun j hj => row_33_correct j (by omega))
  rw [h, ← tableAdvance_get 1 1 280 row32.toList row33.toList e he, transition_34]

theorem transition_35 : tableAdvance 1 1 281 row32.toList row33.toList = row35.toList := by decide

theorem row_35_correct (e : Nat) (he : e < 1) :
    belowCount [1, 1, 1, 1, 1, 1] e 281 = row35.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 1 281 e (belowCount [1, 1, 1, 1, 1])
    (fun j => row32.toList.getD j 0) (fun j => row33.toList.getD j 0)
    (fun j hj => row_32_correct j (by omega))
    (fun j hj => row_33_correct j (by omega))
  rw [h, ← tableAdvance_get 1 1 281 row32.toList row33.toList e he, transition_35]

theorem transition_36 : tableAdvance 1 1 841 row34.toList row35.toList = row36.toList := by decide

theorem row_36_correct (e : Nat) (he : e < 1) :
    belowCount [1, 1, 1, 1, 1, 1, 1] e 841 = row36.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 1 841 e (belowCount [1, 1, 1, 1, 1, 1])
    (fun j => row34.toList.getD j 0) (fun j => row35.toList.getD j 0)
    (fun j hj => row_34_correct j (by omega))
    (fun j hj => row_35_correct j (by omega))
  rw [h, ← tableAdvance_get 1 1 841 row34.toList row35.toList e he, transition_36]

theorem transition_37 : tableAdvance 1 1 842 row34.toList row35.toList = row37.toList := by decide

theorem row_37_correct (e : Nat) (he : e < 1) :
    belowCount [1, 1, 1, 1, 1, 1, 1] e 842 = row37.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 1 842 e (belowCount [1, 1, 1, 1, 1, 1])
    (fun j => row34.toList.getD j 0) (fun j => row35.toList.getD j 0)
    (fun j hj => row_34_correct j (by omega))
    (fun j hj => row_35_correct j (by omega))
  rw [h, ← tableAdvance_get 1 1 842 row34.toList row35.toList e he, transition_37]

theorem transition_38 : tableAdvance 1 1 2523 row36.toList row37.toList = row38.toList := by decide

theorem row_38_correct (e : Nat) (he : e < 1) :
    belowCount [1, 1, 1, 1, 1, 1, 1, 1] e 2523 = row38.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 1 2523 e (belowCount [1, 1, 1, 1, 1, 1, 1])
    (fun j => row36.toList.getD j 0) (fun j => row37.toList.getD j 0)
    (fun j hj => row_36_correct j (by omega))
    (fun j hj => row_37_correct j (by omega))
  rw [h, ← tableAdvance_get 1 1 2523 row36.toList row37.toList e he, transition_38]

theorem transition_39 : tableAdvance 1 1 2524 row36.toList row37.toList = row39.toList := by decide

theorem row_39_correct (e : Nat) (he : e < 1) :
    belowCount [1, 1, 1, 1, 1, 1, 1, 1] e 2524 = row39.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 1 2524 e (belowCount [1, 1, 1, 1, 1, 1, 1])
    (fun j => row36.toList.getD j 0) (fun j => row37.toList.getD j 0)
    (fun j hj => row_36_correct j (by omega))
    (fun j hj => row_37_correct j (by omega))
  rw [h, ← tableAdvance_get 1 1 2524 row36.toList row37.toList e he, transition_39]

theorem transition_40 : tableAdvance 1 1 7570 row38.toList row39.toList = row40.toList := by decide

theorem row_40_correct (e : Nat) (he : e < 1) :
    belowCount [1, 1, 1, 1, 1, 1, 1, 1, 1] e 7570 = row40.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 1 7570 e (belowCount [1, 1, 1, 1, 1, 1, 1, 1])
    (fun j => row38.toList.getD j 0) (fun j => row39.toList.getD j 0)
    (fun j hj => row_38_correct j (by omega))
    (fun j hj => row_39_correct j (by omega))
  rw [h, ← tableAdvance_get 1 1 7570 row38.toList row39.toList e he, transition_40]

theorem transition_41 : tableAdvance 1 1 7571 row38.toList row39.toList = row41.toList := by decide

theorem row_41_correct (e : Nat) (he : e < 1) :
    belowCount [1, 1, 1, 1, 1, 1, 1, 1, 1] e 7571 = row41.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 1 7571 e (belowCount [1, 1, 1, 1, 1, 1, 1, 1])
    (fun j => row38.toList.getD j 0) (fun j => row39.toList.getD j 0)
    (fun j hj => row_38_correct j (by omega))
    (fun j hj => row_39_correct j (by omega))
  rw [h, ← tableAdvance_get 1 1 7571 row38.toList row39.toList e he, transition_41]

theorem transition_42 : tableAdvance 1 1 22710 row40.toList row41.toList = row42.toList := by decide

theorem row_42_correct (e : Nat) (he : e < 1) :
    belowCount [1, 1, 1, 1, 1, 1, 1, 1, 1, 1] e 22710 = row42.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 1 22710 e (belowCount [1, 1, 1, 1, 1, 1, 1, 1, 1])
    (fun j => row40.toList.getD j 0) (fun j => row41.toList.getD j 0)
    (fun j hj => row_40_correct j (by omega))
    (fun j hj => row_41_correct j (by omega))
  rw [h, ← tableAdvance_get 1 1 22710 row40.toList row41.toList e he, transition_42]

theorem transition_43 : tableAdvance 1 1 22711 row40.toList row41.toList = row43.toList := by decide

theorem row_43_correct (e : Nat) (he : e < 1) :
    belowCount [1, 1, 1, 1, 1, 1, 1, 1, 1, 1] e 22711 = row43.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 1 22711 e (belowCount [1, 1, 1, 1, 1, 1, 1, 1, 1])
    (fun j => row40.toList.getD j 0) (fun j => row41.toList.getD j 0)
    (fun j hj => row_40_correct j (by omega))
    (fun j hj => row_41_correct j (by omega))
  rw [h, ← tableAdvance_get 1 1 22711 row40.toList row41.toList e he, transition_43]

theorem transition_44 : tableAdvance 1 1 68130 row42.toList row43.toList = row44.toList := by decide

theorem row_44_correct (e : Nat) (he : e < 1) :
    belowCount [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] e 68130 = row44.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 1 68130 e (belowCount [1, 1, 1, 1, 1, 1, 1, 1, 1, 1])
    (fun j => row42.toList.getD j 0) (fun j => row43.toList.getD j 0)
    (fun j hj => row_42_correct j (by omega))
    (fun j hj => row_43_correct j (by omega))
  rw [h, ← tableAdvance_get 1 1 68130 row42.toList row43.toList e he, transition_44]

theorem transition_45 : tableAdvance 1 1 68131 row42.toList row43.toList = row45.toList := by decide

theorem row_45_correct (e : Nat) (he : e < 1) :
    belowCount [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] e 68131 = row45.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 1 68131 e (belowCount [1, 1, 1, 1, 1, 1, 1, 1, 1, 1])
    (fun j => row42.toList.getD j 0) (fun j => row43.toList.getD j 0)
    (fun j hj => row_42_correct j (by omega))
    (fun j hj => row_43_correct j (by omega))
  rw [h, ← tableAdvance_get 1 1 68131 row42.toList row43.toList e he, transition_45]

theorem transition_46 : tableAdvance 1 1 204391 row44.toList row45.toList = row46.toList := by decide

theorem row_46_correct (e : Nat) (he : e < 1) :
    belowCount [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] e 204391 = row46.toList.getD e 0 := by
  rw [below_cons]
  have h := step_from_tables 1 204391 e (belowCount [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1])
    (fun j => row44.toList.getD j 0) (fun j => row45.toList.getD j 0)
    (fun j hj => row_44_correct j (by omega))
    (fun j hj => row_45_correct j (by omega))
  rw [h, ← tableAdvance_get 1 1 204391 row44.toList row45.toList e he, transition_46]

def alphabets : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
def lower : Nat := 10
def upper : Nat := 204391

theorem below_lower : belowCount alphabets 0 lower = 5 :=
  row_24_correct 0 (by decide)

theorem below_upper : belowCount alphabets 0 upper = 2921 :=
  row_46_correct 0 (by decide)

theorem exact_interval_count : intervalCount alphabets 0 lower upper = 2916 := by
  have h := interval_partition alphabets 0 lower upper (by decide)
  rw [below_lower, below_upper] at h
  omega

#print axioms below_lower
#print axioms below_upper
#print axioms exact_interval_count

end HeilbronnReservedLayer
