import MixedLayerCounting
import PairedLayerData

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace HeilbronnPairedLayer
open HeilbronnMixedLayer (count step step_congr count_cons words)
open HeilbronnMixedSphere

def value (m e : Nat) : Nat := (table[m]!.toList).getD e 0

theorem initial_row (e : Fin 60) : value 0 e = if e.val = 0 then 1 else 0 := by
  change row0.toList.getD e 0 = _
  rw [show row0.toList = 1 :: List.replicate 59 0 by decide]
  obtain ⟨e, he⟩ := e
  cases e with
  | zero => rfl
  | succ e =>
    have h : e < 59 := by omega
    simp only [List.getD, List.get?_eq_getElem?, List.getElem?_cons_succ, List.getElem?_replicate, h,
      if_true, Option.getD_some, Fin.val_mk, Nat.succ_ne_zero, if_false]

def nextList (A : Nat) (row : List Nat) : List Nat :=
  (List.range 60).map (fun e => step A (fun j => row.getD j 0) e)

end HeilbronnPairedLayer
