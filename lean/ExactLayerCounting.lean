import Sphere
import ExactLayerData

set_option maxRecDepth 4096

namespace HeilbronnExactLayer
open HeilbronnSphere

def digits : List (Fin 14) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13]

theorem digits_nodup : digits.Nodup := by decide

def words : (m : Nat) → List (Word 14 m)
  | 0 => [.nil]
  | m + 1 => digits.bind fun d => (words m).map (Word.cons d)

theorem words_nodup (m : Nat) : (words m).Nodup := by
  induction m with
  | zero => simp [words]
  | succ m ih =>
    apply List.pairwise_bind.mpr
    constructor
    · intro d _
      exact ih.map (Word.cons d) (fun a b h he => h (Word.cons.inj he).2)
    · apply digits_nodup.imp
      intro a b hab x hx y hy hxy
      obtain ⟨u, _, rfl⟩ := List.mem_map.mp hx
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hy
      exact hab (Word.cons.inj hxy).1

def count (m e : Nat) : Nat :=
  ((words m).filter fun w => decide (energyIndex (A := 7) w = e)).length

def step (f : Nat → Nat) (e : Nat) : Nat :=
  Nat.sum (digits.map fun d =>
    if triangular (radiusIndex 7 d) ≤ e then f (e - triangular (radiusIndex 7 d)) else 0)

theorem length_bind (l : List α) (f : α → List β) :
    (l.bind f).length = Nat.sum (l.map fun a => (f a).length) := by
  induction l <;> simp [List.bind, *, Nat.sum, Function.comp_def]

theorem filter_cons_length (l : List (Word 14 m)) (d : Fin 14) (e : Nat) :
    ((l.map (Word.cons d)).filter fun w => decide (energyIndex (A := 7) w = e)).length =
      if triangular (radiusIndex 7 d) ≤ e then
        (l.filter fun w => decide (energyIndex (A := 7) w = e - triangular (radiusIndex 7 d))).length
      else 0 := by
  rw [List.filter_map, List.length_map]
  by_cases h : triangular (radiusIndex 7 d) ≤ e
  · rw [if_pos h]
    have heq : (fun w : Word 14 m => decide (energyIndex (A := 7) (Word.cons d w) = e)) =
        (fun w => decide (energyIndex (A := 7) w = e - triangular (radiusIndex 7 d))) := by
      funext w
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      simp only [energyIndex]
      omega
    exact congrArg (fun p => (l.filter p).length) heq
  · rw [if_neg h]
    have he : (fun w : Word 14 m => decide
        (energyIndex (A := 7) (Word.cons d w) = e)) = fun _ => false := by
      funext w
      simp only [energyIndex, decide_eq_false_iff_not]
      omega
    change (l.filter (fun w => decide (energyIndex (A := 7) (Word.cons d w) = e))).length = 0
    rw [he]
    induction l <;> simp_all [List.filter]

theorem count_succ (m e : Nat) : count (m + 1) e = step (count m) e := by
  simp only [count, words, List.filter_bind, length_bind, filter_cons_length, step]

theorem step_congr (f g : Nat → Nat) (e : Nat) (h : ∀ j, j ≤ e → f j = g j) :
    step f e = step g e := by
  unfold step
  congr 2
  funext d
  split
  · rw [h _ (Nat.sub_le _ _)]
  · rfl

def value (m e : Nat) : Nat := (table[m]!.toList).getD e 0

theorem initial_row : ∀ e : Fin 87, value 0 e = if e.val = 0 then 1 else 0 := by decide

def nextList (row : List Nat) : List Nat :=
  (List.range 87).map (fun e => step (fun j => row.getD j 0) e)

end HeilbronnExactLayer
