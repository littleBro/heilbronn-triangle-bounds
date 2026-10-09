import MixedSphere
import MixedLayerData

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace HeilbronnMixedLayer
open HeilbronnMixedSphere
open HeilbronnSphere (triangular radiusIndex)

def finDigits : (n : Nat) → List (Fin n)
  | 0 => []
  | n + 1 => ⟨0, by omega⟩ :: (finDigits n).map Fin.succ

theorem finDigits_nodup (n : Nat) : (finDigits n).Nodup := by
  induction n with
  | zero => simp [finDigits]
  | succ n ih =>
    rw [finDigits, List.nodup_cons]
    constructor
    · intro h
      obtain ⟨a, _, ha⟩ := List.mem_map.mp h
      have hv := congrArg Fin.val ha
      simp at hv
    · exact ih.map Fin.succ (fun a b h he => h (Fin.ext (by
        have hv := congrArg Fin.val he
        simpa only [Fin.val_succ, Nat.add_right_cancel_iff] using hv)))

def digits (A : Nat) : List (Fin (2 * A)) := finDigits (2 * A)

theorem digits_nodup (A : Nat) : (digits A).Nodup := by
  unfold digits
  exact finDigits_nodup _

def words : (as : List Nat) → List (Word as)
  | [] => [.nil]
  | A :: as => (digits A).bind fun d => (words as).map (Word.cons d)

theorem words_nodup (as : List Nat) : (words as).Nodup := by
  induction as with
  | nil => simp [words]
  | cons A as ih =>
    apply List.pairwise_bind.mpr
    constructor
    · intro d _
      exact ih.map (Word.cons d) (fun a b h he => h (Word.cons.inj he).2)
    · apply (digits_nodup A).imp
      intro a b hab x hx y hy hxy
      obtain ⟨u, _, rfl⟩ := List.mem_map.mp hx
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hy
      exact hab (Word.cons.inj hxy).1

def count (as : List Nat) (e : Nat) : Nat :=
  ((words as).filter fun w => decide (energy w = e)).length

def step (A : Nat) (f : Nat → Nat) (e : Nat) : Nat :=
  Nat.sum ((digits A).map fun d =>
    if triangular (radiusIndex A d) ≤ e then f (e - triangular (radiusIndex A d)) else 0)

theorem length_bind (l : List α) (f : α → List β) :
    (l.bind f).length = Nat.sum (l.map fun a => (f a).length) := by
  induction l <;> simp [List.bind, *, Nat.sum, Function.comp_def]

theorem filter_cons_length (l : List (Word as)) (d : Fin (2 * A)) (e : Nat) :
    ((l.map (Word.cons d)).filter fun w => decide (energy w = e)).length =
      if triangular (radiusIndex A d) ≤ e then
        (l.filter fun w => decide (energy w = e - triangular (radiusIndex A d))).length else 0 := by
  rw [List.filter_map, List.length_map]
  by_cases h : triangular (radiusIndex A d) ≤ e
  · rw [if_pos h]
    have heq : (fun w : Word as => decide (energy (Word.cons d w) = e)) =
        (fun w => decide (energy w = e - triangular (radiusIndex A d))) := by
      funext w
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, energy]
      omega
    exact congrArg (fun p => (l.filter p).length) heq
  · rw [if_neg h]
    have he : (fun w : Word as => decide (energy (Word.cons d w) = e)) = fun _ => false := by
      funext w
      simp only [energy, decide_eq_false_iff_not]
      omega
    change (l.filter (fun w => decide (energy (Word.cons d w) = e))).length = 0
    rw [he]
    induction l <;> simp_all [List.filter]

theorem count_cons (A : Nat) (as : List Nat) (e : Nat) :
    count (A :: as) e = step A (count as) e := by
  simp only [count, words, List.filter_bind, length_bind, filter_cons_length, step]

theorem step_congr (A : Nat) (f g : Nat → Nat) (e : Nat) (h : ∀ j, j ≤ e → f j = g j) :
    step A f e = step A g e := by
  unfold step
  congr 2
  funext d
  split
  · rw [h _ (Nat.sub_le _ _)]
  · rfl

def value (m e : Nat) : Nat := (table[m]!.toList).getD e 0

theorem initial_row (e : Fin 120) : value 0 e = if e.val = 0 then 1 else 0 := by
  change row0.toList.getD e 0 = _
  rw [show row0.toList = 1 :: List.replicate 119 0 by decide]
  obtain ⟨e, he⟩ := e
  cases e with
  | zero => rfl
  | succ e =>
    have h : e < 119 := by omega
    simp only [List.getD, List.get?_eq_getElem?, List.getElem?_cons_succ, List.getElem?_replicate, h,
      if_true, Option.getD_some, Fin.val_mk, Nat.succ_ne_zero, if_false]

def nextList (A : Nat) (row : List Nat) : List Nat :=
  (List.range 120).map (fun e => step A (fun j => row.getD j 0) e)


end HeilbronnMixedLayer
