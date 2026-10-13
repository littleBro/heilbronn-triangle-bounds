import MixedLayerCounting

/-! Exact energy-layer counts below an encoded cutoff, and in an interval. -/

namespace HeilbronnInterval
open HeilbronnMixedSphere
open HeilbronnMixedLayer (words digits length_bind)
open HeilbronnSphere (triangular radiusIndex)

def nextBound (A B : Nat) (d : Fin (2 * A)) : Nat :=
  B / (4 * A - 1) + if d.val < B % (4 * A - 1) then 1 else 0

theorem digit_bound (A B n : Nat) (d : Fin (2 * A)) :
    d.val + (4 * A - 1) * n < B ↔ n < nextBound A B d := by
  let b := 4 * A - 1
  have hd : d.val < b := by have := d.isLt; dsimp [b]; omega
  have hb : 0 < b := by omega
  have hr := Nat.mod_lt B hb
  have he := Nat.mod_add_div B b
  change d.val + b * n < B ↔ n < B / b + if d.val < B % b then 1 else 0
  by_cases hn : n < B / b
  · have hm := Nat.mul_le_mul_left b (Nat.succ_le_of_lt hn)
    simp only [Nat.mul_succ] at hm
    split <;> omega
  · by_cases hn' : n = B / b
    · subst n
      split <;> omega
    · have hm := Nat.mul_le_mul_left b (show B / b + 1 ≤ n by omega)
      simp only [Nat.mul_add, Nat.mul_one] at hm
      split <;> omega

def belowCount (as : List Nat) (e B : Nat) : Nat :=
  ((words as).filter fun w => decide (energy w = e ∧ encode w < B)).length

def belowStep (A : Nat) (f : Nat → Nat → Nat) (e B : Nat) : Nat :=
  Nat.sum ((digits A).map fun d =>
    if triangular (radiusIndex A d) ≤ e then
      f (e - triangular (radiusIndex A d)) (nextBound A B d) else 0)

theorem filter_cons_length (l : List (Word as)) (d : Fin (2 * A)) (e B : Nat) :
    ((l.map (Word.cons d)).filter fun w => decide (energy w = e ∧ encode w < B)).length =
      if triangular (radiusIndex A d) ≤ e then
        (l.filter fun w => decide (energy w = e - triangular (radiusIndex A d) ∧
          encode w < nextBound A B d)).length else 0 := by
  rw [List.filter_map, List.length_map]
  by_cases h : triangular (radiusIndex A d) ≤ e
  · rw [if_pos h]
    have heq : (fun w : Word as => decide (energy (Word.cons d w) = e ∧
        encode (Word.cons d w) < B)) =
        (fun w => decide (energy w = e - triangular (radiusIndex A d) ∧
          encode w < nextBound A B d)) := by
      funext w
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, energy, encode, digit_bound]
      omega
    exact congrArg (fun p => (l.filter p).length) heq
  · rw [if_neg h]
    have he : (fun w : Word as => decide (energy (Word.cons d w) = e ∧
        encode (Word.cons d w) < B)) = fun _ => false := by
      funext w
      simp only [energy, decide_eq_false_iff_not]
      omega
    change (l.filter (fun w => decide (energy (Word.cons d w) = e ∧
      encode (Word.cons d w) < B))).length = 0
    rw [he]
    induction l <;> simp_all [List.filter]

theorem below_cons (A : Nat) (as : List Nat) (e B : Nat) :
    belowCount (A :: as) e B = belowStep A (belowCount as) e B := by
  simp only [belowCount, words, List.filter_bind, length_bind, filter_cons_length, belowStep]

def tableStep (A B : Nat) (lo hi : Nat → Nat) (e : Nat) : Nat :=
  Nat.sum ((digits A).map fun d =>
    if triangular (radiusIndex A d) ≤ e then
      (if d.val < B % (4 * A - 1) then hi else lo)
        (e - triangular (radiusIndex A d)) else 0)

theorem step_from_tables (A B e : Nat) (f : Nat → Nat → Nat) (lo hi : Nat → Nat)
    (hl : ∀ j, j ≤ e → f j (B / (4 * A - 1)) = lo j)
    (hh : ∀ j, j ≤ e → f j (B / (4 * A - 1) + 1) = hi j) :
    belowStep A f e B = tableStep A B lo hi e := by
  unfold belowStep tableStep
  congr 2
  funext d
  split
  · simp only [nextBound]
    split
    · exact hh _ (Nat.sub_le _ _)
    · simpa using hl _ (Nat.sub_le _ _)
  · rfl

def tableAdvance (N A B : Nat) (lo hi : List Nat) : List Nat :=
  (List.range N).map fun e => tableStep A B (fun j => lo.getD j 0) (fun j => hi.getD j 0) e

theorem tableAdvance_get (N A B : Nat) (lo hi : List Nat) (e : Nat) (he : e < N) :
    (tableAdvance N A B lo hi).getD e 0 =
      tableStep A B (fun j => lo.getD j 0) (fun j => hi.getD j 0) e := by
  simp [tableAdvance, List.getD, List.getElem?_range, he]

theorem below_nil (e B : Nat) :
    belowCount [] e B = if e = 0 ∧ 0 < B then 1 else 0 := by
  by_cases he : e = 0 <;> by_cases hb : 0 < B <;>
    simp_all [belowCount, words, energy, encode, List.filter, eq_comm]

theorem zero_row (N e : Nat) : (List.replicate N 0).getD e 0 = 0 := by
  simp only [List.getD, List.get?_eq_getElem?, List.getElem?_replicate]
  split <;> rfl

theorem unit_row (N e : Nat) :
    (1 :: List.replicate N 0).getD e 0 = if e = 0 then 1 else 0 := by
  cases e with
  | zero => rfl
  | succ e =>
    change (List.replicate N 0).getD e 0 = 0
    exact zero_row N e

def intervalCount (as : List Nat) (e L U : Nat) : Nat :=
  ((words as).filter fun w => decide (energy w = e ∧ L ≤ encode w ∧ encode w < U)).length

theorem interval_partition (as : List Nat) (e L U : Nat) (h : L ≤ U) :
    belowCount as e L + intervalCount as e L U = belowCount as e U := by
  unfold belowCount intervalCount
  induction words as with
  | nil => rfl
  | cons w ws ih =>
    by_cases he : energy w = e <;>
      by_cases hl : encode w < L <;>
      by_cases hu : encode w < U <;>
      simp_all [List.filter_cons, Nat.not_lt]
    all_goals omega

#print axioms digit_bound
#print axioms below_cons
#print axioms interval_partition

end HeilbronnInterval
