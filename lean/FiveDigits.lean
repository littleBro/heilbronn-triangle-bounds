import FiveProbability
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval

/-! Exact base expansions and uniqueness of the digits forced by Schur minors. -/

namespace HeilbronnFive
open Finset

def radix (B : ℕ) {k : ℕ} (z : Fin k → ℕ) : ℕ :=
  ∑ i, z i * B ^ i.val

theorem radix_succ (B : ℕ) {k : ℕ} (z : Fin (k+1) → ℕ) :
    radix B z = z 0 + B * radix B (fun i => z i.succ) := by
  simp only [radix, Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one,
    Fin.val_succ, pow_succ, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem radix_prefix {B k j : ℕ} (z w : Fin k → Fin B) (hj : j ≤ k)
    (h : Nat.ModEq (B^j) (radix B (fun i => z i)) (radix B (fun i => w i))) :
    ∀ i, i.val < j → z i = w i := by
  induction k generalizing j with
  | zero => intro i; exact Fin.elim0 i
  | succ k ih =>
    cases j with
    | zero => intro i hi; omega
    | succ j =>
      rw [radix_succ, radix_succ] at h
      have hd : B ∣ B^(j+1) := by
        exact dvd_pow_self B (by omega)
      have he := h.of_dvd hd
      have hzero : z 0 = w 0 := by
        apply Fin.ext
        simpa only [Nat.ModEq, Nat.add_mod, Nat.mul_mod_right,
          add_zero, Nat.mod_mod, Nat.mod_eq_of_lt (z 0).isLt,
          Nat.mod_eq_of_lt (w 0).isLt] using he
      rw [hzero] at h
      have ht : Nat.ModEq (B^j) (radix B (fun i => z i.succ))
          (radix B (fun i => w i.succ)) := by
        have hb : 0 < B := Nat.zero_lt_of_lt (z 0).isLt
        have hh := Nat.ModEq.add_left_cancel' (w 0).val h
        rw [pow_succ'] at hh
        exact Nat.ModEq.mul_left_cancel' (Nat.ne_of_gt hb) hh
      intro i
      refine Fin.cases (fun _ => hzero) (fun p hp => ?_) i
      exact ih (fun i => z i.succ) (fun i => w i.succ) (by omega) ht p (by simpa using hp)

theorem tag_unit {B k : ℕ} (z : Fin (k+1) → ℕ) (hz : z 0 = 1) :
    Nat.Coprime B (radix B z) := by
  rw [radix_succ, hz, Nat.coprime_add_mul_left_right]
  exact Nat.coprime_one_right B

/-- Positive representatives of one residue, in an interval of length `r*M`. -/
def residueAlphabet {r M B : ℕ} (hL : r*M < B) (q : Fin r) (x : Fin M) : Fin B :=
  ⟨q.val + 1 + r*x.val, by
    have hq := q.isLt
    have hx := x.isLt
    have hm := Nat.mul_le_mul_left r (Nat.succ_le_of_lt hx)
    nlinarith⟩

theorem residueAlphabet_injective {r M B : ℕ} (hL : r*M < B) (q : Fin r) :
    Function.Injective (residueAlphabet hL q) := by
  intro x y h
  have he := congrArg Fin.val h
  change q.val + 1 + r*x.val = q.val + 1 + r*y.val at he
  have hr : r ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt q.isLt)
  apply Fin.ext
  exact (Nat.mul_left_cancel (Nat.zero_lt_of_ne_zero hr) (Nat.add_left_cancel he))

theorem residueAlphabet_bounds {r M B : ℕ} (hL : r*M < B) (q : Fin r) (x : Fin M) :
    1 ≤ (residueAlphabet hL q x).val ∧ (residueAlphabet hL q x).val ≤ r*M ∧
    (residueAlphabet hL q x).val % r = (q.val+1) % r := by
  have hq := q.isLt
  have hx := x.isLt
  have hm := Nat.mul_le_mul_left r (Nat.succ_le_of_lt hx)
  constructor
  · simp only [residueAlphabet]; omega
  constructor
  · simp only [residueAlphabet]; nlinarith
  · simp only [residueAlphabet, Nat.add_mod, Nat.mul_mod_right, add_zero, Nat.mod_mod]

theorem residueAlphabet_complete {r M B t : ℕ} (hL : r*M < B) (q : Fin r)
    (ht : 1 ≤ t) (htL : t ≤ r*M) (hres : t % r = (q.val+1) % r) :
    ∃ x : Fin M, (residueAlphabet hL q x).val = t := by
  have hr : 0 < r := Nat.zero_lt_of_lt q.isLt
  have hlt : (t-1)/r < M := by
    apply (Nat.div_lt_iff_lt_mul hr).mpr
    rw [Nat.mul_comm]
    omega
  have hmod : (t-1) % r = q.val := by
    have he : Nat.ModEq r ((t-1)+1) (q.val+1) := by
      simpa only [Nat.sub_add_cancel ht] using hres
    have he' := Nat.ModEq.add_right_cancel' 1 he
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt q.isLt] using he'
  refine ⟨⟨(t-1)/r, hlt⟩, ?_⟩
  have he := Nat.mod_add_div (t-1) r
  simp only [residueAlphabet]
  rw [hmod] at he
  omega

/-- Independent third-row digits. Each alphabet is an injection into base digits;
this includes every prescribed residue class with exactly `M` choices. -/
structure DigitModel (k M : ℕ) where
  base : ℕ
  alphabet : (Fin 3 × Fin k) → Fin M → Fin base
  alphabet_injective : ∀ i, Function.Injective (alphabet i)
  top : Fin 3 → ℕ
  top_unit : Nat.Coprime base (top 0)

namespace DigitModel

variable {k M : ℕ} (m : DigitModel k M)

def ofResidues {r B : ℕ} (hL : r*M < B) (residue : (Fin 3 × Fin k) → Fin r)
    (top : Fin 3 → ℕ) (hunit : Nat.Coprime B (top 0)) : DigitModel k M where
  base := B
  alphabet i := residueAlphabet hL (residue i)
  alphabet_injective i := residueAlphabet_injective hL (residue i)
  top := top
  top_unit := hunit

def entry (x : (Fin 3 × Fin k) → Fin M) (c : Fin 3) : ℕ :=
  radix m.base (fun i => m.alphabet (c,i) (x (c,i)))

def schur (j : ℕ) (x : (Fin 3 × Fin k) → Fin M) : Prop :=
  ∀ c : Fin 3, c ≠ 0 →
    Nat.ModEq (m.base^j) (m.top 0 * m.entry x c) (m.top c * m.entry x 0)

theorem schur_prefix {j : ℕ} (hj : j ≤ k)
    {x y : (Fin 3 × Fin k) → Fin M} (hx : m.schur j x) (hy : m.schur j y)
    (hfirst : ∀ p, x (0,p) = y (0,p)) :
    ∀ c p, p.val < j → x (c,p) = y (c,p) := by
  have he : m.entry x 0 = m.entry y 0 := by
    simp only [entry, radix, hfirst]
  intro c p hp
  by_cases hc : c = 0
  · subst c; exact hfirst p
  have hxy := (hx c hc).trans ((he ▸ hy c hc).symm)
  have hmod := Nat.ModEq.cancel_left_of_coprime (m.top_unit.pow_left j) hxy
  exact m.alphabet_injective (c,p)
    (radix_prefix _ _ hj hmod p hp)

end DigitModel

/-- One nonzero coefficient makes a linear equation determine one unused digit. -/
theorem linear_fresh_unique {I : Type*} [Fintype I] [DecidableEq I] {M B : ℕ}
    (alphabet : I → Fin M → Fin B) (hinj : ∀ i, Function.Injective (alphabet i))
    (w : I → ℤ) (v : I) (hv : w v ≠ 0)
    {x y : I → Fin M} (hxy : ∀ i, i ≠ v → x i = y i)
    (he : (∑ i, w i * (alphabet i (x i)).val) =
      ∑ i, w i * (alphabet i (y i)).val) : x v = y v := by
  have hs : ∑ i, (w i * (alphabet i (x i)).val -
      w i * (alphabet i (y i)).val) =
      w v * (alphabet v (x v)).val - w v * (alphabet v (y v)).val := by
    apply Finset.sum_eq_single v
    · intro i _ hi
      rw [hxy i hi, sub_self]
    · simp
  rw [Finset.sum_sub_distrib, he, sub_self] at hs
  have hh : (alphabet v (x v)).val = (alphabet v (y v)).val := by
    apply Int.natCast_inj.mp
    exact mul_left_cancel₀ hv (sub_eq_zero.mp hs.symm)
  exact hinj v (Fin.ext hh)

#print axioms radix_prefix
#print axioms tag_unit
#print axioms residueAlphabet_injective
#print axioms residueAlphabet_bounds
#print axioms residueAlphabet_complete
#print axioms DigitModel.schur_prefix
#print axioms linear_fresh_unique

end HeilbronnFive
