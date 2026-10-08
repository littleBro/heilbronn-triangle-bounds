import Lean
set_option exponentiation.threshold 512

/-
Local replacement lemma for the digit positions in OpenAI math family 191.
This file does NOT formalize the analytic/geometric Heilbronn theorem.
The original manuscript is kept unchanged in ../upstream/manuscript.
-/
namespace HeilbronnPacking

inductive Word : Nat → Type where
  | nil : Word 0
  | cons {m : Nat} : Bool → Word m → Word (m + 1)
  deriving DecidableEq

def ternary : Word m → Nat
  | .nil => 0
  | .cons b w => 3 * ternary w + if b then 1 else 0

def binary : Word m → Nat
  | .nil => 0
  | .cons b w => 2 * binary w + if b then 1 else 0

def ofNat : (m : Nat) → Nat → Word m
  | 0, _ => .nil
  | m + 1, a => .cons (decide (a % 2 = 1)) (ofNat m (a / 2))

theorem ternary_bound (w : Word m) : 2 * ternary w < 3 ^ m := by
  induction w with
  | nil => decide
  | @cons m b w ih =>
    cases b <;> simp only [ternary, Bool.false_eq_true, if_false, if_true, Nat.pow_succ]
      <;> omega

theorem midpoint (x y z : Word m)
    (h : ternary x + ternary y = 2 * ternary z) : x = y ∧ y = z := by
  induction x with
  | nil =>
    cases y
    cases z
    exact ⟨rfl, rfl⟩
  | @cons m b x ih =>
    cases y with
    | cons c y =>
      cases z with
      | cons d z =>
        cases b <;> cases c <;> cases d <;> simp [ternary] at h
          <;> try omega
        all_goals
          have ht : ternary x + ternary y = 2 * ternary z := by omega
          obtain ⟨rfl, rfl⟩ := ih y z ht
          exact ⟨rfl, rfl⟩

theorem binary_ofNat (m a : Nat) (ha : a < 2 ^ m) :
    binary (ofNat m a) = a := by
  induction m generalizing a with
  | zero =>
    have : a = 0 := by simp only [Nat.pow_zero] at ha; omega
    subst a
    rfl
  | succ m ih =>
    have hhalf : a / 2 < 2 ^ m := by
      simp only [Nat.pow_succ] at ha
      omega
    simp only [ofNat, binary, ih (a / 2) hhalf]
    split <;> simp_all <;> omega

theorem ofNat_injective {m a b : Nat} (ha : a < 2 ^ m) (hb : b < 2 ^ m)
    (h : ofNat m a = ofNat m b) : a = b := by
  have hv := congrArg binary h
  simpa only [binary_ofNat m a ha, binary_ofNat m b hb] using hv

def left (m a : Nat) : Nat := ternary (ofNat m a)
def right (m a : Nat) : Nat := 3 ^ m - 1 - 2 * left m a

theorem position_bounds (m a : Nat) :
    left m a < 3 ^ m ∧ right m a < 3 ^ m := by
  have h := ternary_bound (ofNat m a)
  simp only [left, right]
  omega

theorem left_injective {m a b : Nat} (ha : a < 2 ^ m) (hb : b < 2 ^ m)
    (h : left m a = left m b) : a = b := by
  have hw := midpoint (ofNat m a) (ofNat m a) (ofNat m b) (by
    simp only [left] at h
    omega)
  exact ofNat_injective ha hb hw.2

theorem right_injective {m a b : Nat} (ha : a < 2 ^ m) (hb : b < 2 ^ m)
    (h : right m a = right m b) : a = b := by
  have hba := ternary_bound (ofNat m a)
  have hbb := ternary_bound (ofNat m b)
  apply left_injective ha hb
  simp only [right, left] at *
  omega

theorem matching {m a b c : Nat}
    (ha : a < 2 ^ m) (hb : b < 2 ^ m) (hc : c < 2 ^ m) :
    left m a + left m b + right m c = 3 ^ m - 1 ↔ a = b ∧ b = c := by
  have hbc := ternary_bound (ofNat m c)
  constructor
  · intro h
    have ht : ternary (ofNat m a) + ternary (ofNat m b) =
        2 * ternary (ofNat m c) := by
      simp only [left, right] at h
      omega
    obtain ⟨hab, hbc⟩ := midpoint (ofNat m a) (ofNat m b) (ofNat m c) ht
    exact ⟨ofNat_injective ha hb hab, ofNat_injective hb hc hbc⟩
  · rintro ⟨rfl, rfl⟩
    simp only [left, right]
    omega

-- This is the exact finite interface needed by the determinant obstruction:
-- T positions per row, within [0, k), injective in each row, and only matching
-- triples in the designated coefficient. No enumeration of the T positions.
theorem packing_interface {T m : Nat} (hT : T ≤ 2 ^ m) :
    (∀ a, a < T → left m a < 3 ^ m ∧ right m a < 3 ^ m) ∧
    (∀ a b, a < T → b < T → left m a = left m b → a = b) ∧
    (∀ a b, a < T → b < T → right m a = right m b → a = b) ∧
    (∀ a b c, a < T → b < T → c < T →
      (left m a + left m b + right m c = 3 ^ m - 1 ↔ a = b ∧ b = c)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a _
    exact position_bounds m a
  · intro a b ha hb h
    exact left_injective (by omega) (by omega) h
  · intro a b ha hb h
    exact right_injective (by omega) (by omega) h
  · intro a b c ha hb hc
    exact matching (by omega) (by omega) (by omega)

-- This literal is recomputed in two different ways by the Python generator
-- and independent verifier. Its identification with binom(binom(163,41),3)
-- is not a formal theorem in this Lean file.
def paperT : Nat :=
  37230514451212307341579258391864337055334059182582962517976151329575965621134724577475162784520018371181237814762800

theorem paper_capacity : 2 ^ 383 < paperT ∧ paperT ≤ 2 ^ 384 := by decide

theorem paper_matching {a b c : Nat}
    (ha : a < paperT) (hb : b < paperT) (hc : c < paperT) :
    left 384 a + left 384 b + right 384 c = 3 ^ 384 - 1 ↔ a = b ∧ b = c := by
  have hcap := paper_capacity.2
  exact matching (by omega) (by omega) (by omega)

theorem smaller_parameter : 3 ^ 384 < paperT ^ 2 + 1 := by decide

-- Exact comparison of the denominators of the two *paper* exponents.
-- It does not assert an analytic theorem about triangle areas.
theorem exponent_gain :
    8 * 10 ^ 47 * (45435 * 3 ^ 384 + 16) <
      45435 * (paperT ^ 2 + 1) + 16 ∧
    45435 * (paperT ^ 2 + 1) + 16 <
      9 * 10 ^ 47 * (45435 * 3 ^ 384 + 16) := by decide

#print axioms packing_interface
#print axioms paper_matching
#print axioms paper_capacity
#print axioms smaller_parameter
#print axioms exponent_gain

end HeilbronnPacking
