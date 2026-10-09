import Slab

namespace HeilbronnNormCompression
open HeilbronnSphere

-- Permutations map a column index to its selected row in the determinant.
def perm (p : Fin 6) (i : Fin 3) : Fin 3 :=
  (#[#[0, 1, 2], #[0, 2, 1], #[1, 0, 2], #[1, 2, 0], #[2, 0, 1], #[2, 1, 0]]
    : Array (Array (Fin 3)))[p.val]![i.val]!

def comp (p q : Fin 6) : Fin 6 :=
  (#[#[0, 1, 2, 3, 4, 5], #[1, 0, 4, 5, 2, 3], #[2, 3, 0, 1, 5, 4],
      #[3, 2, 5, 4, 0, 1], #[4, 5, 1, 0, 3, 2], #[5, 4, 3, 2, 1, 0]]
    : Array (Array (Fin 6)))[p.val]![q.val]!

def inv (p : Fin 6) : Fin 6 := (#[0, 1, 2, 4, 3, 5] : Array (Fin 6))[p.val]!
def sign (p : Fin 6) : Int := if p.val = 0 ∨ p.val = 3 ∨ p.val = 4 then 1 else -1

theorem perm_injective : ∀ p : Fin 6, ∀ i j : Fin 3,
    perm p i = perm p j → i = j := by decide

theorem perm_distinct : ∀ p q : Fin 6, (∀ i : Fin 3, perm p i = perm q i) → p = q := by decide

def picks (p : Fin 6) (a b c : Fin 3) : Prop :=
  perm p 0 = a ∧ perm p 1 = b ∧ perm p 2 = c

instance (p : Fin 6) (a b c : Fin 3) : Decidable (picks p a b c) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem perm_exhaustive : ∀ a b c : Fin 3, a ≠ b → a ≠ c → b ≠ c →
    ∃ p : Fin 6, picks p a b c := by
  have h : ∀ a b c : Fin 3, a ≠ b → a ≠ c → b ≠ c →
      picks 0 a b c ∨ picks 1 a b c ∨ picks 2 a b c ∨
      picks 3 a b c ∨ picks 4 a b c ∨ picks 5 a b c := by decide
  intro a b c hab hac hbc
  rcases h a b c hab hac hbc with h | h | h | h | h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩
  · exact ⟨2, h⟩
  · exact ⟨3, h⟩
  · exact ⟨4, h⟩
  · exact ⟨5, h⟩

theorem comp_apply : ∀ p q : Fin 6, ∀ i : Fin 3,
    perm (comp p q) i = perm p (perm q i) := by decide

theorem sign_comp : ∀ p q : Fin 6, sign (comp p q) = sign p * sign q := by decide

theorem comp_cancel : ∀ a p : Fin 6,
    comp (comp a (inv p)) p = a ∧ comp (comp a p) (inv p) = a := by decide

def shift (p : Fin 6) : Word 6 m → Word 6 m
  | .nil => .nil
  | .cons a w => .cons (comp a p) (shift p w)

def signature : Word 6 m → Int
  | .nil => 1
  | .cons a w => sign a * signature w

theorem shift_cancel (p : Fin 6) (w : Word 6 m) :
    shift p (shift (inv p) w) = w ∧ shift (inv p) (shift p w) = w := by
  induction w with
  | nil => exact ⟨rfl, rfl⟩
  | cons a w ih =>
    simp only [shift, (comp_cancel a p).1, (comp_cancel a p).2, ih.1, ih.2]
    trivial

theorem shift_signature (p : Fin 6) (w : Word 6 m) :
    signature (shift p w) = signature w * sign p ^ m := by
  induction w with
  | nil => simp [shift, signature, Int.pow_zero]
  | cons a w ih =>
    simp only [shift, signature, sign_comp, ih, Int.pow_succ]
    ac_rfl

def normalize (x : Fin 6 × Word 6 m) : Fin 6 × Word 6 m :=
  (x.1, shift (inv x.1) x.2)

def restore (x : Fin 6 × Word 6 m) : Fin 6 × Word 6 m :=
  (x.1, shift x.1 x.2)

theorem normalization_bijection (x : Fin 6 × Word 6 m) :
    restore (normalize x) = x ∧ normalize (restore x) = x := by
  rcases x with ⟨p, w⟩
  simp only [normalize, restore, (shift_cancel p w).1, (shift_cancel p w).2]
  trivial

theorem normalized_sign (p : Fin 6) (w : Word 6 12) :
    sign p * signature w = signature (shift (inv p) w) * sign p := by
  have h : ∀ p : Fin 6, sign p ^ 12 = 1 := by decide
  rw [shift_signature, h, Int.mul_one, Int.mul_comm]

-- The field-algebra and interpolation argument is written in the note.
-- These theorems certify its permutation bookkeeping and the resulting
-- packing size. NormAlgebra and NormPolynomials prove the field-norm identity.
def normT : Nat := (3 * 13 - 2) * 6 ^ 12

theorem norm_count : normT = 80540946432 := by decide

theorem norm_capacity : normT * (10 * triangular (12 - 1) + 1) ≤ 24 ^ 10 := by decide

theorem norm_packing :
    ∃ u v : Fin ((3 * 13 - 2) * 6 ^ 12) → Nat,
      (∀ a, u a < 47 ^ 10 ∧ v a < 47 ^ 10) ∧
      (∀ a c, u a = u c → a = c) ∧
      (∀ a c, v a = v c → a = c) ∧
      (∀ a c e, u a + u c + v e = 47 ^ 10 - 1 ↔ a = c ∧ c = e) := by
  exact packing_exists (A := 12) (m := 10) (by decide) (by decide)
    (by decide) (by decide) norm_capacity

theorem norm_gain :
    10 ^ 27 * (498 * 47 ^ 10 + 7) < 498 * 379 ^ 17 + 7 ∧
    498 * 379 ^ 17 + 7 < 2 * 10 ^ 27 * (498 * 47 ^ 10 + 7) := by decide

#print axioms perm_injective
#print axioms perm_distinct
#print axioms perm_exhaustive
#print axioms comp_apply
#print axioms sign_comp
#print axioms comp_cancel
#print axioms shift_cancel
#print axioms shift_signature
#print axioms normalization_bijection
#print axioms normalized_sign
#print axioms norm_count
#print axioms norm_capacity
#print axioms norm_packing
#print axioms norm_gain

end HeilbronnNormCompression
