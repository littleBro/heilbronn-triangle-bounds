import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Symbolic regrouping of thirteen determinants; no enumeration of the
    `6 ^ 12` summands is involved in this proof. -/

open Finset Matrix Equiv

namespace HeilbronnNorm

abbrev Row := Fin 3
abbrev Orbit := Fin 12 → Equiv.Perm Row

variable {R : Type*} [CommRing R]

def signR (p : Equiv.Perm Row) : R := ((Equiv.Perm.sign p : ℤ) : R)

lemma signR_mul (p q : Equiv.Perm Row) :
    signR (R := R) (p * q) = signR p * signR q := by
  simp [signR, Equiv.Perm.sign_mul]

lemma signR_pow_twelve (p : Equiv.Perm Row) : (signR (R := R) p) ^ 12 = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign p) with h | h <;> norm_num [signR, h]

lemma det_expansion (A : Matrix Row Row R) :
    A.det = ∑ p, signR p * ∏ i, A (p i) i := Matrix.det_apply' A

/-- The twelve relative row permutations parametrize each diagonal orbit. -/
theorem determinant_product_compression
    (A : Matrix Row Row R) (B : Fin 12 → Matrix Row Row R) :
    A.det * (∏ v, (B v).det) =
      ∑ ρ : Orbit, (∏ v, signR (ρ v)) *
        Matrix.det (fun i j => A i j * ∏ v, B v (ρ v i) j) := by
  classical
  simp only [det_expansion, Fintype.prod_sum]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  symm
  apply Fintype.sum_equiv (Equiv.mulRight (fun _ : Fin 12 => p))
  intro ρ
  simp only [Equiv.coe_mulRight, Pi.mul_apply, signR_mul,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, signR_pow_twelve, mul_one, Equiv.Perm.coe_mul,
    Function.comp_apply]
  rw [Finset.prod_comm]
  ring

theorem orbit_card : Fintype.card Orbit = 6 ^ 12 := by
  simp [Orbit, Row, Fintype.card_fun, Fintype.card_perm, Nat.factorial]

#print axioms determinant_product_compression
#print axioms orbit_card

end HeilbronnNorm
