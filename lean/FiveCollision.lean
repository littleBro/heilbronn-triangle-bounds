import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring

/-! Algebraic factorization used by the written fresh-digit argument. -/

namespace HeilbronnFive

theorem repeated_top_factorization {R : Type*} [CommRing R] (a b c d x y z : R) :
    Matrix.det !![a, a, b; c, c, d; x, y, z] = (a * d - b * c) * (x - y) := by
  simp [Matrix.det_fin_three]
  ring

theorem all_equal_top_determinant {R : Type*} [CommRing R] (a c x y z : R) :
    Matrix.det !![a, a, a; c, c, c; x, y, z] = 0 := by
  rw [repeated_top_factorization]
  ring

#print axioms repeated_top_factorization
#print axioms all_equal_top_determinant

end HeilbronnFive
