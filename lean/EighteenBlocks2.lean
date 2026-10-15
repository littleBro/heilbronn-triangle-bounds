import EighteenForms

open Finset Matrix
set_option maxHeartbeats 1000000

namespace HeilbronnEighteen
open HeilbronnNorm
variable {R : Type*} [CommRing R]

lemma block_4 (u : R) (hu : u ^ 2 - u + 1 = 0) (V : Matrix Row Row R) :
    (∑ t : Fin 3, ∏ j : Row, ∑ i : Row, coefficients u 4 t i * V i j) =
      3 * ((1 : R) * (V 0 0 * V 1 1 * V 2 2 + V 0 0 * V 2 1 * V 1 2 + V 1 0 * V 0 1 * V 2 2 + V 1 0 * V 2 1 * V 0 2 + V 2 0 * V 0 1 * V 1 2 + V 2 0 * V 1 1 * V 0 2) + (-1 : R) * (V 0 0 * V 0 1 * V 0 2) + (-1 : R) * (V 1 0 * V 1 1 * V 1 2) + (1 : R) * (V 2 0 * V 2 1 * V 2 2)) := by
  have h2 : u ^ 2 = u - 1 := by linear_combination hu
  have h3 : u ^ 3 = -1 := by linear_combination (u + 1) * hu
  simp only [Fin.sum_univ_three, Fin.prod_univ_three, coefficients, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, cons_five, Matrix.head_cons, Matrix.tail_cons]
  ring_nf
  simp only [h2, h3]
  ring

lemma block_5 (u : R) (hu : u ^ 2 - u + 1 = 0) (V : Matrix Row Row R) :
    (∑ t : Fin 3, ∏ j : Row, ∑ i : Row, coefficients u 5 t i * V i j) =
      3 * ((-1 : R) * (V 0 0 * V 1 1 * V 2 2 + V 0 0 * V 2 1 * V 1 2 + V 1 0 * V 0 1 * V 2 2 + V 1 0 * V 2 1 * V 0 2 + V 2 0 * V 0 1 * V 1 2 + V 2 0 * V 1 1 * V 0 2) + (1 : R) * (V 0 0 * V 0 1 * V 0 2) + (1 : R) * (V 1 0 * V 1 1 * V 1 2) + (-1 : R) * (V 2 0 * V 2 1 * V 2 2)) := by
  have h2 : u ^ 2 = u - 1 := by linear_combination hu
  have h3 : u ^ 3 = -1 := by linear_combination (u + 1) * hu
  simp only [Fin.sum_univ_three, Fin.prod_univ_three, coefficients, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, cons_five, Matrix.head_cons, Matrix.tail_cons]
  ring_nf
  simp only [h2, h3]
  ring

#print axioms block_4
#print axioms block_5

end HeilbronnEighteen
