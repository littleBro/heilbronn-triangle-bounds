import EighteenBlocks0
import EighteenBlocks1
import EighteenBlocks2

open Finset Matrix
set_option maxHeartbeats 1000000

namespace HeilbronnEighteen
open HeilbronnNorm
variable {R : Type*} [CommRing R]

theorem pair_identity (u : R) (hu : u ^ 2 - u + 1 = 0) (A B : Matrix Row Row R) :
    (3 : R) * A.det * B.det =
      ∑ t : PairTerm, ∏ j : Row, pairForm u t (fun r => A r j) (fun r => B r j) := by
  simp only [PairTerm, Fintype.sum_prod_type, sum_six, pairForm]
  rw [block_0 u hu, block_1 u hu, block_2 u hu, block_3 u hu, block_4 u hu, block_5 u hu]
  simp only [rowIndex, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, cons_five, Matrix.head_cons, Matrix.tail_cons, Matrix.det_fin_three]
  ring

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem paired_product (u : R) (hu : u ^ 2 - u + 1 = 0)
    (M : Matrix Row Row R) (A B : I → Matrix Row Row R) :
    (3 : R) ^ Fintype.card I * (M.det * ∏ v, (A v).det * (B v).det) =
      ∑ w : I → PairTerm, Matrix.det (fun i j => M i j *
        ∏ v, pairForm u (w v) (fun r => A v r j) (fun r => B v r j)) := by
  classical
  have h (w : I → PairTerm) :
      Matrix.det (fun i j => M i j * ∏ v,
        pairForm u (w v) (fun r => A v r j) (fun r => B v r j)) =
      M.det * ∏ j, ∏ v, pairForm u (w v) (fun r => A v r j) (fun r => B v r j) := by
    simpa [mul_comm] using Matrix.det_mul_row
      (fun j => ∏ v, pairForm u (w v) (fun r => A v r j) (fun r => B v r j)) M
  simp_rw [h]
  rw [← Finset.mul_sum]
  simp_rw [Finset.prod_comm (s := (univ : Finset Row))]
  rw [← Fintype.prod_sum (fun (v : I) (t : PairTerm) =>
    ∏ j : Row, pairForm u t (fun r => A v r j) (fun r => B v r j))]
  simp_rw [← pair_identity u hu]
  simp only [mul_assoc, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  ring

#print axioms pair_identity
#print axioms paired_product

end HeilbronnEighteen
