import PairedExpansion

/-! The 18-form decomposition of Conner--Gesmundo--Landsberg--Ventura,
    arXiv:1909.04785, Theorem 4.1. We clear the second coefficient column
    and check the resulting identity directly, including its factor 3. -/

open Finset Matrix

set_option maxHeartbeats 1000000

namespace HeilbronnEighteen
open HeilbronnNorm

abbrev PairTerm := Fin 6 × Fin 3

variable {R : Type*} [CommRing R]

def rowIndex : Fin 6 → Row → Row :=
  ![![0, 1, 2], ![0, 2, 1], ![1, 0, 2], ![2, 0, 1], ![1, 2, 0], ![2, 1, 0]]

def coefficients (u : R) : Fin 6 → Fin 3 → Row → R :=
  ![![![-u, -1, 1-u], ![u-1, -1, u], ![u-1, 1-u, 1-u]],
    ![![-1, -u, u-1], ![1-u, -u, 1], ![u, -u, -u]],
    ![![-u, 1-u, 1], ![u-1, 1-u, u-1], ![u-1, u, 1]],
    ![![-1, -u, 1-u], ![-1, u-1, u], ![-1, 1, -1]],
    ![![-1, -1, 1], ![1-u, u, 1], ![u, 1-u, 1]],
    ![![1, -u, 1-u], ![u-1, u-1, 1-u], ![1, u-1, u]]]

def pairForm (u : R) (t : PairTerm) (x y : Row → R) : R :=
  ∑ i, coefficients u t.1 t.2 i * (x (rowIndex t.1 i) * y i)

private lemma sum_six (f : Fin 6 → R) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_five]
  rfl

private lemma cons_five {α : Type*} (x : α) (v : Fin 5 → α) :
    Matrix.vecCons x v (5 : Fin 6) = v 4 := rfl

private lemma block_0 (u : R) (hu : u ^ 2 - u + 1 = 0) (V : Matrix Row Row R) :
    (∑ t : Fin 3, ∏ j : Row, ∑ i : Row, coefficients u 0 t i * V i j) =
      3 * ((1 : R) * (V 0 0 * V 1 1 * V 2 2 + V 0 0 * V 2 1 * V 1 2 + V 1 0 * V 0 1 * V 2 2 + V 1 0 * V 2 1 * V 0 2 + V 2 0 * V 0 1 * V 1 2 + V 2 0 * V 1 1 * V 0 2) + (1 : R) * (V 0 0 * V 0 1 * V 0 2) + (-1 : R) * (V 1 0 * V 1 1 * V 1 2) + (-1 : R) * (V 2 0 * V 2 1 * V 2 2)) := by
  have h2 : u ^ 2 = u - 1 := by linear_combination hu
  have h3 : u ^ 3 = -1 := by linear_combination (u + 1) * hu
  simp only [Fin.sum_univ_three, Fin.prod_univ_three, coefficients, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, cons_five, Matrix.head_cons, Matrix.tail_cons]
  ring_nf
  simp only [h2, h3]
  ring

private lemma block_1 (u : R) (hu : u ^ 2 - u + 1 = 0) (V : Matrix Row Row R) :
    (∑ t : Fin 3, ∏ j : Row, ∑ i : Row, coefficients u 1 t i * V i j) =
      3 * ((-1 : R) * (V 0 0 * V 1 1 * V 2 2 + V 0 0 * V 2 1 * V 1 2 + V 1 0 * V 0 1 * V 2 2 + V 1 0 * V 2 1 * V 0 2 + V 2 0 * V 0 1 * V 1 2 + V 2 0 * V 1 1 * V 0 2) + (-1 : R) * (V 0 0 * V 0 1 * V 0 2) + (1 : R) * (V 1 0 * V 1 1 * V 1 2) + (1 : R) * (V 2 0 * V 2 1 * V 2 2)) := by
  have h2 : u ^ 2 = u - 1 := by linear_combination hu
  have h3 : u ^ 3 = -1 := by linear_combination (u + 1) * hu
  simp only [Fin.sum_univ_three, Fin.prod_univ_three, coefficients, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, cons_five, Matrix.head_cons, Matrix.tail_cons]
  ring_nf
  simp only [h2, h3]
  ring

private lemma block_2 (u : R) (hu : u ^ 2 - u + 1 = 0) (V : Matrix Row Row R) :
    (∑ t : Fin 3, ∏ j : Row, ∑ i : Row, coefficients u 2 t i * V i j) =
      3 * ((-1 : R) * (V 0 0 * V 1 1 * V 2 2 + V 0 0 * V 2 1 * V 1 2 + V 1 0 * V 0 1 * V 2 2 + V 1 0 * V 2 1 * V 0 2 + V 2 0 * V 0 1 * V 1 2 + V 2 0 * V 1 1 * V 0 2) + (1 : R) * (V 0 0 * V 0 1 * V 0 2) + (-1 : R) * (V 1 0 * V 1 1 * V 1 2) + (1 : R) * (V 2 0 * V 2 1 * V 2 2)) := by
  have h2 : u ^ 2 = u - 1 := by linear_combination hu
  have h3 : u ^ 3 = -1 := by linear_combination (u + 1) * hu
  simp only [Fin.sum_univ_three, Fin.prod_univ_three, coefficients, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, cons_five, Matrix.head_cons, Matrix.tail_cons]
  ring_nf
  simp only [h2, h3]
  ring

private lemma block_3 (u : R) (hu : u ^ 2 - u + 1 = 0) (V : Matrix Row Row R) :
    (∑ t : Fin 3, ∏ j : Row, ∑ i : Row, coefficients u 3 t i * V i j) =
      3 * ((1 : R) * (V 0 0 * V 1 1 * V 2 2 + V 0 0 * V 2 1 * V 1 2 + V 1 0 * V 0 1 * V 2 2 + V 1 0 * V 2 1 * V 0 2 + V 2 0 * V 0 1 * V 1 2 + V 2 0 * V 1 1 * V 0 2) + (-1 : R) * (V 0 0 * V 0 1 * V 0 2) + (1 : R) * (V 1 0 * V 1 1 * V 1 2) + (-1 : R) * (V 2 0 * V 2 1 * V 2 2)) := by
  have h2 : u ^ 2 = u - 1 := by linear_combination hu
  have h3 : u ^ 3 = -1 := by linear_combination (u + 1) * hu
  simp only [Fin.sum_univ_three, Fin.prod_univ_three, coefficients, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, cons_five, Matrix.head_cons, Matrix.tail_cons]
  ring_nf
  simp only [h2, h3]
  ring

private lemma block_4 (u : R) (hu : u ^ 2 - u + 1 = 0) (V : Matrix Row Row R) :
    (∑ t : Fin 3, ∏ j : Row, ∑ i : Row, coefficients u 4 t i * V i j) =
      3 * ((1 : R) * (V 0 0 * V 1 1 * V 2 2 + V 0 0 * V 2 1 * V 1 2 + V 1 0 * V 0 1 * V 2 2 + V 1 0 * V 2 1 * V 0 2 + V 2 0 * V 0 1 * V 1 2 + V 2 0 * V 1 1 * V 0 2) + (-1 : R) * (V 0 0 * V 0 1 * V 0 2) + (-1 : R) * (V 1 0 * V 1 1 * V 1 2) + (1 : R) * (V 2 0 * V 2 1 * V 2 2)) := by
  have h2 : u ^ 2 = u - 1 := by linear_combination hu
  have h3 : u ^ 3 = -1 := by linear_combination (u + 1) * hu
  simp only [Fin.sum_univ_three, Fin.prod_univ_three, coefficients, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, cons_five, Matrix.head_cons, Matrix.tail_cons]
  ring_nf
  simp only [h2, h3]
  ring

private lemma block_5 (u : R) (hu : u ^ 2 - u + 1 = 0) (V : Matrix Row Row R) :
    (∑ t : Fin 3, ∏ j : Row, ∑ i : Row, coefficients u 5 t i * V i j) =
      3 * ((-1 : R) * (V 0 0 * V 1 1 * V 2 2 + V 0 0 * V 2 1 * V 1 2 + V 1 0 * V 0 1 * V 2 2 + V 1 0 * V 2 1 * V 0 2 + V 2 0 * V 0 1 * V 1 2 + V 2 0 * V 1 1 * V 0 2) + (1 : R) * (V 0 0 * V 0 1 * V 0 2) + (1 : R) * (V 1 0 * V 1 1 * V 1 2) + (-1 : R) * (V 2 0 * V 2 1 * V 2 2)) := by
  have h2 : u ^ 2 = u - 1 := by linear_combination hu
  have h3 : u ^ 3 = -1 := by linear_combination (u + 1) * hu
  simp only [Fin.sum_univ_three, Fin.prod_univ_three, coefficients, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, cons_five, Matrix.head_cons, Matrix.tail_cons]
  ring_nf
  simp only [h2, h3]
  ring

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
