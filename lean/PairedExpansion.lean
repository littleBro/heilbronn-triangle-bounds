import RankFiveExpansion

/-! Pair two determinants using the five-term formula and cubic polarization.
    The same bilinear form occurs in all three columns of each summand. -/

open Finset Matrix

namespace HeilbronnPaired
open HeilbronnNorm

abbrev PairTerm := Fin 5 × Fin 4

def signs : Fin 4 → Row → ℤ :=
  ![![1, 1, 1], ![1, -1, -1], ![-1, 1, -1], ![-1, -1, 1]]

variable {R : Type*} [CommRing R]

def pairForm (t : PairTerm) (x y : Row → R) : R :=
  ∑ i, ∑ r, (signs t.2 i * HeilbronnRankFive.coefficient t.1 i r : ℤ) * x r * y i

theorem pair_identity (A B : Matrix Row Row R) :
    (4 : R) * A.det * B.det =
      ∑ t : PairTerm, ∏ j : Row, pairForm t (fun r => A r j) (fun r => B r j) := by
  simp [PairTerm, Fintype.sum_prod_type, pairForm, signs, HeilbronnRankFive.coefficient,
    Row, Fin.sum_univ_succ, Fin.prod_univ_succ, Matrix.det_fin_three]
  ring

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem paired_product (M : Matrix Row Row R) (A B : I → Matrix Row Row R) :
    (4 : R) ^ Fintype.card I * (M.det * ∏ v, (A v).det * (B v).det) =
      ∑ w : I → PairTerm, Matrix.det (fun i j => M i j *
        ∏ v, pairForm (w v) (fun r => A v r j) (fun r => B v r j)) := by
  classical
  have h (w : I → PairTerm) :
      Matrix.det (fun i j => M i j * ∏ v,
        pairForm (w v) (fun r => A v r j) (fun r => B v r j)) =
      M.det * ∏ j, ∏ v, pairForm (w v) (fun r => A v r j) (fun r => B v r j) := by
    simpa [mul_comm] using Matrix.det_mul_row
      (fun j => ∏ v, pairForm (w v) (fun r => A v r j) (fun r => B v r j)) M
  simp_rw [h]
  rw [← Finset.mul_sum]
  simp_rw [Finset.prod_comm (s := (univ : Finset Row))]
  rw [← Fintype.prod_sum (fun (v : I) (t : PairTerm) =>
    ∏ j : Row, pairForm t (fun r => A v r j) (fun r => B v r j))]
  simp_rw [← pair_identity]
  simp only [mul_assoc, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  ring

#print axioms pair_identity
#print axioms paired_product

end HeilbronnPaired
