import FrobeniusNorm

/-! The integral five-term formula of Krishna--Makam (arXiv:1801.00496,
    Section 3.1), followed by antisymmetrization of thirteen factors. -/

open Finset Matrix Equiv

namespace HeilbronnRankFive
open HeilbronnNorm

def coefficient : Fin 5 → Row → Row → ℤ :=
  ![![![0, 1, 1], ![1, 0, 0], ![0, 1, 0]],
    ![![-1, 0, -1], ![0, 1, 0], ![1, 0, 0]],
    ![![0, -1, 0], ![1, 0, 1], ![0, 1, 1]],
    ![![-1, 1, 0], ![0, 0, 1], ![1, 1, 1]],
    ![![1, 0, 0], ![0, 1, 1], ![1, 0, 1]]]

variable {R : Type*} [CommRing R]

def form (t : Fin 5) (i : Row) (v : Row → R) : R := ∑ r, (coefficient t i r : R) * v r

theorem rank_five (M : Matrix Row Row R) :
    M.det = ∑ t : Fin 5, ∏ i : Row, form t i (fun r => M r i) := by
  simp [form, coefficient, Row, Fin.sum_univ_succ, Fin.prod_univ_succ, Matrix.det_fin_three]
  ring

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem product_expansion (M : A → Matrix Row Row R) :
    (∏ a, (M a).det) = ∑ w : A → Fin 5, ∏ i : Row, ∏ a, form (w a) i (fun r => M a r i) := by
  classical
  simp only [rank_five, Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro w _
  exact Finset.prod_comm

theorem antisymmetrized_product (hc : Fintype.card A = 13) (M : A → Matrix Row Row R) :
    (6 : R) * (∏ a, (M a).det) =
      ∑ w : A → Fin 5, Matrix.det (fun i j => ∏ a, form (w a) i (fun r => M a r j)) := by
  classical
  have hd (p : Equiv.Perm Row) :
      (∏ a, Matrix.det (fun i j => M a i (p j))) =
        signR p * ∏ a, (M a).det := by
    have he (a : A) : Matrix.det (fun i j => M a i (p j)) = signR p * (M a).det := by
      simpa [signR, Units.smul_def, Matrix.submatrix] using Matrix.det_permute' p (M a)
    simp only [he, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hc,
      HeilbronnFrobenius.signR_thirteen]
  have hs (p : Equiv.Perm Row) :
      signR p * (∏ a, Matrix.det (fun i j => M a i (p j))) = ∏ a, (M a).det := by
    rw [hd, ← mul_assoc, ← pow_two, HeilbronnFrobenius.signR_sq, one_mul]
  calc
    _ = ∑ p : Equiv.Perm Row, signR p * (∏ a, Matrix.det (fun i j => M a i (p j))) := by
      simp only [hs, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      congr 1
    _ = _ := by
      simp_rw [product_expansion, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro w _
      rw [← Matrix.det_transpose, Matrix.det_apply']
      rfl

#print axioms rank_five
#print axioms antisymmetrized_product

end HeilbronnRankFive
