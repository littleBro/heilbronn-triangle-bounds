import NormPolynomials

/-! Interpolate the product of two representatives, then apply a linear
    functional to the third factor. This needs twenty-five nodes. -/

open Finset Polynomial

namespace HeilbronnNorm

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

noncomputable def interpolationElement (pb : PowerBasis F K)
    (node : Fin 25 → F) (t : Fin 25) : K :=
  aeval pb.gen (Lagrange.basis univ node t)

noncomputable def productCoord (pb : PowerBasis F K) (node : Fin 25 → F)
    (t : Fin 25) : K →ₗ[F] F :=
  (constantCoord pb).comp (LinearMap.mulLeft F (interpolationElement pb node t))

lemma bilinear_interpolation (pb : PowerBasis F K) (hd : pb.dim = 13)
    (node : Fin 25 → F) (hn : Function.Injective node) (x y : K) :
    x * y = ∑ t, algebraMap F K
      ((representative pb x).eval (node t) * (representative pb y).eval (node t)) *
      interpolationElement pb node t := by
  let P := representative pb x * representative pb y
  have hx := representative_degree pb x
  have hy := representative_degree pb y
  rw [hd] at hx hy
  have hP : P.natDegree ≤ 24 := natDegree_mul_le.trans (by omega)
  have hdeg : P.degree < (univ : Finset (Fin 25)).card :=
    degree_le_natDegree.trans_lt (by simpa using (show P.natDegree < 25 by omega))
  have heval : aeval pb.gen P = x * y := by
    simp only [P, map_mul, representative_eval]
  rw [← heval, Lagrange.eq_interpolate (fun _ _ _ _ h => hn h) hdeg]
  simp only [Lagrange.interpolate_apply, map_sum, map_mul, aeval_C,
    P, eval_mul, interpolationElement]

lemma bilinear_triple (pb : PowerBasis F K) (hd : pb.dim = 13)
    (node : Fin 25 → F) (hn : Function.Injective node) (x y z : K) :
    constantCoord pb (x * y * z) = ∑ t,
      (representative pb x).eval (node t) * (representative pb y).eval (node t) *
      productCoord pb node t z := by
  rw [bilinear_interpolation pb hd node hn x y, Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [mul_assoc, ← Algebra.smul_def, map_smul, smul_eq_mul]
  rfl

noncomputable def bilinearRow (pb : PowerBasis F K) (node : Fin 25 → F)
    (t : Fin 25) (i : Row) : K →ₗ[F] F :=
  if i = 2 then productCoord pb node t else evaluationCoord pb (node t)

theorem bilinear_determinant_descent (pb : PowerBasis F K) (hd : pb.dim = 13)
    (node : Fin 25 → F) (hn : Function.Injective node) (M : Matrix Row Row K) :
    constantCoord pb M.det = ∑ t, Matrix.det (fun i j => bilinearRow pb node t i (M i j)) := by
  simp only [Row, Matrix.det_fin_three, map_sub, map_add,
    bilinear_triple pb hd node hn, bilinearRow, show (0 : Fin 3) ≠ 2 by decide,
    show (1 : Fin 3) ≠ 2 by decide, if_false, if_true, evaluationCoord_apply]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]

#print axioms bilinear_interpolation
#print axioms bilinear_determinant_descent

end HeilbronnNorm
