/-
The determinant degree argument adapts the estimate in Mathlib's
LinearAlgebra/Matrix/Polynomial.lean (Copyright 2021 Yakov Pechersky),
licensed under Apache-2.0. The other arguments formalize the research note.
-/
import NormExpansion
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.PowerBasis
import Mathlib.Algebra.Polynomial.BigOperators

/-! Descent through thirty-seven evaluations of degree-at-most-thirty-six
    determinant polynomials. The projection is only used as a linear map. -/

open Finset Polynomial

namespace HeilbronnNorm

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

noncomputable def representative (pb : PowerBasis F K) : K →ₗ[F] F[X] :=
  pb.basis.constr F (fun i => Polynomial.X ^ (i : ℕ))

lemma representative_degree (pb : PowerBasis F K) (x : K) :
    (representative pb x).natDegree < pb.dim := by
  classical
  rw [representative, Basis.constr_apply, Finsupp.sum_fintype]
  · apply lt_of_le_of_lt (natDegree_sum_le_of_forall_le (n := pb.dim - 1) _ _ ?_)
      (Nat.sub_lt pb.dim_pos (show 0 < 1 by decide))
    intro i _
    apply (natDegree_smul_le _ _).trans
    simpa using (show (i : ℕ) ≤ pb.dim - 1 from Nat.le_pred_of_lt i.isLt)
  · intro i
    exact zero_smul _ _

lemma representative_eval (pb : PowerBasis F K) (x : K) :
    aeval pb.gen (representative pb x) = x := by
  have h : (aeval pb.gen).toLinearMap.comp (representative pb) = LinearMap.id := by
    apply pb.basis.ext
    intro i
    change aeval pb.gen ((pb.basis.constr F (fun j => Polynomial.X ^ (j : ℕ)))
      (pb.basis i)) = pb.basis i
    rw [pb.basis.constr_basis, pb.basis_eq_pow]
    simp
  exact LinearMap.congr_fun h x

noncomputable def constantCoord (pb : PowerBasis F K) : K →ₗ[F] F :=
  pb.basis.coord ⟨0, pb.dim_pos⟩

lemma constantCoord_one (pb : PowerBasis F K) : constantCoord pb 1 = 1 := by
  have hb : pb.basis ⟨0, pb.dim_pos⟩ = 1 := by
    rw [pb.basis_eq_pow]
    simp
  change (pb.basis.repr 1) ⟨0, pb.dim_pos⟩ = 1
  rw [← hb, Basis.repr_self]
  exact Finsupp.single_eq_same

lemma constantCoord_algebraMap (pb : PowerBasis F K) (x : F) :
    constantCoord pb (algebraMap F K x) = x := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, constantCoord_one, smul_eq_mul, mul_one]

lemma determinant_degree (P : Matrix Row Row F[X])
    (hP : ∀ i j, (P i j).natDegree ≤ 12) : P.det.natDegree ≤ 36 := by
  classical
  rw [Matrix.det_apply]
  apply natDegree_sum_le_of_forall_le
  intro p _
  have hs : (Equiv.Perm.sign p • ∏ i, P (p i) i).natDegree =
      (∏ i, P (p i) i).natDegree := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign p) with h | h <;>
      simp [h, Units.neg_smul]
  rw [hs]
  calc
    (∏ i, P (p i) i).natDegree ≤ ∑ i, (P (p i) i).natDegree := natDegree_prod_le _ _
    _ ≤ ∑ _i : Row, 12 := Finset.sum_le_sum (fun i _ => hP (p i) i)
    _ = 36 := by simp [Row]

lemma project_interpolate (ℓ : K →ₗ[F] F) (θ : K)
    (node : Fin 37 → F) (hn : Function.Injective node)
    (P : F[X]) (hP : P.natDegree ≤ 36) :
    ℓ (aeval θ P) = ∑ t, ℓ (aeval θ (Lagrange.basis univ node t)) * P.eval (node t) := by
  have hd : P.degree < (univ : Finset (Fin 37)).card := by
    exact (Polynomial.degree_le_natDegree).trans_lt (by simpa using (show P.natDegree < 37 by omega))
  conv_lhs => rw [Lagrange.eq_interpolate (fun _ _ _ _ h => hn h) hd]
  simp only [Lagrange.interpolate_apply, map_sum, map_mul, aeval_C]
  simp only [← Algebra.smul_def, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro t _
  exact mul_comm _ _

/-- One extension-field determinant descends to thirty-seven base-field determinants. -/
theorem determinant_descent (pb : PowerBasis F K) (hd : pb.dim = 13)
    (node : Fin 37 → F) (hn : Function.Injective node)
    (M : Matrix Row Row K) :
    constantCoord pb M.det =
      ∑ t, constantCoord pb (aeval pb.gen (Lagrange.basis univ node t)) *
        Matrix.det (fun i j => (representative pb (M i j)).eval (node t)) := by
  let P : Matrix Row Row F[X] := fun i j => representative pb (M i j)
  have hp : P.det.natDegree ≤ 36 := determinant_degree P (by
    intro i j
    have h := representative_degree pb (M i j)
    rw [hd] at h
    exact Nat.le_of_lt_succ h)
  have h_eval : aeval pb.gen P.det = M.det := by
    rw [AlgHom.map_det]
    congr 1
    ext i j
    exact representative_eval pb (M i j)
  rw [← h_eval, project_interpolate (constantCoord pb) pb.gen node hn P.det hp]
  apply Finset.sum_congr rfl
  intro t _
  congr 1
  exact (evalRingHom (node t)).map_det P

#print axioms determinant_descent

end HeilbronnNorm
