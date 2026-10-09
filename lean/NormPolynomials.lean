import NormAlgebra
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Homogeneous polynomial coordinates for the norm decomposition. -/

open Finset

namespace HeilbronnNorm

variable {F K σ : Type*} [Field F] [Field K] [Algebra F K]

noncomputable def projectPolynomial (ℓ : K →ₗ[F] F) :
    MvPolynomial σ K →ₗ[F] MvPolynomial σ F := Finsupp.mapRange.linearMap ℓ

lemma projectPolynomial_monomial (ℓ : K →ₗ[F] F) (d : σ →₀ ℕ) (c : K) :
    projectPolynomial ℓ (MvPolynomial.monomial d c) = MvPolynomial.monomial d (ℓ c) := by
  exact Finsupp.mapRange_single (hf := ℓ.map_zero)

lemma projectPolynomial_homogeneous (ℓ : K →ₗ[F] F)
    (P : MvPolynomial σ K) {n : ℕ} (hP : P.IsHomogeneous n) :
    (projectPolynomial ℓ P).IsHomogeneous n := by
  intro d hd
  apply hP
  intro h
  apply hd
  change ℓ (MvPolynomial.coeff d P) = 0
  rw [h, map_zero]

lemma projectPolynomial_eval (ℓ : K →ₗ[F] F) (P : MvPolynomial σ K) (z : σ → F) :
    MvPolynomial.eval z (projectPolynomial ℓ P) =
      ℓ (MvPolynomial.eval (fun s => algebraMap F K (z s)) P) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | h1 d c =>
    rw [projectPolynomial_monomial, MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
    simp only [Finsupp.prod, ← map_pow, ← map_prod]
    rw [mul_comm c, ← Algebra.smul_def, map_smul, smul_eq_mul]
    exact mul_comm _ _
  | h2 P Q hp hq => simp only [map_add, MvPolynomial.eval_add, hp, hq]

abbrev Variables (pb : PowerBasis F K) := Row × Fin pb.dim

noncomputable def labelCoordinate (pb : PowerBasis F K) (i : Row)
    (z : Variables pb → F) : K :=
  ∑ v, algebraMap F K (z (i, v)) * pb.basis v

noncomputable def conjugateLinear (pb : PowerBasis F K) (a : K ≃ₐ[F] K)
    (i : Row) : MvPolynomial (Variables pb) K :=
  ∑ v, MvPolynomial.C (a (pb.basis v)) * MvPolynomial.X (i, v)

lemma conjugateLinear_homogeneous (pb : PowerBasis F K) (a : K ≃ₐ[F] K) (i : Row) :
    (conjugateLinear pb a i).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro v _
  exact (MvPolynomial.isHomogeneous_X _ _).C_mul _

lemma conjugateLinear_eval (pb : PowerBasis F K) (a : K ≃ₐ[F] K)
    (i : Row) (z : Variables pb → F) :
    MvPolynomial.eval (fun s => algebraMap F K (z s)) (conjugateLinear pb a i) =
      a (labelCoordinate pb i z) := by
  simp [conjugateLinear, labelCoordinate, MvPolynomial.eval_sum, map_sum, map_mul,
    AlgEquiv.commutes, mul_comm]

noncomputable def orbitPolynomial (pb : PowerBasis F K)
    (a : Fin 13 ≃ (K ≃ₐ[F] K)) (ρ : Orbit) (i : Row) : MvPolynomial (Variables pb) K :=
  conjugateLinear pb (a 0) i * ∏ v : Fin 12, conjugateLinear pb (a v.succ) (ρ v i)

lemma orbitPolynomial_homogeneous (pb : PowerBasis F K)
    (a : Fin 13 ≃ (K ≃ₐ[F] K)) (ρ : Orbit) (i : Row) :
    (orbitPolynomial pb a ρ i).IsHomogeneous 13 := by
  have hp := MvPolynomial.IsHomogeneous.prod univ
    (fun v : Fin 12 => conjugateLinear pb (a v.succ) (ρ v i)) (fun _ => 1)
    (fun _ _ => conjugateLinear_homogeneous _ _ _)
  have := (conjugateLinear_homogeneous pb (a 0) i).mul hp
  simpa [orbitPolynomial] using this

lemma orbitPolynomial_eval (pb : PowerBasis F K)
    (a : Fin 13 ≃ (K ≃ₐ[F] K)) (ρ : Orbit) (i : Row) (z : Variables pb → F) :
    MvPolynomial.eval (fun s => algebraMap F K (z s)) (orbitPolynomial pb a ρ i) =
      orbitCoordinate a (labelCoordinate pb) ρ i z := by
  simp only [orbitPolynomial, MvPolynomial.eval_mul, MvPolynomial.eval_prod,
    conjugateLinear_eval, orbitCoordinate]

noncomputable def evaluationCoord (pb : PowerBasis F K) (t : F) : K →ₗ[F] F :=
  (Polynomial.aeval t).toLinearMap.comp (representative pb)

lemma evaluationCoord_apply (pb : PowerBasis F K) (t : F) (x : K) :
    evaluationCoord pb t x = (representative pb x).eval t := by
  simp [evaluationCoord, Polynomial.aeval_def]
  rfl

noncomputable def descendedPolynomial (pb : PowerBasis F K) (node : Fin 37 → F)
    (a : Fin 13 ≃ (K ≃ₐ[F] K)) (q : Term) (i : Row) : MvPolynomial (Variables pb) F :=
  MvPolynomial.C (if i = 0 then orbitSign q.1 * weight pb node q.2 else 1) *
    projectPolynomial (evaluationCoord pb (node q.2)) (orbitPolynomial pb a q.1 i)

theorem descendedPolynomial_homogeneous (pb : PowerBasis F K) (node : Fin 37 → F)
    (a : Fin 13 ≃ (K ≃ₐ[F] K)) (q : Term) (i : Row) :
    (descendedPolynomial pb node a q i).IsHomogeneous 13 :=
  (projectPolynomial_homogeneous _ _ (orbitPolynomial_homogeneous pb a q.1 i)).C_mul _

theorem descendedPolynomial_eval (pb : PowerBasis F K) (node : Fin 37 → F)
    (a : Fin 13 ≃ (K ≃ₐ[F] K)) (q : Term) (i : Row) (z : Variables pb → F) :
    MvPolynomial.eval z (descendedPolynomial pb node a q i) =
      descendedCoordinate pb node a (labelCoordinate pb) q i z := by
  simp only [descendedPolynomial, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    projectPolynomial_eval, orbitPolynomial_eval, evaluationCoord_apply, descendedCoordinate]

/-- Homogeneous degree-thirteen base-field polynomials, with the exact field-norm identity. -/
theorem polynomial_norm_decomposition [FiniteDimensional F K] [IsGalois F K]
    (pb : PowerBasis F K) (hd : pb.dim = 13)
    (node : Fin 37 → F) (hn : Function.Injective node)
    (a : Fin 13 ≃ (K ≃ₐ[F] K)) (x : Row → (Variables pb → F)) :
    (∀ q i, (descendedPolynomial pb node a q i).IsHomogeneous 13) ∧
    Algebra.norm F (Matrix.det (fun i j => labelCoordinate pb i (x j))) =
      ∑ q : Term, Matrix.det (fun i j => MvPolynomial.eval (x j)
        (descendedPolynomial pb node a q i)) := by
  refine ⟨descendedPolynomial_homogeneous pb node a, ?_⟩
  simp_rw [descendedPolynomial_eval]
  exact norm_decomposition pb hd node hn a (labelCoordinate pb) x

#print axioms polynomial_norm_decomposition

/-- The polynomial form requires no supplied basis, automorphisms, or interpolation data. -/
theorem finite_field_polynomial_norm_decomposition [Fintype F] [Finite K]
    [FiniteDimensional F K] (hd : FiniteDimensional.finrank F K = 13)
    (hF : 37 ≤ Fintype.card F) :
    ∃ pb : PowerBasis F K, pb.dim = 13 ∧
      ∃ f : Fin (37 * 6 ^ 12) → Row → MvPolynomial (Variables pb) F,
        (∀ q i, (f q i).IsHomogeneous 13) ∧
        ∀ x : Row → (Variables pb → F),
          Algebra.norm F (Matrix.det (fun i j => labelCoordinate pb i (x j))) =
            ∑ q, Matrix.det (fun i j => MvPolynomial.eval (x j) (f q i)) := by
  classical
  let pb := Field.powerBasisOfFiniteOfSeparable F K
  have hp : pb.dim = 13 := pb.finrank.symm.trans hd
  let a : Fin 13 ≃ (K ≃ₐ[F] K) :=
    (Fintype.equivFinOfCardEq ((IsGalois.card_aut_eq_finrank F K).trans hd)).symm
  obtain ⟨node⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin 37) ≤ Fintype.card F by simpa using hF)
  let e : Fin (37 * 6 ^ 12) ≃ Term := (Fintype.equivFinOfCardEq term_card).symm
  refine ⟨pb, hp, fun q => descendedPolynomial pb node a (e q), ?_, ?_⟩
  · intro q i
    exact descendedPolynomial_homogeneous pb node a (e q) i
  · intro x
    rw [(polynomial_norm_decomposition pb hp node node.injective a x).2]
    exact (e.sum_comp _).symm

#print axioms finite_field_polynomial_norm_decomposition

end HeilbronnNorm
