import NormDescent
import Mathlib.RingTheory.Norm.Basic
import Mathlib.FieldTheory.Finite.GaloisField

/-! The full functional norm decomposition for degree-thirteen finite-field
    extensions. Each coordinate depends on one label, uniformly for all triples.
    The norm here is Mathlib's field norm, not an assumed product formula. -/

open Finset Polynomial Equiv

namespace HeilbronnNorm

abbrev Term := Orbit × Fin 37

theorem term_card : Fintype.card Term = 37 * 6 ^ 12 := by
  rw [Fintype.card_prod, orbit_card, Fintype.card_fin, Nat.mul_comm]

variable {F K X : Type*} [Field F] [Field K] [Algebra F K]

lemma map_signR (p : Equiv.Perm Row) :
    algebraMap F K (signR p) = signR p := by simp [signR]

noncomputable def orbitSign (ρ : Orbit) : F := ∏ v, signR (ρ v)

noncomputable def orbitCoordinate (a : Fin 13 ≃ (K ≃ₐ[F] K))
    (g : Row → X → K) (ρ : Orbit) (i : Row) (x : X) : K :=
  a 0 (g i x) * ∏ v : Fin 12, a v.succ (g (ρ v i) x)

theorem norm_orbit_expansion [FiniteDimensional F K] [IsGalois F K]
    (a : Fin 13 ≃ (K ≃ₐ[F] K)) (g : Row → X → K) (x : Row → X) :
    algebraMap F K (Algebra.norm F (Matrix.det (fun i j => g i (x j)))) =
      ∑ ρ : Orbit, algebraMap F K (orbitSign ρ) *
        Matrix.det (fun i j => orbitCoordinate a g ρ i (x j)) := by
  classical
  rw [Algebra.norm_eq_prod_automorphisms, ← a.prod_comp, Fin.prod_univ_succ]
  simp only [AlgEquiv.map_det]
  simpa only [orbitCoordinate, orbitSign, map_prod, map_signR,
    RingHom.mapMatrix_apply] using
    determinant_product_compression
      (fun i j => a 0 (g i (x j)))
      (fun v i j => a v.succ (g i (x j)))

noncomputable def weight (pb : PowerBasis F K) (node : Fin 37 → F) (t : Fin 37) : F :=
  constantCoord pb (aeval pb.gen (Lagrange.basis univ node t))

noncomputable def descendedCoordinate (pb : PowerBasis F K) (node : Fin 37 → F)
    (a : Fin 13 ≃ (K ≃ₐ[F] K)) (g : Row → X → K)
    (q : Term) (i : Row) (x : X) : F :=
  (if i = 0 then orbitSign q.1 * weight pb node q.2 else 1) *
    (representative pb (orbitCoordinate a g q.1 i x)).eval (node q.2)

lemma descended_determinant (pb : PowerBasis F K) (node : Fin 37 → F)
    (a : Fin 13 ≃ (K ≃ₐ[F] K)) (g : Row → X → K)
    (q : Term) (x : Row → X) :
    Matrix.det (fun i j => descendedCoordinate pb node a g q i (x j)) =
      (orbitSign q.1 * weight pb node q.2) * Matrix.det
        (fun i j => (representative pb (orbitCoordinate a g q.1 i (x j))).eval (node q.2)) := by
  classical
  unfold descendedCoordinate
  simpa [Row, Fin.prod_univ_succ] using
    Matrix.det_mul_column
      (fun i : Row => if i = 0 then orbitSign q.1 * weight pb node q.2 else 1)
      (fun i j => (representative pb (orbitCoordinate a g q.1 i (x j))).eval (node q.2))

/-- Uniform separation of all label triples into exactly `37 * 6^12` determinants. -/
theorem norm_decomposition [FiniteDimensional F K] [IsGalois F K]
    (pb : PowerBasis F K) (hd : pb.dim = 13)
    (node : Fin 37 → F) (hn : Function.Injective node)
    (a : Fin 13 ≃ (K ≃ₐ[F] K)) (g : Row → X → K) (x : Row → X) :
    Algebra.norm F (Matrix.det (fun i j => g i (x j))) =
      ∑ q : Term, Matrix.det (fun i j => descendedCoordinate pb node a g q i (x j)) := by
  classical
  rw [← constantCoord_algebraMap pb (Algebra.norm F (Matrix.det (fun i j => g i (x j)))),
    norm_orbit_expansion a g x]
  simp only [map_sum, ← Algebra.smul_def, map_smul, smul_eq_mul]
  simp_rw [determinant_descent pb hd node hn]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ρ _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [descended_determinant]
  exact (mul_assoc _ _ _).symm

/-- All algebraic hypotheses are discharged for any finite extension field
    of degree thirteen over a base field with at least thirty-seven elements. -/
theorem finite_field_norm_decomposition [Fintype F] [Finite K]
    [FiniteDimensional F K] (hd : FiniteDimensional.finrank F K = 13)
    (hF : 37 ≤ Fintype.card F) (g : Row → X → K) :
    ∃ f : Fin (37 * 6 ^ 12) → Row → X → F,
      ∀ x : Row → X, Algebra.norm F (Matrix.det (fun i j => g i (x j))) =
        ∑ q, Matrix.det (fun i j => f q i (x j)) := by
  classical
  let pb := Field.powerBasisOfFiniteOfSeparable F K
  have hp : pb.dim = 13 := pb.finrank.symm.trans hd
  let a : Fin 13 ≃ (K ≃ₐ[F] K) :=
    (Fintype.equivFinOfCardEq ((IsGalois.card_aut_eq_finrank F K).trans hd)).symm
  obtain ⟨node⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin 37) ≤ Fintype.card F by simpa using hF)
  let e : Fin (37 * 6 ^ 12) ≃ Term := (Fintype.equivFinOfCardEq term_card).symm
  refine ⟨fun q => descendedCoordinate pb node a g (e q), ?_⟩
  intro x
  rw [norm_decomposition pb hp node node.injective a g x]
  exact (e.sum_comp _).symm

#print axioms norm_orbit_expansion
#print axioms norm_decomposition
#print axioms finite_field_norm_decomposition

end HeilbronnNorm
