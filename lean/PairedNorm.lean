import PairedExpansion
import BilinearNorm

/-! Six pairs and one unpaired conjugate, followed by 25-node descent. -/

open Finset Polynomial Equiv

namespace HeilbronnPaired
open HeilbronnNorm

abbrev Slot := Unit ⊕ (Fin 6 × Fin 2)
abbrev Pattern := Fin 6 → PairTerm
abbrev Term := Pattern × Fin 25

theorem slot_card : Fintype.card Slot = 13 := by decide

theorem term_card : Fintype.card Term = 1600000000 := by
  simp only [Term, Pattern, PairTerm, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  norm_num

variable {F K X : Type*} [Field F] [Field K] [Algebra F K]

noncomputable def coordinate (a : Slot ≃ (K ≃ₐ[F] K))
    (g : Row → X → K) (w : Pattern) (i : Row) (x : X) : K :=
  a (.inl ()) (g i x) * ∏ v : Fin 6,
    pairForm (w v) (fun r => a (.inr (v, 0)) (g r x))
      (fun r => a (.inr (v, 1)) (g r x))

theorem norm_expansion [FiniteDimensional F K] [IsGalois F K]
    (a : Slot ≃ (K ≃ₐ[F] K)) (g : Row → X → K) (x : Row → X) :
    (4 : K) ^ 6 * algebraMap F K (Algebra.norm F (Matrix.det (fun i j => g i (x j)))) =
      ∑ w : Pattern, Matrix.det (fun i j => coordinate a g w i (x j)) := by
  classical
  rw [Algebra.norm_eq_prod_automorphisms, ← a.prod_comp]
  simp only [Fintype.prod_sum_type, Fintype.prod_unique, Fintype.sum_prod_type,
    Fintype.prod_prod_type, Fin.prod_univ_two, AlgEquiv.map_det, RingHom.mapMatrix_apply]
  simpa only [Fintype.card_fin, coordinate] using
    paired_product (fun i j => a (.inl ()) (g i (x j)))
      (fun v i j => a (.inr (v, 0)) (g i (x j)))
      (fun v i j => a (.inr (v, 1)) (g i (x j)))

noncomputable def descendedCoordinate (pb : PowerBasis F K) (node : Fin 25 → F)
    (a : Slot ≃ (K ≃ₐ[F] K)) (g : Row → X → K)
    (q : Term) (i : Row) (x : X) : F :=
  (if i = 0 then ((4 : F) ^ 6)⁻¹ else 1) *
    bilinearRow pb node q.2 i (coordinate a g q.1 i x)

lemma descended_determinant (pb : PowerBasis F K) (node : Fin 25 → F)
    (a : Slot ≃ (K ≃ₐ[F] K)) (g : Row → X → K) (q : Term) (x : Row → X) :
    Matrix.det (fun i j => descendedCoordinate pb node a g q i (x j)) =
      ((4 : F) ^ 6)⁻¹ * Matrix.det
        (fun i j => bilinearRow pb node q.2 i (coordinate a g q.1 i (x j))) := by
  unfold descendedCoordinate
  simpa [Row, Fin.prod_univ_succ] using
    Matrix.det_mul_column (fun i : Row => if i = 0 then ((4 : F) ^ 6)⁻¹ else 1)
      (fun i j => bilinearRow pb node q.2 i (coordinate a g q.1 i (x j)))

theorem norm_decomposition [FiniteDimensional F K] [IsGalois F K]
    (pb : PowerBasis F K) (hd : pb.dim = 13) (h4 : (4 : F) ≠ 0)
    (node : Fin 25 → F) (hn : Function.Injective node)
    (a : Slot ≃ (K ≃ₐ[F] K)) (g : Row → X → K) (x : Row → X) :
    Algebra.norm F (Matrix.det (fun i j => g i (x j))) =
      ∑ q : Term, Matrix.det (fun i j => descendedCoordinate pb node a g q i (x j)) := by
  classical
  have h := congrArg (constantCoord pb) (norm_expansion a g x)
  rw [show (4 : K) ^ 6 = algebraMap F K ((4 : F) ^ 6) by rw [map_pow, map_ofNat],
    ← Algebra.smul_def, map_smul, smul_eq_mul, constantCoord_algebraMap, map_sum] at h
  calc
    _ = ((4 : F) ^ 6)⁻¹ * ((4 : F) ^ 6 *
        Algebra.norm F (Matrix.det (fun i j => g i (x j)))) := by
      rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 6 h4), one_mul]
    _ = _ := by
      rw [h]
      simp_rw [bilinear_determinant_descent pb hd node hn]
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun t _ => (descended_determinant pb node a g (w, t) x).symm)

theorem finite_field_norm [Fintype F] [Finite K] [FiniteDimensional F K]
    (hd : FiniteDimensional.finrank F K = 13) (h4 : (4 : F) ≠ 0)
    (hF : 25 ≤ Fintype.card F) (g : Row → X → K) :
    ∃ f : Fin 1600000000 → Row → X → F,
      ∀ x : Row → X, Algebra.norm F (Matrix.det (fun i j => g i (x j))) =
        ∑ q, Matrix.det (fun i j => f q i (x j)) := by
  classical
  let pb := Field.powerBasisOfFiniteOfSeparable F K
  have hp : pb.dim = 13 := pb.finrank.symm.trans hd
  let a : Slot ≃ (K ≃ₐ[F] K) := Fintype.equivOfCardEq
    (slot_card.trans ((IsGalois.card_aut_eq_finrank F K).trans hd).symm)
  obtain ⟨node⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin 25) ≤ Fintype.card F by simpa using hF)
  let e : Fin 1600000000 ≃ Term := (Fintype.equivFinOfCardEq term_card).symm
  refine ⟨fun q => descendedCoordinate pb node a g (e q), ?_⟩
  intro x
  rw [norm_decomposition pb hp h4 node node.injective a g x]
  exact (e.sum_comp _).symm

#print axioms term_card
#print axioms norm_expansion
#print axioms norm_decomposition
#print axioms finite_field_norm

end HeilbronnPaired
