import FrobeniusNorm

/-! A uniform twenty-five-term descent for each Galois orbit. Keeping the
    singleton orbit in the same format avoids a special coordinate family. -/

open Finset Polynomial Equiv

namespace HeilbronnFrobenius
open HeilbronnNorm

variable {F K X : Type*} [Field F] [Field K] [Algebra F K]
  [FiniteDimensional F K]

noncomputable def projectedRow (ℓ : K →ₗ[F] F) (pb : PowerBasis F K) (node : Fin 25 → F)
    (t : Fin 25) (i : Row) : K →ₗ[F] F :=
  if i = 2 then ℓ.comp (LinearMap.mulLeft F (interpolationElement pb node t))
  else evaluationCoord pb (node t)

omit [FiniteDimensional F K] in
lemma projected_triple (ℓ : K →ₗ[F] F) (pb : PowerBasis F K) (hd : pb.dim = 13)
    (node : Fin 25 → F) (hn : Function.Injective node) (x y z : K) :
    ℓ (x * y * z) = ∑ t, (representative pb x).eval (node t) *
      (representative pb y).eval (node t) * ℓ (interpolationElement pb node t * z) := by
  rw [bilinear_interpolation pb hd node hn x y, Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [mul_assoc, ← Algebra.smul_def, map_smul, smul_eq_mul]

omit [FiniteDimensional F K] in
theorem projected_determinant (ℓ : K →ₗ[F] F) (pb : PowerBasis F K) (hd : pb.dim = 13)
    (node : Fin 25 → F) (hn : Function.Injective node) (M : Matrix Row Row K) :
    ℓ M.det = ∑ t, Matrix.det (fun i j => projectedRow ℓ pb node t i (M i j)) := by
  simp only [Row, Matrix.det_fin_three, map_sub, map_add, projected_triple ℓ pb hd node hn,
    projectedRow, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide,
    if_false, if_true, evaluationCoord_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]

theorem norm_class_sum [IsGalois F K]
    (hc : Fintype.card (Gal (F := F) (K := K)) = 13) (h13 : (13 : F) ≠ 0)
    (pb : PowerBasis F K) (g : Row → X → K) (x : Row → X) :
    Algebra.norm F (Matrix.det (fun i j => g i (x j))) =
      ∑ q : Classes (Gal (F := F) (K := K)),
        (Fintype.card (MulAction.orbit (Gal (F := F) (K := K)) q.out') : F) *
          averagedCoord pb (patternTerm g x q.out') := by
  classical
  rw [← averagedCoord_base hc h13 pb (Algebra.norm F (Matrix.det (fun i j => g i (x j)))),
    norm_pattern_sum hc g x, map_sum]
  apply invariant_sum
  intro a w
  rw [patternTerm_rotate hc, averagedCoord_invariant]

abbrev TraceTerm := Classes (Gal (F := F) (K := K)) × Fin 25

theorem trace_term_card (hc : Fintype.card (Gal (F := F) (K := K)) = 13) :
    Fintype.card (TraceTerm (F := F) (K := K)) = 4186119900 := by
  rw [Fintype.card_prod, class_card _ hc, Fintype.card_fin]

noncomputable def classWeight (q : Classes (Gal (F := F) (K := K))) : F :=
  (Fintype.card (MulAction.orbit (Gal (F := F) (K := K)) q.out') : F) * patternSign q.out'

noncomputable def traceCoordinate (pb : PowerBasis F K) (node : Fin 25 → F)
    (g : Row → X → K) (q : TraceTerm (F := F) (K := K)) (i : Row) (x : X) : F :=
  (if i = 0 then classWeight q.1 else 1) *
    projectedRow (averagedCoord pb) pb node q.2 i (patternCoordinate g q.1.out' i x)

lemma trace_coordinate_det (pb : PowerBasis F K) (node : Fin 25 → F)
    (g : Row → X → K) (q : TraceTerm (F := F) (K := K)) (x : Row → X) :
    Matrix.det (fun i j => traceCoordinate pb node g q i (x j)) =
      classWeight q.1 * Matrix.det (fun i j =>
        projectedRow (averagedCoord pb) pb node q.2 i (patternCoordinate g q.1.out' i (x j))) := by
  classical
  unfold traceCoordinate
  simpa [Row, Fin.prod_univ_succ] using
    Matrix.det_mul_column (fun i : Row => if i = 0 then classWeight q.1 else 1)
      (fun i j => projectedRow (averagedCoord pb) pb node q.2 i
        (patternCoordinate g q.1.out' i (x j)))

lemma project_patternTerm (pb : PowerBasis F K) (g : Row → X → K) (x : Row → X)
    (w : Pattern (Gal (F := F) (K := K))) :
    averagedCoord pb (patternTerm g x w) =
      (patternSign w : F) * averagedCoord pb (Matrix.det (fun i j => patternCoordinate g w i (x j))) := by
  have hs : (patternSign w : K) = algebraMap F K (patternSign w : F) := by
    simp [patternSign, signR]
  rw [patternTerm, hs, ← Algebra.smul_def, map_smul, smul_eq_mul]

theorem trace_norm_decomposition [IsGalois F K] (pb : PowerBasis F K) (hd : pb.dim = 13)
    (h13 : (13 : F) ≠ 0) (node : Fin 25 → F) (hn : Function.Injective node)
    (g : Row → X → K) (x : Row → X) :
    Algebra.norm F (Matrix.det (fun i j => g i (x j))) =
      ∑ q : TraceTerm (F := F) (K := K),
        Matrix.det (fun i j => traceCoordinate pb node g q i (x j)) := by
  classical
  have hc : Fintype.card (Gal (F := F) (K := K)) = 13 :=
    (IsGalois.card_aut_eq_finrank F K).trans (pb.finrank.trans hd)
  rw [norm_class_sum hc h13 pb g x]
  simp_rw [project_patternTerm, projected_determinant _ pb hd node hn]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [trace_coordinate_det]
  exact (mul_assoc _ _ _).symm

theorem finite_field_trace_norm [Fintype F] [Finite K]
    (hd : FiniteDimensional.finrank F K = 13) (h13 : (13 : F) ≠ 0)
    (hF : 25 ≤ Fintype.card F) (g : Row → X → K) :
    ∃ f : Fin 4186119900 → Row → X → F,
      ∀ x : Row → X, Algebra.norm F (Matrix.det (fun i j => g i (x j))) =
        ∑ q, Matrix.det (fun i j => f q i (x j)) := by
  classical
  let pb := Field.powerBasisOfFiniteOfSeparable F K
  have hp : pb.dim = 13 := pb.finrank.symm.trans hd
  have hc : Fintype.card (Gal (F := F) (K := K)) = 13 :=
    (IsGalois.card_aut_eq_finrank F K).trans hd
  obtain ⟨node⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin 25) ≤ Fintype.card F by simpa using hF)
  let e : Fin 4186119900 ≃ TraceTerm (F := F) (K := K) :=
    (Fintype.equivFinOfCardEq (trace_term_card hc)).symm
  refine ⟨fun q => traceCoordinate pb node g (e q), ?_⟩
  intro x
  rw [trace_norm_decomposition pb hp h13 node node.injective g x]
  exact (e.sum_comp _).symm

#print axioms projected_determinant
#print axioms norm_class_sum
#print axioms trace_term_card
#print axioms trace_norm_decomposition
#print axioms finite_field_trace_norm

end HeilbronnFrobenius
