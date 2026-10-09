import RankFiveExpansion
import RankFiveOrbits
import FrobeniusDescent

/-! Five-letter expansion, Galois averaging, and twenty-five-node descent.
    The factor 1/6 comes from antisymmetrization and cannot be omitted. -/

open Finset Equiv Polynomial

namespace HeilbronnRankFive
open HeilbronnNorm
open HeilbronnFrobenius (Gal averagedCoord averagedCoord_base averagedCoord_invariant
  projectedRow projected_determinant)

variable {F K X : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

omit [FiniteDimensional F K] in
lemma form_map (a : Gal (F := F) (K := K)) (t : Fin 5) (i : Row) (v : Row → K) :
    a (form t i v) = form t i (fun r => a (v r)) := by simp [form]

noncomputable def patternCoordinate (g : Row → X → K)
    (w : Pattern (Gal (F := F) (K := K))) (i : Row) (x : X) : K :=
  ∏ a : Gal, a (form (w.word a) i (fun r => g r x))

lemma patternCoordinate_rotate (a : Gal (F := F) (K := K)) (g : Row → X → K)
    (w : Pattern (Gal (F := F) (K := K))) (i : Row) (x : X) :
    patternCoordinate g (a • w) i x = a (patternCoordinate g w i x) := by
  classical
  simp only [patternCoordinate, map_prod, rotate_apply]
  apply Fintype.prod_equiv (Equiv.mulLeft a⁻¹)
  intro σ
  simp only [Equiv.coe_mulLeft, AlgEquiv.mul_apply]
  exact (a.apply_symm_apply _).symm

noncomputable def patternTerm (g : Row → X → K) (x : Row → X)
    (w : Pattern (Gal (F := F) (K := K))) : K :=
  Matrix.det (fun i j => patternCoordinate g w i (x j))

theorem patternTerm_rotate (a : Gal (F := F) (K := K)) (g : Row → X → K)
    (x : Row → X) (w : Pattern (Gal (F := F) (K := K))) :
    patternTerm g x (a • w) = a (patternTerm g x w) := by
  simp only [patternTerm, patternCoordinate_rotate]
  exact (a.map_det _).symm

theorem norm_pattern_sum [IsGalois F K]
    (hc : Fintype.card (Gal (F := F) (K := K)) = 13) (g : Row → X → K) (x : Row → X) :
    (6 : K) * algebraMap F K (Algebra.norm F (Matrix.det (fun i j => g i (x j)))) =
      ∑ w : Pattern (Gal (F := F) (K := K)), patternTerm g x w := by
  classical
  rw [Algebra.norm_eq_prod_automorphisms]
  simp only [AlgEquiv.map_det]
  have h := antisymmetrized_product hc (fun a : Gal (F := F) (K := K) =>
    (fun i j => a (g i (x j)) : Matrix Row Row K))
  change (6 : K) * (∏ a : Gal (F := F) (K := K), Matrix.det (fun i j => a (g i (x j)))) = _
  rw [h]
  symm
  apply Fintype.sum_equiv (patternEquiv _)
  intro w
  simp only [patternTerm, patternCoordinate, form_map, patternEquiv]
  rfl

noncomputable def classWeight (q : Classes (Gal (F := F) (K := K))) : F :=
  (6 : F)⁻¹ * (Fintype.card (MulAction.orbit (Gal (F := F) (K := K)) q.out') : F)

theorem norm_class_sum [IsGalois F K]
    (hc : Fintype.card (Gal (F := F) (K := K)) = 13) (h13 : (13 : F) ≠ 0)
    (h6 : (6 : F) ≠ 0) (pb : PowerBasis F K) (g : Row → X → K) (x : Row → X) :
    Algebra.norm F (Matrix.det (fun i j => g i (x j))) =
      ∑ q : Classes (Gal (F := F) (K := K)),
        classWeight q * averagedCoord pb (patternTerm g x q.out') := by
  classical
  have hs (z : K) : averagedCoord pb ((6 : K) * z) = 6 * averagedCoord pb z := by
    rw [show (6 : K) = algebraMap F K (6 : F) from (map_ofNat (algebraMap F K) 6).symm, ← Algebra.smul_def,
      map_smul, smul_eq_mul]
  have h := congrArg (averagedCoord pb) (norm_pattern_sum hc g x)
  rw [hs, averagedCoord_base hc h13, map_sum] at h
  have hi := invariant_sum (Gal (F := F) (K := K))
    (fun w => averagedCoord pb (patternTerm g x w))
    (fun a w => by dsimp only; rw [patternTerm_rotate, averagedCoord_invariant])
  rw [hi] at h
  calc
    _ = (6 : F)⁻¹ * (6 * Algebra.norm F (Matrix.det (fun i j => g i (x j)))) := by
      rw [← mul_assoc, inv_mul_cancel₀ h6, one_mul]
    _ = _ := by
      rw [h, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      exact (mul_assoc _ _ _).symm

abbrev TraceTerm := Classes (Gal (F := F) (K := K)) × Fin 25

theorem trace_term_card (hc : Fintype.card (Gal (F := F) (K := K)) = 13) :
    Fintype.card (TraceTerm (F := F) (K := K)) = 2347506125 := by
  rw [Fintype.card_prod, class_card _ hc, Fintype.card_fin]

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

theorem trace_norm_decomposition [IsGalois F K] (pb : PowerBasis F K) (hd : pb.dim = 13)
    (h13 : (13 : F) ≠ 0) (h6 : (6 : F) ≠ 0) (node : Fin 25 → F) (hn : Function.Injective node)
    (g : Row → X → K) (x : Row → X) :
    Algebra.norm F (Matrix.det (fun i j => g i (x j))) =
      ∑ q : TraceTerm (F := F) (K := K), Matrix.det (fun i j => traceCoordinate pb node g q i (x j)) := by
  classical
  have hc : Fintype.card (Gal (F := F) (K := K)) = 13 :=
    (IsGalois.card_aut_eq_finrank F K).trans (pb.finrank.trans hd)
  rw [norm_class_sum hc h13 h6 pb g x]
  simp_rw [patternTerm, projected_determinant _ pb hd node hn]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [trace_coordinate_det]

theorem finite_field_trace_norm [Fintype F] [Finite K]
    (hd : FiniteDimensional.finrank F K = 13) (h13 : (13 : F) ≠ 0) (h6 : (6 : F) ≠ 0)
    (hF : 25 ≤ Fintype.card F) (g : Row → X → K) :
    ∃ f : Fin 2347506125 → Row → X → F,
      ∀ x : Row → X, Algebra.norm F (Matrix.det (fun i j => g i (x j))) =
        ∑ q, Matrix.det (fun i j => f q i (x j)) := by
  classical
  let pb := Field.powerBasisOfFiniteOfSeparable F K
  have hp : pb.dim = 13 := pb.finrank.symm.trans hd
  have hc : Fintype.card (Gal (F := F) (K := K)) = 13 :=
    (IsGalois.card_aut_eq_finrank F K).trans hd
  obtain ⟨node⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin 25) ≤ Fintype.card F by simpa using hF)
  let e : Fin 2347506125 ≃ TraceTerm (F := F) (K := K) :=
    (Fintype.equivFinOfCardEq (trace_term_card hc)).symm
  refine ⟨fun q => traceCoordinate pb node g (e q), ?_⟩
  intro x
  rw [trace_norm_decomposition pb hp h13 h6 node node.injective g x]
  exact (e.sum_comp _).symm

#print axioms patternTerm_rotate
#print axioms norm_pattern_sum
#print axioms norm_class_sum
#print axioms trace_term_card
#print axioms trace_norm_decomposition
#print axioms finite_field_trace_norm

end HeilbronnRankFive
