import FrobeniusDescent

/-! The orbit-averaged norm identity retains homogeneous degree-thirteen
    coordinates and the obstruction for three distinct finite-field labels. -/

open Finset Polynomial Equiv

namespace HeilbronnFrobenius
open HeilbronnNorm

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

noncomputable def patternPolynomial (pb : PowerBasis F K)
    (w : Pattern (Gal (F := F) (K := K))) (i : Row) : MvPolynomial (Variables pb) K :=
  ∏ a : Gal, conjugateLinear pb a (w.1 a i)

lemma patternPolynomial_homogeneous (hc : Fintype.card (Gal (F := F) (K := K)) = 13)
    (pb : PowerBasis F K) (w : Pattern (Gal (F := F) (K := K))) (i : Row) :
    (patternPolynomial pb w i).IsHomogeneous 13 := by
  have hp := MvPolynomial.IsHomogeneous.prod Finset.univ
    (fun a : Gal (F := F) (K := K) => conjugateLinear pb a (w.1 a i)) (fun _ => 1)
    (fun _ _ => conjugateLinear_homogeneous _ _ _)
  simpa [patternPolynomial, hc] using hp

lemma patternPolynomial_eval (pb : PowerBasis F K)
    (w : Pattern (Gal (F := F) (K := K))) (i : Row) (z : Variables pb → F) :
    MvPolynomial.eval (fun s => algebraMap F K (z s)) (patternPolynomial pb w i) =
      patternCoordinate (labelCoordinate pb) w i z := by
  simp only [patternPolynomial, MvPolynomial.eval_prod, conjugateLinear_eval, patternCoordinate]

noncomputable def tracePolynomial (pb : PowerBasis F K) (node : Fin 25 → F)
    (q : TraceTerm (F := F) (K := K)) (i : Row) : MvPolynomial (Variables pb) F :=
  MvPolynomial.C (if i = 0 then classWeight q.1 else 1) *
    projectPolynomial (projectedRow (averagedCoord pb) pb node q.2 i)
      (patternPolynomial pb q.1.out' i)

lemma tracePolynomial_homogeneous (hc : Fintype.card (Gal (F := F) (K := K)) = 13)
    (pb : PowerBasis F K) (node : Fin 25 → F)
    (q : TraceTerm (F := F) (K := K)) (i : Row) :
    (tracePolynomial pb node q i).IsHomogeneous 13 :=
  (projectPolynomial_homogeneous _ _ (patternPolynomial_homogeneous hc pb q.1.out' i)).C_mul _

lemma tracePolynomial_eval (pb : PowerBasis F K) (node : Fin 25 → F)
    (q : TraceTerm (F := F) (K := K)) (i : Row) (z : Variables pb → F) :
    MvPolynomial.eval z (tracePolynomial pb node q i) =
      traceCoordinate pb node (labelCoordinate pb) q i z := by
  simp only [tracePolynomial, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    projectPolynomial_eval, patternPolynomial_eval, traceCoordinate]

theorem finite_field_trace_polynomials [Fintype F] [Finite K]
    (hd : FiniteDimensional.finrank F K = 13) (h13 : (13 : F) ≠ 0)
    (hF : 25 ≤ Fintype.card F) :
    ∃ pb : PowerBasis F K, pb.dim = 13 ∧
      ∃ f : Fin 4186119900 → Row → MvPolynomial (Variables pb) F,
        (∀ q i, (f q i).IsHomogeneous 13) ∧
        ∀ x : Row → (Variables pb → F),
          Algebra.norm F (Matrix.det (fun i j => labelCoordinate pb i (x j))) =
            ∑ q, Matrix.det (fun i j => MvPolynomial.eval (x j) (f q i)) := by
  classical
  let pb := Field.powerBasisOfFiniteOfSeparable F K
  have hp : pb.dim = 13 := pb.finrank.symm.trans hd
  have hc : Fintype.card (Gal (F := F) (K := K)) = 13 :=
    (IsGalois.card_aut_eq_finrank F K).trans hd
  obtain ⟨node⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin 25) ≤ Fintype.card F by simpa using hF)
  let e : Fin 4186119900 ≃ TraceTerm (F := F) (K := K) :=
    (Fintype.equivFinOfCardEq (trace_term_card hc)).symm
  refine ⟨pb, hp, fun q => tracePolynomial pb node (e q), ?_, ?_⟩
  · intro q i
    exact tracePolynomial_homogeneous hc pb node (e q) i
  · intro x
    simp_rw [tracePolynomial_eval]
    rw [trace_norm_decomposition pb hp h13 node node.injective (labelCoordinate pb) x]
    exact (e.sum_comp _).symm

theorem prime_field_trace_labels (p : ℕ) [Fact p.Prime] (hp : 37 ≤ p) :
    ∃ f : Fin 4186119900 → Row → GaloisField p 13 → ZMod p,
      ∀ x : Row → GaloisField p 13,
        (Algebra.norm (ZMod p) (Matrix.det (fun i j : Row => x j ^ (i : ℕ))) =
          ∑ q, Matrix.det (fun i j => f q i (x j))) ∧
        ((∑ q, Matrix.det (fun i j => f q i (x j))) ≠ 0 ↔ Function.Injective x) := by
  classical
  have h13 : (13 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 13 := (ZMod.natCast_zmod_eq_zero_iff_dvd 13 p).mp h
    have := Nat.le_of_dvd (by decide : 0 < 13) hdvd
    omega
  obtain ⟨f, hf⟩ := finite_field_trace_norm (GaloisField.finrank p (by decide)) h13
    (by simpa only [ZMod.card] using (show 25 ≤ p by omega))
    (fun (i : Row) (x : GaloisField p 13) => x ^ (i : ℕ))
  refine ⟨f, fun x => ⟨hf x, ?_⟩⟩
  rw [← hf x, Algebra.norm_ne_zero_iff]
  change (Matrix.vandermonde x).transpose.det ≠ 0 ↔ Function.Injective x
  rw [Matrix.det_transpose]
  exact Matrix.det_vandermonde_ne_zero_iff

#print axioms finite_field_trace_polynomials
#print axioms prime_field_trace_labels

end HeilbronnFrobenius
