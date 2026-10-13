import PairedNorm

/-! Homogeneous coordinates and the nonzero criterion for distinct labels. -/

open Finset Polynomial Equiv

namespace HeilbronnPaired
open HeilbronnNorm

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

noncomputable def pairPolynomial (pb : PowerBasis F K) (a b : K ≃ₐ[F] K)
    (t : PairTerm) : MvPolynomial (Variables pb) K :=
  ∑ i : Row, ∑ r : Row,
    MvPolynomial.C (signs t.2 i * HeilbronnRankFive.coefficient t.1 i r : K) *
      (conjugateLinear pb a r * conjugateLinear pb b i)

lemma pairPolynomial_homogeneous (pb : PowerBasis F K) (a b : K ≃ₐ[F] K)
    (t : PairTerm) : (pairPolynomial pb a b t).IsHomogeneous 2 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  apply MvPolynomial.IsHomogeneous.sum
  intro r _
  exact ((conjugateLinear_homogeneous pb a r).mul
    (conjugateLinear_homogeneous pb b i)).C_mul _

lemma pairPolynomial_eval (pb : PowerBasis F K) (a b : K ≃ₐ[F] K)
    (t : PairTerm) (z : Variables pb → F) :
    MvPolynomial.eval (fun s => algebraMap F K (z s)) (pairPolynomial pb a b t) =
      pairForm t (fun r => a (labelCoordinate pb r z)) (fun r => b (labelCoordinate pb r z)) := by
  simp [pairPolynomial, pairForm, MvPolynomial.eval_sum, conjugateLinear_eval, mul_assoc]

noncomputable def coordinatePolynomial (pb : PowerBasis F K)
    (a : Slot ≃ (K ≃ₐ[F] K)) (w : Pattern) (i : Row) : MvPolynomial (Variables pb) K :=
  conjugateLinear pb (a (.inl ())) i * ∏ v : Fin 6,
    pairPolynomial pb (a (.inr (v, 0))) (a (.inr (v, 1))) (w v)

lemma coordinatePolynomial_homogeneous (pb : PowerBasis F K)
    (a : Slot ≃ (K ≃ₐ[F] K)) (w : Pattern) (i : Row) :
    (coordinatePolynomial pb a w i).IsHomogeneous 13 := by
  have hp := MvPolynomial.IsHomogeneous.prod univ
    (fun v : Fin 6 => pairPolynomial pb (a (.inr (v, 0))) (a (.inr (v, 1))) (w v))
    (fun _ => 2) (fun _ _ => pairPolynomial_homogeneous _ _ _ _)
  simpa [coordinatePolynomial] using (conjugateLinear_homogeneous pb (a (.inl ())) i).mul hp

lemma coordinatePolynomial_eval (pb : PowerBasis F K)
    (a : Slot ≃ (K ≃ₐ[F] K)) (w : Pattern) (i : Row) (z : Variables pb → F) :
    MvPolynomial.eval (fun s => algebraMap F K (z s)) (coordinatePolynomial pb a w i) =
      coordinate a (labelCoordinate pb) w i z := by
  simp only [coordinatePolynomial, MvPolynomial.eval_mul, MvPolynomial.eval_prod,
    conjugateLinear_eval, pairPolynomial_eval, coordinate]

noncomputable def descendedPolynomial (pb : PowerBasis F K) (node : Fin 25 → F)
    (a : Slot ≃ (K ≃ₐ[F] K)) (q : Term) (i : Row) : MvPolynomial (Variables pb) F :=
  MvPolynomial.C (if i = 0 then ((4 : F) ^ 6)⁻¹ else 1) *
    projectPolynomial (bilinearRow pb node q.2 i) (coordinatePolynomial pb a q.1 i)

lemma descendedPolynomial_homogeneous (pb : PowerBasis F K) (node : Fin 25 → F)
    (a : Slot ≃ (K ≃ₐ[F] K)) (q : Term) (i : Row) :
    (descendedPolynomial pb node a q i).IsHomogeneous 13 :=
  (projectPolynomial_homogeneous _ _ (coordinatePolynomial_homogeneous pb a q.1 i)).C_mul _

lemma descendedPolynomial_eval (pb : PowerBasis F K) (node : Fin 25 → F)
    (a : Slot ≃ (K ≃ₐ[F] K)) (q : Term) (i : Row) (z : Variables pb → F) :
    MvPolynomial.eval z (descendedPolynomial pb node a q i) =
      descendedCoordinate pb node a (labelCoordinate pb) q i z := by
  simp only [descendedPolynomial, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    projectPolynomial_eval, coordinatePolynomial_eval, descendedCoordinate]

theorem finite_field_polynomials [Fintype F] [Finite K] [FiniteDimensional F K]
    (hd : FiniteDimensional.finrank F K = 13) (h4 : (4 : F) ≠ 0)
    (hF : 25 ≤ Fintype.card F) :
    ∃ pb : PowerBasis F K, pb.dim = 13 ∧
      ∃ f : Fin 1600000000 → Row → MvPolynomial (Variables pb) F,
        (∀ q i, (f q i).IsHomogeneous 13) ∧
        ∀ x : Row → (Variables pb → F),
          Algebra.norm F (Matrix.det (fun i j => labelCoordinate pb i (x j))) =
            ∑ q, Matrix.det (fun i j => MvPolynomial.eval (x j) (f q i)) := by
  classical
  let pb := Field.powerBasisOfFiniteOfSeparable F K
  have hp : pb.dim = 13 := pb.finrank.symm.trans hd
  let a : Slot ≃ (K ≃ₐ[F] K) := Fintype.equivOfCardEq
    (slot_card.trans ((IsGalois.card_aut_eq_finrank F K).trans hd).symm)
  obtain ⟨node⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin 25) ≤ Fintype.card F by simpa using hF)
  let e : Fin 1600000000 ≃ Term := (Fintype.equivFinOfCardEq term_card).symm
  refine ⟨pb, hp, fun q => descendedPolynomial pb node a (e q), ?_, ?_⟩
  · intro q i
    exact descendedPolynomial_homogeneous pb node a (e q) i
  · intro x
    simp_rw [descendedPolynomial_eval]
    rw [norm_decomposition pb hp h4 node node.injective a (labelCoordinate pb) x]
    exact (e.sum_comp _).symm

theorem prime_field_labels (p : ℕ) [Fact p.Prime] (hp : 37 ≤ p) :
    ∃ f : Fin 1600000000 → Row → GaloisField p 13 → ZMod p,
      ∀ x : Row → GaloisField p 13,
        (Algebra.norm (ZMod p) (Matrix.det (fun i j : Row => x j ^ (i : ℕ))) =
          ∑ q, Matrix.det (fun i j => f q i (x j))) ∧
        ((∑ q, Matrix.det (fun i j => f q i (x j))) ≠ 0 ↔ Function.Injective x) := by
  classical
  have h4 : (4 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 4 := (ZMod.natCast_zmod_eq_zero_iff_dvd 4 p).mp h
    have := Nat.le_of_dvd (by decide : 0 < 4) hdvd
    omega
  obtain ⟨f, hf⟩ := finite_field_norm (GaloisField.finrank p (by decide)) h4
    (by simpa only [ZMod.card] using (show 25 ≤ p by omega))
    (fun (i : Row) (x : GaloisField p 13) => x ^ (i : ℕ))
  refine ⟨f, fun x => ⟨hf x, ?_⟩⟩
  rw [← hf x, Algebra.norm_ne_zero_iff]
  change (Matrix.vandermonde x).transpose.det ≠ 0 ↔ Function.Injective x
  rw [Matrix.det_transpose]
  exact Matrix.det_vandermonde_ne_zero_iff

#print axioms finite_field_polynomials
#print axioms prime_field_labels

end HeilbronnPaired
