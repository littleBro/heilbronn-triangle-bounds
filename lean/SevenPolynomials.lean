import SevenNorm
import EighteenPolynomials

/-! Homogeneous coordinates and the nonzero criterion for distinct labels. -/

open Finset Polynomial Equiv

namespace HeilbronnSeven
open HeilbronnEighteen (PairTerm pairForm coefficients rowIndex)
open HeilbronnNorm

variable {F K : Type*} [Field F] [Field K] [Algebra F K]
variable (u : K)

noncomputable def pairPolynomial (pb : PowerBasis F K) (a b : K ≃ₐ[F] K)
    (t : PairTerm) : MvPolynomial (Variables pb) K :=
  ∑ i : Row, MvPolynomial.C (coefficients u t.1 t.2 i) *
      (conjugateLinear pb a (rowIndex t.1 i) * conjugateLinear pb b i)

lemma pairPolynomial_homogeneous (pb : PowerBasis F K) (a b : K ≃ₐ[F] K)
    (t : PairTerm) : (pairPolynomial u pb a b t).IsHomogeneous 2 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  exact ((conjugateLinear_homogeneous pb a (rowIndex t.1 i)).mul
    (conjugateLinear_homogeneous pb b i)).C_mul _

lemma pairPolynomial_eval (pb : PowerBasis F K) (a b : K ≃ₐ[F] K)
    (t : PairTerm) (z : Variables pb → F) :
    MvPolynomial.eval (fun s => algebraMap F K (z s)) (pairPolynomial u pb a b t) =
      pairForm u t (fun r => a (labelCoordinate pb r z)) (fun r => b (labelCoordinate pb r z)) := by
  simp [pairPolynomial, pairForm, MvPolynomial.eval_sum, conjugateLinear_eval, mul_assoc]

noncomputable def coordinatePolynomial (pb : PowerBasis F K)
    (a : Slot ≃ (K ≃ₐ[F] K)) (w : Pattern) (i : Row) : MvPolynomial (Variables pb) K :=
  conjugateLinear pb (a (.inl ())) i * ∏ v : Fin 3,
    pairPolynomial u pb (a (.inr (v, 0))) (a (.inr (v, 1))) (w v)

lemma coordinatePolynomial_homogeneous (pb : PowerBasis F K)
    (a : Slot ≃ (K ≃ₐ[F] K)) (w : Pattern) (i : Row) :
    (coordinatePolynomial u pb a w i).IsHomogeneous 7 := by
  have hp := MvPolynomial.IsHomogeneous.prod univ
    (fun v : Fin 3 => pairPolynomial u pb (a (.inr (v, 0))) (a (.inr (v, 1))) (w v))
    (fun _ => 2) (fun _ _ => pairPolynomial_homogeneous u _ _ _ _)
  simpa [coordinatePolynomial] using (conjugateLinear_homogeneous pb (a (.inl ())) i).mul hp

lemma coordinatePolynomial_eval (pb : PowerBasis F K)
    (a : Slot ≃ (K ≃ₐ[F] K)) (w : Pattern) (i : Row) (z : Variables pb → F) :
    MvPolynomial.eval (fun s => algebraMap F K (z s)) (coordinatePolynomial u pb a w i) =
      coordinate u a (labelCoordinate pb) w i z := by
  simp only [coordinatePolynomial, MvPolynomial.eval_mul, MvPolynomial.eval_prod,
    conjugateLinear_eval, pairPolynomial_eval, coordinate]

noncomputable def descendedPolynomial (pb : PowerBasis F K) (node : Fin 13 → F)
    (a : Slot ≃ (K ≃ₐ[F] K)) (q : Term) (i : Row) : MvPolynomial (Variables pb) F :=
  MvPolynomial.C (if i = 0 then ((3 : F) ^ 3)⁻¹ else 1) *
    projectPolynomial (bilinearRow pb node q.2 i) (coordinatePolynomial u pb a q.1 i)

lemma descendedPolynomial_homogeneous (pb : PowerBasis F K) (node : Fin 13 → F)
    (a : Slot ≃ (K ≃ₐ[F] K)) (q : Term) (i : Row) :
    (descendedPolynomial u pb node a q i).IsHomogeneous 7 :=
  (projectPolynomial_homogeneous _ _ (coordinatePolynomial_homogeneous u pb a q.1 i)).C_mul _

lemma descendedPolynomial_eval (pb : PowerBasis F K) (node : Fin 13 → F)
    (a : Slot ≃ (K ≃ₐ[F] K)) (q : Term) (i : Row) (z : Variables pb → F) :
    MvPolynomial.eval z (descendedPolynomial u pb node a q i) =
      descendedCoordinate u pb node a (labelCoordinate pb) q i z := by
  simp only [descendedPolynomial, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    projectPolynomial_eval, coordinatePolynomial_eval, descendedCoordinate]

theorem finite_field_polynomials [Fintype F] [Finite K] [FiniteDimensional F K]
    (hd : FiniteDimensional.finrank F K = 7) (hu : u ^ 2 - u + 1 = 0) (h3 : (3 : F) ≠ 0)
    (hF : 13 ≤ Fintype.card F) :
    ∃ pb : PowerBasis F K, pb.dim = 7 ∧
      ∃ f : Fin 75816 → Row → MvPolynomial (Variables pb) F,
        (∀ q i, (f q i).IsHomogeneous 7) ∧
        ∀ x : Row → (Variables pb → F),
          Algebra.norm F (Matrix.det (fun i j => labelCoordinate pb i (x j))) =
            ∑ q, Matrix.det (fun i j => MvPolynomial.eval (x j) (f q i)) := by
  classical
  let pb := Field.powerBasisOfFiniteOfSeparable F K
  have hp : pb.dim = 7 := pb.finrank.symm.trans hd
  let a : Slot ≃ (K ≃ₐ[F] K) := Fintype.equivOfCardEq
    (slot_card.trans ((IsGalois.card_aut_eq_finrank F K).trans hd).symm)
  obtain ⟨node⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin 13) ≤ Fintype.card F by simpa using hF)
  let e : Fin 75816 ≃ Term := (Fintype.equivFinOfCardEq term_card).symm
  refine ⟨pb, hp, fun q => descendedPolynomial u pb node a (e q), ?_, ?_⟩
  · intro q i
    exact descendedPolynomial_homogeneous u pb node a (e q) i
  · intro x
    simp_rw [descendedPolynomial_eval]
    rw [norm_decomposition u pb hp h3 node node.injective hu a (labelCoordinate pb) x]
    exact (e.sum_comp _).symm

theorem prime_field_labels (p : ℕ) [Fact p.Prime] (hp : 37 ≤ p) (hp3 : p % 3 = 1) :
    ∃ f : Fin 75816 → Row → GaloisField p 7 → ZMod p,
      ∀ x : Row → GaloisField p 7,
        (Algebra.norm (ZMod p) (Matrix.det (fun i j : Row => x j ^ (i : ℕ))) =
          ∑ q, Matrix.det (fun i j => f q i (x j))) ∧
        ((∑ q, Matrix.det (fun i j => f q i (x j))) ≠ 0 ↔ Function.Injective x) := by
  classical
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 3 := (ZMod.natCast_zmod_eq_zero_iff_dvd 3 p).mp h
    have := Nat.le_of_dvd (by decide : 0 < 3) hdvd
    omega
  obtain ⟨v, hv⟩ := HeilbronnEighteen.root_exists p hp3
  let u := algebraMap (ZMod p) (GaloisField p 7) v
  have hu : u ^ 2 - u + 1 = 0 := by
    simpa only [map_add, map_sub, map_pow, map_one, map_zero] using
      congrArg (algebraMap (ZMod p) (GaloisField p 7)) hv
  obtain ⟨f, hf⟩ := finite_field_norm u (GaloisField.finrank p (by decide)) hu h3
    (by simpa only [ZMod.card] using (show 13 ≤ p by omega))
    (fun (i : Row) (x : GaloisField p 7) => x ^ (i : ℕ))
  refine ⟨f, fun x => ⟨hf x, ?_⟩⟩
  rw [← hf x, Algebra.norm_ne_zero_iff]
  change (Matrix.vandermonde x).transpose.det ≠ 0 ↔ Function.Injective x
  rw [Matrix.det_transpose]
  exact Matrix.det_vandermonde_ne_zero_iff

#print axioms finite_field_polynomials
#print axioms prime_field_labels

end HeilbronnSeven
