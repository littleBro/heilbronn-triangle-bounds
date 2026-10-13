import BilinearDescent
import NormVandermonde

/-! The twenty-five-node descent preserves the norm, homogeneous polynomial
    coordinates, and the obstruction for three distinct labels. -/

open Finset Polynomial Equiv

namespace HeilbronnNorm

abbrev BilinearTerm := Orbit × Fin 25

theorem bilinear_term_card : Fintype.card BilinearTerm = 25 * 6 ^ 12 := by
  rw [Fintype.card_prod, orbit_card, Fintype.card_fin, Nat.mul_comm]

variable {F K X : Type*} [Field F] [Field K] [Algebra F K]

noncomputable def bilinearCoordinate (pb : PowerBasis F K) (node : Fin 25 → F)
    (a : Fin 13 ≃ (K ≃ₐ[F] K)) (g : Row → X → K)
    (q : BilinearTerm) (i : Row) (x : X) : F :=
  (if i = 0 then orbitSign q.1 else 1) *
    bilinearRow pb node q.2 i (orbitCoordinate a g q.1 i x)

lemma bilinear_descended_determinant (pb : PowerBasis F K) (node : Fin 25 → F)
    (a : Fin 13 ≃ (K ≃ₐ[F] K)) (g : Row → X → K)
    (q : BilinearTerm) (x : Row → X) :
    Matrix.det (fun i j => bilinearCoordinate pb node a g q i (x j)) =
      orbitSign q.1 * Matrix.det
        (fun i j => bilinearRow pb node q.2 i (orbitCoordinate a g q.1 i (x j))) := by
  classical
  unfold bilinearCoordinate
  simpa [Row, Fin.prod_univ_succ] using
    Matrix.det_mul_column (fun i : Row => if i = 0 then orbitSign q.1 else 1)
      (fun i j => bilinearRow pb node q.2 i (orbitCoordinate a g q.1 i (x j)))

theorem bilinear_norm_decomposition [FiniteDimensional F K] [IsGalois F K]
    (pb : PowerBasis F K) (hd : pb.dim = 13)
    (node : Fin 25 → F) (hn : Function.Injective node)
    (a : Fin 13 ≃ (K ≃ₐ[F] K)) (g : Row → X → K) (x : Row → X) :
    Algebra.norm F (Matrix.det (fun i j => g i (x j))) =
      ∑ q : BilinearTerm, Matrix.det (fun i j => bilinearCoordinate pb node a g q i (x j)) := by
  classical
  rw [← constantCoord_algebraMap pb (Algebra.norm F (Matrix.det (fun i j => g i (x j)))),
    norm_orbit_expansion a g x]
  simp only [map_sum, ← Algebra.smul_def, map_smul, smul_eq_mul]
  simp_rw [bilinear_determinant_descent pb hd node hn]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ρ _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  exact (bilinear_descended_determinant pb node a g (ρ, t) x).symm

theorem finite_field_bilinear_norm [Fintype F] [Finite K]
    [FiniteDimensional F K] (hd : FiniteDimensional.finrank F K = 13)
    (hF : 25 ≤ Fintype.card F) (g : Row → X → K) :
    ∃ f : Fin (25 * 6 ^ 12) → Row → X → F,
      ∀ x : Row → X, Algebra.norm F (Matrix.det (fun i j => g i (x j))) =
        ∑ q, Matrix.det (fun i j => f q i (x j)) := by
  classical
  let pb := Field.powerBasisOfFiniteOfSeparable F K
  have hp : pb.dim = 13 := pb.finrank.symm.trans hd
  let a : Fin 13 ≃ (K ≃ₐ[F] K) :=
    (Fintype.equivFinOfCardEq ((IsGalois.card_aut_eq_finrank F K).trans hd)).symm
  obtain ⟨node⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin 25) ≤ Fintype.card F by simpa using hF)
  let e : Fin (25 * 6 ^ 12) ≃ BilinearTerm := (Fintype.equivFinOfCardEq bilinear_term_card).symm
  refine ⟨fun q => bilinearCoordinate pb node a g (e q), ?_⟩
  intro x
  rw [bilinear_norm_decomposition pb hp node node.injective a g x]
  exact (e.sum_comp _).symm

noncomputable def bilinearPolynomial (pb : PowerBasis F K) (node : Fin 25 → F)
    (a : Fin 13 ≃ (K ≃ₐ[F] K)) (q : BilinearTerm) (i : Row) : MvPolynomial (Variables pb) F :=
  MvPolynomial.C (if i = 0 then orbitSign q.1 else 1) *
    projectPolynomial (bilinearRow pb node q.2 i) (orbitPolynomial pb a q.1 i)

theorem bilinearPolynomial_homogeneous (pb : PowerBasis F K) (node : Fin 25 → F)
    (a : Fin 13 ≃ (K ≃ₐ[F] K)) (q : BilinearTerm) (i : Row) :
    (bilinearPolynomial pb node a q i).IsHomogeneous 13 :=
  (projectPolynomial_homogeneous _ _ (orbitPolynomial_homogeneous pb a q.1 i)).C_mul _

lemma bilinearPolynomial_eval (pb : PowerBasis F K) (node : Fin 25 → F)
    (a : Fin 13 ≃ (K ≃ₐ[F] K)) (q : BilinearTerm) (i : Row) (z : Variables pb → F) :
    MvPolynomial.eval z (bilinearPolynomial pb node a q i) =
      bilinearCoordinate pb node a (labelCoordinate pb) q i z := by
  simp only [bilinearPolynomial, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    projectPolynomial_eval, orbitPolynomial_eval, bilinearCoordinate]

theorem finite_field_bilinear_polynomials [Fintype F] [Finite K]
    [FiniteDimensional F K] (hd : FiniteDimensional.finrank F K = 13)
    (hF : 25 ≤ Fintype.card F) :
    ∃ pb : PowerBasis F K, pb.dim = 13 ∧
      ∃ f : Fin (25 * 6 ^ 12) → Row → MvPolynomial (Variables pb) F,
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
    (show Fintype.card (Fin 25) ≤ Fintype.card F by simpa using hF)
  let e : Fin (25 * 6 ^ 12) ≃ BilinearTerm := (Fintype.equivFinOfCardEq bilinear_term_card).symm
  refine ⟨pb, hp, fun q => bilinearPolynomial pb node a (e q), ?_, ?_⟩
  · intro q i
    exact bilinearPolynomial_homogeneous pb node a (e q) i
  · intro x
    simp_rw [bilinearPolynomial_eval]
    rw [bilinear_norm_decomposition pb hp node node.injective a (labelCoordinate pb) x]
    exact (e.sum_comp _).symm

theorem prime_field_bilinear_labels (p : ℕ) [Fact p.Prime] (hp : 25 ≤ p) :
    ∃ f : Fin (25 * 6 ^ 12) → Row → GaloisField p 13 → ZMod p,
      ∀ x : Row → GaloisField p 13,
        (Algebra.norm (ZMod p) (Matrix.det (fun i j : Row => x j ^ (i : ℕ))) =
          ∑ q, Matrix.det (fun i j => f q i (x j))) ∧
        ((∑ q, Matrix.det (fun i j => f q i (x j))) ≠ 0 ↔ Function.Injective x) := by
  classical
  obtain ⟨f, hf⟩ := finite_field_bilinear_norm (GaloisField.finrank p (by decide))
    (by simpa only [ZMod.card] using hp) (fun (i : Row) (x : GaloisField p 13) => x ^ (i : ℕ))
  refine ⟨f, fun x => ⟨hf x, ?_⟩⟩
  rw [← hf x, Algebra.norm_ne_zero_iff]
  change (Matrix.vandermonde x).transpose.det ≠ 0 ↔ Function.Injective x
  rw [Matrix.det_transpose]
  exact Matrix.det_vandermonde_ne_zero_iff

#print axioms bilinear_term_card
#print axioms bilinear_norm_decomposition
#print axioms finite_field_bilinear_norm
#print axioms finite_field_bilinear_polynomials
#print axioms prime_field_bilinear_labels

end HeilbronnNorm
