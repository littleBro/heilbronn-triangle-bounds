import NormAlgebra
import Mathlib.LinearAlgebra.Vandermonde

/-! The digit residue sum is nonzero exactly for triples of distinct labels. -/

namespace HeilbronnNorm

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

theorem finite_field_label_decomposition [Fintype F] [Finite K]
    [FiniteDimensional F K] (hd : FiniteDimensional.finrank F K = 13)
    (hF : 37 ≤ Fintype.card F) :
    ∃ f : Fin (37 * 6 ^ 12) → Row → K → F, ∀ x : Row → K,
      (Algebra.norm F (Matrix.det (fun i j : Row => x j ^ (i : ℕ))) =
        ∑ q, Matrix.det (fun i j => f q i (x j))) ∧
      ((∑ q, Matrix.det (fun i j => f q i (x j))) ≠ 0 ↔ Function.Injective x) := by
  classical
  obtain ⟨f, hf⟩ := finite_field_norm_decomposition hd hF (fun (i : Row) (x : K) => x ^ (i : ℕ))
  refine ⟨f, fun x => ⟨hf x, ?_⟩⟩
  rw [← hf x, Algebra.norm_ne_zero_iff]
  change (Matrix.vandermonde x).transpose.det ≠ 0 ↔ Function.Injective x
  rw [Matrix.det_transpose]
  exact Matrix.det_vandermonde_ne_zero_iff

#print axioms finite_field_label_decomposition

/-- The manuscript's fields exist for every prime at least thirty-seven. -/
theorem prime_field_label_decomposition (p : ℕ) [Fact p.Prime] (hp : 37 ≤ p) :
    ∃ f : Fin (37 * 6 ^ 12) → Row → GaloisField p 13 → ZMod p,
      ∀ x : Row → GaloisField p 13,
        (Algebra.norm (ZMod p) (Matrix.det (fun i j : Row => x j ^ (i : ℕ))) =
          ∑ q, Matrix.det (fun i j => f q i (x j))) ∧
        ((∑ q, Matrix.det (fun i j => f q i (x j))) ≠ 0 ↔ Function.Injective x) := by
  exact finite_field_label_decomposition (GaloisField.finrank p (by decide))
    (by simpa only [ZMod.card] using hp)

#print axioms prime_field_label_decomposition

end HeilbronnNorm
