import FiveTagged

/-! Column relabelling preserves the complete digit expectation. This justifies
placing the repeated label in the first two columns without a probabilistic gap. -/

namespace HeilbronnFive
namespace DigitModel
variable {k M : ℕ} (m : DigitModel k M)

def permute (σ : Equiv.Perm (Fin 3)) (hu : Nat.Coprime m.base (m.top (σ 0))) :
    DigitModel k M where
  base := m.base
  alphabet i := m.alphabet (σ i.1, i.2)
  alphabet_injective i := m.alphabet_injective (σ i.1, i.2)
  top c := m.top (σ c)
  top_unit := hu

def drawEquiv (σ : Equiv.Perm (Fin 3)) :
    Equiv.Perm ((Fin 3 × Fin k) → Fin M) where
  toFun x i := x (σ i.1, i.2)
  invFun x i := x (σ.symm i.1, i.2)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

theorem matrix_permute (σ : Equiv.Perm (Fin 3)) (hu) (second : Fin 3 → ℕ) (x) :
    (m.permute σ hu).matrix (fun c => second (σ c)) (drawEquiv σ x) =
      Matrix.submatrix (m.matrix second x) id σ := by
  funext row col
  simp only [matrix, permute, drawEquiv, Equiv.coe_fn_mk, entry, radix,
    Matrix.submatrix_apply, id_eq]

theorem minors_permute (σ : Equiv.Perm (Fin 3)) (hu) (second : Fin 3 → ℕ) (x) (j) :
    (m.permute σ hu).allMinors (fun c => second (σ c)) (drawEquiv σ x) j ↔
      m.allMinors second x j := by
  unfold allMinors
  rw [matrix_permute]
  simp only [permute, Matrix.submatrix_apply, id_eq]
  constructor
  · intro h s t c e
    simpa only [Equiv.apply_symm_apply] using h s t (σ.symm c) (σ.symm e)
  · intro h s t c e
    exact h s t (σ c) (σ e)

theorem minorExponent_permute (σ : Equiv.Perm (Fin 3)) (hu) (second : Fin 3 → ℕ) (x) :
    (m.permute σ hu).minorExponent (fun c => second (σ c)) (drawEquiv σ x) =
      m.minorExponent second x := by
  unfold minorExponent
  congr 1
  funext j
  exact propext (m.minors_permute σ hu second x j)

theorem small_integer_residue_neg (H P z : ℤ) :
    (∃ t : ℤ, H ∣ -z-t ∧ 2*|t| ≤ P) ↔ (∃ t : ℤ, H ∣ z-t ∧ 2*|t| ≤ P) := by
  constructor <;> rintro ⟨t,ht,hp⟩ <;> refine ⟨-t, ?_, by simpa only [abs_neg] using hp⟩
  · convert dvd_neg.mpr ht using 1 <;> ring
  · convert dvd_neg.mpr ht using 1 <;> ring

theorem smallResidue_permute (σ : Equiv.Perm (Fin 3)) (hu) (second : Fin 3 → ℕ) (x) :
    (m.permute σ hu).smallResidue (fun c => second (σ c)) (drawEquiv σ x) ↔
      m.smallResidue second x := by
  unfold smallResidue
  rw [matrix_permute, Matrix.det_permute']
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · simp only [hs, Units.val_one, Int.cast_one, one_mul, permute]
  · simp only [hs, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one,
      neg_one_mul, permute]
    exact small_integer_residue_neg _ _ _

theorem smallMoment_permute (σ : Equiv.Perm (Fin 3)) (hu) (second : Fin 3 → ℕ) :
    (m.permute σ hu).smallMoment (fun c => second (σ c)) = m.smallMoment second := by
  classical
  unfold smallMoment
  rw [← average_equiv (drawEquiv σ)]
  apply congrArg average
  funext x
  rw [m.minorExponent_permute σ hu second x]
  have he := m.smallResidue_permute σ hu second x
  by_cases hx : m.smallResidue second x
  · rw [if_pos (he.mpr hx), if_pos hx]
    rfl
  · have hn : ¬(m.permute σ hu).smallResidue (fun c => second (σ c)) (drawEquiv σ x) :=
      fun h => hx (he.mp h)
    simp only [hx, hn, if_false]

end DigitModel
#print axioms DigitModel.minorExponent_permute
#print axioms DigitModel.smallResidue_permute
#print axioms DigitModel.smallMoment_permute

end HeilbronnFive
