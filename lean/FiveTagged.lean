import FiveCoefficientBounds
import FiveLabels

/-! The finite tagged probability theorem for the actual determinant residue.
The upstream geometric/orbit argument is not part of this theorem. -/

namespace HeilbronnFive
open Polynomial

theorem five_probability_scale {k r B : ℕ} (hk : 0 < k) (hr : 0 < r)
    (hB : B ≤ 80000*k^4*r^6) :
    0 < 400*k^2*r^3 ∧ (B : ℚ)/(400*(k : ℚ)^2*(r : ℚ)^3)^2 ≤ 1/2 := by
  constructor
  · positivity
  · have hkq : (0 : ℚ) < k := by exact_mod_cast hk
    have hrq : (0 : ℚ) < r := by exact_mod_cast hr
    apply (div_le_iff (by positivity : (0 : ℚ) < (400*(k : ℚ)^2*(r : ℚ)^3)^2)).mpr
    have h : (B : ℚ) ≤ 80000*(k : ℚ)^4*(r : ℚ)^6 := by exact_mod_cast hB
    convert h using 1 <;> ring

namespace DigitModel
variable {k M : ℕ} (m : DigitModel k M)

def smallResidue (second : Fin 3 → ℕ) (x : (Fin 3 × Fin k) → Fin M) : Prop :=
  ∃ t : ℤ, (m.base : ℤ)^k ∣ Matrix.det (m.matrix second x) - t ∧
    2*|t| ≤ (m.base : ℤ)^(k-1)

noncomputable def smallMoment (second : Fin 3 → ℕ) : ℚ := by
  classical
  exact average (fun x => if m.smallResidue second x
    then (m.base : ℚ)^(m.minorExponent second x) else 0)

theorem smallMoment_le_uniform (hM : 0 < M) (second : Fin 3 → ℕ)
    (hscale : (m.base : ℚ)/(M : ℚ)^2 ≤ 1/2) : m.smallMoment second ≤ 2 := by
  classical
  apply le_trans _ (m.actual_uniform_moment hM second hscale)
  unfold smallMoment
  apply average_mono
  intro x
  split_ifs <;> first | rfl | positivity

/-- `E[D 1_J] <= 2/M`, from tags, actual minors, residue-class alphabets,
and coefficient range bounds. No probability bound occurs among the premises. -/
theorem tagged_small_residue_moment (hM : 0 < M)
    (second : Fin 3 → ℕ) (A A' Q Q' : ℤ[X]) (a d r L : ℕ)
    (ha : a < d) (hk : 2*d ≤ k) (hrB : r ≤ m.base)
    (hA : ∀ i, i ≤ a → A.coeff i = A'.coeff i) (hA0 : A.coeff 0 = 1)
    (hQ : ∀ i, i < a → Q.coeff i = Q'.coeff i) (hne : Q.coeff a ≠ Q'.coeff a)
    (hQpos : 1 ≤ Q.coeff a) (hQ'pos : 1 ≤ Q'.coeff a)
    (hQle : Q.coeff a ≤ r) (hQ'le : Q'.coeff a ≤ r)
    (hAeval : A.eval (m.base : ℤ) = m.top 0)
    (hA'eval : A'.eval (m.base : ℤ) = m.top 2)
    (hQeval : Q.eval (m.base : ℤ) = second 0)
    (hQ'eval : Q'.eval (m.base : ℤ) = second 2)
    (htop : m.top 1 = m.top 0) (hsecond : second 1 = second 0)
    (hArange : ∀ i, i < k → |A.coeff i| ≤ r)
    (hA'range : ∀ i, i < k → |A'.coeff i| ≤ r)
    (hQrange : ∀ i, i < k → |Q.coeff i| ≤ r)
    (hQ'range : ∀ i, i < k → |Q'.coeff i| ≤ r)
    (hbottom : ∀ i x, (m.alphabet i x).val ≤ L)
    (hbase : 100*k^2*r^2*L < m.base)
    (hscale : (m.base : ℚ)/(M : ℚ)^2 ≤ 1/2) :
    m.smallMoment second ≤ 2/(M : ℚ) := by
  classical
  let P := fun x : (Fin 3 × Fin k) → Fin M =>
    !![A,A,A'; Q,Q,Q'; m.poly x 0,m.poly x 1,m.poly x 2]
  have hB : 0 < m.base := lt_of_le_of_lt (Nat.zero_le _) hbase
  have hbound (x) : ∀ row col i, i < k → |((P x) row col).coeff i| ≤
      (![r,r,L] : Fin 3 → ℕ) row := by
    intro row col i hi
    have hbot (c : Fin 3) : |(m.poly x c).coeff i| ≤ L := by
      have hh := digitPolynomial_coeff
        (fun p => ((m.alphabet (c,p) (x (c,p))).val : ℤ)) (⟨i,hi⟩ : Fin k)
      change |(digitPolynomial _).coeff i| ≤ _
      rw [hh, abs_of_nonneg (by positivity)]
      exact_mod_cast hbottom (c,⟨i,hi⟩) (x (c,⟨i,hi⟩))
    revert col
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun z => Fin.elim0 z))) row
    · intro c
      exact Fin.cases (hArange i hi)
        (Fin.cases (hArange i hi) (Fin.cases (hA'range i hi) (fun z => Fin.elim0 z))) c
    · intro c
      exact Fin.cases (hQrange i hi)
        (Fin.cases (hQrange i hi) (Fin.cases (hQ'range i hi) (fun z => Fin.elim0 z))) c
    · intro c
      exact Fin.cases (hbot 0)
        (Fin.cases (hbot 1) (Fin.cases (hbot 2) (fun z => Fin.elim0 z))) c
  have hbalanced (x) := determinant_balanced_coefficients (P x) ![r,r,L] k m.base
    (by change 100*k^2*r*r*L < m.base
        have hh : 100*k^2*r*r*L = 100*k^2*r^2*L := by ring
        rw [hh]; exact hbase) (hbound x)
  have heval (x) : (Matrix.det (P x)).eval (m.base : ℤ) =
      Matrix.det (m.matrix second x) := by
    simp only [P, Matrix.det_fin_three, eval_add, eval_sub, eval_mul]
    simp [matrix, hAeval, hA'eval, hQeval, hQ'eval, poly_eval, htop, hsecond, Fin.ext_iff]
  have himplies (x) (hx : m.smallResidue second x) : (Matrix.det (P x)).coeff (k-1) = 0 := by
    apply small_residue_coefficient _ (Nat.succ_le_of_lt hB) (by omega) (hbalanced x)
    rw [heval]
    exact hx
  have hmoment := m.tagged_pair_moment_from_tags hM hB second A A' Q Q' a d r
    ha hk hrB hA hA0 hQ hne hQpos hQ'pos hQle hQ'le hAeval hA'eval hQeval hQ'eval hscale
  apply le_trans _ hmoment
  unfold smallMoment
  apply average_mono
  intro x
  by_cases hx : m.smallResidue second x
  · have hh := himplies x hx
    change _ ≤ if (Matrix.det (P x)).coeff (k-1) = 0 then _ else _
    rw [if_pos hx, if_pos hh]
  · rw [if_neg hx]
    split_ifs <;> positivity

end DigitModel
#print axioms five_probability_scale
#print axioms DigitModel.smallMoment_le_uniform
#print axioms DigitModel.tagged_small_residue_moment

end HeilbronnFive
