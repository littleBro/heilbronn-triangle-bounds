import RowDigits

/-! Arithmetic for the tagged degree-five construction. Probability remains written. -/

namespace HeilbronnFiveScales
open HeilbronnRowDigits (rho)

theorem fresh_position {d k a j : Nat} (ha : a < d) (hk : 2 * d ≤ k)
    (hj : j ≤ a) : j < k - 1 - a ∧ k - 1 - a < k := by omega

-- gamma = rho/(rho+1); the two collision terms have powers 2*gamma-2 and 2*gamma-4.
theorem alteration_constraints {k : Nat} (hk : 2 ≤ k) :
    0 < rho k ∧ rho k < rho k + 1 ∧
    2 * rho k + 6 * (rho k + 1) + 2 = 8 * (rho k + 1) ∧
    2 * rho k + 6 * (rho k + 1) < 10 * (rho k + 1) ∧
    rho k < 3 * (k - 1) * (rho k + 1) := by
  have hm : 1 ≤ 3 * (k - 1) := by omega
  have hp := Nat.mul_le_mul_right (rho k + 1) hm
  simp only [Nat.one_mul] at hp
  dsimp [rho] at *
  omega

theorem exponent_identity (k : Nat) :
    3 * (83 * k + 1) = rho k ∧
    rho k * (rho k + 2) = rho k * (rho k + 1) + rho k := by
  constructor
  · simp only [rho]; omega
  · simp only [Nat.mul_add, Nat.mul_one, Nat.mul_succ]

theorem exact_exponent : 249 * 1166895 + 5 = 2 * 145278430 := by decide

#print axioms fresh_position
#print axioms alteration_constraints
#print axioms exponent_identity
#print axioms exact_exponent

end HeilbronnFiveScales
