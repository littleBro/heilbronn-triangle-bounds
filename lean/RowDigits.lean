import Slab

/-! Integer scale certificates for row-dependent digit ranges.
    The conditional probability lemma is proved in the written patch. -/

namespace HeilbronnRowDigits

def longDigits (k r : Nat) : Nat := 400 * k ^ 2 * r ^ 4

theorem long_digits_divisible (k r : Nat) : r ∣ longDigits k r :=
  HeilbronnTuned.digit_scale_divisible k r

theorem digit_moment_bound {k r B : Nat}
    (hB : B ≤ 200 * k ^ 2 * r ^ 2 * longDigits k r) :
    2 * B * r ^ 2 ≤ (longDigits k r) ^ 2 := by
  have he : 2 * (200 * k ^ 2 * r ^ 2 * longDigits k r) * r ^ 2 =
      (longDigits k r) ^ 2 := by
    calc
      _ = (2 * 200) * k ^ 2 * (r ^ 2 * r ^ 2) * longDigits k r := by ac_rfl
      _ = longDigits k r * longDigits k r := by rw [← Nat.pow_add]; rfl
      _ = (longDigits k r) ^ 2 := by simp [Nat.pow_succ]
  exact he ▸ Nat.mul_le_mul_right (r ^ 2) (Nat.mul_le_mul_left 2 hB)

theorem base_scale (k r : Nat) :
    200 * k ^ 2 * r ^ 2 * longDigits k r = 80000 * k ^ 4 * r ^ 6 := by
  calc
    _ = (200 * 400) * (k ^ 2 * k ^ 2) * (r ^ 2 * r ^ 4) := by
      unfold longDigits
      ac_rfl
    _ = _ := by rw [← Nat.pow_add, ← Nat.pow_add]

def rho (k : Nat) : Nat := 249 * k + 3

-- gamma = rho/(2*rho+1); positive denominators are cleared below.
theorem alteration_constraints {k : Nat} (hk : 2 ≤ k) :
    0 < rho k ∧
    2 * rho k < 2 * rho k + 1 ∧
    2 * rho k + 6 * (2 * rho k + 1) + 1 = 7 * (2 * rho k + 1) ∧
    rho k < 3 * (k - 1) * (2 * rho k + 1) := by
  have hm : 1 ≤ 3 * (k - 1) := by omega
  have hp := Nat.mul_le_mul_right (2 * rho k + 1) hm
  simp only [Nat.one_mul] at hp
  dsimp [rho] at *
  omega

theorem exponent_identity (k : Nat) :
    3 * (83 * k + 1) = rho k ∧
    2 * rho k * (rho k + 1) = rho k * (2 * rho k + 1) + rho k := by
  constructor
  · simp only [rho]; omega
  · simp only [Nat.mul_add, Nat.mul_one]
    have he : 2 * rho k * rho k = rho k * (2 * rho k) := by ac_rfl
    omega

#print axioms long_digits_divisible
#print axioms digit_moment_bound
#print axioms base_scale
#print axioms alteration_constraints
#print axioms exponent_identity

end HeilbronnRowDigits
