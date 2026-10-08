import Sphere

namespace HeilbronnTuned

open HeilbronnSphere

def tunedT : Nat := 18004519550937520342031694999844900

theorem tunedT_binomial :
    tunedT = binomialValue (binomialValue 51 13) 3 := by decide

theorem tuned_capacity :
    tunedT * (17 * triangular (101 - 1) + 1) ≤ 202 ^ 17 := by decide

theorem tuned_packing :
    ∃ u v : Fin (binomialValue (binomialValue 51 13) 3) → Nat,
      (∀ a, u a < 403 ^ 17 ∧ v a < 403 ^ 17) ∧
      (∀ a c, u a = u c → a = c) ∧
      (∀ a c, v a = v c → a = c) ∧
      (∀ a c e, u a + u c + v e = 403 ^ 17 - 1 ↔ a = c ∧ c = e) := by
  rw [← tunedT_binomial]
  exact packing_exists (A := 101) (m := 17)
    (by decide) (by decide) (by decide) (by decide) tuned_capacity

-- The following lemmas certify integer inequalities used in the written
-- transfer. They do not state the geometric or asymptotic theorem.
def digitScale (k r : Nat) : Nat := 400 * k ^ 2 * r ^ 4

theorem digit_scale_divisible (k r : Nat) : r ∣ digitScale k r := by
  refine ⟨400 * k ^ 2 * r ^ 3, ?_⟩
  simp only [digitScale, Nat.pow_succ]
  ac_rfl

theorem digit_moment_bound {k r B : Nat}
    (hB : B ≤ 200 * k ^ 2 * (digitScale k r) ^ 3) :
    2 * B * r ^ 4 ≤ (digitScale k r) ^ 4 := by
  have he : 2 * (200 * k ^ 2 * (digitScale k r) ^ 3) * r ^ 4 =
      (digitScale k r) ^ 4 := by
    calc
      _ = ((2 * 200) * k ^ 2 * r ^ 4) * (digitScale k r) ^ 3 := by ac_rfl
      _ = (digitScale k r) * (digitScale k r) ^ 3 := by rfl
      _ = (digitScale k r) ^ 4 :=
        (Nat.mul_comm _ _).trans (Nat.pow_succ _ 3).symm
  exact he ▸ Nat.mul_le_mul_right (r ^ 4) (Nat.mul_le_mul_left 2 hB)

theorem shell_threshold (h : Nat) : (2 * h) / 2 = h := by omega

theorem cap_modulus {h q : Nat} (hh : 3 ≤ h) (hq : h ^ 14 < q) :
    2000 * (2 * h) ^ 2 ≤ q := by
  have hp := Nat.pow_le_pow_of_le_left hh 12
  have hb : 8000 ≤ h ^ 12 := by omega
  have hm := Nat.mul_le_mul_left (h ^ 2) hb
  have he : 2000 * (2 * h) ^ 2 = h ^ 2 * 8000 := by
    simp only [Nat.mul_pow]
    omega
  rw [← Nat.pow_add] at hm
  calc
    _ = h ^ 2 * 8000 := he
    _ ≤ h ^ 14 := hm
    _ ≤ q := Nat.le_of_lt hq

theorem zero_case_bounds {h q : Nat} (hh : 1 ≤ h) (hq : h ^ 14 < q) :
    h ^ 2 * (2 * h) ^ 12 ≤ 4096 * q ∧
    h ^ 2 * (2 * h) ^ 6 ≤ 64 * q ∧
    h ^ 2 * (2 * h) ^ 12 ≤ 4096 * q ^ 2 := by
  have h14 : h ^ 2 * h ^ 12 = h ^ 14 := by rw [← Nat.pow_add]
  have h8 : h ^ 2 * h ^ 6 = h ^ 8 := by rw [← Nat.pow_add]
  have he12 : h ^ 2 * (2 * h) ^ 12 = 4096 * h ^ 14 := by
    rw [Nat.mul_pow, ← h14]
    change h ^ 2 * (4096 * h ^ 12) = 4096 * (h ^ 2 * h ^ 12)
    ac_rfl
  have he6 : h ^ 2 * (2 * h) ^ 6 = 64 * h ^ 8 := by
    rw [Nat.mul_pow, ← h8]
    change h ^ 2 * (64 * h ^ 6) = 64 * (h ^ 2 * h ^ 6)
    ac_rfl
  have h8le : h ^ 8 ≤ h ^ 14 :=
    Nat.pow_le_pow_of_le_right (by omega) (by decide)
  have hqpos : 1 ≤ q := by omega
  have hqsq : q ≤ q ^ 2 := by
    have hm := Nat.mul_le_mul_left q hqpos
    simpa only [Nat.mul_one, Nat.pow_succ, Nat.pow_zero, Nat.one_mul] using hm
  rw [he12, he6]
  exact ⟨Nat.mul_le_mul_left _ (by omega),
    Nat.mul_le_mul_left _ (by omega), Nat.mul_le_mul_left _ (by omega)⟩

def rho (k : Nat) : Nat := 1074 * k + 6

-- gamma = rho/(2*rho+1); all expressions below clear positive denominators.
theorem alteration_constraints {k : Nat} (hk : 2 ≤ k) :
    0 < rho k ∧
    2 * rho k < 2 * rho k + 1 ∧
    2 * rho k + 12 * (2 * rho k + 1) + 1 = 13 * (2 * rho k + 1) ∧
    rho k < 6 * (k - 1) * (2 * rho k + 1) := by
  have hm : 1 ≤ 6 * (k - 1) := by omega
  have hp := Nat.mul_le_mul_right (2 * rho k + 1) hm
  simp only [Nat.one_mul] at hp
  dsimp [rho] at *
  omega

theorem exponent_identity (k : Nat) :
    6 * (179 * k + 1) = rho k ∧
    2 * rho k * (rho k + 1) = rho k * (2 * rho k + 1) + rho k := by
  constructor
  · simp only [rho]; omega
  · simp only [Nat.mul_add, Nat.mul_one]
    have he : 2 * rho k * rho k = rho k * (2 * rho k) := by ac_rfl
    omega

theorem tuned_gain :
    3 * 10 ^ 90 * (2 * (1074 * 403 ^ 17 + 7)) < 45435 * 40011 ^ 29 + 16 ∧
    45435 * 40011 ^ 29 + 16 < 4 * 10 ^ 90 * (2 * (1074 * 403 ^ 17 + 7)) := by decide

#print axioms tunedT_binomial
#print axioms tuned_capacity
#print axioms tuned_packing
#print axioms digit_scale_divisible
#print axioms digit_moment_bound
#print axioms shell_threshold
#print axioms cap_modulus
#print axioms zero_case_bounds
#print axioms alteration_constraints
#print axioms exponent_identity
#print axioms tuned_gain

end HeilbronnTuned
