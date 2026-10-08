import Tuned

namespace HeilbronnSlab

-- Only the first coordinate is restricted in the written cap construction.
-- This lemma certifies its floor-width estimate; the finite-field geometry
-- and the probability argument remain in the accompanying note.
theorem slab_width_bound {q c : Nat} (hc : 0 < c) (hq : 2 * c ≤ q) :
    q ≤ 2 * c * (q / c) := by
  have hd : 1 ≤ q / c := (Nat.le_div_iff_mul_le hc).mpr (by omega)
  have hm := Nat.mul_le_mul_left c hd
  have hr := Nat.mod_lt q hc
  have he := Nat.mod_add_div q c
  simp only [Nat.mul_one] at hm
  have ha : 2 * c * (q / c) = c * (q / c) + c * (q / c) := by
    rw [Nat.mul_assoc]
    omega
  omega

theorem slab_size_bound {q H : Nat} (hH : 1 ≤ H)
    (hq : 2000 * H ^ 2 ≤ q) :
    q ^ 2 ≤ 2000 * H ^ 2 * ((q / (1000 * H ^ 2)) * q) := by
  have hc : 0 < 1000 * H ^ 2 := Nat.mul_pos (by decide) (Nat.pow_pos (by omega))
  have hd := slab_width_bound hc (show 2 * (1000 * H ^ 2) ≤ q by omega)
  have hm := Nat.mul_le_mul_right q hd
  have he : 2 * (1000 * H ^ 2) * (q / (1000 * H ^ 2)) * q =
      2000 * H ^ 2 * ((q / (1000 * H ^ 2)) * q) := by
    simp only [Nat.mul_assoc]
    omega
  rw [he] at hm
  simpa only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul] using hm

theorem cap_modulus {h q : Nat} (hh : 10 ≤ h) (hq : h ^ 6 < q) :
    2000 * (2 * h) ^ 2 ≤ q := by
  have hp := Nat.pow_le_pow_of_le_left hh 4
  have hb : 8000 ≤ h ^ 4 := by omega
  have hm := Nat.mul_le_mul_left (h ^ 2) hb
  have he : 2000 * (2 * h) ^ 2 = h ^ 2 * 8000 := by
    simp only [Nat.mul_pow]
    omega
  rw [← Nat.pow_add] at hm
  calc
    _ = h ^ 2 * 8000 := he
    _ ≤ h ^ 6 := hm
    _ ≤ q := Nat.le_of_lt hq

theorem zero_case_bounds {h q : Nat} (hh : 1 ≤ h) (hq : h ^ 6 < q) :
    h ^ 2 * (2 * h) ^ 4 ≤ 16 * q ∧
    h ^ 2 * (2 * h) ^ 2 ≤ 4 * q ∧
    h ^ 2 * (2 * h) ^ 4 ≤ 16 * q ^ 2 := by
  have h6 : h ^ 2 * h ^ 4 = h ^ 6 := by rw [← Nat.pow_add]
  have h4 : h ^ 2 * h ^ 2 = h ^ 4 := by rw [← Nat.pow_add]
  have he4 : h ^ 2 * (2 * h) ^ 4 = 16 * h ^ 6 := by
    rw [Nat.mul_pow, ← h6]
    change h ^ 2 * (16 * h ^ 4) = 16 * (h ^ 2 * h ^ 4)
    ac_rfl
  have he2 : h ^ 2 * (2 * h) ^ 2 = 4 * h ^ 4 := by
    rw [Nat.mul_pow, ← h4]
    change h ^ 2 * (4 * h ^ 2) = 4 * (h ^ 2 * h ^ 2)
    ac_rfl
  have h4le : h ^ 4 ≤ h ^ 6 :=
    Nat.pow_le_pow_of_le_right (by omega) (by decide)
  have hqpos : 1 ≤ q := by omega
  have hqsq : q ≤ q ^ 2 := by
    have hm := Nat.mul_le_mul_left q hqpos
    simpa only [Nat.mul_one, Nat.pow_succ, Nat.pow_zero, Nat.one_mul] using hm
  rw [he4, he2]
  exact ⟨Nat.mul_le_mul_left _ (by omega),
    Nat.mul_le_mul_left _ (by omega), Nat.mul_le_mul_left _ (by omega)⟩

def rho (k : Nat) : Nat := 498 * k + 6

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
    6 * (83 * k + 1) = rho k ∧
    2 * rho k * (rho k + 1) = rho k * (2 * rho k + 1) + rho k := by
  constructor
  · simp only [rho]; omega
  · simp only [Nat.mul_add, Nat.mul_one]
    have he : 2 * rho k * rho k = rho k * (2 * rho k) := by ac_rfl
    omega

theorem slab_gain :
    215 * (498 * 403 ^ 17 + 7) < 100 * (1074 * 403 ^ 17 + 7) ∧
    100 * (1074 * 403 ^ 17 + 7) < 216 * (498 * 403 ^ 17 + 7) := by decide

#print axioms slab_width_bound
#print axioms slab_size_bound
#print axioms cap_modulus
#print axioms zero_case_bounds
#print axioms alteration_constraints
#print axioms exponent_identity
#print axioms slab_gain

end HeilbronnSlab
