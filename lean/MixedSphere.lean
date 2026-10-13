import Sphere

/-! Centered spheres with a separate alphabet and radix in each coordinate. -/

namespace HeilbronnMixedSphere
open HeilbronnSphere (coordinate triangular radiusIndex)

inductive Word : List Nat → Type where
  | nil : Word []
  | cons {A : Nat} {as : List Nat} : Fin (2 * A) → Word as → Word (A :: as)
  deriving DecidableEq

def size : List Nat → Nat
  | [] => 1
  | A :: as => (4 * A - 1) * size as

def encode : Word as → Nat
  | .nil => 0
  | @Word.cons A _ d w => d.val + (4 * A - 1) * encode w

def norm : Word as → Int
  | .nil => 0
  | @Word.cons A _ d w => coordinate (2 * A) d * coordinate (2 * A) d + norm w

def energy : Word as → Nat
  | .nil => 0
  | @Word.cons A _ d w => triangular (radiusIndex A d) + energy w

theorem norm_energy (x : Word as) : norm x = (as.length : Int) + 8 * (energy x : Int) := by
  induction x with
  | nil => simp [norm, energy]
  | @cons A as d w ih =>
    have hA : 0 < A := by have := d.isLt; omega
    have hd := HeilbronnSphere.digit_energy hA d
    simp only [norm, energy, List.length_cons, Int.ofNat_add, Int.ofNat_one]
    omega

def distance : Word as → Word as → Int
  | .nil, .nil => 0
  | @Word.cons A _ d x, .cons e y =>
      (coordinate (2 * A) d - coordinate (2 * A) e) *
        (coordinate (2 * A) d - coordinate (2 * A) e) + distance x y

def Midpoint : Word as → Word as → Word as → Prop
  | .nil, .nil, .nil => True
  | .cons d x, .cons e y, .cons f z => d.val + e.val = 2 * f.val ∧ Midpoint x y z

theorem distance_nonneg (x y : Word as) : 0 ≤ distance x y := by
  induction x with
  | nil => cases y; simp [distance]
  | @cons A as d x ih =>
    cases y with
    | cons e y =>
      have ht := ih y
      have hh := HeilbronnSphere.square_nonneg (coordinate (2 * A) d - coordinate (2 * A) e)
      simp only [distance]
      omega

theorem distance_zero (x y : Word as) (h : distance x y = 0) : x = y := by
  induction x with
  | nil => cases y; rfl
  | @cons A as d x ih =>
    cases y with
    | cons e y =>
      have ht := distance_nonneg x y
      have hh := HeilbronnSphere.square_nonneg (coordinate (2 * A) d - coordinate (2 * A) e)
      simp only [distance] at h
      have hz : (coordinate (2 * A) d - coordinate (2 * A) e) *
          (coordinate (2 * A) d - coordinate (2 * A) e) = 0 := by omega
      have he : coordinate (2 * A) d = coordinate (2 * A) e := by
        have h0 := Int.mul_eq_zero.mp hz
        omega
      have hd : d = e := by
        apply Fin.ext
        simp only [coordinate] at he
        omega
      have hw : x = y := ih y (by omega)
      subst e
      subst y
      rfl

theorem midpoint_identity (x y z : Word as) (h : Midpoint x y z) :
    distance x y + 4 * norm z = 2 * (norm x + norm y) := by
  induction x with
  | nil => cases y; cases z; simp [distance, norm]
  | @cons A as d x ih =>
    cases y with
    | cons e y =>
      cases z with
      | cons f z =>
        obtain ⟨hd, ht⟩ := h
        have hc : coordinate (2 * A) d + coordinate (2 * A) e = 2 * coordinate (2 * A) f := by
          simp only [coordinate]
          omega
        have hh := HeilbronnSphere.square_identity _ _ _ hc
        have hw := ih y z ht
        simp only [distance, norm]
        omega

theorem midpoint_self (x z : Word as) (h : Midpoint x x z) : x = z := by
  induction x with
  | nil => cases z; rfl
  | cons d x ih =>
    cases z with
    | cons f z =>
      obtain ⟨hd, ht⟩ := h
      have he : d = f := Fin.ext (by omega)
      subst f
      have hw := ih z ht
      subst z
      rfl

theorem midpoint_equal (x y z : Word as) (h : Midpoint x y z)
    (hn : norm x = norm z) (hm : norm y = norm z) : x = y ∧ y = z := by
  have hi := midpoint_identity x y z h
  have hxy : x = y := distance_zero x y (by omega)
  subst y
  exact ⟨rfl, midpoint_self x z h⟩

theorem no_carries (x y z : Word as) (h : encode x + encode y = 2 * encode z) : Midpoint x y z := by
  induction x with
  | nil => cases y; cases z; trivial
  | @cons A as d x ih =>
    cases y with
    | cons e y =>
      cases z with
      | cons f z =>
        let b := 4 * A - 1
        have hd := d.isLt
        have he := e.isLt
        have hf := f.isLt
        have hb : 0 < b := by dsimp [b]; omega
        have hde : d.val + e.val < b := by dsimp [b]; omega
        have hff : 2 * f.val < b := by dsimp [b]; omega
        have hh : (d.val + e.val) + b * (encode x + encode y) = 2 * f.val + b * (2 * encode z) := by
          simp only [encode, Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm b 2] at h ⊢
          dsimp [b] at *
          omega
        have hr := congrArg (fun n => n % b) hh
        simp [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hde, Nat.mod_eq_of_lt hff] at hr
        have ht : b * (encode x + encode y) = b * (2 * encode z) := by omega
        exact ⟨hr, ih y z (Nat.mul_left_cancel hb ht)⟩

theorem encode_bound (x : Word as) : 2 * encode x + 1 ≤ size as := by
  induction x with
  | nil => simp [encode, size]
  | @cons A as d x ih =>
    have hd := d.isLt
    have hh : 2 * d.val + 1 ≤ 4 * A - 1 := by omega
    have ht := Nat.mul_le_mul_left (4 * A - 1) ih
    simp only [encode, size, Nat.mul_add, Nat.mul_one,
      ← Nat.mul_assoc, Nat.mul_comm (4 * A - 1) 2] at ht ⊢
    omega

theorem encode_injective (x y : Word as) (h : encode x = encode y) : x = y :=
  midpoint_self x y (no_carries x x y (by omega))

theorem sphere_matching (x y z : Word as) (hx : norm x = norm z) (hy : norm y = norm z) :
    encode x + encode y + (size as - 1 - 2 * encode z) = size as - 1 ↔ x = y ∧ y = z := by
  have hz := encode_bound z
  constructor
  · intro h
    exact midpoint_equal x y z (no_carries x y z (by omega)) hx hy
  · rintro ⟨rfl, rfl⟩
    omega

theorem position_bounds (x : Word as) : encode x < size as ∧ size as - 1 - 2 * encode x < size as := by
  have h := encode_bound x
  omega

theorem right_injective (x y : Word as)
    (h : size as - 1 - 2 * encode x = size as - 1 - 2 * encode y) : x = y := by
  have hx := encode_bound x
  have hy := encode_bound y
  exact encode_injective x y (by omega)

#print axioms norm_energy
#print axioms sphere_matching

end HeilbronnMixedSphere
