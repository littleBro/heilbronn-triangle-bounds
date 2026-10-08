import Lean
set_option exponentiation.threshold 512

/- The finite sphere construction is proved from counting through selection
and carry-free encoding. No geometric Heilbronn theorem is asserted here. -/
namespace HeilbronnSphere

theorem square_nonneg (x : Int) : 0 ≤ x * x := by
  by_cases h : 0 ≤ x
  · exact Int.mul_nonneg h h
  · exact Int.mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)

theorem square_identity (x y z : Int) (h : x + y = 2 * z) :
    (x - y) * (x - y) + 4 * (z * z) = 2 * (x * x + y * y) := by
  have hh : (x + y) * (x + y) = (2 * z) * (2 * z) := congrArg (fun v => v * v) h
  have hc : (2 * z) * (2 * z) = 4 * (z * z) := by
    calc
      (2 * z) * (2 * z) = (2 * 2) * (z * z) := by ac_rfl
      _ = 4 * (z * z) := rfl
  rw [hc] at hh
  simp only [Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub,
    Int.mul_comm y x] at hh ⊢
  omega

inductive Word (s : Nat) : Nat → Type where
  | nil : Word s 0
  | cons {m : Nat} : Fin s → Word s m → Word s (m + 1)
  deriving DecidableEq

def coordinate (s : Nat) (d : Fin s) : Int := 2 * (d.val : Int) - (s - 1 : Nat)

def encode (b : Nat) : Word s m → Nat
  | .nil => 0
  | .cons d w => d.val + b * encode b w

def norm : Word s m → Int
  | .nil => 0
  | .cons d w => coordinate s d * coordinate s d + norm w

def distance : {m : Nat} → Word s m → Word s m → Int
  | 0, .nil, .nil => 0
  | _ + 1, .cons d x, .cons e y =>
      (coordinate s d - coordinate s e) * (coordinate s d - coordinate s e) +
        distance x y

def Midpoint : {m : Nat} → Word s m → Word s m → Word s m → Prop
  | 0, .nil, .nil, .nil => True
  | _ + 1, .cons d x, .cons e y, .cons f z =>
      d.val + e.val = 2 * f.val ∧ Midpoint x y z

theorem distance_nonneg (x y : Word s m) : 0 ≤ distance x y := by
  induction x with
  | nil => cases y; simp [distance]
  | cons d x ih =>
    cases y with
    | cons e y =>
      have ht := ih y
      have hh := square_nonneg (coordinate s d - coordinate s e)
      simp only [distance]
      omega

theorem distance_zero (x y : Word s m) (h : distance x y = 0) : x = y := by
  induction x with
  | nil => cases y; rfl
  | cons d x ih =>
    cases y with
    | cons e y =>
      have ht := distance_nonneg x y
      have hh := square_nonneg (coordinate s d - coordinate s e)
      simp only [distance] at h
      have hz : (coordinate s d - coordinate s e) *
          (coordinate s d - coordinate s e) = 0 := by omega
      have he : coordinate s d = coordinate s e := by
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

theorem midpoint_identity (x y z : Word s m) (h : Midpoint x y z) :
    distance x y + 4 * norm z = 2 * (norm x + norm y) := by
  induction x with
  | nil => cases y; cases z; simp [distance, norm]
  | cons d x ih =>
    cases y with
    | cons e y =>
      cases z with
      | cons f z =>
        obtain ⟨hd, ht⟩ := h
        have hc : coordinate s d + coordinate s e = 2 * coordinate s f := by
          simp only [coordinate]
          omega
        have hh := square_identity (coordinate s d) (coordinate s e) (coordinate s f) hc
        have hw := ih y z ht
        simp only [distance, norm]
        omega

theorem midpoint_self (x z : Word s m) (h : Midpoint x x z) : x = z := by
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

theorem midpoint_equal (x y z : Word s m) (h : Midpoint x y z)
    (hn : norm x = norm z) (hm : norm y = norm z) : x = y ∧ y = z := by
  have hi := midpoint_identity x y z h
  have hxy : x = y := distance_zero x y (by omega)
  subst y
  exact ⟨rfl, midpoint_self x z h⟩

theorem no_carries (x y z : Word s m) (hb : 0 < b) (hs : 2 * s ≤ b + 1)
    (h : encode b x + encode b y = 2 * encode b z) : Midpoint x y z := by
  induction x with
  | nil => cases y; cases z; trivial
  | cons d x ih =>
    cases y with
    | cons e y =>
      cases z with
      | cons f z =>
        have hd := d.isLt
        have he := e.isLt
        have hf := f.isLt
        have hde : d.val + e.val < b := by omega
        have hff : 2 * f.val < b := by omega
        have hh : (d.val + e.val) + b * (encode b x + encode b y) =
            2 * f.val + b * (2 * encode b z) := by
          simp only [encode, Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm b 2] at h ⊢
          omega
        have hr := congrArg (fun n => n % b) hh
        simp [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hde, Nat.mod_eq_of_lt hff] at hr
        have ht : b * (encode b x + encode b y) = b * (2 * encode b z) := by omega
        exact ⟨hr, ih y z (Nat.mul_left_cancel hb ht)⟩

theorem encode_bound (x : Word s m) (_hb : 0 < b) (hs : 2 * s ≤ b + 1) :
    2 * encode b x + 1 ≤ b ^ m := by
  induction x with
  | nil => simp [encode]
  | @cons m d x ih =>
    have hd := d.isLt
    have hh : 2 * d.val + 1 ≤ b := by omega
    have ht := Nat.mul_le_mul_left b ih
    simp only [encode, Nat.pow_succ, Nat.mul_add, Nat.mul_one,
      ← Nat.mul_assoc, Nat.mul_comm b 2] at ht ⊢
    have hc : b * b ^ m = b ^ m * b := Nat.mul_comm _ _
    omega

theorem encode_injective (x y : Word s m) (hb : 0 < b) (hs : 2 * s ≤ b + 1)
    (h : encode b x = encode b y) : x = y :=
  midpoint_self x y (no_carries x x y hb hs (by omega))

theorem sphere_matching (x y z : Word s m) (hb : 0 < b) (hs : 2 * s ≤ b + 1)
    (hx : norm x = norm z) (hy : norm y = norm z) :
    encode b x + encode b y + (b ^ m - 1 - 2 * encode b z) = b ^ m - 1 ↔
      x = y ∧ y = z := by
  have hz := encode_bound z hb hs
  constructor
  · intro h
    exact midpoint_equal x y z (no_carries x y z hb hs (by omega)) hx hy
  · rintro ⟨rfl, rfl⟩
    omega

theorem position_bounds (x : Word s m) (hb : 0 < b) (hs : 2 * s ≤ b + 1) :
    encode b x < b ^ m ∧ b ^ m - 1 - 2 * encode b x < b ^ m := by
  have h := encode_bound x hb hs
  omega

theorem right_injective (x y : Word s m) (hb : 0 < b) (hs : 2 * s ≤ b + 1)
    (h : b ^ m - 1 - 2 * encode b x = b ^ m - 1 - 2 * encode b y) : x = y := by
  have hx := encode_bound x hb hs
  have hy := encode_bound y hb hs
  exact encode_injective x y hb hs (by omega)

/- Finite counting and the sphere producer. None of these definitions is
evaluated on the enormous paper-sized cube during proof checking. -/

def decode (s : Nat) (hs : 0 < s) : (m : Nat) → Nat → Word s m
  | 0, _ => .nil
  | m + 1, a => .cons ⟨a % s, Nat.mod_lt a hs⟩ (decode s hs m (a / s))

theorem decode_value (hs : 0 < s) (m a : Nat) (ha : a < s ^ m) :
    encode s (decode s hs m a) = a := by
  induction m generalizing a with
  | zero =>
    have : a = 0 := by simp only [Nat.pow_zero] at ha; omega
    subst a
    rfl
  | succ m ih =>
    have ht : a / s < s ^ m := by
      apply (Nat.div_lt_iff_lt_mul hs).2
      simpa only [Nat.pow_succ] using ha
    simp only [decode, encode, ih (a / s) ht]
    exact Nat.mod_add_div a s

theorem decode_injective (hs : 0 < s) (ha : a < s ^ m) (hb : b < s ^ m)
    (h : decode s hs m a = decode s hs m b) : a = b := by
  have hv := congrArg (encode s) h
  simpa only [decode_value hs m a ha, decode_value hs m b hb] using hv

def triangular (r : Nat) : Nat := r * (r + 1) / 2

theorem triangular_twice (r : Nat) : 2 * triangular r = r * (r + 1) := by
  have hr : r % 2 = 0 ∨ r % 2 = 1 := by omega
  have he : (r * (r + 1)) % 2 = 0 := by
    rcases hr with hr | hr <;> simp [Nat.mul_mod, Nat.add_mod, hr]
  have h := Nat.mod_add_div (r * (r + 1)) 2
  simp only [he, Nat.zero_add] at h
  exact h

theorem triangular_mono (h : r ≤ t) : triangular r ≤ triangular t := by
  have hm := Nat.mul_le_mul h (Nat.succ_le_succ h)
  simp only [Nat.succ_eq_add_one] at hm
  have hr := triangular_twice r
  have ht := triangular_twice t
  omega

def radiusIndex (A : Nat) (d : Fin (2 * A)) : Nat :=
  if d.val < A then A - 1 - d.val else d.val - A

theorem radius_bound (_hA : 0 < A) (d : Fin (2 * A)) : radiusIndex A d < A := by
  have hd := d.isLt
  unfold radiusIndex
  split <;> omega

theorem coordinate_radius (hA : 0 < A) (d : Fin (2 * A)) :
    coordinate (2 * A) d = 2 * (radiusIndex A d : Int) + 1 ∨
    coordinate (2 * A) d = -(2 * (radiusIndex A d : Int) + 1) := by
  unfold coordinate radiusIndex
  split <;> omega

theorem odd_square (r : Nat) :
    (2 * (r : Int) + 1) * (2 * (r : Int) + 1) = 8 * (triangular r : Int) + 1 := by
  have ht := congrArg Int.ofNat (triangular_twice r)
  change 2 * (triangular r : Int) = (r : Int) * ((r : Int) + 1) at ht
  have hc : (2 * (r : Int)) * (2 * (r : Int)) = 4 * ((r : Int) * (r : Int)) := by
    calc
      _ = (2 * 2) * ((r : Int) * (r : Int)) := by ac_rfl
      _ = _ := rfl
  simp only [Int.add_mul, Int.mul_add, Int.mul_one, Int.one_mul] at ht ⊢
  omega

theorem digit_energy (hA : 0 < A) (d : Fin (2 * A)) :
    coordinate (2 * A) d * coordinate (2 * A) d =
      1 + 8 * (triangular (radiusIndex A d) : Int) := by
  have hs := odd_square (radiusIndex A d)
  rcases coordinate_radius hA d with hc | hc
  · rw [hc]; omega
  · rw [hc, Int.neg_mul_neg]; omega

def energyIndex : Word (2 * A) m → Nat
  | .nil => 0
  | .cons d w => triangular (radiusIndex A d) + energyIndex w

theorem energy_bound (hA : 0 < A) (w : Word (2 * A) m) :
    energyIndex w ≤ m * triangular (A - 1) := by
  induction w with
  | nil => simp [energyIndex]
  | cons d w ih =>
    have hd := triangular_mono (show radiusIndex A d ≤ A - 1 from by
      have h := radius_bound hA d; omega)
    simp only [energyIndex, Nat.succ_mul]
    omega

theorem norm_energy (hA : 0 < A) (w : Word (2 * A) m) :
    norm w = (m : Int) + 8 * (energyIndex w : Int) := by
  induction w with
  | nil => simp [norm, energyIndex]
  | cons d w ih =>
    have hd := digit_energy hA d
    simp only [norm, energyIndex, Int.ofNat_add]
    omega

theorem filter_partition (l : List α) (f : α → Nat) (q : Nat)
    (hf : ∀ x ∈ l, f x ≤ q) :
    (l.filter (fun x => decide (f x < q))).length +
      (l.filter (fun x => decide (f x = q))).length = l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have hx := hf x (by simp)
    have ht := ih (fun y hy => hf y (by simp [hy]))
    by_cases h : f x < q
    · have hn : f x ≠ q := by omega
      simp [List.filter_cons, h, hn]
      omega
    · have he : f x = q := by omega
      simp [List.filter_cons, he]
      omega

theorem filter_below_eq (l : List α) (f : α → Nat) (hj : j < q) :
    (l.filter (fun x => decide (f x < q))).filter (fun x => decide (f x = j)) =
      l.filter (fun x => decide (f x = j)) := by
  rw [List.filter_filter]
  congr 1
  funext x
  by_cases h : f x = j <;> simp [h, hj]

theorem fiber_bound (l : List α) (f : α → Nat) (Q M : Nat)
    (hf : ∀ x ∈ l, f x < Q)
    (hc : ∀ j, j < Q → (l.filter (fun x => decide (f x = j))).length ≤ M) :
    l.length ≤ Q * M := by
  induction Q generalizing l with
  | zero =>
    cases l with
    | nil => simp
    | cons x l => have := hf x (by simp); omega
  | succ q ih =>
    let low := l.filter (fun x => decide (f x < q))
    have hb : low.length ≤ q * M := by
      apply ih low
      · intro x hx
        exact of_decide_eq_true (List.mem_filter.mp hx).2
      · intro j hj
        have hh := hc j (by omega)
        simpa only [low, filter_below_eq l f hj] using hh
    have ht := hc q (by omega)
    have hp := filter_partition l f q (fun x hx => by have := hf x hx; omega)
    simp only [Nat.succ_mul]
    change low.length + _ = _ at hp
    omega

theorem large_fiber (l : List α) (f : α → Nat) (Q T : Nat)
    (hQ : 0 < Q) (hT : 0 < T)
    (hf : ∀ x ∈ l, f x < Q) (hsize : Q * T ≤ l.length) :
    ∃ j, j < Q ∧ T ≤ (l.filter (fun x => decide (f x = j))).length := by
  apply Classical.byContradiction
  intro hn
  have hb : l.length ≤ Q * (T - 1) := by
    apply fiber_bound l f Q (T - 1) hf
    intro j hj
    have : ¬ T ≤ (l.filter (fun x => decide (f x = j))).length := by
      intro h
      exact hn ⟨j, hj, h⟩
    omega
  have he : Q * (T - 1) + Q = Q * T := by
    have ht : T - 1 + 1 = T := by omega
    calc
      _ = Q * (T - 1 + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = _ := by rw [ht]
  omega

theorem select_large_fiber (N Q T : Nat) (f : Nat → Nat)
    (hQ : 0 < Q) (hT : 0 < T) (hf : ∀ x, x < N → f x < Q)
    (hsize : Q * T ≤ N) :
    ∃ idx : Fin T → Fin N,
      (∀ a b, idx a = idx b → a = b) ∧
      ∃ j, j < Q ∧ ∀ a, f (idx a).val = j := by
  obtain ⟨j, hj, hlen⟩ := large_fiber (List.range N) f Q T hQ hT
    (fun x hx => hf x (List.mem_range.mp hx)) (by simpa using hsize)
  let l := (List.range N).filter (fun x => decide (f x = j))
  have hlength : T ≤ l.length := hlen
  let rank : Fin T → Fin l.length := fun a =>
    ⟨a.val, Nat.lt_of_lt_of_le a.isLt hlength⟩
  let picked : Fin T → Nat := fun a => l.get (rank a)
  have hmem (a : Fin T) : picked a ∈ l := List.get_mem l (rank a).val (rank a).isLt
  have hraw (a : Fin T) : picked a ∈ List.range N ∧ f (picked a) = j := by
    have hh := List.mem_filter.mp (hmem a)
    exact ⟨hh.1, of_decide_eq_true hh.2⟩
  let idx : Fin T → Fin N := fun a => ⟨picked a, List.mem_range.mp (hraw a).1⟩
  have hnd : l.Nodup := (List.filter_sublist (List.range N)).nodup (List.nodup_range N)
  refine ⟨idx, ?_, ⟨j, hj, ?_⟩⟩
  · intro a b h
    apply Fin.ext
    have hp : l.get (rank a) = l.get (rank b) := congrArg Fin.val h
    have he : l[(rank a).val]? = l[(rank b).val]? := by
      rw [List.getElem?_eq_getElem (rank a).isLt, List.getElem?_eq_getElem (rank b).isLt]
      exact congrArg some hp
    exact List.getElem?_inj (rank a).isLt hnd he
  · intro a
    exact (hraw a).2

theorem sphere_family {A m T : Nat} (hA : 0 < A) (hT : 0 < T)
    (hcapacity : T * (m * triangular (A - 1) + 1) ≤ (2 * A) ^ m) :
    ∃ w : Fin T → Word (2 * A) m,
      (∀ a b, w a = w b → a = b) ∧
      (∀ a b, norm (w a) = norm (w b)) := by
  have hs : 0 < 2 * A := by omega
  let N := (2 * A) ^ m
  let Q := m * triangular (A - 1) + 1
  let f : Nat → Nat := fun n => energyIndex (decode (2 * A) hs m n)
  have hf (n : Nat) (_ : n < N) : f n < Q := by
    have he := energy_bound hA (decode (2 * A) hs m n)
    change energyIndex (decode (2 * A) hs m n) < m * triangular (A - 1) + 1
    omega
  obtain ⟨idx, hi, j, _, hj⟩ := select_large_fiber N Q T f (by omega) hT hf
    (by simpa only [N, Q, Nat.mul_comm] using hcapacity)
  let w : Fin T → Word (2 * A) m := fun a => decode (2 * A) hs m (idx a).val
  refine ⟨w, ?_, ?_⟩
  · intro a b h
    apply hi a b
    apply Fin.ext
    exact decode_injective hs (idx a).isLt (idx b).isLt h
  · intro a b
    have ha : energyIndex (w a) = j := hj a
    have hb : energyIndex (w b) = j := hj b
    rw [norm_energy hA, norm_energy hA, ha, hb]

theorem packing_exists {A m T b : Nat} (hA : 0 < A) (hT : 0 < T)
    (hb : 0 < b) (hs : 2 * (2 * A) ≤ b + 1)
    (hcapacity : T * (m * triangular (A - 1) + 1) ≤ (2 * A) ^ m) :
    ∃ u v : Fin T → Nat,
      (∀ a, u a < b ^ m ∧ v a < b ^ m) ∧
      (∀ a c, u a = u c → a = c) ∧
      (∀ a c, v a = v c → a = c) ∧
      (∀ a c e, u a + u c + v e = b ^ m - 1 ↔ a = c ∧ c = e) := by
  obtain ⟨w, hi, hn⟩ := sphere_family hA hT hcapacity
  let u := fun a => encode b (w a)
  let v := fun a => b ^ m - 1 - 2 * u a
  refine ⟨u, v, ?_, ?_, ?_, ?_⟩
  · intro a
    exact position_bounds (w a) hb hs
  · intro a c h
    exact hi a c (encode_injective (w a) (w c) hb hs h)
  · intro a c h
    exact hi a c (right_injective (w a) (w c) hb hs h)
  · intro a c e
    have hm := sphere_matching (w a) (w c) (w e) hb hs (hn a e) (hn c e)
    constructor
    · intro h
      obtain ⟨hac, hce⟩ := hm.mp h
      exact ⟨hi a c hac, hi c e hce⟩
    · rintro ⟨rfl, rfl⟩
      exact hm.mpr ⟨rfl, rfl⟩

def paperT : Nat :=
  37230514451212307341579258391864337055334059182582962517976151329575965621134724577475162784520018371181237814762800

-- Falling-factorial quotient definition of the binomial coefficient.
-- Recursion is in k, never in the enormous upper argument n.
def falling (n : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => falling n k * (n - k)

def binomialValue (n k : Nat) : Nat := falling n k / falling k k

theorem paperT_binomial :
    paperT = binomialValue (binomialValue 163 41) 3 := by decide

-- These are numerical certificates, not a formal enumeration of sphere points.
theorem paper_capacity :
    paperT * (29 * (10003 * 10002 / 2) + 1) ≤ 20006 ^ 29 := by decide

theorem paper_base : 2 * 20006 = 40011 + 1 := by decide

theorem paper_packing :
    ∃ u v : Fin paperT → Nat,
      (∀ a, u a < 40011 ^ 29 ∧ v a < 40011 ^ 29) ∧
      (∀ a c, u a = u c → a = c) ∧
      (∀ a c, v a = v c → a = c) ∧
      (∀ a c e, u a + u c + v e = 40011 ^ 29 - 1 ↔ a = c ∧ c = e) := by
  apply packing_exists (A := 10003) (m := 29) (by decide) (by decide)
    (by decide) (by decide)
  exact paper_capacity

theorem paper_packing_binomial :
    ∃ u v : Fin (binomialValue (binomialValue 163 41) 3) → Nat,
      (∀ a, u a < 40011 ^ 29 ∧ v a < 40011 ^ 29) ∧
      (∀ a c, u a = u c → a = c) ∧
      (∀ a c, v a = v c → a = c) ∧
      (∀ a c e, u a + u c + v e = 40011 ^ 29 - 1 ↔ a = c ∧ c = e) := by
  rw [← paperT_binomial]
  exact paper_packing

theorem sphere_gain :
    5 * 10 ^ 49 * (45435 * 40011 ^ 29 + 16) < 45435 * 3 ^ 384 + 16 ∧
    45435 * 3 ^ 384 + 16 < 6 * 10 ^ 49 * (45435 * 40011 ^ 29 + 16) := by decide

#print axioms sphere_matching
#print axioms position_bounds
#print axioms encode_injective
#print axioms right_injective
#print axioms paper_capacity
#print axioms sphere_gain
#print axioms sphere_family
#print axioms packing_exists
#print axioms paper_packing
#print axioms paperT_binomial
#print axioms paper_packing_binomial

end HeilbronnSphere
