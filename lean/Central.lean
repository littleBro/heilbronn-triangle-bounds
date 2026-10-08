import Slab
set_option maxRecDepth 2048

namespace HeilbronnCentral
open HeilbronnSphere

-- All counting below is symbolic in the number of words. Only the 190
-- one-digit values and the 17-step moment recurrence are evaluated.
def digits : List (Fin 190) := (List.range 190).filterMap fun n =>
  if h : n < 190 then some ⟨n, h⟩ else none

theorem digits_length : digits.length = 190 := by decide

theorem digits_nodup : digits.Nodup := by
  apply List.Pairwise.filterMap _ _ (List.nodup_range 190)
  intro a b hab x hx y hy he
  split at hx <;> simp_all
  obtain ⟨_, hb⟩ := hy
  have ha' : a = y.val := congrArg Fin.val hx
  have hb' : b = y.val := congrArg Fin.val hb
  exact hab (ha'.trans hb'.symm)

def words : (m : Nat) → List (Word 190 m)
  | 0 => [.nil]
  | m + 1 => digits.bind fun d => (words m).map (Word.cons d)

def total (f : α → Int) : List α → Int
  | [] => 0
  | a :: l => f a + total f l

theorem total_append (f : α → Int) (l r : List α) :
    total f (l ++ r) = total f l + total f r := by
  induction l <;> simp [total, *, Int.add_assoc]

theorem total_map (f : β → Int) (g : α → β) (l : List α) :
    total f (l.map g) = total (fun a => f (g a)) l := by
  induction l <;> simp [total, *]

theorem total_bind (f : β → Int) (g : α → List β) (l : List α) :
    total f (l.bind g) = total (fun a => total f (g a)) l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change total f (g a ++ l.bind g) = total f (g a) + total (fun a => total f (g a)) l
    rw [total_append, ih]

theorem total_add (f g : α → Int) (l : List α) :
    total (fun a => f a + g a) l = total f l + total g l := by
  induction l <;> simp [total, *] <;> omega

theorem total_mul (c : Int) (f : α → Int) (l : List α) :
    total (fun a => c * f a) l = c * total f l := by
  induction l <;> simp [total, *, Int.mul_add]

theorem total_const (c : Int) (l : List α) :
    total (fun _ => c) l = (l.length : Int) * c := by
  induction l <;> simp [total, *, Int.ofNat_add, Int.add_mul] <;> omega

theorem length_bind_map (ds : List (Fin s)) (ws : List (Word s m)) :
    (ds.bind fun d => ws.map (Word.cons d)).length = ds.length * ws.length := by
  induction ds with
  | nil => simp [List.bind]
  | cons d ds ih =>
    change (ws.map (Word.cons d) ++ ds.bind (fun d => ws.map (Word.cons d))).length = _
    rw [List.length_append, List.length_map, ih, List.length_cons, Nat.add_mul]
    omega

theorem words_length (m : Nat) : (words m).length = 190 ^ m := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [words, length_bind_map, digits_length, ih, Nat.pow_succ]; omega

theorem words_nodup (m : Nat) : (words m).Nodup := by
  induction m with
  | zero => simp [words]
  | succ m ih =>
    apply List.pairwise_bind.mpr
    constructor
    · intro d _
      exact ih.map (Word.cons d) (fun a b h he => h (Word.cons.inj he).2)
    · apply digits_nodup.imp
      intro a b hab x hx y hy hxy
      obtain ⟨u, _, rfl⟩ := List.mem_map.mp hx
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hy
      exact hab (Word.cons.inj hxy).1

def digitScore (d : Fin 190) : Int :=
  (triangular (radiusIndex 95 d) : Int) - 1504

def score : Word 190 m → Int
  | .nil => 0
  | .cons d w => digitScore d + score w

theorem digit_mean : total digitScore digits = 0 := by decide
theorem digit_square : total (fun d => digitScore d * digitScore d) digits = 343855008 := by decide

theorem shifted_square (x : Int) (f : α → Int) (l : List α) :
    total (fun a => (x + f a) * (x + f a)) l =
      (l.length : Int) * (x * x) + 2 * x * total f l +
        total (fun a => f a * f a) l := by
  induction l with
  | nil => simp [total]
  | cons a l ih =>
    change (x + f a) * (x + f a) + total (fun a => (x + f a) * (x + f a)) l = _
    rw [ih]
    have he : 2 * x * f a = 2 * (x * f a) := by ac_rfl
    simp only [total, List.length_cons, Int.ofNat_add, Int.ofNat_one,
      Int.add_mul, Int.mul_add, Int.one_mul, Int.mul_comm (f a) x, he]
    omega

theorem words_mean (m : Nat) : total score (words m) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [words, total_bind, total_map, score, total_add, total_const, ih,
      Int.add_zero, total_mul, digit_mean, Int.mul_zero]

def secondMoment : Nat → Int
  | 0 => 0
  | m + 1 => 190 * secondMoment m + (190 ^ m : Nat) * 343855008

theorem words_square (m : Nat) :
    total (fun w => score w * score w) (words m) = secondMoment m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [words, total_bind, total_map, score, shifted_square, words_mean,
      Int.mul_zero, Int.add_zero, total_add, total_mul, total_const,
      digit_square, digits_length, ih, words_length, secondMoment]
    omega

theorem score_energy (w : Word 190 m) :
    score w = (energyIndex (A := 95) w : Int) - (m : Int) * 1504 := by
  induction w with
  | nil => rfl
  | cons d w ih =>
    simp only [score, digitScore, energyIndex, Int.ofNat_add, Int.ofNat_one,
      Int.add_mul, Int.one_mul, ih]
    omega

def central (w : Word 190 17) : Bool :=
  decide (15568 ≤ energyIndex (A := 95) w ∧ energyIndex (A := 95) w ≤ 35568)

theorem outside_square (w : Word 190 17) (hw : central w = false) :
    100020001 ≤ score w * score w := by
  have hs := score_energy w
  have he : ¬ (15568 ≤ energyIndex (A := 95) w ∧ energyIndex (A := 95) w ≤ 35568) := by
    simpa [central] using hw
  have hb : score w ≤ -10001 ∨ 10001 ≤ score w := by omega
  have hp : 0 ≤ (score w - 10001) * (score w + 10001) := by
    rcases hb with h | h
    · exact Int.mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
    · exact Int.mul_nonneg (by omega) (by omega)
  simp only [Int.sub_mul, Int.mul_add, Int.mul_comm (score w) 10001] at hp
  omega

theorem central_count_bound (l : List (Word 190 17)) :
    (l.length : Int) * 100020001 ≤
      ((l.filter central).length : Int) * 100020001 +
        total (fun w => score w * score w) l := by
  induction l with
  | nil => simp [total]
  | cons w l ih =>
    cases hc : central w with
    | false =>
      have hb := outside_square w hc
      simp only [List.length_cons, Int.ofNat_add, Int.ofNat_one, List.filter_cons,
        hc, Bool.false_eq_true, ↓reduceIte, total, Int.add_mul, Int.one_mul]
      omega
    | true =>
      have hb := square_nonneg (score w)
      simp only [List.length_cons, Int.ofNat_add, Int.ofNat_one, List.filter_cons,
        hc, ↓reduceIte, total, Int.add_mul, Int.one_mul]
      omega

def centralWords := (words 17).filter central
def centralT : Nat := 18004519550937520342031694999844900

theorem central_capacity : 20001 * centralT ≤ centralWords.length := by
  have h := central_count_bound (words 17)
  rw [words_length, words_square] at h
  change (548038685778480218593900000000000000000 : Int) * 100020001 ≤
    (centralWords.length : Int) * 100020001 +
      16860944176870366476166331396160000000000000000 at h
  change 360108395538301344360975931691897844900 ≤ centralWords.length
  omega

theorem list_large_family (l : List α) (hnd : l.Nodup) (f : α → Nat) (Q T : Nat)
    (hQ : 0 < Q) (hT : 0 < T) (hf : ∀ x ∈ l, f x < Q) (hsize : Q * T ≤ l.length) :
    ∃ w : Fin T → α, (∀ a b, w a = w b → a = b) ∧
      (∀ a, w a ∈ l) ∧ (∀ a b, f (w a) = f (w b)) := by
  obtain ⟨j, _, hj⟩ := large_fiber l f Q T hQ hT hf hsize
  let layer := l.filter (fun x => decide (f x = j))
  let rank : Fin T → Fin layer.length := fun a => ⟨a.val, Nat.lt_of_lt_of_le a.isLt hj⟩
  let w : Fin T → α := fun a => layer.get (rank a)
  have hm (a : Fin T) : w a ∈ layer := List.get_mem layer (rank a).val (rank a).isLt
  have hr (a : Fin T) : w a ∈ l ∧ f (w a) = j := by
    have h := List.mem_filter.mp (hm a)
    exact ⟨h.1, of_decide_eq_true h.2⟩
  refine ⟨w, ?_, fun a => (hr a).1, fun a b => (hr a).2.trans (hr b).2.symm⟩
  intro a b hab
  apply Fin.ext
  have hnd' : layer.Nodup := (List.filter_sublist l).nodup hnd
  have he : layer[(rank a).val]? = layer[(rank b).val]? := by
    rw [List.getElem?_eq_getElem (rank a).isLt, List.getElem?_eq_getElem (rank b).isLt]
    exact congrArg some hab
  exact List.getElem?_inj (rank a).isLt hnd' he

theorem central_family :
    ∃ w : Fin centralT → Word 190 17,
      (∀ a b, w a = w b → a = b) ∧ (∀ a b, norm (w a) = norm (w b)) := by
  have hc (w : Word 190 17) (hw : w ∈ centralWords) :
      15568 ≤ energyIndex (A := 95) w ∧ energyIndex (A := 95) w ≤ 35568 := by
    exact of_decide_eq_true (List.mem_filter.mp hw).2
  let f := fun w : Word 190 17 => energyIndex (A := 95) w - 15568
  obtain ⟨w, hi, hm, he⟩ := list_large_family centralWords
    ((List.filter_sublist (words 17)).nodup (words_nodup 17)) f 20001 centralT
    (by decide) (by decide) (by intro w hw; have := hc w hw; dsimp [f]; omega)
    central_capacity
  refine ⟨w, hi, ?_⟩
  intro a b
  have ha := hc (w a) (hm a)
  have hb := hc (w b) (hm b)
  have hh := he a b
  dsimp [f] at hh
  have heq : energyIndex (A := 95) (w a) = energyIndex (A := 95) (w b) := by omega
  rw [norm_energy (A := 95) (by decide), norm_energy (A := 95) (by decide), heq]

theorem central_packing :
    ∃ u v : Fin centralT → Nat,
      (∀ a, u a < 379 ^ 17 ∧ v a < 379 ^ 17) ∧
      (∀ a c, u a = u c → a = c) ∧
      (∀ a c, v a = v c → a = c) ∧
      (∀ a c e, u a + u c + v e = 379 ^ 17 - 1 ↔ a = c ∧ c = e) := by
  obtain ⟨w, hi, hn⟩ := central_family
  let u := fun a => encode 379 (w a)
  let v := fun a => 379 ^ 17 - 1 - 2 * u a
  refine ⟨u, v, ?_, ?_, ?_, ?_⟩
  · intro a
    exact position_bounds (w a) (by decide) (by decide)
  · intro a c h
    exact hi a c (encode_injective (w a) (w c) (by decide) (by decide) h)
  · intro a c h
    exact hi a c (right_injective (w a) (w c) (by decide) (by decide) h)
  · intro a c e
    have hm := sphere_matching (w a) (w c) (w e) (b := 379) (by decide) (by decide)
      (hn a e) (hn c e)
    constructor
    · intro h
      obtain ⟨hac, hce⟩ := hm.mp h
      exact ⟨hi a c hac, hi c e hce⟩
    · rintro ⟨rfl, rfl⟩
      exact hm.mpr ⟨rfl, rfl⟩

theorem central_packing_binomial :
    ∃ u v : Fin (binomialValue (binomialValue 51 13) 3) → Nat,
      (∀ a, u a < 379 ^ 17 ∧ v a < 379 ^ 17) ∧
      (∀ a c, u a = u c → a = c) ∧
      (∀ a c, v a = v c → a = c) ∧
      (∀ a c e, u a + u c + v e = 379 ^ 17 - 1 ↔ a = c ∧ c = e) := by
  rw [← HeilbronnTuned.tunedT_binomial]
  exact central_packing

theorem moment_value :
    secondMoment 17 = 16860944176870366476166331396160000000000000000 := by decide

theorem capacity_arithmetic :
    secondMoment 17 + (20001 * centralT : Nat) * (10001 ^ 2 : Nat) ≤
      (190 ^ 17 : Nat) * (10001 ^ 2 : Nat) := by decide

theorem central_gain :
    284 * (498 * 379 ^ 17 + 7) < 100 * (498 * 403 ^ 17 + 7) ∧
    100 * (498 * 403 ^ 17 + 7) < 285 * (498 * 379 ^ 17 + 7) := by decide

#print axioms digits_nodup
#print axioms digit_mean
#print axioms digit_square
#print axioms words_length
#print axioms words_nodup
#print axioms words_mean
#print axioms words_square
#print axioms score_energy
#print axioms central_count_bound
#print axioms central_capacity
#print axioms central_family
#print axioms central_packing
#print axioms central_packing_binomial
#print axioms moment_value
#print axioms capacity_arithmetic
#print axioms central_gain

end HeilbronnCentral
