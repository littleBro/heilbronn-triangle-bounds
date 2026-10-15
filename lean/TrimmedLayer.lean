import TrimmedLayerRows3

/-! Generated recurrence proof; every finite transition is kernel-checked. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace HeilbronnTrimmedLayer
open HeilbronnInterval HeilbronnTrimmedData

def alphabets : List Nat := [4, 4, 4, 4, 4, 4, 5, 4, 5, 5, 5]
def lower : Nat := 133535493048
def upper : Nat := 10996285570280

theorem below_lower : belowCount alphabets 32 lower = 10308152 :=
  row_22_correct 32 (by decide)

theorem below_upper : belowCount alphabets 32 upper = 860613752 :=
  row_43_correct 32 (by decide)

theorem exact_interval_count : intervalCount alphabets 32 lower upper = 850305600 := by
  have h := interval_partition alphabets 32 lower upper (by decide)
  rw [below_lower, below_upper] at h
  omega

#print axioms below_lower
#print axioms below_upper
#print axioms exact_interval_count

end HeilbronnTrimmedLayer
