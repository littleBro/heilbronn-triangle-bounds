import PairedExpansion

/-! The 18-form decomposition of Conner--Gesmundo--Landsberg--Ventura,
    arXiv:1909.04785, Theorem 4.1. We clear the second coefficient column
    and check the resulting identity directly, including its factor 3. -/

open Finset Matrix

set_option maxHeartbeats 1000000

namespace HeilbronnEighteen
open HeilbronnNorm

abbrev PairTerm := Fin 6 × Fin 3

variable {R : Type*} [CommRing R]

def rowIndex : Fin 6 → Row → Row :=
  ![![0, 1, 2], ![0, 2, 1], ![1, 0, 2], ![2, 0, 1], ![1, 2, 0], ![2, 1, 0]]

def coefficients (u : R) : Fin 6 → Fin 3 → Row → R :=
  ![![![-u, -1, 1-u], ![u-1, -1, u], ![u-1, 1-u, 1-u]],
    ![![-1, -u, u-1], ![1-u, -u, 1], ![u, -u, -u]],
    ![![-u, 1-u, 1], ![u-1, 1-u, u-1], ![u-1, u, 1]],
    ![![-1, -u, 1-u], ![-1, u-1, u], ![-1, 1, -1]],
    ![![-1, -1, 1], ![1-u, u, 1], ![u, 1-u, 1]],
    ![![1, -u, 1-u], ![u-1, u-1, 1-u], ![1, u-1, u]]]

def pairForm (u : R) (t : PairTerm) (x y : Row → R) : R :=
  ∑ i, coefficients u t.1 t.2 i * (x (rowIndex t.1 i) * y i)

lemma sum_six (f : Fin 6 → R) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_five]
  rfl

lemma cons_five {α : Type*} (x : α) (v : Fin 5 → α) :
    Matrix.vecCons x v (5 : Fin 6) = v 4 := rfl

#print axioms sum_six
#print axioms cons_five

end HeilbronnEighteen
