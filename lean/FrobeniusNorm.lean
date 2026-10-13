import FrobeniusOrbits
import BilinearNorm

/-! Galois equivariance of the signed determinant terms and an invariant
    projection. These let us collect equal projected terms along orbits. -/

open Finset Equiv Polynomial

namespace HeilbronnFrobenius
open HeilbronnNorm

variable {G R : Type*} [Group G] [Fintype G] [CommRing R]

noncomputable def patternSign (w : Pattern G) : R := ∏ g, signR (w.1 g)

lemma signR_inv (p : Equiv.Perm Row) : signR (R := R) p⁻¹ = signR p := by
  simp [signR, Equiv.Perm.sign_inv]

lemma signR_sq (p : Equiv.Perm Row) : signR (R := R) p ^ 2 = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign p) with h | h <;> norm_num [signR, h]

lemma signR_thirteen (p : Equiv.Perm Row) : signR (R := R) p ^ 13 = signR p := by
  rw [show 13 = 12 + 1 from rfl, pow_succ, signR_pow_twelve, one_mul]

lemma patternSign_rotate (hc : Fintype.card G = 13) (a : G) (w : Pattern G) :
    patternSign (R := R) (a • w) = patternSign w * signR (w.1 a⁻¹) := by
  classical
  simp only [patternSign, rotate_apply, signR_mul, signR_inv, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, hc, signR_thirteen]
  exact congrArg (fun z => z * signR (R := R) (w.1 a⁻¹))
    (Equiv.prod_comp (Equiv.mulLeft a⁻¹) (fun g => signR (R := R) (w.1 g)))

variable {F K X : Type*} [Field F] [Field K] [Algebra F K]
  [FiniteDimensional F K]

abbrev Gal := K ≃ₐ[F] K

noncomputable def patternCoordinate (g : Row → X → K) (w : Pattern (Gal (F := F) (K := K)))
    (i : Row) (x : X) : K := ∏ a : Gal, a (g (w.1 a i) x)

lemma patternCoordinate_rotate (a : Gal (F := F) (K := K))
    (g : Row → X → K) (w : Pattern (Gal (F := F) (K := K))) (i : Row) (x : X) :
    patternCoordinate g (a • w) i x =
      a (patternCoordinate g w ((w.1 a⁻¹)⁻¹ i) x) := by
  classical
  simp only [patternCoordinate, map_prod, rotate_apply, Equiv.Perm.coe_mul, Function.comp_apply]
  apply Fintype.prod_equiv (Equiv.mulLeft a⁻¹)
  intro σ
  simp only [Equiv.coe_mulLeft, AlgEquiv.mul_apply]
  exact (a.apply_symm_apply _).symm

noncomputable def patternTerm (g : Row → X → K) (x : Row → X)
    (w : Pattern (Gal (F := F) (K := K))) : K :=
  patternSign w * Matrix.det (fun i j => patternCoordinate g w i (x j))

lemma patternTerm_rotate (hc : Fintype.card (Gal (F := F) (K := K)) = 13)
    (a : Gal (F := F) (K := K)) (g : Row → X → K) (x : Row → X)
    (w : Pattern (Gal (F := F) (K := K))) :
    patternTerm g x (a • w) = a (patternTerm g x w) := by
  classical
  have hs : a (patternSign w : K) = patternSign w := by simp [patternSign, signR]
  have hd : Matrix.det (fun i j => patternCoordinate g (a • w) i (x j)) =
      signR (w.1 a⁻¹) * a (Matrix.det (fun i j => patternCoordinate g w i (x j))) := by
    simp_rw [patternCoordinate_rotate]
    have hm := a.map_det (fun i j => patternCoordinate g w ((w.1 a⁻¹)⁻¹ i) (x j))
    change a (Matrix.det (fun i j => patternCoordinate g w ((w.1 a⁻¹)⁻¹ i) (x j))) =
      Matrix.det (fun i j => a (patternCoordinate g w ((w.1 a⁻¹)⁻¹ i) (x j))) at hm
    rw [← hm]
    have hp := Matrix.det_permute ((w.1 a⁻¹)⁻¹)
      (fun i j => patternCoordinate g w i (x j))
    change a ((Matrix.submatrix (fun i j => patternCoordinate g w i (x j))
      ((w.1 a⁻¹)⁻¹ : Equiv.Perm Row) id).det) = _
    rw [hp]
    simp [signR, Equiv.Perm.sign_inv]
  rw [patternTerm, patternSign_rotate hc, hd, patternTerm, map_mul, hs]
  calc
    _ = patternSign w * signR (R := K) (w.1 a⁻¹) ^ 2 *
        a (Matrix.det (fun i j => patternCoordinate g w i (x j))) := by ring
    _ = _ := by rw [signR_sq, mul_one]

lemma patternSign_enumerated (e : Fin 13 ≃ Gal (F := F) (K := K)) (he : e 0 = 1)
    (w : Pattern (Gal (F := F) (K := K))) :
    patternSign (R := K) w = algebraMap F K (orbitSign (patternEquiv _ e he w)) := by
  classical
  rw [patternSign, ← e.prod_comp, Fin.prod_univ_succ]
  simp [he, w.property, patternEquiv, orbitSign, signR]

lemma patternCoordinate_enumerated (e : Fin 13 ≃ Gal (F := F) (K := K)) (he : e 0 = 1)
    (g : Row → X → K) (w : Pattern (Gal (F := F) (K := K))) (i : Row) (x : X) :
    patternCoordinate g w i x = orbitCoordinate e g (patternEquiv _ e he w) i x := by
  classical
  rw [patternCoordinate, ← e.prod_comp, Fin.prod_univ_succ]
  simp [he, w.property, patternEquiv, orbitCoordinate]

theorem norm_pattern_sum [IsGalois F K] (hc : Fintype.card (Gal (F := F) (K := K)) = 13)
    (g : Row → X → K) (x : Row → X) :
    algebraMap F K (Algebra.norm F (Matrix.det (fun i j => g i (x j)))) =
      ∑ w : Pattern (Gal (F := F) (K := K)), patternTerm g x w := by
  classical
  let e := identityEnumeration (Gal (F := F) (K := K)) hc
  have he : e 0 = 1 := identityEnumeration_zero _ hc
  rw [norm_orbit_expansion e g x]
  symm
  apply Fintype.sum_equiv (patternEquiv _ e he)
  intro w
  simp only [patternTerm, patternSign_enumerated e he, patternCoordinate_enumerated e he]

noncomputable def averagedCoord (pb : PowerBasis F K) : K →ₗ[F] F :=
  (13 : F)⁻¹ • ∑ a : Gal (F := F) (K := K), (constantCoord pb).comp a.toLinearMap

lemma averagedCoord_apply (pb : PowerBasis F K) (z : K) :
    averagedCoord pb z = (13 : F)⁻¹ * ∑ a : Gal (F := F) (K := K), constantCoord pb (a z) := by
  simp [averagedCoord, LinearMap.sum_apply]

lemma averagedCoord_base (hc : Fintype.card (Gal (F := F) (K := K)) = 13)
    (h13 : (13 : F) ≠ 0) (pb : PowerBasis F K) (z : F) :
    averagedCoord pb (algebraMap F K z) = z := by
  rw [averagedCoord_apply]
  simp only [AlgEquiv.commutes, constantCoord_algebraMap, Finset.sum_const, Finset.card_univ,
    hc, nsmul_eq_mul]
  norm_num only [Nat.cast_ofNat] at *
  rw [← mul_assoc, inv_mul_cancel₀ h13, one_mul]

theorem averagedCoord_invariant (pb : PowerBasis F K) (a : Gal (F := F) (K := K)) (z : K) :
    averagedCoord pb (a z) = averagedCoord pb z := by
  classical
  simp only [averagedCoord_apply]
  congr 1
  exact Equiv.sum_comp (Equiv.mulRight a) (fun σ : Gal (F := F) (K := K) => constantCoord pb (σ z))

#print axioms patternTerm_rotate
#print axioms norm_pattern_sum
#print axioms averagedCoord_invariant

end HeilbronnFrobenius
