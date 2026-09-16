import RealRooted.Multiaffine.Rayleigh
import RealRooted.Mathlib.Algebra.MvPolynomial.EvalOnVars
import RealRooted.Mathlib.Algebra.MvPolynomial.Specialize
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Monad

/-!
# Two-coordinate affine slices of multiaffine polynomials

This file packages the coefficient-ring algebra for restricting a polynomial
to affine motion in two coordinates.  Stability consequences belong in the
multivariate-stability layer.
-/

namespace MvPolynomial

noncomputable section

/-- Restrict a multivariate polynomial to affine motion from `x` in
coordinates `i` and `j`.  The two displacement variables are indexed by
`Fin 2`. -/
def twoCoordinateAffineSlice {R σ : Type*} [CommSemiring R]
    [DecidableEq σ] (x : σ → R) (i j : σ) (P : MvPolynomial σ R) :
    MvPolynomial (Fin 2) R :=
  bind₁ (fun k =>
    if k = i then C (x i) + X 0
    else if k = j then C (x j) + X 1
    else C (x k)) P

/-- The variables of `P` other than the two active coordinates.  This finite
list is the canonical boundary-specialization list for a two-coordinate
slice, even when the ambient variable type is infinite. -/
def twoCoordinateSpectators {R σ : Type*} [CommSemiring R]
    [DecidableEq σ] (P : MvPolynomial σ R) (i j : σ) : List σ :=
  ((P.vars.erase i).erase j).toList

/-- Mapping coefficients commutes with taking a two-coordinate affine
slice. -/
theorem map_twoCoordinateAffineSlice {R S σ : Type*}
    [CommSemiring R] [CommSemiring S] [DecidableEq σ]
    (f : R →+* S) (x : σ → R) (i j : σ) (P : MvPolynomial σ R) :
    map f (twoCoordinateAffineSlice x i j P) =
      twoCoordinateAffineSlice (fun k => f (x k)) i j (map f P) := by
  simp only [twoCoordinateAffineSlice, map_bind₁]
  apply congrArg (fun g : σ → MvPolynomial (Fin 2) S =>
    bind₁ g (map f P))
  funext k
  by_cases hki : k = i
  · simp [hki]
  · by_cases hkj : k = j
    · subst k
      simp [hki]
    · simp [hki, hkj]

/-- Specializing every variable of `P` except `i` and `j` gives the same
evaluation as retaining only the two corresponding coordinates of the
assignment. -/
theorem eval_specializeAtList_twoCoordinateSpectators {R σ : Type*}
    [CommSemiring R] [DecidableEq σ] (x z : σ → R) (i j : σ)
    (hij : i ≠ j) (P : MvPolynomial σ R) :
    eval z (specializeAtList x (twoCoordinateSpectators P i j) P) =
      eval (Function.update (Function.update x i (z i)) j (z j)) P := by
  rw [eval_specializeAtList]
  apply eval_eq_of_eq_on_vars
  intro k hk
  by_cases hki : k = i
  · subst k
    rw [specializeAtListAssignment_eq_of_not_mem]
    · simp [hij]
    · simp [twoCoordinateSpectators]
  · by_cases hkj : k = j
    · subst k
      rw [specializeAtListAssignment_eq_of_not_mem]
      · simp
      · simp [twoCoordinateSpectators]
    · rw [specializeAtListAssignment_eq_of_mem]
      · simp [hki, hkj]
      · simp [twoCoordinateSpectators, hk, hki, hkj]

/-- Evaluating a two-coordinate affine slice is evaluation at the
corresponding updated point. -/
@[simp] theorem eval_twoCoordinateAffineSlice {R σ : Type*}
    [CommSemiring R] [DecidableEq σ] (x : σ → R) (i j : σ)
    (hij : i ≠ j) (P : MvPolynomial σ R) (z : Fin 2 → R) :
    eval z (twoCoordinateAffineSlice x i j P) =
      eval
        (Function.update
          (Function.update x i (x i + z 0)) j (x j + z 1)) P := by
  simp only [twoCoordinateAffineSlice, eval, eval₂Hom_bind₁]
  apply eval₂Hom_congr rfl
  · funext k
    by_cases hki : k = i
    · subst k
      simp [hij]
    · by_cases hkj : k = j
      · subst k
        simp [hki]
      · simp [hki, hkj]
  · rfl

/-- Affine evaluation around a base point uses the displacement from that
point as its linear parameter. -/
theorem IsMultiaffine.eval_update_add_eq {R σ : Type*} [CommRing R]
    [DecidableEq σ] {P : MvPolynomial σ R} (hP : IsMultiaffine P)
    (i : σ) (x : σ → R) (s : R) :
    eval (Function.update x i (x i + s)) P =
      eval x P + eval x (MvPolynomial.pderiv i P) * s := by
  have hshift := hP.eval_update_eq_eval_pderiv_mul_add i x (x i + s)
  have hbase := hP.eval_update_eq_eval_pderiv_mul_add i x (x i)
  rw [Function.update_eq_self] at hbase
  rw [hshift, hbase]
  ring

/-- A two-coordinate affine slice of a multiaffine polynomial has the exact
four-coefficient Taylor form at its base point. -/
theorem IsMultiaffine.twoCoordinateAffineSlice_eq {R σ : Type*}
    [CommRing R] [DecidableEq σ] [IsDomain R] [Infinite R]
    {P : MvPolynomial σ R} (hP : IsMultiaffine P)
    (x : σ → R) (i j : σ) (hij : i ≠ j) :
    twoCoordinateAffineSlice x i j P =
      MvPolynomial.C (eval x P) +
        MvPolynomial.C (eval x (MvPolynomial.pderiv i P)) *
          MvPolynomial.X 0 +
        MvPolynomial.C (eval x (MvPolynomial.pderiv j P)) *
          MvPolynomial.X 1 +
        MvPolynomial.C (eval x (MvPolynomial.pderiv i
          (MvPolynomial.pderiv j P))) * MvPolynomial.X 0 *
          MvPolynomial.X 1 := by
  apply MvPolynomial.funext
  intro z
  rw [eval_twoCoordinateAffineSlice x i j hij]
  have hj := hP.eval_update_add_eq j
    (Function.update x i (x i + z 0)) (z 1)
  simp only [Function.update_of_ne (Ne.symm hij)] at hj
  rw [hj]
  rw [hP.eval_update_add_eq i x (z 0)]
  rw [(hP.pderiv j).eval_update_add_eq i x (z 0)]
  simp only [map_add, map_mul, eval_C, eval_X]
  ring

/-- The Rayleigh difference of a two-coordinate affine slice is the constant
given by the original Rayleigh difference at its base point. -/
theorem IsMultiaffine.rayleighDifference_twoCoordinateAffineSlice
    {R σ : Type*} [CommRing R] [DecidableEq σ] [IsDomain R] [Infinite R]
    {P : MvPolynomial σ R} (hP : IsMultiaffine P)
    (x : σ → R) (i j : σ) (hij : i ≠ j) :
    rayleighDifference (twoCoordinateAffineSlice x i j P) 0 1 =
      MvPolynomial.C (eval x (rayleighDifference P i j)) := by
  rw [hP.twoCoordinateAffineSlice_eq x i j hij]
  rw [rayleighDifference_bivariate (0 : Fin 2) 1 (by decide)]
  congr 1
  rw [eval_rayleighDifference]

end

end MvPolynomial
