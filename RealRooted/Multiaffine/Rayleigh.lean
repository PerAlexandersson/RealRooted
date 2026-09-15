import RealRooted.Mathlib.Algebra.MvPolynomial.PDeriv
import RealRooted.Multiaffine
import Mathlib.Data.Real.Basic

/-!
# Rayleigh differences of multiaffine polynomials

This file provides the coefficient-ring algebra for the Rayleigh criterion.
The stability implications belong in the multivariate-stability layer; the
definitions and identities here require no root theory.
-/

namespace MvPolynomial

noncomputable section

/-- The Rayleigh difference in coordinates `i` and `j`. -/
def rayleighDifference {R σ : Type*} [CommRing R]
    (P : MvPolynomial σ R) (i j : σ) : MvPolynomial σ R :=
  pderiv i P * pderiv j P - P * pderiv i (pderiv j P)

/-- Rayleigh differences are symmetric in their two coordinates. -/
theorem rayleighDifference_comm {R σ : Type*} [CommRing R]
    (P : MvPolynomial σ R) (i j : σ) :
    rayleighDifference P i j = rayleighDifference P j i := by
  rw [rayleighDifference, rayleighDifference, pderiv_comm]
  ring

/-- Rayleigh differences commute with coefficient maps. -/
theorem rayleighDifference_map {R S σ : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (P : MvPolynomial σ R) (i j : σ) :
    rayleighDifference (map f P) i j =
      map f (rayleighDifference P i j) := by
  simp only [rayleighDifference, pderiv_map, map_mul, map_sub]

/-- Rayleigh differences commute with injective variable renamings. -/
theorem rayleighDifference_rename {R σ τ : Type*} [CommRing R]
    (f : σ → τ) (hf : Function.Injective f)
    (P : MvPolynomial σ R) (i j : σ) :
    rayleighDifference (rename f P) (f i) (f j) =
      rename f (rayleighDifference P i j) := by
  simp only [rayleighDifference, pderiv_rename hf, map_mul, map_sub]

/-- Evaluation of a Rayleigh difference is the corresponding scalar
determinant. -/
theorem eval_rayleighDifference {R σ : Type*} [CommRing R]
    (z : σ → R) (P : MvPolynomial σ R) (i j : σ) :
    eval z (rayleighDifference P i j) =
      eval z (pderiv i P) * eval z (pderiv j P) -
        eval z P * eval z (pderiv i (pderiv j P)) := by
  simp only [rayleighDifference, map_sub, map_mul]

/-- The Rayleigh difference of a bivariate multiaffine coefficient form is
its two-by-two coefficient determinant. -/
theorem rayleighDifference_bivariate {R σ : Type*} [CommRing R]
    (i j : σ) (hij : i ≠ j) (a b c d : R) :
    rayleighDifference
        (C a + C b * X i + C c * X j + C d * X i * X j) i j =
      C (b * c - a * d) := by
  classical
  simp only [rayleighDifference, map_add, pderiv_C, pderiv_mul,
    pderiv_X_self, pderiv_X_of_ne hij, pderiv_X_of_ne (Ne.symm hij),
    zero_mul, mul_zero, zero_add, add_zero, mul_one]
  calc
    _ = C b * C c - C a * C d := by ring
    _ = C (b * c - a * d) := by simp only [map_sub, map_mul]

/-- A bivariate coefficient form in two distinct coordinates is
multiaffine. -/
theorem isMultiaffine_bivariate {R σ : Type*} [CommRing R] [Nontrivial R]
    (i j : σ) (hij : i ≠ j) (a b c d : R) :
    IsMultiaffine
      (C a + C b * X i + C c * X j + C d * X i * X j) := by
  classical
  have hlast : IsMultiaffine (C d * X i * X j : MvPolynomial σ R) := by
    have hprod := (IsMultiaffine.prod_X (R := R) ({i, j} : Finset σ)).C_mul d
    simpa [hij, Ne.symm hij, mul_assoc] using hprod
  exact (((IsMultiaffine.C a).add ((IsMultiaffine.X i).C_mul b)).add
    ((IsMultiaffine.X j).C_mul c)).add hlast

/-- In a multiaffine polynomial, the same-coordinate Rayleigh difference is
the square of the corresponding partial derivative. -/
theorem IsMultiaffine.rayleighDifference_self {R σ : Type*} [CommRing R]
    {P : MvPolynomial σ R} (hP : IsMultiaffine P) (i : σ) :
    rayleighDifference P i i = MvPolynomial.pderiv i P ^ 2 := by
  rw [rayleighDifference, hP.pderiv_pderiv_self_eq_zero]
  ring

/-- A real polynomial is Rayleigh when every Rayleigh difference is
nonnegative at every real point. -/
def IsRayleigh {σ : Type*} (P : MvPolynomial σ ℝ) : Prop :=
  ∀ i j x, 0 ≤ eval x (rayleighDifference P i j)

/-- Same-coordinate Rayleigh inequalities hold automatically for a
multiaffine real polynomial. -/
theorem IsMultiaffine.eval_rayleighDifference_self_nonneg
    {σ : Type*} {P : MvPolynomial σ ℝ} (hP : IsMultiaffine P)
    (i : σ) (x : σ → ℝ) :
    0 ≤ eval x (rayleighDifference P i i) := by
  rw [hP.rayleighDifference_self, map_pow]
  positivity

end

end MvPolynomial
