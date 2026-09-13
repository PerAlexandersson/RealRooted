import RealRooted.BrandenVecchi.SupersymmetricCoefficients
import RealRooted.PFPolynomial

/-!
# Finite factor certificates for rational tiling kernels

This file packages the finite products used as inputs to the two-kernel
theorem.  The background series is a product of nonnegative geometric factors;
the marked series is a positive scalar, a positive-order shift, and a finite
product of optional-rise factors.
-/

open Polynomial

namespace RealRooted.BrandenLeite

noncomputable section

/-- The polynomial `c * ∏ x ∈ xs, (1 + x * X)`. -/
def optionalRisePolynomial (c : ℝ) (xs : List ℝ) : ℝ[X] :=
  C c * (xs.map fun x => 1 + C x * X).prod

/-- The formal series `∏ y ∈ ys, (1 - y * X)⁻¹`. -/
def rationalBackgroundSeries (ys : List ℝ) : PowerSeries ℝ :=
  BrandenVecchi.finiteSupersymmetricSeries [] ys

/-- The positive-order marked series `X^r * c * ∏ x ∈ xs, (1 + x * X)`. -/
def markedFactorSeries (c : ℝ) (r : ℕ) (xs : List ℝ) : PowerSeries ℝ :=
  ((X ^ r * optionalRisePolynomial c xs : ℝ[X]) : PowerSeries ℝ)

/-- Nonnegative optional-rise factors and a positive scale form a PF
polynomial. -/
theorem optionalRisePolynomial_isPFPolynomial
    {c : ℝ} (hc : 0 < c) {xs : List ℝ}
    (hxs : ∀ x ∈ xs, 0 ≤ x) :
    IsPFPolynomial (optionalRisePolynomial c xs) := by
  have hproduct : IsPFPolynomial
      (xs.map fun x => (1 + C x * X : ℝ[X])).prod := by
    induction xs with
    | nil => simpa using IsPFPolynomial.one
    | cons x xs ih =>
        have hx : 0 ≤ x := hxs x (by simp)
        have htail : ∀ y ∈ xs, 0 ≤ y := by
          intro y hy
          exact hxs y (by simp [hy])
        have hfactor : IsPFPolynomial (1 + C x * X : ℝ[X]) := by
          by_cases hx0 : x = 0
          · simpa [hx0] using IsPFPolynomial.one
          · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
            have heq : (1 + C x * X : ℝ[X]) =
                C x * (X + C x⁻¹) := by
              rw [mul_add, ← C_mul]
              simp [hx0]
              ring
            rw [heq]
            exact (isPFPolynomial_X_add_C (inv_nonneg.mpr hx)).const_mul hxpos
        simpa using hfactor.mul (ih htail)
  simpa [optionalRisePolynomial] using hproduct.const_mul hc

/-- Coefficients of a finite product of nonnegative geometric factors are
Pólya-frequency. -/
theorem rationalBackgroundSeries_coeff_isPolyaFreqSeq
    {ys : List ℝ} (hys : ∀ y ∈ ys, 0 ≤ y) :
    IsPolyaFreqSeq (fun n =>
      PowerSeries.coeff n (rationalBackgroundSeries ys)) := by
  change IsPolyaFreqSeq
    (BrandenVecchi.finiteSupersymmetricCoeff [] ys)
  exact BrandenVecchi.finiteSupersymmetricCoeff_isPolyaFreqSeq
    (xs := []) (ys := ys) (by simp) hys

/-- Every finite geometric background product has constant coefficient one. -/
@[simp]
theorem constantCoeff_rationalBackgroundSeries (ys : List ℝ) :
    PowerSeries.constantCoeff (rationalBackgroundSeries ys) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simpa [rationalBackgroundSeries,
    BrandenVecchi.finiteSupersymmetricCoeff] using
    BrandenVecchi.finiteSupersymmetricCoeff_zero ([] : List ℝ) ys

/-- The geometric background product is an exact formal inverse of its finite
denominator product. -/
theorem rationalBackgroundSeries_mul_denominators (ys : List ℝ) :
    rationalBackgroundSeries ys *
        (ys.map fun y =>
          1 - PowerSeries.C y * PowerSeries.X).prod = 1 := by
  simpa [rationalBackgroundSeries,
    BrandenVecchi.finiteSupersymmetricSeries] using
    BrandenVecchi.finiteSupersymmetricSeries_mul_denominators
      ([] : List ℝ) ys

/-- The marked-factor series has the expected guarded coefficient formula. -/
theorem coeff_markedFactorSeries (c : ℝ) (r : ℕ) (xs : List ℝ) (n : ℕ) :
    PowerSeries.coeff n (markedFactorSeries c r xs) =
      if r ≤ n then (optionalRisePolynomial c xs).coeff (n - r) else 0 := by
  rw [markedFactorSeries, Polynomial.coeff_coe,
    Polynomial.coeff_X_pow_mul']

/-- A positive-order marked-factor series has zero constant coefficient. -/
@[simp]
theorem constantCoeff_markedFactorSeries
    (c : ℝ) {r : ℕ} (hr : r ≠ 0) (xs : List ℝ) :
    PowerSeries.constantCoeff (markedFactorSeries c r xs) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    coeff_markedFactorSeries]
  simp [Nat.not_le_of_lt (Nat.pos_of_ne_zero hr)]

/-- The coefficient sequence of a nonnegatively factored marked series is
Pólya-frequency. -/
theorem markedFactorSeries_coeff_isPolyaFreqSeq
    {c : ℝ} (hc : 0 < c) (r : ℕ) {xs : List ℝ}
    (hxs : ∀ x ∈ xs, 0 ≤ x) :
    IsPolyaFreqSeq (fun n =>
      PowerSeries.coeff n (markedFactorSeries c r xs)) := by
  simpa only [markedFactorSeries, Polynomial.coeff_coe] using
    ((isPFPolynomial_X_pow r).mul
      (optionalRisePolynomial_isPFPolynomial hc hxs)).to_sequence

/-- Marked-factor coefficients vanish below their prescribed order. -/
theorem coeff_markedFactorSeries_eq_zero_of_lt
    (c : ℝ) (xs : List ℝ) {r n : ℕ} (hnr : n < r) :
    PowerSeries.coeff n (markedFactorSeries c r xs) = 0 := by
  rw [coeff_markedFactorSeries]
  simp [Nat.not_le_of_lt hnr]

@[simp]
theorem optionalRisePolynomial_nil (c : ℝ) :
    optionalRisePolynomial c [] = C c := by
  simp [optionalRisePolynomial]

@[simp]
theorem rationalBackgroundSeries_nil :
    rationalBackgroundSeries [] = 1 := by
  simp [rationalBackgroundSeries,
    BrandenVecchi.finiteSupersymmetricSeries]

end

end RealRooted.BrandenLeite
