import RealRooted.PolyaFrequencyConvolution.Basic
import RealRooted.PolyaFrequencyConvolution.GeometricScaling
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Finite supersymmetric product coefficients

This file defines the coefficient sequence of the finite product

`prod_i (1 + x_i z) / prod_j (1 - y_j z)`

as a formal power series and proves that it is Pólya-frequency when all
parameters are nonnegative. No infinite-product claim is made here.
-/

open Polynomial

namespace RealRooted.BrandenVecchi

noncomputable section

/-- The numerator factor `1 + x z`, embedded into formal power series. -/
def supersymmetricNumeratorFactor (x : ℝ) : PowerSeries ℝ :=
  ((1 + C x * X : ℝ[X]) : PowerSeries ℝ)

/-- The geometric denominator factor `(1 - y z)⁻¹`. -/
def supersymmetricDenominatorFactor (y : ℝ) : PowerSeries ℝ :=
  PowerSeries.rescale y (PowerSeries.mk 1)

/-- The finite supersymmetric product as a formal power series. -/
def finiteSupersymmetricSeries (xs ys : List ℝ) : PowerSeries ℝ :=
  (xs.map supersymmetricNumeratorFactor).prod *
    (ys.map supersymmetricDenominatorFactor).prod

/-- Coefficients of the finite supersymmetric product. -/
def finiteSupersymmetricCoeff (xs ys : List ℝ) (n : ℕ) : ℝ :=
  PowerSeries.coeff n (finiteSupersymmetricSeries xs ys)

@[simp]
theorem coeff_supersymmetricNumeratorFactor (x : ℝ) (n : ℕ) :
    PowerSeries.coeff n (supersymmetricNumeratorFactor x) =
      (1 + C x * X : ℝ[X]).coeff n :=
  Polynomial.coeff_coe (1 + C x * X : ℝ[X]) n

@[simp]
theorem coeff_supersymmetricDenominatorFactor (y : ℝ) (n : ℕ) :
    PowerSeries.coeff n (supersymmetricDenominatorFactor y) = y ^ n := by
  simp [supersymmetricDenominatorFactor]

@[simp]
theorem constantCoeff_supersymmetricNumeratorFactor (x : ℝ) :
    PowerSeries.constantCoeff (supersymmetricNumeratorFactor x) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp

@[simp]
theorem constantCoeff_supersymmetricDenominatorFactor (y : ℝ) :
    PowerSeries.constantCoeff (supersymmetricDenominatorFactor y) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp

/-- The claimed denominator factor is an exact formal inverse. -/
theorem supersymmetricDenominatorFactor_mul_one_sub (y : ℝ) :
    supersymmetricDenominatorFactor y *
      (1 - PowerSeries.C y * PowerSeries.X) = 1 := by
  have h := congrArg (PowerSeries.rescale y)
    (PowerSeries.mk_one_mul_one_sub_eq_one ℝ)
  simpa [supersymmetricDenominatorFactor, map_sub,
    PowerSeries.rescale_X] using h

private theorem denominatorFactors_mul_denominators : ∀ ys : List ℝ,
    (ys.map supersymmetricDenominatorFactor).prod *
      (ys.map fun y => 1 - PowerSeries.C y * PowerSeries.X).prod = 1
  | [] => by simp
  | y :: ys => by
      rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons]
      rw [show supersymmetricDenominatorFactor y *
          (ys.map supersymmetricDenominatorFactor).prod *
          ((1 - PowerSeries.C y * PowerSeries.X) *
            (ys.map fun z => 1 - PowerSeries.C z * PowerSeries.X).prod) =
          supersymmetricDenominatorFactor y *
            (1 - PowerSeries.C y * PowerSeries.X) *
            ((ys.map supersymmetricDenominatorFactor).prod *
              (ys.map fun z =>
                1 - PowerSeries.C z * PowerSeries.X).prod) by ring]
      rw [supersymmetricDenominatorFactor_mul_one_sub,
        denominatorFactors_mul_denominators]
      simp

/-- Literal finite rational-product identity for the coefficient series. -/
theorem finiteSupersymmetricSeries_mul_denominators (xs ys : List ℝ) :
    finiteSupersymmetricSeries xs ys *
        (ys.map fun y => 1 - PowerSeries.C y * PowerSeries.X).prod =
      (xs.map supersymmetricNumeratorFactor).prod := by
  rw [finiteSupersymmetricSeries, mul_assoc,
    denominatorFactors_mul_denominators, mul_one]

private theorem isPolyaFreqSeq_coeff_list_prod
    (fs : List (PowerSeries ℝ))
    (hfs : ∀ f ∈ fs, IsPolyaFreqSeq fun n => PowerSeries.coeff n f) :
    IsPolyaFreqSeq fun n => PowerSeries.coeff n fs.prod := by
  induction fs with
  | nil =>
      convert IsPolyaFreqSeq.one using 1
      funext n
      simp [Polynomial.coeff_one]
  | cons f fs ih =>
      have hf := hfs f (by simp)
      have htail : ∀ g ∈ fs,
          IsPolyaFreqSeq fun n => PowerSeries.coeff n g := by
        intro g hg
        exact hfs g (by simp [hg])
      have hconv := hf.natCauchyConvolution (ih htail)
      convert hconv using 1
      funext n
      exact coeff_mul_eq_natCauchyConvolution f fs.prod n

private theorem numeratorFactor_isPolyaFreqSeq
    (x : ℝ) (hx : 0 ≤ x) :
    IsPolyaFreqSeq fun n =>
      PowerSeries.coeff n (supersymmetricNumeratorFactor x) := by
  have hbase : IsPolyaFreqSeq (X + 1 : ℝ[X]).coeff := by
    convert IsPolyaFreqSeq.linear (r := (-1 : ℝ)) (by norm_num) using 1
    funext n
    simp
  have hscaled := hbase.geometricScale x hx
  convert hscaled using 1
  funext n
  cases n with
  | zero => simp [geometricScale]
  | succ n =>
      cases n with
      | zero => simp [geometricScale, Polynomial.coeff_one]
      | succ n => simp [geometricScale, coeff_X, coeff_one]

private theorem denominatorFactor_isPolyaFreqSeq
    (y : ℝ) (hy : 0 ≤ y) :
    IsPolyaFreqSeq fun n =>
      PowerSeries.coeff n (supersymmetricDenominatorFactor y) := by
  simpa using geometric_isPolyaFreqSeq y hy

/-- Finite supersymmetric product coefficients are Pólya-frequency for
nonnegative parameters. -/
theorem finiteSupersymmetricCoeff_isPolyaFreqSeq
    {xs ys : List ℝ} (hxs : ∀ x ∈ xs, 0 ≤ x)
    (hys : ∀ y ∈ ys, 0 ≤ y) :
    IsPolyaFreqSeq (finiteSupersymmetricCoeff xs ys) := by
  have hproduct := isPolyaFreqSeq_coeff_list_prod
    (xs.map supersymmetricNumeratorFactor ++
      ys.map supersymmetricDenominatorFactor) (by
        intro f hf
        simp only [List.mem_append, List.mem_map] at hf
        rcases hf with ⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩
        · exact numeratorFactor_isPolyaFreqSeq x (hxs x hx)
        · exact denominatorFactor_isPolyaFreqSeq y (hys y hy))
  change IsPolyaFreqSeq fun n => PowerSeries.coeff n
    ((xs.map supersymmetricNumeratorFactor).prod *
      (ys.map supersymmetricDenominatorFactor).prod)
  simpa only [List.prod_append] using hproduct

@[simp]
theorem finiteSupersymmetricCoeff_zero (xs ys : List ℝ) :
    finiteSupersymmetricCoeff xs ys 0 = 1 := by
  rw [finiteSupersymmetricCoeff, finiteSupersymmetricSeries,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
    map_list_prod, map_list_prod]
  have hx :
      (xs.map (PowerSeries.constantCoeff ∘ supersymmetricNumeratorFactor)).prod = 1 := by
    induction xs with
    | nil => simp
    | cons x xs ih => simp [ih]
  have hy :
      (ys.map (PowerSeries.constantCoeff ∘ supersymmetricDenominatorFactor)).prod = 1 := by
    induction ys with
    | nil => simp
    | cons y ys ih => simp [ih]
  rw [List.map_map, List.map_map, hx, hy, mul_one]

end

end RealRooted.BrandenVecchi
