module

public import RealRooted.TotalPositivity.PFRiordan

/-!
# Pólya-frequency Riordan rows for OEIS A114123

The sequence-specific generating identities and root-location theorem.
-/

@[expose] public section

open Polynomial RealRooted.PFRiordan

noncomputable section

namespace RealRooted.Applications.OEIS.A114123

/-- Coefficients of `(1 + z)^2 / (1 - z)`, the `K`-series for A114123. -/
def kCoeff : ℕ → ℝ :=
  rationalPFCoeff 1 0 [1, 1] [1]

/-- The A114123 `K`-series has the claimed finite rational factorization. -/
theorem mk_kCoeff_mul_one_sub :
    PowerSeries.mk kCoeff * (1 - PowerSeries.X) =
      (1 + PowerSeries.X) ^ 2 := by
  rw [kCoeff, mk_rationalPFCoeff]
  simpa [BrandenVecchi.supersymmetricNumeratorFactor, pow_two] using
    BrandenVecchi.finiteSupersymmetricSeries_mul_denominators
      ([1, 1] : List ℝ) ([1] : List ℝ)

/-- The A114123 rows, equivalently
`[z^n] (1-z) / ((1-z)^2 - X z (1+z)^2)`. -/
def row (n : ℕ) : ℝ[X] :=
  rowPolynomial geometricOneCoeff kCoeff n

/-- Exact generating-series identity
`((1-z)^2 - X z (1+z)^2) F(X,z) = 1-z` for the A114123 rows. -/
theorem denominator_mul_rowGeneratingSeries :
    (BrandenLeite.polynomialLift ((1 - PowerSeries.X) ^ 2) -
        PowerSeries.C X * BrandenLeite.polynomialLift
          (PowerSeries.X * (1 + PowerSeries.X) ^ 2)) *
      rowGeneratingSeries geometricOneCoeff kCoeff =
        BrandenLeite.polynomialLift (1 - PowerSeries.X) := by
  have hd :
      (1 - PowerSeries.X) ^ 2 * PowerSeries.mk geometricOneCoeff =
        1 - PowerSeries.X := by
    calc
      (1 - PowerSeries.X) ^ 2 * PowerSeries.mk geometricOneCoeff =
          (1 - PowerSeries.X) *
            (PowerSeries.mk geometricOneCoeff * (1 - PowerSeries.X)) := by ring
      _ = 1 - PowerSeries.X := by rw [mk_geometricOneCoeff_mul_one_sub]; ring
  have hK :
      PowerSeries.X * (1 - PowerSeries.X) *
          PowerSeries.mk kCoeff =
        PowerSeries.X * (1 + PowerSeries.X) ^ 2 := by
    calc
      PowerSeries.X * (1 - PowerSeries.X) *
          PowerSeries.mk kCoeff =
          PowerSeries.X *
            (PowerSeries.mk kCoeff * (1 - PowerSeries.X)) := by ring
      _ = PowerSeries.X * (1 + PowerSeries.X) ^ 2 := by
        rw [mk_kCoeff_mul_one_sub]
  have hd' :
      PowerSeries.mk
            (fun n => PowerSeries.coeff n ((1 - PowerSeries.X) ^ 2)) *
          PowerSeries.mk geometricOneCoeff =
        PowerSeries.mk (fun n => PowerSeries.coeff n (1 - PowerSeries.X)) := by
    simpa only [BrandenLeite.mk_coeff_eq] using hd
  have hK' :
      PowerSeries.X *
          PowerSeries.mk (fun n => PowerSeries.coeff n (1 - PowerSeries.X)) *
          PowerSeries.mk kCoeff =
        PowerSeries.mk (fun n => PowerSeries.coeff n
          (PowerSeries.X * (1 + PowerSeries.X) ^ 2)) := by
    simpa only [BrandenLeite.mk_coeff_eq] using hK
  simpa only [BrandenLeite.mk_coeff_eq] using
    PFRiordan.denominator_mul_rowGeneratingSeries
      (D₀ := fun n => PowerSeries.coeff n ((1 - PowerSeries.X) ^ 2))
      (L := fun n => PowerSeries.coeff n
        (PowerSeries.X * (1 + PowerSeries.X) ^ 2))
      (N := fun n => PowerSeries.coeff n (1 - PowerSeries.X))
      (d := geometricOneCoeff) (K := kCoeff) hd' hK'

/-- Every A114123 row splits and has only nonpositive roots. -/
theorem row_splits_and_roots_nonpos (n : ℕ) :
    (row n).Splits ∧
      ∀ r ∈ (row n).roots, r ≤ 0 := by
  apply rowPolynomial_splits_and_roots_nonpos
  · exact rationalPFCoeff_isPolyaFreqSeq
      (c := 1) (by norm_num) 0 (by simp) (by simp)
  · exact rationalPFCoeff_isPolyaFreqSeq
      (c := 1) (by norm_num) 0 (by simp) (by simp)

end RealRooted.Applications.OEIS.A114123
