module

public import RealRooted.AissenSchoenbergWhitneyBase
public import RealRooted.ToeplitzFin
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.FinTruncation
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg.Mul
public import RealRooted.NatCauchyConvolution
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Cauchy convolution of Pólya-frequency sequences

This file identifies finite lower-Toeplitz truncation multiplication with
Cauchy convolution and proves that Pólya-frequency sequences are closed under
that operation.
-/

public section

open Matrix

namespace RealRooted

/-- Coefficients of a product of power series are the Cauchy convolution of
their coefficient sequences. -/
theorem coeff_mul_eq_natCauchyConvolution (F G : PowerSeries ℝ) (n : ℕ) :
    PowerSeries.coeff n (F * G) =
      natCauchyConvolution (fun k => PowerSeries.coeff k F)
        (fun k => PowerSeries.coeff k G) n := by
  rw [PowerSeries.coeff_mul]
  simpa [natCauchyConvolution] using
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
      (fun p => PowerSeries.coeff p.1 F * PowerSeries.coeff p.2 G) n

/-- Multiplication of finite lower-Toeplitz truncations realizes Cauchy
convolution without losing any summands. -/
theorem toeplitzFin_mul (a b : ℕ → ℝ) (N : ℕ) :
    toeplitzFin a N * toeplitzFin b N =
      toeplitzFin (natCauchyConvolution a b) N := by
  rw [toeplitzFin_mul_coeff]
  congr 1
  funext n
  simpa using
    coeff_mul_eq_natCauchyConvolution (PowerSeries.mk a) (PowerSeries.mk b) n

/-- Pólya-frequency sequences are closed under Cauchy convolution. -/
protected theorem IsPolyaFreqSeq.natCauchyConvolution
    {a b : ℕ → ℝ} (ha : IsPolyaFreqSeq a) (hb : IsPolyaFreqSeq b) :
    IsPolyaFreqSeq (natCauchyConvolution a b) := by
  rw [IsPolyaFreqSeq]
  apply Matrix.IsTotallyNonneg.of_fin_truncations
    (Mfin := fun N => toeplitzFin a N * toeplitzFin b N)
  · intro N i j
    rw [toeplitzFin_mul]
    rfl
  · intro N
    exact Matrix.IsTotallyNonneg.mul
      (ha.submatrix Fin.val_strictMono Fin.val_strictMono)
      (hb.submatrix Fin.val_strictMono Fin.val_strictMono)

/-- The product of two formal power series with Pólya-frequency coefficient
sequences again has a Pólya-frequency coefficient sequence. -/
theorem IsPolyaFreqSeq.coeff_mul {F G : PowerSeries ℝ}
    (hF : IsPolyaFreqSeq fun k => PowerSeries.coeff k F)
    (hG : IsPolyaFreqSeq fun k => PowerSeries.coeff k G) :
    IsPolyaFreqSeq fun k => PowerSeries.coeff k (F * G) := by
  simpa only [coeff_mul_eq_natCauchyConvolution] using hF.natCauchyConvolution hG

end RealRooted
