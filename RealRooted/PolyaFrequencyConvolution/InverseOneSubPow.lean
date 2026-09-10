import RealRooted.PolyaFrequencyConvolution
import RealRooted.PolyaFrequencyConvolution.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Pólya-frequency coefficients of inverse powers of `1 - X`

This file combines closure under Cauchy convolution with the constant-one
certificate to prove that the binomial coefficient sequence of every positive
inverse power of `1 - X` is Pólya-frequency.
-/

namespace RealRooted

/-- The coefficient sequence of `(1 - X) ^ (-(d + 1))`. -/
def invOneSubPowCoeff (d n : ℕ) : ℝ :=
  Nat.choose (d + n) d

@[simp]
theorem invOneSubPowCoeff_zero (n : ℕ) : invOneSubPowCoeff 0 n = 1 := by
  simp [invOneSubPowCoeff]

/-- Convolution with the constant-one sequence raises the inverse-power
parameter by one. -/
theorem natCauchyConvolution_invOneSubPowCoeff_one (d : ℕ) :
    natCauchyConvolution (invOneSubPowCoeff d) (fun _ => 1) =
      invOneSubPowCoeff (d + 1) := by
  funext n
  simp only [natCauchyConvolution, mul_one, invOneSubPowCoeff]
  norm_cast
  simpa [add_comm, add_left_comm, add_assoc] using Nat.sum_range_add_choose n d

/-- The coefficients of every positive inverse power of `1 - X` form a
Pólya-frequency sequence. -/
theorem invOneSubPowCoeff_isPolyaFreqSeq (d : ℕ) :
    IsPolyaFreqSeq (invOneSubPowCoeff d) := by
  induction d with
  | zero =>
      rw [show invOneSubPowCoeff 0 = fun _ => 1 by
        funext n
        simp [invOneSubPowCoeff]]
      exact constantOne_isPolyaFreqSeq
  | succ d ih =>
      rw [← natCauchyConvolution_invOneSubPowCoeff_one d]
      exact ih.natCauchyConvolution constantOne_isPolyaFreqSeq

/-- The Mathlib inverse-power series has the binomial PF sequence above as its
coefficient sequence. -/
theorem coeff_invOneSubPow_val_succ (d n : ℕ) :
    PowerSeries.coeff n (PowerSeries.invOneSubPow ℝ (d + 1)).val =
      invOneSubPowCoeff d n := by
  rw [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]
  simp [invOneSubPowCoeff]

end RealRooted
