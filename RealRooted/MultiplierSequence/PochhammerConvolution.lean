module

public import RealRooted.MultiplierSequence.Infinite
public import Mathlib.RingTheory.Polynomial.Pochhammer
import RealRooted.Mathlib.RingTheory.Polynomial.Pochhammer.ReciprocalConvolution
import RealRooted.MultiplierSequence.BinomialConvolution
import RealRooted.MultiplierSequence.InvPochhammer

/-!
# Positive reciprocal-Pochhammer convolution

The convolution of two reciprocal rising-factorial multiplier sequences has
an exact finite-product formula. This is the Gamma-free normalization of
Craven--Csordas (2006), Lemma 3.12 and Theorem 3.14. It includes the removable
singularity when the parameter sum is one and the index is zero.
-/

public section

open Polynomial

namespace RealRooted

/-- The canceled reciprocal-Pochhammer convolution is a PF multiplier
sequence for all positive parameters, including their sum equal to one. -/
theorem isPFMultiplierSequence_pochhammerConvolution {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    IsPFMultiplierSequence (fun n =>
      (ascPochhammer ℝ n).eval (a + b + n - 1) /
        ((ascPochhammer ℝ n).eval a * (ascPochhammer ℝ n).eval b)) := by
  have h := (isPFMultiplierSequence_inv_ascPochhammer ha).binomialConvolution
    (isPFMultiplierSequence_inv_ascPochhammer hb)
  convert h using 1
  ext n
  exact (sum_choose_mul_inv_ascPochhammer n
    (ascPochhammer_pos n a ha).ne' (ascPochhammer_pos n b hb).ne').symm

end RealRooted
