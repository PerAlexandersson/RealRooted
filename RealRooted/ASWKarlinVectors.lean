import RealRooted.Mathlib.LinearAlgebra.Matrix.SignVariation
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Karlin root and sine vectors

This file contains the finite vectors used in Karlin's sector proof.  The
root vector records imaginary parts of powers of a complex root; after
normalizing by the positive powers of the norm, it has the same sign pattern
as the corresponding sampled sine vector.
-/

noncomputable section

namespace RealRooted

/-- The imaginary parts of successive powers of a complex number, truncated
to the columns of Karlin's repeated matrix. -/
def aswKarlinRootVector (z : ℂ) (degree order blocks : ℕ) :
    Fin (blocks * (degree + order - 1) + 1) → ℝ :=
  fun j => (z ^ (j : ℕ)).im

/-- The sampled sine vector corresponding to the argument of a complex root. -/
def aswKarlinSineVector (θ : ℝ) (degree order blocks : ℕ) :
    Fin (blocks * (degree + order - 1) + 1) → ℝ :=
  fun j => Real.sin ((j : ℕ) * θ)

@[simp]
lemma aswKarlinSineVector_zero_apply (degree order blocks : ℕ)
    (j : Fin (blocks * (degree + order - 1) + 1)) :
    aswKarlinSineVector 0 degree order blocks j = 0 := by
  simp [aswKarlinSineVector]

lemma aswKarlinSineVector_neg (θ : ℝ) (degree order blocks : ℕ) :
    aswKarlinSineVector (-θ) degree order blocks =
      fun j => -aswKarlinSineVector θ degree order blocks j := by
  funext j
  simp [aswKarlinSineVector, mul_neg]

lemma im_pow_eq_norm_pow_mul_sin_arg (z : ℂ) (n : ℕ) :
    (z ^ n).im = ‖z‖ ^ n * Real.sin (n * z.arg) := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I z]
  rw [mul_pow, ← Complex.exp_nat_mul, ← Complex.ofReal_pow, Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    Complex.exp_im]
  simp

/-- A nonzero complex number's root vector and sampled sine vector have the
same coordinate signs. -/
lemma signVariations_aswKarlinRootVector_eq_sine {z : ℂ} (hz : z ≠ 0)
    (degree order blocks : ℕ) :
    Fin.signVariations (aswKarlinRootVector z degree order blocks) =
      Fin.signVariations (aswKarlinSineVector z.arg degree order blocks) := by
  apply Fin.signVariations_congr_sign
  intro j
  rw [aswKarlinRootVector, aswKarlinSineVector,
    im_pow_eq_norm_pow_mul_sin_arg, sign_mul]
  have hnorm : 0 < ‖z‖ ^ (j : ℕ) := pow_pos (norm_pos_iff.mpr hz) _
  simp [hnorm]

lemma signVariations_aswKarlinSineVector_neg (θ : ℝ) (degree order blocks : ℕ) :
    Fin.signVariations (aswKarlinSineVector (-θ) degree order blocks) =
      Fin.signVariations (aswKarlinSineVector θ degree order blocks) := by
  rw [aswKarlinSineVector_neg]
  exact Fin.signVariations_neg (aswKarlinSineVector θ degree order blocks)

@[simp]
lemma signVariations_aswKarlinSineVector_zero (degree order blocks : ℕ) :
    Fin.signVariations (aswKarlinSineVector 0 degree order blocks) = 0 := by
  simp [Fin.signVariations, List.signVariations]

/-- In the one-block Karlin matrix, a nonreal complex number gives a nonzero
root vector: the coordinate at exponent one is its imaginary part. -/
lemma aswKarlinRootVector_ne_zero_of_im_ne_zero {z : ℂ} {degree order : ℕ}
    (hdegree : 0 < degree) (horder : 0 < order) (him : z.im ≠ 0) :
    aswKarlinRootVector z degree order 1 ≠ 0 := by
  intro hzero
  have hcols : 1 < 1 * (degree + order - 1) + 1 := by
    have hsum : 1 ≤ degree + order - 1 := by lia
    lia
  have hcoord :=
    congrFun hzero (⟨1, hcols⟩ : Fin (1 * (degree + order - 1) + 1))
  exact him (by simpa [aswKarlinRootVector] using hcoord)

end RealRooted
