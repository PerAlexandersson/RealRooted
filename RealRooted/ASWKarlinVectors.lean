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

/-- If a nonreal complex geometric progression has an interior zero imaginary
part, the adjacent imaginary parts have opposite strict signs. -/
lemma im_pow_mul_im_pow_add_two_neg_of_im_pow_add_one_eq_zero
    {z : ℂ} (him : z.im ≠ 0) (i : ℕ)
    (hzero : (z ^ (i + 1)).im = 0) :
    (z ^ i).im * (z ^ (i + 2)).im < 0 := by
  let θ := z.arg
  have hz : z ≠ 0 := by
    intro hz
    apply him
    simp [hz]
  have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hsin : Real.sin θ ≠ 0 := by
    have hpolar := im_pow_eq_norm_pow_mul_sin_arg z 1
    simp only [pow_one, Nat.cast_one, one_mul] at hpolar
    intro hs
    apply him
    rw [hpolar, hs, mul_zero]
  have hzeroSin : Real.sin ((i + 1 : ℕ) * θ) = 0 := by
    rw [im_pow_eq_norm_pow_mul_sin_arg] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero _ hnorm.ne')
  have hcos : Real.cos ((i + 1 : ℕ) * θ) ≠ 0 := by
    intro hc
    have hsq := Real.sin_sq_add_cos_sq ((i + 1 : ℕ) * θ)
    rw [hzeroSin, hc] at hsq
    norm_num at hsq
  have hprev :
      Real.sin (i * θ) =
        -Real.cos ((i + 1 : ℕ) * θ) * Real.sin θ := by
    have harg :
        (i : ℝ) * θ = ((i + 1 : ℕ) : ℝ) * θ - θ := by
      push_cast
      ring
    rw [harg, Real.sin_sub, hzeroSin]
    ring
  have hnext :
      Real.sin ((i + 2 : ℕ) * θ) =
        Real.cos ((i + 1 : ℕ) * θ) * Real.sin θ := by
    have harg :
        ((i + 2 : ℕ) : ℝ) * θ =
          ((i + 1 : ℕ) : ℝ) * θ + θ := by
      push_cast
      ring
    rw [harg, Real.sin_add, hzeroSin]
    ring
  have htrig :
      Real.sin (i * θ) * Real.sin ((i + 2 : ℕ) * θ) < 0 := by
    rw [hprev, hnext]
    calc
      (-Real.cos ((i + 1 : ℕ) * θ) * Real.sin θ) *
          (Real.cos ((i + 1 : ℕ) * θ) * Real.sin θ) =
          -(Real.cos ((i + 1 : ℕ) * θ) ^ 2 * Real.sin θ ^ 2) := by
            ring
      _ < 0 := neg_lt_zero.mpr
        (mul_pos (sq_pos_of_ne_zero hcos) (sq_pos_of_ne_zero hsin))
  rw [im_pow_eq_norm_pow_mul_sin_arg,
    im_pow_eq_norm_pow_mul_sin_arg]
  calc
    (‖z‖ ^ i * Real.sin (i * θ)) *
        (‖z‖ ^ (i + 2) * Real.sin ((i + 2 : ℕ) * θ)) =
        (‖z‖ ^ i * ‖z‖ ^ (i + 2)) *
          (Real.sin (i * θ) * Real.sin ((i + 2 : ℕ) * θ)) := by
            ring
    _ < 0 := mul_neg_of_pos_of_neg
      (mul_pos (pow_pos hnorm _) (pow_pos hnorm _)) htrig

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
