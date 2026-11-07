module

public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.Basic.Real.Basic
public import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic

/-! Positivity of negative-binomial coefficients from rising factorials. -/

public section

namespace Ring

variable {R : Type*} [CommRing R] [BinomialRing R]

/-- Removing the alternating signs from a negative generalized binomial
coefficient gives the corresponding multichoose coefficient. -/
theorem neg_one_pow_mul_choose_neg (a : R) (n : ℕ) :
    (-1 : R) ^ n * choose (-a) n = multichoose a n := by
  rw [choose_neg', Units.smul_def, zsmul_eq_mul, Int.cast_negOnePow_natCast,
    ← mul_assoc, ← mul_pow]
  simp

/-- Multiplication by the factorial recovers the evaluated rising
factorial from a multichoose coefficient. -/
theorem factorial_mul_multichoose (a : R) (n : ℕ) :
    (n.factorial : R) * multichoose a n =
      (ascPochhammer R n).eval a := by
  simpa only [nsmul_eq_mul, Polynomial.ascPochhammer_smeval_eq_eval] using
    factorial_nsmul_multichoose_eq_ascPochhammer a n

/-- Multichoose coefficients with a strictly positive real parameter
are strictly positive in every degree. -/
theorem multichoose_pos {a : ℝ} (ha : 0 < a) (n : ℕ) :
    0 < multichoose a n := by
  have hf : (0 : ℝ) < n.factorial := by positivity
  apply (mul_pos_iff_of_pos_left hf).mp
  rw [factorial_mul_multichoose]
  exact ascPochhammer_pos n a ha

/-- Multichoose coefficients with a nonnegative real parameter are
nonnegative in every degree. -/
theorem multichoose_nonneg {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    0 ≤ multichoose a n := by
  rcases ha.eq_or_lt with h | h
  · subst a
    cases n with
    | zero => simp
    | succ n => simp [multichoose_zero_succ]
  · exact (multichoose_pos h n).le

/-- Every coefficient of the negative binomial expansion becomes strictly
positive after the usual alternating-sign correction. -/
theorem neg_one_pow_mul_choose_neg_pos {a : ℝ} (ha : 0 < a) (n : ℕ) :
    0 < (-1 : ℝ) ^ n * choose (-a) n := by
  rw [neg_one_pow_mul_choose_neg]
  exact multichoose_pos ha n

end Ring

namespace PowerSeries

/-- The series `(1-X)^(-a)` has multichoose coefficients. -/
theorem coeff_rescale_neg_one_binomialSeries_neg (a : ℝ) (n : ℕ) :
    coeff n (rescale (-1) (binomialSeries ℝ (-a))) = Ring.multichoose a n := by
  simpa [coeff_rescale, binomialSeries_coeff, smul_eq_mul] using
    Ring.neg_one_pow_mul_choose_neg a n

/-- The real negative-binomial series has strictly positive coefficients
when its parameter is strictly positive. -/
theorem coeff_rescale_neg_one_binomialSeries_neg_pos {a : ℝ}
    (ha : 0 < a) (n : ℕ) :
    0 < coeff n (rescale (-1) (binomialSeries ℝ (-a))) := by
  rw [coeff_rescale_neg_one_binomialSeries_neg]
  exact Ring.multichoose_pos ha n

end PowerSeries
