module

public import RealRooted.ExponentialRows.SubstitutionRows
public import RealRooted.PFPolynomial
import RealRooted.ExponentialRows.Substitution
import Mathlib.Tactic

/-!
# Iterated squaring of an arbitrary admissible marked series

Every substitution `B ↦ B^(2^k)` preserves real-rooted exponential rows and
all directed weak input interlacings. We also cover every even quartic
`a B² + c B⁴`. These are all-index consequences of quadratic substitution,
with no restriction on the input marked series.

This subfamily does not settle arbitrary positive integer powers or arbitrary
PF polynomial outer substitutions. Those are Theorem 1 of the unpublished
manuscript *Degree-raising substitutions for exponential rows*, issue #2415:
https://github.com/PerAlexandersson/RealRooted/issues/2415#issuecomment-7141592218.
-/

public section

open Polynomial

namespace RealRooted.ExponentialRows

private theorem square_constantCoeff :
    PowerSeries.constantCoeff (PowerSeries.X ^ 2 : PowerSeries ℝ) = 0 := by
  simp only [map_pow, PowerSeries.constantCoeff_X, zero_pow two_ne_zero]

private theorem square_ode :
    PowerSeries.derivative (PowerSeries.X ^ 2 : PowerSeries ℝ) =
      PowerSeries.C 0 + PowerSeries.C 2 * PowerSeries.X +
        PowerSeries.C 0 * PowerSeries.X ^ 2 := by
  simp only [PowerSeries.derivative_X_pow, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    map_zero, zero_add, zero_mul, add_zero]

private theorem constantCoeff_pow_two_pow {B : PowerSeries ℝ}
    (hB : PowerSeries.constantCoeff B = 0) (k : ℕ) :
    PowerSeries.constantCoeff (B ^ (2 ^ k)) = 0 := by
  rw [map_pow, hB, zero_pow (pow_ne_zero _ two_ne_zero)]

/-- One squaring step on the marked series agrees with its exponential
substitution operator. -/
private theorem exponentialSubstitution_square_insertionRow {A B : PowerSeries ℝ}
    (hA : PowerSeries.constantCoeff A = 0) (hB : PowerSeries.constantCoeff B = 0)
    (k n : ℕ) :
    exponentialSubstitution (PowerSeries.X ^ 2)
        (insertionRow (affineBlockWeights A (B ^ (2 ^ k))) n) =
      insertionRow (affineBlockWeights A (B ^ (2 ^ (k + 1)))) n := by
  rw [exponentialSubstitution_insertionRow hA (constantCoeff_pow_two_pow hB k)
    square_constantCoeff]
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_pow_two_pow hB k)
  rw [PowerSeries.subst_pow hs, PowerSeries.subst_X hs, ← pow_mul, ← pow_succ]

/-- Every iterated square of an admissible nonnegative marked series gives
PF rows, including all ranks and all iteration counts. -/
theorem insertionRow_isPF_pow_two_pow {A B : PowerSeries ℝ}
    (hA : PowerSeries.constantCoeff A = 0) (hB : PowerSeries.constantCoeff B = 0)
    (hAnn : ∀ r, 0 ≤ PowerSeries.coeff r A) (hBnn : ∀ r, 0 ≤ PowerSeries.coeff r B)
    (n : ℕ) (hrow : (insertionRow (affineBlockWeights A B) n).Splits) (k : ℕ) :
    IsPFPolynomial (insertionRow (affineBlockWeights A (B ^ (2 ^ k))) n) := by
  induction k with
  | zero =>
    simpa only [pow_zero, pow_one] using IsPFPolynomial.of_realRooted_nonneg
      (hasNonnegCoeffs_insertionRow_affineBlockWeights hAnn hBnn n) hrow
  | succ k ih =>
    rw [← exponentialSubstitution_square_insertionRow hA hB]
    exact isPFPolynomial_exponentialSubstitution square_constantCoeff square_ode
      le_rfl (by norm_num) le_rfl ih

/-- All powers `B^(2^k)` preserve splitting of each input exponential row. -/
theorem insertionRow_splits_pow_two_pow {A B : PowerSeries ℝ}
    (hA : PowerSeries.constantCoeff A = 0) (hB : PowerSeries.constantCoeff B = 0)
    (hAnn : ∀ r, 0 ≤ PowerSeries.coeff r A) (hBnn : ∀ r, 0 ≤ PowerSeries.coeff r B)
    (n : ℕ) (hrow : (insertionRow (affineBlockWeights A B) n).Splits) (k : ℕ) :
    (insertionRow (affineBlockWeights A (B ^ (2 ^ k))) n).Splits :=
  (insertionRow_isPF_pow_two_pow hA hB hAnn hBnn n hrow k).splits

/-- Every directed weak interlacing of the input rows survives arbitrarily
many squarings of the marked series. -/
theorem insertionRow_interl_pow_two_pow {A B : PowerSeries ℝ}
    (hA : PowerSeries.constantCoeff A = 0) (hB : PowerSeries.constantCoeff B = 0)
    (hAnn : ∀ r, 0 ≤ PowerSeries.coeff r A) (hBnn : ∀ r, 0 ≤ PowerSeries.coeff r B)
    {m n : ℕ} (hm : (insertionRow (affineBlockWeights A B) m).Splits)
    (hn : (insertionRow (affineBlockWeights A B) n).Splits)
    (hinterl : Interl (insertionRow (affineBlockWeights A B) m)
      (insertionRow (affineBlockWeights A B) n)) (k : ℕ) :
    Interl (insertionRow (affineBlockWeights A (B ^ (2 ^ k))) m)
      (insertionRow (affineBlockWeights A (B ^ (2 ^ k))) n) := by
  induction k with
  | zero => simpa only [pow_zero, pow_one] using hinterl
  | succ k ih =>
    rw [← exponentialSubstitution_square_insertionRow hA hB,
      ← exponentialSubstitution_square_insertionRow hA hB]
    exact interl_exponentialSubstitution square_constantCoeff square_ode
      le_rfl (by norm_num) le_rfl
      (insertionRow_isPF_pow_two_pow hA hB hAnn hBnn m hm k)
      (insertionRow_isPF_pow_two_pow hA hB hAnn hBnn n hn k) ih


private theorem quadratic_constantCoeff (a c : ℝ) :
    PowerSeries.constantCoeff
      (PowerSeries.C a * PowerSeries.X + PowerSeries.C c * PowerSeries.X ^ 2) = 0 := by
  simp only [map_add, map_mul, map_pow, PowerSeries.constantCoeff_X,
    zero_pow two_ne_zero, mul_zero, add_zero]

private theorem quadratic_ode (a c : ℝ) :
    PowerSeries.derivative
        (PowerSeries.C a * PowerSeries.X + PowerSeries.C c * PowerSeries.X ^ 2) =
      PowerSeries.C a + PowerSeries.C (2 * c) * PowerSeries.X +
        PowerSeries.C 0 *
          (PowerSeries.C a * PowerSeries.X + PowerSeries.C c * PowerSeries.X ^ 2) := by
  simp only [map_add, PowerSeries.derivative.leibniz, PowerSeries.derivative_C,
    PowerSeries.derivative_X, PowerSeries.derivative_X_pow, Nat.cast_ofNat,
    Nat.reduceSub, pow_one, zero_mul, map_zero, add_zero, map_mul]
  ring

/-- Two quadratic substitution operators act on the rows as the literal even
quartic `a B² + c B⁴`. -/
private theorem exponentialSubstitution_even_quartic_insertionRow {A B : PowerSeries ℝ}
    (hA : PowerSeries.constantCoeff A = 0) (hB : PowerSeries.constantCoeff B = 0)
    (a c : ℝ) (n : ℕ) :
    exponentialSubstitution
        (PowerSeries.C a * PowerSeries.X + PowerSeries.C c * PowerSeries.X ^ 2)
        (insertionRow (affineBlockWeights A (B ^ 2)) n) =
      insertionRow (affineBlockWeights A
        (PowerSeries.C a * B ^ 2 + PowerSeries.C c * B ^ 4)) n := by
  have hB2 : PowerSeries.constantCoeff (B ^ 2) = 0 := by
    rw [map_pow, hB, zero_pow two_ne_zero]
  rw [exponentialSubstitution_insertionRow hA hB2 (quadratic_constantCoeff a c)]
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' hB2
  rw [PowerSeries.subst_add hs, PowerSeries.subst_mul hs, PowerSeries.subst_mul hs,
    PowerSeries.subst_C, PowerSeries.subst_C, PowerSeries.subst_X hs,
    PowerSeries.subst_pow hs, PowerSeries.subst_X hs, ← pow_mul]
  rfl

/-- Every nonnegative even quartic outer substitution preserves splitting of
all exponential rows. This includes the entire `b = 0` face of Theorem 3. -/
theorem insertionRow_splits_even_quartic_subst {A B : PowerSeries ℝ} {a c : ℝ}
    (hA : PowerSeries.constantCoeff A = 0) (hB : PowerSeries.constantCoeff B = 0)
    (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hAnn : ∀ r, 0 ≤ PowerSeries.coeff r A) (hBnn : ∀ r, 0 ≤ PowerSeries.coeff r B)
    (n : ℕ) (hrow : (insertionRow (affineBlockWeights A B) n).Splits) :
    (insertionRow (affineBlockWeights A
      (PowerSeries.C a * B ^ 2 + PowerSeries.C c * B ^ 4)) n).Splits := by
  have hseed : IsPFPolynomial (insertionRow (affineBlockWeights A (B ^ 2)) n) := by
    simpa only [pow_one] using insertionRow_isPF_pow_two_pow hA hB hAnn hBnn n hrow 1
  rw [← exponentialSubstitution_even_quartic_insertionRow hA hB]
  exact (isPFPolynomial_exponentialSubstitution (quadratic_constantCoeff a c)
    (quadratic_ode a c) ha (mul_nonneg (by norm_num) hc) le_rfl hseed).splits

/-- Every nonnegative even quartic outer substitution preserves every directed
weak interlacing of input exponential rows. -/
theorem insertionRow_interl_even_quartic_subst {A B : PowerSeries ℝ} {a c : ℝ}
    (hA : PowerSeries.constantCoeff A = 0) (hB : PowerSeries.constantCoeff B = 0)
    (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hAnn : ∀ r, 0 ≤ PowerSeries.coeff r A) (hBnn : ∀ r, 0 ≤ PowerSeries.coeff r B)
    {m n : ℕ} (hm : (insertionRow (affineBlockWeights A B) m).Splits)
    (hn : (insertionRow (affineBlockWeights A B) n).Splits)
    (hinterl : Interl (insertionRow (affineBlockWeights A B) m)
      (insertionRow (affineBlockWeights A B) n)) :
    Interl (insertionRow (affineBlockWeights A
        (PowerSeries.C a * B ^ 2 + PowerSeries.C c * B ^ 4)) m)
      (insertionRow (affineBlockWeights A
        (PowerSeries.C a * B ^ 2 + PowerSeries.C c * B ^ 4)) n) := by
  have hseed (j : ℕ) (hj : (insertionRow (affineBlockWeights A B) j).Splits) :
      IsPFPolynomial (insertionRow (affineBlockWeights A (B ^ 2)) j) := by
    simpa only [pow_one] using insertionRow_isPF_pow_two_pow hA hB hAnn hBnn j hj 1
  have hpair : Interl (insertionRow (affineBlockWeights A (B ^ 2)) m)
      (insertionRow (affineBlockWeights A (B ^ 2)) n) := by
    simpa only [pow_one] using insertionRow_interl_pow_two_pow hA hB hAnn hBnn hm hn hinterl 1
  rw [← exponentialSubstitution_even_quartic_insertionRow hA hB,
    ← exponentialSubstitution_even_quartic_insertionRow hA hB]
  exact interl_exponentialSubstitution (quadratic_constantCoeff a c) (quadratic_ode a c)
    ha (mul_nonneg (by norm_num) hc) le_rfl (hseed m hm) (hseed n hn) hpair

end RealRooted.ExponentialRows
