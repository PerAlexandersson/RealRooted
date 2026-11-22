module

public import RealRooted.Hermite.Jensen
public import RealRooted.SimpleRoots
public import RealRooted.Mathlib.Algebra.Polynomial.BasisTransform
import RealRooted.BasisTransform.Hermite
import RealRooted.Mathlib.Algebra.Polynomial.Reverse
import RealRooted.Mathlib.Algebra.Polynomial.Chow
import RealRooted.Mathlib.Algebra.Polynomial.Derivative

/-!
# Finite Jensen-to-Hermite transfer

At each fixed degree, splitting of a Jensen polynomial implies splitting of
its Hermite version. A nonzero input gives simple real roots, even if the
Jensen polynomial has repeated roots. No entire-function hypothesis is needed.
The splitting implications are Corollaries 3.7 and 3.8 of Cormac O'Sullivan,
*Zeros of Jensen polynomials and asymptotics for the Riemann xi function*,
https://arxiv.org/abs/2007.13582. The simple-root statements strengthen them.
-/

public section

open Polynomial

namespace RealRooted

/-- Differentiation lowers the physicists' Hermite index with factor `2n`. -/
theorem derivative_hermitePhysicists (n : ℕ) :
    (hermitePhysicists (n + 1)).derivative = C (2 * (n + 1 : ℝ)) * hermitePhysicists n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [map_ofNat]
  | one => simp [hermitePhysicists_add_two, map_ofNat]; ring
  | more n ih ih' =>
      rw [show n + 2 + 1 = (n + 1) + 2 by lia, hermitePhysicists_add_two]
      simp only [derivative_sub, derivative_mul, derivative_ofNat, derivative_X,
        derivative_C, zero_mul, mul_one, zero_add]
      rw [show n + 1 + 1 = n + 2 by lia, ih', ih]
      rw [hermitePhysicists_add_two]
      simp only [map_mul, map_add, map_natCast, map_ofNat, map_one]
      push_cast
      ring

/-- The physicists' Hermite raising operator is `2X - d/dX`. -/
theorem hermitePhysicists_succ_derivative (n : ℕ) :
    hermitePhysicists (n + 1) =
      (C 2 * X + C 0) * hermitePhysicists n + C (-1) * (hermitePhysicists n).derivative := by
  cases n with
  | zero => simp [map_ofNat]
  | succ n =>
      rw [derivative_hermitePhysicists, hermitePhysicists_add_two]
      simp [map_ofNat, sub_eq_add_neg]

/-- The raising recurrence determines both degree and leading coefficient. -/
private theorem hermitePhysicists_degree_and_leadingCoeff (n : ℕ) :
    (hermitePhysicists n).natDegree = n ∧ (hermitePhysicists n).leadingCoeff = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h := natDegree_and_leadingCoeff_quadratic_derivative_add_linear_mul_add
        (hermitePhysicists n) (C (-1) * (hermitePhysicists n).derivative) 0 0 0 2
        ((natDegree_C_mul_le _ _).trans
          ((natDegree_derivative_le _).trans (Nat.sub_le _ _)))
        (by simp [ih.2])
      have heq : C 2 * X * hermitePhysicists n +
          C (-1) * (hermitePhysicists n).derivative = hermitePhysicists (n + 1) := by
        rw [hermitePhysicists_succ_derivative]
        simp
      simp only [map_zero, zero_mul, zero_add, heq] at h
      simpa [ih.1, ih.2, pow_succ, mul_comm] using h

/-- The physicists' Hermite polynomial has its index as degree. -/
theorem natDegree_hermitePhysicists (n : ℕ) :
    (hermitePhysicists n).natDegree = n :=
  (hermitePhysicists_degree_and_leadingCoeff n).1

/-- The physicists' Hermite normalization has leading coefficient `2^n`. -/
theorem leadingCoeff_hermitePhysicists (n : ℕ) :
    (hermitePhysicists n).leadingCoeff = 2 ^ n :=
  (hermitePhysicists_degree_and_leadingCoeff n).2

/-- The Hermite convolution never exceeds its specified degree. -/
theorem natDegree_hermiteJensenPolynomial_le (d : ℕ) (gamma : ℕ → ℝ) :
    (hermiteJensenPolynomial d gamma).natDegree ≤ d := by
  apply natDegree_sum_le_of_forall_le
  intro k _
  exact (natDegree_C_mul_le _ _).trans
    ((natDegree_hermitePhysicists (d - k)).le.trans (Nat.sub_le _ _))

/-- The top coefficient depends on `gamma 0`, rather than on `gamma d`. -/
theorem coeff_hermiteJensenPolynomial_self (d : ℕ) (gamma : ℕ → ℝ) :
    (hermiteJensenPolynomial d gamma).coeff d = gamma 0 * 2 ^ d := by
  classical
  rw [hermiteJensenPolynomial, finsetSum_coeff, Finset.sum_eq_single 0]
  · simp only [coeff_C_mul, Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
    have hcoeff := coeff_natDegree (p := hermitePhysicists d)
    rw [natDegree_hermitePhysicists, leadingCoeff_hermitePhysicists] at hcoeff
    rw [hcoeff]
  · intro k hmem hk
    have hkd : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hmem)
    rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt, mul_zero]
    rw [natDegree_hermitePhysicists]
    lia
  · simp

/-- A nonzero zeroth coefficient makes the Hermite convolution degree exact. -/
theorem natDegree_hermiteJensenPolynomial {d : ℕ} {gamma : ℕ → ℝ}
    (hgamma : gamma 0 ≠ 0) : (hermiteJensenPolynomial d gamma).natDegree = d :=
  natDegree_eq_of_le_of_coeff_ne_zero (natDegree_hermiteJensenPolynomial_le d gamma)
    (by rw [coeff_hermiteJensenPolynomial_self]; exact mul_ne_zero hgamma (by positivity))

/-- The leading coefficient of a degree-exact Hermite convolution. -/
theorem leadingCoeff_hermiteJensenPolynomial {d : ℕ} {gamma : ℕ → ℝ}
    (hgamma : gamma 0 ≠ 0) :
    (hermiteJensenPolynomial d gamma).leadingCoeff = gamma 0 * 2 ^ d := by
  rw [← coeff_natDegree, natDegree_hermiteJensenPolynomial hgamma,
    coeff_hermiteJensenPolynomial_self]

/-- Replacing monomials by physicists' Hermite polynomials strictly
regularizes every nonzero real-rooted polynomial. -/
theorem isSimpleRealRooted_hermiteBasisTransform {p : ℝ[X]}
    (hp : p.Splits) (hp0 : p ≠ 0) :
    IsSimpleRealRooted (basisTransform hermitePhysicists p) :=
  isSimpleRealRooted_basisTransform_of_raising hermitePhysicists_zero
    (by norm_num) (by norm_num) hermitePhysicists_succ_derivative hp hp0

/-- Replacing monomials by physicists' Hermite polynomials preserves
real-rootedness, including zero. -/
theorem splits_hermiteBasisTransform {p : ℝ[X]} (hp : p.Splits) :
    (basisTransform hermitePhysicists p).Splits :=
  splits_basisTransform_of_raising hermitePhysicists_zero
    (by norm_num) (by norm_num) hermitePhysicists_succ_derivative hp

/-- The Hermite basis transform preserves the degree of every nonzero input,
without a real-rootedness assumption. -/
theorem natDegree_hermiteBasisTransform {p : ℝ[X]} (hp : p ≠ 0) :
    (basisTransform hermitePhysicists p).natDegree = p.natDegree :=
  basisTransform_natDegree_eq natDegree_hermitePhysicists
    (fun n => leadingCoeff_ne_zero.mp (by rw [leadingCoeff_hermitePhysicists]; positivity)) hp

/-- The finite Hermite convolution is the Hermite basis transform of the
degree-reflected Jensen polynomial. -/
theorem hermiteJensenPolynomial_eq_basisTransform (d : ℕ) (gamma : ℕ → ℝ) :
    hermiteJensenPolynomial d gamma =
      basisTransform hermitePhysicists (reflect d (jensenPolynomial d gamma)) := by
  classical
  simp only [jensenPolynomial, ← C_mul_X_pow_eq_monomial, reflect_finset_sum_C_mul,
    reflect_monomial, basisTransform_finset_sum, basisTransform_C_mul_X_pow,
    hermiteJensenPolynomial]
  apply Finset.sum_congr rfl
  intro k hk
  rw [revAt_le (by simpa using hk)]

/-- O'Sullivan's finite-degree implication requires only the corresponding
Jensen polynomial to split. -/
theorem hermiteJensenPolynomial_splits_of_jensenPolynomial_splits
    {d : ℕ} {gamma : ℕ → ℝ} (hp : (jensenPolynomial d gamma).Splits) :
    (hermiteJensenPolynomial d gamma).Splits := by
  rw [hermiteJensenPolynomial_eq_basisTransform]
  exact splits_hermiteBasisTransform
    ((splits_reflect_iff (natDegree_jensenPolynomial_le d gamma)).mpr hp)

/-- A nonzero split Jensen polynomial yields a Hermite polynomial with simple
real roots. No simplicity hypothesis is imposed on the Jensen polynomial. -/
theorem isSimpleRealRooted_hermiteJensenPolynomial
    {d : ℕ} {gamma : ℕ → ℝ} (hp : (jensenPolynomial d gamma).Splits)
    (hp0 : jensenPolynomial d gamma ≠ 0) :
    IsSimpleRealRooted (hermiteJensenPolynomial d gamma) := by
  rw [hermiteJensenPolynomial_eq_basisTransform]
  exact isSimpleRealRooted_hermiteBasisTransform
    ((splits_reflect_iff (natDegree_jensenPolynomial_le d gamma)).mpr hp)
    (fun h => hp0 (reflect_eq_zero_iff.mp h))

/-- Nonvanishing of the zeroth Taylor coefficient supplies the nonzero
hypothesis in the finite Hermite simplicity theorem. -/
theorem isSimpleRealRooted_hermiteJensenPolynomial_of_coeff_zero
    {d : ℕ} {gamma : ℕ → ℝ} (hp : (jensenPolynomial d gamma).Splits)
    (hgamma : gamma 0 ≠ 0) :
    IsSimpleRealRooted (hermiteJensenPolynomial d gamma) := by
  apply isSimpleRealRooted_hermiteJensenPolynomial hp
  intro hz
  have h := congrArg (fun p : ℝ[X] => p.coeff 0) hz
  simp only [coeff_jensenPolynomial, Nat.zero_le, ite_true, Nat.choose_zero_right,
    Nat.cast_one, one_mul, coeff_zero] at h
  exact hgamma h

end RealRooted
