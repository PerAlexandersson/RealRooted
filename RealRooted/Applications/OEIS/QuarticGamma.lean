module

public import Mathlib
public import RealRooted.Basic.Coefficients
public import RealRooted.Basic.ProperPosition
public import RealRooted.GammaTransform.Basic
import RealRooted.AffineProperPosition
import RealRooted.GammaTransform.ProperPosition
import RealRooted.GammaTransform.Preservation
import RealRooted.Linear
import RealRooted.Recurrence.Uniqueness
import RealRooted.MaWang.Weak.DerivativeSign
import RealRooted.HermiteBiehler.OrientedPencil
import RealRooted.Mathlib.Algebra.QuadraticDiscriminant
import RealRooted.QuadraticRoot

/-!
# A quartic-cofactor family containing three OEIS rows

This module studies the common two-parameter family containing
[OEIS A157169](https://oeis.org/A157169),
[OEIS A157171](https://oeis.org/A157171), and
[OEIS A124376](https://oeis.org/A124376).  We use the closed recurrence form
because the repository has no recurrence-based definition of these three row
families to identify with it.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted.Applications.OEIS.QuarticGamma

/-- The common row-polynomial family for OEIS A157169, A157171, and A124376.

It is the family `P_n = gammaTransform_n (γ_n)` with
`γ_0 = γ_1 = 1`, `γ_{n+2}(Z) = 1 + a (n+1) Z + b binom(n,2) Z²`.  Here it is given by its five
seeds and the recurrence `P_{n+5} = 3 s P_{n+4} - 3 s² P_{n+3} + s³ P_{n+2}`, `s = 1 + X`.
For `(a, b) = (3, 2), (9, 6), (2, 1)` these are OEIS A157169, A157171, A124376. -/
def polynomial (a b : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | 2 => (1 + X) ^ 2 + C a * X
  | 3 => (1 + X) ^ 3 + C (2 * a) * X * (1 + X)
  | 4 => (1 + X) ^ 4 + C (3 * a) * X * (1 + X) ^ 2 + C b * X ^ 2
  | n + 5 => 3 * (1 + X) * polynomial a b (n + 4) - 3 * (1 + X) ^ 2 * polynomial a b (n + 3) +
      (1 + X) ^ 3 * polynomial a b (n + 2)

/-- The gamma-polynomial model underlying `polynomial a b n`. -/
def gammaPolynomial (a b : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1
  | 2 => C a * X + 1
  | 3 => C (2 * a) * X + 1
  | n + 4 =>
      C (b / 2 * ((n : ℝ) + 2) * ((n : ℝ) + 1)) * X ^ 2 +
        C (a * ((n : ℝ) + 3)) * X + 1

/-- A polynomial sequence with the five displayed seeds and the order-five
recurrence is `polynomial a b`. -/
theorem eq_polynomial_of_five_seeds_and_recurrence
    {a b : ℝ} {Q : ℕ → ℝ[X]}
    (h0 : Q 0 = 1)
    (h1 : Q 1 = 1 + X)
    (h2 : Q 2 = (1 + X) ^ 2 + C a * X)
    (h3 : Q 3 = (1 + X) ^ 3 + C (2 * a) * X * (1 + X))
    (h4 : Q 4 = (1 + X) ^ 4 + C (3 * a) * X * (1 + X) ^ 2 + C b * X ^ 2)
    (hrec : ∀ n,
      Q (n + 5) = 3 * (1 + X) * Q (n + 4) - 3 * (1 + X) ^ 2 * Q (n + 3) +
        (1 + X) ^ 3 * Q (n + 2)) :
    Q = polynomial a b := by
  funext n
  exact sequence_eq_of_same_finite_recurrence
    (k := 5) (op := fun _ w => 3 * (1 + X) * w 4 - 3 * (1 + X) ^ 2 * w 3 +
      (1 + X) ^ 3 * w 2)
    (by intro i hi; interval_cases i <;> assumption) hrec (fun _ => rfl) n

/-- The quartic cofactor of `polynomial a b (n + 4)`. -/
private def quarticCofactor (a b : ℝ) (n : ℕ) : ℝ[X] :=
  (1 + X) ^ 4 + C (a * ((n : ℝ) + 3)) * X * (1 + X) ^ 2 +
        C (b / 2 * ((n : ℝ) + 2) * ((n : ℝ) + 1)) * X ^ 2

private theorem polynomial_add_four_eq (a b : ℝ) (n : ℕ) :
    polynomial a b (n + 4) = (1 + X) ^ n * quarticCofactor a b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 | 1 | 2 =>
      apply Polynomial.funext
      intro x
      simp only [polynomial, quarticCofactor, eval_add, eval_mul, eval_sub, eval_pow,
        eval_one, eval_X, eval_C, eval_ofNat, Nat.cast_ofNat]
      ring
    | k + 3 =>
      rw [show k + 3 + 4 = (k + 2) + 5 by lia, polynomial,
        ih (k + 2) (by lia), show k + 2 + 3 = (k + 1) + 4 by lia,
        ih (k + 1) (by lia), show k + 2 + 2 = k + 4 by lia, ih k (by lia)]
      apply Polynomial.funext
      intro x
      simp only [quarticCofactor, eval_add, eval_mul, eval_sub, eval_pow,
        eval_one, eval_X, eval_C, eval_ofNat, Nat.cast_add, Nat.cast_ofNat, pow_add]
      ring

/-- Closed form for every row of index at least four. -/
theorem polynomial_add_four (a b : ℝ) (n : ℕ) :
    polynomial a b (n + 4) = (1 + X) ^ n *
      ((1 + X) ^ 4 + C (a * ((n : ℝ) + 3)) * X * (1 + X) ^ 2 +
        C (b / 2 * ((n : ℝ) + 2) * ((n : ℝ) + 1)) * X ^ 2) := by
  rw [polynomial_add_four_eq]
  rfl

/-- The recurrence-defined rows are the ambient-degree gamma transforms of
`gammaPolynomial`. -/
theorem polynomial_eq_gammaTransform (a b : ℝ) (n : ℕ) :
    polynomial a b n = gammaTransform n (gammaPolynomial a b n) := by
  match n with
  | 0 => simp [polynomial, gammaPolynomial, gammaTransform, gammaBasisTerm]
  | 1 => simp [polynomial, gammaPolynomial, gammaTransform, gammaBasisTerm]; ring
  | 2 =>
    simp only [polynomial, gammaPolynomial, gammaTransform_add]
    rw [show C a * X = C a * X ^ 1 by simp,
      gammaTransform_C_mul_X_pow _ (by norm_num : 1 ≤ 2 / 2)]
    have hone : (1 : ℝ[X]) = C 1 * X ^ 0 := by simp
    rw [hone, gammaTransform_C_mul_X_pow _ (by norm_num : 0 ≤ 2 / 2)]
    simp only [gammaBasisTerm, map_one]
    ring
  | 3 =>
    simp only [polynomial, gammaPolynomial, gammaTransform_add]
    rw [show C (2 * a) * X = C (2 * a) * X ^ 1 by simp,
      gammaTransform_C_mul_X_pow _ (by norm_num : 1 ≤ 3 / 2)]
    have hone : (1 : ℝ[X]) = C 1 * X ^ 0 := by simp
    rw [hone, gammaTransform_C_mul_X_pow _ (by norm_num : 0 ≤ 3 / 2)]
    simp only [gammaBasisTerm, map_one]
    ring
  | k + 4 =>
    rw [polynomial_add_four]
    simp only [gammaPolynomial, gammaTransform_add]
    rw [gammaTransform_C_mul_X_pow _ (by lia : 2 ≤ (k + 4) / 2),
      show C (a * ((k : ℝ) + 3)) * X =
        C (a * ((k : ℝ) + 3)) * X ^ 1 by simp,
      gammaTransform_C_mul_X_pow _ (by lia : 1 ≤ (k + 4) / 2)]
    have hone : (1 : ℝ[X]) = C 1 * X ^ 0 := by simp
    rw [hone, gammaTransform_C_mul_X_pow _ (by lia : 0 ≤ (k + 4) / 2)]
    simp only [gammaBasisTerm, map_one]
    rw [show k + 4 - 2 = k + 2 by lia, show k + 4 - 4 = k by lia,
      show k + 4 - 0 = k + 4 by lia]
    rw [show (X + 1 : ℝ[X]) = 1 + X by ring]
    ring

private lemma natDegree_gammaPolynomial_le_half (a b : ℝ) (n : ℕ) :
    (gammaPolynomial a b n).natDegree ≤ n / 2 := by
  match n with
  | 0 | 1 | 2 | 3 => simp only [gammaPolynomial]; compute_degree!
  | k + 4 =>
      calc
        (gammaPolynomial a b (k + 4)).natDegree ≤ 2 := by
          simp only [gammaPolynomial]
          compute_degree!
        _ ≤ (k + 4) / 2 := by lia

private lemma hasNonnegCoeffs_gammaPolynomial {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    HasNonnegCoeffs (gammaPolynomial a b n) := by
  match n with
  | 0 => exact hasNonnegCoeffs_one
  | 1 => exact hasNonnegCoeffs_one
  | 2 =>
      exact ((hasNonnegCoeffs_C ha).mul hasNonnegCoeffs_X).add hasNonnegCoeffs_one
  | 3 =>
      exact ((hasNonnegCoeffs_C (by positivity)).mul hasNonnegCoeffs_X).add
        hasNonnegCoeffs_one
  | k + 4 =>
      exact (((hasNonnegCoeffs_C (by positivity)).mul (hasNonnegCoeffs_X.pow 2)).add
        ((hasNonnegCoeffs_C (by positivity)).mul hasNonnegCoeffs_X)).add
          hasNonnegCoeffs_one

private lemma coeff_zero_gammaPolynomial (a b : ℝ) (n : ℕ) :
    (gammaPolynomial a b n).coeff 0 = 1 := by
  match n with
  | 0 | 1 | 2 | 3 | k + 4 => simp [gammaPolynomial]


private lemma quarticCofactor_monic_natDegree (a b : ℝ) (n : ℕ) :
    (quarticCofactor a b n).Monic ∧
      (quarticCofactor a b n).natDegree = 4 := by
  unfold quarticCofactor
  constructor
  · monicity!
  · compute_degree!

private theorem monic_natDegree_polynomial (a b : ℝ) (n : ℕ) :
    (polynomial a b n).Monic ∧ (polynomial a b n).natDegree = n := by
  rw [polynomial_eq_gammaTransform]
  have hdeg := natDegree_gammaTransform_le n (gammaPolynomial a b n)
  have hcoeff : (gammaTransform n (gammaPolynomial a b n)).coeff n = 1 := by
    rw [coeff_ambient_gammaTransform, coeff_zero_gammaPolynomial]
  exact ⟨monic_of_natDegree_le_of_coeff_eq_one n hdeg hcoeff,
    natDegree_eq_of_le_of_coeff_ne_zero hdeg (by rw [hcoeff]; norm_num)⟩

/-- Every polynomial in the family is monic. -/
theorem monic_polynomial (a b : ℝ) (n : ℕ) :
    (polynomial a b n).Monic :=
  (monic_natDegree_polynomial a b n).1

/-- Every polynomial in the family has degree equal to its row index. -/
theorem natDegree_polynomial (a b : ℝ) (n : ℕ) :
    (polynomial a b n).natDegree = n :=
  (monic_natDegree_polynomial a b n).2


/-- All coefficients are nonnegative when both parameters are nonnegative. -/
theorem hasNonnegCoeffs_polynomial {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    HasNonnegCoeffs (polynomial a b n) := by
  rw [polynomial_eq_gammaTransform]
  exact hasNonnegCoeffs_gammaTransform (hasNonnegCoeffs_gammaPolynomial ha hb n)

/-- Every row has constant coefficient one. -/
theorem coeff_zero_polynomial (a b : ℝ) (n : ℕ) :
    (polynomial a b n).coeff 0 = 1 := by
  rw [polynomial_eq_gammaTransform, coeff_zero_gammaTransform, coeff_zero_gammaPolynomial]

/-- Every real root is strictly negative when both parameters are nonnegative. -/
theorem roots_mem_Iio_zero {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) :
    ∀ r ∈ (polynomial a b n).roots, r ∈ Set.Iio (0 : ℝ) := by
  exact roots_neg_of_hasNonnegCoeffs_of_coeff_zero_ne
    (hasNonnegCoeffs_polynomial ha hb n) (by rw [coeff_zero_polynomial]; norm_num)

private lemma gammaPolynomial_splits {a b : ℝ}
    (hb : 0 ≤ b) (hab : 2 * b ≤ a ^ 2) (n : ℕ) :
    (gammaPolynomial a b n).Splits := by
  match n with
  | 0 | 1 => exact Splits.one
  | 2 | 3 => exact Splits.of_natDegree_le_one (by simp only [gammaPolynomial]; compute_degree!)
  | k + 4 =>
    apply quadraticPoly_splits_of_discrim_nonneg_or_linear
    rw [discrim]
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sq_nonneg ((k : ℝ) + 3)),
      mul_nonneg hb hk]

/-- Every row splits when `0 ≤ a`, `0 ≤ b`, and `2b ≤ a²`. -/
theorem splits_polynomial {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 2 * b ≤ a ^ 2) (n : ℕ) :
    (polynomial a b n).Splits := by
  rw [polynomial_eq_gammaTransform]
  exact (isRealRooted_gammaTransform_of_isRealRooted_of_hasNonnegCoeffs
    (natDegree_gammaPolynomial_le_half a b n)
    (by intro h; have hc := coeff_zero_gammaPolynomial a b n; simp [h] at hc)
    (gammaPolynomial_splits hb hab n) (hasNonnegCoeffs_gammaPolynomial ha hb n)).2

/-- For `b > 0`, the root `-1` has exactly the multiplicity forced by the
closed form. -/
theorem rootMultiplicity_neg_one_polynomial_add_four {a b : ℝ}
    (hb : 0 < b) (n : ℕ) :
    (polynomial a b (n + 4)).rootMultiplicity (-1) = n := by
  rw [polynomial_eq_gammaTransform,
    rootMultiplicity_neg_one_gammaTransform (natDegree_gammaPolynomial_le_half a b (n + 4))
      (by intro h; have hc := coeff_zero_gammaPolynomial a b (n + 4); simp [h] at hc)]
  have hdeg : (gammaPolynomial a b (n + 4)).natDegree = 2 := by
    exact natDegree_quadratic (by positivity : b / 2 * ((n : ℝ) + 2) * (n + 1) ≠ 0)
  rw [hdeg]
  lia

/-- The parameter inequality is necessary if every row splits. -/
theorem two_mul_le_sq_of_forall_splits_polynomial {a b : ℝ}
    (h : ∀ n, (polynomial a b n).Splits) : 2 * b ≤ a ^ 2 := by
  by_contra hlt
  push Not at hlt
  have hb' : 0 < b := by nlinarith
  obtain ⟨m, hm⟩ := exists_nat_gt (6 * b / (2 * b - a ^ 2))
  have hpos : 0 < 2 * b - a ^ 2 := by linarith
  have hm' : 6 * b < (2 * b - a ^ 2) * m := by rw [div_lt_iff₀ hpos] at hm; linarith
  have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
  set A := a * ((m : ℝ) + 3)
  set B := b / 2 * ((m : ℝ) + 2) * ((m : ℝ) + 1)
  have hD : A ^ 2 - 4 * B < 0 := by
    simp only [A, B]
    nlinarith [mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by norm_num : (0:ℝ) ≤ 3) :
      (m:ℝ) ≤ m + 3) hpos.le]
  have hrow := h (m + 4)
  have hne : polynomial a b (m + 4) ≠ 0 := (monic_polynomial a b (m + 4)).ne_zero
  rw [polynomial_add_four_eq] at hrow hne
  have hQs : (quarticCofactor a b m).Splits := hrow.of_dvd hne (dvd_mul_left _ _)
  have hdeg : (quarticCofactor a b m).degree ≠ 0 := by
    rw [degree_eq_natDegree (quarticCofactor_monic_natDegree a b m).1.ne_zero,
      (quarticCofactor_monic_natDegree a b m).2]
    decide
  obtain ⟨x, hx⟩ := hQs.exists_eval_eq_zero hdeg
  simp only [quarticCofactor, eval_add, eval_pow, eval_one, eval_X, eval_mul,
    eval_C] at hx
  change (1 + x) ^ 4 + A * x * (1 + x) ^ 2 + B * x ^ 2 = 0 at hx
  rcases eq_or_ne x 0 with rfl | hx0
  · norm_num at hx
  · have hx2 : 0 < x ^ 2 := by positivity
    nlinarith [sq_nonneg (2 * (1 + x) ^ 2 + A * x), mul_pos hx2 (neg_pos.2 hD)]

/-- For nonnegative parameters, every row splits exactly in the sharp range
`2b ≤ a²`. -/
theorem forall_splits_polynomial_iff {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∀ n, (polynomial a b n).Splits) ↔ 2 * b ≤ a ^ 2 := by
  constructor
  · exact two_mul_le_sq_of_forall_splits_polynomial
  · intro hab n
    exact splits_polynomial ha hb hab n

private lemma gammaPolynomial_ne_zero (a b : ℝ) (n : ℕ) :
    gammaPolynomial a b n ≠ 0 := by
  intro hzero
  have hcoeff := coeff_zero_gammaPolynomial a b n
  rw [hzero] at hcoeff
  simp at hcoeff

/-- A single quadratic formula covers every gamma row from index two. -/
private def quadraticGamma (a b : ℝ) (n : ℕ) : ℝ[X] :=
  C (b / 2 * (n : ℝ) * ((n : ℝ) - 1)) * X ^ 2 +
    C (a * ((n : ℝ) + 1)) * X + 1

private lemma gammaPolynomial_add_two_eq (a b : ℝ) (n : ℕ) :
    gammaPolynomial a b (n + 2) = quadraticGamma a b n := by
  match n with
  | 0 | 1 | k + 2 =>
    apply Polynomial.funext
    intro x
    simp only [gammaPolynomial, quadraticGamma, eval_add, eval_mul, eval_pow,
      eval_C, eval_X, eval_one, Nat.cast_zero, Nat.cast_one, Nat.cast_add, Nat.cast_ofNat]
    ring

/-- The quadratic discriminant of every full pencil is a sum of nonnegative terms. -/
private lemma allComboRealRooted_quadraticGamma {a b : ℝ}
    (hb : 0 ≤ b) (hab : 2 * b ≤ a ^ 2) (n : ℕ) :
    AllComboRealRooted (quadraticGamma a b n) (quadraticGamma a b (n + 1)) := by
  intro s t
  let z := s + t
  let q := s * (b / 2 * (n : ℝ) * ((n : ℝ) - 1)) +
    t * (b / 2 * ((n : ℝ) + 1) * (n : ℝ))
  let ell := s * (a * ((n : ℝ) + 1)) + t * (a * ((n : ℝ) + 2))
  have hform : C s * quadraticGamma a b n + C t * quadraticGamma a b (n + 1) =
      C q * X ^ 2 + C ell * X + C z := by
    simp only [quadraticGamma, q, ell, z, Nat.cast_add, Nat.cast_one, C_mul, C_add,
      C_sub, C_1, C_ofNat]
    ring
  rw [hform]
  apply quadraticPoly_splits_of_discrim_nonneg_or_linear
  rw [discrim]
  have hdecomp : ell ^ 2 - 4 * q * z =
      (a ^ 2 - 2 * b) * (((n : ℝ) + 1) * z + t) ^ 2 +
        2 * b * (t + z) ^ 2 + 6 * b * (n : ℝ) * z ^ 2 := by
    simp only [q, ell, z]
    ring
  rw [hdecomp]
  have hdelta : 0 ≤ a ^ 2 - 2 * b := sub_nonneg.mpr hab
  positivity

/-- Global Wronskian nonnegativity selects the same orientation in every degree case. -/
private lemma wronskian_quadraticGamma_nonneg {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 2 * b ≤ a ^ 2) (n : ℕ) (x : ℝ) :
    0 ≤ (wronskian (quadraticGamma a b n) (quadraticGamma a b (n + 1))).eval x := by
  have hd : discrim (a * b / 2 * n * ((n : ℝ) + 3)) (2 * b * n) a ≤ 0 := by
    rw [discrim]
    have heq : (2 * b * (n : ℝ)) ^ 2 -
        4 * (a * b / 2 * n * ((n : ℝ) + 3)) * a =
        -2 * b * n * ((a ^ 2 - 2 * b) * n + 3 * a ^ 2) := by ring
    rw [heq]
    have hdelta : 0 ≤ a ^ 2 - 2 * b := sub_nonneg.mpr hab
    have hn : -2 * b * (n : ℝ) ≤ 0 := by nlinarith [mul_nonneg hb (Nat.cast_nonneg n)]
    exact mul_nonpos_of_nonpos_of_nonneg hn (by positivity)
  have h := Quadratic.nonneg_of_nonneg_of_discrim_nonpos (by positivity) ha hd x
  convert h using 1
  simp only [quadraticGamma, wronskian, derivative_add, derivative_mul, derivative_C,
    derivative_X, derivative_pow, derivative_one, eval_add, eval_sub, eval_mul,
    eval_pow, eval_C, eval_X, eval_zero, eval_one, Nat.cast_add, Nat.cast_one]
  ring

/-- Consecutive gamma polynomials are in directed strict interlacing throughout
the sharp nonnegative parameter range. -/
theorem gammaPolynomial_strictInterl_succ {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 2 * b ≤ a ^ 2) (n : ℕ) :
    StrictInterl (gammaPolynomial a b n) (gammaPolynomial a b (n + 1)) := by
  match n with
  | 0 => simpa [gammaPolynomial] using StrictInterl.refl one_ne_zero Splits.one
  | 1 =>
    apply StrictInterl.of_natDegree_eq_zero_left
      (gammaPolynomial_ne_zero a b 1) (by simp [gammaPolynomial])
      (gammaPolynomial_ne_zero a b 2)
    simp only [gammaPolynomial]
    compute_degree
  | n + 2 =>
    have hp := (hasNonnegCoeffs_gammaPolynomial ha hb (n + 2)).pos_leadingCoeff
      (gammaPolynomial_ne_zero a b (n + 2))
    have hq := (hasNonnegCoeffs_gammaPolynomial ha hb (n + 3)).pos_leadingCoeff
      (gammaPolynomial_ne_zero a b (n + 3))
    rw [gammaPolynomial_add_two_eq] at hp
    rw [show n + 3 = (n + 1) + 2 by lia, gammaPolynomial_add_two_eq] at hq
    rw [gammaPolynomial_add_two_eq, show n + 2 + 1 = (n + 1) + 2 by lia,
      gammaPolynomial_add_two_eq]
    exact strictInterl_of_allComboRealRooted_of_wronskian_nonneg hq hp
      (allComboRealRooted_quadraticGamma hb hab n).comm
      (wronskian_quadraticGamma_nonneg ha hb hab n)

/-- Consecutive recurrence-defined rows are in directed strict interlacing
throughout the sharp nonnegative parameter range. -/
theorem polynomial_strictInterl_succ {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 2 * b ≤ a ^ 2) (n : ℕ) :
    StrictInterl (polynomial a b n) (polynomial a b (n + 1)) := by
  rw [polynomial_eq_gammaTransform, polynomial_eq_gammaTransform]
  apply (strictInterl_gammaTransform_succ_iff
    (natDegree_gammaPolynomial_le_half a b n)
    (natDegree_gammaPolynomial_le_half a b (n + 1))
    (hasNonnegCoeffs_gammaPolynomial ha hb n)
    (hasNonnegCoeffs_gammaPolynomial ha hb (n + 1))
    (by rw [coeff_zero_gammaPolynomial]; norm_num)
    (by rw [coeff_zero_gammaPolynomial]; norm_num)).2
  exact gammaPolynomial_strictInterl_succ ha hb hab n

end RealRooted.Applications.OEIS.QuarticGamma
