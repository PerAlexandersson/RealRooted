module

public import RealRooted.CombinatorialExamples.Touchard
public import RealRooted.Recurrence.RowModel
public import RealRooted.Recurrence.Uniqueness
public import RealRooted.Transforms.ReverseHermite

set_option rr.row.explain true
set_option linter.style.longLine false

/-!
# The row polynomials of OEIS A395326

The model rows are scaled reverse-Hermite transforms of the Touchard
polynomials.  Preservation of zero-aware proper position supplies adjacent
interlacing, and an order-two recurrence identifies generated row sequences
with the model.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted.Applications.OEIS.A395326

/-- The scaled reverse-Hermite transform used by the A395326 model. -/
def transform (p : ℝ[X]) : ℝ[X] :=
  (reverseHermiteTransform (p.comp (C (1 / 2 : ℝ) * X))).comp (C 4 * X)

/-- The Touchard-transform model for the rows of A395326. -/
def polynomial (n : ℕ) : ℝ[X] := transform (touchard n)

private lemma transform_add (p q : ℝ[X]) :
    transform (p + q) = transform p + transform q := by
  simp only [transform, add_comp, reverseHermiteTransform_add]

private lemma transform_C_mul (a : ℝ) (p : ℝ[X]) :
    transform (C a * p) = C a * transform p := by
  unfold transform
  rw [mul_comp, C_comp, reverseHermiteTransform_C_mul, mul_comp, C_comp]

private lemma transform_X_mul (p : ℝ[X]) :
    transform (X * p) = 2 * X * transform p + X * transform p.derivative := by
  unfold transform
  rw [mul_comp, X_comp]
  rw [show C (1 / 2 : ℝ) * X * p.comp (C (1 / 2 : ℝ) * X) =
      C (1 / 2 : ℝ) * (X * p.comp (C (1 / 2 : ℝ) * X)) by ring]
  rw [reverseHermiteTransform_C_mul, reverseHermiteTransform_X_mul]
  simp only [mul_comp, C_comp, X_comp, add_comp, Polynomial.derivative_comp,
    derivative_mul, derivative_C, derivative_X, zero_mul, zero_add]
  norm_num
  rw [reverseHermiteTransform_C_mul, mul_comp, C_comp]
  apply Polynomial.funext
  intro x
  simp only [eval_add, eval_mul, eval_C, eval_X, eval_ofNat]
  ring

private lemma transform_derivative (p : ℝ[X]) :
    (transform p).derivative =
      2 * transform p.derivative +
        C (1 / 2 : ℝ) * transform p.derivative.derivative := by
  unfold transform
  rw [Polynomial.derivative_comp]
  simp only [derivative_mul, derivative_C, derivative_X, zero_mul, zero_add]
  norm_num
  rw [reverseHermiteTransform_derivative]
  simp only [Polynomial.derivative_comp, derivative_mul, derivative_C,
    derivative_X, zero_mul, zero_add]
  norm_num
  simp_rw [reverseHermiteTransform_C_mul]
  simp only [mul_comp, C_comp]
  apply Polynomial.funext
  intro x
  simp only [eval_add, eval_mul, eval_C, eval_ofNat]
  ring

private lemma transform_touchard_step (p : ℝ[X]) :
    transform (X * p + X * p.derivative) =
      2 * X * transform p + 3 * X * transform p.derivative +
        X * transform p.derivative.derivative := by
  rw [transform_add, transform_X_mul, transform_X_mul]
  ring

private lemma transform_touchard_step_derivative (p : ℝ[X]) :
    transform ((X * p + X * p.derivative).derivative) =
      transform p + transform p.derivative + 2 * X * transform p.derivative +
        3 * X * transform p.derivative.derivative +
        X * transform p.derivative.derivative.derivative := by
  simp only [derivative_add, derivative_mul, derivative_X, one_mul]
  rw [transform_add, transform_add, transform_add, transform_X_mul]
  rw [transform_X_mul]
  ring

private lemma transform_touchard_step_secondDerivative (p : ℝ[X]) :
    transform ((X * p + X * p.derivative).derivative.derivative) =
      2 * transform p.derivative + 2 * transform p.derivative.derivative +
        2 * X * transform p.derivative.derivative +
        3 * X * transform p.derivative.derivative.derivative +
        X * transform p.derivative.derivative.derivative.derivative := by
  simp only [derivative_add, derivative_mul, derivative_X, one_mul]
  rw [transform_add, transform_add, transform_add, transform_add,
    transform_X_mul]
  rw [transform_add, transform_X_mul]
  ring

private lemma polynomial_succ (n : ℕ) :
    polynomial (n + 1) =
      2 * X * transform (touchard n) +
        3 * X * transform (touchard n).derivative +
        X * transform (touchard n).derivative.derivative := by
  rw [polynomial, touchard_succ]
  exact transform_touchard_step (touchard n)

/-- The generated order-two update for A395326. -/
def nextRow (_n : ℕ) (q p : ℝ[X]) : ℝ[X] :=
  (-4 * X ^ 2) * p.derivative.derivative +
    (4 * X) * q.derivative +
    (-14 * X ^ 2 - 2 * X) * p.derivative +
    (-1 + 8 * X) * q +
    (-12 * X ^ 2 - 3 * X) * p

/-- The model satisfies the generated order-two recurrence. -/
theorem polynomial_step (n : ℕ) :
    polynomial (n + 2) = nextRow n (polynomial (n + 1)) (polynomial n) := by
  let p := touchard n
  have hnext : polynomial (n + 1) =
      2 * X * transform p + 3 * X * transform p.derivative +
        X * transform p.derivative.derivative := by
    simpa [p] using polynomial_succ n
  have hnext_der : (polynomial (n + 1)).derivative =
      2 * transform p + (4 * X + 3) * transform p.derivative +
        (7 * X + 1) * transform p.derivative.derivative +
        C (7 / 2 : ℝ) * X * transform p.derivative.derivative.derivative +
        C (1 / 2 : ℝ) * X *
          transform p.derivative.derivative.derivative.derivative := by
    rw [hnext]
    simp only [derivative_add, derivative_mul, derivative_X, one_mul,
      derivative_ofNat]
    rw [transform_derivative, transform_derivative, transform_derivative]
    norm_num [map_ofNat]
    apply Polynomial.funext
    intro x
    simp only [eval_add, eval_mul, eval_C, eval_X, eval_ofNat, eval_one]
    ring
  have hpder : (polynomial n).derivative =
      2 * transform p.derivative +
        C (1 / 2 : ℝ) * transform p.derivative.derivative := by
    simpa [polynomial, p] using transform_derivative p
  have hpder2 : (polynomial n).derivative.derivative =
      4 * transform p.derivative.derivative +
        2 * transform p.derivative.derivative.derivative +
        C (1 / 4 : ℝ) *
          transform p.derivative.derivative.derivative.derivative := by
    rw [hpder]
    simp only [derivative_add, derivative_mul, derivative_ofNat, derivative_C,
      zero_mul, zero_add]
    rw [transform_derivative, transform_derivative]
    norm_num [map_ofNat]
    apply Polynomial.funext
    intro x
    simp only [eval_add, eval_mul, eval_C, eval_ofNat]
    ring
  have htwo : polynomial (n + 2) =
      2 * X * polynomial (n + 1) +
        3 * X * (transform p + transform p.derivative +
          2 * X * transform p.derivative +
          3 * X * transform p.derivative.derivative +
          X * transform p.derivative.derivative.derivative) +
        X * (2 * transform p.derivative +
          2 * transform p.derivative.derivative +
          2 * X * transform p.derivative.derivative +
          3 * X * transform p.derivative.derivative.derivative +
          X * transform p.derivative.derivative.derivative.derivative) := by
    rw [show n + 2 = (n + 1) + 1 by lia, polynomial_succ]
    rw [show touchard (n + 1) = X * p + X * p.derivative by
      simpa [p] using touchard_succ n]
    rw [transform_touchard_step, transform_touchard_step_derivative,
      transform_touchard_step_secondDerivative]
    simp_all
  unfold nextRow
  rw [htwo, hnext_der, hpder2, hpder, hnext]
  change _ = _ + (-12 * X ^ 2 - 3 * X) * transform p
  apply Polynomial.funext
  intro x
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_pow,
    eval_ofNat, eval_neg, eval_one]
  ring

private lemma transform_one : transform 1 = 1 := by
  unfold transform
  simp

private lemma transform_zero : transform 0 = 0 := by
  simp [transform]

private lemma transform_X : transform X = 2 * X := by
  have h := transform_X_mul (1 : ℝ[X])
  simpa [transform_one, transform_zero] using h

private lemma polynomial_zero : polynomial 0 = 1 := by
  simp [polynomial, touchard, transform_one]

private lemma polynomial_one : polynomial 1 = 2 * X := by
  simp [polynomial, touchard, transform_X]

/-- The model row indexed by `n` has degree `n`. -/
theorem polynomial_natDegree (n : ℕ) : (polynomial n).natDegree = n := by
  let p := (touchard n).comp (C (1 / 2 : ℝ) * X)
  have hp : p ≠ 0 := by
    exact (isRealRooted_comp_C_mul_X (touchard_posLeadingCoeff n).ne_zero
      (strictInterl_touchard_succ n).1.2 (by norm_num)).1
  have hpdeg : p.natDegree = n := by
    dsimp [p]
    rw [natDegree_comp, natDegree_touchard]
    norm_num
  unfold polynomial transform
  rw [natDegree_comp, natDegree_reverseHermiteTransform hp, hpdeg]
  norm_num

private lemma polynomial_ne_zero (n : ℕ) : polynomial n ≠ 0 := by
  intro hzero
  have hdegree := polynomial_natDegree n
  rw [hzero, natDegree_zero] at hdegree
  cases n with
  | zero => simp [polynomial_zero] at hzero
  | succ n => simp at hdegree

private lemma polynomial_interl (n : ℕ) :
    Interl (polynomial n) (polynomial (n + 1)) := by
  let f := (touchard n).comp (C (1 / 2 : ℝ) * X)
  let g := (touchard (n + 1)).comp (C (1 / 2 : ℝ) * X)
  have htouch := strictInterl_touchard_succ n
  have hfpf : IsPFPolynomial f := by
    simpa only [f, map_zero, add_zero] using
      IsPFPolynomial.comp_C_mul_X_add_C (a := 1 / 2) (d := 0)
        (by norm_num) (by norm_num)
        (IsPFPolynomial.of_realRooted_nonneg
          (touchard_nonnegCoeffs n) htouch.1.2)
  have hgpf : IsPFPolynomial g := by
    simpa only [g, map_zero, add_zero] using
      IsPFPolynomial.comp_C_mul_X_add_C (a := 1 / 2) (d := 0)
        (by norm_num) (by norm_num)
        (IsPFPolynomial.of_realRooted_nonneg
          (touchard_nonnegCoeffs (n + 1)) htouch.2.1.2)
  have hfg : StrictInterl f g := htouch.comp_C_mul_X (by norm_num)
  have htransform :
      Interl (reverseHermiteTransform f) (reverseHermiteTransform g) :=
    reverseHermiteTransform_strictInterl_to_interl hfpf hgpf hfg
  simpa only [polynomial, transform, f, g] using
    htransform.comp_C_mul_X (by norm_num)

/-- Consecutive model rows interlace. -/
theorem polynomial_interlaces (n : ℕ) :
    Interlaces (polynomial n) (polynomial (n + 1)) := by
  apply (polynomial_interl n).toStrictInterl_of_ne
      (polynomial_ne_zero n) (polynomial_ne_zero (n + 1)) |>.toInterlaces
  rw [polynomial_natDegree, polynomial_natDegree]

/-- Consecutive rows of any sequence satisfying the A395326 recurrence
interlace. -/
@[rr_row_model]
theorem interlaces_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hone : P 1 = 2 * X)
    (hrec : ∀ n : ℕ, P (n + 2) = nextRow n (P (n + 1)) (P n))
    (n : ℕ) :
    Interlaces (P n) (P (n + 1)) := by
  have heq := sequence_eq_of_same_lag_two_recurrence
    (P := P) (Q := polynomial) (fun m p q => nextRow m p q)
    (hzero.trans polynomial_zero.symm) (hone.trans polynomial_one.symm)
    hrec polynomial_step
  rw [heq n, heq (n + 1)]
  exact polynomial_interlaces n

end RealRooted.Applications.OEIS.A395326
