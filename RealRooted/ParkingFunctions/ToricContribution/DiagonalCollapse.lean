import RealRooted.ParkingFunctions.ToricContribution.TriangleAlgebra

/-!
# Diagonal collapse for the toric-contribution triangle

This file conjugates the horizontal insertion operators by powers of `1-X`.
The resulting Euler operators act diagonally on coefficients, reducing the
remaining identification with `R_d` to a finite coefficient identity.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace ParkingFunctions
namespace ToricContribution

/-- The shifted Euler operator `(X D + a)`. -/
def eulerShiftOperator (a : ℝ) (f : ℝ[X]) : ℝ[X] :=
  X * f.derivative + C a * f

/-- Successive shifted Euler operators with parameters `c, c+1, ...`. -/
def risingEulerOperator (c : ℝ) : ℕ → ℝ[X] → ℝ[X]
  | 0, f => f
  | t + 1, f => eulerShiftOperator (c + t) (risingEulerOperator c t f)

/-- Coefficients of the Euler-transformed terminating `₂F₁`. -/
def eulerTransformedCoeff (m ε d k : ℕ) : ℝ :=
  realRisingFactorial (-(m : ℝ)) k *
      realRisingFactorial ((m : ℝ) + 1 + ε) k /
    (realRisingFactorial ((ε : ℝ) + d + 2) k * k.factorial)

/-- The Euler-transformed terminating `₂F₁` of degree at most `m`. -/
def eulerTransformedPolynomial (m ε d : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (m + 1), monomial k (eulerTransformedCoeff m ε d k)

@[simp]
theorem coeff_eulerTransformedPolynomial (m ε d k : ℕ) :
    (eulerTransformedPolynomial m ε d).coeff k =
      if k ≤ m then eulerTransformedCoeff m ε d k else 0 := by
  simp only [eulerTransformedPolynomial, finsetSum_coeff, coeff_monomial]
  rw [Finset.sum_ite_eq' (Finset.range (m + 1)) k]
  simp

@[simp]
theorem eulerTransformedCoeff_zero (m ε d : ℕ) :
    eulerTransformedCoeff m ε d 0 = 1 := by
  simp [eulerTransformedCoeff]

theorem eulerTransformedCoeff_succ_mul (m ε d k : ℕ) :
    ((ε : ℝ) + d + 2 + k) * (k + 1) *
        eulerTransformedCoeff m ε d (k + 1) =
      (-(m : ℝ) + k) * ((m : ℝ) + 1 + ε + k) *
        eulerTransformedCoeff m ε d k := by
  simp only [eulerTransformedCoeff]
  rw [realRisingFactorial_succ, realRisingFactorial_succ,
    realRisingFactorial_succ, Nat.factorial_succ]
  have hC : 0 < realRisingFactorial ((ε : ℝ) + d + 2) k := by
    apply realRisingFactorial_pos
    positivity
  have hk : 0 < (k.factorial : ℝ) := by positivity
  have hsucc : 0 < (k : ℝ) + 1 := by positivity
  push_cast
  field_simp [hC.ne', hk.ne', hsucc.ne']

theorem eulerTransformedCoeff_succ_degree_eq_zero (m ε d : ℕ) :
    eulerTransformedCoeff m ε d (m + 1) = 0 := by
  simp only [eulerTransformedCoeff, realRisingFactorial_succ]
  ring

theorem natDegree_eulerTransformedPolynomial_le (m ε d : ℕ) :
    (eulerTransformedPolynomial m ε d).natDegree ≤ m := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  exact (Polynomial.natDegree_monomial_le _).trans
    (Finset.mem_range_succ_iff.mp hk)

/-- The Euler-transformed polynomial satisfies the Jacobi differential
equation with parameters `α=ε+d+1` and `β=-d-1`. -/
theorem eulerTransformedPolynomial_differentialEquation (m ε d : ℕ) :
    C ((m : ℝ) * (m + ε + 1)) * eulerTransformedPolynomial m ε d +
      insertionOperator (ε + d + 2) (ε + 2)
        (eulerTransformedPolynomial m ε d).derivative = 0 := by
  apply Polynomial.ext
  intro k
  cases k with
  | zero =>
      rw [coeff_add, coeff_C_mul, coeff_zero]
      have hM0 :
          (insertionOperator (ε + d + 2) (ε + 2)
            (eulerTransformedPolynomial m ε d).derivative).coeff 0 =
            (ε + d + 2) * (eulerTransformedPolynomial m ε d).coeff 1 := by
        rw [coeff_zero_eq_eval_zero, insertionOperator_eval_zero,
          ← coeff_zero_eq_eval_zero, coeff_derivative]
        ring
      have hcoeff1 :
          (eulerTransformedPolynomial m ε d).coeff 1 =
            eulerTransformedCoeff m ε d 1 := by
        rw [coeff_eulerTransformedPolynomial]
        by_cases hm : 1 ≤ m
        · rw [if_pos hm]
        · have hm0 : m = 0 := by lia
          rw [if_neg hm, hm0, eulerTransformedCoeff_succ_degree_eq_zero]
      rw [hM0, coeff_eulerTransformedPolynomial, if_pos (Nat.zero_le m),
        eulerTransformedCoeff_zero, hcoeff1]
      have hrec := eulerTransformedCoeff_succ_mul m ε d 0
      simp only [eulerTransformedCoeff_zero] at hrec ⊢
      push_cast at hrec ⊢
      ring_nf at hrec ⊢
      linear_combination hrec
  | succ k =>
      rw [coeff_add, coeff_C_mul, coeff_insertionOperator_succ,
        coeff_derivative, coeff_derivative, coeff_zero]
      by_cases hk : k + 1 ≤ m
      · have hcur :
            (eulerTransformedPolynomial m ε d).coeff (k + 1) =
              eulerTransformedCoeff m ε d (k + 1) := by
          rw [coeff_eulerTransformedPolynomial, if_pos hk]
        have hnext :
            (eulerTransformedPolynomial m ε d).coeff (k + 1 + 1) =
              eulerTransformedCoeff m ε d (k + 1 + 1) := by
          rw [coeff_eulerTransformedPolynomial]
          by_cases hle : k + 1 + 1 ≤ m
          · rw [if_pos hle]
          · have heq : k + 1 + 1 = m + 1 := by lia
            rw [if_neg hle, heq, eulerTransformedCoeff_succ_degree_eq_zero]
        rw [hcur, hnext]
        have hrec := eulerTransformedCoeff_succ_mul m ε d (k + 1)
        push_cast at hrec ⊢
        ring_nf at hrec ⊢
        linear_combination hrec
      · have hcur :
            (eulerTransformedPolynomial m ε d).coeff (k + 1) = 0 := by
          rw [coeff_eulerTransformedPolynomial, if_neg hk]
        have hnext :
            (eulerTransformedPolynomial m ε d).coeff (k + 1 + 1) = 0 := by
          rw [coeff_eulerTransformedPolynomial, if_neg (by lia)]
        rw [hcur, hnext]
        ring

/-- Product rule for a power of `1-X`, normalized for later gauge calculations. -/
theorem derivative_one_sub_X_pow_succ_mul (r : ℕ) (f : ℝ[X]) :
    ((1 - X : ℝ[X]) ^ (r + 1) * f).derivative =
      (1 - X : ℝ[X]) ^ (r + 1) * f.derivative -
        C ((r : ℝ) + 1) * (1 - X : ℝ[X]) ^ r * f := by
  rw [derivative_mul, derivative_pow_succ]
  simp only [derivative_sub, derivative_one, derivative_X, zero_sub, map_add,
    map_one, map_natCast]
  ring

/-- Second product rule for a power of `1-X`, with a positive exponent at
least two. -/
theorem derivative_derivative_one_sub_X_pow_add_two_mul (r : ℕ) (f : ℝ[X]) :
    ((1 - X : ℝ[X]) ^ (r + 2) * f).derivative.derivative =
      (1 - X : ℝ[X]) ^ (r + 2) * f.derivative.derivative -
        C (2 * ((r : ℝ) + 2)) * (1 - X : ℝ[X]) ^ (r + 1) * f.derivative +
          C (((r : ℝ) + 2) * (r + 1)) * (1 - X : ℝ[X]) ^ r * f := by
  rw [show r + 2 = (r + 1) + 1 by lia,
    derivative_one_sub_X_pow_succ_mul, derivative_sub,
    derivative_one_sub_X_pow_succ_mul]
  rw [show C ((r + 1 : ℕ) + 1 : ℝ) * (1 - X) ^ (r + 1) * f =
      C ((r + 1 : ℕ) + 1 : ℝ) * ((1 - X) ^ (r + 1) * f) by ring,
    derivative_C_mul, derivative_one_sub_X_pow_succ_mul]
  push_cast
  apply Polynomial.funext
  intro x
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_one, eval_pow]
  ring

/-- Multiplication by `(1-X)^(r+1)` gauges a Jacobi differential equation by
lowering the second insertion parameter by `2(r+1)`. -/
theorem one_sub_X_pow_succ_gauge_differentialEquation
    (a eigenvalue : ℝ) (r : ℕ) (f : ℝ[X]) :
    C (eigenvalue + (r + 1) * a) * ((1 - X) ^ (r + 1) * f) +
        insertionOperator a (a - (r + 1) + 1)
          (((1 - X) ^ (r + 1) * f).derivative) =
      (1 - X) ^ (r + 1) *
        (C eigenvalue * f +
          insertionOperator a (a + (r + 1) + 1) f.derivative) := by
  cases r with
  | zero =>
      have hfirst := derivative_one_sub_X_pow_succ_mul 0 f
      have hfirst' :
          ((1 - X : ℝ[X]) * f).derivative =
            (1 - X) * f.derivative - f := by
        simpa using hfirst
      have hsecond :
          ((1 - X) * f).derivative.derivative =
            (1 - X) * f.derivative.derivative - 2 * f.derivative := by
        rw [hfirst', derivative_sub, derivative_mul]
        simp only [derivative_sub, derivative_one, derivative_X, zero_sub]
        ring
      have hfirstPow :
          ((1 - X : ℝ[X]) ^ (0 + 1) * f).derivative =
            (1 - X) * f.derivative - f := by
        simpa using hfirst'
      have hsecondPow :
          ((1 - X : ℝ[X]) ^ (0 + 1) * f).derivative.derivative =
            (1 - X) * f.derivative.derivative - 2 * f.derivative := by
        simpa using hsecond
      simp only [insertionOperator]
      rw [hsecondPow, hfirstPow]
      simp only [intervalWeight, Nat.cast_zero, zero_add, pow_one, map_add,
        map_sub, map_one]
      apply Polynomial.funext
      intro x
      simp only [eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_one,
        eval_ofNat]
      ring
  | succ r =>
      have hfirst := derivative_one_sub_X_pow_succ_mul (r + 1) f
      have hsecond := derivative_derivative_one_sub_X_pow_add_two_mul r f
      have hsecond' :
          ((1 - X : ℝ[X]) ^ (r + 1 + 1) * f).derivative.derivative =
            (1 - X) ^ (r + 2) * f.derivative.derivative -
              C (2 * ((r : ℝ) + 2)) * (1 - X) ^ (r + 1) * f.derivative +
                C (((r : ℝ) + 2) * (r + 1)) * (1 - X) ^ r * f := by
        rw [show r + 1 + 1 = r + 2 by lia]
        exact hsecond
      simp only [insertionOperator]
      rw [hsecond', hfirst]
      simp only [intervalWeight, Nat.cast_add, Nat.cast_one, map_add, map_sub,
        map_one]
      have hpowOne : (1 - X : ℝ[X]) ^ (r + 1) = (1 - X) ^ r * (1 - X) := by
        rw [pow_succ]
      have hpowTwo :
          (1 - X : ℝ[X]) ^ (r + 2) = (1 - X) ^ r * (1 - X) * (1 - X) := by
        rw [show r + 2 = (r + 1) + 1 by lia, pow_succ, pow_succ]
      rw [hpowOne, hpowTwo]
      apply Polynomial.funext
      intro x
      simp only [eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_one, eval_pow]
      ring

/-- The gauged derivative row has the differential equation of the terminating
Euler transform. -/
theorem one_sub_X_pow_mul_iterate_derivative_jPolynomial_differentialEquation
    (m ε d : ℕ) (hm : 0 < m) :
    C ((m : ℝ) * (m + ε + 1)) *
          ((1 - X) ^ (d + 1) * (derivative^[d]) (jPolynomial m ε)) +
        insertionOperator (ε + d + 2) (ε + 2)
          (((1 - X) ^ (d + 1) *
            (derivative^[d]) (jPolynomial m ε)).derivative) = 0 := by
  let f := (derivative^[d]) (jPolynomial m ε)
  let a : ℝ := ε + d + 2
  let eigenvalue : ℝ :=
    (((m - 1 : ℕ) : ℝ) - d) * ((m - 1 : ℕ) + d + ε + 3)
  have hbase :
      C eigenvalue * f +
        insertionOperator a (a + (d + 1) + 1) f.derivative = 0 := by
    have h := iteratedDerivative_jPolynomial_differentialEquation m ε d
    dsimp only [f, a, eigenvalue]
    have hparameter :
        (ε : ℝ) + d + 2 + (d + 1) + 1 = (ε : ℝ) + 2 * d + 4 := by
      ring
    rw [hparameter]
    simpa only [Function.iterate_succ_apply'] using h
  have hgauge := one_sub_X_pow_succ_gauge_differentialEquation
    a eigenvalue d f
  have haLow : a - (d + 1) + 1 = (ε : ℝ) + 2 := by
    dsimp only [a]
    ring
  have heigen : eigenvalue + (d + 1) * a =
      (m : ℝ) * (m + ε + 1) := by
    have hmCast : (((m - 1 : ℕ) : ℝ)) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub (by lia)]
      norm_num
    dsimp only [eigenvalue, a]
    rw [hmCast]
    ring
  rw [hbase, mul_zero] at hgauge
  rw [heigen, haLow] at hgauge
  exact hgauge

/-- Finite Euler transformation for the derivative row of `J`, normalized by
its constant coefficient. -/
theorem one_sub_X_pow_mul_iterate_derivative_jPolynomial_eq
    (m ε d : ℕ) (hm : 0 < m) (hd : d ≤ m - 1) :
    (1 - X) ^ (d + 1) * (derivative^[d]) (jPolynomial m ε) =
      C ((d.factorial : ℝ) * jCoeff m ε d) *
        eulerTransformedPolynomial m ε d := by
  let p : ℝ[X] :=
    (1 - X) ^ (d + 1) * (derivative^[d]) (jPolynomial m ε)
  let scale : ℝ := (d.factorial : ℝ) * jCoeff m ε d
  have hdata := iteratedDerivative_jPolynomial_intervalRootData m ε d hm hd
  have hscaleEval :
      ((derivative^[d]) (jPolynomial m ε)).eval 0 = scale := by
    exact iterate_derivative_jPolynomial_eval_zero m ε d (by lia)
  have hscale : scale ≠ 0 := by
    have hpos := negOnePow_mul_iterate_derivative_jPolynomial_eval_zero_pos
      m ε d hm hd
    rw [hscaleEval] at hpos
    exact right_ne_zero_of_mul (ne_of_gt hpos)
  have hα : -1 < (ε : ℝ) + d + 1 := by
    have hε : 0 ≤ (ε : ℝ) := by positivity
    have hdReal : 0 ≤ (d : ℝ) := by positivity
    linarith
  apply eq_of_jacobi_differential_equation m
    (α := (ε : ℝ) + d + 1) (β := -((d : ℝ) + 1)) hα
  · calc
      ((1 - X) ^ (d + 1) *
          (derivative^[d]) (jPolynomial m ε)).natDegree ≤
          ((1 - X : ℝ[X]) ^ (d + 1)).natDegree +
            ((derivative^[d]) (jPolynomial m ε)).natDegree :=
        Polynomial.natDegree_mul_le
      _ = d + 1 + (m - 1 - d) := by
        have hw : (1 - X : ℝ[X]).natDegree = 1 := by
          rw [show (1 - X : ℝ[X]) = -(X - 1) by ring,
            Polynomial.natDegree_neg]
          simpa using (Polynomial.natDegree_X_sub_C (R := ℝ) 1)
        rw [Polynomial.natDegree_pow, hdata.natDegree_eq]
        rw [hw, mul_one]
      _ = m := by lia
  · rw [Polynomial.natDegree_C_mul hscale]
    exact natDegree_eulerTransformedPolynomial_le m ε d
  · rw [coeff_zero_eq_eval_zero, coeff_zero_eq_eval_zero]
    have hE0 : (eulerTransformedPolynomial m ε d).eval 0 = 1 := by
      rw [← coeff_zero_eq_eval_zero, coeff_eulerTransformedPolynomial,
        if_pos (Nat.zero_le m), eulerTransformedCoeff_zero]
    simp only [eval_mul, eval_pow, eval_sub, eval_one, eval_X, sub_zero,
      one_pow, hscaleEval, eval_C, hE0, mul_one]
    dsimp only [scale]
    ring
  · have hp :=
      one_sub_X_pow_mul_iterate_derivative_jPolynomial_differentialEquation
        m ε d hm
    simp only [insertionOperator, intervalWeight] at hp ⊢
    ring_nf at hp ⊢
    exact hp
  · have hE := eulerTransformedPolynomial_differentialEquation m ε d
    have hscaled := congrArg (C scale * ·) hE
    dsimp only [scale] at hscaled ⊢
    simp only [mul_zero, derivative_C_mul, insertionOperator, intervalWeight] at hscaled ⊢
    ring_nf at hscaled ⊢
    exact hscaled

/-- A shifted Euler operator multiplies coefficient `k` by `k+a`. -/
theorem coeff_eulerShiftOperator (a : ℝ) (f : ℝ[X]) (k : ℕ) :
    (eulerShiftOperator a f).coeff k = (k + a) * f.coeff k := by
  simp only [eulerShiftOperator, coeff_add, coeff_C_mul]
  cases k with
  | zero =>
      simp
  | succ k =>
      rw [coeff_X_mul, coeff_derivative]
      push_cast
      ring

/-- Successive shifted Euler operators multiply coefficient `k` by the rising
factorial `(c+k)_t`. -/
theorem coeff_risingEulerOperator (c : ℝ) (t : ℕ) (f : ℝ[X]) (k : ℕ) :
    (risingEulerOperator c t f).coeff k =
      realRisingFactorial (c + k) t * f.coeff k := by
  induction t with
  | zero => simp [risingEulerOperator]
  | succ t ih =>
      rw [risingEulerOperator, coeff_eulerShiftOperator, ih,
        realRisingFactorial_succ]
      ring

/-- Splitting a rising factorial after its first block. -/
theorem realRisingFactorial_add (a : ℝ) (n k : ℕ) :
    realRisingFactorial a (n + k) =
      realRisingFactorial a n * realRisingFactorial (a + n) k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.add_succ, realRisingFactorial_succ, ih,
        realRisingFactorial_succ]
      push_cast
      ring

/-- The crossed form of rising-factorial block splitting. -/
theorem realRisingFactorial_shift_mul (a : ℝ) (d k : ℕ) :
    realRisingFactorial (a + k) d * realRisingFactorial a k =
      realRisingFactorial a d * realRisingFactorial (a + d) k := by
  rw [mul_comm (realRisingFactorial (a + k) d),
    ← realRisingFactorial_add a k d, ← realRisingFactorial_add a d k,
    Nat.add_comm]

/-- The Euler multiplier supplies exactly the extra numerator/denominator
ratio in the coefficient of `R_d`. -/
theorem realRisingFactorial_mul_eulerTransformedCoeff
    (m ε d k : ℕ) :
    realRisingFactorial ((ε : ℝ) + 1 / 2 + k) d *
        eulerTransformedCoeff m ε d k =
      realRisingFactorial ((ε : ℝ) + 1 / 2) d * rCoeff m ε d k := by
  let c : ℝ := ε + 1 / 2
  have hc : 0 < realRisingFactorial c k := by
    apply realRisingFactorial_pos
    dsimp only [c]
    positivity
  have hden : 0 < realRisingFactorial ((ε : ℝ) + d + 2) k := by
    apply realRisingFactorial_pos
    positivity
  have hfactorial : 0 < (k.factorial : ℝ) := by positivity
  have hshift := realRisingFactorial_shift_mul c d k
  dsimp only [c] at hshift
  simp only [eulerTransformedCoeff, rCoeff]
  rw [show (ε : ℝ) + 1 / 2 + d + 3 / 2 = (ε : ℝ) + d + 2 by ring]
  let A := realRisingFactorial (-(m : ℝ)) k
  let B := realRisingFactorial ((m : ℝ) + 1 + ε) k
  let C₀ := realRisingFactorial ((ε : ℝ) + 1 / 2) k
  let C₁ := realRisingFactorial ((ε : ℝ) + 1 / 2 + d) k
  let D := realRisingFactorial ((ε : ℝ) + d + 2) k
  let F : ℝ := k.factorial
  let S := realRisingFactorial ((ε : ℝ) + 1 / 2 + k) d
  let T := realRisingFactorial ((ε : ℝ) + 1 / 2) d
  change S * (A * B / (D * F)) = T * (A * B * C₁ / (C₀ * D * F))
  change S * C₀ = T * C₁ at hshift
  have hC₀ : C₀ ≠ 0 := hc.ne'
  have hD : D ≠ 0 := hden.ne'
  have hF : F ≠ 0 := hfactorial.ne'
  field_simp [hC₀, hD, hF]
  linear_combination hshift * (A * B)

/-- Conjugating one insertion step by powers of `1-X` produces a shifted
Euler operator. -/
theorem one_sub_X_pow_mul_insertionOperator (a : ℝ) (r : ℕ) (f : ℝ[X]) :
    (1 - X) ^ r * insertionOperator a (a + (r + 1)) f =
      eulerShiftOperator a ((1 - X) ^ (r + 1) * f) := by
  simp only [eulerShiftOperator, insertionOperator, intervalWeight,
    derivative_mul, derivative_pow_succ, derivative_sub, derivative_one,
    derivative_X, zero_sub, map_add, map_one, map_natCast]
  ring

/-- The horizontal triangle recursion telescopes to successive Euler
operators after multiplication by the corresponding power of `1-X`. -/
theorem one_sub_X_pow_mul_triangleFamily
    (c : ℝ) (J : ℝ[X]) (d t : ℕ) (ht : t ≤ d) :
    (1 - X) ^ (d + 1 - t) * triangleFamily c J d t =
      risingEulerOperator c t ((1 - X) ^ (d + 1) * (derivative^[d]) J) := by
  induction t with
  | zero => simp [risingEulerOperator]
  | succ t ih =>
      have ht' : t ≤ d := by lia
      rw [show d + 1 - (t + 1) = d - t by lia, triangleFamily_succ]
      have hb : c + d + 1 = (c + t) + (d - t + 1) := by
        ring
      rw [hb, ← Nat.cast_sub ht', one_sub_X_pow_mul_insertionOperator]
      have hexponent : d - t + 1 = d + 1 - t := by lia
      rw [hexponent, ih ht', risingEulerOperator]

/-- At the diagonal, the factor is exactly `1-X`. -/
theorem one_sub_X_mul_triangleFamily_diagonal (c : ℝ) (J : ℝ[X]) (d : ℕ) :
    (1 - X) * triangleFamily c J d d =
      risingEulerOperator c d ((1 - X) ^ (d + 1) * (derivative^[d]) J) := by
  simpa using one_sub_X_pow_mul_triangleFamily c J d d le_rfl

/-- Every nonexceptional triangle diagonal collapses, after multiplication by
`1-X`, to the normalized toric-contribution polynomial `R_d`. -/
theorem one_sub_X_mul_triangleFamily_diagonal_eq_C_mul_rPolynomial
    (m ε d : ℕ) (hm : 0 < m) (hd : d ≤ m - 1) :
    (1 - X) * triangleFamily ((ε : ℝ) + 1 / 2)
        (jPolynomial m ε) d d =
      C (realRisingFactorial ((ε : ℝ) + 1 / 2) d *
          ((d.factorial : ℝ) * jCoeff m ε d)) * rPolynomial m ε d := by
  rw [one_sub_X_mul_triangleFamily_diagonal,
    one_sub_X_pow_mul_iterate_derivative_jPolynomial_eq m ε d hm hd]
  apply Polynomial.ext
  intro k
  rw [coeff_risingEulerOperator, coeff_C_mul, coeff_C_mul,
    coeff_eulerTransformedPolynomial, coeff_rPolynomial]
  by_cases hk : k ≤ m
  · rw [if_pos hk, if_pos hk]
    rw [show realRisingFactorial ((ε : ℝ) + 1 / 2 + k) d *
          ((d.factorial : ℝ) * jCoeff m ε d *
            eulerTransformedCoeff m ε d k) =
        ((d.factorial : ℝ) * jCoeff m ε d) *
          (realRisingFactorial ((ε : ℝ) + 1 / 2 + k) d *
            eulerTransformedCoeff m ε d k) by ring,
      realRisingFactorial_mul_eulerTransformedCoeff]
    ring
  · rw [if_neg hk, if_neg hk]
    ring

end ToricContribution
end ParkingFunctions
end RealRooted
