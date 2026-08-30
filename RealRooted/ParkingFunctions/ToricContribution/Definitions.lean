import Mathlib.RingTheory.Polynomial.Pochhammer
import RealRooted.Derivative

/-!
# Algebra for the A390883 toric-contribution family

This file defines the terminating hypergeometric polynomials and differential
operators used in the common-interlacer proof. All hypergeometric expressions
are finite polynomial sums; no analytic hypergeometric function is introduced.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace ParkingFunctions
namespace ToricContribution

/-- The parity data `n = 2m + ε`, with `ε ∈ {0,1}`, used throughout the
toric-contribution normalization. -/
structure ParityData (n : ℕ) where
  m : ℕ
  epsilon : ℕ
  decompose : n = 2 * m + epsilon
  epsilon_lt_two : epsilon < 2

/-- The canonical parity data of a natural number. -/
def parityData (n : ℕ) : ParityData n where
  m := n / 2
  epsilon := n % 2
  decompose := by simpa using (Nat.div_add_mod n 2).symm
  epsilon_lt_two := Nat.mod_lt n (by norm_num)

/-- The half-integer parameter `c = ε + 1/2`. -/
def ParityData.c {n : ℕ} (p : ParityData n) : ℝ :=
  p.epsilon + 1 / 2

theorem ParityData.epsilon_eq_zero_or_one {n : ℕ} (p : ParityData n) :
    p.epsilon = 0 ∨ p.epsilon = 1 := by
  have hεlt := p.epsilon_lt_two
  apply Nat.le_one_iff_eq_zero_or_eq_one.mp
  lia

theorem ParityData.c_pos {n : ℕ} (p : ParityData n) :
    0 < p.c := by
  simp only [ParityData.c]
  positivity

theorem ParityData.m_pos {n : ℕ} (p : ParityData n) (hn : 2 ≤ n) :
    0 < p.m := by
  have hdecompose := p.decompose
  have hεlt := p.epsilon_lt_two
  have hε : p.epsilon ≤ 1 := by lia
  lia

/-- The real rising factorial `(a)_k`. -/
def realRisingFactorial (a : ℝ) (k : ℕ) : ℝ :=
  (ascPochhammer ℝ k).eval a

@[simp]
theorem realRisingFactorial_zero (a : ℝ) :
    realRisingFactorial a 0 = 1 := by
  simp [realRisingFactorial]

@[simp]
theorem realRisingFactorial_succ (a : ℝ) (k : ℕ) :
    realRisingFactorial a (k + 1) =
      realRisingFactorial a k * (a + k) := by
  simpa [realRisingFactorial] using ascPochhammer_succ_eval k a

theorem realRisingFactorial_succ_left (a : ℝ) (k : ℕ) :
    realRisingFactorial a (k + 1) =
      a * realRisingFactorial (a + 1) k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [realRisingFactorial_succ, ih, realRisingFactorial_succ]
      push_cast
      ring

theorem realRisingFactorial_pos {a : ℝ} (k : ℕ) (ha : 0 < a) :
    0 < realRisingFactorial a k := by
  simpa [realRisingFactorial] using ascPochhammer_pos k a ha

/-- Coefficient of the terminating polynomial `R_d`. -/
def rCoeff (m ε d k : ℕ) : ℝ :=
  realRisingFactorial (-(m : ℝ)) k *
      realRisingFactorial ((m : ℝ) + 1 + ε) k *
      realRisingFactorial ((ε : ℝ) + 1 / 2 + d) k /
    (realRisingFactorial ((ε : ℝ) + 1 / 2) k *
      realRisingFactorial ((ε : ℝ) + 1 / 2 + d + 3 / 2) k * k.factorial)

/-- The normalized reciprocal toric-contribution polynomial `R_d`. -/
def rPolynomial (m ε d : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (m + 1), monomial k (rCoeff m ε d k)

/-- Coefficient of the degree-`m - 1` Jacobi interlacer `J`. -/
def jCoeff (m ε k : ℕ) : ℝ :=
  realRisingFactorial (1 - (m : ℝ)) k *
      realRisingFactorial ((m : ℝ) + 2 + ε) k /
    (realRisingFactorial ((ε : ℝ) + 2) k * k.factorial)

/-- The terminating Jacobi interlacer `J`. -/
def jPolynomial (m ε : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range m, monomial k (jCoeff m ε k)

@[simp]
theorem coeff_rPolynomial (m ε d k : ℕ) :
    (rPolynomial m ε d).coeff k =
      if k ≤ m then rCoeff m ε d k else 0 := by
  simp only [rPolynomial, finsetSum_coeff, coeff_monomial]
  rw [Finset.sum_ite_eq' (Finset.range (m + 1)) k]
  simp

@[simp]
theorem coeff_jPolynomial (m ε k : ℕ) :
    (jPolynomial m ε).coeff k =
      if k < m then jCoeff m ε k else 0 := by
  simp only [jPolynomial, finsetSum_coeff, coeff_monomial]
  rw [Finset.sum_ite_eq' (Finset.range m) k]
  simp

@[simp]
theorem rCoeff_zero (m ε d : ℕ) :
    rCoeff m ε d 0 = 1 := by
  simp [rCoeff]

@[simp]
theorem jCoeff_zero (m ε : ℕ) :
    jCoeff m ε 0 = 1 := by
  simp [jCoeff]

theorem rCoeff_offset_zero (m ε k : ℕ) :
    rCoeff m ε 0 k =
      realRisingFactorial (-(m : ℝ)) k *
          realRisingFactorial ((m : ℝ) + 1 + ε) k /
        (realRisingFactorial ((ε : ℝ) + 2) k * k.factorial) := by
  let A := realRisingFactorial (-(m : ℝ)) k
  let B := realRisingFactorial ((m : ℝ) + 1 + ε) k
  let C := realRisingFactorial ((ε : ℝ) + 1 / 2) k
  let D := realRisingFactorial ((ε : ℝ) + 2) k
  let F : ℝ := k.factorial
  have hc : 0 < C := by
    apply realRisingFactorial_pos
    positivity
  simp only [rCoeff, Nat.cast_zero, add_zero]
  rw [show (ε : ℝ) + 1 / 2 + 3 / 2 = (ε : ℝ) + 2 by ring]
  change A * B * C / (C * D * F) = A * B / (D * F)
  calc
    A * B * C / (C * D * F) = C * (A * B) / (C * (D * F)) := by
      congr 1 <;> ring
    _ = A * B / (D * F) := mul_div_mul_left _ _ hc.ne'

theorem rCoeff_offset_zero_succ (m ε k : ℕ) :
    rCoeff m ε 0 (k + 1) = jCoeff m ε (k + 1) - jCoeff m ε k := by
  rw [rCoeff_offset_zero]
  simp only [jCoeff]
  rw [realRisingFactorial_succ_left (-(m : ℝ)) k,
    realRisingFactorial_succ_left ((m : ℝ) + 1 + ε) k,
    realRisingFactorial_succ (1 - (m : ℝ)) k,
    realRisingFactorial_succ ((m : ℝ) + 2 + ε) k,
    realRisingFactorial_succ ((ε : ℝ) + 2) k, Nat.factorial_succ]
  have hd : 0 < realRisingFactorial (2 + (ε : ℝ)) k := by
    apply realRisingFactorial_pos
    positivity
  have hk : 0 < (k.factorial : ℝ) := by positivity
  have hsucc : 0 < (k : ℝ) + 1 := by positivity
  push_cast
  field_simp [hd.ne', hk.ne', hsucc.ne']
  ring_nf

theorem jCoeff_self_eq_zero (m ε : ℕ) (hm : 0 < m) :
    jCoeff m ε m = 0 := by
  cases m with
  | zero => contradiction
  | succ m =>
      have hzero : realRisingFactorial (1 - ((m + 1 : ℕ) : ℝ)) (m + 1) = 0 := by
        rw [realRisingFactorial_succ]
        push_cast
        ring
      simp only [jCoeff, hzero, zero_mul, zero_div]

@[simp]
theorem coeff_one_sub_X_mul_zero (p : ℝ[X]) :
    ((1 - X) * p).coeff 0 = p.coeff 0 := by
  simp [sub_mul]

theorem coeff_one_sub_X_mul_succ (p : ℝ[X]) (k : ℕ) :
    ((1 - X) * p).coeff (k + 1) = p.coeff (k + 1) - p.coeff k := by
  rw [sub_mul, one_mul, coeff_sub, coeff_X_mul]

/-- The offset-zero terminating hypergeometric polynomial has the endpoint
factor predicted by the finite Euler transformation. -/
theorem rPolynomial_zero_eq_one_sub_X_mul_jPolynomial
    (m ε : ℕ) (hm : 0 < m) :
    rPolynomial m ε 0 = (1 - X) * jPolynomial m ε := by
  ext k
  cases k with
  | zero =>
      simp [hm]
  | succ k =>
      rw [coeff_rPolynomial, coeff_one_sub_X_mul_succ]
      by_cases hk : k < m
      · rw [if_pos (by lia : k + 1 ≤ m), coeff_jPolynomial,
          coeff_jPolynomial, if_pos hk]
        by_cases hksucc : k + 1 < m
        · rw [if_pos hksucc, rCoeff_offset_zero_succ]
        · have heq : k + 1 = m := by lia
          rw [if_neg hksucc, rCoeff_offset_zero_succ, heq,
            jCoeff_self_eq_zero m ε hm, zero_sub]
      · rw [if_neg (by lia : ¬k + 1 ≤ m), coeff_jPolynomial,
          coeff_jPolynomial, if_neg (by lia : ¬k + 1 < m),
          if_neg (by lia : ¬k < m), sub_zero]

theorem natDegree_rPolynomial_le (m ε d : ℕ) :
    (rPolynomial m ε d).natDegree ≤ m := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  exact (Polynomial.natDegree_monomial_le _).trans (Finset.mem_range_succ_iff.mp hk)

theorem natDegree_jPolynomial_le (m ε : ℕ) :
    (jPolynomial m ε).natDegree ≤ m - 1 := by
  cases m with
  | zero => simp [jPolynomial]
  | succ m =>
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro k hk
      exact (Polynomial.natDegree_monomial_le _).trans (by simpa using hk)

@[simp]
theorem rPolynomial_eval_zero (m ε d : ℕ) :
    (rPolynomial m ε d).eval 0 = 1 := by
  rw [← coeff_zero_eq_eval_zero]
  simp only [rPolynomial, finsetSum_coeff, coeff_monomial]
  rw [Finset.sum_ite_eq' (Finset.range (m + 1)) 0]
  simp

@[simp]
theorem jPolynomial_eval_zero (m ε : ℕ) (hm : 0 < m) :
    (jPolynomial m ε).eval 0 = 1 := by
  rw [← coeff_zero_eq_eval_zero]
  simp only [jPolynomial, finsetSum_coeff, coeff_monomial]
  rw [Finset.sum_ite_eq' (Finset.range m) 0]
  simp [hm]

/-- The polynomial `z(1-z)` appearing in every Darboux operator. -/
def intervalWeight : ℝ[X] :=
  X * (1 - X)

/-- The first-order operator `M_{a,b} f = z(1-z)f' + (a-bz)f`. -/
def insertionOperator (a b : ℝ) (f : ℝ[X]) : ℝ[X] :=
  intervalWeight * f.derivative + (C a - C b * X) * f

@[simp]
theorem insertionOperator_eval_zero (a b : ℝ) (f : ℝ[X]) :
    (insertionOperator a b f).eval 0 = a * f.eval 0 := by
  simp [insertionOperator, intervalWeight]

theorem coeff_insertionOperator_succ (a b : ℝ) (f : ℝ[X]) (k : ℕ) :
    (insertionOperator a b f).coeff (k + 1) =
      (k + 1 + a) * f.coeff (k + 1) - (k + b) * f.coeff k := by
  have hform :
      insertionOperator a b f =
        X * f.derivative - X * (X * f.derivative) +
          C a * f - C b * (X * f) := by
    simp only [insertionOperator, intervalWeight]
    ring
  rw [hform, coeff_sub, coeff_add, coeff_sub, coeff_X_mul,
    coeff_C_mul, coeff_C_mul, coeff_X_mul, coeff_derivative]
  cases k with
  | zero =>
      simp
      ring
  | succ k =>
      rw [coeff_X_mul, coeff_derivative,
        show k + 1 + 1 = (k + 1) + 1 by rfl, coeff_X_mul]
      push_cast
      ring

/-- The triangular differential family beginning with the `d`th derivative
of `J` and applying the horizontal insertion operators successively. -/
def triangleFamily (c : ℝ) (J : ℝ[X]) (d : ℕ) : ℕ → ℝ[X]
  | 0 => (derivative^[d]) J
  | t + 1 => insertionOperator (c + t) (c + d + 1) (triangleFamily c J d t)

@[simp]
theorem triangleFamily_zero (c : ℝ) (J : ℝ[X]) (d : ℕ) :
    triangleFamily c J d 0 = (derivative^[d]) J := by
  rfl

@[simp]
theorem triangleFamily_succ (c : ℝ) (J : ℝ[X]) (d t : ℕ) :
    triangleFamily c J d (t + 1) =
      insertionOperator (c + t) (c + d + 1) (triangleFamily c J d t) := by
  rfl

theorem triangleFamily_eval_zero (c : ℝ) (J : ℝ[X]) (d t : ℕ) :
    (triangleFamily c J d t).eval 0 =
      realRisingFactorial c t * ((derivative^[d]) J).eval 0 := by
  induction t with
  | zero => simp
  | succ t ih =>
      rw [triangleFamily_succ, insertionOperator_eval_zero, ih,
        realRisingFactorial_succ]
      ring

/-- The signed triangular family used to make every value at zero positive. -/
def signedTriangleFamily (c : ℝ) (J : ℝ[X]) (d t : ℕ) : ℝ[X] :=
  C ((-1 : ℝ) ^ d) * triangleFamily c J d t

/-- Darboux commutation for the interval-insertion operators. The scalar
relation is exactly the one satisfied by the A390883 triangular parameters. -/
theorem insertionOperator_comp_commute
    (a b A B : ℝ) (h : B - A = b - a + 1) (f : ℝ[X]) :
    insertionOperator a b (insertionOperator A B f) =
      insertionOperator A (B - 1) (insertionOperator a (b + 1) f) := by
  have hB : B = A + b - a + 1 := by linarith
  rw [hB]
  apply Polynomial.funext
  intro x
  simp only [insertionOperator, intervalWeight, derivative_add, derivative_sub,
    derivative_mul, derivative_C, derivative_X, derivative_one, zero_mul, one_mul,
    eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_one]
  ring

/-- The Darboux square specialized to the triangular A390883 parameters. -/
theorem triangle_insertionOperator_comp_commute
    (c : ℝ) (d t : ℕ) (f : ℝ[X]) :
    insertionOperator (c + t) (c + d + 1)
        (insertionOperator (c + d + 3 / 2) (c + 2 * d + 7 / 2 - t) f) =
      insertionOperator (c + d + 3 / 2) (c + 2 * d + 7 / 2 - t - 1)
        (insertionOperator (c + t) (c + d + 1 + 1) f) := by
  apply insertionOperator_comp_commute
  ring

end ToricContribution
end ParkingFunctions
end RealRooted
