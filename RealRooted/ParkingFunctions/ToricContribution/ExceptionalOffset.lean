import RealRooted.JacobiBetaZeroOrthogonality
import RealRooted.ObreschkoffConverse
import RealRooted.ParkingFunctions.ToricContribution.FiniteOffsets

/-!
# The exceptional A390883 toric-contribution offset

This file treats the offset `d = m`, where the factorization through the
finite derivative triangle drops degree.  The replacement is the
Euler-inverse family whose two distinguished parameters give `R_(m-1)` and
`R_m`.
-/

open Polynomial
open MeasureTheory Set

noncomputable section

namespace RealRooted
namespace ParkingFunctions
namespace ToricContribution

/-- Coefficients of the degree-`m` Jacobi polynomial underlying the
exceptional Euler-inverse family. -/
def exceptionalBaseCoeff (m ε k : ℕ) : ℝ :=
  realRisingFactorial (-(m : ℝ)) k *
      realRisingFactorial ((ε : ℝ) + 1 / 2 + m) k /
    (realRisingFactorial ((ε : ℝ) + 1 / 2) k * k.factorial)

/-- The terminating Jacobi polynomial `F` used to define the Euler-inverse
family. -/
def exceptionalBasePolynomial (m ε : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (m + 1), monomial k (exceptionalBaseCoeff m ε k)

/-- The Euler inverse of `F` at parameter `γ`: coefficient `k` is multiplied
by `γ / (γ + k)`. -/
def exceptionalEulerInverse (m ε : ℕ) (γ : ℝ) : ℝ[X] :=
  ∑ k ∈ Finset.range (m + 1),
    monomial k (exceptionalBaseCoeff m ε k * γ / (γ + k))

@[simp]
theorem coeff_exceptionalBasePolynomial (m ε k : ℕ) :
    (exceptionalBasePolynomial m ε).coeff k =
      if k ≤ m then exceptionalBaseCoeff m ε k else 0 := by
  simp only [exceptionalBasePolynomial, finsetSum_coeff, coeff_monomial]
  rw [Finset.sum_ite_eq' (Finset.range (m + 1)) k]
  simp

@[simp]
theorem coeff_exceptionalEulerInverse (m ε k : ℕ) (γ : ℝ) :
    (exceptionalEulerInverse m ε γ).coeff k =
      if k ≤ m then
        exceptionalBaseCoeff m ε k * γ / (γ + k)
      else 0 := by
  simp only [exceptionalEulerInverse, finsetSum_coeff, coeff_monomial]
  rw [Finset.sum_ite_eq' (Finset.range (m + 1)) k]
  simp

@[simp]
theorem exceptionalBaseCoeff_zero (m ε : ℕ) :
    exceptionalBaseCoeff m ε 0 = 1 := by
  simp [exceptionalBaseCoeff]

theorem exceptionalBaseCoeff_succ_mul (m ε k : ℕ) :
    ((ε : ℝ) + 1 / 2 + k) * (k + 1) *
        exceptionalBaseCoeff m ε (k + 1) =
      (-(m : ℝ) + k) * ((ε : ℝ) + 1 / 2 + m + k) *
        exceptionalBaseCoeff m ε k := by
  simp only [exceptionalBaseCoeff]
  rw [realRisingFactorial_succ, realRisingFactorial_succ,
    realRisingFactorial_succ, Nat.factorial_succ]
  have hC : 0 < realRisingFactorial ((ε : ℝ) + 1 / 2) k := by
    apply realRisingFactorial_pos
    positivity
  have hk : 0 < (k.factorial : ℝ) := by positivity
  have hsucc : 0 < (k : ℝ) + 1 := by positivity
  push_cast
  field_simp [hC.ne', hk.ne', hsucc.ne']

theorem exceptionalBaseCoeff_succ_degree_eq_zero (m ε : ℕ) :
    exceptionalBaseCoeff m ε (m + 1) = 0 := by
  simp only [exceptionalBaseCoeff, realRisingFactorial_succ]
  ring

theorem natDegree_exceptionalBasePolynomial_le (m ε : ℕ) :
    (exceptionalBasePolynomial m ε).natDegree ≤ m := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  exact (Polynomial.natDegree_monomial_le _).trans
    (Finset.mem_range_succ_iff.mp hk)

/-- The terminating base polynomial satisfies the beta-zero shifted-Jacobi
differential equation. -/
theorem exceptionalBasePolynomial_differentialEquation (m ε : ℕ) :
    C ((m : ℝ) * ((m : ℝ) + ε + 1 / 2)) *
          exceptionalBasePolynomial m ε +
        insertionOperator ((ε : ℝ) + 1 / 2) ((ε : ℝ) + 3 / 2)
          (exceptionalBasePolynomial m ε).derivative = 0 := by
  apply Polynomial.ext
  intro k
  cases k with
  | zero =>
      rw [coeff_add, coeff_C_mul, coeff_zero]
      have hoperator :
          (insertionOperator ((ε : ℝ) + 1 / 2)
            ((ε : ℝ) + 3 / 2)
            (exceptionalBasePolynomial m ε).derivative).coeff 0 =
              ((ε : ℝ) + 1 / 2) *
                (exceptionalBasePolynomial m ε).coeff 1 := by
        rw [coeff_zero_eq_eval_zero, insertionOperator_eval_zero,
          ← coeff_zero_eq_eval_zero, coeff_derivative]
        ring
      have hcoeffOne :
          (exceptionalBasePolynomial m ε).coeff 1 =
            exceptionalBaseCoeff m ε 1 := by
        rw [coeff_exceptionalBasePolynomial]
        by_cases hm : 1 ≤ m
        · rw [if_pos hm]
        · have hm0 : m = 0 := by lia
          rw [if_neg hm, hm0, exceptionalBaseCoeff_succ_degree_eq_zero]
      rw [hoperator, coeff_exceptionalBasePolynomial,
        if_pos (Nat.zero_le m), exceptionalBaseCoeff_zero, hcoeffOne]
      have hrec := exceptionalBaseCoeff_succ_mul m ε 0
      simp only [exceptionalBaseCoeff_zero] at hrec ⊢
      push_cast at hrec ⊢
      ring_nf at hrec ⊢
      linear_combination hrec
  | succ k =>
      rw [coeff_add, coeff_C_mul, coeff_insertionOperator_succ,
        coeff_derivative, coeff_derivative, coeff_zero]
      by_cases hk : k + 1 ≤ m
      · have hcur :
            (exceptionalBasePolynomial m ε).coeff (k + 1) =
              exceptionalBaseCoeff m ε (k + 1) := by
          rw [coeff_exceptionalBasePolynomial, if_pos hk]
        have hnext :
            (exceptionalBasePolynomial m ε).coeff (k + 1 + 1) =
              exceptionalBaseCoeff m ε (k + 1 + 1) := by
          rw [coeff_exceptionalBasePolynomial]
          by_cases hle : k + 1 + 1 ≤ m
          · rw [if_pos hle]
          · have heq : k + 1 + 1 = m + 1 := by lia
            rw [if_neg hle, heq,
              exceptionalBaseCoeff_succ_degree_eq_zero]
        rw [hcur, hnext]
        have hrec := exceptionalBaseCoeff_succ_mul m ε (k + 1)
        push_cast at hrec ⊢
        ring_nf at hrec ⊢
        linear_combination hrec
      · have hcur :
            (exceptionalBasePolynomial m ε).coeff (k + 1) = 0 := by
          rw [coeff_exceptionalBasePolynomial, if_neg hk]
        have hnext :
            (exceptionalBasePolynomial m ε).coeff (k + 1 + 1) = 0 := by
          rw [coeff_exceptionalBasePolynomial, if_neg (by lia)]
        rw [hcur, hnext]
        ring

/-- The base polynomial is the constant-term-one normalization of the
beta-zero shifted Jacobi polynomial. -/
theorem exceptionalBasePolynomial_eq_C_mul_shiftedJacobi (m ε : ℕ) :
    exceptionalBasePolynomial m ε =
      C ((Ring.choose
        ((m : ℝ) + ((ε : ℝ) - 1 / 2)) m)⁻¹) *
        shiftedJacobi m ((ε : ℝ) - 1 / 2) 0 := by
  let α : ℝ := ε - 1 / 2
  let scale : ℝ := (Ring.choose ((m : ℝ) + α) m)⁻¹
  have hα : -1 < α := by
    dsimp only [α]
    have hε : 0 ≤ (ε : ℝ) := by positivity
    linarith
  have hchoose : 0 < Ring.choose ((m : ℝ) + α) m := by
    apply Polynomial.ring_choose_pos
    linarith
  change exceptionalBasePolynomial m ε =
    C scale * shiftedJacobi m α 0
  apply eq_of_jacobi_differential_equation m (α := α) (β := 0) hα
  · exact natDegree_exceptionalBasePolynomial_le m ε
  · rw [natDegree_C_mul (inv_ne_zero hchoose.ne'),
      natDegree_shiftedJacobi m hα (by norm_num)]
  · rw [coeff_exceptionalBasePolynomial, if_pos (Nat.zero_le m),
      exceptionalBaseCoeff_zero, coeff_C_mul, coeff_shiftedJacobi,
      if_pos (Nat.zero_le m)]
    simp [scale, hchoose.ne']
  · have hbase := exceptionalBasePolynomial_differentialEquation m ε
    dsimp only [insertionOperator, intervalWeight] at hbase ⊢
    dsimp only [α]
    ring_nf at hbase ⊢
    exact hbase
  · have h := shiftedJacobi_differential_equation m α 0
    have hscaled := congrArg (C scale * ·) h
    simp only [mul_zero, derivative_C_mul] at hscaled ⊢
    dsimp only [scale, α] at hscaled ⊢
    ring_nf at hscaled ⊢
    exact hscaled

theorem exceptionalBasePolynomial_betaZeroInner_eq_zero
    (m ε : ℕ) (q : ℝ[X]) (hq : q.natDegree < m) :
    jacobiBetaZeroInner ((ε : ℝ) - 1 / 2)
      (exceptionalBasePolynomial m ε) q = 0 := by
  have hα : -1 < (ε : ℝ) - 1 / 2 := by
    have hε : 0 ≤ (ε : ℝ) := by positivity
    linarith
  rw [exceptionalBasePolynomial_eq_C_mul_shiftedJacobi,
    jacobiBetaZeroInner_C_mul_left,
    shiftedJacobi_betaZeroInner_eq_zero hα q hq, mul_zero]

private theorem jacobiBetaZeroFunctional_exceptionalBase_mul_X_pow
    (m ε j : ℕ) :
    jacobiBetaZeroFunctional ((ε : ℝ) - 1 / 2)
        (exceptionalBasePolynomial m ε * X ^ j) =
      ∑ k ∈ Finset.range (m + 1),
        exceptionalBaseCoeff m ε k /
          ((ε : ℝ) + 1 / 2 + k + j) := by
  rw [exceptionalBasePolynomial, Finset.sum_mul,
    jacobiBetaZeroFunctional_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp [X_pow_eq_monomial, monomial_mul_monomial,
    jacobiBetaZeroMoment]
  ring

private theorem jacobiBetaZeroFunctional_exceptionalEulerInverse_mul_X_pow
    (m ε j : ℕ) (γ : ℝ) :
    jacobiBetaZeroFunctional ((ε : ℝ) - 1 / 2)
        (exceptionalEulerInverse m ε γ * X ^ j) =
      ∑ k ∈ Finset.range (m + 1),
        (exceptionalBaseCoeff m ε k * (γ / (γ + k))) /
          ((ε : ℝ) + 1 / 2 + k + j) := by
  rw [exceptionalEulerInverse, Finset.sum_mul,
    jacobiBetaZeroFunctional_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp [X_pow_eq_monomial, monomial_mul_monomial,
    jacobiBetaZeroMoment]
  ring

/-- Moments of the exterior power weight on `(1, ∞)`. -/
def exceptionalExteriorFunctional (c γ : ℝ) (p : ℝ[X]) : ℝ :=
  p.sum fun k a => a / (γ - c - k)

@[simp]
theorem exceptionalExteriorFunctional_add
    (c γ : ℝ) (p q : ℝ[X]) :
    exceptionalExteriorFunctional c γ (p + q) =
      exceptionalExteriorFunctional c γ p +
        exceptionalExteriorFunctional c γ q := by
  simp only [exceptionalExteriorFunctional]
  apply Polynomial.sum_add_index <;> simp [add_div]

@[simp]
theorem exceptionalExteriorFunctional_sum {ι : Type*}
    (c γ : ℝ) (s : Finset ι) (p : ι → ℝ[X]) :
    exceptionalExteriorFunctional c γ (∑ i ∈ s, p i) =
      ∑ i ∈ s, exceptionalExteriorFunctional c γ (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [exceptionalExteriorFunctional]
  | insert i s hi hs => simp [hi, hs]

@[simp]
theorem exceptionalExteriorFunctional_C_mul
    (c γ a : ℝ) (p : ℝ[X]) :
    exceptionalExteriorFunctional c γ (C a * p) =
      a * exceptionalExteriorFunctional c γ p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [mul_add, hp, hq, mul_add]
  | monomial n b =>
      simp [exceptionalExteriorFunctional, C_mul_monomial, mul_div_assoc]

@[simp]
theorem exceptionalExteriorFunctional_X_pow (c γ : ℝ) (k : ℕ) :
    exceptionalExteriorFunctional c γ (X ^ k) =
      1 / (γ - c - k) := by
  simp [exceptionalExteriorFunctional, X_pow_eq_monomial]

private theorem integral_Ioi_finsetPolynomial
    (c γ : ℝ) (b : ℕ → ℝ) (M : ℕ)
    (h : ∀ j ∈ Finset.range M, c + j < γ) :
    (∫ x in Ioi (1 : ℝ),
        (∑ j ∈ Finset.range M, b j * x ^ j) * x ^ (c - γ - 1)) =
      ∑ j ∈ Finset.range M, b j / (γ - c - j) := by
  have hexponent : ∀ j ∈ Finset.range M,
      c - γ - 1 + (j : ℝ) < -1 := by
    intro j hj
    have hjγ := h j hj
    linarith
  have hintegrable : ∀ j ∈ Finset.range M,
      IntegrableOn
        (fun x : ℝ => b j * x ^ (c - γ - 1 + (j : ℝ)))
        (Ioi 1) volume := by
    intro j hj
    exact (integrableOn_Ioi_rpow_of_lt
      (hexponent j hj) one_pos).const_mul _
  have hintegral :
      (∫ x in Ioi (1 : ℝ),
          (∑ j ∈ Finset.range M, b j * x ^ j) * x ^ (c - γ - 1)) =
        ∫ x in Ioi (1 : ℝ), ∑ j ∈ Finset.range M,
          b j * x ^ (c - γ - 1 + (j : ℝ)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hxpos : 0 < x := lt_trans one_pos hx
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Real.rpow_add hxpos, Real.rpow_natCast]
    ring
  rw [hintegral, integral_finsetSum _ hintegrable]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_const_mul,
    integral_Ioi_rpow_of_lt (hexponent j hj) one_pos, Real.one_rpow]
  have hexponentEq :
      c - γ - 1 + (j : ℝ) + 1 = -(γ - c - j) := by ring
  rw [hexponentEq]
  have hden : γ - c - (j : ℝ) ≠ 0 := by
    have hjγ := h j hj
    linarith
  field_simp

/-- The exterior coefficient functional is integration on `(1, ∞)` against
the signed-moment weight. -/
theorem exceptionalExteriorFunctional_eq_integral
    (c γ : ℝ) (p : ℝ[X]) (hγ : c + p.natDegree < γ) :
    exceptionalExteriorFunctional c γ p =
      ∫ x in Ioi (1 : ℝ), p.eval x * x ^ (c - γ - 1) := by
  have hjγ : ∀ j ∈ Finset.range (p.natDegree + 1), c + j < γ := by
    intro j hj
    have hjlt : j < p.natDegree + 1 := Finset.mem_range.mp hj
    have hjle : j ≤ p.natDegree := by lia
    have hjleCast : (j : ℝ) ≤ p.natDegree := by exact_mod_cast hjle
    linarith
  calc
    exceptionalExteriorFunctional c γ p =
        ∑ j ∈ Finset.range (p.natDegree + 1),
          p.coeff j / (γ - c - j) := by
      conv_lhs => rw [p.as_sum_range_C_mul_X_pow]
      rw [exceptionalExteriorFunctional_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [exceptionalExteriorFunctional_C_mul,
        exceptionalExteriorFunctional_X_pow]
      ring
    _ = ∫ x in Ioi (1 : ℝ),
          (∑ j ∈ Finset.range (p.natDegree + 1),
            p.coeff j * x ^ j) * x ^ (c - γ - 1) :=
      (integral_Ioi_finsetPolynomial c γ p.coeff
        (p.natDegree + 1) hjγ).symm
    _ = ∫ x in Ioi (1 : ℝ), p.eval x * x ^ (c - γ - 1) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      change
        (∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * x ^ j) *
            x ^ (c - γ - 1) =
          p.eval x * x ^ (c - γ - 1)
      have heval :
        (∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * x ^ j) =
            (∑ j ∈ Finset.range (p.natDegree + 1),
              C (p.coeff j) * X ^ j).eval x := by
          rw [eval_finsetSum]
          simp
      rw [heval, ← p.as_sum_range_C_mul_X_pow]

private theorem exceptionalEulerInverse_eval_one_eq_sum
    (m ε : ℕ) (γ : ℝ) :
    (exceptionalEulerInverse m ε γ).eval 1 =
      ∑ k ∈ Finset.range (m + 1),
        exceptionalBaseCoeff m ε k * (γ / (γ + k)) := by
  rw [exceptionalEulerInverse, eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [eval_monomial, one_pow, mul_one]
  rw [mul_div_assoc]

private theorem exceptionalEulerInverse_partialFraction_sum
    (m ε j : ℕ) {γ : ℝ}
    (hγ : (ε : ℝ) + 1 / 2 + m - 1 < γ) (hj : j < m) :
    ∑ k ∈ Finset.range (m + 1),
        (exceptionalBaseCoeff m ε k * (γ / (γ + k))) /
          ((ε : ℝ) + 1 / 2 + k + j) =
      (∑ k ∈ Finset.range (m + 1),
        exceptionalBaseCoeff m ε k * (γ / (γ + k))) /
          ((ε : ℝ) + 1 / 2 + j - γ) := by
  let c : ℝ := ε + 1 / 2
  have hm : 0 < m := by lia
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  have hγpos : 0 < γ := by
    have hmcast : (1 : ℝ) ≤ m := by exact_mod_cast hm
    dsimp only [c] at hc
    linarith
  have hden : c + (j : ℝ) - γ ≠ 0 := by
    have hjcast : (j : ℝ) ≤ (m : ℝ) - 1 := by
      have hjone : j + 1 ≤ m := by lia
      have hjoneCast : (j : ℝ) + 1 ≤ m := by exact_mod_cast hjone
      linarith
    dsimp only [c] at hγ ⊢
    linarith
  have horth := exceptionalBasePolynomial_betaZeroInner_eq_zero
    m ε (X ^ j) (by simp [hj])
  rw [jacobiBetaZeroInner,
    jacobiBetaZeroFunctional_exceptionalBase_mul_X_pow] at horth
  have hkey : ∀ k ∈ Finset.range (m + 1),
      (exceptionalBaseCoeff m ε k * (γ / (γ + k))) /
          (c + k + j) =
        (exceptionalBaseCoeff m ε k * (γ / (γ + k))) /
            (c + j - γ) -
          (γ / (c + j - γ)) *
            (exceptionalBaseCoeff m ε k / (c + k + j)) := by
    intro k hk
    have hγk : γ + (k : ℝ) ≠ 0 := by positivity
    have hckj : c + (k : ℝ) + j ≠ 0 := by positivity
    field_simp [hγk, hckj, hden]
    ring
  rw [Finset.sum_congr rfl hkey, Finset.sum_sub_distrib,
    ← Finset.mul_sum, horth, mul_zero, sub_zero, Finset.sum_div]

/-- The signed moment identity for a monomial of degree below `m`. -/
theorem jacobiBetaZeroFunctional_exceptionalEulerInverse_mul_X_pow_eq
    (m ε j : ℕ) {γ : ℝ}
    (hγ : (ε : ℝ) + 1 / 2 + m - 1 < γ) (hj : j < m) :
    jacobiBetaZeroFunctional ((ε : ℝ) - 1 / 2)
        (exceptionalEulerInverse m ε γ * X ^ j) =
      -(exceptionalEulerInverse m ε γ).eval 1 *
        exceptionalExteriorFunctional ((ε : ℝ) + 1 / 2) γ
          (X ^ j) := by
  rw [jacobiBetaZeroFunctional_exceptionalEulerInverse_mul_X_pow,
    exceptionalEulerInverse_partialFraction_sum m ε j hγ hj,
    exceptionalEulerInverse_eval_one_eq_sum,
    exceptionalExteriorFunctional_X_pow]
  have hden : γ - ((ε : ℝ) + 1 / 2) - j ≠ 0 := by
    have hjcast : (j : ℝ) ≤ (m : ℝ) - 1 := by
      have hjone : j + 1 ≤ m := by lia
      have hjoneCast : (j : ℝ) + 1 ≤ m := by exact_mod_cast hjone
      linarith
    linarith
  rw [show (ε : ℝ) + 1 / 2 + j - γ =
    -(γ - ((ε : ℝ) + 1 / 2) - j) by ring, div_neg]
  ring

/-- The signed moment identity for every polynomial of degree below `m`. -/
theorem jacobiBetaZeroFunctional_exceptionalEulerInverse_mul_eq
    (m ε : ℕ) {γ : ℝ} (p : ℝ[X])
    (hγ : (ε : ℝ) + 1 / 2 + m - 1 < γ)
    (hp : p.natDegree < m) :
    jacobiBetaZeroFunctional ((ε : ℝ) - 1 / 2)
        (exceptionalEulerInverse m ε γ * p) =
      -(exceptionalEulerInverse m ε γ).eval 1 *
        exceptionalExteriorFunctional ((ε : ℝ) + 1 / 2) γ p := by
  rw [p.as_sum_range_C_mul_X_pow' hp, Finset.mul_sum,
    jacobiBetaZeroFunctional_sum, exceptionalExteriorFunctional_sum,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [show exceptionalEulerInverse m ε γ *
        (C (p.coeff j) * X ^ j) =
      C (p.coeff j) * (exceptionalEulerInverse m ε γ * X ^ j) by ring,
    jacobiBetaZeroFunctional_C_mul,
    exceptionalExteriorFunctional_C_mul,
    jacobiBetaZeroFunctional_exceptionalEulerInverse_mul_X_pow_eq
      m ε j hγ (Finset.mem_range.mp hj)]
  ring

/-- The exceptional Euler inverse satisfies the signed moment identity from
the gap-free route: its beta-zero Jacobi moments on `(0, 1)` equal a signed
exterior moment on `(1, ∞)`. -/
theorem exceptionalEulerInverse_signedMomentIdentity
    (m ε : ℕ) {γ : ℝ} (p : ℝ[X])
    (hγ : (ε : ℝ) + 1 / 2 + m - 1 < γ)
    (hp : p.natDegree < m) :
    (∫ x : ℝ in 0..1,
        (exceptionalEulerInverse m ε γ * p).eval x *
          x ^ ((ε : ℝ) - 1 / 2)) =
      -(exceptionalEulerInverse m ε γ).eval 1 *
        ∫ x in Ioi (1 : ℝ),
          p.eval x * x ^ ((ε : ℝ) + 1 / 2 - γ - 1) := by
  have hε : 0 ≤ (ε : ℝ) := by positivity
  have hα : -1 < (ε : ℝ) - 1 / 2 := by linarith
  have hpOne : p.natDegree + 1 ≤ m := by lia
  have hpOneCast : (p.natDegree : ℝ) + 1 ≤ m := by
    exact_mod_cast hpOne
  have hExterior :
      (ε : ℝ) + 1 / 2 + p.natDegree < γ := by linarith
  calc
    (∫ x : ℝ in 0..1,
        (exceptionalEulerInverse m ε γ * p).eval x *
          x ^ ((ε : ℝ) - 1 / 2)) =
        jacobiBetaZeroFunctional ((ε : ℝ) - 1 / 2)
          (exceptionalEulerInverse m ε γ * p) :=
      (jacobiBetaZeroFunctional_eq_integral hα _).symm
    _ = -(exceptionalEulerInverse m ε γ).eval 1 *
          exceptionalExteriorFunctional
            ((ε : ℝ) + 1 / 2) γ p :=
      jacobiBetaZeroFunctional_exceptionalEulerInverse_mul_eq
        m ε p hγ hp
    _ = -(exceptionalEulerInverse m ε γ).eval 1 *
          ∫ x in Ioi (1 : ℝ),
            p.eval x * x ^ ((ε : ℝ) + 1 / 2 - γ - 1) := by
      rw [exceptionalExteriorFunctional_eq_integral _ _ p hExterior]

@[simp]
theorem exceptionalEulerInverse_eval_zero (m ε : ℕ) {γ : ℝ}
    (hγ : γ ≠ 0) :
    (exceptionalEulerInverse m ε γ).eval 0 = 1 := by
  rw [← coeff_zero_eq_eval_zero, coeff_exceptionalEulerInverse]
  simp [hγ]

/-- The defining Euler equation `(X D + γ) R_γ = γ F`. -/
theorem eulerShiftOperator_exceptionalEulerInverse
    (m ε : ℕ) {γ : ℝ} (hγ : 0 < γ) :
    eulerShiftOperator γ (exceptionalEulerInverse m ε γ) =
      C γ * exceptionalBasePolynomial m ε := by
  ext k
  rw [coeff_eulerShiftOperator, coeff_C_mul,
    coeff_exceptionalEulerInverse, coeff_exceptionalBasePolynomial]
  split_ifs
  · have hden : γ + (k : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  · ring

private theorem realRisingFactorial_mul_shift
    (a : ℝ) (k : ℕ) :
    a * realRisingFactorial (a + 1) k =
      (a + k) * realRisingFactorial a k := by
  rw [← realRisingFactorial_succ_left,
    realRisingFactorial_succ]
  ring

/-- The lower distinguished Euler parameter gives the last
nonexceptional toric-contribution polynomial. -/
theorem exceptionalEulerInverse_lower_eq_rPolynomial
    (m ε : ℕ) (hm : 0 < m) :
    exceptionalEulerInverse m ε
        ((ε : ℝ) + 1 / 2 + m - 1) =
      rPolynomial m ε (m - 1) := by
  let c : ℝ := ε + 1 / 2
  let A : ℝ := c + m - 1
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  have hA : 0 < A := by
    dsimp only [A]
    have hm_cast : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  ext k
  rw [coeff_exceptionalEulerInverse, coeff_rPolynomial]
  split_ifs with hk
  · have hC : 0 < realRisingFactorial c k :=
      realRisingFactorial_pos k hc
    have hD : 0 < realRisingFactorial (c + m + 1 / 2) k := by
      apply realRisingFactorial_pos
      positivity
    have hF : 0 < (k.factorial : ℝ) := by positivity
    have hAk : A + (k : ℝ) ≠ 0 := by positivity
    have hratio := realRisingFactorial_mul_shift A k
    simp only [exceptionalBaseCoeff, rCoeff]
    change
      (realRisingFactorial (-(m : ℝ)) k *
            realRisingFactorial (c + m) k /
          (realRisingFactorial c k * k.factorial)) * A / (A + k) =
        realRisingFactorial (-(m : ℝ)) k *
            realRisingFactorial ((m : ℝ) + 1 + ε) k *
            realRisingFactorial (c + (m - 1 : ℕ)) k /
          (realRisingFactorial c k *
            realRisingFactorial (c + (m - 1 : ℕ) + 3 / 2) k *
            k.factorial)
    have hm_sub_cast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub (by lia : 1 ≤ m)]
      norm_num
    rw [hm_sub_cast]
    have hfirst : (m : ℝ) + 1 + ε = c + m + 1 / 2 := by
      dsimp only [c]
      ring
    have hsecond : c + ((m : ℝ) - 1) = A := by
      dsimp only [A]
      ring
    have hthird : A + 3 / 2 = c + m + 1 / 2 := by
      dsimp only [A]
      ring
    rw [hfirst, hsecond, hthird]
    have hratio' :
        A * realRisingFactorial (c + m) k =
          (A + k) * realRisingFactorial A k := by
      have hAone : A + 1 = c + m := by
        dsimp only [A]
        ring
      simpa only [hAone] using hratio
    have hquotient :
        realRisingFactorial (c + m) k * A / (A + k) =
          realRisingFactorial A k := by
      rw [div_eq_iff hAk]
      nlinarith
    calc
      (realRisingFactorial (-(m : ℝ)) k *
              realRisingFactorial (c + m) k /
            (realRisingFactorial c k * k.factorial)) * A / (A + k) =
          (realRisingFactorial (-(m : ℝ)) k /
              (realRisingFactorial c k * k.factorial)) *
            (realRisingFactorial (c + m) k * A / (A + k)) := by ring
      _ = realRisingFactorial (-(m : ℝ)) k /
            (realRisingFactorial c k * k.factorial) *
          realRisingFactorial A k := by rw [hquotient]
      _ = realRisingFactorial (-(m : ℝ)) k *
              realRisingFactorial (c + m + 1 / 2) k *
              realRisingFactorial A k /
            (realRisingFactorial c k *
              realRisingFactorial (c + m + 1 / 2) k *
              k.factorial) := by
        have hDnorm : 0 <
            realRisingFactorial (((c + m) * 2 + 1) / 2) k := by
          apply realRisingFactorial_pos
          positivity
        field_simp [hC.ne', hD.ne', hDnorm.ne', hF.ne']
  · rfl

/-- The upper distinguished Euler parameter is exactly the exceptional
toric-contribution polynomial `R_m`. -/
theorem exceptionalEulerInverse_upper_eq_rPolynomial
    (m ε : ℕ) :
    exceptionalEulerInverse m ε
        ((ε : ℝ) + 1 / 2 + m + 1 / 2) =
      rPolynomial m ε m := by
  let c : ℝ := ε + 1 / 2
  let B : ℝ := c + m + 1 / 2
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  have hB : 0 < B := by
    dsimp only [B]
    positivity
  ext k
  rw [coeff_exceptionalEulerInverse, coeff_rPolynomial]
  split_ifs
  · have hC : 0 < realRisingFactorial c k :=
      realRisingFactorial_pos k hc
    have hD : 0 < realRisingFactorial (B + 1) k := by
      apply realRisingFactorial_pos
      positivity
    have hF : 0 < (k.factorial : ℝ) := by positivity
    have hBk : B + (k : ℝ) ≠ 0 := by positivity
    have hratio := realRisingFactorial_mul_shift B k
    simp only [exceptionalBaseCoeff, rCoeff]
    change
      (realRisingFactorial (-(m : ℝ)) k *
            realRisingFactorial (c + m) k /
          (realRisingFactorial c k * k.factorial)) * B / (B + k) =
        realRisingFactorial (-(m : ℝ)) k *
            realRisingFactorial ((m : ℝ) + 1 + ε) k *
            realRisingFactorial (c + m) k /
          (realRisingFactorial c k *
            realRisingFactorial (c + m + 3 / 2) k * k.factorial)
    have hfirst : (m : ℝ) + 1 + ε = B := by
      dsimp only [B, c]
      ring
    have hsecond : c + m + 3 / 2 = B + 1 := by
      dsimp only [B]
      ring
    rw [hfirst, hsecond]
    have hratioDiv :
        realRisingFactorial B k / realRisingFactorial (B + 1) k =
          B / (B + k) := by
      rw [div_eq_div_iff hD.ne' hBk]
      nlinarith
    have hquotient :
        realRisingFactorial B k *
            realRisingFactorial (c + m) k /
              realRisingFactorial (B + 1) k =
          realRisingFactorial (c + m) k * B / (B + k) := by
      calc
        realRisingFactorial B k *
              realRisingFactorial (c + m) k /
                realRisingFactorial (B + 1) k =
            realRisingFactorial (c + m) k *
              (realRisingFactorial B k /
                realRisingFactorial (B + 1) k) := by ring
        _ = realRisingFactorial (c + m) k * (B / (B + k)) := by
          rw [hratioDiv]
        _ = realRisingFactorial (c + m) k * B / (B + k) := by ring
    calc
      (realRisingFactorial (-(m : ℝ)) k *
              realRisingFactorial (c + m) k /
            (realRisingFactorial c k * k.factorial)) * B / (B + k) =
          realRisingFactorial (-(m : ℝ)) k /
              (realRisingFactorial c k * k.factorial) *
            (realRisingFactorial (c + m) k * B / (B + k)) := by ring
      _ = realRisingFactorial (-(m : ℝ)) k /
              (realRisingFactorial c k * k.factorial) *
            (realRisingFactorial B k *
              realRisingFactorial (c + m) k /
                realRisingFactorial (B + 1) k) := by rw [hquotient]
      _ = realRisingFactorial (-(m : ℝ)) k *
              realRisingFactorial B k *
              realRisingFactorial (c + m) k /
            (realRisingFactorial c k *
              realRisingFactorial (B + 1) k * k.factorial) := by ring
  · rfl

end ToricContribution
end ParkingFunctions
end RealRooted
