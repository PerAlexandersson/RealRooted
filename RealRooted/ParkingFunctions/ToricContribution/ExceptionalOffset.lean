import RealRooted.JacobiBetaZeroOrthogonality
import RealRooted.ObreschkoffConverse
import RealRooted.ParkingFunctions.ToricContribution.FiniteOffsets
import RealRooted.DegreeDropReversal
import RealRooted.RootContinuity
import RealRooted.SuccDegreeLeftEndpoint
import Mathlib.Analysis.SpecificLimits.Basic

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

private theorem exceptionalBase_partialFraction_eq_zero
    (m ε j : ℕ) (hj : j < m) :
    ∑ k ∈ Finset.range (m + 1),
        exceptionalBaseCoeff m ε k /
          ((ε : ℝ) + 1 / 2 + k + j) = 0 := by
  have horth := exceptionalBasePolynomial_betaZeroInner_eq_zero
    m ε (X ^ j) (by simp [hj])
  rw [jacobiBetaZeroInner,
    jacobiBetaZeroFunctional_exceptionalBase_mul_X_pow] at horth
  exact horth

/-- Common denominator for the exceptional endpoint sum, regarded as a
polynomial in the Euler parameter. -/
def exceptionalEndpointDenominator (m : ℕ) : ℝ[X] :=
  ∏ k ∈ Finset.range (m + 1), (X + C (k : ℝ))

/-- Numerator obtained after clearing the common denominator in the
exceptional endpoint sum. -/
def exceptionalEndpointNumerator (m ε : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (m + 1),
    C (exceptionalBaseCoeff m ε k) * X *
      ∏ l ∈ (Finset.range (m + 1)).erase k, (X + C (l : ℝ))

@[simp]
theorem exceptionalEndpointDenominator_eval (m : ℕ) (γ : ℝ) :
    (exceptionalEndpointDenominator m).eval γ =
      ∏ k ∈ Finset.range (m + 1), (γ + (k : ℝ)) := by
  rw [exceptionalEndpointDenominator, eval_prod]
  simp

@[simp]
theorem exceptionalEndpointNumerator_eval (m ε : ℕ) (γ : ℝ) :
    (exceptionalEndpointNumerator m ε).eval γ =
      ∑ k ∈ Finset.range (m + 1),
        exceptionalBaseCoeff m ε k * γ *
          ∏ l ∈ (Finset.range (m + 1)).erase k,
            (γ + (l : ℝ)) := by
  rw [exceptionalEndpointNumerator, eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [eval_mul, eval_C, eval_X, eval_prod, eval_add]

theorem exceptionalEulerInverse_eval_one_mul_endpointDenominator
    (m ε : ℕ) {γ : ℝ}
    (hγ : ∀ k ∈ Finset.range (m + 1), γ + k ≠ 0) :
    (exceptionalEulerInverse m ε γ).eval 1 *
        (exceptionalEndpointDenominator m).eval γ =
      (exceptionalEndpointNumerator m ε).eval γ := by
  rw [exceptionalEulerInverse_eval_one_eq_sum,
    exceptionalEndpointDenominator_eval,
    exceptionalEndpointNumerator_eval, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Finset.prod_erase_mul _ _ hk]
  have hγk := hγ k hk
  field_simp

theorem exceptionalEndpointNumerator_eval_parameterRoot
    (m ε j : ℕ) (hj : j < m) :
    (exceptionalEndpointNumerator m ε).eval
        ((ε : ℝ) + 1 / 2 + j) = 0 := by
  let γ : ℝ := ε + 1 / 2 + j
  have hγpos : 0 < γ := by
    dsimp only [γ]
    positivity
  have hden : ∀ k ∈ Finset.range (m + 1), γ + k ≠ 0 := by
    intro k hk
    positivity
  rw [← exceptionalEulerInverse_eval_one_mul_endpointDenominator
    m ε hden]
  have hsum := exceptionalBase_partialFraction_eq_zero m ε j hj
  have hendpoint : (exceptionalEulerInverse m ε γ).eval 1 = 0 := by
    rw [exceptionalEulerInverse_eval_one_eq_sum]
    rw [show (∑ k ∈ Finset.range (m + 1),
        exceptionalBaseCoeff m ε k * (γ / (γ + k))) =
      γ * ∑ k ∈ Finset.range (m + 1),
        exceptionalBaseCoeff m ε k / (γ + k) by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          ring]
    have hsum' : ∑ k ∈ Finset.range (m + 1),
        exceptionalBaseCoeff m ε k / (γ + k) = 0 := by
      simpa only [γ, add_assoc, add_left_comm, add_comm] using hsum
    rw [hsum', mul_zero]
  rw [hendpoint, zero_mul]

private theorem prod_range_erase_natCast_sub
    (m r : ℕ) (hr : r ≤ m) :
    ∏ l ∈ (Finset.range (m + 1)).erase r,
        ((l : ℝ) - r) =
      (-1 : ℝ) ^ r * r.factorial * (m - r).factorial := by
  have herase :
      (Finset.range (m + 1)).erase r =
        Finset.range r ∪ Finset.Ioc r m := by
    ext l
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union,
      Finset.mem_Ioc]
    constructor
    · intro hl
      by_cases hlr : l < r
      · exact Or.inl hlr
      · exact Or.inr ⟨by lia, by lia⟩
    · intro hl
      constructor
      · rcases hl with hl | hl <;> lia
      · rcases hl with hl | hl <;> lia
  have hdisjoint : Disjoint (Finset.range r) (Finset.Ioc r m) := by
    rw [Finset.disjoint_left]
    intro l hlrange hlIoc
    simp only [Finset.mem_range] at hlrange
    simp only [Finset.mem_Ioc] at hlIoc
    lia
  have hlower :
      ∏ l ∈ Finset.range r, ((l : ℝ) - r) =
        (-1 : ℝ) ^ r * r.factorial := by
    simp_rw [show ∀ l : ℕ, (l : ℝ) - r = -((r : ℝ) - l) by
      intro l
      ring]
    rw [Finset.prod_neg, Finset.card_range,
      Finset.prod_range_natCast_sub]
    norm_cast
    rw [← Nat.descFactorial_eq_prod_range,
      Nat.descFactorial_self]
  have hupper :
      ∏ l ∈ Finset.Ioc r m, ((l : ℝ) - r) =
        (m - r).factorial := by
    have hIoc : Finset.Ioc r m = Finset.Ico (r + 1) (m + 1) := by
      ext l
      simp
    rw [hIoc, Finset.prod_Ico_eq_prod_range]
    have hsub : m + 1 - (r + 1) = m - r := by lia
    rw [hsub]
    have hfactorial :
        (∏ l ∈ Finset.range (m - r), ((l + 1 : ℕ) : ℝ)) =
          ((m - r).factorial : ℝ) := by
      exact_mod_cast Finset.prod_range_add_one_eq_factorial (m - r)
    rw [← hfactorial]
    apply Finset.prod_congr rfl
    intro l hl
    push_cast
    ring
  rw [herase, Finset.prod_union hdisjoint, hlower, hupper]

private theorem realRisingFactorial_neg_nat_eq_descFactorial
    (m r : ℕ) (hr : r ≤ m) :
    realRisingFactorial (-(m : ℝ)) r =
      (-1 : ℝ) ^ r * m.descFactorial r := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hrle : r ≤ m := by lia
      rw [realRisingFactorial_succ, ih hrle,
        Nat.descFactorial_succ, pow_succ]
      have hcast : ((m - r : ℕ) : ℝ) = (m : ℝ) - r := by
        rw [Nat.cast_sub hrle]
      push_cast
      rw [hcast]
      ring

private theorem realRisingFactorial_neg_nat_eq_factorial_div
    (m r : ℕ) (hr : r ≤ m) :
    realRisingFactorial (-(m : ℝ)) r =
      (-1 : ℝ) ^ r * m.factorial / (m - r).factorial := by
  rw [realRisingFactorial_neg_nat_eq_descFactorial m r hr]
  have hfactorial := Nat.factorial_mul_descFactorial hr
  have hden : (0 : ℝ) < (m - r).factorial := by positivity
  have hfactorialCast :
      ((m - r).factorial : ℝ) * m.descFactorial r = m.factorial := by
    exact_mod_cast hfactorial
  have hdesc :
      (m.descFactorial r : ℝ) =
        m.factorial / (m - r).factorial := by
    rw [eq_div_iff hden.ne']
    nlinarith
  rw [hdesc]
  ring

private theorem prod_range_add_eq_realRisingFactorial
    (a : ℝ) (m : ℕ) :
    ∏ j ∈ Finset.range m, (a + j) = realRisingFactorial a m := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.prod_range_succ, realRisingFactorial_succ, ih]

private theorem prod_range_neg_add_eq_realRisingFactorial
    (a : ℝ) (m : ℕ) :
    ∏ j ∈ Finset.range m, (-(a + j)) =
      (-1 : ℝ) ^ m * realRisingFactorial a m := by
  rw [Finset.prod_neg, Finset.card_range,
    prod_range_add_eq_realRisingFactorial]

private theorem neg_one_pow_sq_real (k : ℕ) :
    ((-1 : ℝ) ^ k) ^ 2 = 1 := by
  rw [← pow_mul]
  norm_num

/-- Closed product form of the numerator predicted by the terminating
Saalschütz evaluation. -/
def exceptionalEndpointClosedNumerator (m ε : ℕ) : ℝ[X] :=
  C (realRisingFactorial (-(m : ℝ)) m /
      realRisingFactorial ((ε : ℝ) + 1 / 2) m) *
    X * ∏ j ∈ Finset.range m,
      (X - C ((ε : ℝ) + 1 / 2 + j))

@[simp]
theorem exceptionalEndpointClosedNumerator_eval
    (m ε : ℕ) (γ : ℝ) :
    (exceptionalEndpointClosedNumerator m ε).eval γ =
      (realRisingFactorial (-(m : ℝ)) m /
          realRisingFactorial ((ε : ℝ) + 1 / 2) m) *
        γ * ∏ j ∈ Finset.range m,
          (γ - ((ε : ℝ) + 1 / 2 + j)) := by
  rw [exceptionalEndpointClosedNumerator, eval_mul, eval_mul,
    eval_C, eval_X, eval_prod]
  simp

private theorem natDegree_exceptionalEndpointNumerator_le
    (m ε : ℕ) :
    (exceptionalEndpointNumerator m ε).natDegree ≤ m + 1 := by
  rw [exceptionalEndpointNumerator]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  calc
    (C (exceptionalBaseCoeff m ε k) * X *
          ∏ l ∈ (Finset.range (m + 1)).erase k,
            (X + C (l : ℝ))).natDegree ≤
        (C (exceptionalBaseCoeff m ε k) * X).natDegree +
          (∏ l ∈ (Finset.range (m + 1)).erase k,
            (X + C (l : ℝ))).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 1 + m := by
      apply Nat.add_le_add
      · exact Polynomial.natDegree_mul_le.trans (by simp)
      · rw [Polynomial.natDegree_prod_of_monic]
        · calc
            ∑ l ∈ (Finset.range (m + 1)).erase k,
                (X + C (l : ℝ)).natDegree =
                ∑ l ∈ (Finset.range (m + 1)).erase k, 1 := by
              apply Finset.sum_congr rfl
              intro l hl
              rw [Polynomial.natDegree_X_add_C]
            _ = ((Finset.range (m + 1)).erase k).card := by simp
            _ ≤ m := by simp [hk]
        · intro l hl
          exact Polynomial.monic_X_add_C _
    _ = m + 1 := by lia

private theorem natDegree_exceptionalEndpointClosedNumerator_le
    (m ε : ℕ) :
    (exceptionalEndpointClosedNumerator m ε).natDegree ≤ m + 1 := by
  rw [exceptionalEndpointClosedNumerator]
  calc
    (C (realRisingFactorial (-(m : ℝ)) m /
          realRisingFactorial ((ε : ℝ) + 1 / 2) m) * X *
        ∏ j ∈ Finset.range m,
          (X - C ((ε : ℝ) + 1 / 2 + j))).natDegree ≤
        (C (realRisingFactorial (-(m : ℝ)) m /
          realRisingFactorial ((ε : ℝ) + 1 / 2) m) * X).natDegree +
        (∏ j ∈ Finset.range m,
          (X - C ((ε : ℝ) + 1 / 2 + j))).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 1 + m := by
      apply Nat.add_le_add
      · exact Polynomial.natDegree_mul_le.trans (by simp)
      · rw [Polynomial.natDegree_prod_of_monic]
        · calc
            ∑ j ∈ Finset.range m,
                (X - C ((ε : ℝ) + 1 / 2 + j)).natDegree =
                ∑ j ∈ Finset.range m, 1 := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [Polynomial.natDegree_X_sub_C]
            _ ≤ m := by simp
        · intro j hj
          exact Polynomial.monic_X_sub_C _
    _ = m + 1 := by lia

private theorem exceptionalEndpointNumerator_eval_neg_nat
    (m ε r : ℕ) (hr : r ≤ m) :
    (exceptionalEndpointNumerator m ε).eval (-(r : ℝ)) =
      (exceptionalEndpointClosedNumerator m ε).eval (-(r : ℝ)) := by
  let c : ℝ := ε + 1 / 2
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  have hnum :
      (exceptionalEndpointNumerator m ε).eval (-(r : ℝ)) =
        exceptionalBaseCoeff m ε r * (-(r : ℝ)) *
          ((-1 : ℝ) ^ r * r.factorial * (m - r).factorial) := by
    rw [exceptionalEndpointNumerator_eval, Finset.sum_eq_single r]
    · rw [show ∏ l ∈ (Finset.range (m + 1)).erase r,
          (-(r : ℝ) + l) =
        ∏ l ∈ (Finset.range (m + 1)).erase r,
          ((l : ℝ) - r) by
            apply Finset.prod_congr rfl
            intro l hl
            ring,
        prod_range_erase_natCast_sub m r hr]
    · intro k hk hkr
      have hrmem : r ∈ (Finset.range (m + 1)).erase k := by
        simp [hr, hkr.symm]
      have hprod :
          ∏ l ∈ (Finset.range (m + 1)).erase k,
              (-(r : ℝ) + l) = 0 := by
        apply Finset.prod_eq_zero hrmem
        ring
      rw [hprod, mul_zero]
    · intro hrnot
      exact False.elim (hrnot (by simp [hr]))
  have hclosed :
      (exceptionalEndpointClosedNumerator m ε).eval (-(r : ℝ)) =
        (realRisingFactorial (-(m : ℝ)) m /
            realRisingFactorial c m) *
          (-(r : ℝ)) *
            ((-1 : ℝ) ^ m * realRisingFactorial (c + r) m) := by
    rw [exceptionalEndpointClosedNumerator_eval]
    rw [show ∏ j ∈ Finset.range m,
          (-(r : ℝ) - ((ε : ℝ) + 1 / 2 + j)) =
        ∏ j ∈ Finset.range m, (-((c + r) + j)) by
          apply Finset.prod_congr rfl
          intro j hj
          dsimp only [c]
          ring]
    change
      (realRisingFactorial (-(m : ℝ)) m /
            realRisingFactorial c m) *
          (-(r : ℝ)) *
            (∏ j ∈ Finset.range m, (-((c + r) + j))) = _
    rw [prod_range_neg_add_eq_realRisingFactorial]
  rw [hnum, hclosed, exceptionalBaseCoeff]
  rw [realRisingFactorial_neg_nat_eq_factorial_div m r hr,
    realRisingFactorial_neg_nat_eq_factorial_div m m le_rfl]
  have hcr : 0 < realRisingFactorial c r :=
    realRisingFactorial_pos r hc
  have hcm : 0 < realRisingFactorial c m :=
    realRisingFactorial_pos m hc
  have hfactorialR : (0 : ℝ) < r.factorial := by positivity
  have hfactorialSub : (0 : ℝ) < (m - r).factorial := by positivity
  have hshift := realRisingFactorial_shift_mul c m r
  have hratio :
      realRisingFactorial (c + m) r / realRisingFactorial c r =
        realRisingFactorial (c + r) m / realRisingFactorial c m := by
    field_simp [hcr.ne', hcm.ne']
    nlinarith [hshift]
  dsimp only [c] at hshift hratio ⊢
  simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, div_one]
  field_simp [hcr.ne', hcm.ne', hfactorialR.ne', hfactorialSub.ne']
  ring_nf at hshift hratio ⊢
  have hsignR : (-1 : ℝ) ^ (r * 2) = 1 := by
    rw [pow_mul, neg_one_pow_sq_real]
  have hsignM : (-1 : ℝ) ^ (m * 2) = 1 := by
    rw [pow_mul, neg_one_pow_sq_real]
  rw [hsignR, hsignM, mul_one] at ⊢
  nlinarith [hratio]

private theorem exceptionalEndpointNumerator_eval_baseParameter
    (m ε : ℕ) :
    (exceptionalEndpointNumerator m ε).eval
        ((ε : ℝ) + 1 / 2) =
      (exceptionalEndpointClosedNumerator m ε).eval
        ((ε : ℝ) + 1 / 2) := by
  cases m with
  | zero =>
      simp [exceptionalEndpointNumerator,
        exceptionalEndpointClosedNumerator, exceptionalBaseCoeff]
  | succ m =>
      have hnum := exceptionalEndpointNumerator_eval_parameterRoot
        (m + 1) ε 0 (by lia)
      have hnum' :
          (exceptionalEndpointNumerator (m + 1) ε).eval
              ((ε : ℝ) + 1 / 2) = 0 := by
        simpa only [Nat.cast_zero, add_zero] using hnum
      have hzero :
          ∏ j ∈ Finset.range (m + 1),
              ((ε : ℝ) + 1 / 2 - ((ε : ℝ) + 1 / 2 + j)) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_range.mpr (by lia : 0 < m + 1))
        ring
      rw [hnum', exceptionalEndpointClosedNumerator_eval, hzero]
      ring

/-- The cleared endpoint numerator is the product predicted by the terminating
Saalschütz evaluation. The proof uses finite polynomial interpolation. -/
theorem exceptionalEndpointNumerator_eq_closed (m ε : ℕ) :
    exceptionalEndpointNumerator m ε =
      exceptionalEndpointClosedNumerator m ε := by
  let c : ℝ := ε + 1 / 2
  let f : Fin (m + 2) → ℝ := fun i =>
    if i.val ≤ m then -(i.val : ℝ) else c
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  have hf : Function.Injective f := by
    intro i j hij
    by_cases hi : i.val ≤ m
    · by_cases hj : j.val ≤ m
      · simp only [f, hi, hj, ↓reduceIte] at hij
        apply Fin.ext
        exact_mod_cast neg_inj.mp hij
      · have hnonpos : -(i.val : ℝ) ≤ 0 :=
          neg_nonpos.mpr (Nat.cast_nonneg _)
        simp only [f, hi, hj, ↓reduceIte] at hij
        linarith
    · by_cases hj : j.val ≤ m
      · have hnonpos : -(j.val : ℝ) ≤ 0 :=
          neg_nonpos.mpr (Nat.cast_nonneg _)
        simp only [f, hi, hj, ↓reduceIte] at hij
        linarith
      · apply Fin.ext
        have hiBound := i.isLt
        have hjBound := j.isLt
        lia
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq
    (exceptionalEndpointNumerator m ε)
    (exceptionalEndpointClosedNumerator m ε) hf
  · intro i
    by_cases hi : i.val ≤ m
    · simpa only [f, hi, ↓reduceIte] using
        exceptionalEndpointNumerator_eval_neg_nat m ε i.val hi
    · simpa only [f, hi, ↓reduceIte, c] using
        exceptionalEndpointNumerator_eval_baseParameter m ε
  · simp only [Fintype.card_fin]
    have hnum := natDegree_exceptionalEndpointNumerator_le m ε
    have hclosed := natDegree_exceptionalEndpointClosedNumerator_le m ε
    have hmax : max
        (exceptionalEndpointNumerator m ε).natDegree
        (exceptionalEndpointClosedNumerator m ε).natDegree ≤ m + 1 :=
      max_le hnum hclosed
    lia

/-- Product evaluation of the exceptional Euler inverse at the right
endpoint. -/
theorem exceptionalEulerInverse_eval_one_eq_endpointProduct
    (m ε : ℕ) {γ : ℝ} (hm : 0 < m)
    (hγ : (ε : ℝ) + 1 / 2 + m - 1 < γ) :
    (exceptionalEulerInverse m ε γ).eval 1 =
      (realRisingFactorial (-(m : ℝ)) m /
          realRisingFactorial ((ε : ℝ) + 1 / 2) m) *
        (∏ j ∈ Finset.range m,
          (γ - ((ε : ℝ) + 1 / 2 + j))) /
        realRisingFactorial (γ + 1) m := by
  let c : ℝ := ε + 1 / 2
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  have hmCast : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hγpos : 0 < γ := by
    dsimp only [c] at hc
    linarith
  have hden : ∀ k ∈ Finset.range (m + 1), γ + k ≠ 0 := by
    intro k hk
    positivity
  have hmul := exceptionalEulerInverse_eval_one_mul_endpointDenominator
    m ε hden
  rw [exceptionalEndpointDenominator_eval,
    exceptionalEndpointNumerator_eq_closed,
    exceptionalEndpointClosedNumerator_eval] at hmul
  have hdenProduct :
      ∏ k ∈ Finset.range (m + 1), (γ + (k : ℝ)) =
        γ * realRisingFactorial (γ + 1) m := by
    rw [prod_range_add_eq_realRisingFactorial,
      realRisingFactorial_succ_left]
  have hrf : 0 < realRisingFactorial (γ + 1) m :=
    realRisingFactorial_pos m (by linarith)
  rw [hdenProduct] at hmul
  apply (eq_div_iff hrf.ne').2
  apply (mul_left_cancel₀ hγpos.ne')
  nlinarith [hmul]

/-- The exceptional endpoint has the parity sign prescribed by the signed
moment route. -/
theorem negOnePow_mul_exceptionalEulerInverse_eval_one_pos
    (m ε : ℕ) {γ : ℝ} (hm : 0 < m)
    (hγ : (ε : ℝ) + 1 / 2 + m - 1 < γ) :
    0 < (-1 : ℝ) ^ m *
      (exceptionalEulerInverse m ε γ).eval 1 := by
  rw [exceptionalEulerInverse_eval_one_eq_endpointProduct m ε hm hγ]
  rw [realRisingFactorial_neg_nat_eq_factorial_div m m le_rfl]
  simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, div_one]
  have hc : 0 < (ε : ℝ) + 1 / 2 := by positivity
  have hmCast : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hγpos : 0 < γ := by linarith
  have hbase :
      0 < realRisingFactorial ((ε : ℝ) + 1 / 2) m :=
    realRisingFactorial_pos m hc
  have hden : 0 < realRisingFactorial (γ + 1) m :=
    realRisingFactorial_pos m (by linarith)
  have hprod :
      0 < ∏ j ∈ Finset.range m,
        (γ - ((ε : ℝ) + 1 / 2 + j)) := by
    apply Finset.prod_pos
    intro j hj
    have hjlt : j < m := Finset.mem_range.mp hj
    have hjCast : (j : ℝ) ≤ m - 1 := by
      have hjSucc : j + 1 ≤ m := by lia
      have hjSuccCast : (j : ℝ) + 1 ≤ m := by
        exact_mod_cast hjSucc
      linarith
    linarith
  have hsignSq : ((-1 : ℝ) ^ m) ^ 2 = 1 :=
    neg_one_pow_sq_real m
  have hrearrange :
      (-1 : ℝ) ^ m *
          (((-1 : ℝ) ^ m * (m.factorial : ℝ) /
              realRisingFactorial ((ε : ℝ) + 1 / 2) m) *
            (∏ j ∈ Finset.range m,
              (γ - ((ε : ℝ) + 1 / 2 + j))) /
            realRisingFactorial (γ + 1) m) =
        (m.factorial : ℝ) *
            (∏ j ∈ Finset.range m,
              (γ - ((ε : ℝ) + 1 / 2 + j))) /
          (realRisingFactorial ((ε : ℝ) + 1 / 2) m *
            realRisingFactorial (γ + 1) m) := by
    field_simp [hbase.ne', hden.ne']
    rw [hsignSq]
    ring
  rw [hrearrange]
  positivity

theorem exceptionalBaseCoeff_ne_zero_of_le
    (m ε k : ℕ) (hk : k ≤ m) :
    exceptionalBaseCoeff m ε k ≠ 0 := by
  rw [exceptionalBaseCoeff,
    realRisingFactorial_neg_nat_eq_factorial_div m k hk]
  have hc : 0 < (ε : ℝ) + 1 / 2 := by positivity
  have hcm : 0 < (ε : ℝ) + 1 / 2 + m := by positivity
  have hnum :
      realRisingFactorial ((ε : ℝ) + 1 / 2 + m) k ≠ 0 :=
    ne_of_gt (realRisingFactorial_pos k hcm)
  have hden : realRisingFactorial ((ε : ℝ) + 1 / 2) k ≠ 0 :=
    ne_of_gt (realRisingFactorial_pos k hc)
  positivity

theorem natDegree_exceptionalEulerInverse_le
    (m ε : ℕ) (γ : ℝ) :
    (exceptionalEulerInverse m ε γ).natDegree ≤ m := by
  rw [exceptionalEulerInverse]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  exact (Polynomial.natDegree_monomial_le _).trans
    (Finset.mem_range_succ_iff.mp hk)

theorem natDegree_exceptionalEulerInverse
    (m ε : ℕ) {γ : ℝ} (hγ : 0 < γ) :
    (exceptionalEulerInverse m ε γ).natDegree = m := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_exceptionalEulerInverse_le m ε γ)
  rw [coeff_exceptionalEulerInverse, if_pos le_rfl]
  exact div_ne_zero
    (mul_ne_zero (exceptionalBaseCoeff_ne_zero_of_le m ε m le_rfl)
      hγ.ne')
    (by positivity)

/-- Ratio of the two highest coefficients in the exceptional family. -/
theorem exceptionalEulerInverse_topCoeff_ratio
    (m ε : ℕ) {γ : ℝ} (hm : 0 < m) (hγ : 0 < γ) :
    (exceptionalEulerInverse m ε γ).coeff m /
        (exceptionalEulerInverse m ε γ).coeff (m - 1) =
      (exceptionalBaseCoeff m ε m /
          exceptionalBaseCoeff m ε (m - 1)) *
        (γ + (m : ℝ) - 1) / (γ + m) := by
  rw [coeff_exceptionalEulerInverse, if_pos le_rfl,
    coeff_exceptionalEulerInverse, if_pos (by lia)]
  have hbasePrev := exceptionalBaseCoeff_ne_zero_of_le
    m ε (m - 1) (by lia)
  have hγm : γ + (m : ℝ) ≠ 0 := by positivity
  have hγprev : γ + (m : ℝ) - 1 ≠ 0 := by
    have hmCast : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  rw [Nat.cast_sub (by lia : 1 ≤ m)]
  field_simp
  ring

private theorem exceptionalParameterTopRatio_strictMono
    (m : ℕ) {γ₁ γ₂ : ℝ} (hm : 0 < m)
    (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) (hγ : γ₁ < γ₂) :
    (γ₁ + (m : ℝ) - 1) / (γ₁ + m) <
      (γ₂ + (m : ℝ) - 1) / (γ₂ + m) := by
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
  nlinarith

/-- At distinct positive parameters, the top two coefficient vectors are
linearly independent. -/
theorem exceptionalEulerInverse_topCoeff_det_ne_zero
    (m ε : ℕ) {γ₁ γ₂ : ℝ} (hm : 0 < m)
    (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) (hγ : γ₁ ≠ γ₂) :
    (exceptionalEulerInverse m ε γ₁).coeff m *
          (exceptionalEulerInverse m ε γ₂).coeff (m - 1) ≠
      (exceptionalEulerInverse m ε γ₂).coeff m *
          (exceptionalEulerInverse m ε γ₁).coeff (m - 1) := by
  let R₁ := exceptionalEulerInverse m ε γ₁
  let R₂ := exceptionalEulerInverse m ε γ₂
  have hb₁ : R₁.coeff (m - 1) ≠ 0 := by
    dsimp only [R₁]
    rw [coeff_exceptionalEulerInverse, if_pos (by lia)]
    exact div_ne_zero
      (mul_ne_zero
        (exceptionalBaseCoeff_ne_zero_of_le m ε (m - 1) (by lia))
        hγ₁.ne')
      (by positivity)
  have hb₂ : R₂.coeff (m - 1) ≠ 0 := by
    dsimp only [R₂]
    rw [coeff_exceptionalEulerInverse, if_pos (by lia)]
    exact div_ne_zero
      (mul_ne_zero
        (exceptionalBaseCoeff_ne_zero_of_le m ε (m - 1) (by lia))
        hγ₂.ne')
      (by positivity)
  intro hdet
  have hratio : R₁.coeff m / R₁.coeff (m - 1) =
      R₂.coeff m / R₂.coeff (m - 1) :=
    (div_eq_div_iff hb₁ hb₂).2 hdet
  rw [show R₁ = exceptionalEulerInverse m ε γ₁ by rfl,
    exceptionalEulerInverse_topCoeff_ratio m ε hm hγ₁,
    show R₂ = exceptionalEulerInverse m ε γ₂ by rfl,
    exceptionalEulerInverse_topCoeff_ratio m ε hm hγ₂] at hratio
  have hbase :
      exceptionalBaseCoeff m ε m /
          exceptionalBaseCoeff m ε (m - 1) ≠ 0 :=
    div_ne_zero
      (exceptionalBaseCoeff_ne_zero_of_le m ε m le_rfl)
      (exceptionalBaseCoeff_ne_zero_of_le m ε (m - 1) (by lia))
  have hparameter :
      (γ₁ + (m : ℝ) - 1) / (γ₁ + m) =
        (γ₂ + (m : ℝ) - 1) / (γ₂ + m) :=
    mul_left_cancel₀ hbase (by
      simpa only [mul_div_assoc] using hratio)
  rcases lt_or_gt_of_ne hγ with hγlt | hγgt
  · exact (ne_of_lt
      (exceptionalParameterTopRatio_strictMono m hm hγ₁ hγ₂ hγlt))
      hparameter
  · exact (ne_of_gt
      (exceptionalParameterTopRatio_strictMono m hm hγ₂ hγ₁ hγgt))
      hparameter

/-- A nonzero pencil member at distinct positive parameters cannot drop below
degree `m - 1`. -/
theorem exceptionalEulerInverse_pencil_natDegree_ge_sub_one
    (m ε : ℕ) {γ₁ γ₂ a b : ℝ} (hm : 0 < m)
    (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂) (hγ : γ₁ ≠ γ₂)
    (hne : C a * exceptionalEulerInverse m ε γ₁ +
        C b * exceptionalEulerInverse m ε γ₂ ≠ 0) :
    m - 1 ≤ (C a * exceptionalEulerInverse m ε γ₁ +
      C b * exceptionalEulerInverse m ε γ₂).natDegree := by
  let R₁ := exceptionalEulerInverse m ε γ₁
  let R₂ := exceptionalEulerInverse m ε γ₂
  let Q := C a * R₁ + C b * R₂
  have hdet : R₁.coeff m * R₂.coeff (m - 1) ≠
      R₂.coeff m * R₁.coeff (m - 1) :=
    exceptionalEulerInverse_topCoeff_det_ne_zero
      m ε hm hγ₁ hγ₂ hγ
  by_cases htop : Q.coeff m = 0
  · have hprev : Q.coeff (m - 1) ≠ 0 := by
      intro hprev
      have htop' : a * R₁.coeff m + b * R₂.coeff m = 0 := by
        simpa only [Q, coeff_add, coeff_C_mul] using htop
      have hprev' :
          a * R₁.coeff (m - 1) + b * R₂.coeff (m - 1) = 0 := by
        simpa only [Q, coeff_add, coeff_C_mul] using hprev
      have haDet :
          a * (R₁.coeff m * R₂.coeff (m - 1) -
            R₂.coeff m * R₁.coeff (m - 1)) = 0 := by
        linear_combination R₂.coeff (m - 1) * htop' -
          R₂.coeff m * hprev'
      have hdetSub : R₁.coeff m * R₂.coeff (m - 1) -
          R₂.coeff m * R₁.coeff (m - 1) ≠ 0 :=
        sub_ne_zero.mpr hdet
      have ha : a = 0 := (mul_eq_zero.mp haDet).resolve_right hdetSub
      have hb₂ : R₂.coeff (m - 1) ≠ 0 := by
        dsimp only [R₂]
        rw [coeff_exceptionalEulerInverse, if_pos (by lia)]
        exact div_ne_zero
          (mul_ne_zero
            (exceptionalBaseCoeff_ne_zero_of_le m ε (m - 1) (by lia))
            hγ₂.ne')
          (by positivity)
      have hb : b = 0 := by
        rw [ha, zero_mul, zero_add] at hprev'
        exact (mul_eq_zero.mp hprev').resolve_right hb₂
      apply hne
      rw [ha, hb]
      simp
    simpa only [Q, R₁, R₂] using
      Polynomial.le_natDegree_of_ne_zero hprev
  · have hdegree := (Nat.sub_le m 1).trans
      (Polynomial.le_natDegree_of_ne_zero htop)
    simpa only [Q, R₁, R₂] using hdegree

theorem exceptionalBaseCoeff_one
    (m ε : ℕ) :
    exceptionalBaseCoeff m ε 1 =
      -(m : ℝ) * ((ε : ℝ) + 1 / 2 + m) /
        ((ε : ℝ) + 1 / 2) := by
  rw [exceptionalBaseCoeff]
  simp only [realRisingFactorial_succ, realRisingFactorial_zero,
    mul_one, Nat.factorial_one, Nat.cast_one]
  have hc : (ε : ℝ) + 1 / 2 ≠ 0 := by positivity
  field_simp
  ring

/-- The negative linear coefficient is the reciprocal-root sum from the
orientation step. -/
theorem neg_coeff_one_exceptionalEulerInverse
    (m ε : ℕ) {γ : ℝ} (hm : 0 < m) :
    -(exceptionalEulerInverse m ε γ).coeff 1 =
      ((m : ℝ) * ((ε : ℝ) + 1 / 2 + m) /
          ((ε : ℝ) + 1 / 2)) *
        (γ / (γ + 1)) := by
  rw [coeff_exceptionalEulerInverse, if_pos (by lia : 1 ≤ m),
    exceptionalBaseCoeff_one]
  ring

theorem neg_coeff_one_exceptionalEulerInverse_strictMono
    (m ε : ℕ) {γ₁ γ₂ : ℝ} (hm : 0 < m)
    (hγ₁ : 0 < γ₁) (hγ : γ₁ < γ₂) :
    -(exceptionalEulerInverse m ε γ₁).coeff 1 <
      -(exceptionalEulerInverse m ε γ₂).coeff 1 := by
  rw [neg_coeff_one_exceptionalEulerInverse m ε hm,
    neg_coeff_one_exceptionalEulerInverse m ε hm]
  have hγ₂ : 0 < γ₂ := lt_trans hγ₁ hγ
  have hratio : γ₁ / (γ₁ + 1) < γ₂ / (γ₂ + 1) := by
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
    nlinarith
  have hfactor :
      0 < (m : ℝ) * ((ε : ℝ) + 1 / 2 + m) /
        ((ε : ℝ) + 1 / 2) := by positivity
  exact mul_lt_mul_of_pos_left hratio hfactor

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

/-- Exterior density associated with a signed pencil member. -/
def exceptionalPencilExteriorDensity
    (m ε : ℕ) (γ₁ γ₂ a b x : ℝ) : ℝ :=
  a * (exceptionalEulerInverse m ε γ₁).eval 1 *
      x ^ ((ε : ℝ) + 1 / 2 - γ₁ - 1) +
    b * (exceptionalEulerInverse m ε γ₂).eval 1 *
      x ^ ((ε : ℝ) + 1 / 2 - γ₂ - 1)

@[simp]
theorem exceptionalPencilExteriorDensity_one
    (m ε : ℕ) (γ₁ γ₂ a b : ℝ) :
    exceptionalPencilExteriorDensity m ε γ₁ γ₂ a b 1 =
      (C a * exceptionalEulerInverse m ε γ₁ +
        C b * exceptionalEulerInverse m ε γ₂).eval 1 := by
  simp [exceptionalPencilExteriorDensity]

private theorem continuousAt_exceptionalPencilExteriorDensity
    (m ε : ℕ) (γ₁ γ₂ a b : ℝ) {x : ℝ} (hx : x ≠ 0) :
    ContinuousAt
      (exceptionalPencilExteriorDensity m ε γ₁ γ₂ a b) x := by
  unfold exceptionalPencilExteriorDensity
  exact
    ((continuousAt_const.mul continuousAt_const).mul
      (continuousAt_id.rpow_const (Or.inl hx))).add
    ((continuousAt_const.mul continuousAt_const).mul
      (continuousAt_id.rpow_const (Or.inl hx)))

private theorem mul_pos_of_continuousOn_of_ne_zero
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hno : ∀ x, a ≤ x → x ≤ b → f x ≠ 0) :
    0 < f a * f b := by
  have ha : f a ≠ 0 := hno a le_rfl hab
  have hb : f b ≠ 0 := hno b hab le_rfl
  rcases lt_or_gt_of_ne ha with haNeg | haPos
  · have hbNeg : f b < 0 := by
      rcases lt_or_gt_of_ne hb with hbNeg | hbPos
      · exact hbNeg
      · have hzero : (0 : ℝ) ∈ Set.Icc (f a) (f b) :=
          ⟨haNeg.le, hbPos.le⟩
        obtain ⟨x, hx, hfx⟩ :=
          intermediate_value_Icc hab hf hzero
        exact ((hno x hx.1 hx.2) hfx).elim
    exact mul_pos_of_neg_of_neg haNeg hbNeg
  · have hbPos : 0 < f b := by
      rcases lt_or_gt_of_ne hb with hbNeg | hbPos
      · have hzero : (0 : ℝ) ∈ Set.Icc (f b) (f a) :=
          ⟨hbNeg.le, haPos.le⟩
        obtain ⟨x, hx, hfx⟩ :=
          intermediate_value_Icc' hab hf hzero
        exact ((hno x hx.1 hx.2) hfx).elim
      · exact hbPos
    exact mul_pos haPos hbPos

/-- A nonzero two-power exterior density has at most one zero on `(1, ∞)`.
This is the analytic core of P6. -/
theorem exceptionalPencilExteriorDensity_ne_zero_of_lt
    (m ε : ℕ) {γ₁ γ₂ a b x y : ℝ}
    (hγ : γ₁ < γ₂) (hx : 1 < x) (hxy : x < y)
    (hcoeff :
      a * (exceptionalEulerInverse m ε γ₁).eval 1 ≠ 0 ∨
        b * (exceptionalEulerInverse m ε γ₂).eval 1 ≠ 0)
    (hxzero : exceptionalPencilExteriorDensity
      m ε γ₁ γ₂ a b x = 0) :
    exceptionalPencilExteriorDensity m ε γ₁ γ₂ a b y ≠ 0 := by
  let A := a * (exceptionalEulerInverse m ε γ₁).eval 1
  let B := b * (exceptionalEulerInverse m ε γ₂).eval 1
  let e := (ε : ℝ) + 1 / 2 - γ₂ - 1
  let d := γ₂ - γ₁
  have hxpos : 0 < x := lt_trans one_pos hx
  have hypos : 0 < y := lt_trans hxpos hxy
  have hd : 0 < d := by
    dsimp only [d]
    linarith
  have hxFactor :
      exceptionalPencilExteriorDensity m ε γ₁ γ₂ a b x =
        x ^ e * (A * x ^ d + B) := by
    rw [exceptionalPencilExteriorDensity]
    dsimp only [A, B, e, d]
    have hxpow :
        x ^ ((ε : ℝ) + 1 / 2 - γ₁ - 1) =
          x ^ ((ε : ℝ) + 1 / 2 - γ₂ - 1) * x ^ (γ₂ - γ₁) := by
      calc
        x ^ ((ε : ℝ) + 1 / 2 - γ₁ - 1) =
            x ^ (((ε : ℝ) + 1 / 2 - γ₂ - 1) + (γ₂ - γ₁)) := by
          congr 1
          ring
        _ = _ := Real.rpow_add hxpos _ _
    rw [hxpow]
    ring
  have hyFactor :
      exceptionalPencilExteriorDensity m ε γ₁ γ₂ a b y =
        y ^ e * (A * y ^ d + B) := by
    rw [exceptionalPencilExteriorDensity]
    dsimp only [A, B, e, d]
    have hypow :
        y ^ ((ε : ℝ) + 1 / 2 - γ₁ - 1) =
          y ^ ((ε : ℝ) + 1 / 2 - γ₂ - 1) * y ^ (γ₂ - γ₁) := by
      calc
        y ^ ((ε : ℝ) + 1 / 2 - γ₁ - 1) =
            y ^ (((ε : ℝ) + 1 / 2 - γ₂ - 1) + (γ₂ - γ₁)) := by
          congr 1
          ring
        _ = _ := Real.rpow_add hypos _ _
    rw [hypow]
    ring
  have hxLinear : A * x ^ d + B = 0 := by
    rw [hxFactor] at hxzero
    exact (mul_eq_zero.mp hxzero).resolve_left
      (Real.rpow_pos_of_pos hxpos e).ne'
  intro hyzero
  have hyLinear : A * y ^ d + B = 0 := by
    rw [hyFactor] at hyzero
    exact (mul_eq_zero.mp hyzero).resolve_left
      (Real.rpow_pos_of_pos hypos e).ne'
  have hA : A ≠ 0 := by
    intro hAzero
    have hBzero : B = 0 := by simpa only [hAzero, zero_mul, zero_add] using hxLinear
    rcases hcoeff with hcoeff | hcoeff
    · exact hcoeff hAzero
    · exact hcoeff hBzero
  have hpowers : x ^ d = y ^ d := by
    apply mul_left_cancel₀ hA
    linarith
  have hpowlt : x ^ d < y ^ d :=
    Real.rpow_lt_rpow hxpos.le hxy hd
  linarith

private theorem exceptionalPencilExteriorDensity_crossing_pos
    (m ε : ℕ) {γ₁ γ₂ a b κ x : ℝ}
    (hγ : γ₁ < γ₂) (hκ : 1 < κ) (hx : 1 < x) (hxκ : x ≠ κ)
    (hcoeff :
      a * (exceptionalEulerInverse m ε γ₁).eval 1 ≠ 0 ∨
        b * (exceptionalEulerInverse m ε γ₂).eval 1 ≠ 0)
    (hκzero : exceptionalPencilExteriorDensity
      m ε γ₁ γ₂ a b κ = 0) :
    0 < exceptionalPencilExteriorDensity m ε γ₁ γ₂ a b 1 *
      ((κ - x) *
        exceptionalPencilExteriorDensity m ε γ₁ γ₂ a b x) := by
  let A := a * (exceptionalEulerInverse m ε γ₁).eval 1
  let B := b * (exceptionalEulerInverse m ε γ₂).eval 1
  let e := (ε : ℝ) + 1 / 2 - γ₂ - 1
  let d := γ₂ - γ₁
  have hκpos : 0 < κ := one_pos.trans hκ
  have hxpos : 0 < x := one_pos.trans hx
  have hd : 0 < d := by
    dsimp only [d]
    linarith
  have hfactor : ∀ {z : ℝ}, 0 < z →
      exceptionalPencilExteriorDensity m ε γ₁ γ₂ a b z =
        z ^ e * (A * z ^ d + B) := by
    intro z hz
    rw [exceptionalPencilExteriorDensity]
    dsimp only [A, B, e, d]
    have hzpow :
        z ^ ((ε : ℝ) + 1 / 2 - γ₁ - 1) =
          z ^ ((ε : ℝ) + 1 / 2 - γ₂ - 1) *
            z ^ (γ₂ - γ₁) := by
      calc
        z ^ ((ε : ℝ) + 1 / 2 - γ₁ - 1) =
            z ^ (((ε : ℝ) + 1 / 2 - γ₂ - 1) +
              (γ₂ - γ₁)) := by
          congr 1
          ring
        _ = _ := Real.rpow_add hz _ _
    rw [hzpow]
    ring
  have hκLinear : A * κ ^ d + B = 0 := by
    rw [hfactor hκpos] at hκzero
    exact (mul_eq_zero.mp hκzero).resolve_left
      (Real.rpow_pos_of_pos hκpos e).ne'
  have hA : A ≠ 0 := by
    intro hAzero
    have hBzero : B = 0 := by
      simpa only [hAzero, zero_mul, zero_add] using hκLinear
    rcases hcoeff with hcoeff | hcoeff
    · exact hcoeff hAzero
    · exact hcoeff hBzero
  have hOne :
      exceptionalPencilExteriorDensity m ε γ₁ γ₂ a b 1 =
        A * (1 - κ ^ d) := by
    calc
      exceptionalPencilExteriorDensity m ε γ₁ γ₂ a b 1 =
          A + B := by simp [exceptionalPencilExteriorDensity, A, B]
      _ = A * (1 - κ ^ d) := by linarith
  have hX :
      exceptionalPencilExteriorDensity m ε γ₁ γ₂ a b x =
        x ^ e * A * (x ^ d - κ ^ d) := by
    rw [hfactor hxpos]
    have hB : B = -(A * κ ^ d) := by linarith
    rw [hB]
    ring
  have hκpow : 1 < κ ^ d := by
    simpa only [Real.one_rpow] using
      Real.rpow_lt_rpow one_pos.le hκ hd
  have hpair : (κ - x) * (x ^ d - κ ^ d) < 0 := by
    rcases lt_or_gt_of_ne hxκ with hxκ | hκx
    · have hpow := Real.rpow_lt_rpow hxpos.le hxκ hd
      exact mul_neg_of_pos_of_neg (sub_pos.mpr hxκ)
        (sub_neg.mpr hpow)
    · have hpow := Real.rpow_lt_rpow hκpos.le hκx hd
      exact mul_neg_of_neg_of_pos (sub_neg.mpr hκx)
        (sub_pos.mpr hpow)
  have hxpow : 0 < x ^ e := Real.rpow_pos_of_pos hxpos e
  rw [hOne, hX]
  calc
    A * (1 - κ ^ d) *
        ((κ - x) * (x ^ e * A * (x ^ d - κ ^ d))) =
      A ^ 2 * x ^ e * (κ ^ d - 1) *
        (-((κ - x) * (x ^ d - κ ^ d))) := by ring
    _ > 0 :=
      mul_pos
        (mul_pos
          (mul_pos (sq_pos_of_ne_zero hA) hxpow)
          (sub_pos.mpr hκpow))
        (neg_pos.mpr hpair)

/-- Algebraic P6 identity for an arbitrary signed pencil member. -/
theorem jacobiBetaZeroFunctional_exceptionalPencil_mul_eq
    (m ε : ℕ) {γ₁ γ₂ a b : ℝ} (p : ℝ[X])
    (hγ₁ : (ε : ℝ) + 1 / 2 + m - 1 < γ₁)
    (hγ₂ : (ε : ℝ) + 1 / 2 + m - 1 < γ₂)
    (hp : p.natDegree < m) :
    jacobiBetaZeroFunctional ((ε : ℝ) - 1 / 2)
        ((C a * exceptionalEulerInverse m ε γ₁ +
          C b * exceptionalEulerInverse m ε γ₂) * p) =
      -(a * (exceptionalEulerInverse m ε γ₁).eval 1) *
          exceptionalExteriorFunctional
            ((ε : ℝ) + 1 / 2) γ₁ p -
        (b * (exceptionalEulerInverse m ε γ₂).eval 1) *
          exceptionalExteriorFunctional
            ((ε : ℝ) + 1 / 2) γ₂ p := by
  rw [add_mul, jacobiBetaZeroFunctional_add]
  rw [show C a * exceptionalEulerInverse m ε γ₁ * p =
      C a * (exceptionalEulerInverse m ε γ₁ * p) by ring,
    show C b * exceptionalEulerInverse m ε γ₂ * p =
      C b * (exceptionalEulerInverse m ε γ₂ * p) by ring,
    jacobiBetaZeroFunctional_C_mul,
    jacobiBetaZeroFunctional_C_mul,
    jacobiBetaZeroFunctional_exceptionalEulerInverse_mul_eq
      m ε p hγ₁ hp,
    jacobiBetaZeroFunctional_exceptionalEulerInverse_mul_eq
      m ε p hγ₂ hp]
  ring

private theorem integrableOn_exceptionalExteriorIntegrand
    (c γ : ℝ) (p : ℝ[X]) (hγ : c + p.natDegree < γ) :
    IntegrableOn (fun x : ℝ => p.eval x * x ^ (c - γ - 1))
      (Ioi 1) volume := by
  have hexponent : ∀ j ∈ Finset.range (p.natDegree + 1),
      c - γ - 1 + (j : ℝ) < -1 := by
    intro j hj
    have hjle : j ≤ p.natDegree := by
      have hjlt := Finset.mem_range.mp hj
      lia
    have hjleCast : (j : ℝ) ≤ p.natDegree := by exact_mod_cast hjle
    linarith
  have hsum : IntegrableOn
      (fun x : ℝ => ∑ j ∈ Finset.range (p.natDegree + 1),
        p.coeff j * x ^ (c - γ - 1 + (j : ℝ)))
      (Ioi 1) volume := by
    apply integrable_finsetSum
    intro j hj
    exact (integrableOn_Ioi_rpow_of_lt
      (hexponent j hj) one_pos).const_mul _
  exact hsum.congr_fun (fun x hx => by
    have hxpos : 0 < x := lt_trans one_pos hx
    rw [Polynomial.eval_eq_sum_range]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Real.rpow_add hxpos, Real.rpow_natCast]
    ring) measurableSet_Ioi

private theorem integrableOn_mul_exceptionalPencilExteriorDensity
    (m ε : ℕ) {γ₁ γ₂ a b : ℝ} (p : ℝ[X])
    (hγ₁ : (ε : ℝ) + 1 / 2 + p.natDegree < γ₁)
    (hγ₂ : (ε : ℝ) + 1 / 2 + p.natDegree < γ₂) :
    IntegrableOn
      (fun x : ℝ => p.eval x *
        exceptionalPencilExteriorDensity m ε γ₁ γ₂ a b x)
      (Ioi 1) volume := by
  let c : ℝ := ε + 1 / 2
  let A := a * (exceptionalEulerInverse m ε γ₁).eval 1
  let B := b * (exceptionalEulerInverse m ε γ₂).eval 1
  have h₁ := integrableOn_exceptionalExteriorIntegrand
    c γ₁ p (by simpa only [c] using hγ₁)
  have h₂ := integrableOn_exceptionalExteriorIntegrand
    c γ₂ p (by simpa only [c] using hγ₂)
  have hsum : IntegrableOn
      (fun x : ℝ =>
        A * (p.eval x * x ^ (c - γ₁ - 1)) +
          B * (p.eval x * x ^ (c - γ₂ - 1)))
      (Ioi 1) volume :=
    (h₁.const_mul A).add (h₂.const_mul B)
  exact hsum.congr_fun (fun x hx => by
    unfold exceptionalPencilExteriorDensity
    dsimp only [A, B, c]
    ring) measurableSet_Ioi

private theorem setIntegral_pos_of_pos_Ioi
    {f : ℝ → ℝ} (hfInt : IntegrableOn f (Ioi 1) volume)
    (hfPos : ∀ x : ℝ, 1 < x → 0 < f x) :
    0 < ∫ x in Ioi (1 : ℝ), f x := by
  have hfNonneg : 0 ≤ᵐ[volume.restrict (Ioi 1)] f := by
    rw [Filter.EventuallyLE,
      MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with x hx
    exact (hfPos x hx).le
  apply (MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae
    hfNonneg hfInt).mpr
  have hsubset : Ioo (1 : ℝ) 2 ⊆
      Function.support f ∩ Ioi 1 := by
    intro x hx
    exact ⟨Function.mem_support.mpr (hfPos x hx.1).ne', hx.1⟩
  exact ((MeasureTheory.Measure.measure_Ioo_pos _).mpr
    (show (1 : ℝ) < 2 by norm_num)).trans_le
      (MeasureTheory.measure_mono hsubset)

/-- Integral form of P6 for an arbitrary signed pencil member. -/
theorem exceptionalEulerInverse_pencil_signedMomentIdentity
    (m ε : ℕ) {γ₁ γ₂ a b : ℝ} (p : ℝ[X])
    (hγ₁ : (ε : ℝ) + 1 / 2 + m - 1 < γ₁)
    (hγ₂ : (ε : ℝ) + 1 / 2 + m - 1 < γ₂)
    (hp : p.natDegree < m) :
    (∫ x : ℝ in 0..1,
        ((C a * exceptionalEulerInverse m ε γ₁ +
          C b * exceptionalEulerInverse m ε γ₂) * p).eval x *
            x ^ ((ε : ℝ) - 1 / 2)) =
      -∫ x in Ioi (1 : ℝ),
        p.eval x * exceptionalPencilExteriorDensity
          m ε γ₁ γ₂ a b x := by
  let c : ℝ := ε + 1 / 2
  let A := a * (exceptionalEulerInverse m ε γ₁).eval 1
  let B := b * (exceptionalEulerInverse m ε γ₂).eval 1
  have hε : 0 ≤ (ε : ℝ) := by positivity
  have hα : -1 < (ε : ℝ) - 1 / 2 := by linarith
  have hpCast : (p.natDegree : ℝ) ≤ m - 1 := by
    have hpOne : p.natDegree + 1 ≤ m := by lia
    have hpOneCast : (p.natDegree : ℝ) + 1 ≤ m := by
      exact_mod_cast hpOne
    linarith
  have hγ₁p : c + p.natDegree < γ₁ := by
    dsimp only [c]
    linarith
  have hγ₂p : c + p.natDegree < γ₂ := by
    dsimp only [c]
    linarith
  have hint₁ := integrableOn_exceptionalExteriorIntegrand
    c γ₁ p hγ₁p
  have hint₂ := integrableOn_exceptionalExteriorIntegrand
    c γ₂ p hγ₂p
  rw [← jacobiBetaZeroFunctional_eq_integral hα]
  rw [jacobiBetaZeroFunctional_exceptionalPencil_mul_eq
    m ε p hγ₁ hγ₂ hp]
  rw [exceptionalExteriorFunctional_eq_integral c γ₁ p hγ₁p,
    exceptionalExteriorFunctional_eq_integral c γ₂ p hγ₂p]
  change
    -A * (∫ x in Ioi (1 : ℝ), p.eval x * x ^ (c - γ₁ - 1)) -
        B * (∫ x in Ioi (1 : ℝ), p.eval x * x ^ (c - γ₂ - 1)) = _
  rw [show -A * (∫ x in Ioi (1 : ℝ),
          p.eval x * x ^ (c - γ₁ - 1)) -
        B * (∫ x in Ioi (1 : ℝ),
          p.eval x * x ^ (c - γ₂ - 1)) =
      -(A * (∫ x in Ioi (1 : ℝ),
          p.eval x * x ^ (c - γ₁ - 1)) +
        B * (∫ x in Ioi (1 : ℝ),
          p.eval x * x ^ (c - γ₂ - 1))) by ring]
  congr 1
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add (hint₁.const_mul A) (hint₂.const_mul B)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  unfold exceptionalPencilExteriorDensity
  dsimp only [A, B, c]
  ring

private def interiorRootProduct (q : ℝ[X]) : ℝ[X] :=
  ((q.roots.filter fun r => 0 < r ∧ r < 1).map
    fun r => X - C r).prod

private theorem natDegree_interiorRootProduct (q : ℝ[X]) :
    (interiorRootProduct q).natDegree =
      (q.roots.filter fun r => 0 < r ∧ r < 1).card := by
  exact Polynomial.natDegree_multiset_prod_X_sub_C_eq_card _

private theorem interiorRootProduct_eval_pos_of_one_le
    (q : ℝ[X]) {x : ℝ} (hx : 1 ≤ x) :
    0 < (interiorRootProduct q).eval x := by
  rw [interiorRootProduct, Polynomial.eval_multiset_prod,
    Multiset.map_map]
  apply Multiset.prod_pos
  intro y hy
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hy
  have hrOne : r < 1 := (Multiset.mem_filter.mp hr).2.2
  simpa using sub_pos.mpr (hrOne.trans_le hx)

private theorem exists_interiorRootComplement
    {q : ℝ[X]} (hq : q ≠ 0) :
    ∃ s : ℝ[X], interiorRootProduct q * s = q ∧
      ∀ x : ℝ, 0 < x → x < 1 → s.eval x ≠ 0 := by
  let rootsI := q.roots.filter fun r => 0 < r ∧ r < 1
  let P := (rootsI.map fun r => X - C r).prod
  have hPle : rootsI ≤ q.roots := Multiset.filter_le _ _
  have hPdvd : P ∣ q :=
    (Multiset.prod_X_sub_C_dvd_iff_le_roots hq rootsI).mpr hPle
  obtain ⟨s, hs⟩ := hPdvd
  have hP : P ≠ 0 :=
    (Polynomial.monic_multisetProd_X_sub_C rootsI).ne_zero
  have hs0 : s ≠ 0 := by
    intro hszero
    rw [hszero, mul_zero] at hs
    exact hq hs
  refine ⟨s, ?_, ?_⟩
  · simpa only [interiorRootProduct, P, rootsI] using hs.symm
  · intro x hx0 hx1 hsx
    have hsroot : s.IsRoot x := by
      simpa only [Polynomial.IsRoot.def] using hsx
    have hsMem : x ∈ s.roots :=
      (Polynomial.mem_roots hs0).mpr hsroot
    have hroots : q.roots = rootsI + s.roots := by
      rw [hs, Polynomial.roots_mul (mul_ne_zero hP hs0),
        Polynomial.roots_multiset_prod_X_sub_C]
    have hcount := congrArg (fun u : Multiset ℝ => u.count x) hroots
    have hfilter : rootsI.count x = q.roots.count x := by
      simp [rootsI, hx0, hx1]
    have hsCount : 0 < s.roots.count x :=
      Multiset.count_pos.mpr hsMem
    simp only [Multiset.count_add] at hcount
    lia

private theorem interiorRootProduct_signedIntegral_pos
    {q : ℝ[X]} (hq : q ≠ 0) (hqOne : q.eval 1 ≠ 0)
    {α : ℝ} (hα : -1 < α) (t : ℝ[X])
    (ht : ∀ x : ℝ, 0 < x → x ≤ 1 → 0 < t.eval x) :
    0 < q.eval 1 *
      (∫ x : ℝ in 0..1,
        (q * (interiorRootProduct q * t)).eval x * x ^ α) := by
  let P := interiorRootProduct q
  obtain ⟨s, hfactor, hsNo⟩ :=
    (show ∃ s : ℝ[X], P * s = q ∧
        ∀ x : ℝ, 0 < x → x < 1 → s.eval x ≠ 0 by
      simpa only [P] using exists_interiorRootComplement hq)
  have hP : P ≠ 0 := by
    dsimp only [P, interiorRootProduct]
    exact (Polynomial.monic_multisetProd_X_sub_C _).ne_zero
  have hPone : 0 < P.eval 1 := by
    dsimp only [P]
    exact interiorRootProduct_eval_pos_of_one_le q le_rfl
  have hfactorEval : ∀ x : ℝ, P.eval x * s.eval x = q.eval x := by
    intro x
    simpa only [eval_mul] using
      congrArg (Polynomial.eval x) hfactor
  have hsOne : s.eval 1 ≠ 0 := by
    intro hsOne
    have h := hfactorEval 1
    rw [hsOne, mul_zero] at h
    exact hqOne h.symm
  have hsSame : ∀ x : ℝ, 0 < x → x ≤ 1 →
      0 < s.eval x * s.eval 1 := by
    intro x hx0 hx1
    apply eval_same_sign_of_no_roots hx1
    intro z hxz hz1
    by_cases hz : z = 1
    · simpa only [hz] using hsOne
    · exact hsNo z (hx0.trans_le hxz) (lt_of_le_of_ne hz1 hz)
  let f : ℝ → ℝ := fun x =>
    q.eval 1 * ((q * (P * t)).eval x * x ^ α)
  have hfInt : IntervalIntegrable f volume 0 1 := by
    have h := intervalIntegrable_jacobiBetaZeroIntegrand hα
      (C (q.eval 1) * (q * (P * t)))
    convert h using 1
    ext x
    simp only [f, eval_mul, eval_C]
    ring
  have hfNonneg : 0 ≤ᵐ[volume.restrict (Set.uIoc 0 1)] f := by
    rw [Set.uIoc_of_le zero_le_one, Filter.EventuallyLE,
      MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with x hx
    have hsPos := hsSame x hx.1 hx.2
    have hxpow : 0 < x ^ α := Real.rpow_pos_of_pos hx.1 α
    have htPos := ht x hx.1 hx.2
    have hfactorX := hfactorEval x
    have hfactorOne := hfactorEval 1
    dsimp only [f]
    simp only [eval_mul]
    calc
      q.eval 1 * (q.eval x * (P.eval x * t.eval x) * x ^ α) =
          P.eval 1 * P.eval x ^ 2 *
            (s.eval x * s.eval 1) * t.eval x * x ^ α := by
        rw [← hfactorX, ← hfactorOne]
        ring
      _ ≥ 0 := by positivity
  obtain ⟨x, hx, havoid⟩ :=
    (Set.Ioo_infinite (show (0 : ℝ) < 1 by norm_num)).exists_notMem_finset
      P.roots.toFinset
  have hPx : P.eval x ≠ 0 := by
    intro hPx
    apply havoid
    have hroot : P.IsRoot x := by
      simpa only [Polynomial.IsRoot.def] using hPx
    exact Multiset.mem_toFinset.mpr
      ((Polynomial.mem_roots hP).mpr hroot)
  have hfx : 0 < f x := by
    have hsPos := hsSame x hx.1 hx.2.le
    have hxpow : 0 < x ^ α := Real.rpow_pos_of_pos hx.1 α
    have htPos := ht x hx.1 hx.2.le
    have hfactorX := hfactorEval x
    have hfactorOne := hfactorEval 1
    dsimp only [f]
    simp only [eval_mul]
    calc
      q.eval 1 * (q.eval x * (P.eval x * t.eval x) * x ^ α) =
          P.eval 1 * P.eval x ^ 2 *
            (s.eval x * s.eval 1) * t.eval x * x ^ α := by
        rw [← hfactorX, ← hfactorOne]
        ring
      _ > 0 := by positivity
  have hfCont : ContinuousAt f x := by
    have hx0 : x ≠ 0 := hx.1.ne'
    dsimp only [f]
    exact continuousAt_const.mul
      ((q * (P * t)).continuousAt.mul
        (continuousAt_id.rpow_const (Or.inl hx0)))
  have hevent : ∀ᶠ y in nhds x, f y ≠ 0 :=
    hfCont.eventually_ne hfx.ne'
  obtain ⟨a, b, hxab, hab⟩ := hevent.exists_Ioo_subset
  let a' := max a 0
  let b' := min b 1
  have ha'x : a' < x := max_lt hxab.1 hx.1
  have hxb' : x < b' := lt_min hxab.2 hx.2
  have ha'b' : a' < b' := ha'x.trans hxb'
  have hsubset : Set.Ioo a' b' ⊆
      Function.support f ∩ Set.Ioc 0 1 := by
    intro y hy
    have hay : a < y := (le_max_left a 0).trans_lt hy.1
    have hyb : y < b := hy.2.trans_le (min_le_left b 1)
    refine ⟨Function.mem_support.mpr (hab ⟨hay, hyb⟩), ?_⟩
    exact ⟨(le_max_right a 0).trans_lt hy.1,
      (hy.2.trans_le (min_le_right b 1)).le⟩
  have hmeasure : 0 < volume
      (Function.support f ∩ Set.Ioc 0 1) :=
    ((MeasureTheory.Measure.measure_Ioo_pos _).mpr ha'b').trans_le
      (MeasureTheory.measure_mono hsubset)
  rw [← intervalIntegral.integral_const_mul]
  exact (intervalIntegral.integral_pos_iff_support_of_nonneg_ae'
    hfNonneg hfInt).mpr ⟨zero_lt_one, hmeasure⟩

/-- A generic nonzero exceptional pencil member has at least `m - 1` roots,
counted with multiplicity, in the open unit interval. -/
theorem exceptionalEulerInverse_pencil_card_roots_Ioo_ge_sub_one
    (m ε : ℕ) {γ₁ γ₂ a b : ℝ} (hm : 0 < m)
    (hγ₁ : (ε : ℝ) + 1 / 2 + m - 1 < γ₁)
    (hγ₂ : (ε : ℝ) + 1 / 2 + m - 1 < γ₂)
    (hγ : γ₁ < γ₂) (hab : a ≠ 0 ∨ b ≠ 0)
    (hOne :
      (C a * exceptionalEulerInverse m ε γ₁ +
        C b * exceptionalEulerInverse m ε γ₂).eval 1 ≠ 0) :
    m - 1 ≤
      ((C a * exceptionalEulerInverse m ε γ₁ +
        C b * exceptionalEulerInverse m ε γ₂).roots.filter
          fun r => 0 < r ∧ r < 1).card := by
  let Q := C a * exceptionalEulerInverse m ε γ₁ +
    C b * exceptionalEulerInverse m ε γ₂
  let P := interiorRootProduct Q
  let K := exceptionalPencilExteriorDensity m ε γ₁ γ₂ a b
  have hQOne : Q.eval 1 ≠ 0 := by
    simpa only [Q] using hOne
  have hQ : Q ≠ 0 := by
    intro hzero
    apply hQOne
    rw [hzero]
    simp
  have hR₁One :
      (exceptionalEulerInverse m ε γ₁).eval 1 ≠ 0 := by
    have hsign :=
      negOnePow_mul_exceptionalEulerInverse_eval_one_pos
        m ε hm hγ₁
    intro hzero
    rw [hzero, mul_zero] at hsign
    linarith
  have hR₂One :
      (exceptionalEulerInverse m ε γ₂).eval 1 ≠ 0 := by
    have hsign :=
      negOnePow_mul_exceptionalEulerInverse_eval_one_pos
        m ε hm hγ₂
    intro hzero
    rw [hzero, mul_zero] at hsign
    linarith
  have hcoeff :
      a * (exceptionalEulerInverse m ε γ₁).eval 1 ≠ 0 ∨
        b * (exceptionalEulerInverse m ε γ₂).eval 1 ≠ 0 := by
    rcases hab with ha | hb
    · exact Or.inl (mul_ne_zero ha hR₁One)
    · exact Or.inr (mul_ne_zero hb hR₂One)
  have hKOne : K 1 = Q.eval 1 := by
    simpa only [K, Q] using
      exceptionalPencilExteriorDensity_one m ε γ₁ γ₂ a b
  have hα : -1 < (ε : ℝ) - 1 / 2 := by
    have hε : 0 ≤ (ε : ℝ) := by positivity
    linarith
  have hparameterBound : ∀ {p : ℝ[X]}, p.natDegree < m →
      (ε : ℝ) + 1 / 2 + p.natDegree < γ₁ ∧
        (ε : ℝ) + 1 / 2 + p.natDegree < γ₂ := by
    intro p hp
    have hpOne : p.natDegree + 1 ≤ m := by lia
    have hpCast : (p.natDegree : ℝ) + 1 ≤ m := by
      exact_mod_cast hpOne
    constructor <;> linarith
  by_contra hcount
  have hcard :
      (Q.roots.filter fun r => 0 < r ∧ r < 1).card < m - 1 := by
    simpa only [Q] using Nat.lt_of_not_ge hcount
  have hPdeg : P.natDegree < m := by
    rw [show P = interiorRootProduct Q by rfl,
      natDegree_interiorRootProduct]
    lia
  have hPdegSucc : P.natDegree + 1 < m := by
    rw [show P = interiorRootProduct Q by rfl,
      natDegree_interiorRootProduct]
    lia
  have hPpos : ∀ x : ℝ, 1 < x → 0 < P.eval x := by
    intro x hx
    exact interiorRootProduct_eval_pos_of_one_le Q hx.le
  by_cases hzero : ∃ κ : ℝ, 1 < κ ∧ K κ = 0
  · obtain ⟨κ, hκ, hκzero⟩ := hzero
    let T : ℝ[X] := C κ - X
    let test := P * T
    have hTdeg : T.natDegree ≤ 1 := by
      dsimp only [T]
      simpa using natDegree_sub_le (C κ) X
    have htestDeg : test.natDegree < m := by
      calc
        test.natDegree ≤ P.natDegree + T.natDegree :=
          natDegree_mul_le
        _ ≤ P.natDegree + 1 := Nat.add_le_add_left hTdeg _
        _ < m := hPdegSucc
    have hTpos : ∀ x : ℝ, 0 < x → x ≤ 1 → 0 < T.eval x := by
      intro x hx0 hx1
      dsimp only [T]
      simp only [eval_sub, eval_C, eval_X]
      linarith
    have hInterior :
        0 < Q.eval 1 *
          (∫ x : ℝ in 0..1,
            (Q * test).eval x * x ^ ((ε : ℝ) - 1 / 2)) := by
      simpa only [test, T, P] using
        interiorRootProduct_signedIntegral_pos
          hQ hQOne hα (C κ - X) hTpos
    have hmoment :=
      exceptionalEulerInverse_pencil_signedMomentIdentity
        m ε (a := a) (b := b) test hγ₁ hγ₂ htestDeg
    have hbounds := hparameterBound htestDeg
    have hExtInt :=
      integrableOn_mul_exceptionalPencilExteriorDensity
        m ε (a := a) (b := b) test hbounds.1 hbounds.2
    let f : ℝ → ℝ := fun x =>
      Q.eval 1 * (test.eval x * K x)
    have hfNonneg : 0 ≤ᵐ[volume.restrict (Ioi 1)] f := by
      rw [Filter.EventuallyLE,
        MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
      filter_upwards with x hx
      by_cases hxκ : x = κ
      · subst x
        change 0 ≤ f κ
        dsimp only [f]
        rw [hκzero]
        simp
      · have hcross :=
          exceptionalPencilExteriorDensity_crossing_pos
            m ε hγ hκ hx hxκ hcoeff hκzero
        have hP := hPpos x hx
        dsimp only [f, test, T]
        simp only [eval_mul, eval_sub, eval_C, eval_X]
        rw [← hKOne]
        calc
          K 1 * (P.eval x * (κ - x) * K x) =
              P.eval x * (K 1 * ((κ - x) * K x)) := by ring
          _ ≥ 0 := (mul_pos hP hcross).le
    have hfInt : IntegrableOn f (Ioi 1) volume := by
      exact hExtInt.const_mul (Q.eval 1)
    have hsubset : Ioo (1 : ℝ) κ ⊆
        Function.support f ∩ Ioi 1 := by
      intro x hx
      have hxκ : x ≠ κ := ne_of_lt hx.2
      have hcross :=
        exceptionalPencilExteriorDensity_crossing_pos
          m ε hγ hκ hx.1 hxκ hcoeff hκzero
      have hP := hPpos x hx.1
      refine ⟨Function.mem_support.mpr ?_, hx.1⟩
      dsimp only [f, test, T]
      simp only [eval_mul, eval_sub, eval_C, eval_X]
      rw [← hKOne]
      have hpos :
          0 < K 1 * (P.eval x * (κ - x) * K x) := by
        calc
          K 1 * (P.eval x * (κ - x) * K x) =
              P.eval x * (K 1 * ((κ - x) * K x)) := by ring
          _ > 0 := mul_pos hP hcross
      exact hpos.ne'
    have hExterior :
        0 < Q.eval 1 *
          (∫ x in Ioi (1 : ℝ), test.eval x * K x) := by
      rw [← MeasureTheory.integral_const_mul]
      apply (MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae
        hfNonneg hfInt).mpr
      exact ((MeasureTheory.Measure.measure_Ioo_pos _).mpr hκ).trans_le
        (MeasureTheory.measure_mono hsubset)
    have hEq := congrArg (fun z : ℝ => Q.eval 1 * z) hmoment
    dsimp only [Q, K] at hmoment hEq
    nlinarith
  · have hKNo : ∀ x : ℝ, 1 < x → K x ≠ 0 := by
      intro x hx hKx
      exact hzero ⟨x, hx, hKx⟩
    let test : ℝ[X] := P
    have hInterior :
        0 < Q.eval 1 *
          (∫ x : ℝ in 0..1,
            (Q * test).eval x * x ^ ((ε : ℝ) - 1 / 2)) := by
      simpa only [test, P, mul_one] using
        interiorRootProduct_signedIntegral_pos
          hQ hQOne hα 1 (by simp)
    have hmoment :=
      exceptionalEulerInverse_pencil_signedMomentIdentity
        m ε (a := a) (b := b) test hγ₁ hγ₂ hPdeg
    have hbounds := hparameterBound hPdeg
    have hExtInt :=
      integrableOn_mul_exceptionalPencilExteriorDensity
        m ε (a := a) (b := b) test hbounds.1 hbounds.2
    have hKsame : ∀ x : ℝ, 1 < x → 0 < K 1 * K x := by
      intro x hx
      apply mul_pos_of_continuousOn_of_ne_zero hx.le
      · intro z hz
        exact (continuousAt_exceptionalPencilExteriorDensity
          m ε γ₁ γ₂ a b
            (one_pos.trans_le hz.1).ne').continuousWithinAt
      · intro z hz1 hzx
        by_cases hz : z = 1
        · simpa only [hz, hKOne] using hQOne
        · exact hKNo z (lt_of_le_of_ne hz1 (Ne.symm hz))
    have hExterior :
        0 < Q.eval 1 *
          (∫ x in Ioi (1 : ℝ), test.eval x * K x) := by
      rw [← MeasureTheory.integral_const_mul]
      apply setIntegral_pos_of_pos_Ioi
        (hExtInt.const_mul (Q.eval 1))
      intro x hx
      have hP := hPpos x hx
      have hsame := hKsame x hx
      dsimp only [test]
      rw [← hKOne]
      nlinarith
    have hEq := congrArg (fun z : ℝ => Q.eval 1 * z) hmoment
    dsimp only [Q, K] at hmoment hEq
    nlinarith

/-- A generic exceptional pencil member splits over `ℝ`.  The interior-root
product leaves a quotient of degree at most one. -/
theorem exceptionalEulerInverse_pencil_splits_of_eval_one_ne_zero
    (m ε : ℕ) {γ₁ γ₂ a b : ℝ} (hm : 0 < m)
    (hγ₁ : (ε : ℝ) + 1 / 2 + m - 1 < γ₁)
    (hγ₂ : (ε : ℝ) + 1 / 2 + m - 1 < γ₂)
    (hγ : γ₁ < γ₂) (hab : a ≠ 0 ∨ b ≠ 0)
    (hOne :
      (C a * exceptionalEulerInverse m ε γ₁ +
        C b * exceptionalEulerInverse m ε γ₂).eval 1 ≠ 0) :
    (C a * exceptionalEulerInverse m ε γ₁ +
      C b * exceptionalEulerInverse m ε γ₂).Splits := by
  let Q := C a * exceptionalEulerInverse m ε γ₁ +
    C b * exceptionalEulerInverse m ε γ₂
  let P := interiorRootProduct Q
  have hQOne : Q.eval 1 ≠ 0 := by
    simpa only [Q] using hOne
  have hQ : Q ≠ 0 := by
    intro hzero
    apply hQOne
    rw [hzero]
    simp
  have hPdeg : m - 1 ≤ P.natDegree := by
    rw [show P = interiorRootProduct Q by rfl,
      natDegree_interiorRootProduct]
    simpa only [Q] using
      exceptionalEulerInverse_pencil_card_roots_Ioo_ge_sub_one
        m ε hm hγ₁ hγ₂ hγ hab hOne
  have hQdeg : Q.natDegree ≤ m := by
    dsimp only [Q]
    exact (Polynomial.natDegree_add_le _ _).trans
      (max_le
        ((Polynomial.natDegree_C_mul_le a _).trans
          (natDegree_exceptionalEulerInverse_le m ε γ₁))
        ((Polynomial.natDegree_C_mul_le b _).trans
          (natDegree_exceptionalEulerInverse_le m ε γ₂)))
  obtain ⟨s, hfactor, -⟩ := exists_interiorRootComplement hQ
  have hP : P ≠ 0 := by
    dsimp only [P, interiorRootProduct]
    exact (Polynomial.monic_multisetProd_X_sub_C _).ne_zero
  have hs : s ≠ 0 := by
    apply right_ne_zero_of_mul
    rw [hfactor]
    exact hQ
  have hPsplit : P.Splits := by
    apply splits_of_card_roots
    rw [show P = interiorRootProduct Q by rfl, interiorRootProduct,
      Polynomial.roots_multiset_prod_X_sub_C,
      Polynomial.natDegree_multiset_prod_X_sub_C_eq_card]
  have hdegMul := Polynomial.natDegree_mul hP hs
  rw [hfactor] at hdegMul
  have hsdeg : s.natDegree ≤ 1 := by lia
  have hssplit : s.Splits :=
    (isRealRooted_of_natDegree_le_one hs hsdeg).2
  change Q.Splits
  rw [← hfactor]
  simpa only [P] using hPsplit.mul hssplit

private theorem exceptionalEulerInverse_pencil_splits_of_eval_one_eq_zero
    (m ε : ℕ) {γ₁ γ₂ a b : ℝ} (hm : 0 < m)
    (hγ₁ : (ε : ℝ) + 1 / 2 + m - 1 < γ₁)
    (hγ₂ : (ε : ℝ) + 1 / 2 + m - 1 < γ₂)
    (hγ : γ₁ < γ₂)
    (hOne :
      (C a * exceptionalEulerInverse m ε γ₁ +
        C b * exceptionalEulerInverse m ε γ₂).eval 1 = 0) :
    (C a * exceptionalEulerInverse m ε γ₁ +
      C b * exceptionalEulerInverse m ε γ₂).Splits := by
  let R := exceptionalEulerInverse m ε γ₁
  let Q := C a * R + C b * exceptionalEulerInverse m ε γ₂
  change Q.Splits
  by_cases hQ : Q = 0
  · rw [hQ]
    exact Polynomial.Splits.zero
  have hQOne : Q.eval 1 = 0 := by
    simpa only [Q, R] using hOne
  have hmCast : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hε : 0 ≤ (ε : ℝ) := by positivity
  have hγ₁pos : 0 < γ₁ := by linarith
  have hγ₂pos : 0 < γ₂ := by linarith
  have hQdegLower : m - 1 ≤ Q.natDegree := by
    simpa only [Q, R] using
      exceptionalEulerInverse_pencil_natDegree_ge_sub_one
        m ε hm hγ₁pos hγ₂pos hγ.ne hQ
  have hQdegUpper : Q.natDegree ≤ m := by
    dsimp only [Q, R]
    exact (Polynomial.natDegree_add_le _ _).trans
      (max_le
        ((Polynomial.natDegree_C_mul_le a _).trans
          (natDegree_exceptionalEulerInverse_le m ε γ₁))
        ((Polynomial.natDegree_C_mul_le b _).trans
          (natDegree_exceptionalEulerInverse_le m ε γ₂)))
  have hR : R ≠ 0 := by
    intro hzero
    have hdegree := natDegree_exceptionalEulerInverse m ε hγ₁pos
    dsimp only [R] at hzero
    rw [hzero] at hdegree
    simp at hdegree
    lia
  have hQlc : Q.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hQ
  have hRlc : R.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hR
  let f := C Q.leadingCoeff⁻¹ * Q
  let g := C R.leadingCoeff⁻¹ * R
  have hfPos : HasPosLeadingCoeff f := by
    apply hasPosLeadingCoeff_of_monic
    dsimp only [f]
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    exact inv_mul_cancel₀ hQlc
  have hgPos : HasPosLeadingCoeff g := by
    apply hasPosLeadingCoeff_of_monic
    dsimp only [g]
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    exact inv_mul_cancel₀ hRlc
  have hfdeg : f.natDegree = Q.natDegree := by
    dsimp only [f]
    exact Polynomial.natDegree_C_mul (inv_ne_zero hQlc)
  have hgdeg : g.natDegree = m := by
    dsimp only [g, R]
    rw [Polynomial.natDegree_C_mul (inv_ne_zero hRlc),
      natDegree_exceptionalEulerInverse m ε hγ₁pos]
  have hROne : R.eval 1 ≠ 0 := by
    have hsign :=
      negOnePow_mul_exceptionalEulerInverse_eval_one_pos
        m ε hm hγ₁
    dsimp only [R]
    intro hzero
    rw [hzero, mul_zero] at hsign
    linarith
  have hfamily : ∀ {μ : ℝ}, 0 < μ →
      ((f + C μ * g) ≠ 0 ∧ (f + C μ * g).Splits) := by
    intro μ hμ
    let a' := Q.leadingCoeff⁻¹ * a +
      μ * R.leadingCoeff⁻¹
    let b' := Q.leadingCoeff⁻¹ * b
    have hrewrite :
        f + C μ * g =
          C a' * exceptionalEulerInverse m ε γ₁ +
            C b' * exceptionalEulerInverse m ε γ₂ := by
      dsimp only [f, g, Q, R, a', b']
      ext k
      simp only [coeff_add, coeff_C_mul]
      ring
    have heval : (f + C μ * g).eval 1 =
        μ * R.leadingCoeff⁻¹ * R.eval 1 := by
      dsimp only [f, g]
      simp only [eval_add, eval_mul, eval_C]
      rw [hQOne]
      ring
    have hevalNe : (f + C μ * g).eval 1 ≠ 0 := by
      rw [heval]
      exact mul_ne_zero (mul_ne_zero hμ.ne' (inv_ne_zero hRlc)) hROne
    have hab' : a' ≠ 0 ∨ b' ≠ 0 := by
      by_contra hz
      simp only [not_or, not_ne_iff] at hz
      apply hevalNe
      rw [hrewrite, hz.1, hz.2]
      simp
    refine ⟨?_, ?_⟩
    · intro hzero
      apply hevalNe
      rw [hzero]
      simp
    · rw [hrewrite]
      apply exceptionalEulerInverse_pencil_splits_of_eval_one_ne_zero
        m ε hm hγ₁ hγ₂ hγ hab'
      simpa only [← hrewrite] using hevalNe
  have hfSplit : f.Splits := by
    by_cases hdegree : Q.natDegree = m
    · have hpos : PosComboRealRooted f g :=
        PosComboRealRooted.of_add_right hfamily
      exact (hpos.isRealRooted_left_of_sameDegree hfPos hgPos
        (by rw [hgdeg, hfdeg, hdegree])).2
    · apply splits_of_add_C_mul_family_of_succDegree hfamily hfPos hgPos
      rw [hgdeg, hfdeg]
      lia
  have hscaled := hfSplit.C_mul Q.leadingCoeff
  simpa only [f, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hQlc,
    C_1, one_mul] using hscaled

/-- Every exceptional signed-pencil member splits, including the zero member,
the endpoint-value boundary, and the unique possible degree drop. -/
theorem exceptionalEulerInverse_pencil_splits
    (m ε : ℕ) {γ₁ γ₂ a b : ℝ} (hm : 0 < m)
    (hγ₁ : (ε : ℝ) + 1 / 2 + m - 1 < γ₁)
    (hγ₂ : (ε : ℝ) + 1 / 2 + m - 1 < γ₂)
    (hγ : γ₁ < γ₂) :
    (C a * exceptionalEulerInverse m ε γ₁ +
      C b * exceptionalEulerInverse m ε γ₂).Splits := by
  by_cases hOne :
      (C a * exceptionalEulerInverse m ε γ₁ +
        C b * exceptionalEulerInverse m ε γ₂).eval 1 = 0
  · exact exceptionalEulerInverse_pencil_splits_of_eval_one_eq_zero
      m ε hm hγ₁ hγ₂ hγ hOne
  · have hab : a ≠ 0 ∨ b ≠ 0 := by
      by_contra hz
      simp only [not_or, not_ne_iff] at hz
      apply hOne
      rw [hz.1, hz.2]
      simp
    exact exceptionalEulerInverse_pencil_splits_of_eval_one_ne_zero
      m ε hm hγ₁ hγ₂ hγ hab hOne

@[simp]
theorem exceptionalEulerInverse_eval_zero (m ε : ℕ) {γ : ℝ}
    (hγ : γ ≠ 0) :
    (exceptionalEulerInverse m ε γ).eval 0 = 1 := by
  rw [← coeff_zero_eq_eval_zero, coeff_exceptionalEulerInverse]
  simp [hγ]

/-- The top coefficient of the exceptional Euler inverse has sign `(-1)^m`. -/
theorem negOnePow_mul_exceptionalEulerInverse_leadingCoeff_pos
    (m ε : ℕ) {γ : ℝ} (hγ : 0 < γ) :
    0 < (-1 : ℝ) ^ m *
      (exceptionalEulerInverse m ε γ).leadingCoeff := by
  have hdegree := natDegree_exceptionalEulerInverse m ε hγ
  rw [Polynomial.leadingCoeff, hdegree,
    coeff_exceptionalEulerInverse, if_pos le_rfl,
    exceptionalBaseCoeff,
    realRisingFactorial_neg_nat_eq_factorial_div m m le_rfl]
  have hc : 0 < (ε : ℝ) + 1 / 2 := by positivity
  have hcm : 0 < (ε : ℝ) + 1 / 2 + m := by positivity
  have hdenC : 0 < realRisingFactorial ((ε : ℝ) + 1 / 2) m :=
    realRisingFactorial_pos m hc
  have hnumC : 0 < realRisingFactorial
      ((ε : ℝ) + 1 / 2 + m) m :=
    realRisingFactorial_pos m hcm
  have hsignSq : ((-1 : ℝ) ^ m) ^ 2 = 1 :=
    neg_one_pow_sq_real m
  have hγm : 0 < γ + (m : ℝ) := by positivity
  simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, div_one]
  rw [show (-1 : ℝ) ^ m *
        (((-1 : ℝ) ^ m * (m.factorial : ℝ) *
            realRisingFactorial ((ε : ℝ) + 1 / 2 + m) m /
              (realRisingFactorial ((ε : ℝ) + 1 / 2) m * m.factorial)) *
          γ / (γ + m)) =
      realRisingFactorial ((ε : ℝ) + 1 / 2 + m) m * γ /
        (realRisingFactorial ((ε : ℝ) + 1 / 2) m *
          (γ + m)) by
      field_simp [hdenC.ne', hγm.ne']
      rw [hsignSq]
      ring]
  positivity

/-- Every root of a positive-parameter exceptional Euler inverse is positive. -/
theorem exceptionalEulerInverse_roots_pos
    (m ε : ℕ) {γ : ℝ} (hm : 0 < m)
    (hγ : (ε : ℝ) + 1 / 2 + m - 1 < γ) :
    ∀ r ∈ (exceptionalEulerInverse m ε γ).roots, 0 < r := by
  let R := exceptionalEulerInverse m ε γ
  have hmCast : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hε : 0 ≤ (ε : ℝ) := by positivity
  have hγpos : 0 < γ := by linarith
  have hγsucc : (ε : ℝ) + 1 / 2 + m - 1 < γ + 1 := by linarith
  have hsplit : R.Splits := by
    simpa [R] using
      exceptionalEulerInverse_pencil_splits
        m ε (γ₁ := γ) (γ₂ := γ + 1) (a := 1) (b := 0)
          hm hγ hγsucc (by linarith)
  have hdegree : R.natDegree = m := by
    dsimp only [R]
    exact natDegree_exceptionalEulerInverse m ε hγpos
  have hcardRoots : R.roots.card = m := by
    rw [card_roots_of_splits hsplit, hdegree]
  have hOne : R.eval 1 ≠ 0 := by
    have hsign :=
      negOnePow_mul_exceptionalEulerInverse_eval_one_pos
        m ε hm hγ
    intro hzero
    dsimp only [R] at hzero
    rw [hzero, mul_zero] at hsign
    linarith
  have hcardInterior : m - 1 ≤
      (R.roots.filter fun x => 0 < x ∧ x < 1).card := by
    simpa [R] using
      exceptionalEulerInverse_pencil_card_roots_Ioo_ge_sub_one
        m ε (γ₁ := γ) (γ₂ := γ + 1) (a := 1) (b := 0)
          hm hγ hγsucc (by linarith) (Or.inl one_ne_zero) (by simpa using hOne)
  have hzero : R.coeff 0 = 1 := by
    rw [coeff_zero_eq_eval_zero]
    dsimp only [R]
    exact exceptionalEulerInverse_eval_zero m ε hγpos.ne'
  have hprod : 0 < R.roots.prod := by
    have hcoeff := hsplit.coeff_zero_eq_leadingCoeff_mul_prod_roots
    have hlead :=
      negOnePow_mul_exceptionalEulerInverse_leadingCoeff_pos
        m ε hγpos
    rw [hzero, hdegree] at hcoeff
    change 0 < (-1 : ℝ) ^ m * R.leadingCoeff at hlead
    nlinarith
  intro r hr
  change r ∈ R.roots at hr
  by_contra hrpos
  have hrle : r ≤ 0 := le_of_not_gt hrpos
  have hrzero : r ≠ 0 := by
    intro hr0
    subst r
    have hR : R ≠ 0 := by
      intro hRzero
      rw [hRzero] at hdegree
      simp at hdegree
      lia
    have hroot : R.IsRoot 0 := (Polynomial.mem_roots hR).mp hr
    rw [Polynomial.IsRoot.def, ← coeff_zero_eq_eval_zero, hzero] at hroot
    norm_num at hroot
  have hrneg : r < 0 := lt_of_le_of_ne hrle hrzero
  let tail := R.roots.erase r
  have hcons : r ::ₘ tail = R.roots := by
    exact Multiset.cons_erase hr
  have htailCard : tail.card = m - 1 := by
    dsimp only [tail]
    rw [Multiset.card_erase_of_mem hr, hcardRoots]
    exact Nat.pred_eq_sub_one
  have hfilterTail :
      (tail.filter fun x => 0 < x ∧ x < 1).card = tail.card := by
    have hfilterEq :
        (R.roots.filter fun x => 0 < x ∧ x < 1) =
          tail.filter fun x => 0 < x ∧ x < 1 := by
      rw [← hcons]
      simp only [Multiset.filter_cons, hrneg.not_gt, false_and,
        ↓reduceIte, zero_add]
    apply le_antisymm
    · exact Multiset.card_le_card (Multiset.filter_le _ _)
    · rw [htailCard, ← hfilterEq]
      exact hcardInterior
  have htailAll : ∀ x ∈ tail, 0 < x ∧ x < 1 := by
    exact Multiset.filter_eq_self.mp
      (Multiset.eq_of_le_of_card_le
        (Multiset.filter_le _ _) hfilterTail.ge)
  have htailProd : 0 < tail.prod := by
    apply Multiset.prod_pos
    intro x hx
    exact (htailAll x hx).1
  rw [← hcons, Multiset.prod_cons] at hprod
  nlinarith

private theorem neg_coeff_one_eq_sum_roots_inv
    {p : ℝ[X]} (hp : p.Splits) (hzero : p.coeff 0 = 1)
    (hdegree : 0 < p.natDegree) :
    -p.coeff 1 = (p.roots.map fun r => r⁻¹).sum := by
  have hzeroNe : p.coeff 0 ≠ 0 := by rw [hzero]; norm_num
  have htrail : p.natTrailingDegree = 0 :=
    Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hzeroNe)
  have hrevDegree : p.reverse.natDegree = p.natDegree := by
    rw [Polynomial.reverse_natDegree, htrail, Nat.sub_zero]
  have hrevLead : p.reverse.leadingCoeff = 1 := by
    rw [Polynomial.reverse_leadingCoeff, Polynomial.trailingCoeff,
      htrail, hzero]
  have hrevNext : p.reverse.nextCoeff = p.coeff 1 := by
    rw [Polynomial.nextCoeff, if_neg (by rw [hrevDegree]; lia),
      hrevDegree, Polynomial.coeff_reverse]
    have hindex : Polynomial.revAt p.natDegree
        (p.natDegree - 1) = 1 := by
      rw [Polynomial.revAt_le (Nat.sub_le _ _)]
      lia
    rw [hindex]
  have hroots :=
    DegreeDropReversal.roots_reverse_eq_map_inv_of_splits_coeff_zero_ne
      hp hzeroNe
  have hnext :=
    (DegreeDropReversal.splits_reverse hp).nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
  rw [hrevNext, hrevLead, hroots] at hnext
  simp only [neg_mul, one_mul] at hnext
  linarith

private theorem neg_coeff_one_le_of_prec_sameDegree_of_roots_pos
    {f g : ℝ[X]} (hprec : Prec f g)
    (hdegree : f.natDegree = g.natDegree)
    (hfzero : f.coeff 0 = 1) (hgzero : g.coeff 0 = 1)
    (hfdegree : 0 < f.natDegree)
    (hfpos : ∀ r ∈ f.roots, 0 < r)
    (hgpos : ∀ r ∈ g.roots, 0 < r) :
    -g.coeff 1 ≤ -f.coeff 1 := by
  rcases hprec with
    ⟨hf, hg, ss, rs, hssSorted, hrsSorted, hssRoots, hrsRoots, hshape⟩
  have hssLength : ss.length = f.natDegree := by
    rw [← Multiset.coe_card, hssRoots, card_roots_of_splits hf.2]
  have hrsLength : rs.length = g.natDegree := by
    rw [← Multiset.coe_card, hrsRoots, card_roots_of_splits hg.2]
  have halt : ListAlternates ss rs := by
    rcases hshape with hinter | halt
    · exfalso
      lia
    · exact halt.2
  have hcoord : List.Forall₂ (fun x y : ℝ => x ≤ y) ss rs :=
    listAlternates_forall₂_le halt
  have hssPos : ∀ x ∈ ss, 0 < x := by
    intro x hx
    apply hfpos x
    rw [← hssRoots]
    exact Multiset.mem_coe.mpr hx
  have hrsPos : ∀ x ∈ rs, 0 < x := by
    intro x hx
    apply hgpos x
    rw [← hrsRoots]
    exact Multiset.mem_coe.mpr hx
  have invSumAux : ∀ {xs ys : List ℝ},
      List.Forall₂ (fun x y : ℝ => x ≤ y) xs ys →
      (∀ x ∈ xs, 0 < x) → (∀ y ∈ ys, 0 < y) →
      (ys.map fun y => y⁻¹).sum ≤ (xs.map fun x => x⁻¹).sum := by
    intro xs ys hxy
    induction hxy with
    | nil => simp
    | @cons x y xs ys hxy htail ih =>
        intro hxs hys
        have hx : 0 < x := hxs x (by simp)
        have hxsTail : ∀ z ∈ xs, 0 < z := by
          intro z hz
          exact hxs z (by simp [hz])
        have hysTail : ∀ z ∈ ys, 0 < z := by
          intro z hz
          exact hys z (by simp [hz])
        have htailSum := ih hxsTail hysTail
        simp only [List.map_cons, List.sum_cons]
        exact add_le_add
          (by simpa only [one_div] using one_div_le_one_div_of_le hx hxy)
          htailSum
  have hsumInv : (rs.map fun x => x⁻¹).sum ≤
      (ss.map fun x => x⁻¹).sum :=
    invSumAux hcoord hssPos hrsPos
  have hssMap : (↑(ss.map fun x => x⁻¹) : Multiset ℝ) =
      f.roots.map fun x => x⁻¹ := by
    simpa using congrArg (Multiset.map fun x : ℝ => x⁻¹) hssRoots
  have hrsMap : (↑(rs.map fun x => x⁻¹) : Multiset ℝ) =
      g.roots.map fun x => x⁻¹ := by
    simpa using congrArg (Multiset.map fun x : ℝ => x⁻¹) hrsRoots
  have hsumRoots : (g.roots.map fun x => x⁻¹).sum ≤
      (f.roots.map fun x => x⁻¹).sum := by
    simpa [← Multiset.sum_coe, hssMap, hrsMap] using hsumInv
  have hfCoeff := neg_coeff_one_eq_sum_roots_inv
    hf.2 hfzero hfdegree
  have hgCoeff := neg_coeff_one_eq_sum_roots_inv
    hg.2 hgzero (by rw [← hdegree]; exact hfdegree)
  linarith

/-- The exceptional Euler-inverse family has a fully real-rooted real pencil. -/
theorem exceptionalEulerInverse_allComboRealRooted
    (m ε : ℕ) {γ₁ γ₂ : ℝ} (hm : 0 < m)
    (hγ₁ : (ε : ℝ) + 1 / 2 + m - 1 < γ₁)
    (hγ₂ : (ε : ℝ) + 1 / 2 + m - 1 < γ₂)
    (hγ : γ₁ < γ₂) :
    AllComboRealRooted
      (exceptionalEulerInverse m ε γ₁)
      (exceptionalEulerInverse m ε γ₂) := by
  intro a b
  exact exceptionalEulerInverse_pencil_splits
    m ε hm hγ₁ hγ₂ hγ

/-- Larger exceptional Euler parameter gives the left-hand root set in proper
position.  The strict reciprocal-root sum selects this orientation from the
Obreschkoff dichotomy. -/
theorem exceptionalEulerInverse_prec
    (m ε : ℕ) {γ₁ γ₂ : ℝ} (hm : 0 < m)
    (hγ₁ : (ε : ℝ) + 1 / 2 + m - 1 < γ₁)
    (hγ₂ : (ε : ℝ) + 1 / 2 + m - 1 < γ₂)
    (hγ : γ₁ < γ₂) :
    Prec (exceptionalEulerInverse m ε γ₂)
      (exceptionalEulerInverse m ε γ₁) := by
  let R₁ := exceptionalEulerInverse m ε γ₁
  let R₂ := exceptionalEulerInverse m ε γ₂
  have hmCast : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hε : 0 ≤ (ε : ℝ) := by positivity
  have hγ₁pos : 0 < γ₁ := by linarith
  have hγ₂pos : 0 < γ₂ := by linarith
  have hdeg₁ : R₁.natDegree = m := by
    dsimp only [R₁]
    exact natDegree_exceptionalEulerInverse m ε hγ₁pos
  have hdeg₂ : R₂.natDegree = m := by
    dsimp only [R₂]
    exact natDegree_exceptionalEulerInverse m ε hγ₂pos
  have hR₁ : R₁ ≠ 0 := by
    intro hzero
    rw [hzero] at hdeg₁
    simp at hdeg₁
    lia
  have hR₂ : R₂ ≠ 0 := by
    intro hzero
    rw [hzero] at hdeg₂
    simp at hdeg₂
    lia
  have hall : AllComboRealRooted R₁ R₂ := by
    simpa only [R₁, R₂] using
      exceptionalEulerInverse_allComboRealRooted
        m ε hm hγ₁ hγ₂ hγ
  have hsplit₁ : R₁.Splits := hall.left_splits
  have hsplit₂ : R₂.Splits := hall.right_splits
  have horient : Prec R₁ R₂ ∨ Prec R₂ R₁ :=
    prec_of_allComboRealRooted hR₁ hsplit₁ hR₂ hsplit₂ hall
      (Or.inr (hdeg₁.trans hdeg₂.symm))
  rcases horient with hforward | hreverse
  · have hzero₁ : R₁.coeff 0 = 1 := by
      rw [coeff_zero_eq_eval_zero]
      dsimp only [R₁]
      exact exceptionalEulerInverse_eval_zero m ε hγ₁pos.ne'
    have hzero₂ : R₂.coeff 0 = 1 := by
      rw [coeff_zero_eq_eval_zero]
      dsimp only [R₂]
      exact exceptionalEulerInverse_eval_zero m ε hγ₂pos.ne'
    have hrecipLe :=
      neg_coeff_one_le_of_prec_sameDegree_of_roots_pos
        hforward (hdeg₁.trans hdeg₂.symm) hzero₁ hzero₂
          (by rw [hdeg₁]; exact hm)
          (by
            intro r hr
            exact exceptionalEulerInverse_roots_pos
              m ε hm hγ₁ r (by simpa only [R₁] using hr))
          (by
            intro r hr
            exact exceptionalEulerInverse_roots_pos
              m ε hm hγ₂ r (by simpa only [R₂] using hr))
    have hrecipLt :=
      neg_coeff_one_exceptionalEulerInverse_strictMono
        m ε hm hγ₁pos hγ
    dsimp only [R₁, R₂] at hrecipLe
    linarith
  · exact hreverse

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

/-- The pencil between the lower distinguished parameter and any larger
parameter is real-rooted.  Approximants preserve the top two coefficients,
so the possible degree drop from `m` to `m - 1` is retained in the limit. -/
private theorem exceptionalEulerInverse_lower_allComboRealRooted
    (m ε : ℕ) (hm : 0 < m) {γ : ℝ}
    (hγ : (ε : ℝ) + 1 / 2 + m - 1 < γ) :
    AllComboRealRooted
      (exceptionalEulerInverse m ε
        ((ε : ℝ) + 1 / 2 + m - 1))
      (exceptionalEulerInverse m ε γ) := by
  let A : ℝ := (ε : ℝ) + 1 / 2 + m - 1
  let L := exceptionalEulerInverse m ε A
  let U := exceptionalEulerInverse m ε γ
  have hmCast : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hA : 0 < A := by
    dsimp only [A]
    have hε : 0 ≤ (ε : ℝ) := by positivity
    linarith
  have hγpos : 0 < γ := hA.trans hγ
  have hAγ : A ≠ γ := hγ.ne
  have hLdegree : L.natDegree = m := by
    dsimp only [L]
    exact natDegree_exceptionalEulerInverse m ε hA
  have hUdegree : U.natDegree = m := by
    dsimp only [U]
    exact natDegree_exceptionalEulerInverse m ε hγpos
  have hdetLimit :
      L.coeff m * U.coeff (m - 1) -
          U.coeff m * L.coeff (m - 1) ≠ 0 := by
    rw [sub_ne_zero]
    exact exceptionalEulerInverse_topCoeff_det_ne_zero
      m ε hm hA hγpos hAγ
  intro a b
  let Q := C a * L + C b * U
  by_cases hQ : Q = 0
  · rw [show C a * exceptionalEulerInverse m ε
          ((ε : ℝ) + 1 / 2 + m - 1) +
          C b * exceptionalEulerInverse m ε γ = Q by rfl, hQ]
    exact Polynomial.Splits.zero
  have hQlower : m - 1 ≤ Q.natDegree := by
    simpa only [Q, L, U] using
      exceptionalEulerInverse_pencil_natDegree_ge_sub_one
        m ε hm hA hγpos hAγ hQ
  have hQupper : Q.natDegree ≤ m := by
    dsimp only [Q, L, U]
    exact (Polynomial.natDegree_add_le _ _).trans
      (max_le
        ((Polynomial.natDegree_C_mul_le a _).trans
          (natDegree_exceptionalEulerInverse_le m ε A))
        ((Polynomial.natDegree_C_mul_le b _).trans
          (natDegree_exceptionalEulerInverse_le m ε γ)))
  have hQdegree : Q.natDegree = m - 1 ∨ Q.natDegree = m := by
    lia
  have hQlead : Q.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hQ
  let gap : ℝ := (γ - A) / 2
  let δ : ℕ → ℝ := fun n => gap * ((n + 1 : ℕ) : ℝ)⁻¹
  let γn : ℕ → ℝ := fun n => A + δ n
  let R : ℕ → ℝ[X] := fun n => exceptionalEulerInverse m ε (γn n)
  let D : ℕ → ℝ := fun n =>
    (R n).coeff m * U.coeff (m - 1) -
      U.coeff m * (R n).coeff (m - 1)
  have hδpos : ∀ n, 0 < δ n := by
    intro n
    dsimp only [δ, gap]
    positivity
  have hδle : ∀ n, δ n ≤ gap := by
    intro n
    dsimp only [δ]
    apply mul_le_of_le_one_right
    · dsimp only [gap]
      positivity
    · apply (inv_le_one₀ (by positivity)).2
      norm_num
  have hγnLower : ∀ n, A < γn n := by
    intro n
    dsimp only [γn]
    linarith [hδpos n]
  have hγnUpper : ∀ n, γn n < γ := by
    intro n
    calc
      γn n = A + δ n := by rfl
      _ ≤ A + gap := by linarith [hδle n]
      _ < γ := by
        dsimp only [gap, A]
        linarith
  have hγnPos : ∀ n, 0 < γn n := by
    intro n
    exact hA.trans (hγnLower n)
  have hD : ∀ n, D n ≠ 0 := by
    intro n
    dsimp only [D, R]
    rw [sub_ne_zero]
    exact exceptionalEulerInverse_topCoeff_det_ne_zero
      m ε hm (hγnPos n) hγpos (hγnUpper n).ne
  let an : ℕ → ℝ := fun n =>
    (Q.coeff m * U.coeff (m - 1) -
      U.coeff m * Q.coeff (m - 1)) / D n
  let bn : ℕ → ℝ := fun n =>
    ((R n).coeff m * Q.coeff (m - 1) -
      Q.coeff m * (R n).coeff (m - 1)) / D n
  let Qn : ℕ → ℝ[X] := fun n => C (an n) * R n + C (bn n) * U
  have hQnTop : ∀ n, (Qn n).coeff m = Q.coeff m := by
    intro n
    dsimp only [Qn, an, bn]
    simp only [coeff_add, coeff_C_mul]
    field_simp [hD n]
    ring
  have hQnPrev : ∀ n, (Qn n).coeff (m - 1) = Q.coeff (m - 1) := by
    intro n
    dsimp only [Qn, an, bn]
    simp only [coeff_add, coeff_C_mul]
    field_simp [hD n]
    ring
  have hQnDegree : ∀ n, (Qn n).natDegree = Q.natDegree := by
    intro n
    rcases hQdegree with hdrop | hfull
    · rw [hdrop]
      apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
        intro k hk
        by_cases hkm : k = m
        · subst k
          rw [hQnTop]
          exact Polynomial.coeff_eq_zero_of_natDegree_lt (by lia)
        · have hmk : m < k := by lia
          dsimp only [Qn, R, U]
          simp only [coeff_add, coeff_C_mul,
            coeff_exceptionalEulerInverse, if_neg (not_le.mpr hmk)]
          ring
      · rw [hQnPrev]
        simpa only [Polynomial.leadingCoeff, hdrop] using hQlead
    · rw [hfull]
      apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      · dsimp only [Qn, R, U]
        exact (Polynomial.natDegree_add_le _ _).trans
          (max_le
            ((Polynomial.natDegree_C_mul_le (an n) _).trans
              (natDegree_exceptionalEulerInverse_le m ε (γn n)))
            ((Polynomial.natDegree_C_mul_le (bn n) _).trans
              (natDegree_exceptionalEulerInverse_le m ε γ)))
      · rw [hQnTop]
        simpa only [Polynomial.leadingCoeff, hfull] using hQlead
  have hQnSplits : ∀ n, (Qn n).Splits := by
    intro n
    dsimp only [Qn, R, U]
    apply exceptionalEulerInverse_pencil_splits m ε hm
    · simpa only [A] using hγnLower n
    · simpa only [A] using hγ
    · exact hγnUpper n
  have hδTendsto : Filter.Tendsto δ Filter.atTop (nhds 0) := by
    have hinv : Filter.Tendsto
        (fun n : ℕ => (((n + 1 : ℕ) : ℝ))⁻¹)
        Filter.atTop (nhds 0) := by
      have heq : (fun n : ℕ => (((n + 1 : ℕ) : ℝ))⁻¹) =
          (fun n : ℕ => ((n : ℝ)⁻¹)) ∘ fun n => n + 1 := by
        funext n
        simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
      rw [heq]
      exact (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (Filter.tendsto_add_atTop_nat 1)
    simpa only [δ, mul_zero] using tendsto_const_nhds.mul hinv
  have hγnTendsto : Filter.Tendsto γn Filter.atTop (nhds A) := by
    simpa only [γn, add_zero] using tendsto_const_nhds.add hδTendsto
  have hRcoeffTendsto : ∀ k,
      Filter.Tendsto (fun n => (R n).coeff k) Filter.atTop
        (nhds (L.coeff k)) := by
    intro k
    dsimp only [R, L]
    rw [show (fun n => (exceptionalEulerInverse m ε (γn n)).coeff k) =
        fun n => if k ≤ m then
          exceptionalBaseCoeff m ε k * γn n / (γn n + k)
        else 0 by
          funext n
          rw [coeff_exceptionalEulerInverse]]
    rw [coeff_exceptionalEulerInverse]
    split_ifs
    · exact (tendsto_const_nhds.mul hγnTendsto).div
        (hγnTendsto.add tendsto_const_nhds)
        (by positivity)
    · exact tendsto_const_nhds
  have hDTendsto : Filter.Tendsto D Filter.atTop
      (nhds (L.coeff m * U.coeff (m - 1) -
        U.coeff m * L.coeff (m - 1))) := by
    dsimp only [D]
    exact ((hRcoeffTendsto m).mul_const _).sub
      (tendsto_const_nhds.mul (hRcoeffTendsto (m - 1)))
  have hanLimit :
      (Q.coeff m * U.coeff (m - 1) -
          U.coeff m * Q.coeff (m - 1)) /
          (L.coeff m * U.coeff (m - 1) -
            U.coeff m * L.coeff (m - 1)) = a := by
    apply (div_eq_iff hdetLimit).2
    dsimp only [Q]
    simp only [coeff_add, coeff_C_mul]
    ring
  have hbnLimit :
      (L.coeff m * Q.coeff (m - 1) -
          Q.coeff m * L.coeff (m - 1)) /
          (L.coeff m * U.coeff (m - 1) -
            U.coeff m * L.coeff (m - 1)) = b := by
    apply (div_eq_iff hdetLimit).2
    dsimp only [Q]
    simp only [coeff_add, coeff_C_mul]
    ring
  have hanTendsto : Filter.Tendsto an Filter.atTop (nhds a) := by
    rw [← hanLimit]
    dsimp only [an]
    exact tendsto_const_nhds.div hDTendsto hdetLimit
  have hbnTendsto : Filter.Tendsto bn Filter.atTop (nhds b) := by
    rw [← hbnLimit]
    dsimp only [bn]
    exact ((hRcoeffTendsto m).mul_const _).sub
      (tendsto_const_nhds.mul (hRcoeffTendsto (m - 1))) |>.div
        hDTendsto hdetLimit
  have hQnCoeffTendsto : ∀ k,
      Filter.Tendsto (fun n => (Qn n).coeff k) Filter.atTop
        (nhds (Q.coeff k)) := by
    intro k
    dsimp only [Qn, Q]
    simp only [coeff_add, coeff_C_mul]
    exact (hanTendsto.mul (hRcoeffTendsto k)).add
      (hbnTendsto.mul_const _)
  let q := C Q.leadingCoeff⁻¹ * Q
  let qn : ℕ → ℝ[X] := fun n => C Q.leadingCoeff⁻¹ * Qn n
  have hqMonic : q.Monic := by
    dsimp only [q]
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    exact inv_mul_cancel₀ hQlead
  have hqnMonic : ∀ n, (qn n).Monic := by
    intro n
    dsimp only [qn]
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    rw [show (Qn n).leadingCoeff = Q.leadingCoeff by
      simp only [Polynomial.leadingCoeff, hQnDegree n]
      rcases hQdegree with hdrop | hfull
      · rw [hdrop, hQnPrev]
      · rw [hfull, hQnTop]]
    exact inv_mul_cancel₀ hQlead
  have hqnDegree : ∀ n, (qn n).natDegree = q.natDegree := by
    intro n
    dsimp only [qn, q]
    rw [Polynomial.natDegree_C_mul (inv_ne_zero hQlead),
      Polynomial.natDegree_C_mul (inv_ne_zero hQlead), hQnDegree]
  have hqnSplits : ∀ n, (qn n).Splits := by
    intro n
    exact (hQnSplits n).C_mul Q.leadingCoeff⁻¹
  have hqnCoeffTendsto : ∀ k,
      Filter.Tendsto (fun n => (qn n).coeff k) Filter.atTop
        (nhds (q.coeff k)) := by
    intro k
    dsimp only [qn, q]
    simp only [coeff_C_mul]
    exact tendsto_const_nhds.mul (hQnCoeffTendsto k)
  have hqSplits := splits_of_monic_of_coeff_tendsto
    hqMonic hqnMonic hqnDegree hqnSplits hqnCoeffTendsto
  have hscaled := hqSplits.C_mul Q.leadingCoeff
  rw [show C Q.leadingCoeff * q = Q by
    dsimp only [q]
    rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hQlead, C_1, one_mul]] at hscaled
  simpa only [Q, L, U, A] using hscaled

/-- The upper distinguished exceptional polynomial is in proper position
before the lower endpoint polynomial. -/
theorem exceptionalEulerInverse_upper_prec_lower
    (m ε : ℕ) (hm : 0 < m) :
    Prec
      (exceptionalEulerInverse m ε
        ((ε : ℝ) + 1 / 2 + m + 1 / 2))
      (exceptionalEulerInverse m ε
        ((ε : ℝ) + 1 / 2 + m - 1)) := by
  let A : ℝ := (ε : ℝ) + 1 / 2 + m - 1
  let B : ℝ := (ε : ℝ) + 1 / 2 + m + 1 / 2
  let L := exceptionalEulerInverse m ε A
  let U := exceptionalEulerInverse m ε B
  have hmCast : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hA : 0 < A := by
    dsimp only [A]
    have hε : 0 ≤ (ε : ℝ) := by positivity
    linarith
  have hB : 0 < B := by
    dsimp only [B]
    positivity
  have hAB : A < B := by
    dsimp only [A, B]
    linarith
  have hLdegree : L.natDegree = m := by
    dsimp only [L]
    exact natDegree_exceptionalEulerInverse m ε hA
  have hUdegree : U.natDegree = m := by
    dsimp only [U]
    exact natDegree_exceptionalEulerInverse m ε hB
  have hL : L ≠ 0 := by
    intro hzero
    rw [hzero] at hLdegree
    simp at hLdegree
    lia
  have hU : U ≠ 0 := by
    intro hzero
    rw [hzero] at hUdegree
    simp at hUdegree
    lia
  have hall : AllComboRealRooted L U := by
    simpa only [L, U, A, B] using
      exceptionalEulerInverse_lower_allComboRealRooted
        m ε hm (γ := B) (by dsimp only [B]; linarith)
  have horient : Prec L U ∨ Prec U L :=
    prec_of_allComboRealRooted hL hall.left_splits hU hall.right_splits
      hall (Or.inr (hLdegree.trans hUdegree.symm))
  rcases horient with hwrong | hright
  · have hLzero : L.coeff 0 = 1 := by
      rw [coeff_zero_eq_eval_zero]
      dsimp only [L]
      exact exceptionalEulerInverse_eval_zero m ε hA.ne'
    have hUzero : U.coeff 0 = 1 := by
      rw [coeff_zero_eq_eval_zero]
      dsimp only [U]
      exact exceptionalEulerInverse_eval_zero m ε hB.ne'
    have hwrongCoeff :=
      neg_coeff_one_le_of_prec_sameDegree_of_roots_pos
        hwrong (hLdegree.trans hUdegree.symm) hLzero hUzero
          (by rw [hLdegree]; exact hm)
          (by
            intro r hr
            rw [show L = rPolynomial m ε (m - 1) by
              simpa only [L, A] using
                exceptionalEulerInverse_lower_eq_rPolynomial m ε hm] at hr
            exact (rPolynomial_rightClosedIntervalRootData
              m ε (m - 1) hm (by lia)).roots_mem_Ioc r hr |>.1)
          (by
            intro r hr
            exact exceptionalEulerInverse_roots_pos
              m ε hm (by simpa only [A, B] using hAB) r
                (by simpa only [U] using hr))
    have hstrict := neg_coeff_one_exceptionalEulerInverse_strictMono
      m ε hm hA hAB
    dsimp only [L, U, A, B] at hwrongCoeff
    linarith
  · simpa only [U, L, B, A] using hright

/-- The two exceptional toric-contribution polynomials have the required
weak proper-position orientation. -/
theorem rPolynomial_exceptional_prec (m ε : ℕ) (hm : 0 < m) :
    Prec (rPolynomial m ε m) (rPolynomial m ε (m - 1)) := by
  rw [← exceptionalEulerInverse_upper_eq_rPolynomial m ε,
    ← exceptionalEulerInverse_lower_eq_rPolynomial m ε hm]
  exact exceptionalEulerInverse_upper_prec_lower m ε hm

end ToricContribution
end ParkingFunctions
end RealRooted
