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
