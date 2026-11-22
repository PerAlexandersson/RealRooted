module

public import RealRooted.EulerOperator.ArithmeticProduct
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import RealRooted.EulerOperator.ArithmeticNormalization
import RealRooted.Mathlib.Algebra.Polynomial.Degree.Lemmas
import RealRooted.PFPolynomial.Closure
import RealRooted.Mathlib.Topology.Algebra.Polynomial

/-!
# Exponential generating sections of PF polynomials

For a nonzero stride `r`, the exponential section takes the raw exponential
coefficients `b_n` to `b_(r*k)`. Finite polar Euler approximants converge
coefficientwise to this section and preserve its real nonpositive roots.
The zero-stride value of the polynomial operator is defined to be zero.
-/

@[expose] public section

open Polynomial Filter Topology

namespace RealRooted

/-- The arithmetic section of exponential generating coefficients, with the
zero polynomial as the zero-stride convention. -/
noncomputable def exponentialSection (r : ℕ) (p : ℝ[X]) : ℝ[X] :=
  if r = 0 then 0 else
    diagonalOperator (fun k => ((r * k).factorial : ℝ) / k.factorial) (contract r p)

/-- The normalized finite polar approximation to an exponential section. -/
noncomputable def arithmeticSectionApprox (r M : ℕ) (p : ℝ[X]) : ℝ[X] :=
  C ((arithmeticPolarMultiplier r (r * M) 0)⁻¹) *
    (contract r (polarThetaProduct (arithmeticPolarParameters r (r * M))
      (p.comp (-X)))).comp (C (-((r : ℝ) ^ r * (M : ℝ) ^ (r - 1))) * X)

theorem coeff_exponentialSection {r : ℕ} (hr : r ≠ 0) (p : ℝ[X]) (k : ℕ) :
    (exponentialSection r p).coeff k =
      ((r * k).factorial : ℝ) / k.factorial * p.coeff (r * k) := by
  simp [exponentialSection, hr, coeff_contract, Nat.mul_comm k r]

theorem coeff_arithmeticSectionApprox {r : ℕ} (hr : r ≠ 0) (M : ℕ) (p : ℝ[X]) (k : ℕ) :
    (arithmeticSectionApprox r M p).coeff k = p.coeff (r * k) *
      ((-1 : ℝ) ^ (r * k + k) *
        (arithmeticPolarMultiplier r (r * M) (r * k) /
          arithmeticPolarMultiplier r (r * M) 0) *
        ((r : ℝ) ^ r * (M : ℝ) ^ (r - 1)) ^ k) := by
  simp only [arithmeticSectionApprox, coeff_C_mul, comp_C_mul_X_coeff,
    coeff_contract hr, coeff_arithmetic_polarThetaProduct, coeff_comp_neg_X,
    Nat.mul_comm k r]
  rw [show (-((r : ℝ) ^ r * (M : ℝ) ^ (r - 1))) ^ k =
    (-1 : ℝ) ^ k * ((r : ℝ) ^ r * (M : ℝ) ^ (r - 1)) ^ k from neg_pow _ _, pow_add]
  ring

/-- The finite approximants converge coefficientwise to the exponential section. -/
theorem tendsto_coeff_arithmeticSectionApprox {r : ℕ} (hr : r ≠ 0)
    (p : ℝ[X]) (k : ℕ) :
    Tendsto (fun M => (arithmeticSectionApprox r M p).coeff k) atTop
      (𝓝 ((exponentialSection r p).coeff k)) := by
  simpa only [coeff_arithmeticSectionApprox hr, coeff_exponentialSection hr, mul_comm]
    using (tendsto_arithmeticPolarMultiplier_normalized hr k).const_mul (p.coeff (r * k))

/-- Once the cutoff exceeds the input degree, the approximants have nonnegative coefficients. -/
theorem HasNonnegCoeffs.arithmeticSectionApprox {p : ℝ[X]} (hp : HasNonnegCoeffs p)
    {r M : ℕ} (hr : r ≠ 0) (hM : M ≠ 0) (hdeg : p.natDegree ≤ M) :
    HasNonnegCoeffs (RealRooted.arithmeticSectionApprox r M p) := by
  intro k
  rw [coeff_arithmeticSectionApprox hr]
  by_cases hk : k ≤ M
  · rw [arithmeticPolarMultiplier_normalized hr hM hk]
    exact mul_nonneg (hp _) (by positivity)
  · have hpzero : p.coeff (r * k) = 0 := coeff_eq_zero_of_natDegree_lt
      ((hdeg.trans_lt (Nat.lt_of_not_ge hk)).trans_le
        (Nat.le_mul_of_pos_left k (Nat.pos_of_ne_zero hr)))
    rw [hpzero, zero_mul]

/-- Every sufficiently large finite arithmetic approximant of a PF polynomial
nonzero at zero is PF. -/
theorem IsPFPolynomial.arithmeticSectionApprox {p : ℝ[X]} (hp : IsPFPolynomial p)
    (h0 : p.coeff 0 ≠ 0) {r M : ℕ} (hr : r ≠ 0) (hM : M ≠ 0)
    (hdeg : p.natDegree ≤ M) :
    IsPFPolynomial (RealRooted.arithmeticSectionApprox r M p) := by
  apply IsPFPolynomial.of_realRooted_nonneg
    (hp.hasNonnegCoeffs.arithmeticSectionApprox hr hM hdeg)
  exact ((hp.contract_arithmetic_polarThetaProduct_splits h0 hr
    (hdeg.trans (Nat.le_mul_of_pos_left M (Nat.pos_of_ne_zero hr)))).comp_of_degree_le_one
      (degree_C_mul_X_le _)).C_mul _

/-- Arithmetic sections of raw exponential coefficients preserve PF
polynomials with nonzero constant coefficient (Pólya, 1929, §4(b)). -/
private theorem IsPFPolynomial.exponentialSection_of_coeff_zero_ne_zero {p : ℝ[X]}
    (hp : IsPFPolynomial p) (h0 : p.coeff 0 ≠ 0) {r : ℕ} (hr : r ≠ 0) :
    IsPFPolynomial (exponentialSection r p) := by
  let M : ℕ → ℕ := fun n => n + p.natDegree + 1
  have hM : Tendsto M atTop atTop := tendsto_atTop.mpr fun k =>
    (eventually_ge_atTop k).mono fun n hn => by dsimp [M]; lia
  apply IsPFPolynomial.of_coeff_tendsto
    (p := fun n => RealRooted.arithmeticSectionApprox r (M n) p)
    (fun n => hp.arithmeticSectionApprox h0 hr (by dsimp [M]; lia) (by dsimp [M]; lia))
  intro k
  exact (tendsto_coeff_arithmeticSectionApprox hr p k).comp hM

/-- Arithmetic subsequences of exponential generating coefficients preserve
PF polynomials (Pólya, 1929, §4(b)). Zero polynomials and roots at zero are
included; the zero-stride value uses the stated zero-polynomial convention. -/
theorem IsPFPolynomial.exponentialSection {p : ℝ[X]} (hp : IsPFPolynomial p) (r : ℕ) :
    IsPFPolynomial (RealRooted.exponentialSection r p) := by
  by_cases hr : r = 0
  · simpa [RealRooted.exponentialSection, hr] using IsPFPolynomial.zero
  by_cases hp0 : p = 0
  · simpa [RealRooted.exponentialSection, hr, hp0, contract] using IsPFPolynomial.zero
  have hc : IsClosed {t : ℝ | IsPFPolynomial
      (RealRooted.exponentialSection r (p.comp (X + C t)))} :=
    isClosed_isPFPolynomial _ fun k => by
      simpa only [coeff_exponentialSection hr] using
        (p.continuous_coeff_comp_X_add_C (r * k)).const_mul
          (((r * k).factorial : ℝ) / k.factorial)
  have hmem : Set.Ioi (0 : ℝ) ⊆ {t : ℝ | IsPFPolynomial
      (RealRooted.exponentialSection r (p.comp (X + C t)))} := by
    intro t ht
    have hp' : IsPFPolynomial (p.comp (X + C t)) := by
      simpa using hp.comp_C_mul_X_add_C (a := 1) (by norm_num) (le_of_lt ht)
    apply hp'.exponentialSection_of_coeff_zero_ne_zero _ hr
    rw [coeff_zero_eq_eval_zero, eval_comp]
    simpa only [eval_add, eval_X, eval_C, zero_add] using
      (eval_pos_of_hasNonnegCoeffs hp.hasNonnegCoeffs hp0 ht).ne'
  have hlimit := closure_minimal hmem hc (show (0 : ℝ) ∈ closure (Set.Ioi 0) by simp)
  simpa only [Set.mem_ofPred_eq, map_zero, add_zero, comp_X] using hlimit

end RealRooted
