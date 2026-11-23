module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.Mathlib.Analysis.Analytic.TaylorSeries
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Star
import RealRooted.Mathlib.Analysis.Complex.LinearProduct
import RealRooted.Mathlib.Analysis.Complex.PolynomialLimitCoeff
import RealRooted.Mathlib.Algebra.Polynomial.LinearFactors
import RealRooted.Mathlib.RingTheory.PowerSeries.NewtonSums
import RealRooted.Mathlib.RingTheory.PowerSeries.LogarithmPositive
import Mathlib.Analysis.Asymptotics.Lemmas
import TauCeti.Analysis.SpecialFunctions.Complex.Exp.LogDeriv

/-!
# Logarithmic derivative coefficients as power sums

For a convergent linear product, the signed Taylor coefficients of its
logarithmic derivative are the power sums of the slopes. The proof passes
from finite products through coefficientwise continuity of the formal
logarithm, then identifies the analytic logarithmic derivative.
-/

public section

open Complex Polynomial Filter Topology

namespace RealRooted

/-- Signed logarithmic coefficients of a finite linear product are power sums. -/
private theorem signed_coeff_logOf_linear_product (s : Finset ℕ) (a : ℕ → ℝ)
    {k : ℕ} (hk : k ≠ 0) :
    (-1 : ℝ) ^ (k + 1) * k * PowerSeries.coeff k
      (PowerSeries.logOf (∏ i ∈ s, (1 + PowerSeries.C (a i) * PowerSeries.X))) =
        ∑ i ∈ s, a i ^ k := by
  have h := PowerSeries.coeff_neg_logOf_prod_one_sub_C_mul_X s (fun i => -a i) hk
  simp only [map_neg, neg_mul, sub_neg_eq_add] at h
  have hsum : (∑ i ∈ s, (-a i) ^ k) = (-1 : ℝ) ^ k * ∑ i ∈ s, a i ^ k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact neg_pow (a i) k
  rw [hsum] at h
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have heq := (eq_div_iff hkR).mp h
  have hsign : (-1 : ℝ) ^ k * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
  rw [pow_succ]
  calc
    _ = (-1 : ℝ) ^ k *
        (-PowerSeries.coeff k (PowerSeries.logOf
          (∏ i ∈ s, (1 + PowerSeries.C (a i) * PowerSeries.X))) * k) := by ring
    _ = (-1 : ℝ) ^ k * ((-1 : ℝ) ^ k * ∑ i ∈ s, a i ^ k) := by rw [heq]
    _ = _ := by rw [← mul_assoc, hsign, one_mul]

/-- Real linear partial products converge as real polynomial approximants. -/
private theorem tendsto_linear_polynomials (a : ℕ → ℝ) (hs : Summable a) :
    TendstoLocallyUniformly (fun n z =>
      ((∏ i ∈ Finset.range n, (1 + C (a i) * X : ℝ[X])).map ofRealHom).eval z)
      (fun z => ∏' i, (1 + (a i : ℂ) * z)) atTop := by
  simpa only [Polynomial.map_prod, Polynomial.map_add, Polynomial.map_one,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, Polynomial.eval_prod,
    Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, ofRealHom_eq_coe] using
    Complex.tendstoLocallyUniformly_prod_one_add a hs

/-- A summable real linear product is an LP function, without sign restrictions on the slopes. -/
private theorem isLaguerrePolya_linear_product (a : ℕ → ℝ) (hs : Summable a) :
    IsLaguerrePolya (fun z => ∏' i, (1 + (a i : ℂ) * z)) :=
  ⟨fun n => ∏ i ∈ Finset.range n, (1 + C (a i) * X),
    fun n => Or.inr (splits_prod_one_add_C_mul_X (Finset.range n) a),
    tendsto_linear_polynomials a hs⟩

/-- Formal logarithmic coefficients of an infinite linear product are power sums. -/
private theorem signed_coeff_logOf_linear_tprod (a : ℕ → ℝ) (hs : Summable a)
    (k : ℕ) :
    (-1 : ℝ) ^ (k + 1 + 1) * ((k + 1 : ℕ) : ℝ) * PowerSeries.coeff (k + 1)
      (PowerSeries.logOf (PowerSeries.mk (fun j =>
        (iteratedDeriv j (fun z => ∏' i, (1 + (a i : ℂ) * z)) 0).re / j.factorial))) =
          ∑' i, a i ^ (k + 1) := by
  let p : ℕ → ℝ[X] := fun n => ∏ i ∈ Finset.range n, (1 + C (a i) * X)
  let b : PowerSeries ℝ := PowerSeries.mk (fun j =>
    (iteratedDeriv j (fun z => ∏' i, (1 + (a i : ℂ) * z)) 0).re / j.factorial)
  have hp0 (n : ℕ) : PowerSeries.constantCoeff (p n : PowerSeries ℝ) = 1 := by
    simp [p, coeff_zero_eq_eval_zero, eval_prod]
  have hb0 : PowerSeries.constantCoeff b = 1 := by simp [b]
  have hcoeff (j : ℕ) : Tendsto
      (fun n => PowerSeries.coeff j (p n : PowerSeries ℝ)) atTop
      (𝓝 (PowerSeries.coeff j b)) := by
    simpa only [p, b, PowerSeries.coeff_mk, Polynomial.coeff_coe, div_natCast_re] using
      Polynomial.tendsto_coeff_of_tendstoLocallyUniformly (tendsto_linear_polynomials a hs) j
  have hlim := (PowerSeries.tendsto_coeff_logOf_of_coeff_tendsto hp0 hb0 hcoeff
    (k + 1)).const_mul ((-1 : ℝ) ^ (k + 1 + 1) * ((k + 1 : ℕ) : ℝ))
  have hfinite (n : ℕ) :
      (-1 : ℝ) ^ (k + 1 + 1) * ((k + 1 : ℕ) : ℝ) *
        PowerSeries.coeff (k + 1) (PowerSeries.logOf (p n : PowerSeries ℝ)) =
          ∑ i ∈ Finset.range n, a i ^ (k + 1) := by
    dsimp only [p]
    rw [coe_prod_one_add_C_mul_X]
    exact signed_coeff_logOf_linear_product _ a (Nat.succ_ne_zero k)
  simp_rw [hfinite] at hlim
  have hsum : Summable (fun i => a i ^ (k + 1)) := by
    simpa only [pow_succ, mul_comm] using
      hs.norm.mul_tendsto_const (hs.tendsto_cofinite_zero.pow k)
  exact tendsto_nhds_unique hlim hsum.hasSum.tendsto_sum_nat

/-- The signed analytic logarithmic-derivative coefficients of a summable
real linear product are exactly its positive-index power sums. -/
theorem signed_logDeriv_linear_product (a : ℕ → ℝ) (hs : Summable a) (k : ℕ) :
    (-1 : ℝ) ^ k *
      (iteratedDeriv k (logDeriv (fun z => ∏' i, (1 + (a i : ℂ) * z))) 0).re /
        k.factorial = ∑' i, a i ^ (k + 1) := by
  let f : ℂ → ℂ := fun z => ∏' i, (1 + (a i : ℂ) * z)
  have hf := isLaguerrePolya_linear_product a hs
  have hreal (j : ℕ) : ((iteratedDeriv j f 0).re : ℂ) = iteratedDeriv j f 0 :=
    ofReal_re_iteratedDeriv_zero hf.conj j
  have h := AnalyticAt.re_iteratedDeriv_logDeriv_eq_coeff_logOf
    (hf.differentiable.analyticAt 0) (by simp) hreal k
  have hm := signed_coeff_logOf_linear_tprod a hs k
  change (-1 : ℝ) ^ k * (iteratedDeriv k (logDeriv f) 0).re / k.factorial = _
  rw [mul_div_assoc, h]
  simp only [mul_zero, add_zero, tprod_one, one_re, mul_one]
  rw [Nat.cast_add, Nat.cast_one,
    show k + 1 + 1 = k + 2 by lia, pow_add] at hm
  convert hm using 1
  ring


/-- A nonzero constant and a real exponential add only the constant moment
to the signed logarithmic-derivative power sums. The constant may be complex. -/
theorem signed_logDeriv_exp_linear_product {c : ℂ} (hc : c ≠ 0)
    (gamma : ℝ) (a : ℕ → ℝ) (hs : Summable a) (k : ℕ) :
    (-1 : ℝ) ^ k * (iteratedDeriv k (logDeriv (fun z =>
      c * exp ((gamma : ℂ) * z) * ∏' i, (1 + (a i : ℂ) * z))) 0).re / k.factorial =
        gamma * 0 ^ k + ∑' i, a i ^ (k + 1) := by
  let P : ℂ → ℂ := fun z => ∏' i, (1 + (a i : ℂ) * z)
  have hd : Differentiable ℂ P := (isLaguerrePolya_linear_product a hs).differentiable
  have hP0 : P 0 ≠ 0 := by simp [P]
  have heq : logDeriv (fun z => c * exp ((gamma : ℂ) * z) * P z) =ᶠ[𝓝 0]
      (fun z => (gamma : ℂ) + logDeriv P z) := by
    filter_upwards [hd.continuous.continuousAt.eventually_ne hP0] with z hz
    rw [show (fun w => c * exp ((gamma : ℂ) * w) * P w) =
      (fun w => c * (exp ((gamma : ℂ) * w) * P w)) by funext w; ring]
    rw [logDeriv_const_mul _ _ hc,
      TauCeti.logDeriv_cexp_mul hz (hd z) (by fun_prop), deriv_const_mul_id]
  have hder := heq.iteratedDeriv_eq k
  have hm := signed_logDeriv_linear_product a hs k
  change (-1 : ℝ) ^ k *
    (iteratedDeriv k (logDeriv (fun z => c * exp ((gamma : ℂ) * z) * P z)) 0).re /
      k.factorial = _
  rw [hder]
  cases k with
  | zero =>
      simp only [iteratedDeriv_zero, pow_zero, one_mul, Nat.factorial_zero,
        Nat.cast_one, div_one, mul_one, add_re, ofReal_re]
      simpa only [iteratedDeriv_zero, pow_zero, one_mul, Nat.factorial_zero,
        Nat.cast_one, div_one, P] using congrArg (fun x : ℝ => gamma + x) hm
  | succ k =>
      rw [iteratedDeriv_const_add (Nat.succ_pos k)]
      simpa only [zero_pow (Nat.succ_ne_zero k), mul_zero, zero_add, P] using hm

end RealRooted
