import RealRooted.GeneralizedEulerian
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# The generating function of the Eulerian polynomials

Write `E_k = generalizedEulerian 1 k` (the classical Eulerian polynomial
`A_{k+1}` divided by `x`, of degree `k`, with `E_0 = 1`).  Then

```text
sum_{m ≥ 0} m^(k+1) q^m · (1 - q)^(k+2) = q · E_k(q).
```

The identity is proved twice:

* as an identity of formal power series (`eulerianPowerSumSeries_mul_one_sub_X_pow`),
  from which the explicit alternating-sum formula for the coefficients of `E_k`
  follows (`coeff_generalizedEulerian_one_eq_sum`);
* analytically for complex `q` with `‖q‖ < 1`
  (`eulerianPowerSum_mul_one_sub_pow`), via term-by-term differentiation.

Both inductions close on the defining recurrence `generalizedEulerian_succ`:
differentiating `q E_k(q) (1 - q)^(-(k+2))` and multiplying by `q` produces
exactly `q E_{k+1}(q) (1 - q)^(-(k+3))`.

Ported from `real-rooted-oeis-proofs` (`EulerianPowerSeries`, `EulerianGenFun`).
-/

open scoped Polynomial

noncomputable section

namespace RealRooted
namespace GeneralizedEulerian

/-! ### Formal power series -/

section Formal

open PowerSeries

/-- The formal power series `sum_m m^k X^m`. -/
def eulerianPowerSumSeries (k : ℕ) : PowerSeries ℝ :=
  PowerSeries.mk fun m : ℕ => (m : ℝ) ^ k

@[simp] theorem coeff_eulerianPowerSumSeries (k m : ℕ) :
    PowerSeries.coeff m (eulerianPowerSumSeries k) = (m : ℝ) ^ k := by
  simp [eulerianPowerSumSeries]

/-- The Euler operator `X d/dX` raises the exponent. -/
theorem X_mul_derivative_eulerianPowerSumSeries (k : ℕ) :
    (PowerSeries.X : PowerSeries ℝ) * d⁄dX (eulerianPowerSumSeries k) =
      eulerianPowerSumSeries (k + 1) := by
  ext m
  cases m with
  | zero => simp [eulerianPowerSumSeries, derivative]
  | succ j =>
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
      simp [eulerianPowerSumSeries]
      ring

private theorem derivative_one_sub_X_pow (n : ℕ) :
    d⁄dX ((1 - PowerSeries.X) ^ n) =
      -(n : PowerSeries ℝ) * (1 - PowerSeries.X) ^ (n - 1) := by
  rw [derivative_pow]
  have h1 : d⁄dX (1 : PowerSeries ℝ) = 0 := by simp
  have h : d⁄dX (1 - PowerSeries.X : PowerSeries ℝ) = -1 := by
    rw [map_sub, derivative_X, h1]
    ring
  rw [h]
  ring

private theorem derivative_coe_generalizedEulerian (k : ℕ) :
    d⁄dX ((generalizedEulerian 1 k : ℝ[X]) : PowerSeries ℝ) =
      (((generalizedEulerian 1 k).derivative : ℝ[X]) : PowerSeries ℝ) := by
  rw [derivative_coe]

/-- The Eulerian recurrence, as an identity of power series. -/
theorem coe_generalizedEulerian_one_succ (k : ℕ) :
    ((generalizedEulerian 1 (k + 1) : ℝ[X]) : PowerSeries ℝ) =
      (1 + PowerSeries.C ((k : ℝ) + 1) * PowerSeries.X) *
          ((generalizedEulerian 1 k : ℝ[X]) : PowerSeries ℝ) +
        PowerSeries.X * (1 - PowerSeries.X) *
          d⁄dX ((generalizedEulerian 1 k : ℝ[X]) : PowerSeries ℝ) := by
  rw [generalizedEulerian_succ, derivative_coe_generalizedEulerian]
  push_cast
  rw [show ((1 : ℝ) * (k : ℝ) + 1) = ((k : ℝ) + 1) by ring]
  simp only [map_one, one_mul]

private theorem eulerianPowerSumSeries_one_mul :
    eulerianPowerSumSeries 1 * (1 - PowerSeries.X) ^ 2 = (PowerSeries.X : PowerSeries ℝ) := by
  have hrw : eulerianPowerSumSeries 1 * (1 - PowerSeries.X) ^ 2 =
      eulerianPowerSumSeries 1 - PowerSeries.X * eulerianPowerSumSeries 1 -
        (PowerSeries.X * eulerianPowerSumSeries 1 -
          PowerSeries.X * (PowerSeries.X * eulerianPowerSumSeries 1)) := by ring
  rw [hrw]
  ext m
  cases m with
  | zero => simp [eulerianPowerSumSeries]
  | succ j =>
      cases j with
      | zero => simp [eulerianPowerSumSeries]
      | succ i =>
          simp only [map_sub, PowerSeries.coeff_succ_X_mul, coeff_eulerianPowerSumSeries,
            PowerSeries.coeff_X]
          norm_num

/-- **The Eulerian generating function, formally.**
`(sum_m m^(k+1) X^m) (1 - X)^(k+2) = X E_k(X)`. -/
theorem eulerianPowerSumSeries_mul_one_sub_X_pow : ∀ k : ℕ,
    eulerianPowerSumSeries (k + 1) * (1 - PowerSeries.X) ^ (k + 2) =
      PowerSeries.X * ((generalizedEulerian 1 k : ℝ[X]) : PowerSeries ℝ) := by
  intro k
  induction k with
  | zero => simpa [generalizedEulerian] using eulerianPowerSumSeries_one_mul
  | succ k ih =>
      have hd : d⁄dX (eulerianPowerSumSeries (k + 1) * (1 - PowerSeries.X) ^ (k + 2)) =
          d⁄dX (PowerSeries.X * ((generalizedEulerian 1 k : ℝ[X]) : PowerSeries ℝ)) := by
        rw [ih]
      rw [Derivation.leibniz, Derivation.leibniz, derivative_one_sub_X_pow,
        derivative_X] at hd
      simp only [smul_eq_mul, mul_one] at hd
      rw [show k + 2 - 1 = k + 1 from rfl] at hd
      have hstep := X_mul_derivative_eulerianPowerSumSeries (k + 1)
      have hc2 : ((k + 2 : ℕ) : PowerSeries ℝ) = PowerSeries.C (k : ℝ) + 2 := by
        push_cast
        simp
      have hc1 : PowerSeries.C ((k : ℝ) + 1) = PowerSeries.C (k : ℝ) + 1 := by
        rw [map_add, map_one]
      rw [hc2] at hd
      rw [coe_generalizedEulerian_one_succ, hc1]
      linear_combination (PowerSeries.X * (1 - PowerSeries.X)) * hd +
        ((PowerSeries.C (k : ℝ) + 2) * PowerSeries.X) * ih -
          ((1 - PowerSeries.X) ^ (k + 3)) * hstep

private theorem coeff_one_sub_X_pow (n m : ℕ) :
    PowerSeries.coeff m ((1 - PowerSeries.X : PowerSeries ℝ) ^ n) =
      (-1 : ℝ) ^ m * (n.choose m : ℝ) := by
  have h : (1 - PowerSeries.X : PowerSeries ℝ) = (-PowerSeries.X) + 1 := by ring
  rw [h, add_pow, map_sum]
  have hterm : ∀ i ∈ Finset.range (n + 1),
      PowerSeries.coeff m ((-PowerSeries.X : PowerSeries ℝ) ^ i * 1 ^ (n - i) *
          (n.choose i : PowerSeries ℝ)) =
        if i = m then (-1 : ℝ) ^ m * (n.choose m : ℝ) else 0 := by
    intro i _
    have hpow : ((-PowerSeries.X : PowerSeries ℝ)) ^ i =
        (PowerSeries.C ((-1 : ℝ) ^ i)) * PowerSeries.X ^ i := by
      rw [neg_pow]
      congr 1
      rw [map_pow]
      simp
    rw [hpow, one_pow, mul_one]
    rw [show (n.choose i : PowerSeries ℝ) = PowerSeries.C ((n.choose i : ℝ)) by simp]
    rw [mul_comm (PowerSeries.C ((-1 : ℝ) ^ i) * PowerSeries.X ^ i),
      ← mul_assoc, ← map_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
    by_cases hi : i = m
    · subst hi; simp [mul_comm]
    · simp [hi, Ne.symm hi]
  rw [Finset.sum_congr rfl hterm]
  by_cases hm : m ≤ n
  · rw [Finset.sum_ite_eq' (Finset.range (n + 1)) m]
    simp [Nat.lt_succ_of_le hm]
  · have hz : (n.choose m : ℝ) = 0 := by
      rw [Nat.choose_eq_zero_of_lt (by lia)]
      simp
    rw [Finset.sum_ite_eq' (Finset.range (n + 1)) m]
    simp [hz, hm]

/-- **Explicit coefficients of the Eulerian polynomials.**  The formal
counterpart of `A(n, j) = sum_i (-1)^i C(n+1, i) (j+1-i)^n`. -/
theorem coeff_generalizedEulerian_one_eq_sum (k j : ℕ) :
    (generalizedEulerian 1 k).coeff j =
      ∑ i ∈ Finset.range (j + 2),
        (i : ℝ) ^ (k + 1) * ((-1 : ℝ) ^ (j + 1 - i) * (((k + 2).choose (j + 1 - i) : ℝ))) := by
  have h := congrArg (PowerSeries.coeff (j + 1)) (eulerianPowerSumSeries_mul_one_sub_X_pow k)
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_succ_X_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Polynomial.coeff_coe] at h
  rw [← h]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [coeff_eulerianPowerSumSeries, coeff_one_sub_X_pow]

end Formal

/-! ### The analytic generating function -/

section Analytic

open Polynomial Complex

/-- The Eulerian polynomial with complex coefficients. -/
private def complexEulerian (k : ℕ) : ℂ[X] := (generalizedEulerian 1 k).map (algebraMap ℝ ℂ)

private theorem complexEulerian_succ (k : ℕ) :
    complexEulerian (k + 1) =
      (1 + C ((k : ℂ) + 1) * X) * complexEulerian k +
        X * (1 - X) * (complexEulerian k).derivative := by
  unfold complexEulerian
  rw [generalizedEulerian_succ]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_one,
    Polynomial.map_X, Polynomial.map_C, Polynomial.derivative_map]
  norm_num

/-- The power sum `sum' m, m^k q^m`, convergent for `‖q‖ < 1`. -/
def eulerianPowerSum (k : ℕ) (q : ℂ) : ℂ := ∑' m : ℕ, (m : ℂ) ^ k * q ^ m

theorem summable_eulerianPowerSum_terms (k : ℕ) {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun m : ℕ => (m : ℂ) ^ k * q ^ m) :=
  summable_pow_mul_geometric_of_norm_lt_one k hq

private theorem hasDerivAt_term (k m : ℕ) (q : ℂ) :
    HasDerivAt (fun z : ℂ => (m : ℂ) ^ k * z ^ m) ((m : ℂ) ^ (k + 1) * q ^ (m - 1)) q := by
  have h := (hasDerivAt_pow m q).const_mul ((m : ℂ) ^ k)
  have hval : (m : ℂ) ^ k * ((m : ℂ) * q ^ (m - 1)) = (m : ℂ) ^ (k + 1) * q ^ (m - 1) := by
    rw [pow_succ]; ring
  rwa [hval] at h

private theorem summable_bound (k : ℕ) {r : ℝ} (hr0 : 0 < r) (hr : r < 1) :
    Summable (fun m : ℕ => (m : ℝ) ^ (k + 1) * r ^ (m - 1)) := by
  have hs : Summable (fun m : ℕ => (m : ℝ) ^ (k + 1) * r ^ m) :=
    summable_pow_mul_geometric_of_norm_lt_one (k + 1)
      (by rwa [Real.norm_eq_abs, abs_of_pos hr0])
  refine (hs.mul_left r⁻¹).congr ?_
  intro m
  match m with
  | 0 => simp
  | (j + 1) =>
      simp only [Nat.add_sub_cancel]
      rw [pow_succ]
      field_simp
      ring

/-- Term-by-term differentiation of the power sum on any disc of radius `r < 1`. -/
theorem hasDerivAt_eulerianPowerSum (k : ℕ) {r : ℝ} (hr0 : 0 < r) (hr : r < 1) {q : ℂ}
    (hq : q ∈ Metric.ball (0 : ℂ) r) :
    HasDerivAt (eulerianPowerSum k) (∑' m : ℕ, (m : ℂ) ^ (k + 1) * q ^ (m - 1)) q := by
  refine hasDerivAt_tsum_of_isPreconnected (u := fun m : ℕ => (m : ℝ) ^ (k + 1) * r ^ (m - 1))
    (summable_bound k hr0 hr) Metric.isOpen_ball ((convex_ball (0 : ℂ) r).isPreconnected)
    (fun m y _ => hasDerivAt_term k m y) ?_ (y₀ := 0) (Metric.mem_ball_self hr0) ?_ hq
  · intro m y hy
    have hy' : ‖y‖ < r := by simpa [Complex.dist_eq] using hy
    rw [norm_mul, norm_pow, norm_pow, Complex.norm_natCast]
    have h1 : ‖y‖ ^ (m - 1) ≤ r ^ (m - 1) := pow_le_pow_left₀ (norm_nonneg y) (le_of_lt hy') _
    have h2 : (0 : ℝ) ≤ (m : ℝ) ^ (k + 1) := by positivity
    exact mul_le_mul_of_nonneg_left h1 h2
  · refine summable_of_ne_finset_zero (s := {0}) ?_
    intro m hm
    simp only [Finset.mem_singleton] at hm
    simp [zero_pow hm]

private theorem one_sub_ne_zero {q : ℂ} (hq : ‖q‖ < 1) : (1 : ℂ) - q ≠ 0 := by
  intro h
  have hq1 : q = 1 := by linear_combination -h
  rw [hq1] at hq
  simp at hq

private theorem q_mul_tsum (k : ℕ) (q : ℂ) :
    q * (∑' m : ℕ, (m : ℂ) ^ (k + 1) * q ^ (m - 1)) = eulerianPowerSum (k + 1) q := by
  rw [eulerianPowerSum, ← tsum_mul_left]
  refine tsum_congr ?_
  intro m
  match m with
  | 0 => simp
  | (i + 1) =>
      simp only [Nat.add_sub_cancel]
      rw [pow_succ]
      ring

/-- **The Eulerian generating function.**
`(sum' m, m^(k+1) q^m) (1 - q)^(k+2) = q E_k(q)` for complex `‖q‖ < 1`. -/
theorem eulerianPowerSum_mul_one_sub_pow (k : ℕ) : ∀ {q : ℂ}, ‖q‖ < 1 →
    eulerianPowerSum (k + 1) q * (1 - q) ^ (k + 2) =
      q * ((generalizedEulerian 1 k).map (algebraMap ℝ ℂ)).eval q := by
  change ∀ {q : ℂ}, ‖q‖ < 1 → _ = q * (complexEulerian k).eval q
  induction k with
  | zero =>
      intro q hq
      have h1 : eulerianPowerSum 1 q = q / (1 - q) ^ 2 := by
        rw [eulerianPowerSum,
          show (fun m : ℕ => (m : ℂ) ^ 1 * q ^ m) = (fun m : ℕ => (m : ℂ) * q ^ m) from
            funext (fun m => by rw [pow_one])]
        exact tsum_coe_mul_geometric_of_norm_lt_one hq
      rw [h1]
      simp only [complexEulerian, generalizedEulerian, Polynomial.map_one, Polynomial.eval_one]
      have h2 : (1 : ℂ) - q ≠ 0 := one_sub_ne_zero hq
      field_simp
  | succ j ih =>
      intro q hq
      obtain ⟨r, hqr, hr1⟩ := exists_between hq
      have hr0 : (0 : ℝ) < r := lt_of_le_of_lt (norm_nonneg q) hqr
      have hqmem : q ∈ Metric.ball (0 : ℂ) r := by simpa [Complex.dist_eq] using hqr
      have hGH : Set.EqOn (fun z : ℂ => eulerianPowerSum (j + 1) z * (1 - z) ^ (j + 2))
          (fun z : ℂ => z * (complexEulerian j).eval z) (Metric.ball (0 : ℂ) r) := by
        intro z hz
        exact ih (lt_trans (by simpa [Complex.dist_eq] using hz) hr1)
      have hpow : HasDerivAt (fun z : ℂ => (1 - z) ^ (j + 2))
          (((j : ℂ) + 2) * (1 - q) ^ (j + 1) * (0 - 1)) q := by
        have hb : HasDerivAt (fun z : ℂ => 1 - z) (0 - 1) q :=
          (hasDerivAt_const q (1 : ℂ)).sub (hasDerivAt_id q)
        have h2 := hb.pow (j + 2)
        have hc : ((j + 2 : ℕ) : ℂ) = (j : ℂ) + 2 := by push_cast; ring
        have hn : j + 2 - 1 = j + 1 := by lia
        rw [hc, hn] at h2
        exact h2
      have hDG : HasDerivAt (fun z : ℂ => eulerianPowerSum (j + 1) z * (1 - z) ^ (j + 2))
          ((∑' m : ℕ, (m : ℂ) ^ (j + 2) * q ^ (m - 1)) * (1 - q) ^ (j + 2) +
            eulerianPowerSum (j + 1) q * (((j : ℂ) + 2) * (1 - q) ^ (j + 1) * (0 - 1))) q :=
        (hasDerivAt_eulerianPowerSum (j + 1) hr0 hr1 hqmem).mul hpow
      have hDH : HasDerivAt (fun z : ℂ => z * (complexEulerian j).eval z)
          (1 * (complexEulerian j).eval q + q * (complexEulerian j).derivative.eval q) q :=
        (hasDerivAt_id q).mul ((complexEulerian j).hasDerivAt q)
      have hev : (fun z : ℂ => z * (complexEulerian j).eval z) =ᶠ[nhds q]
          (fun z : ℂ => eulerianPowerSum (j + 1) z * (1 - z) ^ (j + 2)) :=
        Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hqmem)
          (fun z hz => (hGH hz).symm)
      have hkey := (hDG.congr_of_eventuallyEq hev).unique hDH
      have hshift := q_mul_tsum (j + 1) q
      have hIH := ih hq
      have hrec : (complexEulerian (j + 1)).eval q =
          (1 + ((j : ℂ) + 1) * q) * (complexEulerian j).eval q +
            q * (1 - q) * (complexEulerian j).derivative.eval q := by
        rw [complexEulerian_succ]
        simp
      have hA2 : (1 - q) ^ (j + 2) = (1 - q) ^ (j + 1) * (1 - q) := by
        rw [show j + 2 = j + 1 + 1 from rfl, pow_succ]
      have hA3 : (1 - q) ^ (j + 1 + 2) = (1 - q) ^ (j + 1) * (1 - q) * (1 - q) := by
        rw [show j + 1 + 2 = j + 1 + 1 + 1 from rfl, pow_succ, pow_succ]
      rw [hrec, hA3, ← hshift]
      rw [hA2] at hkey hIH
      linear_combination (q * (1 - q)) * hkey + ((j : ℂ) + 2) * q * hIH

end Analytic

end GeneralizedEulerian
end RealRooted
