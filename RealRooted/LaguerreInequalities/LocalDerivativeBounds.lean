module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import Mathlib.Analysis.Calculus.Deriv.Basic
import RealRooted.LaguerreInequalities.LocalNonzeroLimit
import RealRooted.LaguerreInequalities.LocalProductLimit
import RealRooted.LaguerreInequalities.LogConcavity
import RealRooted.LaguerreInequalities.DerivativeFormula
import RealRooted.Mathlib.Analysis.Complex.LocallyUniformIteratedDeriv
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import Mathlib.Analysis.Convex.Deriv

/-!
# Derivative bounds from pointwise Laguerre--Pólya limits

Real logarithmic concavity controls the otherwise unconstrained exponential
slope of a Laguerre--Pólya function. Together with the common zero-free disk,
three convergent real values bound its first derivative.
-/

public section

open Complex Filter Topology
open scoped ComplexConjugate

namespace RealRooted

private theorem re_ne_zero_of_real_limit {F : ℕ → ℂ → ℂ} {w : ℂ}
    (hF : ∀ n, IsLaguerrePolya (F n)) (x : ℝ)
    (ht : Tendsto (fun n => F n x) atTop (𝓝 w)) (hw : w ≠ 0) : w.re ≠ 0 := by
  have hreal (n : ℕ) : ((F n x).re : ℂ) = F n x := by
    apply conj_eq_iff_re.mp
    simpa using ((hF n).conj x).symm
  have heq : (w.re : ℂ) = w := tendsto_nhds_unique
    (((continuous_re.tendsto w).comp ht).ofReal.congr hreal) ht
  intro hr
  exact hw (by rw [← heq, hr, ofReal_zero])

private theorem exists_eventually_logDeriv_bound {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hF : ∀ n, IsLaguerrePolya (F n)) {a x b : ℝ} (hax : a < x) (hxb : x < b)
    (hpoint : ∀ y ∈ ({a, x, b} : Set ℝ),
      Tendsto (fun n => F n y) atTop (𝓝 (g y)))
    (hg : ∀ y ∈ ({a, x, b} : Set ℝ), g y ≠ 0)
    (hne : ∀ᶠ n in atTop, ∀ y ∈ Set.Icc a b, F n y ≠ 0) :
    ∃ C > 0, ∀ᶠ n in atTop, |(deriv (F n) x).re / (F n x).re| ≤ C := by
  let L (n : ℕ) (y : ℝ) := Real.log (F n y).re
  let l (y : ℝ) := Real.log (g y).re
  have hlog (y : ℝ) (hy : y ∈ ({a, x, b} : Set ℝ)) :
      Tendsto (fun n => L n y) atTop (𝓝 (l y)) :=
    ((continuous_re.tendsto _).comp (hpoint y hy)).log
      (re_ne_zero_of_real_limit hF y (hpoint y hy) (hg y hy))
  have hleft : Tendsto (fun n => slope (L n) a x) atTop (𝓝 (slope l a x)) := by
    simpa only [slope_def_field] using
      ((hlog x (by simp)).sub (hlog a (by simp))).div_const (x - a)
  have hright : Tendsto (fun n => slope (L n) x b) atTop (𝓝 (slope l x b)) := by
    simpa only [slope_def_field] using
      ((hlog b (by simp)).sub (hlog x (by simp))).div_const (b - x)
  obtain ⟨A, hA, hAb⟩ := (Metric.isBounded_range_of_tendsto _ hleft).exists_pos_norm_le
  obtain ⟨B, hB, hBb⟩ := (Metric.isBounded_range_of_tendsto _ hright).exists_pos_norm_le
  refine ⟨A + B, add_pos hA hB, ?_⟩
  filter_upwards [hne] with n hn
  have hx : x ∈ Set.Icc a b := ⟨hax.le, hxb.le⟩
  have hreal : ((F n x).re : ℂ) = F n x := by
    apply conj_eq_iff_re.mp
    simpa using ((hF n).conj x).symm
  have hrex : (F n x).re ≠ 0 := by
    intro hz
    exact hn x hx (by rw [← hreal, hz, ofReal_zero])
  have hd := ((hF n).differentiable x).hasDerivAt.real_of_complex.log hrex
  have hc := (hF n).concaveOn_log_re (convex_Icc a b) hn
  have hu := hc.le_slope_of_hasDerivAt (Set.left_mem_Icc.mpr (hax.trans hxb).le) hx hax hd
  have hl := hc.slope_le_of_hasDerivAt hx (Set.right_mem_Icc.mpr (hax.trans hxb).le) hxb hd
  have hA' : |slope (L n) a x| ≤ A := by simpa using hAb _ ⟨n, rfl⟩
  have hB' : |slope (L n) x b| ≤ B := by simpa using hBb _ ⟨n, rfl⟩
  dsimp only [L] at hA' hB'
  rw [abs_le] at hA' hB' ⊢
  constructor <;> linarith

/-- Pointwise convergence of Laguerre--Pólya functions on a disk, with a
nonzero limiting value at its real center, bounds the first derivatives there. -/
theorem exists_eventually_norm_deriv_le_of_tendsto {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hF : ∀ n, IsLaguerrePolya (F n)) (x : ℝ) {r : ℝ} (hr : 0 < r)
    (hpoint : ∀ z ∈ Metric.ball (x : ℂ) r,
      Tendsto (fun n => F n z) atTop (𝓝 (g z))) (hg : g x ≠ 0) :
    ∃ C > 0, ∀ᶠ n in atTop, ‖deriv (F n) x‖ ≤ C := by
  obtain ⟨δ, hδ, hgnz, hFnz⟩ := exists_ball_ne_zero_of_tendsto hF x hr hpoint hg
  let ε := min δ r / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hmem {y : ℝ} (hy : y ∈ Set.Icc (x - ε) (x + ε)) :
      (y : ℂ) ∈ Metric.ball (x : ℂ) (min δ r) := by
    have habs : |y - x| ≤ ε := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have : |y - x| < min δ r := by dsimp [ε] at hε habs; linarith
    simpa [Metric.mem_ball, dist_eq_norm, ← ofReal_sub] using this
  have hthree {y : ℝ} (hy : y ∈ ({x - ε, x, x + ε} : Set ℝ)) :
      y ∈ Set.Icc (x - ε) (x + ε) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl <;> constructor <;> linarith
  obtain ⟨A, hA, hAb⟩ := exists_eventually_logDeriv_bound hF
    (show x - ε < x by linarith) (show x < x + ε by linarith)
    (fun y hy => hpoint y (Metric.ball_subset_ball (min_le_right δ r) (hmem (hthree hy))))
    (fun y hy => hgnz y (Metric.ball_subset_ball (min_le_left δ r) (hmem (hthree hy))))
    (hFnz.mono fun n hn y hy => hn y (Metric.ball_subset_ball (min_le_left δ r) (hmem hy)))
  obtain ⟨B, hB, hBb⟩ := (Metric.isBounded_range_of_tendsto _
    (hpoint x (by simpa using hr))).exists_pos_norm_le
  refine ⟨A * B, mul_pos hA hB, ?_⟩
  filter_upwards [hAb, hFnz] with n hn hnonzero
  have hne : F n x ≠ 0 := hnonzero x (by simpa using hδ)
  have hreal : ((F n x).re : ℂ) = F n x := by
    apply conj_eq_iff_re.mp
    simpa using ((hF n).conj x).symm
  have hdreal : ((deriv (F n) x).re : ℂ) = deriv (F n) x := by
    apply conj_eq_iff_re.mp
    simpa using ((hF n).deriv.conj x).symm
  have hrex : (F n x).re ≠ 0 := by
    intro hz
    exact hne (by rw [← hreal, hz, ofReal_zero])
  calc
    ‖deriv (F n) x‖ = |(deriv (F n) x).re / (F n x).re| * ‖F n x‖ := by
      rw [← hdreal, ← hreal, norm_real, Real.norm_eq_abs, norm_real, Real.norm_eq_abs,
        ofReal_re, ofReal_re, abs_div, div_mul_cancel₀ _ (abs_ne_zero.mpr hrex)]
    _ ≤ A * B := mul_le_mul hn (hBb _ ⟨n, rfl⟩) (norm_nonneg _) hA.le

/-- Under pointwise convergence with a nonzero real limiting value, the
second derivatives of Laguerre--Pólya functions are eventually bounded too. -/
theorem exists_eventually_norm_deriv_deriv_le_of_tendsto {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hF : ∀ n, IsLaguerrePolya (F n)) (x : ℝ) {r : ℝ} (hr : 0 < r)
    (hpoint : ∀ z ∈ Metric.ball (x : ℂ) r,
      Tendsto (fun n => F n z) atTop (𝓝 (g z))) (hg : g x ≠ 0) :
    ∃ C > 0, ∀ᶠ n in atTop, ‖deriv (deriv (F n)) x‖ ≤ C := by
  obtain ⟨A, hA, hAb⟩ := exists_eventually_norm_deriv_le_of_tendsto hF x hr hpoint hg
  have hlim := tendstoLocallyUniformlyOn_laguerreProduct hF x hr hpoint
  have hjlim := hlim.iteratedDeriv_of_entire (Eventually.of_forall fun n =>
    differentiable_laguerreProduct (hF n).differentiable x) Metric.isOpen_ball 2
  have hjet := hjlim.tendsto_at (show (0 : ℂ) ∈ Metric.ball 0 r by simpa using hr)
  have hL : Tendsto (fun n => laguerreCoefficient (F n) x 1) atTop
      (𝓝 (laguerreCoefficient g x 1)) := by
    exact ((continuous_re.tendsto _).comp hjet).div_const (2 : ℝ)
  obtain ⟨B, hB, hBb⟩ := (Metric.isBounded_range_of_tendsto _ hL).exists_pos_norm_le
  have hx := hpoint x (by simpa using hr)
  obtain ⟨C, hC, hCb⟩ := (Metric.isBounded_range_of_tendsto _ (hx.inv₀ hg)).exists_pos_norm_le
  refine ⟨(A ^ 2 + B) * C, mul_pos (by positivity) hC, ?_⟩
  filter_upwards [hAb, hx.eventually_ne hg] with n hn hne
  have hreal : ((F n x).re : ℂ) = F n x := by
    apply conj_eq_iff_re.mp
    simpa using ((hF n).conj x).symm
  have hdreal : ((deriv (deriv (F n)) x).re : ℂ) = deriv (deriv (F n)) x := by
    apply conj_eq_iff_re.mp
    simpa using ((hF n).deriv.deriv.conj x).symm
  have hrex : (F n x).re ≠ 0 := by
    intro hz
    exact hne (by rw [← hreal, hz, ofReal_zero])
  have hformula := laguerreCoefficient_one (hF n).differentiable (hF n).conj x
  simp only [iteratedDeriv_succ, iteratedDeriv_zero] at hformula
  have heq : (deriv (deriv (F n)) x).re =
      ((deriv (F n) x).re ^ 2 - laguerreCoefficient (F n) x 1) / (F n x).re := by
    apply (eq_div_iff hrex).mpr
    nlinarith [hformula]
  have hbound : |(deriv (F n) x).re ^ 2 - laguerreCoefficient (F n) x 1| ≤ A ^ 2 + B := by
    calc
      _ ≤ |(deriv (F n) x).re ^ 2| + |laguerreCoefficient (F n) x 1| := abs_sub _ _
      _ ≤ A ^ 2 + B := by
        apply add_le_add _ (show |laguerreCoefficient (F n) x 1| ≤ B by
          simpa using hBb _ ⟨n, rfl⟩)
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) ((abs_re_le_norm _).trans hn) 2
  have hnorm : ‖deriv (deriv (F n)) x‖ =
      |(deriv (F n) x).re ^ 2 - laguerreCoefficient (F n) x 1| * ‖(F n x)⁻¹‖ := by
    conv_lhs => rw [← hdreal, norm_real, Real.norm_eq_abs, heq, abs_div]
    rw [norm_inv, ← hreal, norm_real, Real.norm_eq_abs, ofReal_re, div_eq_mul_inv]
  rw [hnorm]
  exact mul_le_mul hbound (hCb _ ⟨n, rfl⟩) (norm_nonneg _) (by positivity)

end RealRooted
