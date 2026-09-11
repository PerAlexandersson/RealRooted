import RealRooted.Mathlib.Analysis.SpecialFunctions.Choose
import RealRooted.MultiplierSequence
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

/-!
# Rescaled Jensen limits

This explicitly analytic leaf proves coefficientwise and summable pointwise
convergence for rescaled Jensen polynomials, together with uniform convergence
on real intervals and complex closed disks under an explicit summable majorant.
The same all-radius majorant gives an entire complex exponential-generating
function. This leaf does not prove a Laguerre--Pólya limit theorem or establish
a Pólya--Schur classification direction.
-/

open Filter Polynomial Topology

noncomputable section

namespace RealRooted

private theorem tsum_coeff_mul_pow_eq_eval (p : ℝ[X]) (x : ℝ) :
    (∑' k : ℕ, p.coeff k * x ^ k) = p.eval x := by
  rw [tsum_eq_sum (s := p.support) (fun k hk => by
    have hzero : p.coeff k = 0 := by
      apply Classical.by_contradiction
      intro hne
      exact hk (Finsupp.mem_support_iff.mpr hne)
    simp [hzero]), p.eval_eq_sum]
  rfl

private theorem tsum_coeff_mul_pow_eq_eval_complex (p : ℝ[X]) (z : ℂ) :
    (∑' k : ℕ, (p.coeff k : ℂ) * z ^ k) =
      (p.map Complex.ofRealHom).eval z := by
  rw [tsum_eq_sum (s := p.support) (fun k hk => by
    have hzero : p.coeff k = 0 := by
      apply Classical.by_contradiction
      intro hne
      exact hk (Finsupp.mem_support_iff.mpr hne)
    simp [hzero]), Polynomial.eval_map, Polynomial.eval₂_eq_sum]
  rfl

/-- The degree-`n` Jensen polynomial after the variable rescaling `X ↦ X / n`.
The convention at `n = 0` uses Lean's zero inverse. -/
def rescaledJensenPolynomial (n : ℕ) (gamma : ℕ → ℝ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    monomial k ((n.choose k : ℝ) * gamma k * ((n : ℝ)⁻¹) ^ k)

@[simp]
theorem coeff_rescaledJensenPolynomial (n k : ℕ) (gamma : ℕ → ℝ) :
    (rescaledJensenPolynomial n gamma).coeff k =
      if k ≤ n then (n.choose k : ℝ) * gamma k * ((n : ℝ)⁻¹) ^ k else 0 := by
  classical
  unfold rescaledJensenPolynomial
  by_cases hk : k ≤ n
  · have hmem : k ∈ Finset.range (n + 1) := by simp_all
    rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single k]
    · simp [hk]
    · intro b hb hbk
      simp [Polynomial.coeff_monomial, hbk]
    · simp_all
  · rw [Polynomial.finsetSum_coeff, Finset.sum_eq_zero]
    · simp [hk]
    · intro b hb
      have hb_le : b ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
      have hne : k ≠ b := by grind
      have hbk : b ≠ k := Ne.symm hne
      simp [Polynomial.coeff_monomial, hbk]

/-- The coefficient-form rescaling agrees with substitution by `X / n`. -/
theorem rescaledJensenPolynomial_eq_jensenPolynomial_comp (n : ℕ)
    (gamma : ℕ → ℝ) :
    rescaledJensenPolynomial n gamma =
      (jensenPolynomial n gamma).comp (C ((n : ℝ)⁻¹) * X) := by
  ext k
  rw [coeff_rescaledJensenPolynomial, Polynomial.comp_C_mul_X_coeff,
    coeff_jensenPolynomial]
  split <;> simp_all [mul_left_comm, mul_comm]

/-- Each fixed coefficient of the rescaled Jensen polynomials converges to
the corresponding exponential-generating-function coefficient. -/
theorem tendsto_coeff_rescaledJensenPolynomial (gamma : ℕ → ℝ) (k : ℕ) :
    Tendsto (fun n : ℕ => (rescaledJensenPolynomial n gamma).coeff k) atTop
      (𝓝 (gamma k / k.factorial)) := by
  have heq : (fun n : ℕ => (rescaledJensenPolynomial n gamma).coeff k) =ᶠ[atTop]
      fun n => (n.choose k : ℝ) * gamma k * ((n : ℝ)⁻¹) ^ k := by
    filter_upwards [eventually_ge_atTop k] with n hn
    rw [coeff_rescaledJensenPolynomial, if_pos hn]
  refine Tendsto.congr' heq.symm ?_
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    (tendsto_choose_mul_inv_pow_atTop k).mul_const (gamma k)

/-- The rescaled Jensen coefficient has the summable majorant supplied by
the exponential-generating coefficient of `gamma`. -/
theorem norm_coeff_rescaledJensenPolynomial_le (n k : ℕ) (gamma : ℕ → ℝ) :
    ‖(rescaledJensenPolynomial n gamma).coeff k‖ ≤ ‖gamma k‖ / k.factorial := by
  rw [coeff_rescaledJensenPolynomial]
  split
  · calc
      ‖(n.choose k : ℝ) * gamma k * ((n : ℝ)⁻¹) ^ k‖ =
          ‖(n.choose k : ℝ) * ((n : ℝ)⁻¹) ^ k‖ * ‖gamma k‖ := by
        have hreorder : (n.choose k : ℝ) * gamma k * ((n : ℝ)⁻¹) ^ k =
            ((n.choose k : ℝ) * ((n : ℝ)⁻¹) ^ k) * gamma k := by
          ring
        rw [hreorder, norm_mul]
      _ ≤ (1 / (k.factorial : ℝ)) * ‖gamma k‖ :=
        mul_le_mul_of_nonneg_right (norm_choose_mul_inv_pow_le n k) (norm_nonneg _)
      _ = ‖gamma k‖ / k.factorial := by ring
  · simp only [norm_zero]
    exact div_nonneg (norm_nonneg _) (by positivity)

/-- A summable exponential-generating majorant gives uniform convergence of
the limiting series on the indicated closed ball. -/
theorem hasSumUniformlyOn_expGeneratingSeries (gamma : ℕ → ℝ) (R : ℝ)
    (hsum : Summable (fun k => ‖gamma k‖ * R ^ k / k.factorial)) :
    HasSumUniformlyOn
      (fun k (x : ℝ) => (gamma k / k.factorial) * x ^ k)
      (fun x => ∑' k, (gamma k / k.factorial) * x ^ k)
      (Metric.closedBall 0 R) := by
  apply HasSumUniformlyOn.of_norm_le_summable hsum
  intro k x hx
  have hxR : ‖x‖ ≤ R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  calc
    ‖(gamma k / k.factorial) * x ^ k‖ =
        (‖gamma k‖ / k.factorial) * ‖x‖ ^ k := by
      rw [norm_mul, norm_div, Real.norm_natCast, norm_pow]
    _ ≤ (‖gamma k‖ / k.factorial) * R ^ k :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg x) hxR _) (by positivity)
    _ = ‖gamma k‖ * R ^ k / k.factorial := by ring

private theorem tendstoUniformlyOn_rescaledJensenPolynomial_finset
    (gamma : ℕ → ℝ) (R : ℝ) (hR : 0 ≤ R) (t : Finset ℕ) :
    TendstoUniformlyOn
      (fun n (x : ℝ) => ∑ k ∈ t, (rescaledJensenPolynomial n gamma).coeff k * x ^ k)
      (fun x => ∑ k ∈ t, (gamma k / k.factorial) * x ^ k) atTop (Metric.closedBall 0 R) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hterm (k : ℕ) : Tendsto
      (fun n => ‖(rescaledJensenPolynomial n gamma).coeff k - gamma k / k.factorial‖ * R ^ k)
      atTop (𝓝 0) := by
    have hzero : Tendsto
        (fun n => ‖(rescaledJensenPolynomial n gamma).coeff k - gamma k / k.factorial‖)
        atTop (𝓝 0) := by simpa only [Function.comp_def, sub_self, norm_zero] using
          (tendsto_norm.comp ((tendsto_coeff_rescaledJensenPolynomial gamma k).sub
            (tendsto_const_nhds : Tendsto (fun _ : ℕ => gamma k / k.factorial) atTop
              (𝓝 (gamma k / k.factorial)))))
    simpa using hzero.mul_const (R ^ k)
  have hsum : Tendsto (fun n => ∑ k ∈ t,
      ‖(rescaledJensenPolynomial n gamma).coeff k - gamma k / k.factorial‖ * R ^ k)
      atTop (𝓝 0) := by simpa using tendsto_finsetSum t fun k _ => hterm k
  rw [Metric.tendsto_nhds] at hsum
  filter_upwards [hsum ε hε] with n hn x hx
  have hxR : ‖x‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  rw [dist_eq_norm, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k ∈ t, ‖(gamma k / k.factorial) * x ^ k -
        (rescaledJensenPolynomial n gamma).coeff k * x ^ k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ t, ‖(rescaledJensenPolynomial n gamma).coeff k - gamma k / k.factorial‖ * R ^ k := by
      gcongr with k hk
      rw [show (gamma k / k.factorial) * x ^ k -
          (rescaledJensenPolynomial n gamma).coeff k * x ^ k =
          (gamma k / k.factorial - (rescaledJensenPolynomial n gamma).coeff k) * x ^ k by ring,
        norm_mul, norm_sub_rev]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [norm_pow] using pow_le_pow_left₀ (norm_nonneg x) hxR k) (norm_nonneg _)
    _ < ε := by rw [dist_zero_right, Real.norm_of_nonneg (by positivity)] at hn; exact hn

/-- On every closed ball with a summable exponential-generating majorant, the
rescaled Jensen polynomials converge uniformly to their limiting series. -/
theorem tendstoUniformlyOn_eval_rescaledJensenPolynomial_of_summable
    (gamma : ℕ → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hsum : Summable (fun k => ‖gamma k‖ * R ^ k / k.factorial)) :
    TendstoUniformlyOn (fun n (x : ℝ) => (rescaledJensenPolynomial n gamma).eval x)
      (fun x => ∑' k, (gamma k / k.factorial) * x ^ k) atTop (Metric.closedBall 0 R) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let ⟨S, hS⟩ := hsum
  obtain ⟨T, hT⟩ : ∃ (T : Finset ℕ),
      dist (∑ k ∈ T, ‖gamma k‖ * R ^ k / k.factorial) S < ε / 3 := by
    rw [HasSum, Metric.tendsto_nhds] at hS
    classical exact Eventually.exists <| hS _ (by positivity)
  have htail : ∑' (k : (Tᶜ : Set ℕ)), ‖gamma k.1‖ * R ^ k.1 / k.1.factorial < ε / 3 := by
    calc _ ≤ ‖∑' (k : (Tᶜ : Set ℕ)), ‖gamma k.1‖ * R ^ k.1 / k.1.factorial‖ := Real.le_norm_self _
         _ = ‖S - ∑ k ∈ T, ‖gamma k‖ * R ^ k / k.factorial‖ := congrArg _ (by
           simpa only [hsum.sum_add_tsum_compl, eq_sub_iff_add_eq'] using hS.tsum_eq)
         _ < ε / 3 := by rwa [dist_eq_norm, norm_sub_rev] at hT
  have hfinite := tendstoUniformlyOn_rescaledJensenPolynomial_finset gamma R hR T
  rw [Metric.tendstoUniformlyOn_iff] at hfinite
  filter_upwards [hfinite (ε / 3) (by positivity)] with n hn x hx
  have hxR : ‖x‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  have hbound (k : ℕ) : ‖(rescaledJensenPolynomial n gamma).coeff k * x ^ k‖ ≤
      ‖gamma k‖ * R ^ k / k.factorial := by
    calc
      _ = ‖(rescaledJensenPolynomial n gamma).coeff k‖ * ‖x‖ ^ k := by rw [norm_mul, norm_pow]
      _ ≤ (‖gamma k‖ / k.factorial) * ‖x‖ ^ k := mul_le_mul_of_nonneg_right
        (norm_coeff_rescaledJensenPolynomial_le n k gamma) (pow_nonneg (norm_nonneg _) _)
      _ ≤ (‖gamma k‖ / k.factorial) * R ^ k := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg x) hxR _) (by positivity)
      _ = _ := by ring
  have hlimbound (k : ℕ) : ‖(gamma k / k.factorial) * x ^ k‖ ≤
      ‖gamma k‖ * R ^ k / k.factorial := by
    calc
      _ = (‖gamma k‖ / k.factorial) * ‖x‖ ^ k := by
        rw [norm_mul, norm_div, Real.norm_natCast, norm_pow]
      _ ≤ (‖gamma k‖ / k.factorial) * R ^ k := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg x) hxR _) (by positivity)
      _ = _ := by ring
  have hsuma : Summable (fun k => ‖(rescaledJensenPolynomial n gamma).coeff k * x ^ k‖) :=
    hsum.of_norm_bounded (by simpa only [norm_norm] using hbound)
  have hsumb : Summable (fun k => ‖(gamma k / k.factorial) * x ^ k‖) :=
    hsum.of_norm_bounded (by simpa only [norm_norm] using hlimbound)
  rw [← tsum_coeff_mul_pow_eq_eval, dist_eq_norm, norm_sub_rev,
    ← hsuma.of_norm.tsum_sub hsumb.of_norm,
    ← (hsuma.of_norm.sub hsumb.of_norm).sum_add_tsum_subtype_compl (s := T),
    (by ring : ε = ε / 3 + (ε / 3 + ε / 3))]
  refine (norm_add_le _ _).trans_lt (add_lt_add ?_ ?_)
  · rw [Finset.sum_sub_distrib, norm_sub_rev]
    simpa only [dist_eq_norm] using hn x hx
  · rw [(hsuma.subtype _).of_norm.tsum_sub (hsumb.subtype _).of_norm]
    refine (norm_sub_le _ _).trans_lt (add_lt_add ?_ ?_)
    · refine ((norm_tsum_le_tsum_norm (hsuma.subtype _)).trans ?_).trans_lt htail
      exact (hsuma.subtype _).tsum_le_tsum (fun k => hbound k) (hsum.subtype _)
    · refine ((norm_tsum_le_tsum_norm (hsumb.subtype _)).trans ?_).trans_lt htail
      exact (hsumb.subtype _).tsum_le_tsum (fun k => hlimbound k) (hsum.subtype _)

private theorem tendstoUniformlyOn_rescaledJensenPolynomial_complex_finset
    (gamma : ℕ → ℝ) (R : ℝ) (hR : 0 ≤ R) (t : Finset ℕ) :
    TendstoUniformlyOn
      (fun n (z : ℂ) => ∑ k ∈ t,
        ((rescaledJensenPolynomial n gamma).coeff k : ℂ) * z ^ k)
      (fun z => ∑ k ∈ t, ((gamma k / k.factorial : ℝ) : ℂ) * z ^ k)
      atTop (Metric.closedBall 0 R) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hterm (k : ℕ) : Tendsto
      (fun n => ‖((rescaledJensenPolynomial n gamma).coeff k - gamma k / k.factorial : ℝ)‖ * R ^ k)
      atTop (𝓝 0) := by
    have hzero : Tendsto
        (fun n => ‖(rescaledJensenPolynomial n gamma).coeff k - gamma k / k.factorial‖)
        atTop (𝓝 0) := by
      simpa only [Function.comp_def, sub_self, norm_zero] using
        (tendsto_norm.comp ((tendsto_coeff_rescaledJensenPolynomial gamma k).sub
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => gamma k / k.factorial) atTop
            (𝓝 (gamma k / k.factorial)))))
    simpa using hzero.mul_const (R ^ k)
  have hsum : Tendsto (fun n => ∑ k ∈ t,
      ‖((rescaledJensenPolynomial n gamma).coeff k - gamma k / k.factorial : ℝ)‖ * R ^ k)
      atTop (𝓝 0) := by
    simpa using tendsto_finsetSum t fun k _ => hterm k
  rw [Metric.tendsto_nhds] at hsum
  filter_upwards [hsum ε hε] with n hn z hz
  have hzR : ‖z‖ ≤ R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  rw [dist_eq_norm, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k ∈ t, ‖((gamma k / k.factorial : ℝ) : ℂ) * z ^ k -
        ((rescaledJensenPolynomial n gamma).coeff k : ℂ) * z ^ k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ t,
        ‖((rescaledJensenPolynomial n gamma).coeff k - gamma k / k.factorial : ℝ)‖ * R ^ k := by
      gcongr with k hk
      rw [show ((gamma k / k.factorial : ℝ) : ℂ) * z ^ k -
          ((rescaledJensenPolynomial n gamma).coeff k : ℂ) * z ^ k =
          -(((rescaledJensenPolynomial n gamma).coeff k - gamma k / k.factorial : ℝ) : ℂ) * z ^ k by
            push_cast
            ring,
        norm_mul, norm_neg, Complex.norm_real]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [norm_pow] using pow_le_pow_left₀ (norm_nonneg z) hzR k) (norm_nonneg _)
    _ < ε := by
      rw [dist_zero_right, Real.norm_of_nonneg (by positivity)] at hn
      exact hn

/-- On every complex closed disk with a summable exponential-generating
majorant, the complexifications of the rescaled Jensen polynomials converge
uniformly to the complex exponential-generating series. -/
theorem tendstoUniformlyOn_eval_complex_rescaledJensenPolynomial_of_summable
    (gamma : ℕ → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hsum : Summable (fun k => ‖gamma k‖ * R ^ k / k.factorial)) :
    TendstoUniformlyOn
      (fun n (z : ℂ) => (rescaledJensenPolynomial n gamma).map Complex.ofRealHom |>.eval z)
      (fun z => ∑' k, ((gamma k / k.factorial : ℝ) : ℂ) * z ^ k)
      atTop (Metric.closedBall 0 R) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let ⟨S, hS⟩ := hsum
  obtain ⟨T, hT⟩ : ∃ (T : Finset ℕ),
      dist (∑ k ∈ T, ‖gamma k‖ * R ^ k / k.factorial) S < ε / 3 := by
    rw [HasSum, Metric.tendsto_nhds] at hS
    classical exact Eventually.exists <| hS _ (by positivity)
  have htail : ∑' (k : (Tᶜ : Set ℕ)), ‖gamma k.1‖ * R ^ k.1 / k.1.factorial < ε / 3 := by
    calc _ ≤ ‖∑' (k : (Tᶜ : Set ℕ)), ‖gamma k.1‖ * R ^ k.1 / k.1.factorial‖ :=
           Real.le_norm_self _
         _ = ‖S - ∑ k ∈ T, ‖gamma k‖ * R ^ k / k.factorial‖ := congrArg _ (by
           simpa only [hsum.sum_add_tsum_compl, eq_sub_iff_add_eq'] using hS.tsum_eq)
         _ < ε / 3 := by rwa [dist_eq_norm, norm_sub_rev] at hT
  have hfinite := tendstoUniformlyOn_rescaledJensenPolynomial_complex_finset gamma R hR T
  rw [Metric.tendstoUniformlyOn_iff] at hfinite
  filter_upwards [hfinite (ε / 3) (by positivity)] with n hn z hz
  have hzR : ‖z‖ ≤ R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  have hbound (k : ℕ) :
      ‖((rescaledJensenPolynomial n gamma).coeff k : ℂ) * z ^ k‖ ≤
        ‖gamma k‖ * R ^ k / k.factorial := by
    calc
      _ = ‖(rescaledJensenPolynomial n gamma).coeff k‖ * ‖z‖ ^ k := by
        rw [norm_mul, Complex.norm_real, norm_pow]
      _ ≤ (‖gamma k‖ / k.factorial) * ‖z‖ ^ k :=
        mul_le_mul_of_nonneg_right
          (norm_coeff_rescaledJensenPolynomial_le n k gamma) (pow_nonneg (norm_nonneg _) _)
      _ ≤ (‖gamma k‖ / k.factorial) * R ^ k :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg z) hzR _) (by positivity)
      _ = _ := by ring
  have hlimbound (k : ℕ) : ‖((gamma k / k.factorial : ℝ) : ℂ) * z ^ k‖ ≤
      ‖gamma k‖ * R ^ k / k.factorial := by
    calc
      _ = (‖gamma k‖ / k.factorial) * ‖z‖ ^ k := by
        rw [norm_mul, Complex.norm_real, norm_div, Real.norm_natCast, norm_pow]
      _ ≤ (‖gamma k‖ / k.factorial) * R ^ k :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg z) hzR _) (by positivity)
      _ = _ := by ring
  have hsuma : Summable (fun k =>
      ‖((rescaledJensenPolynomial n gamma).coeff k : ℂ) * z ^ k‖) :=
    hsum.of_norm_bounded (by simpa only [norm_norm] using hbound)
  have hsumb : Summable (fun k => ‖((gamma k / k.factorial : ℝ) : ℂ) * z ^ k‖) :=
    hsum.of_norm_bounded (by simpa only [norm_norm] using hlimbound)
  rw [← tsum_coeff_mul_pow_eq_eval_complex (rescaledJensenPolynomial n gamma) z,
    dist_eq_norm, norm_sub_rev,
    ← hsuma.of_norm.tsum_sub hsumb.of_norm,
    ← (hsuma.of_norm.sub hsumb.of_norm).sum_add_tsum_subtype_compl (s := T),
    (by ring : ε = ε / 3 + (ε / 3 + ε / 3))]
  refine (norm_add_le _ _).trans_lt (add_lt_add ?_ ?_)
  · rw [Finset.sum_sub_distrib, norm_sub_rev]
    simpa only [dist_eq_norm] using hn z hz
  · rw [(hsuma.subtype _).of_norm.tsum_sub (hsumb.subtype _).of_norm]
    refine (norm_sub_le _ _).trans_lt (add_lt_add ?_ ?_)
    · refine ((norm_tsum_le_tsum_norm (hsuma.subtype _)).trans ?_).trans_lt htail
      exact (hsuma.subtype _).tsum_le_tsum (fun k => hbound k) (hsum.subtype _)
    · refine ((norm_tsum_le_tsum_norm (hsumb.subtype _)).trans ?_).trans_lt htail
      exact (hsumb.subtype _).tsum_le_tsum (fun k => hlimbound k) (hsum.subtype _)

/-- Summability of the complex exponential-generating majorant at every
nonnegative radius upgrades the rescaled Jensen limit to local uniform
convergence on `ℂ`. -/
theorem tendstoLocallyUniformly_eval_complex_rescaledJensenPolynomial_of_summable
    (gamma : ℕ → ℝ)
    (hsum : ∀ R : ℝ, 0 ≤ R → Summable (fun k => ‖gamma k‖ * R ^ k / k.factorial)) :
    TendstoLocallyUniformly
      (fun n (z : ℂ) => (rescaledJensenPolynomial n gamma).map Complex.ofRealHom |>.eval z)
      (fun z => ∑' k, ((gamma k / k.factorial : ℝ) : ℂ) * z ^ k) atTop := by
  intro u hu z
  let R : ℝ := ‖z‖ + 1
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  have hz : z ∈ Metric.ball 0 R := by
    simpa only [Metric.mem_ball, dist_zero_right] using lt_add_one ‖z‖
  have hU := tendstoUniformlyOn_eval_complex_rescaledJensenPolynomial_of_summable
    gamma R hR (hsum R hR)
  exact ⟨Metric.closedBall 0 R, Metric.closedBall_mem_nhds_of_mem hz, hU u hu⟩

/-- The complex exponential-generating function of a real sequence. -/
def complexExpGeneratingFunction (gamma : ℕ → ℝ) : ℂ → ℂ :=
  FormalMultilinearSeries.ofScalarsSum (E := ℂ)
    (fun k => ((gamma k / k.factorial : ℝ) : ℂ))

/-- The formal-series definition of the complex exponential-generating
function agrees with its coefficientwise `tsum` expression. -/
theorem complexExpGeneratingFunction_eq_tsum (gamma : ℕ → ℝ) :
    complexExpGeneratingFunction gamma =
      fun z => ∑' k : ℕ, ((gamma k / k.factorial : ℝ) : ℂ) * z ^ k := by
  simpa only [complexExpGeneratingFunction, smul_eq_mul] using
    (FormalMultilinearSeries.ofScalarsSum_eq_tsum (E := ℂ)
      (fun k => ((gamma k / k.factorial : ℝ) : ℂ)))

/-- An all-radius exponential-generating majorant makes the complex
exponential-generating function entire. -/
theorem analyticOnNhd_complexExpGeneratingFunction_of_summable (gamma : ℕ → ℝ)
    (hsum : ∀ R : ℝ, 0 ≤ R → Summable (fun k => ‖gamma k‖ * R ^ k / k.factorial)) :
    AnalyticOnNhd ℂ (complexExpGeneratingFunction gamma) Set.univ := by
  let c : ℕ → ℂ := fun k => ((gamma k / k.factorial : ℝ) : ℂ)
  let p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ c
  have hp : p.radius = ⊤ := by
    apply FormalMultilinearSeries.radius_eq_top_of_summable_norm p
    intro r
    dsimp only [p]
    simp_rw [FormalMultilinearSeries.ofScalars_norm ℂ c]
    convert hsum (r : ℝ) r.coe_nonneg using 1
    ext n
    simp only [Complex.norm_real, c, norm_div, Real.norm_natCast]
    ring
  have hball : Metric.eball (0 : ℂ) p.radius = Set.univ := by
    simp [hp]
  rw [← hball]
  simpa only [complexExpGeneratingFunction, p,
    FormalMultilinearSeries.ofScalarsSum] using p.analyticOnNhd

/-- Under the all-radius majorant, the complexified rescaled Jensen
polynomials converge locally uniformly to the entire exponential-generating
function. -/
theorem tendstoLocallyUniformly_complexExpGeneratingFunction_of_summable
    (gamma : ℕ → ℝ)
    (hsum : ∀ R : ℝ, 0 ≤ R → Summable (fun k => ‖gamma k‖ * R ^ k / k.factorial)) :
    TendstoLocallyUniformly
      (fun n (z : ℂ) => (rescaledJensenPolynomial n gamma).map Complex.ofRealHom |>.eval z)
      (complexExpGeneratingFunction gamma) atTop := by
  rw [complexExpGeneratingFunction_eq_tsum]
  exact tendstoLocallyUniformly_eval_complex_rescaledJensenPolynomial_of_summable gamma hsum

/-- Summability of the exponential-generating majorant at every nonnegative
radius upgrades the rescaled Jensen limit to local uniform convergence. -/
theorem tendstoLocallyUniformly_eval_rescaledJensenPolynomial_of_summable
    (gamma : ℕ → ℝ)
    (hsum : ∀ R : ℝ, 0 ≤ R → Summable (fun k => ‖gamma k‖ * R ^ k / k.factorial)) :
    TendstoLocallyUniformly (fun n (x : ℝ) => (rescaledJensenPolynomial n gamma).eval x)
      (fun x => ∑' k, (gamma k / k.factorial) * x ^ k) atTop := by
  intro u hu x
  let R : ℝ := ‖x‖ + 1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hx : x ∈ Metric.ball 0 R := by
    simpa only [Metric.mem_ball, dist_zero_right] using lt_add_one ‖x‖
  have hU := tendstoUniformlyOn_eval_rescaledJensenPolynomial_of_summable gamma R hR
    (hsum R hR)
  exact ⟨Metric.closedBall 0 R, Metric.closedBall_mem_nhds_of_mem hx, hU u hu⟩

/-- Under absolute summability at `x`, the rescaled Jensen polynomials
converge pointwise to the exponential-generating series of `gamma`. -/
theorem tendsto_eval_rescaledJensenPolynomial_of_summable
    (gamma : ℕ → ℝ) (x : ℝ)
    (hsum : Summable (fun k => ‖gamma k‖ * ‖x‖ ^ k / k.factorial)) :
    Tendsto (fun n => (rescaledJensenPolynomial n gamma).eval x) atTop
      (𝓝 (∑' k, (gamma k / k.factorial) * x ^ k)) := by
  have hlim := tendsto_tsum_of_dominated_convergence hsum
    (fun k => (tendsto_coeff_rescaledJensenPolynomial gamma k).mul_const (x ^ k))
    (Filter.Eventually.of_forall fun n k => by
      calc
        ‖(rescaledJensenPolynomial n gamma).coeff k * x ^ k‖ =
            ‖(rescaledJensenPolynomial n gamma).coeff k‖ * ‖x‖ ^ k := by
          rw [norm_mul, norm_pow]
        _ ≤ (‖gamma k‖ / k.factorial) * ‖x‖ ^ k :=
          mul_le_mul_of_nonneg_right (norm_coeff_rescaledJensenPolynomial_le n k gamma)
            (pow_nonneg (norm_nonneg _) _)
        _ = ‖gamma k‖ * ‖x‖ ^ k / k.factorial := by ring)
  simpa only [tsum_coeff_mul_pow_eq_eval] using hlim

/-- Rescaled Jensen polynomials converge coefficientwise to the exponential
generating coefficients of `gamma`. -/
theorem tendsto_rescaledJensenPolynomial_coeffwise (gamma : ℕ → ℝ) :
    Tendsto (fun n k => (rescaledJensenPolynomial n gamma).coeff k) atTop
      (𝓝 fun k => gamma k / k.factorial) := by
  rw [tendsto_pi_nhds]
  intro k
  exact tendsto_coeff_rescaledJensenPolynomial gamma k

end RealRooted
