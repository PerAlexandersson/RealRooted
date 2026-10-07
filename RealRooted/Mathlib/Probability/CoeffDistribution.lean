import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Harper's central limit theorem for real-rooted polynomials

For a real polynomial `p` with nonnegative coefficients and `p ≠ 0`, the coefficient
distribution of `p` is the probability measure on `ℝ` giving mass `p.coeff k / p.eval 1` to `k`.

If `p` is moreover real-rooted (`p.Splits`), its roots `a` satisfy `a ≤ 0`, and
`p(z) / p(1) = ∏ₐ ((1 - qₐ) + qₐ z)` with `qₐ = (1 - a)⁻¹ ∈ (0, 1]`; that is, the coefficient
distribution is the law of a sum of independent Bernoulli variables.  In particular the mean is
`∑ qₐ` and the variance is `∑ qₐ (1 - qₐ)`.

**Harper's theorem** (Harper 1967, Bender 1973): if `P n` are real-rooted with nonnegative
coefficients and the variances of their coefficient distributions tend to infinity, then the
standardized coefficient distributions converge weakly to the standard Gaussian.

## Main declarations

* `Polynomial.coeffMeasure`, `Polynomial.coeffDistribution`: the coefficient distribution.
* `Polynomial.coeffMean`, `Polynomial.coeffVariance`, `Polynomial.coeffStdDev`.
* `Polynomial.standardizedCoeffDistribution`: the pushforward by `x ↦ (x - μ) / σ`.
* `Polynomial.aeval_div_eval_one_eq_prod`: the Bernoulli product factorization.
* `Polynomial.coeffMean_eq_sum`, `Polynomial.coeffVariance_eq_sum`.
* `Polynomial.norm_charFun_standardizedCoeffDistribution_sub_le`: the quantitative estimate
  `‖φₙ(t) - exp (-t²/2)‖ ≤ 2 |t|³ / σ` for `|t| ≤ σ`.
* `Polynomial.tendsto_standardizedCoeffDistribution`: Harper's central limit theorem.
-/

open MeasureTheory ProbabilityTheory Filter Topology Complex

noncomputable section

namespace Polynomial

/-! ### The coefficient distribution -/

/-- The mean `p'(1) / p(1)` of the coefficient distribution of `p`. -/
def coeffMean (p : ℝ[X]) : ℝ := p.derivative.eval 1 / p.eval 1

/-- The variance `p''(1) / p(1) + μ - μ ^ 2` of the coefficient distribution of `p`,
where `μ = p.coeffMean`. -/
def coeffVariance (p : ℝ[X]) : ℝ :=
  p.derivative.derivative.eval 1 / p.eval 1 + p.coeffMean - p.coeffMean ^ 2

/-- The standard deviation of the coefficient distribution of `p`. -/
def coeffStdDev (p : ℝ[X]) : ℝ := √p.coeffVariance

/-- The coefficient measure of `p`: the mass `p.coeff k / p.eval 1` placed at each `k`. -/
def coeffMeasure (p : ℝ[X]) : Measure ℝ :=
  ∑ k ∈ Finset.range (p.natDegree + 1),
    ENNReal.ofReal (p.coeff k / p.eval 1) • Measure.dirac (k : ℝ)

theorem eval_pos_of_coeff_nonneg {p : ℝ[X]} (hnn : ∀ k, 0 ≤ p.coeff k) (hp : p ≠ 0) {x : ℝ}
    (hx : 0 < x) : 0 < p.eval x := by
  rw [eval_eq_sum_range]
  refine Finset.sum_pos' (fun k _ => mul_nonneg (hnn k) (pow_nonneg hx.le k))
    ⟨p.natDegree, by simp, mul_pos ?_ (pow_pos hx _)⟩
  rw [coeff_natDegree]
  exact lt_of_le_of_ne (by simpa using hnn p.natDegree) (leadingCoeff_ne_zero.mpr hp).symm

theorem eval_one_nonneg_of_coeff_nonneg {p : ℝ[X]} (hnn : ∀ k, 0 ≤ p.coeff k) :
    0 ≤ p.eval 1 := by
  rw [eval_eq_sum_range]
  exact Finset.sum_nonneg fun k _ => by simpa using hnn k

theorem isProbabilityMeasure_coeffMeasure {p : ℝ[X]} (hnn : ∀ k, 0 ≤ p.coeff k)
    (hp : p ≠ 0) : IsProbabilityMeasure p.coeffMeasure := by
  have h1 := eval_pos_of_coeff_nonneg hnn hp one_pos
  constructor
  simp only [coeffMeasure, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => div_nonneg (hnn k) h1.le), ← Finset.sum_div]
  have hsum : ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k = p.eval 1 := by
    simp [eval_eq_sum_range]
  rw [hsum, div_self h1.ne', ENNReal.ofReal_one]

open scoped Classical in
/-- The coefficient distribution of `p` as a probability measure on `ℝ`.  When `p = 0` or `p` has
a negative coefficient this is the junk value `dirac 0`. -/
def coeffDistribution (p : ℝ[X]) : ProbabilityMeasure ℝ :=
  if h : (∀ k, 0 ≤ p.coeff k) ∧ p ≠ 0 then
    ⟨p.coeffMeasure, isProbabilityMeasure_coeffMeasure h.1 h.2⟩
  else ⟨Measure.dirac 0, inferInstance⟩

/-- The standardized coefficient distribution of `p`: the law of `(K - μ) / σ` where `K` has the
coefficient distribution of `p`, `μ = p.coeffMean` and `σ = p.coeffStdDev`. -/
def standardizedCoeffDistribution (p : ℝ[X]) : ProbabilityMeasure ℝ :=
  p.coeffDistribution.map fun x => (x - p.coeffMean) / p.coeffStdDev

theorem coeffDistribution_toMeasure {p : ℝ[X]} (hnn : ∀ k, 0 ≤ p.coeff k) (hp : p ≠ 0) :
    (p.coeffDistribution : Measure ℝ) = p.coeffMeasure := by
  simp [coeffDistribution, hnn, hp]

theorem integral_coeffMeasure {p : ℝ[X]} (hnn : ∀ k, 0 ≤ p.coeff k) (g : ℝ → ℂ) :
    ∫ x, g x ∂p.coeffMeasure =
      ∑ k ∈ Finset.range (p.natDegree + 1), ((p.coeff k / p.eval 1 : ℝ) : ℂ) * g k := by
  have h1 := eval_one_nonneg_of_coeff_nonneg hnn
  rw [coeffMeasure, integral_finsetSum_measure]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (div_nonneg (hnn k) h1),
      Complex.real_smul]
  · exact fun k _ => (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top

/-- The characteristic function of the standardized coefficient distribution. -/
theorem charFun_standardizedCoeffDistribution {p : ℝ[X]} (hnn : ∀ k, 0 ≤ p.coeff k)
    (hp : p ≠ 0) (t : ℝ) :
    charFun (p.standardizedCoeffDistribution : Measure ℝ) t =
      cexp (-(t * p.coeffMean / p.coeffStdDev : ℝ) * I) *
        aeval (cexp ((t / p.coeffStdDev : ℝ) * I)) p / p.eval 1 := by
  rw [standardizedCoeffDistribution, ProbabilityMeasure.toMeasure_map,
    coeffDistribution_toMeasure hnn hp, charFun_apply_real,
    integral_map (by fun_prop) (by fun_prop), integral_coeffMeasure hnn, aeval_eq_sum_range,
    Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Complex.exp_nat_mul, Complex.real_smul, mul_comm (p.coeff k : ℂ), mul_assoc,
    ← mul_assoc _ _ (p.coeff k : ℂ), ← Complex.exp_add]
  push_cast
  ring_nf

/-! ### The Bernoulli factorization -/

theorem roots_nonpos_of_coeff_nonneg {p : ℝ[X]} (hnn : ∀ k, 0 ≤ p.coeff k) {a : ℝ}
    (ha : a ∈ p.roots) : a ≤ 0 := by
  have hp : p ≠ 0 := (mem_roots'.mp ha).1
  by_contra h
  have := eval_pos_of_coeff_nonneg hnn hp (not_le.mp h)
  rw [(mem_roots hp).mp ha] at this
  exact lt_irrefl _ this

/-- **Bernoulli factorization.** For a real-rooted polynomial with nonnegative coefficients,
`p(z) / p(1) = ∏ₐ ((1 - qₐ) + qₐ z)` over the roots `a`, where `qₐ = (1 - a)⁻¹`. -/
theorem aeval_div_eval_one_eq_prod {p : ℝ[X]} (hs : p.Splits) (hnn : ∀ k, 0 ≤ p.coeff k)
    (hp : p ≠ 0) (z : ℂ) :
    aeval z p / p.eval 1 =
      (p.roots.map fun a => ((1 - (1 - a)⁻¹ : ℝ) : ℂ) + ((1 - a)⁻¹ : ℝ) * z).prod := by
  have hroot : ∀ a ∈ p.roots, (1 - a : ℂ) ≠ 0 := fun a ha => by
    have := roots_nonpos_of_coeff_nonneg hnn ha
    exact_mod_cast (show (1 - a : ℝ) ≠ 0 by linarith)
  have hlc : (p.leadingCoeff : ℂ) ≠ 0 := by exact_mod_cast leadingCoeff_ne_zero.mpr hp
  have hval : ∀ w : ℂ,
      aeval w p = p.leadingCoeff * (p.roots.map fun a : ℝ => w - (a : ℂ)).prod := by
    intro w
    conv_lhs => rw [hs.eq_prod_roots]
    rw [map_mul, aeval_C, map_multiset_prod, Multiset.map_map]
    simp
  have h1 : ((p.eval 1 : ℝ) : ℂ) = aeval (1 : ℂ) p := by
    simpa using (aeval_algebraMap_apply_eq_algebraMap_eval (A := ℂ) (1 : ℝ) p).symm
  rw [h1, hval, hval, mul_div_mul_left _ _ hlc, ← Multiset.prod_map_div]
  refine congrArg _ (Multiset.map_congr rfl fun a ha => ?_)
  push_cast
  field_simp [hroot a ha]
  ring

/-! ### Mean and variance -/

theorem coeffMean_mul {f g : ℝ[X]} (hf : f.eval 1 ≠ 0) (hg : g.eval 1 ≠ 0) :
    (f * g).coeffMean = f.coeffMean + g.coeffMean := by
  simp only [coeffMean, derivative_mul, eval_add, eval_mul]
  field_simp

theorem coeffVariance_mul {f g : ℝ[X]} (hf : f.eval 1 ≠ 0) (hg : g.eval 1 ≠ 0) :
    (f * g).coeffVariance = f.coeffVariance + g.coeffVariance := by
  simp only [coeffVariance, coeffMean_mul hf hg]
  simp only [coeffMean, derivative_mul, derivative_add, eval_add, eval_mul]
  field_simp
  ring

theorem coeffMean_X_sub_C (a : ℝ) : (X - C a).coeffMean = (1 - a)⁻¹ := by
  simp [coeffMean]

theorem coeffVariance_X_sub_C (a : ℝ) :
    (X - C a).coeffVariance = (1 - a)⁻¹ * (1 - (1 - a)⁻¹) := by
  simp only [coeffVariance, coeffMean_X_sub_C, derivative_sub, derivative_X, derivative_C,
    sub_zero, derivative_one, eval_zero, zero_div]
  ring

private theorem eval_one_C_mul_prod_ne_zero {c : ℝ} (hc : c ≠ 0) {s : Multiset ℝ}
    (hs : ∀ a ∈ s, a ≤ 0) : (C c * (s.map fun a => X - C a).prod).eval 1 ≠ 0 := by
  rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
  refine mul_ne_zero hc (Multiset.prod_ne_zero fun h => ?_)
  obtain ⟨a, ha, h0⟩ := Multiset.mem_map.mp h
  simp only [Function.comp_apply, eval_sub, eval_X, eval_C] at h0
  linarith [hs a ha]

private theorem eval_one_X_sub_C_ne_zero {a : ℝ} (ha : a ≤ 0) : (X - C a).eval 1 ≠ 0 := by
  rw [eval_sub, eval_X, eval_C]
  exact sub_ne_zero.mpr (show a < 1 by linarith).ne'

theorem coeffMean_C_mul_prod {c : ℝ} (hc : c ≠ 0) {s : Multiset ℝ} (hs : ∀ a ∈ s, a ≤ 0) :
    (C c * (s.map fun a => X - C a).prod).coeffMean = (s.map fun a => (1 - a)⁻¹).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [coeffMean]
  | cons a s ih =>
    have hs' : ∀ b ∈ s, b ≤ 0 := fun b hb => hs b (Multiset.mem_cons_of_mem hb)
    rw [Multiset.map_cons, Multiset.prod_cons, mul_left_comm,
      coeffMean_mul (eval_one_X_sub_C_ne_zero (hs a (Multiset.mem_cons_self a s)))
        (eval_one_C_mul_prod_ne_zero hc hs'), ih hs', Multiset.map_cons, Multiset.sum_cons,
      coeffMean_X_sub_C]

theorem coeffVariance_C_mul_prod {c : ℝ} (hc : c ≠ 0) {s : Multiset ℝ} (hs : ∀ a ∈ s, a ≤ 0) :
    (C c * (s.map fun a => X - C a).prod).coeffVariance =
      (s.map fun a => (1 - a)⁻¹ * (1 - (1 - a)⁻¹)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [coeffVariance, coeffMean]
  | cons a s ih =>
    have hs' : ∀ b ∈ s, b ≤ 0 := fun b hb => hs b (Multiset.mem_cons_of_mem hb)
    rw [Multiset.map_cons, Multiset.prod_cons, mul_left_comm,
      coeffVariance_mul (eval_one_X_sub_C_ne_zero (hs a (Multiset.mem_cons_self a s)))
        (eval_one_C_mul_prod_ne_zero hc hs'), ih hs', Multiset.map_cons, Multiset.sum_cons,
      coeffVariance_X_sub_C]

/-- The mean of the coefficient distribution of a real-rooted polynomial with nonnegative
coefficients is `∑ₐ qₐ`, where `qₐ = (1 - a)⁻¹` over the roots `a`. -/
theorem coeffMean_eq_sum {p : ℝ[X]} (hs : p.Splits) (hnn : ∀ k, 0 ≤ p.coeff k) (hp : p ≠ 0) :
    p.coeffMean = (p.roots.map fun a => (1 - a)⁻¹).sum := by
  have h := coeffMean_C_mul_prod (leadingCoeff_ne_zero.mpr hp) fun a ha =>
    roots_nonpos_of_coeff_nonneg hnn ha
  rwa [← hs.eq_prod_roots] at h

/-- The variance of the coefficient distribution of a real-rooted polynomial with nonnegative
coefficients is `∑ₐ qₐ (1 - qₐ)`, where `qₐ = (1 - a)⁻¹` over the roots `a`. -/
theorem coeffVariance_eq_sum {p : ℝ[X]} (hs : p.Splits) (hnn : ∀ k, 0 ≤ p.coeff k)
    (hp : p ≠ 0) :
    p.coeffVariance = (p.roots.map fun a => (1 - a)⁻¹ * (1 - (1 - a)⁻¹)).sum := by
  have h := coeffVariance_C_mul_prod (leadingCoeff_ne_zero.mpr hp) fun a ha =>
    roots_nonpos_of_coeff_nonneg hnn ha
  rwa [← hs.eq_prod_roots] at h

/-! ### The characteristic-function estimate -/

private theorem norm_cexp_mul_I_sub_le {y : ℝ} (hy : |y| ≤ 1) :
    ‖cexp (y * I) - (1 + y * I - y ^ 2 / 2)‖ ≤ |y| ^ 3 := by
  have hn : ‖(y * I : ℂ)‖ = |y| := by simp
  have hb := Complex.exp_bound (x := y * I) (hn ▸ hy) (n := 3) (by norm_num)
  have hsum : ∑ m ∈ Finset.range 3, (y * I : ℂ) ^ m / m.factorial = 1 + y * I - y ^ 2 / 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    norm_num [Nat.factorial]
    linear_combination (y : ℂ) ^ 2 / 2 * I_sq
  have hc : ((Nat.succ 3 : ℕ) : ℝ) * (((Nat.factorial 3 : ℕ) : ℝ) * ((3 : ℕ) : ℝ))⁻¹ = 2 / 9 := by
    norm_num [Nat.factorial]
  rw [hsum, hn, hc] at hb
  nlinarith [pow_nonneg (abs_nonneg y) 3]

private theorem abs_one_sub_sub_exp_neg_le {x : ℝ} (hx : |x| ≤ 1) :
    |1 - x - Real.exp (-x)| ≤ x ^ 2 := by
  have h := Real.abs_exp_sub_one_sub_id_le (x := -x) (by rwa [abs_neg])
  have e : 1 - x - Real.exp (-x) = -(Real.exp (-x) - 1 - -x) := by ring
  rwa [e, abs_neg, ← neg_sq]

/-- The characteristic-function estimate for one centred Bernoulli factor: if `0 ≤ q ≤ 1` and
`|s| ≤ 1`, then `(1 - q + q e^{is}) e^{-isq}` differs from `exp (-q (1 - q) s² / 2)` by at most
`2 q (1 - q) |s|³`. -/
theorem norm_bernoulli_charFun_sub_le {q s : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hs : |s| ≤ 1) :
    ‖(((1 - q : ℝ) : ℂ) + (q : ℂ) * cexp ((s : ℂ) * I)) * cexp (((-s * q : ℝ) : ℂ) * I) -
        cexp ((-(q * (1 - q) * s ^ 2 / 2) : ℝ))‖ ≤ 2 * (q * (1 - q) * |s| ^ 3) := by
  have h1q : 0 ≤ 1 - q := by linarith
  have hsa := abs_nonneg s
  have hsq : |-s * q| ≤ 1 := by
    rw [abs_mul, abs_neg, abs_of_nonneg hq0]
    nlinarith
  have hsq' : |s * (1 - q)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg h1q]
    nlinarith
  have e1 := norm_cexp_mul_I_sub_le hsq
  have e2 := norm_cexp_mul_I_sub_le hsq'
  have hs2 : s ^ 2 = |s| ^ 2 := (sq_abs s).symm
  have hq4 : q * (1 - q) ≤ 1 / 4 := by nlinarith [sq_nonneg (q - 1 / 2)]
  have hs1 : |s| ^ 2 ≤ 1 := by nlinarith
  have hx : |q * (1 - q) * s ^ 2 / 2| ≤ 1 := by
    rw [abs_of_nonneg (by positivity), hs2]
    linarith [mul_le_mul hq4 hs1 (sq_nonneg _) (by norm_num)]
  have e3 := abs_one_sub_sub_exp_neg_le hx
  have hB : cexp ((s : ℂ) * I) * cexp (((-s * q : ℝ) : ℂ) * I) =
      cexp (((s * (1 - q) : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hsplit : (((1 - q : ℝ) : ℂ) + (q : ℂ) * cexp ((s : ℂ) * I)) *
        cexp (((-s * q : ℝ) : ℂ) * I) - cexp ((-(q * (1 - q) * s ^ 2 / 2) : ℝ)) =
      ((1 - q : ℝ) : ℂ) * (cexp (((-s * q : ℝ) : ℂ) * I) -
          (1 + ((-s * q : ℝ) : ℂ) * I - ((-s * q : ℝ) : ℂ) ^ 2 / 2)) +
        (q : ℂ) * (cexp (((s * (1 - q) : ℝ) : ℂ) * I) -
          (1 + ((s * (1 - q) : ℝ) : ℂ) * I - ((s * (1 - q) : ℝ) : ℂ) ^ 2 / 2)) +
        ((1 - q * (1 - q) * s ^ 2 / 2 - Real.exp (-(q * (1 - q) * s ^ 2 / 2)) : ℝ) : ℂ) := by
    rw [add_mul, mul_assoc, hB]
    push_cast
    ring
  have hkey : (1 - q) * |-s * q| ^ 3 + q * |s * (1 - q)| ^ 3 + (q * (1 - q) * s ^ 2 / 2) ^ 2 =
      q * (1 - q) * |s| ^ 3 * (1 - 2 * (q * (1 - q)) + q * (1 - q) * |s| / 4) := by
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hq0, abs_of_nonneg h1q, hs2]
    ring
  calc _ = _ := by rw [hsplit]
    _ ≤ _ := norm_add₃_le
    _ ≤ (1 - q) * |-s * q| ^ 3 + q * |s * (1 - q)| ^ 3 + (q * (1 - q) * s ^ 2 / 2) ^ 2 := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg h1q, abs_of_nonneg hq0]
      gcongr
    _ ≤ _ := by
      rw [hkey]
      have hw : 0 ≤ q * (1 - q) * |s| ^ 3 := by positivity
      have hst : 1 - 2 * (q * (1 - q)) + q * (1 - q) * |s| / 4 ≤ 2 := by
        nlinarith [mul_nonneg hq0 h1q, mul_le_mul hq4 hs hsa (by norm_num)]
      linarith [mul_le_mul_of_nonneg_left hst hw]

private theorem norm_multiset_prod_le_one {ι : Type*} (s : Multiset ι) (f : ι → ℂ)
    (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) : ‖(s.map f).prod‖ ≤ 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, norm_mul]
    exact (mul_le_mul (hf a (Multiset.mem_cons_self a s))
      (ih fun i hi => hf i (Multiset.mem_cons_of_mem hi)) (norm_nonneg _) zero_le_one).trans_eq
      (one_mul 1)

/-- For complex numbers of norm at most one, `‖∏ fᵢ - ∏ gᵢ‖ ≤ ∑ ‖fᵢ - gᵢ‖`. -/
theorem norm_multiset_prod_sub_prod_le {ι : Type*} (s : Multiset ι) (f g : ι → ℂ)
    (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) (hg : ∀ i ∈ s, ‖g i‖ ≤ 1) :
    ‖(s.map f).prod - (s.map g).prod‖ ≤ (s.map fun i => ‖f i - g i‖).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ih' := ih (fun i hi => hf i (Multiset.mem_cons_of_mem hi))
      (fun i hi => hg i (Multiset.mem_cons_of_mem hi))
    have hfa := hf a (Multiset.mem_cons_self a s)
    have hG := norm_multiset_prod_le_one s g fun i hi => hg i (Multiset.mem_cons_of_mem hi)
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons,
      Multiset.map_cons, Multiset.sum_cons]
    calc ‖f a * (s.map f).prod - g a * (s.map g).prod‖
        = ‖f a * ((s.map f).prod - (s.map g).prod) + (f a - g a) * (s.map g).prod‖ := by
          congr 1
          ring
      _ ≤ ‖f a‖ * ‖(s.map f).prod - (s.map g).prod‖ + ‖f a - g a‖ * ‖(s.map g).prod‖ := by
          rw [← norm_mul, ← norm_mul]
          exact norm_add_le _ _
      _ ≤ 1 * (s.map fun i => ‖f i - g i‖).sum + ‖f a - g a‖ * 1 := by gcongr
      _ = _ := by ring

private theorem cexp_multiset_sum_mul {ι : Type*} (s : Multiset ι) (g : ι → ℝ) (c : ℂ) :
    cexp (((s.map g).sum : ℝ) * c) = (s.map fun i => cexp (g i * c)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.map_cons, Multiset.prod_cons, ofReal_add,
      add_mul, Complex.exp_add, ih]

/-- The characteristic function of the standardized coefficient distribution of a real-rooted
polynomial with nonnegative coefficients is a product of characteristic functions of centred
Bernoulli variables with parameters `qₐ = (1 - a)⁻¹`. -/
theorem charFun_standardizedCoeffDistribution_eq_prod {p : ℝ[X]} (hs : p.Splits)
    (hnn : ∀ k, 0 ≤ p.coeff k) (hp : p ≠ 0) (t : ℝ) :
    charFun (p.standardizedCoeffDistribution : Measure ℝ) t =
      (p.roots.map fun a =>
        (((1 - (1 - a)⁻¹ : ℝ) : ℂ) + ((1 - a)⁻¹ : ℝ) * cexp ((t / p.coeffStdDev : ℝ) * I)) *
          cexp (((-(t / p.coeffStdDev) * (1 - a)⁻¹ : ℝ) : ℂ) * I)).prod := by
  rw [charFun_standardizedCoeffDistribution hnn hp, mul_div_assoc,
    aeval_div_eval_one_eq_prod hs hnn hp, Multiset.prod_map_mul, mul_comm (cexp _),
    ← cexp_multiset_sum_mul, coeffMean_eq_sum hs hnn hp, Multiset.sum_map_mul_left]
  congr 3
  push_cast
  ring

/-- **Quantitative characteristic-function estimate.** For a real-rooted polynomial with
nonnegative coefficients and positive variance `σ²`, the characteristic function of its
standardized coefficient distribution satisfies `‖φ(t) - exp (-t² / 2)‖ ≤ 2 |t|³ / σ`
whenever `|t| ≤ σ`. -/
theorem norm_charFun_standardizedCoeffDistribution_sub_le {p : ℝ[X]} (hs : p.Splits)
    (hnn : ∀ k, 0 ≤ p.coeff k) (hvar : 0 < p.coeffVariance) {t : ℝ}
    (ht : |t| ≤ p.coeffStdDev) :
    ‖charFun (p.standardizedCoeffDistribution : Measure ℝ) t - cexp ((-(t ^ 2 / 2) : ℝ))‖ ≤
      2 * |t| ^ 3 / p.coeffStdDev := by
  have hp : p ≠ 0 := by
    rintro rfl
    simp [coeffVariance, coeffMean] at hvar
  have hσ : 0 < p.coeffStdDev := Real.sqrt_pos.mpr hvar
  have hσ2 : p.coeffStdDev ^ 2 = p.coeffVariance := Real.sq_sqrt hvar.le
  have hs1 : |t / p.coeffStdDev| ≤ 1 := by
    rw [abs_div, abs_of_pos hσ]
    exact (div_le_one hσ).mpr ht
  have hq : ∀ a ∈ p.roots, 0 ≤ (1 - a)⁻¹ ∧ (1 - a)⁻¹ ≤ 1 := fun a ha => by
    have := roots_nonpos_of_coeff_nonneg hnn ha
    exact ⟨inv_nonneg.mpr (by linarith), inv_le_one_of_one_le₀ (by linarith)⟩
  have hsum : (p.roots.map fun a =>
      -((1 - a)⁻¹ * (1 - (1 - a)⁻¹) * (t / p.coeffStdDev) ^ 2 / 2)).sum = -(t ^ 2 / 2) := by
    have h := Multiset.sum_map_mul_right (s := p.roots)
      (f := fun a => (1 - a)⁻¹ * (1 - (1 - a)⁻¹)) (a := -((t / p.coeffStdDev) ^ 2 / 2))
    rw [← coeffVariance_eq_sum hs hnn hp, ← hσ2] at h
    rw [Multiset.map_congr rfl fun a _ => (show
        -((1 - a)⁻¹ * (1 - (1 - a)⁻¹) * (t / p.coeffStdDev) ^ 2 / 2) =
          (1 - a)⁻¹ * (1 - (1 - a)⁻¹) * -((t / p.coeffStdDev) ^ 2 / 2) by ring), h]
    field_simp
  have hgauss : cexp ((-(t ^ 2 / 2) : ℝ)) = (p.roots.map fun a =>
      cexp ((-((1 - a)⁻¹ * (1 - (1 - a)⁻¹) * (t / p.coeffStdDev) ^ 2 / 2) : ℝ))).prod := by
    have h := cexp_multiset_sum_mul p.roots
      (fun a => -((1 - a)⁻¹ * (1 - (1 - a)⁻¹) * (t / p.coeffStdDev) ^ 2 / 2)) 1
    simp only [mul_one, hsum] at h
    exact h
  rw [charFun_standardizedCoeffDistribution_eq_prod hs hnn hp, hgauss]
  refine (norm_multiset_prod_sub_prod_le _ _ _ (fun a ha => ?_) (fun a ha => ?_)).trans ?_
  · obtain ⟨h0, h1⟩ := hq a ha
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0, abs_of_nonneg (by linarith)]
    linarith
  · obtain ⟨h0, h1⟩ := hq a ha
    have : 0 ≤ 1 - (1 - a)⁻¹ := by linarith
    rw [Complex.norm_exp_ofReal, Real.exp_le_one_iff, neg_nonpos]
    positivity
  · calc _ ≤ (p.roots.map fun a =>
          2 * |t / p.coeffStdDev| ^ 3 * ((1 - a)⁻¹ * (1 - (1 - a)⁻¹))).sum :=
          Multiset.sum_map_le_sum_map _ _ fun a ha =>
            (norm_bernoulli_charFun_sub_le (hq a ha).1 (hq a ha).2 hs1).trans_eq (by ring)
      _ = 2 * |t| ^ 3 / p.coeffStdDev := by
        rw [Multiset.sum_map_mul_left, ← coeffVariance_eq_sum hs hnn hp, ← hσ2, abs_div,
          abs_of_pos hσ]
        field_simp

/-! ### Harper's central limit theorem -/

/-- **Harper's central limit theorem** (Harper 1967; Bender 1973).  If the polynomials `P n` are
real-rooted with nonnegative coefficients and the variances of their coefficient distributions
tend to infinity, then the standardized coefficient distributions converge weakly to the standard
Gaussian distribution. -/
theorem tendsto_standardizedCoeffDistribution {P : ℕ → ℝ[X]} (hs : ∀ n, (P n).Splits)
    (hnn : ∀ n k, 0 ≤ (P n).coeff k)
    (hvar : Tendsto (fun n => (P n).coeffVariance) atTop atTop) :
    Tendsto (fun n => (P n).standardizedCoeffDistribution) atTop
      (𝓝 ⟨gaussianReal 0 1, inferInstance⟩) := by
  refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t => ?_
  have hσ : Tendsto (fun n => (P n).coeffStdDev) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hvar
  have hg : charFun (gaussianReal 0 1) t = cexp ((-(t ^ 2 / 2) : ℝ)) := by
    rw [charFun_gaussianReal]
    congr 1
    push_cast
    ring
  change Tendsto _ atTop (𝓝 (charFun (gaussianReal 0 1) t))
  rw [hg, ← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_ ((tendsto_const_nhds (x := 2 * |t| ^ 3)).div_atTop hσ)
  filter_upwards [hvar.eventually_gt_atTop 0, hσ.eventually_ge_atTop |t|] with n h1 h2
  exact norm_charFun_standardizedCoeffDistribution_sub_le (hs n) (hnn n) h1 h2

end Polynomial
