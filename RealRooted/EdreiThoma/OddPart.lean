module

public import RealRooted.Mathlib.Analysis.Complex.BorelGrowth

@[expose] public section

section Quotient_part


/-!
# Proximity of `e^G` when `e^G · M = K` with `M, K` entire

This is where the first main theorem of value distribution theory (as in Mathlib) is used.
-/


open Complex Real Filter ValueDistribution

noncomputable section

namespace RealRooted.EdreiThoma

private theorem posLog_norm_exp (w : ℂ) : log⁺ ‖Complex.exp w‖ = max w.re 0 := by
  rw [Complex.norm_exp]
  simp [Real.posLog, Real.log_exp, max_comm]

/-- If `e^G · M = K` with `M, K` entire and `M ≢ 0`, then
`posMean G r ≤ m(r, K) + m(r, M) + C` for `r ≥ 1`. -/
private theorem posMean_le_of_exp_mul_eq {G K M : ℂ → ℂ}
    (hK : Differentiable ℂ K) (hM : Differentiable ℂ M) {x₀ : ℂ} (hx₀ : M x₀ ≠ 0)
    (heq : ∀ z, Complex.exp (G z) * M z = K z) :
    ∃ C, ∀ r, 1 ≤ r → posMean G r ≤ circleAverage (fun z => log⁺ ‖K z‖) 0 r +
      circleAverage (fun z => log⁺ ‖M z‖) 0 r + C := by
  have hMa : AnalyticOnNhd ℂ M Set.univ := fun z _ => hM.analyticAt z
  have hKm : Meromorphic K := fun z => (hK.analyticAt z).meromorphicAt
  have hMm : Meromorphic M := fun z => (hM.analyticAt z).meromorphicAt
  refine ⟨-Real.log ‖meromorphicTrailingCoeffAt M 0‖, fun r hr => ?_⟩
  have hr0 : r ≠ 0 := by positivity
  have h1 : posMean G r = proximity (fun z => Complex.exp (G z)) ⊤ r := by
    rw [proximity_top]; simp only [posLog_norm_exp]; rfl
  have hcod : (fun z => Complex.exp (G z)) =ᶠ[codiscrete ℂ] K * M⁻¹ := by
    filter_upwards [hMa.preimage_zero_mem_codiscrete hx₀] with z hz
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] at hz
    simp only [Pi.mul_apply, Pi.inv_apply, ← heq z]
    field_simp
  have h2 := proximity_congr_codiscrete (a := ⊤) hcod hr0
  have h3 := proximity_mul_top_le hKm hMm.inv r
  have h4 : proximity M⁻¹ ⊤ r ≤ characteristic M⁻¹ ⊤ r := by
    unfold characteristic
    simp only [Pi.add_apply, le_add_iff_nonneg_right]
    exact logCounting_nonneg hr
  have h5 := characteristic_sub_characteristic_inv_of_ne_zero hMm hr0
  have h6 : logCounting M ⊤ = 0 := by
    rw [logCounting_top]
    have : (MeromorphicOn.divisor M Set.univ)⁻ = 0 :=
      negPart_eq_zero.mpr (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hMa)
    rw [this, map_zero]
  have h7 : characteristic M ⊤ r = proximity M ⊤ r := by
    unfold characteristic; simp [h6]
  have h8 : proximity K ⊤ r = circleAverage (fun z => log⁺ ‖K z‖) 0 r := by
    rw [proximity_top]
  rw [h1, h2]
  simp only [Pi.add_apply] at h3
  rw [proximity_top] at h7
  linarith

end RealRooted.EdreiThoma
end
end Quotient_part

section KeyGrowth_part


/-!
# The key growth estimate (an elementary substitute for the second main theorem)

Suppose `g, F, P, Q` are entire, `P(0) = Q(0) = 1`, `log|P|, log|Q| ≤ C (1 + |z|)^2`, and
`e^{g/2} P(z) + e^{-g/2} P(-z) = 2 e^{F} Q(z)`.  Then `posMean g r = O((1 + r)^2)`.

Proof: a Wronskian elimination gives `e^g M = K` with
`M = Q (g'P/2 + P') - (F'Q + Q') P`, `K = (F'Q + Q') P(-z) - Q (-P'(-z) - g' P(-z)/2)`;
the first main theorem bounds `posMean g` by `m(r, K) + m(r, M)`, which only involve
`log⁺ |g'|`, `log⁺ |F'|` (bounded through Cauchy estimates by `log` of `posMean g`, `posMean F`
on a larger circle) and the growth of `P, Q`.  Borel's lemma absorbs the logarithmic terms.
-/


open Complex Real Filter Topology

noncomputable section

namespace RealRooted.EdreiThoma

private theorem posLog_le_of_le_exp {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : x ≤ Real.exp y) :
    log⁺ x ≤ y := by
  rcases hx.eq_or_lt with hx | hx
  · rw [← hx]; simpa using hy
  · simp only [Real.posLog]
    exact max_le hy ((Real.log_le_log hx h).trans (le_of_eq (Real.log_exp y)))

private theorem circleAverage_posLog_le {K : ℂ → ℂ} (hK : Differentiable ℂ K)
    {r B : ℝ} (hr : 0 < r) (h : ∀ z : ℂ, ‖z‖ = r → log⁺ ‖K z‖ ≤ B) :
    circleAverage (fun z => log⁺ ‖K z‖) 0 r ≤ B := by
  apply circleAverage_mono_on_of_le_circle
  · exact MeromorphicOn.circleIntegrable_posLog_norm
      (fun z _ => (hK.analyticAt z).meromorphicAt)
  · intro z hz
    rw [mem_sphere_zero_iff_norm, abs_of_pos hr] at hz
    exact h z hz

private theorem norm_deriv_le_exp {P : ℂ → ℂ} (hP : Differentiable ℂ P) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ z, ‖P z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ 2)) (z : ℂ) :
    ‖deriv P z‖ ≤ Real.exp (C * (2 + ‖z‖) ^ 2) := by
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := z) (R := 1)
    (C := Real.exp (C * (2 + ‖z‖) ^ 2)) one_pos hP.diffContOnCl ?_
  · simpa using this
  · intro w hw
    rw [mem_sphere_iff_norm] at hw
    refine (hb w).trans ?_
    have : 1 + ‖w‖ ≤ 2 + ‖z‖ := by
      have := norm_sub_norm_le w z
      linarith
    exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) this 2) hC)

private theorem posMean_bdd {g : ℂ → ℂ} (hg : Differentiable ℂ g) (R : ℝ) :
    ∃ B, ∀ r ∈ Set.Ioc 0 R, posMean g r ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    hg.continuous.continuousOn
  refine ⟨max B 0, fun r hr => ?_⟩
  apply circleAverage_mono_on_of_le_circle
  · exact (continuous_re.comp hg.continuous |>.max continuous_const).continuousOn.circleIntegrable'
  · intro z hz
    rw [mem_sphere_zero_iff_norm, abs_of_pos hr.1] at hz
    have hzR : z ∈ Metric.closedBall (0 : ℂ) R := by
      rw [mem_closedBall_zero_iff, hz]; exact hr.2
    have := hB z hzR
    apply max_le_max _ le_rfl
    exact (re_le_norm _).trans this

private theorem posLog_norm_add_le (a b : ℂ) :
    log⁺ ‖a + b‖ ≤ Real.log 2 + log⁺ ‖a‖ + log⁺ ‖b‖ :=
  (posLog_le_posLog (by linarith [norm_nonneg (a + b)]) (norm_add_le a b)).trans posLog_add

private theorem posLog_norm_mul_le (a b : ℂ) :
    log⁺ ‖a * b‖ ≤ log⁺ ‖a‖ + log⁺ ‖b‖ := by
  rw [norm_mul]; exact posLog_mul

private theorem posLog_norm_le_of_exp_bound {P : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ z, ‖P z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ 2)) (z : ℂ) :
    log⁺ ‖P z‖ ≤ C * (1 + ‖z‖) ^ 2 :=
  posLog_le_of_le_exp (norm_nonneg _) (by positivity) (hb z)

private theorem max_half_add_max_neg_half (x : ℝ) : max (x / 2) 0 + max (-x / 2) 0 = |x| / 2 := by
  rcases le_total x 0 with h | h
  · rw [max_eq_right (by linarith), max_eq_left (by linarith), abs_of_nonpos h]; ring
  · rw [max_eq_left (by linarith), max_eq_right (by linarith), abs_of_nonneg h]; ring

/-- Step 1: the even part `F` is controlled by `g`. -/
private theorem posMean_F_le {g F P Q : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hP : Differentiable ℂ P) (hQ : Differentiable ℂ Q) (hQ0 : Q 0 = 1) {C : ℝ} (hC : 0 ≤ C)
    (hPb : ∀ z, ‖P z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ 2))
    (hQb : ∀ z, ‖Q z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ 2))
    (heq : ∀ z, Complex.exp (g z / 2) * P z + Complex.exp (-(g z) / 2) * P (-z) =
      2 * Complex.exp (F z) * Q z) :
    ∃ C₁, 0 ≤ C₁ ∧
      ∀ r, 1 ≤ r → posMean F r ≤ posMean g r + C₁ * (1 + r) ^ 2 := by
  set K : ℂ → ℂ := fun z => Complex.exp (g z / 2) * P z + Complex.exp (-(g z) / 2) * P (-z)
  have hK : Differentiable ℂ K := by
    have : Differentiable ℂ (fun z => P (-z)) := hP.comp differentiable_neg
    fun_prop
  have hM : Differentiable ℂ (fun z => 2 * Q z) := by fun_prop
  obtain ⟨C₀, hC₀⟩ := posMean_le_of_exp_mul_eq (G := F) hK hM (x₀ := 0) (by simp [hQ0])
    (fun z => by simp only [K]; rw [heq z]; ring)
  refine ⟨3 * C + |(g 0).re| + 2 + |C₀|, by positivity, fun r hr => ?_⟩
  have hr0 : 0 < r := by linarith
  have h1 := hC₀ r hr
  have hKb : circleAverage (fun z => log⁺ ‖K z‖) 0 r ≤
      circleAverage (fun z => |(g z).re| / 2 + (2 * C * (1 + r) ^ 2 + Real.log 2)) 0 r := by
    apply circleAverage_mono
    · exact MeromorphicOn.circleIntegrable_posLog_norm
        (fun z _ => (hK.analyticAt z).meromorphicAt)
    · exact circleIntegrable_of_continuous
        (((continuous_abs.comp (continuous_re.comp hg.continuous)).div_const _).add
          continuous_const) r
    · intro z hz
      rw [mem_sphere_zero_iff_norm, abs_of_pos hr0] at hz
      have e1 := posLog_norm_mul_le (Complex.exp (g z / 2)) (P z)
      have e2 := posLog_norm_mul_le (Complex.exp (-(g z) / 2)) (P (-z))
      have e3 := posLog_norm_add_le (Complex.exp (g z / 2) * P z)
        (Complex.exp (-(g z) / 2) * P (-z))
      rw [posLog_norm_exp] at e1 e2
      have p1 := posLog_norm_le_of_exp_bound hC hPb z
      have p2 := posLog_norm_le_of_exp_bound hC hPb (-z)
      rw [norm_neg, hz] at p2
      rw [hz] at p1
      have hre1 : (g z / 2).re = (g z).re / 2 := by simp
      have hre2 : (-(g z) / 2).re = -(g z).re / 2 := by simp
      rw [hre1] at e1; rw [hre2] at e2
      have := max_half_add_max_neg_half (g z).re
      simp only [K]
      linarith
  have hMb : circleAverage (fun z => log⁺ ‖2 * Q z‖) 0 r ≤
      Real.log 2 + C * (1 + r) ^ 2 := by
    apply circleAverage_posLog_le hM hr0
    intro z hz
    have e1 := posLog_norm_mul_le 2 (Q z)
    have p1 := posLog_norm_le_of_exp_bound hC hQb z
    rw [hz] at p1
    have : log⁺ ‖(2:ℂ)‖ = Real.log 2 := by
      rw [posLog_eq_log (by norm_num)]; simp
    linarith
  have hKavg : circleAverage (fun z => |(g z).re| / 2 + (2 * C * (1 + r) ^ 2 + Real.log 2)) 0 r
      = (2 * posMean g r - (g 0).re) / 2 + (2 * C * (1 + r) ^ 2 + Real.log 2) := by
    rw [circleAverage_fun_add, circleAverage_const, ← circleAverage_abs_re hg r]
    · rw [show (fun z => |(g z).re| / 2) = fun z => (1 / 2 : ℝ) • |(g z).re| by
        funext z; simp; ring, circleAverage_fun_smul]
      simp; ring
    · exact circleIntegrable_of_continuous
        ((continuous_abs.comp (continuous_re.comp hg.continuous)).div_const _) r
    · exact circleIntegrable_const _ _ _
  rw [hKavg] at hKb
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hsq : 1 ≤ (1 + r) ^ 2 := by nlinarith
  have ha : -(g 0).re ≤ |(g 0).re| := neg_le_abs _
  have hc : C₀ ≤ |C₀| := le_abs_self _
  have h2 := mul_le_mul_of_nonneg_left hsq (abs_nonneg (g 0).re)
  have h3 := mul_le_mul_of_nonneg_left hsq (abs_nonneg C₀)
  have h4 : |(g 0).re| / 2 ≤ |(g 0).re| := by linarith [abs_nonneg (g 0).re]
  have e : (3 * C + |(g 0).re| + 2 + |C₀|) * (1 + r) ^ 2 =
      3 * C * (1 + r) ^ 2 + |(g 0).re| * (1 + r) ^ 2 +
        2 * (1 + r) ^ 2 + |C₀| * (1 + r) ^ 2 := by ring
  rw [e]
  linarith

/-- The Wronskian-type combination `M`. -/
private def wM (g F P Q : ℂ → ℂ) (z : ℂ) : ℂ :=
  Q z * (deriv g z / 2 * P z + deriv P z) - (deriv F z * Q z + deriv Q z) * P z

/-- The Wronskian-type combination `K`. -/
private def wK (g F P Q : ℂ → ℂ) (z : ℂ) : ℂ :=
  (deriv F z * Q z + deriv Q z) * P (-z) - Q z * (-deriv P (-z) - deriv g z / 2 * P (-z))

/-- Elimination: `e^g · M = K`. -/
private theorem wronskian_identity {g F P Q : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hF : Differentiable ℂ F) (hP : Differentiable ℂ P) (hQ : Differentiable ℂ Q)
    (heq : ∀ z, Complex.exp (g z / 2) * P z + Complex.exp (-(g z) / 2) * P (-z) =
      2 * Complex.exp (F z) * Q z) (z : ℂ) :
    Complex.exp (g z) * wM g F P Q z = wK g F P Q z := by
  unfold wM wK
  have hL : HasDerivAt (fun w => Complex.exp (g w / 2) * P w + Complex.exp (-(g w) / 2) * P (-w))
      (Complex.exp (g z / 2) * (deriv g z / 2) * P z + Complex.exp (g z / 2) * deriv P z +
        (Complex.exp (-(g z) / 2) * (-(deriv g z) / 2) * P (-z) +
          Complex.exp (-(g z) / 2) * (deriv P (-z) * (-1)))) z := by
    have h1 : HasDerivAt (fun w => g w / 2) (deriv g z / 2) z :=
      (hg z).hasDerivAt.div_const 2
    have h2 : HasDerivAt (fun w => -(g w) / 2) (-(deriv g z) / 2) z :=
      (hg z).hasDerivAt.neg.div_const 2
    have h3 : HasDerivAt (fun w => P (-w)) (deriv P (-z) * (-1)) z := by
      have := (hP (-z)).hasDerivAt.comp z (hasDerivAt_neg z)
      exact this
    exact ((h1.cexp.mul (hP z).hasDerivAt)).add (h2.cexp.mul h3)
  have hR : HasDerivAt (fun w => 2 * Complex.exp (F w) * Q w)
      (2 * (Complex.exp (F z) * deriv F z) * Q z + 2 * Complex.exp (F z) * deriv Q z) z :=
    (((hF z).hasDerivAt.cexp.const_mul 2).mul (hQ z).hasDerivAt)
  have hfun : (fun w => Complex.exp (g w / 2) * P w + Complex.exp (-(g w) / 2) * P (-w)) =
      fun w => 2 * Complex.exp (F w) * Q w := funext heq
  rw [hfun] at hL
  have E1 := hL.unique hR
  have E0 := heq z
  set x := Complex.exp (g z / 2)
  set y := Complex.exp (-(g z) / 2)
  set e := Complex.exp (F z)
  have hxx : Complex.exp (g z) = x * x := by
    simp only [x]; rw [← Complex.exp_add]; ring_nf
  have hxy : x * y = 1 := by
    simp only [x, y]; rw [← Complex.exp_add]; ring_nf; simp
  have he : (2 * e) ≠ 0 := mul_ne_zero two_ne_zero (Complex.exp_ne_zero _)
  rw [hxx]
  apply mul_left_cancel₀ he
  set u := deriv g z / 2 * P z + deriv P z
  set v := -(deriv g z) / 2 * P (-z) - deriv P (-z)
  set w := deriv F z * Q z + deriv Q z
  linear_combination (-(x * x * u + v)) * E0 + (x * x * P z + P (-z)) * E1 +
    x * (u * P (-z) - v * P z) * hxy

/-- The degenerate case `M ≡ 0`: then `e^g (2 - λ) P Q = λ Q P(-z)` with `λ ≠ 2`. -/
private theorem degenerate_identity {g F P Q : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hF : Differentiable ℂ F) (hP : Differentiable ℂ P) (hQ : Differentiable ℂ Q)
    (hP0 : P 0 = 1) (hQ0 : Q 0 = 1)
    (heq : ∀ z, Complex.exp (g z / 2) * P z + Complex.exp (-(g z) / 2) * P (-z) =
      2 * Complex.exp (F z) * Q z)
    (hM0 : ∀ z, wM g F P Q z = 0) :
    ∃ l : ℂ, l ≠ 2 ∧
      ∀ z, Complex.exp (g z) * ((2 - l) * P z * Q z) = l * Q z * P (-z) := by
  unfold wM at hM0
  set Φ : ℂ → ℂ := fun w => Complex.exp (g w / 2) * P w
  set Ψ : ℂ → ℂ := fun w => Complex.exp (F w) * Q w
  have hΦd : ∀ w, HasDerivAt Φ (Complex.exp (g w / 2) * (deriv g w / 2) * P w +
      Complex.exp (g w / 2) * deriv P w) w := fun w =>
    ((hg w).hasDerivAt.div_const 2).cexp.mul (hP w).hasDerivAt
  have hΨd : ∀ w, HasDerivAt Ψ (Complex.exp (F w) * deriv F w * Q w +
      Complex.exp (F w) * deriv Q w) w := fun w =>
    (hF w).hasDerivAt.cexp.mul (hQ w).hasDerivAt
  have hΦ : Differentiable ℂ Φ := fun w => (hΦd w).differentiableAt
  have hΨ : Differentiable ℂ Ψ := fun w => (hΨd w).differentiableAt
  have hΨ0 : Ψ 0 ≠ 0 := by simp [Ψ, hQ0, Complex.exp_ne_zero]
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    (hΨ.continuous.continuousAt.eventually_ne hΨ0)
  set l := Φ 0 / Ψ 0
  have hloc : ∀ w ∈ Metric.ball (0 : ℂ) δ, Φ w / Ψ w = Φ 0 / Ψ 0 := by
    intro w hw
    apply IsOpen.is_const_of_deriv_eq_zero Metric.isOpen_ball (convex_ball _ _).isPreconnected
      _ _ hw (Metric.mem_ball_self hδ)
    · intro v hv
      exact ((hΦd v).div (hΨd v) (hball v hv)).differentiableAt.differentiableWithinAt
    · intro v hv
      change deriv (Φ / Ψ) v = 0
      rw [((hΦd v).div (hΨd v) (hball v hv)).deriv]
      have := hM0 v
      rw [div_eq_zero_iff]; left
      simp only [Φ, Ψ]
      linear_combination Complex.exp (g v / 2) * Complex.exp (F v) * this
  have hev : Φ =ᶠ[𝓝 0] fun w => l * Ψ w := by
    filter_upwards [Metric.ball_mem_nhds 0 hδ] with w hw
    have := hloc w hw
    rw [div_eq_iff (hball w hw)] at this
    rw [this]
  have hglob : Φ = fun w => l * Ψ w :=
    AnalyticOnNhd.eq_of_eventuallyEq (fun w _ => hΦ.analyticAt w)
      (fun w _ => (hΨ.const_mul l).analyticAt w) hev
  have hl2 : l ≠ 2 := by
    intro h2
    have e0 := heq 0
    have e1 := congrFun hglob 0
    simp only [Φ, Ψ] at e1
    rw [h2] at e1
    simp only [neg_zero, hP0, mul_one] at e0 e1
    have : Complex.exp (-(g 0) / 2) = 0 := by linear_combination e0 - e1
    exact Complex.exp_ne_zero _ this
  refine ⟨l, hl2, fun z => ?_⟩
  have E1 := congrFun hglob z
  have E0 := heq z
  simp only [Φ, Ψ] at E1
  set x := Complex.exp (g z / 2)
  set y := Complex.exp (-(g z) / 2)
  set e := Complex.exp (F z)
  have hxx : Complex.exp (g z) = x * x := by
    simp only [x]; rw [← Complex.exp_add]; ring_nf
  have hxy : x * y = 1 := by
    simp only [x, y]; rw [← Complex.exp_add]; ring_nf; simp
  have he : e * y ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
  rw [hxx]
  apply mul_left_cancel₀ he
  linear_combination (2 * e * Q z) * E1 - (l * Q z * e) * E0 + e * x * (2 - l) * P z * Q z * hxy

private theorem norm_wM_bound {a b p p' q q' : ℂ} {E : ℝ} (hE : 0 ≤ E)
    (hp : ‖p‖ ≤ E) (hp' : ‖p'‖ ≤ E)
    (hq : ‖q‖ ≤ E) (hq' : ‖q'‖ ≤ E) :
    ‖q * (a / 2 * p + p') - (b * q + q') * p‖ ≤ E ^ 2 * (‖a‖ + ‖b‖ + 2) := by
  have h1 : ‖q * (a / 2 * p + p')‖ ≤ E * (‖a‖ * E + E) := by
    rw [norm_mul]
    apply mul_le_mul hq _ (norm_nonneg _) hE
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_div]
    simp only [Complex.norm_ofNat]
    have : ‖a‖ / 2 * ‖p‖ ≤ ‖a‖ * E := by
      have := mul_le_mul_of_nonneg_left hp (norm_nonneg a)
      nlinarith [norm_nonneg a, norm_nonneg p]
    linarith
  have h2 : ‖(b * q + q') * p‖ ≤ (‖b‖ * E + E) * E := by
    rw [norm_mul]
    apply mul_le_mul _ hp (norm_nonneg _) (by positivity)
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    have := mul_le_mul_of_nonneg_left hq (norm_nonneg b)
    linarith
  calc _ ≤ ‖q * (a / 2 * p + p')‖ + ‖(b * q + q') * p‖ := norm_sub_le _ _
    _ ≤ E * (‖a‖ * E + E) + (‖b‖ * E + E) * E := add_le_add h1 h2
    _ = E ^ 2 * (‖a‖ + ‖b‖ + 2) := by ring

private theorem norm_wK_bound {a b p p' q q' : ℂ} {E : ℝ} (hE : 0 ≤ E)
    (hp : ‖p‖ ≤ E) (hp' : ‖p'‖ ≤ E)
    (hq : ‖q‖ ≤ E) (hq' : ‖q'‖ ≤ E) :
    ‖(b * q + q') * p - q * (-p' - a / 2 * p)‖ ≤ E ^ 2 * (‖a‖ + ‖b‖ + 2) := by
  have h1 : ‖(b * q + q') * p‖ ≤ (‖b‖ * E + E) * E := by
    rw [norm_mul]
    apply mul_le_mul _ hp (norm_nonneg _) (by positivity)
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    have := mul_le_mul_of_nonneg_left hq (norm_nonneg b)
    linarith
  have h2 : ‖q * (-p' - a / 2 * p)‖ ≤ E * (E + ‖a‖ * E) := by
    rw [norm_mul]
    apply mul_le_mul hq _ (norm_nonneg _) hE
    refine (norm_sub_le _ _).trans ?_
    rw [norm_neg, norm_mul, norm_div]
    simp only [Complex.norm_ofNat]
    have : ‖a‖ / 2 * ‖p‖ ≤ ‖a‖ * E := by
      have := mul_le_mul_of_nonneg_left hp (norm_nonneg a)
      nlinarith [norm_nonneg a, norm_nonneg p]
    linarith
  calc _ ≤ ‖(b * q + q') * p‖ + ‖q * (-p' - a / 2 * p)‖ := norm_sub_le _ _
    _ ≤ (‖b‖ * E + E) * E + E * (E + ‖a‖ * E) := add_le_add h1 h2
    _ = E ^ 2 * (‖a‖ + ‖b‖ + 2) := by ring

private theorem differentiable_deriv' {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ (deriv f) :=
  differentiableOn_univ.mp ((hf.differentiableOn).deriv isOpen_univ)

/-- The growth inequality for `posMean g` (an elementary substitute for the second main
private theorem in this situation). -/
private theorem key_GI {g F P Q : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hF : Differentiable ℂ F)
    (hP : Differentiable ℂ P) (hQ : Differentiable ℂ Q) (hP0 : P 0 = 1) (hQ0 : Q 0 = 1)
    {C : ℝ} (hC : 0 ≤ C)
    (hPb : ∀ z, ‖P z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ 2))
    (hQb : ∀ z, ‖Q z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ 2))
    (heq : ∀ z, Complex.exp (g z / 2) * P z + Complex.exp (-(g z) / 2) * P (-z) =
      2 * Complex.exp (F z) * Q z) :
    ∃ C', 0 ≤ C' ∧ ∀ r ρ, 1 ≤ r → r < ρ →
      posMean g r ≤ 2 * Real.log (2 + 2 * ρ / (ρ - r) ^ 2 *
        (4 * posMean g ρ + C' * (1 + ρ) ^ 2)) + C' * (1 + r) ^ 2 := by
  obtain ⟨C₁, hC₁, hF₁⟩ := posMean_F_le hg hP hQ hQ0 hC hPb hQb heq
  have harg : ∀ r ρ C', 0 ≤ C' → r < ρ → 0 ≤ ρ →
      1 ≤ 2 + 2 * ρ / (ρ - r) ^ 2 * (4 * posMean g ρ + C' * (1 + ρ) ^ 2) := by
    intro r ρ C' hC' hrρ hρ
    have : 0 ≤ 2 * ρ / (ρ - r) ^ 2 * (4 * posMean g ρ + C' * (1 + ρ) ^ 2) := by
      have := posMean_nonneg g ρ; positivity
    linarith
  by_cases hdeg : ∀ z, wM g F P Q z = 0
  · obtain ⟨l, hl2, hl⟩ := degenerate_identity hg hF hP hQ hP0 hQ0 heq hdeg
    have hPm : Differentiable ℂ (fun z => P (-z)) := hP.comp differentiable_neg
    have hK : Differentiable ℂ (fun z => l * Q z * P (-z)) := by fun_prop
    have hM : Differentiable ℂ (fun z => (2 - l) * P z * Q z) := by fun_prop
    obtain ⟨C₀, hC₀⟩ := posMean_le_of_exp_mul_eq (G := g) hK hM (x₀ := 0)
      (by simp [hP0, hQ0, sub_ne_zero.mpr hl2.symm]) hl
    have hC' : 0 ≤ log⁺ ‖l‖ + log⁺ ‖2 - l‖ + |C₀| + 4 * C :=
      add_nonneg (add_nonneg (add_nonneg posLog_nonneg posLog_nonneg) (abs_nonneg _))
        (by positivity)
    refine ⟨log⁺ ‖l‖ + log⁺ ‖2 - l‖ + |C₀| + 4 * C, hC', fun r ρ hr hrρ => ?_⟩
    have hr0 : 0 < r := by linarith
    have hKb : circleAverage (fun z => log⁺ ‖l * Q z * P (-z)‖) 0 r ≤
        log⁺ ‖l‖ + 2 * C * (1 + r) ^ 2 := by
      apply circleAverage_posLog_le hK hr0
      intro z hz
      have e1 := posLog_norm_mul_le (l * Q z) (P (-z))
      have e2 := posLog_norm_mul_le l (Q z)
      have p1 := posLog_norm_le_of_exp_bound hC hQb z
      have p2 := posLog_norm_le_of_exp_bound hC hPb (-z)
      rw [hz] at p1; rw [norm_neg, hz] at p2
      linarith
    have hMb : circleAverage (fun z => log⁺ ‖(2 - l) * P z * Q z‖) 0 r ≤
        log⁺ ‖2 - l‖ + 2 * C * (1 + r) ^ 2 := by
      apply circleAverage_posLog_le hM hr0
      intro z hz
      have e1 := posLog_norm_mul_le ((2 - l) * P z) (Q z)
      have e2 := posLog_norm_mul_le (2 - l) (P z)
      have p1 := posLog_norm_le_of_exp_bound hC hQb z
      have p2 := posLog_norm_le_of_exp_bound hC hPb z
      rw [hz] at p1 p2
      linarith
    have h := hC₀ r hr
    have hlog := Real.log_nonneg (harg r ρ (log⁺ ‖l‖ + log⁺ ‖2 - l‖ + |C₀| + 4 * C)
      hC' hrρ (by linarith))
    have hsq : 1 ≤ (1 + r) ^ 2 := by nlinarith
    have a1 := mul_le_mul_of_nonneg_left hsq (posLog_nonneg (x := ‖l‖))
    have a2 := mul_le_mul_of_nonneg_left hsq (posLog_nonneg (x := ‖2 - l‖))
    have a3 := mul_le_mul_of_nonneg_left hsq (abs_nonneg C₀)
    have a4 := le_abs_self C₀
    have e : (log⁺ ‖l‖ + log⁺ ‖2 - l‖ + |C₀| + 4 * C) * (1 + r) ^ 2 =
        log⁺ ‖l‖ * (1 + r) ^ 2 + log⁺ ‖2 - l‖ * (1 + r) ^ 2 + |C₀| * (1 + r) ^ 2 +
          4 * C * (1 + r) ^ 2 := by ring
    rw [e]
    linarith
  · push Not at hdeg
    obtain ⟨x₀, hx₀⟩ := hdeg
    have hg' := differentiable_deriv' hg
    have hF' := differentiable_deriv' hF
    have hP' := differentiable_deriv' hP
    have hQ' := differentiable_deriv' hQ
    have hPm : Differentiable ℂ (fun z => P (-z)) := hP.comp differentiable_neg
    have hPm' : Differentiable ℂ (fun z => deriv P (-z)) := hP'.comp differentiable_neg
    have hK : Differentiable ℂ (wK g F P Q) := by unfold wK; fun_prop
    have hM : Differentiable ℂ (wM g F P Q) := by unfold wM; fun_prop
    obtain ⟨C₀, hC₀⟩ := posMean_le_of_exp_mul_eq (G := g) hK hM hx₀
      (wronskian_identity hg hF hP hQ heq)
    set C₂ := 2 * C₁ + |(g 0).re| + |(F 0).re| with hC₂
    have hC₂0 : 0 ≤ C₂ := by positivity
    refine ⟨C₂ + 16 * C + |C₀|, by positivity, fun r ρ hr hrρ => ?_⟩
    have hr0 : 0 < r := by linarith
    have hρ1 : 1 ≤ ρ := by linarith
    have hfac : 0 ≤ 2 * ρ / (ρ - r) ^ 2 := by positivity
    set D := 2 * ρ / (ρ - r) ^ 2 * (4 * posMean g ρ + C₂ * (1 + ρ) ^ 2) with hD
    have hD0 : 0 ≤ D := by have := posMean_nonneg g ρ; positivity
    have hder : ∀ z : ℂ, ‖z‖ = r → ‖deriv g z‖ + ‖deriv F z‖ ≤ D := by
      intro z hz
      have h1 := norm_deriv_le_posMean hg (z := z) (ρ := ρ) (by rw [hz]; exact hrρ)
      have h2 := norm_deriv_le_posMean hF (z := z) (ρ := ρ) (by rw [hz]; exact hrρ)
      rw [hz] at h1 h2
      have h3 := hF₁ ρ hρ1
      have hin : (2 * posMean g ρ - (g 0).re) + (2 * posMean F ρ - (F 0).re) ≤
          4 * posMean g ρ + C₂ * (1 + ρ) ^ 2 := by
        have hsq : 1 ≤ (1 + ρ) ^ 2 := by nlinarith
        have b1 := mul_le_mul_of_nonneg_left hsq (abs_nonneg (g 0).re)
        have b2 := mul_le_mul_of_nonneg_left hsq (abs_nonneg (F 0).re)
        have b3 := neg_le_abs (g 0).re
        have b4 := neg_le_abs (F 0).re
        have e : C₂ * (1 + ρ) ^ 2 = 2 * (C₁ * (1 + ρ) ^ 2) + |(g 0).re| * (1 + ρ) ^ 2 +
            |(F 0).re| * (1 + ρ) ^ 2 := by rw [hC₂]; ring
        rw [e]
        linarith
      calc ‖deriv g z‖ + ‖deriv F z‖
          ≤ 2 * ρ / (ρ - r) ^ 2 * (2 * posMean g ρ - (g 0).re) +
            2 * ρ / (ρ - r) ^ 2 * (2 * posMean F ρ - (F 0).re) := add_le_add h1 h2
        _ = 2 * ρ / (ρ - r) ^ 2 * ((2 * posMean g ρ - (g 0).re) +
            (2 * posMean F ρ - (F 0).re)) := by ring
        _ ≤ D := mul_le_mul_of_nonneg_left hin hfac
    set E := Real.exp (C * (2 + r) ^ 2) with hE
    have hE0 : 0 ≤ E := (Real.exp_pos _).le
    have hle : Real.exp (C * (1 + r) ^ 2) ≤ E := Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) 2) hC)
    have hlogb : ∀ X : ℂ, ‖X‖ ≤ E ^ 2 * (D + 2) →
        log⁺ ‖X‖ ≤ 2 * C * (2 + r) ^ 2 + Real.log (D + 2) := by
      intro X hX
      have hl0 : 0 ≤ Real.log (D + 2) := Real.log_nonneg (by linarith)
      apply posLog_le_of_le_exp (norm_nonneg _) (by positivity)
      rw [Real.exp_add, Real.exp_log (by linarith)]
      have : E ^ 2 = Real.exp (2 * C * (2 + r) ^ 2) := by
        rw [hE, sq, ← Real.exp_add]; ring_nf
      rw [← this]; exact hX
    have hKb : circleAverage (fun z => log⁺ ‖wK g F P Q z‖) 0 r ≤
        2 * C * (2 + r) ^ 2 + Real.log (D + 2) := by
      apply circleAverage_posLog_le hK hr0
      intro z hz
      apply hlogb
      have hd := hder z hz
      refine (norm_wK_bound (a := deriv g z) (b := deriv F z) (p := P (-z))
        (p' := deriv P (-z)) (q := Q z) (q' := deriv Q z) hE0
        ((hPb (-z)).trans (by rw [norm_neg, hz]; exact hle))
        ((norm_deriv_le_exp hP hC hPb (-z)).trans (by rw [norm_neg, hz]))
        ((hQb z).trans (by rw [hz]; exact hle))
        ((norm_deriv_le_exp hQ hC hQb z).trans (by rw [hz]))).trans ?_
      gcongr
    have hMb : circleAverage (fun z => log⁺ ‖wM g F P Q z‖) 0 r ≤
        2 * C * (2 + r) ^ 2 + Real.log (D + 2) := by
      apply circleAverage_posLog_le hM hr0
      intro z hz
      apply hlogb
      have hd := hder z hz
      refine (norm_wM_bound (a := deriv g z) (b := deriv F z) (p := P z)
        (p' := deriv P z) (q := Q z) (q' := deriv Q z) hE0
        ((hPb z).trans (by rw [hz]; exact hle))
        ((norm_deriv_le_exp hP hC hPb z).trans (by rw [hz]))
        ((hQb z).trans (by rw [hz]; exact hle))
        ((norm_deriv_le_exp hQ hC hQb z).trans (by rw [hz]))).trans ?_
      gcongr
    have h := hC₀ r hr
    -- compare `log (D + 2)` with the target logarithm
    have hDle : D + 2 ≤ 2 + 2 * ρ / (ρ - r) ^ 2 *
        (4 * posMean g ρ + (C₂ + 16 * C + |C₀|) * (1 + ρ) ^ 2) := by
      have : C₂ * (1 + ρ) ^ 2 ≤ (C₂ + 16 * C + |C₀|) * (1 + ρ) ^ 2 := by
        gcongr; have := abs_nonneg C₀; linarith
      have : D ≤ 2 * ρ / (ρ - r) ^ 2 *
          (4 * posMean g ρ + (C₂ + 16 * C + |C₀|) * (1 + ρ) ^ 2) := by
        rw [hD]; gcongr
      linarith
    have hlog := Real.log_le_log (by linarith) hDle
    have hsq : 1 ≤ (1 + r) ^ 2 := by nlinarith
    have h2r : (2 + r) ^ 2 ≤ 4 * (1 + r) ^ 2 := by nlinarith
    have a1 := mul_le_mul_of_nonneg_left h2r hC
    have a3 := mul_le_mul_of_nonneg_left hsq (abs_nonneg C₀)
    have a4 := le_abs_self C₀
    have a5 : 0 ≤ C₂ * (1 + r) ^ 2 := by positivity
    have e : (C₂ + 16 * C + |C₀|) * (1 + r) ^ 2 =
        C₂ * (1 + r) ^ 2 + 16 * (C * (1 + r) ^ 2) + |C₀| * (1 + r) ^ 2 := by ring
    rw [e]
    linarith

/-- **Key growth estimate.** Under the functional identity
`e^{g/2} P(z) + e^{-g/2} P(-z) = 2 e^{F} Q(z)` with `P, Q` of order at most two
(`log |P|, log |Q| ≤ C (1 + |z|)^2`) and `P(0) = Q(0) = 1`, the Nevanlinna characteristic
`T(r, e^g) = posMean g r` grows at most quadratically. -/
private theorem key_growth {g F P Q : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hF : Differentiable ℂ F)
    (hP : Differentiable ℂ P) (hQ : Differentiable ℂ Q) (hP0 : P 0 = 1) (hQ0 : Q 0 = 1)
    {C : ℝ} (hC : 0 ≤ C)
    (hPb : ∀ z, ‖P z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ 2))
    (hQb : ∀ z, ‖Q z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ 2))
    (heq : ∀ z, Complex.exp (g z / 2) * P z + Complex.exp (-(g z) / 2) * P (-z) =
      2 * Complex.exp (F z) * Q z) :
    ∃ A, ∀ r, 0 < r → posMean g r ≤ A * (1 + r) ^ 2 := by
  obtain ⟨C', hC', hGI⟩ := key_GI hg hF hP hQ hP0 hQ0 hC hPb hQb heq
  exact growth_of_GI (posMean_nonneg g) (posMean_bdd hg) hC' hGI

end RealRooted.EdreiThoma
end
end KeyGrowth_part

section Products_part


/-!
# Genus-zero products `∏ (1 + a_i z)` with `a_i ≥ 0` summable
-/


open Complex Real Filter Topology

noncomputable section

namespace RealRooted.EdreiThoma

/-- The genus-zero product `∏' i, (1 + a i * z)`. -/
private def gprod (a : ℕ → ℝ) (z : ℂ) : ℂ := ∏' i, (1 + (a i : ℂ) * z)

variable {a : ℕ → ℝ}

private theorem gprod_zero (a : ℕ → ℝ) : gprod a 0 = 1 := by
  simp [gprod]

private theorem gprod_differentiable (ha : ∀ i, 0 ≤ a i) (s : Summable a) :
    Differentiable ℂ (gprod a) := by
  intro z
  set R := ‖z‖ + 1
  have hU : IsOpen (Metric.ball (0 : ℂ) R) := Metric.isOpen_ball
  have hprod : HasProdLocallyUniformlyOn (fun i x => 1 + (a i : ℂ) * x) (gprod a)
      (Metric.ball (0 : ℂ) R) := by
    apply Summable.hasProdLocallyUniformlyOn_nat_one_add hU (s.mul_right R)
    · refine Eventually.of_forall fun n x hx => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha n)]
      have : ‖x‖ ≤ R := by simpa using (Metric.mem_ball.mp hx).le
      exact mul_le_mul_of_nonneg_left this (ha n)
    · intro n; fun_prop
  have hd : DifferentiableOn ℂ (gprod a) (Metric.ball (0 : ℂ) R) := by
    apply TendstoLocallyUniformlyOn.differentiableOn hprod _ hU
    refine Eventually.of_forall fun s => ?_
    apply DifferentiableOn.fun_finsetProd
    intro i _
    fun_prop
  apply hd.differentiableAt
  apply hU.mem_nhds
  simp [R]

private theorem norm_gprod_le (ha : ∀ i, 0 ≤ a i) (s : Summable a) (z : ℂ) :
    ‖gprod a z‖ ≤ Real.exp ((∑' i, a i) * ‖z‖) := by
  have hm : Multipliable (fun i => 1 + (a i : ℂ) * z) := by
    apply multipliable_one_add_of_summable
    refine (s.mul_right ‖z‖).congr fun i => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha i)]
  have ht := hm.hasProd.tendsto_prod_nat
  have hb : ∀ n, ‖∏ i ∈ Finset.range n, (1 + (a i : ℂ) * z)‖ ≤
      Real.exp ((∑' i, a i) * ‖z‖) := by
    intro n
    calc ‖∏ i ∈ Finset.range n, (1 + (a i : ℂ) * z)‖
        ≤ ∏ i ∈ Finset.range n, ‖1 + (a i : ℂ) * z‖ := Finset.norm_prod_le _ _
      _ ≤ ∏ i ∈ Finset.range n, Real.exp (a i * ‖z‖) := by
          apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
          intro i _
          calc ‖1 + (a i : ℂ) * z‖ ≤ 1 + a i * ‖z‖ := by
                refine (norm_add_le _ _).trans ?_
                rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha i)]
            _ ≤ Real.exp (a i * ‖z‖) := by
                have := Real.add_one_le_exp (a i * ‖z‖); linarith
      _ = Real.exp ((∑ i ∈ Finset.range n, a i) * ‖z‖) := by
          rw [← Real.exp_sum, Finset.sum_mul]
      _ ≤ Real.exp ((∑' i, a i) * ‖z‖) := by
          gcongr
          exact s.sum_le_tsum _ (fun i _ => ha i)
  exact le_of_tendsto' ht.norm hb

end RealRooted.EdreiThoma
end
end Products_part

section Assembly_part


/-!
# Assembly: from Edrei's functional identity to the quadratic growth of the odd part
-/


open Complex Real Filter Topology

noncomputable section

namespace RealRooted.EdreiThoma

private theorem tprod_one_sub_eq (a : ℕ → ℝ) (z : ℂ) :
    ∏' i, (1 - (a i : ℂ) * z) = gprod a (-z) := by
  simp only [gprod, mul_neg, ← sub_eq_add_neg]

/-- An odd polynomial function of degree `≤ 2` is linear. -/
private theorem odd_quadratic_is_linear {g : ℂ → ℂ} (hodd : ∀ z, g (-z) = -g z)
    {p : Polynomial ℂ} (hp : p.natDegree ≤ 2) (hgp : ∀ z, g z = p.eval z) :
    ∃ c : ℂ, ∀ z, g z = 2 * c * z := by
  have hev : ∀ z, g z = p.coeff 0 + p.coeff 1 * z + p.coeff 2 * z ^ 2 := by
    intro z
    rw [hgp, Polynomial.eval_eq_sum_range' (n := 3) (by lia)]
    simp [Finset.sum_range_succ]
  have h0 : p.coeff 0 = 0 := by
    have := hodd 0
    rw [neg_zero] at this
    have h : g 0 = p.coeff 0 := by simpa using hev 0
    have : g 0 = 0 := by linear_combination this / 2
    rw [this] at h; exact h.symm
  have h2 : p.coeff 2 = 0 := by
    have a := hodd 1
    rw [hev, hev] at a
    rw [h0] at a
    linear_combination a / 2
  refine ⟨p.coeff 1 / 2, fun z => ?_⟩
  rw [hev, h0, h2]; ring

/-- The identity of `odd_part_linear`, cleared of denominators, holds everywhere. -/
private theorem entire_identity {φ φs : ℂ → ℂ} (hφ : Differentiable ℂ φ)
    (hφs : Differentiable ℂ φs)
    {α β αs βs : ℕ → ℝ} (hα : ∀ i, 0 ≤ α i) (hβ : ∀ i, 0 ≤ β i)
    (hαs : ∀ i, 0 ≤ αs i) (hβs : ∀ i, 0 ≤ βs i)
    (sα : Summable α) (sβ : Summable β) (sαs : Summable αs) (sβs : Summable βs)
    (hrel : ∀ z : ℂ, (∏' i, (1 - (β i : ℂ) * z)) ≠ 0 →
      (∏' i, (1 - (β i : ℂ) * (-z))) ≠ 0 →
      (∏' i, (1 - (βs i : ℂ) * z ^ 2)) ≠ 0 →
      Complex.exp (φ z) * (∏' i, (1 + (α i : ℂ) * z)) / (∏' i, (1 - (β i : ℂ) * z)) +
        Complex.exp (φ (-z)) * (∏' i, (1 + (α i : ℂ) * (-z))) /
          (∏' i, (1 - (β i : ℂ) * (-z))) =
      2 * Complex.exp (φs (z ^ 2)) * (∏' i, (1 + (αs i : ℂ) * z ^ 2)) /
        (∏' i, (1 - (βs i : ℂ) * z ^ 2))) :
    ∀ z, Complex.exp (φ z) * (gprod α z * gprod β z * gprod βs (-z ^ 2)) +
        Complex.exp (φ (-z)) * (gprod α (-z) * gprod β (-z) * gprod βs (-(-z) ^ 2)) =
      2 * Complex.exp (φs (z ^ 2)) * (gprod αs (z ^ 2) * gprod β (-z) * gprod β z) := by
  have dα := gprod_differentiable hα sα
  have dβ := gprod_differentiable hβ sβ
  have dαs := gprod_differentiable hαs sαs
  have dβs := gprod_differentiable hβs sβs
  set L : ℂ → ℂ := fun z =>
    Complex.exp (φ z) * (gprod α z * gprod β z * gprod βs (-z ^ 2)) +
    Complex.exp (φ (-z)) * (gprod α (-z) * gprod β (-z) * gprod βs (-(-z) ^ 2))
  set R : ℂ → ℂ := fun z =>
      2 * Complex.exp (φs (z ^ 2)) * (gprod αs (z ^ 2) * gprod β (-z) * gprod β z)
  have hL : Differentiable ℂ L := by
    have h1 : Differentiable ℂ (fun z => φ (-z)) := hφ.comp differentiable_neg
    have h2 : Differentiable ℂ (fun z : ℂ => gprod α (-z)) := dα.comp differentiable_neg
    have h3 : Differentiable ℂ (fun z : ℂ => gprod β (-z)) := dβ.comp differentiable_neg
    have h4 : Differentiable ℂ (fun z : ℂ => gprod βs (-z ^ 2)) :=
      dβs.comp (by fun_prop)
    have h5 : Differentiable ℂ (fun z : ℂ => gprod βs (-(-z) ^ 2)) :=
      dβs.comp (by fun_prop)
    fun_prop
  have hR : Differentiable ℂ R := by
    have h3 : Differentiable ℂ (fun z : ℂ => gprod β (-z)) := dβ.comp differentiable_neg
    have h6 : Differentiable ℂ (fun z : ℂ => gprod αs (z ^ 2)) := dαs.comp (by fun_prop)
    have h7 : Differentiable ℂ (fun z : ℂ => φs (z ^ 2)) := hφs.comp (by fun_prop)
    fun_prop
  -- the three denominators are nonzero near `0`
  have c1 : ∀ᶠ z in 𝓝 (0 : ℂ), gprod β (-z) ≠ 0 :=
    ((dβ.comp differentiable_neg).continuous.continuousAt (x := 0)).eventually_ne
      (by simp [gprod_zero])
  have c2 : ∀ᶠ z in 𝓝 (0 : ℂ), gprod β z ≠ 0 :=
    (dβ.continuous.continuousAt (x := 0)).eventually_ne (by simp [gprod_zero])
  have c3 : ∀ᶠ z in 𝓝 (0 : ℂ), gprod βs (-z ^ 2) ≠ 0 :=
    ((dβs.comp (by fun_prop : Differentiable ℂ (fun z : ℂ => -z ^ 2))).continuous.continuousAt
      (x := 0)).eventually_ne (by simp [gprod_zero])
  have hev : L =ᶠ[𝓝 0] R := by
    filter_upwards [c1, c2, c3] with z h1 h2 h3
    have h := hrel z (by rwa [tprod_one_sub_eq]) (by rwa [tprod_one_sub_eq, neg_neg])
      (by rwa [tprod_one_sub_eq])
    rw [tprod_one_sub_eq, tprod_one_sub_eq, tprod_one_sub_eq, neg_neg] at h
    change Complex.exp (φ z) * gprod α z / gprod β (-z) +
        Complex.exp (φ (-z)) * gprod α (-z) / gprod β z =
      2 * Complex.exp (φs (z ^ 2)) * gprod αs (z ^ 2) / gprod βs (-z ^ 2) at h
    simp only [L, R, neg_sq]
    field_simp at h
    linear_combination h
  have := AnalyticOnNhd.eq_of_eventuallyEq (fun z _ => hL.analyticAt z)
    (fun z _ => hR.analyticAt z) hev
  exact fun z => congrFun this z

/-- Under the hypotheses of `odd_part_linear`, the odd part `g(z) = φ(z) - φ(-z)` satisfies
`T(r, e^g) = posMean g r ≤ A (1 + r)^2`. -/
private theorem odd_part_growth {φ φs : ℂ → ℂ} (hφ : Differentiable ℂ φ)
    (hφs : Differentiable ℂ φs)
    {α β αs βs : ℕ → ℝ} (hα : ∀ i, 0 ≤ α i) (hβ : ∀ i, 0 ≤ β i)
    (hαs : ∀ i, 0 ≤ αs i) (hβs : ∀ i, 0 ≤ βs i)
    (sα : Summable α) (sβ : Summable β) (sαs : Summable αs) (sβs : Summable βs)
    (hrel : ∀ z : ℂ, (∏' i, (1 - (β i : ℂ) * z)) ≠ 0 →
      (∏' i, (1 - (β i : ℂ) * (-z))) ≠ 0 →
      (∏' i, (1 - (βs i : ℂ) * z ^ 2)) ≠ 0 →
      Complex.exp (φ z) * (∏' i, (1 + (α i : ℂ) * z)) / (∏' i, (1 - (β i : ℂ) * z)) +
        Complex.exp (φ (-z)) * (∏' i, (1 + (α i : ℂ) * (-z))) /
          (∏' i, (1 - (β i : ℂ) * (-z))) =
      2 * Complex.exp (φs (z ^ 2)) * (∏' i, (1 + (αs i : ℂ) * z ^ 2)) /
        (∏' i, (1 - (βs i : ℂ) * z ^ 2))) :
    ∃ A, ∀ r, 0 < r → posMean (fun z => φ z - φ (-z)) r ≤ A * (1 + r) ^ 2 := by
  have dα := gprod_differentiable hα sα
  have dβ := gprod_differentiable hβ sβ
  have dαs := gprod_differentiable hαs sαs
  have dβs := gprod_differentiable hβs sβs
  have hE := entire_identity hφ hφs hα hβ hαs hβs sα sβ sαs sβs hrel
  set g : ℂ → ℂ := fun z => φ z - φ (-z) with hg_def
  set F : ℂ → ℂ := fun z => φs (z ^ 2) - (φ z + φ (-z)) / 2 with hF_def
  set P : ℂ → ℂ := fun z => gprod α z * gprod β z * gprod βs (-z ^ 2) with hP_def
  set Q : ℂ → ℂ := fun z => gprod αs (z ^ 2) * gprod β (-z) * gprod β z with hQ_def
  have hφm : Differentiable ℂ (fun z => φ (-z)) := hφ.comp differentiable_neg
  have hg : Differentiable ℂ g := by simp only [hg_def]; fun_prop
  have hF : Differentiable ℂ F := by
    have : Differentiable ℂ (fun z : ℂ => φs (z ^ 2)) := hφs.comp (by fun_prop)
    simp only [hF_def]; fun_prop
  have hP : Differentiable ℂ P := by
    have h4 : Differentiable ℂ (fun z : ℂ => gprod βs (-z ^ 2)) := dβs.comp (by fun_prop)
    simp only [hP_def]; fun_prop
  have hQ : Differentiable ℂ Q := by
    have h3 : Differentiable ℂ (fun z : ℂ => gprod β (-z)) := dβ.comp differentiable_neg
    have h6 : Differentiable ℂ (fun z : ℂ => gprod αs (z ^ 2)) := dαs.comp (by fun_prop)
    simp only [hQ_def]; fun_prop
  have hP0 : P 0 = 1 := by simp [hP_def, gprod_zero]
  have hQ0 : Q 0 = 1 := by simp [hQ_def, gprod_zero]
  set C := (∑' i, α i) + 2 * (∑' i, β i) + (∑' i, βs i) + (∑' i, αs i) with hC_def
  have hSα : 0 ≤ ∑' i, α i := tsum_nonneg hα
  have hSβ : 0 ≤ ∑' i, β i := tsum_nonneg hβ
  have hSαs : 0 ≤ ∑' i, αs i := tsum_nonneg hαs
  have hSβs : 0 ≤ ∑' i, βs i := tsum_nonneg hβs
  have hC : 0 ≤ C := by positivity
  have hz1 : ∀ z : ℂ, ‖z‖ ≤ (1 + ‖z‖) ^ 2 := fun z => by nlinarith [norm_nonneg z]
  have hz2 : ∀ z : ℂ, ‖z‖ ^ 2 ≤ (1 + ‖z‖) ^ 2 := fun z => by nlinarith [norm_nonneg z]
  have hPb : ∀ z, ‖P z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ 2) := by
    intro z
    simp only [hP_def, norm_mul]
    have b1 := norm_gprod_le hα sα z
    have b2 := norm_gprod_le hβ sβ z
    have b3 := norm_gprod_le hβs sβs (-z ^ 2)
    rw [norm_neg, norm_pow] at b3
    calc ‖gprod α z‖ * ‖gprod β z‖ * ‖gprod βs (-z ^ 2)‖
        ≤ Real.exp ((∑' i, α i) * ‖z‖) * Real.exp ((∑' i, β i) * ‖z‖) *
          Real.exp ((∑' i, βs i) * ‖z‖ ^ 2) := by gcongr
      _ = Real.exp
          ((∑' i, α i) * ‖z‖ + (∑' i, β i) * ‖z‖ +
            (∑' i, βs i) * ‖z‖ ^ 2) := by
          rw [Real.exp_add, Real.exp_add]
      _ ≤ Real.exp (C * (1 + ‖z‖) ^ 2) := by
          apply Real.exp_le_exp.mpr
          have := hz1 z; have := hz2 z
          have a1 := mul_le_mul_of_nonneg_left (hz1 z) hSα
          have a2 := mul_le_mul_of_nonneg_left (hz1 z) hSβ
          have a3 := mul_le_mul_of_nonneg_left (hz2 z) hSβs
          have a4 := mul_le_mul_of_nonneg_left (hz2 z) (add_nonneg hSβ hSαs)
          simp only [hC_def]
          nlinarith
  have hQb : ∀ z, ‖Q z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ 2) := by
    intro z
    simp only [hQ_def, norm_mul]
    have b1 := norm_gprod_le hαs sαs (z ^ 2)
    have b2 := norm_gprod_le hβ sβ (-z)
    have b3 := norm_gprod_le hβ sβ z
    rw [norm_pow] at b1
    rw [norm_neg] at b2
    calc ‖gprod αs (z ^ 2)‖ * ‖gprod β (-z)‖ * ‖gprod β z‖
        ≤ Real.exp ((∑' i, αs i) * ‖z‖ ^ 2) * Real.exp ((∑' i, β i) * ‖z‖) *
          Real.exp ((∑' i, β i) * ‖z‖) := by gcongr
      _ = Real.exp
          ((∑' i, αs i) * ‖z‖ ^ 2 + (∑' i, β i) * ‖z‖ +
            (∑' i, β i) * ‖z‖) := by
          rw [Real.exp_add, Real.exp_add]
      _ ≤ Real.exp (C * (1 + ‖z‖) ^ 2) := by
          apply Real.exp_le_exp.mpr
          have a1 := mul_le_mul_of_nonneg_left (hz2 z) hSαs
          have a2 := mul_le_mul_of_nonneg_left (hz1 z) hSβ
          have a3 := mul_le_mul_of_nonneg_left (hz2 z) (add_nonneg hSα hSβs)
          have a4 := mul_le_mul_of_nonneg_left (hz1 z) hSβ
          simp only [hC_def]
          nlinarith
  have heq : ∀ z, Complex.exp (g z / 2) * P z + Complex.exp (-(g z) / 2) * P (-z) =
      2 * Complex.exp (F z) * Q z := by
    intro z
    have h := hE z
    set m := Complex.exp ((φ z + φ (-z)) / 2)
    have e1 : Complex.exp (φ z) = m * Complex.exp (g z / 2) := by
      simp only [m, hg_def]; rw [← Complex.exp_add]; congr 1; ring
    have e2 : Complex.exp (φ (-z)) = m * Complex.exp (-(g z) / 2) := by
      simp only [m, hg_def]; rw [← Complex.exp_add]; congr 1; ring
    have e3 : Complex.exp (φs (z ^ 2)) = m * Complex.exp (F z) := by
      simp only [m, hF_def]; rw [← Complex.exp_add]; congr 1; ring
    rw [e1, e2, e3] at h
    have hm : m ≠ 0 := Complex.exp_ne_zero _
    apply mul_left_cancel₀ hm
    simp only [hP_def, hQ_def]
    linear_combination h
  exact key_growth hg hF hP hQ hP0 hQ0 hC hPb hQb heq

end RealRooted.EdreiThoma
end
end Assembly_part

open Complex Filter Topology

noncomputable section

namespace RealRooted.EdreiThoma
/-- **The odd-part step of Edrei's Proposition B** (Edrei, Canad. J. Math. 5 (1953), p. 92-93,
formulas (26)-(27) and the appeal to Nevanlinna's theorem).

Let `f = e^φ ∏(1+α z)/∏(1-β z)` and `f* = e^{φ*} ∏(1+α* z)/∏(1-β* z)` with
`φ, φ*` entire and
`α, β, α*, β* ≥ 0` summable (so all products have genus zero), and suppose
`f(z) + f(-z) = 2 f*(z^2)` (away from the poles).  Then the odd part of `φ` is linear:
`φ z - φ (-z) = 2 c z`.

(Proof in the source: `u = f(z)/f(-z)` has zeros/poles with `n(r) = o(r)` and its `(-1)`-points
(the zeros of `f*(z^2)`) satisfy `n(r) = O(r^2)`; Nevanlinna's theorem on three values gives
`T(r,u) = O(r^2)`; hence `e^{φ(z)-φ(-z)}` has order `≤ 2`, so `φ(z) - φ(-z)` is a
polynomial of
degree `≤ 2`, odd with value `0` at `0`, hence linear.  The second fundamental theorem is not in
Mathlib: an elementary substitute (a Borel-type theorem for `e^g + 1`, or a direct argument
for this specific identity) is what is needed.) -/
theorem odd_part_linear {φ φs : ℂ → ℂ} (hφ : Differentiable ℂ φ)
    (hφs : Differentiable ℂ φs)
    {α β αs βs : ℕ → ℝ} (hα : ∀ i, 0 ≤ α i) (hβ : ∀ i, 0 ≤ β i)
    (hαs : ∀ i, 0 ≤ αs i) (hβs : ∀ i, 0 ≤ βs i)
    (sα : Summable α) (sβ : Summable β) (sαs : Summable αs) (sβs : Summable βs)
    (hrel : ∀ z : ℂ, (∏' i, (1 - (β i : ℂ) * z)) ≠ 0 →
      (∏' i, (1 - (β i : ℂ) * (-z))) ≠ 0 →
      (∏' i, (1 - (βs i : ℂ) * z ^ 2)) ≠ 0 →
      Complex.exp (φ z) * (∏' i, (1 + (α i : ℂ) * z)) / (∏' i, (1 - (β i : ℂ) * z)) +
        Complex.exp (φ (-z)) * (∏' i, (1 + (α i : ℂ) * (-z))) /
          (∏' i, (1 - (β i : ℂ) * (-z))) =
      2 * Complex.exp (φs (z ^ 2)) * (∏' i, (1 + (αs i : ℂ) * z ^ 2)) /
        (∏' i, (1 - (βs i : ℂ) * z ^ 2))) :
    ∃ c : ℂ, ∀ z, φ z - φ (-z) = 2 * c * z := by
  -- `T(r, e^g) = O(r^2)` for the odd part `g(z) = φ(z) - φ(-z)` (elementary substitute for the
  -- second main theorem, see `EdreiOdd/KeyGrowth.lean`)
  obtain ⟨A, hA⟩ := odd_part_growth hφ hφs hα hβ hαs hβs sα sβ sαs sβs hrel
  -- hence `g` is a polynomial of degree `≤ 2`
  obtain ⟨p, hp, hgp⟩ := poly_of_mean_pos_re_le (g := fun z => φ z - φ (-z))
    (hφ.sub (hφ.comp differentiable_neg)) (k := 2) hA
  -- and, being odd, it is linear
  exact odd_quadratic_is_linear (g := fun z => φ z - φ (-z)) (fun z => by simp) hp hgp

end RealRooted.EdreiThoma

