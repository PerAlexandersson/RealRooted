/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib

/-!
# Hurwitz-type theorem for upper-half-plane-stable polynomials

Hurwitz's theorem in the following form: a locally uniform limit of holomorphic functions on a
ball that have no zeros there is either zero-free or identically zero. For multivariate complex
polynomials, we deduce that a locally uniform limit of polynomials with no zeros in the product of
upper half-planes is itself zero-free there or zero. The deduction restricts to a complex line
through a point of the product of half-planes and applies the one-variable statement.

## Main definitions

* `Complex.IsLimitOfZeros`: every neighborhood contains a zero of every sufficiently late
  function in a sequence.
* `MvPolynomial.upperHalfPlane`: the set `{z : τ → ℂ | ∀ i, 0 < (z i).im}`.

## Main statements

* `Complex.forall_ne_or_forall_eq_of_tendstoLocallyUniformlyOn_ball`: Hurwitz's theorem on a ball.
* `Complex.isClosed_isLimitOfZeros`: liminf limits of zeros form a closed set.
* `Complex.isLimitOfZeros_of_tendstoLocallyUniformlyOn_ball`: the local zero-producing
  corollary of Hurwitz's theorem.
* `Complex.isLimitOfZeros_finset_unique_dominant`: Sokal's Theorem 1.5(a), a unique dominant
  base whose coefficient vanishes at `z₀` without vanishing identically near it.
* `MvPolynomial.eval_ne_zero_or_eq_zero_of_tendstoLocallyUniformlyOn`: the limit `q` of
  polynomials `p k` with no zeros in `upperHalfPlane τ` has no zeros there, or `q = 0`.
-/

@[expose] public section

open Filter Topology Metric

noncomputable section

namespace Complex

private lemma le_norm_center_of_sphere {c z0 : ℂ} {r ρ M : ℝ} (hρ : 0 < ρ) (hM : 0 < M)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball c r))
    (hne : ∀ z ∈ ball c r, f z ≠ 0) (hsub : closedBall z0 ρ ⊆ ball c r)
    (hbd : ∀ z ∈ sphere z0 ρ, M ≤ ‖f z‖) : M ≤ ‖f z0‖ := by
  have hd : DiffContOnCl ℂ (fun z => (f z)⁻¹) (ball z0 ρ) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball z0 hρ.ne']
    exact (hf.mono hsub).inv (fun z hz => hne z (hsub hz))
  have key := Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball) hd (C := M⁻¹)
    (by
      intro z hz
      rw [frontier_ball z0 hρ.ne'] at hz
      rw [norm_inv]
      exact inv_anti₀ hM (hbd z hz))
    (subset_closure (mem_ball_self hρ))
  have h0 : f z0 ≠ 0 := hne z0 (hsub (mem_closedBall_self hρ.le))
  rw [norm_inv] at key
  exact (inv_le_inv₀ (norm_pos_iff.mpr h0) hM).mp key

/-- A locally uniform limit of zero-free holomorphic functions on a ball is either zero-free or
identically zero there. -/
theorem forall_ne_or_forall_eq_of_tendstoLocallyUniformlyOn_ball {c : ℂ} {r : ℝ}
    {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ} (hF : ∀ k, DifferentiableOn ℂ (F k) (ball c r))
    (hconv : TendstoLocallyUniformlyOn F g atTop (ball c r))
    (hne : ∀ k, ∀ z ∈ ball c r, F k z ≠ 0) :
    (∀ z ∈ ball c r, g z ≠ 0) ∨ (∀ z ∈ ball c r, g z = 0) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨z0, hz0, hg0⟩, ⟨z1, hz1, hg1⟩⟩ := hcon
  have hgd : DifferentiableOn ℂ g (ball c r) :=
    hconv.differentiableOn (Eventually.of_forall hF) isOpen_ball
  have han : AnalyticOnNhd ℂ g (ball c r) := hgd.analyticOnNhd isOpen_ball
  have hev : ∀ᶠ z in 𝓝[≠] z0, g z ≠ 0 := by
    rcases (han z0 hz0).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact absurd (han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (convex_ball c r).isPreconnected hz0 h hz1) hg1
    · exact h
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hεg⟩ := hev
  have hδ : 0 < r - dist z0 c := by
    rw [mem_ball] at hz0
    linarith
  set ρ := min ε (r - dist z0 c) / 2 with hρdef
  have hρ : 0 < ρ := by positivity
  have hρε : ρ < ε := by
    linarith [min_le_left ε (r - dist z0 c)]
  have hρδ : ρ < r - dist z0 c := by
    linarith [min_le_right ε (r - dist z0 c)]
  have hsub : closedBall z0 ρ ⊆ ball c r := by
    intro z hz
    rw [mem_closedBall] at hz
    rw [mem_ball]
    linarith [dist_triangle z z0 c]
  have hsph : ∀ z ∈ sphere z0 ρ, g z ≠ 0 := by
    intro z hz
    rw [mem_sphere] at hz
    apply hεg (by rw [hz]; exact hρε)
    intro h
    rw [h, dist_self] at hz
    linarith
  obtain ⟨w, hw, hmin⟩ := (isCompact_sphere z0 ρ).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hρ.le)
    (hgd.continuousOn.norm.mono (sphere_subset_closedBall.trans hsub))
  set m := ‖g w‖
  have hm : 0 < m := norm_pos_iff.mpr (hsph w hw)
  have hunif := (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball).mp hconv
    _ hsub (isCompact_closedBall z0 ρ)
  rw [Metric.tendstoUniformlyOn_iff] at hunif
  obtain ⟨k, hk⟩ := (hunif (m / 2) (by positivity)).exists
  have hbd : ∀ z ∈ sphere z0 ρ, m / 2 ≤ ‖F k z‖ := by
    intro z hz
    have h1 := hk z (sphere_subset_closedBall hz)
    have h2 : m ≤ ‖g z‖ := hmin hz
    rw [dist_eq_norm] at h1
    have hnorm := norm_sub_norm_le (g z) (F k z)
    linarith
  have hc := le_norm_center_of_sphere hρ (by positivity) (hF k) (hne k) hsub hbd
  have h3 := hk z0 (mem_closedBall_self hρ.le)
  rw [hg0, dist_zero_left] at h3
  linarith

/-- A point is a limit of zeros of a sequence of complex-valued functions if every ball around
it contains a zero of every sufficiently late function. This is the liminf notion of a limit of
zero sets used by Sokal, *Combinatorics, Probability and Computing* 13 (2004), Theorem 1.5. -/
def IsLimitOfZeros (F : ℕ → ℂ → ℂ) (z : ℂ) : Prop :=
  ∀ ε > 0, ∀ᶠ n in atTop, ∃ w ∈ ball z ε, F n w = 0

/-- The set of liminf limits of zeros of a sequence of complex-valued functions is closed. -/
theorem isClosed_isLimitOfZeros (F : ℕ → ℂ → ℂ) :
    IsClosed {z | IsLimitOfZeros F z} := by
  rw [← isOpen_compl_iff]
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hz ⊢
  rw [IsLimitOfZeros] at hz
  push Not at hz
  obtain ⟨ε, hε, hbad⟩ := hz
  refine mem_of_superset (ball_mem_nhds z (half_pos hε)) ?_
  intro y hy hyLim
  obtain ⟨n, hn, hn'⟩ :=
    (hbad.and_eventually (hyLim (ε / 2) (half_pos hε))).exists
  obtain ⟨w, hwy, hw0⟩ := hn'
  apply hn w
  · rw [mem_ball] at hy hwy ⊢
    linarith [dist_triangle w y z]
  · exact hw0

/-- A non-locally-constant locally uniform limit that vanishes at the center of a ball is a
liminf limit of zeros of its holomorphic approximants. This is the Hurwitz step in the main
direction of Sokal, *Combinatorics, Probability and Computing* 13 (2004), Theorem 1.5. -/
theorem isLimitOfZeros_of_tendstoLocallyUniformlyOn_ball {z₀ : ℂ} {r : ℝ}
    {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ} (hr : 0 < r)
    (hF : ∀ n, DifferentiableOn ℂ (F n) (ball z₀ r))
    (hconv : TendstoLocallyUniformlyOn F g atTop (ball z₀ r))
    (hg0 : g z₀ = 0) (hnconst : ¬∀ᶠ z in 𝓝 z₀, g z = g z₀) :
    IsLimitOfZeros F z₀ := by
  intro ε hε
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  obtain ⟨φ, hφ, hφzero⟩ := extraction_of_frequently_atTop hcon
  set ρ := min ε r / 2 with hρdef
  have hρ : 0 < ρ := by positivity
  have hρε : ρ ≤ ε := by
    linarith [min_le_left ε r]
  have hρr : ρ ≤ r := by
    linarith [min_le_right ε r]
  have hconv' : TendstoLocallyUniformlyOn (fun n => F (φ n)) g atTop (ball z₀ ρ) := by
    intro u hu z hz
    obtain ⟨s, hs, H⟩ := hconv u hu z (Metric.ball_subset_ball hρr hz)
    exact ⟨s, nhdsWithin_mono z (Metric.ball_subset_ball hρr) hs,
      hφ.tendsto_atTop H⟩
  have hne : ∀ n, ∀ z ∈ ball z₀ ρ, F (φ n) z ≠ 0 := by
    intro n z hz hz0
    exact hφzero n ⟨z, Metric.ball_subset_ball hρε hz, hz0⟩
  rcases forall_ne_or_forall_eq_of_tendstoLocallyUniformlyOn_ball
      (fun n => (hF (φ n)).mono (Metric.ball_subset_ball hρr)) hconv' hne with hne | heq
  · exact hne z₀ (mem_ball_self hρ) hg0
  · apply hnconst
    filter_upwards [ball_mem_nhds z₀ hρ] with z hz
    rw [heq z hz, hg0]

/-- A nonvanishing analytic germ has a normalized analytic logarithm on a sufficiently small ball.
This is the local branch construction used in Sokal, *Combinatorics, Probability and Computing*
13 (2004), Theorem 1.5(b). -/
theorem exists_ball_analytic_log_ratio {r : ℂ → ℂ} {z₀ : ℂ}
    (hr : AnalyticAt ℂ r z₀) (hr0 : r z₀ ≠ 0) :
    ∃ ε > 0, (∀ z ∈ ball z₀ ε, r z / r z₀ ∈ slitPlane) ∧
      (∀ z ∈ ball z₀ ε, AnalyticAt ℂ (fun w => log (r w / r z₀)) z) ∧
      (∀ z ∈ ball z₀ ε, exp (log (r z / r z₀)) = r z / r z₀) := by
  have hquot : AnalyticAt ℂ (fun z => r z / r z₀) z₀ := hr.div_const
  have hquot0 : r z₀ / r z₀ = 1 := div_self hr0
  have hmem : ∀ᶠ z in 𝓝 z₀, r z / r z₀ ∈ slitPlane :=
    hquot.continuousAt.eventually_mem
      (isOpen_slitPlane.mem_nhds (by simp [hquot0]))
  have han : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ (fun w => r w / r z₀) z :=
    hquot.eventually_analyticAt
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hmem.and han)
  refine ⟨ε, hε, ?_, ?_, ?_⟩
  · intro z hz
    exact (hball hz).1
  · intro z hz
    exact (hball hz).2.clog (hball hz).1
  · intro z hz
    exact exp_log (slitPlane_ne_zero (hball hz).1)

private theorem log_ratio_not_locally_constant {r : ℂ → ℂ} {z₀ : ℂ} {ε : ℝ}
    (hε : 0 < ε) (hr0 : r z₀ ≠ 0)
    (hslit : ∀ z ∈ ball z₀ ε, r z / r z₀ ∈ slitPlane)
    (hr : ¬∀ᶠ z in 𝓝 z₀, r z = r z₀) :
    ¬∀ᶠ z in 𝓝 z₀, log (r z / r z₀) = 0 := by
  intro hlog
  apply hr
  filter_upwards [hlog, ball_mem_nhds z₀ hε] with z hz hzball
  have heq : r z / r z₀ = 1 := by
    rw [← exp_log (slitPlane_ne_zero (hslit z hzball)), hz, exp_zero]
  exact (div_eq_one_iff_eq hr0).mp heq

private theorem tendstoLocallyUniformlyOn_div_nat {g : ℂ → ℂ} {s : Set ℂ}
    (hg : ContinuousOn g s) :
    TendstoLocallyUniformlyOn (fun (n : ℕ) z => g z / (n : ℂ))
      (fun _ => 0) atTop s := by
  have hfixed : TendstoLocallyUniformlyOn (fun _ : ℕ => g) g atTop s := by
    apply TendstoUniformlyOn.tendstoLocallyUniformlyOn
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    exact Eventually.of_forall fun _ z _ => by simpa using hε
  have hscalar : TendstoLocallyUniformlyOn
      (fun n : ℕ => fun _ : ℂ => (n : ℂ)⁻¹) (fun _ => 0) atTop s :=
    (tendsto_inv_atTop_nhds_zero_nat.tendstoUniformlyOn_const s).tendstoLocallyUniformlyOn
  have hprod := hfixed.mul₀ hscalar hg continuousOn_const
  have hF : ((fun _ : ℕ => g) * (fun n : ℕ => fun _ : ℂ => (n : ℂ)⁻¹)) =
      (fun (n : ℕ) z => g z / (n : ℂ)) := by
    funext n z
    simp [Pi.mul_apply, div_eq_mul_inv]
  have hzero : g * (fun _ : ℂ => 0) = fun _ => 0 := by
    funext z
    simp [Pi.mul_apply]
  rw [hF, hzero] at hprod
  exact hprod

private theorem tendstoLocallyUniformlyOn_div_nat_of_tendsto {g : ℂ → ℂ}
    {G : ℕ → ℂ → ℂ} {s : Set ℂ}
    (hG : TendstoLocallyUniformlyOn G g atTop s) (hg : ContinuousOn g s) :
    TendstoLocallyUniformlyOn (fun (n : ℕ) z => G n z / (n : ℂ))
      (fun _ => 0) atTop s := by
  have hscalar : TendstoLocallyUniformlyOn
      (fun n : ℕ => fun _ : ℂ => (n : ℂ)⁻¹) (fun _ => 0) atTop s :=
    (tendsto_inv_atTop_nhds_zero_nat.tendstoUniformlyOn_const s).tendstoLocallyUniformlyOn
  have hprod := hG.mul₀ hscalar hg continuousOn_const
  have hF : (G * (fun n : ℕ => fun _ : ℂ => (n : ℂ)⁻¹)) =
      (fun (n : ℕ) z => G n z / (n : ℂ)) := by
    funext n z
    simp [Pi.mul_apply, div_eq_mul_inv]
  have hzero : g * (fun _ : ℂ => 0) = fun _ => 0 := by
    funext z
    simp [Pi.mul_apply]
  rw [hF, hzero] at hprod
  exact hprod

private theorem tendstoLocallyUniformlyOn_log_of_closedBall_one
    {H : ℕ → ℂ → ℂ} {h : ℂ → ℂ} {s : Set ℂ}
    (hconv : TendstoLocallyUniformlyOn H h atTop s)
    (hh : Set.MapsTo h s (closedBall 1 (1 / 2)))
    (hH : ∀ᶠ n in atTop, Set.MapsTo (H n) s (closedBall 1 (1 / 2))) :
    TendstoLocallyUniformlyOn (fun n z => log (H n z)) (fun z => log (h z))
      atTop s := by
  have hsub : closedBall (1 : ℂ) (1 / 2 : ℝ) ⊆ slitPlane := by
    intro z hz
    apply ball_one_subset_slitPlane
    rw [mem_ball, dist_eq_norm]
    have hle : dist z (1 : ℂ) ≤ 1 / 2 := mem_closedBall.mp hz
    rw [dist_eq_norm] at hle
    linarith
  have hcont : ContinuousOn log (closedBall (1 : ℂ) (1 / 2 : ℝ)) :=
    fun z hz => (analyticAt_id.clog (hsub hz)).continuousAt.continuousWithinAt
  have huc : UniformContinuousOn log (closedBall (1 : ℂ) (1 / 2 : ℝ)) :=
    (isCompact_closedBall (1 : ℂ) (1 / 2 : ℝ)).uniformContinuousOn_of_continuous hcont
  simpa only [Function.comp_def] using
    huc.comp_tendstoLocallyUniformlyOn hconv hh hH

/-- A local eventual implication between zero sets transfers liminf limits of zeros.
This is the elementary comparison step used in Sokal, *Combinatorics, Probability and Computing*
13 (2004), Theorem 1.5(b). -/
theorem isLimitOfZeros_of_eventually_zero_imp {F G : ℕ → ℂ → ℂ}
    {z₀ : ℂ} {r : ℝ} (hr : 0 < r) (hG : IsLimitOfZeros G z₀)
    (himp : ∀ᶠ n in atTop, ∀ z ∈ ball z₀ r, G n z = 0 → F n z = 0) :
    IsLimitOfZeros F z₀ := by
  intro ε hε
  let ρ := min ε r / 2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρε : ρ ≤ ε := by dsimp [ρ]; have := min_le_left ε r; linarith
  have hρr : ρ ≤ r := by dsimp [ρ]; have := min_le_right ε r; linarith
  filter_upwards [hG ρ hρ, himp] with n hn hzero
  obtain ⟨z, hz, hGz⟩ := hn
  exact ⟨z, ball_subset_ball hρε hz,
    hzero z (ball_subset_ball hρr hz) hGz⟩

private theorem isLimitOfZeros_of_auxiliary {F G : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hG : ∀ n, DifferentiableOn ℂ (G n) (ball z₀ r))
    (hconv : TendstoLocallyUniformlyOn G g atTop (ball z₀ r))
    (hg0 : g z₀ = 0) (hnconst : ¬∀ᶠ z in 𝓝 z₀, g z = g z₀)
    (himp : ∀ᶠ n in atTop, ∀ z ∈ ball z₀ r, G n z = 0 → F n z = 0) :
    IsLimitOfZeros F z₀ := by
  apply isLimitOfZeros_of_eventually_zero_imp
    hr (isLimitOfZeros_of_tendstoLocallyUniformlyOn_ball hr hG hconv hg0 hnconst)
  exact himp

private theorem tendsto_log_rotated_div_nat (ω h : ℂ) (hω : ‖ω‖ = 1) :
    Tendsto (fun n : ℕ => log (ω⁻¹ ^ n * h) / (n : ℂ)) atTop (𝓝 0) := by
  have hnorm (n : ℕ) : ‖ω⁻¹ ^ n * h‖ = ‖h‖ := by
    simp [norm_pow, hω]
  have hbound (n : ℕ) : ‖log (ω⁻¹ ^ n * h)‖ ≤ |Real.log ‖h‖| + Real.pi := by
    calc
      ‖log (ω⁻¹ ^ n * h)‖ ≤ |(log (ω⁻¹ ^ n * h)).re| +
          |(log (ω⁻¹ ^ n * h)).im| := norm_le_abs_re_add_abs_im _
      _ = |Real.log ‖h‖| + |arg (ω⁻¹ ^ n * h)| := by
        rw [log_re, log_im, hnorm]
      _ ≤ |Real.log ‖h‖| + Real.pi := by gcongr; exact abs_arg_le_pi _
  have ht : Tendsto (fun n : ℕ => ‖log (ω⁻¹ ^ n * h)‖ / (n : ℝ))
      atTop (𝓝 0) :=
    tendsto_bdd_div_atTop_nhds_zero
      (Eventually.of_forall fun n => norm_nonneg _)
      (Eventually.of_forall hbound) tendsto_natCast_atTop_atTop
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa [norm_div] using ht

private theorem tendstoLocallyUniformlyOn_log_auxiliary {r h : ℂ → ℂ} {z₀ : ℂ}
    {ρ : ℝ} (hr0 : ‖r z₀‖ = 1)
    (hH : ContinuousOn (fun z => log (h z / h z₀)) (ball z₀ ρ)) :
    TendstoLocallyUniformlyOn
      (fun (n : ℕ) z => log (r z / r z₀) -
        log ((r z₀)⁻¹ ^ n * h z₀) / (n : ℂ) -
        log (h z / h z₀) / (n : ℂ))
      (fun z => log (r z / r z₀)) atTop (ball z₀ ρ) := by
  let L : ℂ → ℂ := fun z => log (r z / r z₀)
  let H : ℂ → ℂ := fun z => log (h z / h z₀)
  let c : ℕ → ℂ := fun n => log ((r z₀)⁻¹ ^ n * h z₀) / (n : ℂ)
  have hfixed : TendstoLocallyUniformlyOn (fun _ : ℕ => L) L atTop (ball z₀ ρ) := by
    apply TendstoUniformlyOn.tendstoLocallyUniformlyOn
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    exact Eventually.of_forall fun _ z _ => by simpa using hε
  have hc : TendstoLocallyUniformlyOn (fun n => fun _ : ℂ => c n)
      (fun _ => 0) atTop (ball z₀ ρ) :=
    ((tendsto_log_rotated_div_nat (r z₀) (h z₀) hr0).tendstoUniformlyOn_const
      (ball z₀ ρ)).tendstoLocallyUniformlyOn
  have hHdiv : TendstoLocallyUniformlyOn (fun (n : ℕ) z => H z / (n : ℂ))
      (fun _ => 0) atTop (ball z₀ ρ) := tendstoLocallyUniformlyOn_div_nat hH
  have hconv := (hfixed.sub hc).sub hHdiv
  have hF : ((fun _ : ℕ => L) - (fun n => fun _ : ℂ => c n) -
      (fun (n : ℕ) z => H z / (n : ℂ))) =
      (fun (n : ℕ) z => L z - c n - H z / (n : ℂ)) := by
    funext n z
    simp [Pi.sub_apply]
  have hlim : (L - (fun _ => 0) - (fun _ => 0)) = L := by
    funext z
    simp [Pi.sub_apply]
  rw [hF, hlim] at hconv
  exact hconv

private theorem tendstoLocallyUniformlyOn_varying_log_auxiliary
    {r : ℂ → ℂ} {h₀ : ℂ} {K : ℕ → ℂ → ℂ} {k : ℂ → ℂ}
    {z₀ : ℂ} {ρ : ℝ} (hr0 : ‖r z₀‖ = 1)
    (hK : TendstoLocallyUniformlyOn (fun n z => log (K n z))
      (fun z => log (k z)) atTop (ball z₀ ρ))
    (hkcont : ContinuousOn (fun z => log (k z)) (ball z₀ ρ)) :
    TendstoLocallyUniformlyOn
      (fun (n : ℕ) z => log (r z / r z₀) -
        log ((r z₀)⁻¹ ^ n * h₀) / (n : ℂ) - log (K n z) / (n : ℂ))
      (fun z => log (r z / r z₀)) atTop (ball z₀ ρ) := by
  let L : ℂ → ℂ := fun z => log (r z / r z₀)
  have hfixed : TendstoLocallyUniformlyOn (fun _ : ℕ => L) L atTop (ball z₀ ρ) := by
    apply TendstoUniformlyOn.tendstoLocallyUniformlyOn
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    exact Eventually.of_forall fun _ z _ => by simpa using hε
  have hc : TendstoLocallyUniformlyOn
      (fun n : ℕ => fun _ : ℂ => log ((r z₀)⁻¹ ^ n * h₀) / (n : ℂ))
      (fun _ => 0) atTop (ball z₀ ρ) :=
    ((tendsto_log_rotated_div_nat (r z₀) h₀ hr0).tendstoUniformlyOn_const
      (ball z₀ ρ)).tendstoLocallyUniformlyOn
  have hKdiv := tendstoLocallyUniformlyOn_div_nat_of_tendsto hK hkcont
  have hconv := (hfixed.sub hc).sub hKdiv
  have hF : ((fun _ : ℕ => L) -
      (fun n : ℕ => fun _ : ℂ => log ((r z₀)⁻¹ ^ n * h₀) / (n : ℂ)) -
      (fun (n : ℕ) z => log (K n z) / (n : ℂ))) =
      (fun (n : ℕ) z => L z -
        log ((r z₀)⁻¹ ^ n * h₀) / (n : ℂ) - log (K n z) / (n : ℂ)) := by
    funext n z
    simp [Pi.sub_apply]
  have hlim : (L - (fun _ => 0) - (fun _ => 0)) = L := by
    funext z
    simp [Pi.sub_apply]
  rw [hF, hlim] at hconv
  exact hconv

private theorem log_auxiliary_zero_imp_pow_eq {r h : ℂ → ℂ} {z₀ z : ℂ} {ρ : ℝ}
    (hr0 : r z₀ ≠ 0) (hh0 : h z₀ ≠ 0) (hz : z ∈ ball z₀ ρ)
    (hR : ∀ w ∈ ball z₀ ρ, exp (log (r w / r z₀)) = r w / r z₀)
    (hH : ∀ w ∈ ball z₀ ρ, exp (log (h w / h z₀)) = h w / h z₀)
    {n : ℕ} (hn : n ≠ 0)
    (hG : log (r z / r z₀) - log ((r z₀)⁻¹ ^ n * h z₀) / (n : ℂ) -
      log (h z / h z₀) / (n : ℂ) = 0) :
    r z ^ n = h z := by
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hEq : (n : ℂ) * log (r z / r z₀) =
      log ((r z₀)⁻¹ ^ n * h z₀) + log (h z / h z₀) := by
    field_simp [hnC] at hG
    simp only [inv_eq_one_div] at ⊢
    linear_combination hG
  have hexp := congrArg exp hEq
  rw [exp_add, exp_nat_mul, hR z hz, exp_log, hH z hz] at hexp
  · calc
      r z ^ n = (r z / r z₀) ^ n * (r z₀) ^ n := by
        rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hr0)]
      _ = h z := by
        rw [hexp]
        field_simp [hr0, hh0]
        simp only [one_div]
        calc
          (r z₀)⁻¹ ^ n * h z * (r z₀) ^ n =
              ((r z₀)⁻¹ * r z₀) ^ n * h z := by rw [mul_pow]; ring
          _ = h z := by simp [hr0]
  · exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hr0)) hh0

private theorem varying_log_auxiliary_zero_imp_pow_eq
    {r K : ℂ → ℂ} {h₀ z₀ z : ℂ} {ρ : ℝ}
    (hr0 : r z₀ ≠ 0) (hh₀ : h₀ ≠ 0) (hz : z ∈ ball z₀ ρ)
    (hR : ∀ w ∈ ball z₀ ρ, exp (log (r w / r z₀)) = r w / r z₀)
    (hK : ∀ w ∈ ball z₀ ρ, exp (log (K w)) = K w)
    {n : ℕ} (hn : n ≠ 0)
    (hG : log (r z / r z₀) - log ((r z₀)⁻¹ ^ n * h₀) / (n : ℂ) -
      log (K z) / (n : ℂ) = 0) :
    r z ^ n = h₀ * K z := by
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hEq : (n : ℂ) * log (r z / r z₀) =
      log ((r z₀)⁻¹ ^ n * h₀) + log (K z) := by
    field_simp [hnC] at hG
    simp only [inv_eq_one_div] at ⊢
    linear_combination hG
  have hexp := congrArg exp hEq
  rw [exp_add, exp_nat_mul, hR z hz, exp_log, hK z hz] at hexp
  · calc
      r z ^ n = (r z / r z₀) ^ n * (r z₀) ^ n := by
        rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hr0)]
      _ = h₀ * K z := by
        rw [hexp]
        calc
          (r z₀)⁻¹ ^ n * h₀ * K z * (r z₀) ^ n =
              ((r z₀)⁻¹ * r z₀) ^ n * (h₀ * K z) := by rw [mul_pow]; ring
          _ = h₀ * K z := by simp [hr0]
  · exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hr0)) hh₀

private theorem isLimitOfZeros_pow_sub_varying_of_closedBall_one
    {r : ℂ → ℂ} {h₀ : ℂ} {K : ℕ → ℂ → ℂ} {k : ℂ → ℂ}
    {z₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hr : AnalyticAt ℂ r z₀) (hrunit : ‖r z₀‖ = 1) (hh₀ : h₀ ≠ 0)
    (hnconst : ¬∀ᶠ z in 𝓝 z₀, r z = r z₀)
    (hKanalytic : ∀ n, ∀ z ∈ ball z₀ ρ, AnalyticAt ℂ (K n) z)
    (hKmap : ∀ n, Set.MapsTo (K n) (ball z₀ ρ) (closedBall 1 (1 / 2)))
    (hkmap : Set.MapsTo k (ball z₀ ρ) (closedBall 1 (1 / 2)))
    (hKconv : TendstoLocallyUniformlyOn K k atTop (ball z₀ ρ)) :
    IsLimitOfZeros (fun n z => r z ^ n - h₀ * K n z) z₀ := by
  have hr0 : r z₀ ≠ 0 := by
    exact fun heq => by simp [heq] at hrunit
  obtain ⟨ρr, hρr, hRslit, hRanalytic, hRexp⟩ := exists_ball_analytic_log_ratio hr hr0
  let δ := min ρ ρr
  have hδ : 0 < δ := lt_min hρ hρr
  have hsubK : ball z₀ δ ⊆ ball z₀ ρ := ball_subset_ball (min_le_left _ _)
  have hsubR : ball z₀ δ ⊆ ball z₀ ρr := ball_subset_ball (min_le_right _ _)
  let L : ℂ → ℂ := fun z => log (r z / r z₀)
  let G : ℕ → ℂ → ℂ := fun n z => L z -
    log ((r z₀)⁻¹ ^ n * h₀) / (n : ℂ) - log (K n z) / (n : ℂ)
  have hkcont : ContinuousOn (fun z => log (k z)) (ball z₀ δ) := by
    have hcont : ContinuousOn k (ball z₀ ρ) :=
      hKconv.continuousOn (Frequently.of_forall fun n z hz =>
        (hKanalytic n z hz).continuousAt.continuousWithinAt)
    intro z hz
    have hkz : k z ∈ slitPlane := by
      apply ball_one_subset_slitPlane
      have hkz' := hkmap (hsubK hz)
      rw [mem_ball]
      have := mem_closedBall.mp hkz'
      linarith
    exact ((analyticAt_id.clog hkz).continuousAt.comp_continuousWithinAt
      (hcont.mono hsubK z hz))
  have hlogconv : TendstoLocallyUniformlyOn
      (fun n z => log (K n z)) (fun z => log (k z)) atTop (ball z₀ δ) :=
    tendstoLocallyUniformlyOn_log_of_closedBall_one
      (hKconv.mono hsubK) (fun z hz => hkmap (hsubK hz))
      (Eventually.of_forall fun n z hz => hKmap n (hsubK hz))
  have hconv : TendstoLocallyUniformlyOn G L atTop (ball z₀ δ) :=
    tendstoLocallyUniformlyOn_varying_log_auxiliary hrunit hlogconv hkcont
  have hKexp : ∀ n, ∀ z ∈ ball z₀ δ, exp (log (K n z)) = K n z := by
    intro n z hz
    apply exp_log
    apply slitPlane_ne_zero
    apply ball_one_subset_slitPlane
    have hmap := hKmap n (hsubK hz)
    rw [mem_ball]
    have := mem_closedBall.mp hmap
    linarith
  have hGanalytic : ∀ n, DifferentiableOn ℂ (G n) (ball z₀ δ) := by
    intro n z hz
    have hKslit : K n z ∈ slitPlane := by
      apply ball_one_subset_slitPlane
      have hmap := hKmap n (hsubK hz)
      rw [mem_ball]
      have := mem_closedBall.mp hmap
      linarith
    exact ((hRanalytic z (hsubR hz)).differentiableAt.sub
      (differentiableAt_const _)).sub
      (((hKanalytic n z (hsubK hz)).clog hKslit).differentiableAt.div_const _)
      |>.differentiableWithinAt
  have hL0 : L z₀ = 0 := by simp [L]
  have hLnonconst : ¬∀ᶠ z in 𝓝 z₀, L z = L z₀ := by
    rw [hL0]
    exact log_ratio_not_locally_constant hδ hr0
      (fun z hz => hRslit z (hsubR hz)) hnconst
  have himp : ∀ᶠ n in atTop, ∀ z ∈ ball z₀ δ,
      G n z = 0 → r z ^ n - h₀ * K n z = 0 := by
    filter_upwards [eventually_ne_atTop 0] with n hn z hz hzero
    apply sub_eq_zero.mpr
    exact varying_log_auxiliary_zero_imp_pow_eq hr0 hh₀ hz
      (fun w hw => hRexp w (hsubR hw)) (hKexp n) hn hzero
  exact isLimitOfZeros_of_auxiliary hδ hGanalytic hconv hL0 hLnonconst himp

/-- The two-term analytic zero-limit theorem, in normalized form. It is the two-dominant
case of Sokal, *Combinatorics, Probability and Computing* 13 (2004), Theorem 1.5. -/
theorem isLimitOfZeros_pow_sub_of_analyticAt {r h : ℂ → ℂ} {z₀ : ℂ}
    (hr : AnalyticAt ℂ r z₀) (hh : AnalyticAt ℂ h z₀)
    (hrunit : ‖r z₀‖ = 1) (hh0 : h z₀ ≠ 0)
    (hnconst : ¬∀ᶠ z in 𝓝 z₀, r z = r z₀) :
    IsLimitOfZeros (fun n z => r z ^ n - h z) z₀ := by
  have hr0 : r z₀ ≠ 0 := by
    exact fun heq => by simp [heq] at hrunit
  obtain ⟨ρr, hρr, hRslit, hRanalytic, hRexp⟩ := exists_ball_analytic_log_ratio hr hr0
  obtain ⟨ρh, hρh, hHslit, hHanalytic, hHexp⟩ := exists_ball_analytic_log_ratio hh hh0
  let ρ := min ρr ρh
  have hρ : 0 < ρ := lt_min hρr hρh
  have hsubR : ball z₀ ρ ⊆ ball z₀ ρr :=
    ball_subset_ball (min_le_left _ _)
  have hsubH : ball z₀ ρ ⊆ ball z₀ ρh :=
    ball_subset_ball (min_le_right _ _)
  let L : ℂ → ℂ := fun z => log (r z / r z₀)
  let H : ℂ → ℂ := fun z => log (h z / h z₀)
  let G : ℕ → ℂ → ℂ := fun n z => L z -
    log ((r z₀)⁻¹ ^ n * h z₀) / (n : ℂ) - H z / (n : ℂ)
  have hHcont : ContinuousOn H (ball z₀ ρ) := by
    intro z hz
    exact (hHanalytic z (hsubH hz)).continuousAt.continuousWithinAt
  have hconv : TendstoLocallyUniformlyOn G L atTop (ball z₀ ρ) :=
    tendstoLocallyUniformlyOn_log_auxiliary hrunit hHcont
  have hGanalytic : ∀ n, DifferentiableOn ℂ (G n) (ball z₀ ρ) := by
    intro n z hz
    exact ((hRanalytic z (hsubR hz)).differentiableAt.sub
      (differentiableAt_const _)).sub
      ((hHanalytic z (hsubH hz)).differentiableAt.div_const _)
      |>.differentiableWithinAt
  have hL0 : L z₀ = 0 := by simp [L]
  have hLnonconst : ¬∀ᶠ z in 𝓝 z₀, L z = L z₀ := by
    rw [hL0]
    exact log_ratio_not_locally_constant hρ hr0
      (fun z hz => hRslit z (hsubR hz)) hnconst
  have himp : ∀ᶠ n in atTop, ∀ z ∈ ball z₀ ρ,
      G n z = 0 → r z ^ n - h z = 0 := by
    filter_upwards [eventually_ne_atTop 0] with n hn z hz hzero
    apply sub_eq_zero.mpr
    exact log_auxiliary_zero_imp_pow_eq hr0 hh0 hz
      (fun w hw => hRexp w (hsubR hw))
      (fun w hw => hHexp w (hsubH hw)) hn hzero
  exact isLimitOfZeros_of_auxiliary hρ hGanalytic hconv hL0 hLnonconst himp

/-- Two nonzero, equimodular analytic bases with a nonconstant ratio produce nearby zeros of
their two-term exponential sum. This is the two-term case of Sokal, *Combinatorics, Probability
and Computing* 13 (2004), Theorem 1.5(b). -/
theorem isLimitOfZeros_two_terms {α₁ α₂ β₁ β₂ : ℂ → ℂ} {z₀ : ℂ}
    (hα₁ : AnalyticAt ℂ α₁ z₀) (hα₂ : AnalyticAt ℂ α₂ z₀)
    (hβ₁ : AnalyticAt ℂ β₁ z₀) (hβ₂ : AnalyticAt ℂ β₂ z₀)
    (hα₁0 : α₁ z₀ ≠ 0) (hα₂0 : α₂ z₀ ≠ 0)
    (hβ₂0 : β₂ z₀ ≠ 0) (heq : ‖β₁ z₀‖ = ‖β₂ z₀‖)
    (hnconst : ¬∀ᶠ z in 𝓝 z₀, β₁ z / β₂ z = β₁ z₀ / β₂ z₀) :
    IsLimitOfZeros (fun n z => α₁ z * β₁ z ^ n + α₂ z * β₂ z ^ n) z₀ := by
  let r : ℂ → ℂ := fun z => β₁ z / β₂ z
  let h : ℂ → ℂ := fun z => -α₂ z / α₁ z
  have hr : AnalyticAt ℂ r z₀ := hβ₁.div hβ₂ hβ₂0
  have hh : AnalyticAt ℂ h z₀ := hα₂.neg.div hα₁ hα₁0
  have hrunit : ‖r z₀‖ = 1 := by
    simp [r, heq, hβ₂0]
  have hh0 : h z₀ ≠ 0 := div_ne_zero (neg_ne_zero.mpr hα₂0) hα₁0
  have hβ₂ev : ∀ᶠ z in 𝓝 z₀, β₂ z ≠ 0 :=
    hβ₂.continuousAt.eventually_ne hβ₂0
  have hα₁ev : ∀ᶠ z in 𝓝 z₀, α₁ z ≠ 0 :=
    hα₁.continuousAt.eventually_ne hα₁0
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp (hβ₂ev.and hα₁ev)
  have himp : ∀ᶠ n in atTop, ∀ z ∈ ball z₀ ρ,
      r z ^ n - h z = 0 → α₁ z * β₁ z ^ n + α₂ z * β₂ z ^ n = 0 := by
    exact Eventually.of_forall fun n z hz hzero => by
      have hβ₂z : β₂ z ≠ 0 := (hball hz).1
      have hα₁z : α₁ z ≠ 0 := (hball hz).2
      have heqz : r z ^ n = h z := sub_eq_zero.mp hzero
      simp only [r, h] at heqz
      rw [div_pow] at heqz
      field_simp [hα₁z, hβ₂z] at heqz
      linear_combination heqz
  exact isLimitOfZeros_of_eventually_zero_imp hρ
    (isLimitOfZeros_pow_sub_of_analyticAt hr hh hrunit hh0 hnconst) himp

private theorem tendstoUniformlyOn_mul_pow_of_bounds {a b : ℂ → ℂ}
    {s : Set ℂ} {M q : ℝ} (hM : 0 ≤ M) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (ha : ∀ z ∈ s, ‖a z‖ ≤ M) (hb : ∀ z ∈ s, ‖b z‖ ≤ q) :
    TendstoUniformlyOn (fun n z => a z * b z ^ n) (fun _ => 0) atTop s := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have ht : Tendsto (fun n : ℕ => M * q ^ n) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1)
  filter_upwards [ht.eventually (eventually_lt_nhds hε)] with n hn z hz
  rw [dist_zero_left]
  calc
    ‖a z * b z ^ n‖ = ‖a z‖ * ‖b z‖ ^ n := by simp
    _ ≤ M * q ^ n := by
      gcongr
      · exact ha z hz
      · exact hb z hz
    _ < ε := hn

private theorem exists_ball_tendstoUniformlyOn_mul_pow_zero {a b : ℂ → ℂ} {z₀ : ℂ}
    (ha : ContinuousAt a z₀) (hb : ContinuousAt b z₀) (h : ‖b z₀‖ < 1) :
    ∃ r > 0, TendstoUniformlyOn (fun n z => a z * b z ^ n)
      (fun _ => (0 : ℂ)) atTop (ball z₀ r) := by
  let q := (‖b z₀‖ + 1) / 2
  let M := ‖a z₀‖ + 1
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hq : ‖b z₀‖ < q := by dsimp [q]; linarith
  have hMev : ∀ᶠ z in 𝓝 z₀, ‖a z‖ < M :=
    ha.norm.eventually (eventually_lt_nhds (by dsimp [M]; linarith))
  have hqev : ∀ᶠ z in 𝓝 z₀, ‖b z‖ < q :=
    hb.norm.eventually (eventually_lt_nhds hq)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hMev.and hqev)
  exact ⟨r, hr, tendstoUniformlyOn_mul_pow_of_bounds hM hq0 hq1
    (fun z hz => (hball hz).1.le) (fun z hz => (hball hz).2.le)⟩

/-- A finite sum of continuous coefficients times uniformly subunit bases tends uniformly to zero
on some ball. This is the elementary tail estimate in Sokal, *Combinatorics, Probability and
Computing* 13 (2004), Theorem 1.5. -/
theorem exists_ball_tendstoUniformlyOn_sum_mul_pow_zero {κ : Type*}
    (s : Finset κ) (a b : κ → ℂ → ℂ) {z₀ : ℂ}
    (ha : ∀ k ∈ s, ContinuousAt (a k) z₀)
    (hb : ∀ k ∈ s, ContinuousAt (b k) z₀)
    (hsmall : ∀ k ∈ s, ‖b k z₀‖ < 1) :
    ∃ r > 0, TendstoUniformlyOn
      (fun n z => ∑ k ∈ s, a k z * b k z ^ n)
      (fun _ => (0 : ℂ)) atTop (ball z₀ r) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨1, by norm_num, ?_⟩
      simp only [Finset.sum_empty]
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      exact Eventually.of_forall fun _ _ _ => by simpa using hε
  | @insert k s hks ih =>
      have ha' : ∀ j ∈ s, ContinuousAt (a j) z₀ :=
        fun j hj => ha j (Finset.mem_insert_of_mem hj)
      have hb' : ∀ j ∈ s, ContinuousAt (b j) z₀ :=
        fun j hj => hb j (Finset.mem_insert_of_mem hj)
      have hsmall' : ∀ j ∈ s, ‖b j z₀‖ < 1 :=
        fun j hj => hsmall j (Finset.mem_insert_of_mem hj)
      obtain ⟨r₁, hr₁, h₁⟩ := ih ha' hb' hsmall'
      obtain ⟨r₂, hr₂, h₂⟩ := exists_ball_tendstoUniformlyOn_mul_pow_zero
        (ha k (Finset.mem_insert_self _ _))
        (hb k (Finset.mem_insert_self _ _))
        (hsmall k (Finset.mem_insert_self _ _))
      let r := min r₁ r₂
      have hr : 0 < r := lt_min hr₁ hr₂
      have hsum : TendstoUniformlyOn
          (fun n z => ∑ j ∈ s, a j z * b j z ^ n)
          (fun _ => (0 : ℂ)) atTop (ball z₀ r) :=
        h₁.mono (ball_subset_ball (min_le_left _ _))
      have hterm : TendstoUniformlyOn
          (fun n z => a k z * b k z ^ n)
          (fun _ => (0 : ℂ)) atTop (ball z₀ r) :=
        h₂.mono (ball_subset_ball (min_le_right _ _))
      refine ⟨r, hr, ?_⟩
      convert hterm.add hsum using 1
      · funext n z
        simp [Finset.sum_insert hks]
      · funext z
        simp

/-- A finite normalized tail with strictly smaller bases tends uniformly to zero on a ball.
This is the tail estimate in Sokal, *Combinatorics, Probability and Computing* 13 (2004),
Theorem 1.5(b). -/
theorem exists_ball_tendstoUniformlyOn_normalized_tail {κ : Type*}
    (s : Finset κ) (α β : κ → ℂ → ℂ) (i j : κ) {z₀ : ℂ}
    (hα : ∀ k ∈ s, AnalyticAt ℂ (α k) z₀)
    (hβ : ∀ k ∈ s, AnalyticAt ℂ (β k) z₀)
    (hαi : AnalyticAt ℂ (α i) z₀) (hβj : AnalyticAt ℂ (β j) z₀)
    (hαi0 : α i z₀ ≠ 0) (hβj0 : β j z₀ ≠ 0)
    (hsmall : ∀ k ∈ s, ‖β k z₀‖ < ‖β j z₀‖) :
    ∃ ρ > 0, TendstoUniformlyOn
      (fun n z => ∑ k ∈ s, (α k z / α i z) * (β k z / β j z) ^ n)
      (fun _ => (0 : ℂ)) atTop (ball z₀ ρ) := by
  apply exists_ball_tendstoUniformlyOn_sum_mul_pow_zero s
    (fun k z => α k z / α i z) (fun k z => β k z / β j z)
  · intro k hk
    exact ((hα k hk).div hαi hαi0).continuousAt
  · intro k hk
    exact ((hβ k hk).div hβj hβj0).continuousAt
  · intro k hk
    rw [norm_div]
    exact (div_lt_one (norm_pos_iff.mpr hβj0)).mpr (hsmall k hk)

private theorem exists_ball_eventually_normalized_perturb_in_closedBall
    {h : ℂ → ℂ} {T : ℕ → ℂ → ℂ} {z₀ : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hh : ContinuousAt h z₀) (hh0 : h z₀ ≠ 0)
    (hT : TendstoUniformlyOn T (fun _ => (0 : ℂ)) atTop (ball z₀ ρ)) :
    ∃ δ > 0, δ ≤ ρ ∧
      Set.MapsTo (fun z => h z / h z₀) (ball z₀ δ) (closedBall 1 (1 / 2)) ∧
      ∀ᶠ n in atTop,
      Set.MapsTo (fun z => (h z - T n z) / h z₀)
        (ball z₀ δ) (closedBall 1 (1 / 2)) := by
  have hclose0 : ‖h z₀ / h z₀ - 1‖ < (1 / 4 : ℝ) := by simp [hh0]
  have hcloseev : ∀ᶠ z in 𝓝 z₀, ‖h z / h z₀ - 1‖ < (1 / 4 : ℝ) :=
    ((hh.div_const _).sub continuousAt_const).norm.eventually
      (eventually_lt_nhds hclose0)
  obtain ⟨ε, hε, hclose⟩ := Metric.mem_nhds_iff.mp hcloseev
  let δ := min ε ρ
  have hδ : 0 < δ := lt_min hε hρ
  have hδρ : δ ≤ ρ := min_le_right _ _
  have hδε : δ ≤ ε := min_le_left _ _
  rw [Metric.tendstoUniformlyOn_iff] at hT
  have hlim := hT (‖h z₀‖ / 4) (by positivity)
  refine ⟨δ, hδ, hδρ, ?_, ?_⟩
  · intro z hz
    rw [mem_closedBall, dist_eq_norm]
    exact (hclose (ball_subset_ball hδε hz)).le.trans (by norm_num)
  filter_upwards [hlim] with n hn z hz
  rw [mem_closedBall, dist_eq_norm]
  have hsmall : ‖T n z‖ < ‖h z₀‖ / 4 := by
    simpa [dist_zero_left] using hn z (ball_subset_ball hδρ hz)
  have hratio : ‖T n z / h z₀‖ < 1 / 4 := by
    rw [norm_div]
    exact (div_lt_iff₀ (norm_pos_iff.mpr hh0)).mpr (by linarith)
  have hnear : ‖h z / h z₀ - 1‖ < 1 / 4 :=
    hclose (ball_subset_ball hδε hz)
  calc
    ‖(h z - T n z) / h z₀ - 1‖ =
        ‖(h z / h z₀ - 1) - T n z / h z₀‖ := by
      congr 1
      ring
    _ ≤ ‖h z / h z₀ - 1‖ + ‖T n z / h z₀‖ := norm_sub_le _ _
    _ ≤ 1 / 2 := by linarith

private theorem tendstoUniformlyOn_normalized_perturb
    {h : ℂ → ℂ} {T : ℕ → ℂ → ℂ} {z₀ : ℂ} {s : Set ℂ}
    (hh0 : h z₀ ≠ 0)
    (hT : TendstoUniformlyOn T (fun _ => (0 : ℂ)) atTop s) :
    TendstoUniformlyOn (fun n z => (h z - T n z) / h z₀)
      (fun z => h z / h z₀) atTop s := by
  rw [Metric.tendstoUniformlyOn_iff] at hT ⊢
  intro ε hε
  have hnorm : 0 < ‖h z₀‖ := norm_pos_iff.mpr hh0
  filter_upwards [hT (ε * ‖h z₀‖) (mul_pos hε hnorm)] with n hn z hz
  have hsmall : ‖T n z‖ < ε * ‖h z₀‖ := by
    simpa [dist_zero_left] using hn z hz
  rw [dist_eq_norm]
  have heq : (h z - T n z) / h z₀ - h z / h z₀ = -(T n z / h z₀) := by ring
  rw [norm_sub_rev, heq, norm_neg, norm_div]
  exact (div_lt_iff₀ hnorm).mpr hsmall

private theorem isLimitOfZeros_pow_sub_perturbed
    {r h : ℂ → ℂ} {T : ℕ → ℂ → ℂ} {z₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hr : AnalyticAt ℂ r z₀) (hrunit : ‖r z₀‖ = 1)
    (hnconst : ¬∀ᶠ z in 𝓝 z₀, r z = r z₀)
    (hh : ∀ z ∈ ball z₀ ρ, AnalyticAt ℂ h z) (hh0 : h z₀ ≠ 0)
    (hTanalytic : ∀ n, ∀ z ∈ ball z₀ ρ, AnalyticAt ℂ (T n) z)
    (hTconv : TendstoUniformlyOn T (fun _ => (0 : ℂ)) atTop (ball z₀ ρ)) :
    IsLimitOfZeros (fun n z => r z ^ n - (h z - T n z)) z₀ := by
  obtain ⟨δ, hδ, hδρ, hkmap, hrawmap⟩ :=
    exists_ball_eventually_normalized_perturb_in_closedBall hρ
      (hh z₀ (mem_ball_self hρ)).continuousAt hh0 hTconv
  obtain ⟨N, hN⟩ := eventually_atTop.mp hrawmap
  let k : ℂ → ℂ := fun z => h z / h z₀
  let K : ℕ → ℂ → ℂ := fun n z =>
    if n < N then 1 else (h z - T n z) / h z₀
  have hKmap : ∀ n, Set.MapsTo (K n) (ball z₀ δ) (closedBall 1 (1 / 2)) := by
    intro n z hz
    by_cases hn : n < N
    · simp [K, hn]
    · simpa [K, hn] using hN n (Nat.le_of_not_gt hn) hz
  have hKanalytic : ∀ n, ∀ z ∈ ball z₀ δ, AnalyticAt ℂ (K n) z := by
    intro n z hz
    by_cases hn : n < N
    · simpa [K, hn] using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) z)
    · simpa [K, hn] using
        ((hh z (ball_subset_ball hδρ hz)).sub
          (hTanalytic n z (ball_subset_ball hδρ hz))).div_const
  have hrawconv : TendstoLocallyUniformlyOn
      (fun n z => (h z - T n z) / h z₀) k atTop (ball z₀ δ) :=
    ((tendstoUniformlyOn_normalized_perturb hh0 hTconv).mono
      (ball_subset_ball hδρ)).tendstoLocallyUniformlyOn
  have hKconv : TendstoLocallyUniformlyOn K k atTop (ball z₀ δ) := by
    apply hrawconv.congr_inseparable
    filter_upwards [eventually_ge_atTop N] with n hn z hz
    exact .of_eq (by simp [K, Nat.not_lt.mpr hn])
  have hzeros := isLimitOfZeros_pow_sub_varying_of_closedBall_one hδ
    hr hrunit hh0 hnconst hKanalytic hKmap hkmap hKconv
  apply isLimitOfZeros_of_eventually_zero_imp hδ hzeros
  filter_upwards [eventually_ge_atTop N] with n hn z hz hzero
  simp only [K, Nat.not_lt.mpr hn, ↓reduceIte] at hzero
  rw [mul_div_cancel₀ _ hh0] at hzero
  exact hzero

/-- Two equimodular dominant terms in a finite analytic exponential sum produce nearby zeros.
The sum is displayed as two leading terms and its subdominant finite tail. This is Sokal,
*Combinatorics, Probability and Computing* 13 (2004), Theorem 1.5(b), under nonvanishing
coefficient hypotheses. -/
theorem isLimitOfZeros_two_dominant_with_tail {κ : Type*}
    (s : Finset κ) (α β : κ → ℂ → ℂ) (i j : κ) {z₀ : ℂ}
    (hαi : AnalyticAt ℂ (α i) z₀) (hαj : AnalyticAt ℂ (α j) z₀)
    (hβi : AnalyticAt ℂ (β i) z₀) (hβj : AnalyticAt ℂ (β j) z₀)
    (hα : ∀ k ∈ s, AnalyticAt ℂ (α k) z₀)
    (hβ : ∀ k ∈ s, AnalyticAt ℂ (β k) z₀)
    (hαi0 : α i z₀ ≠ 0) (hαj0 : α j z₀ ≠ 0)
    (hβj0 : β j z₀ ≠ 0) (heq : ‖β i z₀‖ = ‖β j z₀‖)
    (hsmall : ∀ k ∈ s, ‖β k z₀‖ < ‖β j z₀‖)
    (hnconst : ¬∀ᶠ z in 𝓝 z₀, β i z / β j z = β i z₀ / β j z₀) :
    IsLimitOfZeros (fun n z => α i z * β i z ^ n + α j z * β j z ^ n +
      ∑ k ∈ s, α k z * β k z ^ n) z₀ := by
  classical
  let r : ℂ → ℂ := fun z => β i z / β j z
  let h : ℂ → ℂ := fun z => -α j z / α i z
  let T : ℕ → ℂ → ℂ := fun n z =>
    ∑ k ∈ s, (α k z / α i z) * (β k z / β j z) ^ n
  have hr : AnalyticAt ℂ r z₀ := hβi.div hβj hβj0
  have hrunit : ‖r z₀‖ = 1 := by simp [r, heq, hβj0]
  have hh0 : h z₀ ≠ 0 := div_ne_zero (neg_ne_zero.mpr hαj0) hαi0
  obtain ⟨ρT, hρT, hTconv⟩ :=
    exists_ball_tendstoUniformlyOn_normalized_tail s α β i j
      hα hβ hαi hβj hαi0 hβj0 hsmall
  have hαiev : ∀ᶠ z in 𝓝 z₀, α i z ≠ 0 :=
    hαi.continuousAt.eventually_ne hαi0
  have hβjev : ∀ᶠ z in 𝓝 z₀, β j z ≠ 0 :=
    hβj.continuousAt.eventually_ne hβj0
  have hαev : ∀ᶠ z in 𝓝 z₀, ∀ k ∈ s, AnalyticAt ℂ (α k) z := by
    exact (eventually_all_finset s).2 fun k hk => (hα k hk).eventually_analyticAt
  have hβev : ∀ᶠ z in 𝓝 z₀, ∀ k ∈ s, AnalyticAt ℂ (β k) z := by
    exact (eventually_all_finset s).2 fun k hk => (hβ k hk).eventually_analyticAt
  have hnear : ∀ᶠ z in 𝓝 z₀, (α i z ≠ 0 ∧ β j z ≠ 0) ∧
      (AnalyticAt ℂ (α i) z ∧ AnalyticAt ℂ (α j) z ∧
        AnalyticAt ℂ (β i) z ∧ AnalyticAt ℂ (β j) z) ∧
      (∀ k ∈ s, AnalyticAt ℂ (α k) z) ∧
      (∀ k ∈ s, AnalyticAt ℂ (β k) z) := by
    filter_upwards [hαiev, hβjev, hαi.eventually_analyticAt,
      hαj.eventually_analyticAt, hβi.eventually_analyticAt,
      hβj.eventually_analyticAt, hαev, hβev] with
      z hαiz hβjz hαiz' hαjz hβiz hβjz' hαz hβz
    exact ⟨⟨hαiz, hβjz⟩, ⟨hαiz', hαjz, hβiz, hβjz'⟩, hαz, hβz⟩
  obtain ⟨ρA, hρA, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let ρ := min ρT ρA
  have hρ : 0 < ρ := lt_min hρT hρA
  have hρT' : ball z₀ ρ ⊆ ball z₀ ρT := ball_subset_ball (min_le_left _ _)
  have hρA' : ball z₀ ρ ⊆ ball z₀ ρA := ball_subset_ball (min_le_right _ _)
  have hhanalytic : ∀ z ∈ ball z₀ ρ, AnalyticAt ℂ h z := by
    intro z hz
    have h := hball (hρA' hz)
    change (α i z ≠ 0 ∧ β j z ≠ 0) ∧
      (AnalyticAt ℂ (α i) z ∧ AnalyticAt ℂ (α j) z ∧
        AnalyticAt ℂ (β i) z ∧ AnalyticAt ℂ (β j) z) ∧
      (∀ k ∈ s, AnalyticAt ℂ (α k) z) ∧
      (∀ k ∈ s, AnalyticAt ℂ (β k) z) at h
    exact h.2.1.2.1.neg.div h.2.1.1 h.1.1
  have hTanalytic : ∀ n, ∀ z ∈ ball z₀ ρ, AnalyticAt ℂ (T n) z := by
    intro n z hz
    have hdata := hball (hρA' hz)
    change (α i z ≠ 0 ∧ β j z ≠ 0) ∧
      (AnalyticAt ℂ (α i) z ∧ AnalyticAt ℂ (α j) z ∧
        AnalyticAt ℂ (β i) z ∧ AnalyticAt ℂ (β j) z) ∧
      (∀ k ∈ s, AnalyticAt ℂ (α k) z) ∧
      (∀ k ∈ s, AnalyticAt ℂ (β k) z) at hdata
    apply Finset.analyticAt_fun_sum s
    intro k hk
    exact ((hdata.2.2.1 k hk).div hdata.2.1.1 hdata.1.1).mul
      (((hdata.2.2.2 k hk).div hdata.2.1.2.2.2 hdata.1.2).pow n)
  have hzeros : IsLimitOfZeros
      (fun n z => r z ^ n - (h z - T n z)) z₀ :=
    isLimitOfZeros_pow_sub_perturbed hρ hr hrunit hnconst
      hhanalytic hh0 hTanalytic (hTconv.mono hρT')
  have himp : ∀ᶠ n in atTop, ∀ z ∈ ball z₀ ρ,
      r z ^ n - (h z - T n z) = 0 →
      α i z * β i z ^ n + α j z * β j z ^ n +
        ∑ k ∈ s, α k z * β k z ^ n = 0 := by
    exact Eventually.of_forall fun n z hz hzero => by
      have hdata := hball (hρA' hz)
      change (α i z ≠ 0 ∧ β j z ≠ 0) ∧
        (AnalyticAt ℂ (α i) z ∧ AnalyticAt ℂ (α j) z ∧
          AnalyticAt ℂ (β i) z ∧ AnalyticAt ℂ (β j) z) ∧
        (∀ k ∈ s, AnalyticAt ℂ (α k) z) ∧
        (∀ k ∈ s, AnalyticAt ℂ (β k) z) at hdata
      have hαiz : α i z ≠ 0 := hdata.1.1
      have hβjz : β j z ≠ 0 := hdata.1.2
      simp only [r, h, T] at hzero
      simp only [div_pow] at hzero
      field_simp [hαiz, hβjz] at hzero
      have hsum : β j z ^ n * α i z *
          (∑ k ∈ s, α k z * β k z ^ n / (β j z ^ n * α i z)) =
          ∑ k ∈ s, α k z * β k z ^ n := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by field_simp [hαiz, hβjz]
      linear_combination hzero - hsum
  exact isLimitOfZeros_of_eventually_zero_imp hρ hzeros himp

/-- Sokal's two-dominant-index zero-limit theorem for a finite analytic exponential sum,
with nonvanishing leading coefficients; *Combinatorics, Probability and Computing* 13 (2004),
Theorem 1.5(b). -/
theorem isLimitOfZeros_finset_two_dominant {κ : Type*}
    (s : Finset κ) (α β : κ → ℂ → ℂ) (i j : κ) {z₀ : ℂ}
    (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j)
    (hα : ∀ k ∈ s, AnalyticAt ℂ (α k) z₀)
    (hβ : ∀ k ∈ s, AnalyticAt ℂ (β k) z₀)
    (hαi0 : α i z₀ ≠ 0) (hαj0 : α j z₀ ≠ 0)
    (hβj0 : β j z₀ ≠ 0) (heq : ‖β i z₀‖ = ‖β j z₀‖)
    (hsmall : ∀ k ∈ s, k ≠ i → k ≠ j → ‖β k z₀‖ < ‖β j z₀‖)
    (hnconst : ¬∀ᶠ z in 𝓝 z₀, β i z / β j z = β i z₀ / β j z₀) :
    IsLimitOfZeros (fun n z => ∑ k ∈ s, α k z * β k z ^ n) z₀ := by
  classical
  let t := (s.erase i).erase j
  have hj' : j ∈ s.erase i := Finset.mem_erase.mpr ⟨hij.symm, hj⟩
  have htail : IsLimitOfZeros (fun n z =>
      α i z * β i z ^ n + α j z * β j z ^ n +
        ∑ k ∈ t, α k z * β k z ^ n) z₀ := by
    exact isLimitOfZeros_two_dominant_with_tail t α β i j
      (hα i hi) (hα j hj) (hβ i hi) (hβ j hj)
      (fun k hk => hα k (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hk)))
      (fun k hk => hβ k (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hk)))
      hαi0 hαj0 hβj0 heq (fun k hk => by
        have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
        have hki : k ≠ i := (Finset.mem_erase.mp
          (Finset.mem_erase.mp hk).2).1
        exact hsmall k (Finset.mem_of_mem_erase
          (Finset.mem_of_mem_erase hk)) hki hkj) hnconst
  have hfun : (fun n z =>
      α i z * β i z ^ n + α j z * β j z ^ n +
        ∑ k ∈ t, α k z * β k z ^ n) =
      (fun n z => ∑ k ∈ s, α k z * β k z ^ n) := by
    ext n z
    have hsum1 := Finset.sum_erase_add s (fun k => α k z * β k z ^ n) hi
    have hsum2 := Finset.sum_erase_add (s.erase i)
      (fun k => α k z * β k z ^ n) hj'
    dsimp [t] at hsum2 ⊢
    linear_combination hsum1 + hsum2
  rw [hfun] at htail
  exact htail

private theorem exists_nearby_unit_complex_ne {ω : ℂ} (hω : ‖ω‖ = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ w : ℂ, ‖w‖ = 1 ∧ w ≠ ω ∧ dist w ω < ε := by
  let t := min (ε / 2) (Real.pi / 2)
  have ht0 : 0 < t := lt_min (half_pos hε) (half_pos Real.pi_pos)
  have htε : t < ε := by
    dsimp [t]
    linarith [min_le_left (ε / 2) (Real.pi / 2)]
  have htπ : t < Real.pi := by
    dsimp [t]
    linarith [Real.pi_pos, min_le_right (ε / 2) (Real.pi / 2)]
  let w : ℂ := ω * exp (I * (t : ℂ))
  refine ⟨w, ?_, ?_, ?_⟩
  · simp [w, hω, norm_exp_I_mul_ofReal]
  · intro heq
    have hω0 : ω ≠ 0 := norm_ne_zero_iff.mp (by rw [hω]; norm_num)
    have hexp : exp (I * (t : ℂ)) = 1 := by
      apply mul_left_cancel₀ hω0
      simpa [w] using heq
    have him : (exp (I * (t : ℂ))).im = Real.sin t := by
      simpa [mul_comm] using exp_ofReal_mul_I_im t
    have hsin : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht0 htπ
    simp [hexp] at him
    linarith
  · rw [dist_eq_norm]
    have heq : w - ω = ω * (exp (I * (t : ℂ)) - 1) := by simp [w, mul_sub]
    rw [heq, norm_mul, hω, one_mul]
    have hbound := Real.norm_exp_I_mul_ofReal_sub_one_le (x := t)
    rw [Real.norm_eq_abs, abs_of_pos ht0] at hbound
    exact hbound.trans_lt htε

private theorem not_locally_constant_on_analytic_ball {r : ℂ → ℂ} {z₀ : ℂ}
    {ρ : ℝ} (hρ : 0 < ρ)
    (hr : ∀ z ∈ ball z₀ ρ, AnalyticAt ℂ r z)
    (hnconst : ¬∀ᶠ z in 𝓝 z₀, r z = r z₀) :
    ∀ z ∈ ball z₀ ρ, ¬∀ᶠ w in 𝓝 z, r w = r z := by
  intro z hz hlocal
  have hron : AnalyticOnNhd ℂ r (ball z₀ ρ) := hr
  have heq : Set.EqOn r (fun _ => r z) (ball z₀ ρ) :=
    hron.eqOn_of_preconnected_of_eventuallyEq
      (fun _ _ => analyticAt_const) (convex_ball z₀ ρ).isPreconnected hz hlocal
  have hz₀ : r z₀ = r z := heq (mem_ball_self hρ)
  apply hnconst
  filter_upwards [ball_mem_nhds z₀ hρ] with w hw
  exact (heq hw).trans hz₀.symm

private theorem exists_nearby_equimodular_nonzero {r a b : ℂ → ℂ} {z₀ : ℂ}
    (hr : AnalyticAt ℂ r z₀) (ha : AnalyticAt ℂ a z₀)
    (hb : AnalyticAt ℂ b z₀) (hrunit : ‖r z₀‖ = 1)
    (hrnonconst : ¬∀ᶠ z in 𝓝 z₀, r z = r z₀)
    (hanonzero : ¬∀ᶠ z in 𝓝 z₀, a z = 0)
    (hbnonzero : ¬∀ᶠ z in 𝓝 z₀, b z = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ z ∈ ball z₀ ε, z ≠ z₀ ∧ ‖r z‖ = 1 ∧ a z ≠ 0 ∧ b z ≠ 0 := by
  have ham : ∀ᶠ z in 𝓝[≠] z₀, a z ≠ 0 :=
    ha.eventually_eq_zero_or_eventually_ne_zero.resolve_left hanonzero
  have hbm : ∀ᶠ z in 𝓝[≠] z₀, b z ≠ 0 :=
    hb.eventually_eq_zero_or_eventually_ne_zero.resolve_left hbnonzero
  have hgood : ∀ᶠ z in 𝓝 z₀, z ≠ z₀ → a z ≠ 0 ∧ b z ≠ 0 := by
    rw [eventually_nhdsWithin_iff] at ham hbm
    filter_upwards [ham, hbm] with z hza hzb hz
    exact ⟨hza hz, hzb hz⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    (hgood.and (ball_mem_nhds z₀ hε))
  have hmap : 𝓝 (r z₀) ≤ Filter.map r (𝓝 z₀) :=
    (hr.eventually_constant_or_nhds_le_map_nhds).resolve_left hrnonconst
  have himage : r '' ball z₀ δ ∈ 𝓝 (r z₀) := by
    apply hmap
    change r ⁻¹' (r '' ball z₀ δ) ∈ 𝓝 z₀
    exact mem_of_superset (ball_mem_nhds z₀ hδ)
      (fun z hz => ⟨z, hz, rfl⟩)
  obtain ⟨η, hη, hηim⟩ := Metric.mem_nhds_iff.mp himage
  obtain ⟨w, hwunit, hwne, hwnear⟩ := exists_nearby_unit_complex_ne hrunit hη
  obtain ⟨z, hzδ, hrz⟩ := hηim hwnear
  have hz0 : z ≠ z₀ := by
    intro heq
    exact hwne (by simpa [heq] using hrz.symm)
  have hprops := hball hzδ
  refine ⟨z, hprops.2, hz0, ?_, (hprops.1 hz0).1, (hprops.1 hz0).2⟩
  rw [hrz]
  exact hwunit

/-- The coefficient-zero closure extension of Sokal's two-dominant theorem. Each leading
coefficient need only be nonzero as an analytic germ, not at the equimodular point itself;
*Combinatorics, Probability and Computing* 13 (2004), Theorem 1.5(b). -/
theorem isLimitOfZeros_finset_two_dominant_closure {κ : Type*}
    (s : Finset κ) (α β : κ → ℂ → ℂ) (i j : κ) {z₀ : ℂ}
    (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j)
    (hα : ∀ k ∈ s, AnalyticAt ℂ (α k) z₀)
    (hβ : ∀ k ∈ s, AnalyticAt ℂ (β k) z₀)
    (hαigerm : ¬∀ᶠ z in 𝓝 z₀, α i z = 0)
    (hαjgerm : ¬∀ᶠ z in 𝓝 z₀, α j z = 0)
    (hβj0 : β j z₀ ≠ 0) (heq : ‖β i z₀‖ = ‖β j z₀‖)
    (hsmall : ∀ k ∈ s, k ≠ i → k ≠ j → ‖β k z₀‖ < ‖β j z₀‖)
    (hnconst : ¬∀ᶠ z in 𝓝 z₀, β i z / β j z = β i z₀ / β j z₀) :
    IsLimitOfZeros (fun n z => ∑ k ∈ s, α k z * β k z ^ n) z₀ := by
  classical
  let r : ℂ → ℂ := fun z => β i z / β j z
  have hr : AnalyticAt ℂ r z₀ := (hβ i hi).div (hβ j hj) hβj0
  have hrunit : ‖r z₀‖ = 1 := by simp [r, heq, hβj0]
  have hβjev : ∀ᶠ z in 𝓝 z₀, β j z ≠ 0 :=
    (hβ j hj).continuousAt.eventually_ne hβj0
  have hαev : ∀ᶠ z in 𝓝 z₀, ∀ k ∈ s, AnalyticAt ℂ (α k) z :=
    (eventually_all_finset s).2 fun k hk => (hα k hk).eventually_analyticAt
  have hβev : ∀ᶠ z in 𝓝 z₀, ∀ k ∈ s, AnalyticAt ℂ (β k) z :=
    (eventually_all_finset s).2 fun k hk => (hβ k hk).eventually_analyticAt
  have hsmallev : ∀ᶠ z in 𝓝 z₀,
      ∀ k ∈ s, k ≠ i → k ≠ j → ‖β k z‖ < ‖β j z‖ := by
    apply (eventually_all_finset s).2
    intro k hk
    by_cases hki : k = i
    · exact Eventually.of_forall fun z hne _ => (hne hki).elim
    by_cases hkj : k = j
    · exact Eventually.of_forall fun z _ hne => (hne hkj).elim
    exact ((hβ k hk).continuousAt.norm.eventually_lt
      (hβ j hj).continuousAt.norm (hsmall k hk hki hkj)).mono
      (fun z hz _ _ => hz)
  have hnear : ∀ᶠ z in 𝓝 z₀,
      β j z ≠ 0 ∧ (∀ k ∈ s, AnalyticAt ℂ (α k) z) ∧
        (∀ k ∈ s, AnalyticAt ℂ (β k) z) ∧
        (∀ k ∈ s, k ≠ i → k ≠ j → ‖β k z‖ < ‖β j z‖) ∧
        AnalyticAt ℂ r z := by
    filter_upwards [hβjev, hαev, hβev, hsmallev,
      hr.eventually_analyticAt] with z hβjz hαz hβz hsmallz hrz
    exact ⟨hβjz, hαz, hβz, hsmallz, hrz⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hnear
  have hranalytic : ∀ z ∈ ball z₀ ρ, AnalyticAt ℂ r z := by
    intro z hz
    exact (hball hz).2.2.2.2
  have hnonconstAt := not_locally_constant_on_analytic_ball hρ hranalytic hnconst
  let F : ℕ → ℂ → ℂ := fun n z => ∑ k ∈ s, α k z * β k z ^ n
  have hclosed : IsClosed {z | IsLimitOfZeros F z} := isClosed_isLimitOfZeros F
  have hcl : z₀ ∈ closure {z | IsLimitOfZeros F z} := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    let δ := min ε ρ / 2
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hδε : δ ≤ ε := by
      dsimp [δ]
      linarith [min_le_left ε ρ]
    have hδρ : δ ≤ ρ := by
      dsimp [δ]
      linarith [min_le_right ε ρ]
    obtain ⟨z, hzδ, hz0, hzunit, hαiz, hαjz⟩ :=
      exists_nearby_equimodular_nonzero hr (hα i hi) (hα j hj)
        hrunit hnconst hαigerm hαjgerm hδ
    have hzρ : z ∈ ball z₀ ρ := ball_subset_ball hδρ hzδ
    have hdata := hball hzρ
    change β j z ≠ 0 ∧ (∀ k ∈ s, AnalyticAt ℂ (α k) z) ∧
      (∀ k ∈ s, AnalyticAt ℂ (β k) z) ∧
      (∀ k ∈ s, k ≠ i → k ≠ j → ‖β k z‖ < ‖β j z‖) ∧
      AnalyticAt ℂ r z at hdata
    have heqz : ‖β i z‖ = ‖β j z‖ := by
      have hnorm : ‖β i z‖ / ‖β j z‖ = 1 := by
        simpa [r, norm_div] using hzunit
      exact (div_eq_one_iff_eq (norm_ne_zero_iff.mpr hdata.1)).mp hnorm
    have hzlim : IsLimitOfZeros F z :=
      isLimitOfZeros_finset_two_dominant s α β i j hi hj hij
        hdata.2.1 hdata.2.2.1 hαiz hαjz hdata.1 heqz
        hdata.2.2.2.1 (hnonconstAt z hzρ)
    exact ⟨z, hzlim, by
      rw [dist_comm]
      exact (ball_subset_ball hδε hzδ)⟩
  change IsLimitOfZeros F z₀
  simpa only [hclosed.closure_eq, Set.mem_ofPred_eq] using hcl

/-- **Unique dominant index.** If the base `β i` strictly dominates every other base at `z₀`,
and the coefficient `α i` vanishes at `z₀` without vanishing identically near `z₀`, then
`z₀` is a liminf limit of zeros of `∑ k ∈ s, α k z * β k z ^ n`.
Sokal, *Combinatorics, Probability and Computing* 13 (2004), Theorem 1.5(a). -/
theorem isLimitOfZeros_finset_unique_dominant {κ : Type*}
    (s : Finset κ) (α β : κ → ℂ → ℂ) (i : κ) {z₀ : ℂ} (hi : i ∈ s)
    (hα : ∀ k ∈ s, AnalyticAt ℂ (α k) z₀)
    (hβ : ∀ k ∈ s, AnalyticAt ℂ (β k) z₀)
    (hβi0 : β i z₀ ≠ 0)
    (hsmall : ∀ k ∈ s, k ≠ i → ‖β k z₀‖ < ‖β i z₀‖)
    (hαi0 : α i z₀ = 0) (hnconst : ¬∀ᶠ z in 𝓝 z₀, α i z = 0) :
    IsLimitOfZeros (fun n z => ∑ k ∈ s, α k z * β k z ^ n) z₀ := by
  classical
  obtain ⟨G, hGdef⟩ : ∃ G : ℕ → ℂ → ℂ, ∀ n z,
      G n z = α i z + ∑ k ∈ s.erase i, α k z * (β k z / β i z) ^ n :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨r₁, hr₁, h₁⟩ := exists_ball_tendstoUniformlyOn_sum_mul_pow_zero (s.erase i) α
    (fun k z => β k z / β i z)
    (fun k hk => (hα k (Finset.mem_of_mem_erase hk)).continuousAt)
    (fun k hk => ((hβ k (Finset.mem_of_mem_erase hk)).div (hβ i hi) hβi0).continuousAt)
    (fun k hk => by
      rw [norm_div]
      exact (div_lt_one (norm_pos_iff.mpr hβi0)).mpr
        (hsmall k (Finset.mem_of_mem_erase hk) (Finset.ne_of_mem_erase hk)))
  have hev : ∀ᶠ z in 𝓝 z₀,
      (∀ k ∈ s, AnalyticAt ℂ (α k) z ∧ AnalyticAt ℂ (β k) z) ∧ β i z ≠ 0 := by
    refine ((Filter.eventually_all_finset s).2 fun k hk =>
      (hα k hk).eventually_analyticAt.and (hβ k hk).eventually_analyticAt).and ?_
    exact (hβ i hi).continuousAt.eventually_ne hβi0
  obtain ⟨r₂, hr₂, hball⟩ := Metric.mem_nhds_iff.mp hev
  have hr : 0 < min r₁ r₂ := lt_min hr₁ hr₂
  have hballr : ∀ z ∈ ball z₀ (min r₁ r₂), z ∈ ball z₀ r₂ :=
    fun z hz => ball_subset_ball (min_le_right _ _) hz
  have hG : ∀ n, DifferentiableOn ℂ (G n) (ball z₀ (min r₁ r₂)) := by
    intro n z hz
    obtain ⟨hk, hne⟩ := hball (hballr z hz)
    refine DifferentiableAt.differentiableWithinAt ?_
    have hGz : G n = fun w => α i w +
        ∑ k ∈ s.erase i, α k w * (β k w / β i w) ^ n := funext fun w => hGdef n w
    rw [hGz]
    refine DifferentiableAt.add (hk i hi).1.differentiableAt ?_
    refine DifferentiableAt.fun_sum fun k hk' => ?_
    have hkk := hk k (Finset.mem_of_mem_erase hk')
    exact hkk.1.differentiableAt.mul
      ((hkk.2.div (hk i hi).2 hne).pow n).differentiableAt
  have hconv : TendstoLocallyUniformlyOn G (α i) atTop (ball z₀ (min r₁ r₂)) := by
    apply TendstoUniformlyOn.tendstoLocallyUniformlyOn
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have h₁' := Metric.tendstoUniformlyOn_iff.mp
      (h₁.mono (ball_subset_ball (min_le_left r₁ r₂))) ε hε
    filter_upwards [h₁'] with n hn z hz
    have hnz := hn z hz
    beta_reduce at hnz
    rw [dist_eq_norm, zero_sub] at hnz
    rw [hGdef, dist_eq_norm, sub_add_cancel_left]
    exact hnz
  have hnconst' : ¬∀ᶠ z in 𝓝 z₀, α i z = α i z₀ := by
    intro h
    apply hnconst
    filter_upwards [h] with z hz
    rw [hz, hαi0]
  have hfac : ∀ z, β i z ≠ 0 → ∀ n : ℕ,
      ∑ k ∈ s, α k z * β k z ^ n = β i z ^ n * G n z := by
    intro z hz n
    have h0 := Finset.sum_erase_add s (fun k => α k z * β k z ^ n) hi
    have h1 : β i z ^ n * ∑ k ∈ s.erase i, α k z * (β k z / β i z) ^ n =
        ∑ k ∈ s.erase i, α k z * β k z ^ n := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [div_pow]
      field_simp
    rw [hGdef, mul_add, h1]
    linear_combination (-1 : ℂ) * h0
  refine isLimitOfZeros_of_auxiliary (G := G) (g := α i) hr hG hconv hαi0 hnconst' ?_
  refine Eventually.of_forall fun n z hz hGz => ?_
  obtain ⟨-, hne⟩ := hball (hballr z hz)
  rw [hfac z hne n, hGz, mul_zero]

end Complex

namespace MvPolynomial

/-- The open product of upper half-planes. -/
def upperHalfPlane (τ : Type*) : Set (τ → ℂ) := {z | ∀ i, 0 < (z i).im}

private lemma isOpen_upperHalfPlane (τ : Type*) [Finite τ] : IsOpen (upperHalfPlane τ) := by
  have h : upperHalfPlane τ = ⋂ i, (fun z : τ → ℂ => (z i).im) ⁻¹' Set.Ioi 0 := by
    ext z
    simp [upperHalfPlane]
  rw [h]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_Ioi.preimage (Complex.continuous_im.comp (continuous_apply i))

private lemma exists_upperHalfPlane_eval_ne_zero {τ : Type*} {q : MvPolynomial τ ℂ}
    (hq : q ≠ 0) :
    ∃ y ∈ upperHalfPlane τ, MvPolynomial.eval y q ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hq
  rw [MvPolynomial.funext_set_iff (fun _ => {w : ℂ | 0 < w.im})]
  · intro x hx
    simp only [map_zero]
    exact hcon x (fun i => hx i (Set.mem_univ i))
  · intro i
    have h : {w : ℂ | 0 < w.im} ∈ 𝓝 Complex.I :=
      (isOpen_lt continuous_const Complex.continuous_im).mem_nhds (by simp)
    exact infinite_of_mem_nhds _ h

private lemma eval_line_poly {τ : Type*} (q : MvPolynomial τ ℂ) (z d : τ → ℂ) (t : ℂ) :
    Polynomial.eval t (MvPolynomial.aeval
      (fun i => Polynomial.C (z i) + Polynomial.C (d i) * Polynomial.X) q) =
      MvPolynomial.eval (z + t • d) q := by
  have h := congrArg (fun φ => φ q) (MvPolynomial.comp_aeval
    (fun i => Polynomial.C (z i) + Polynomial.C (d i) * Polynomial.X)
    (Polynomial.aeval (R := ℂ) t))
  simp only [AlgHom.comp_apply] at h
  rw [← Polynomial.coe_aeval_eq_eval, h, ← MvPolynomial.coe_aeval_eq_eval]
  have hf : (fun i => (Polynomial.aeval t) (Polynomial.C (z i) + Polynomial.C (d i) *
      Polynomial.X)) = z + t • d := by
    funext i
    simp
    ring
  rw [hf]
  rfl

private lemma differentiable_eval_line {τ : Type*} (q : MvPolynomial τ ℂ) (z d : τ → ℂ) :
    Differentiable ℂ (fun t : ℂ => MvPolynomial.eval (z + t • d) q) := by
  let Q : Polynomial ℂ :=
    MvPolynomial.aeval (fun i => Polynomial.C (z i) + Polynomial.C (d i) * Polynomial.X) q
  rw [← differentiableOn_univ]
  apply DifferentiableOn.congr (Polynomial.differentiable Q).differentiableOn
  intro t ht
  exact (eval_line_poly q z d t).symm

/-- A locally uniform upper-half-plane-stable polynomial limit is upper-half-plane-stable
or zero. -/
theorem eval_ne_zero_or_eq_zero_of_tendstoLocallyUniformlyOn {τ : Type*} [Finite τ]
    (p : ℕ → MvPolynomial τ ℂ) (q : MvPolynomial τ ℂ)
    (hp : ∀ k, ∀ z ∈ upperHalfPlane τ, MvPolynomial.eval z (p k) ≠ 0)
    (hconv : TendstoLocallyUniformlyOn (fun k z => MvPolynomial.eval z (p k))
      (fun z => MvPolynomial.eval z q) atTop (upperHalfPlane τ)) :
    (∀ z ∈ upperHalfPlane τ, MvPolynomial.eval z q ≠ 0) ∨ q = 0 := by
  let _ := Fintype.ofFinite τ
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨z0, hz0, hq0⟩, hq⟩ := hcon
  obtain ⟨y, hy, hqy⟩ := exists_upperHalfPlane_eval_ne_zero hq
  set d := y - z0 with hd
  set h : Polynomial ℂ :=
    MvPolynomial.aeval (fun i => Polynomial.C (z0 i) + Polynomial.C (d i) * Polynomial.X) q
  have hh : ∀ t, h.eval t = MvPolynomial.eval (z0 + t • d) q := eval_line_poly q z0 d
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isOpen_upperHalfPlane τ) z0 hz0
  set ρ := ε / (‖d‖ + 1) with hρdef
  have hd1 : 0 < ‖d‖ + 1 := by positivity
  have hρ : 0 < ρ := by positivity
  set g : ℂ → (τ → ℂ) := fun t => z0 + t • d with hg
  have hmaps : Set.MapsTo g (ball 0 ρ) (upperHalfPlane τ) := by
    intro t ht
    apply hball
    rw [mem_ball, dist_eq_norm]
    simp only [g, add_sub_cancel_left, norm_smul]
    rw [mem_ball, dist_zero_right] at ht
    calc
      ‖t‖ * ‖d‖ ≤ ‖t‖ * (‖d‖ + 1) := by
        gcongr
        linarith
      _ < ρ * (‖d‖ + 1) := by gcongr
      _ = ε := by
        rw [hρdef]
        field_simp
  have hcont : Continuous g := by fun_prop
  have hconv' := hconv.comp g hmaps hcont.continuousOn
  have hdiff : ∀ k, DifferentiableOn ℂ
      ((fun k z => MvPolynomial.eval z (p k)) k ∘ g) (ball 0 ρ) := by
    intro k
    apply DifferentiableOn.congr (differentiable_eval_line (p k) z0 d).differentiableOn
    intro t ht
    rfl
  have hne : ∀ k, ∀ t ∈ ball (0 : ℂ) ρ,
      ((fun k z => MvPolynomial.eval z (p k)) k ∘ g) t ≠ 0 :=
    fun k t ht => hp k _ (hmaps ht)
  rcases Complex.forall_ne_or_forall_eq_of_tendstoLocallyUniformlyOn_ball hdiff hconv' hne with
    h1 | h1
  · exact h1 0 (mem_ball_self hρ) (by simp [g, hq0])
  · have h0 : h = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      refine Set.Infinite.mono (fun t ht => ?_)
        (infinite_of_mem_nhds (0 : ℂ) (ball_mem_nhds (0 : ℂ) hρ))
      change Polynomial.IsRoot h t
      rw [Polynomial.IsRoot, hh]
      exact h1 t ht
    apply hqy
    rw [show y = z0 + (1 : ℂ) • d by simp [d], ← hh, h0, Polynomial.eval_zero]

end MvPolynomial
