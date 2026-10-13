import Mathlib

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
    have hmin := min_le_left ε (r - dist z0 c)
    linarith
  have hρδ : ρ < r - dist z0 c := by
    have hmin := min_le_right ε (r - dist z0 c)
    linarith
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
