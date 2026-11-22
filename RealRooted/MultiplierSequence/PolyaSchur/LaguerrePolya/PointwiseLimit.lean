module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
import RealRooted.LaguerreInequalities.LocalDerivativeBounds
import RealRooted.LaguerreInequalities.LocalZeroLimit
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.UniformDerivativeBounds
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Closure
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.Mathlib.Analysis.Normed.Group.LocallyBoundedMajorant
import TauCeti.Analysis.Complex.Conformal.Vitali

/-!
# Entire Laguerre--Pólya extension of pointwise local limits

A pointwise limit on a disk centered on the real line extends to an entire
Laguerre--Pólya function. The zero case uses symmetric products. A nonzero
real value controls the first two derivatives and hence supplies a common
Gaussian majorant and a global normal limit. The zero case does not assert
global convergence of the approximating sequence.
-/

public section

open Complex Filter Topology

namespace RealRooted

/-- A nonzero limiting value at zero turns pointwise local convergence of
Laguerre--Pólya functions into an eventual common Gaussian bound. -/
theorem exists_eventually_norm_le_exp_of_tendsto {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hF : ∀ n, IsLaguerrePolya (F n)) {r : ℝ} (hr : 0 < r)
    (hpoint : ∀ z ∈ Metric.ball (0 : ℂ) r,
      Tendsto (fun n => F n z) atTop (𝓝 (g z))) (hg : g 0 ≠ 0) :
    ∃ B > 0, ∃ C ≥ 0, ∀ᶠ n in atTop, ∀ z : ℂ,
      ‖F n z‖ ≤ B * Real.exp (C * ‖z‖ ^ 2) := by
  obtain ⟨A, hA, hAb⟩ := exists_eventually_norm_deriv_le_of_tendsto hF 0 hr hpoint hg
  obtain ⟨D, hD, hDb⟩ := exists_eventually_norm_deriv_deriv_le_of_tendsto hF 0 hr hpoint hg
  have hzero := hpoint 0 (by simpa using hr)
  obtain ⟨E, hE, hEb⟩ := (Metric.isBounded_range_of_tendsto _ hzero).exists_pos_norm_le
  obtain ⟨Q, hQ, hQb⟩ := (Metric.isBounded_range_of_tendsto _
    (hzero.inv₀ hg)).exists_pos_norm_le
  obtain ⟨B, hB, C, hC, hbound⟩ :=
    exists_uniform_norm_bound_of_jet_bounds (show 0 ≤ A + D + E + Q by linarith)
  refine ⟨B, hB, C, hC, ?_⟩
  filter_upwards [hAb, hDb, hzero.eventually_ne hg] with n hn₁ hn₂ hn₀
  apply hbound (F n) (hF n) hn₀
  · exact (hEb _ ⟨n, rfl⟩).trans (by linarith)
  · exact (hQb _ ⟨n, rfl⟩).trans (by linarith)
  · exact hn₁.trans (by linarith)
  · exact hn₂.trans (by linarith)

/-- Pointwise convergence on a neighborhood of a real point with nonzero
limit extends to a global Laguerre--Pólya function. Agreement holds at every
point where the original pointwise limit was specified. -/
theorem exists_isLaguerrePolya_eqOn_of_pointwise_limit {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hF : ∀ n, IsLaguerrePolya (F n)) {U : Set ℂ} {x : ℝ}
    (hU : U ∈ 𝓝 (x : ℂ))
    (hpoint : ∀ z ∈ U, Tendsto (fun n => F n z) atTop (𝓝 (g z))) (hg : g x ≠ 0) :
    ∃ G : ℂ → ℂ, IsLaguerrePolya G ∧ Set.EqOn G g U := by
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp hU
  let T (n : ℕ) (z : ℂ) := F n (z + x)
  have hT (n : ℕ) : IsLaguerrePolya (T n) := by
    simpa only [ofReal_one, one_mul] using (hF n).comp_affine_real 1 x
  have hTpoint : ∀ z ∈ Metric.ball (0 : ℂ) r,
      Tendsto (fun n => T n z) atTop (𝓝 (g (z + x))) := by
    intro z hz
    apply hpoint _ (hrU _)
    simpa [Metric.mem_ball, dist_eq_norm] using hz
  obtain ⟨B, _, C, _, hbound⟩ := exists_eventually_norm_le_exp_of_tendsto hT hr hTpoint
    (by simpa using hg)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hbound
  have htail : ∀ n (z : ℂ), ‖F (n + N) z‖ ≤ B * Real.exp (C * ‖z - (x : ℂ)‖ ^ 2) := by
    intro n z
    simpa only [T, sub_add_cancel] using hN (n + N) (Nat.le_add_left _ _) (z - (x : ℂ))
  have hb : TauCeti.IsLocallyBoundedOn (fun n => F (n + N)) Set.univ :=
    TauCeti.isLocallyBoundedOn_of_norm_le_continuous (by fun_prop)
      (fun n z _ => htail n z)
  have htailpoint (z : ℂ) (hz : z ∈ U) := (hpoint z hz).comp (tendsto_add_atTop_nat N)
  have hx : (x : ℂ) ∈ Metric.ball (x : ℂ) r := by simpa using hr
  obtain ⟨G, _, _, hlim⟩ := TauCeti.vitali_of_tendsto isOpen_univ isPreconnected_univ
    (fun n => (hF (n + N)).differentiable.differentiableOn) hb (Set.subset_univ _)
    (Set.mem_univ (x : ℂ)) (Metric.isOpen_ball.preperfect _ hx)
    (fun z hz => htailpoint z (hrU hz))
  refine ⟨G, IsLaguerrePolya.of_tendstoLocallyUniformly (fun n => hF (n + N))
    (tendstoLocallyUniformlyOn_univ.mp hlim), ?_⟩
  intro z hz
  exact tendsto_nhds_unique (hlim.tendsto_at (Set.mem_univ z)) (htailpoint z hz)

/-- Every pointwise limit on a disk centered at zero of entire
Laguerre--Pólya functions has an entire Laguerre--Pólya extension. This includes
the identically zero local limit and imposes no normal convergence hypothesis. -/
theorem exists_isLaguerrePolya_eqOn_of_tendsto {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hF : ∀ n, IsLaguerrePolya (F n)) {r : ℝ}
    (hpoint : ∀ z ∈ Metric.ball (0 : ℂ) r,
      Tendsto (fun n => F n z) atTop (𝓝 (g z))) :
    ∃ G : ℂ → ℂ, IsLaguerrePolya G ∧ Set.EqOn G g (Metric.ball 0 r) := by
  by_cases hzero : ∀ y : ℝ, (y : ℂ) ∈ Metric.ball (0 : ℂ) r → g y = 0
  · exact ⟨0, IsLaguerrePolya.zero,
      (eqOn_zero_of_tendsto_of_real_eq_zero hF hpoint hzero).symm⟩
  · push Not at hzero
    obtain ⟨x, hx, hg⟩ := hzero
    exact exists_isLaguerrePolya_eqOn_of_pointwise_limit hF
      (Metric.isOpen_ball.mem_nhds hx) hpoint hg

end RealRooted
