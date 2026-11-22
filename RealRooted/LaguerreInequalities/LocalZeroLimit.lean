module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import RealRooted.LaguerreInequalities.Analytic
import RealRooted.LaguerreInequalities.LocalProductLimit
import RealRooted.Mathlib.Analysis.Complex.LineIdentity
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import TauCeti.Analysis.Complex.Conformal.Vitali

/-!
# Vanishing local limits of Laguerre--Pólya functions

The zero case of the local limit problem can be detected on the real line.
Symmetric products allow analytic continuation of this vanishing even when
normal convergence of the original functions has not been established.
-/

public section

open Complex Filter Topology

namespace RealRooted

/-- If a pointwise disk limit of Laguerre--Pólya functions vanishes on the
real diameter, its symmetric products converge locally uniformly to zero. -/
theorem tendstoLocallyUniformlyOn_laguerreProduct_zero {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hF : ∀ n, IsLaguerrePolya (F n)) (x : ℝ) {r : ℝ} (hr : 0 < r)
    (hpoint : ∀ z ∈ Metric.ball (x : ℂ) r,
      Tendsto (fun n => F n z) atTop (𝓝 (g z)))
    (hzero : ∀ y : ℝ, (y : ℂ) ∈ Metric.ball (x : ℂ) r → g y = 0) :
    TendstoLocallyUniformlyOn (fun n => laguerreProduct (F n) x)
      (fun _ => 0) atTop (Metric.ball 0 r) := by
  have hlim := tendstoLocallyUniformlyOn_laguerreProduct hF x hr hpoint
  have hd := hlim.differentiableOn (Eventually.of_forall fun n =>
    (differentiable_laguerreProduct (hF n).differentiable x).differentiableOn)
    Metric.isOpen_ball
  have hz : (0 : ℂ) ∈ Metric.ball 0 r := by simpa using hr
  have heq := (hd.analyticOnNhd Metric.isOpen_ball).eqOn_zero_of_line_eq_zero
    (convex_ball (0 : ℂ) r).isPreconnected hz I_ne_zero
    (show ∀ᶠ t : ℝ in 𝓝 0, laguerreProduct g x (0 + (t : ℂ) * I) = 0 from by
      have ht : ∀ᶠ t : ℝ in 𝓝 0, ((x - t : ℝ) : ℂ) ∈ Metric.ball (x : ℂ) r :=
        (show Continuous (fun t : ℝ => ((x - t : ℝ) : ℂ)) from by fun_prop).tendsto 0
          |>.eventually (Metric.isOpen_ball.mem_nhds (by simpa using hr))
      filter_upwards [ht] with t ht
      simp only [laguerreProduct, zero_add, mul_assoc, I_mul_I, mul_neg_one]
      rw [show (x : ℂ) + -(t : ℂ) = ((x - t : ℝ) : ℂ) by push_cast; ring,
        hzero _ ht, zero_mul])
  exact hlim.congr_right heq

/-- A convergent vertical endpoint propagates vanishing symmetric products
from a smaller disk to the full disk bounded by that endpoint. -/
theorem tendstoLocallyUniformlyOn_laguerreProduct_zero_of_endpoint
    {F : ℕ → ℂ → ℂ} (hF : ∀ n, IsLaguerrePolya (F n)) (x : ℝ)
    {R δ : ℝ} (hδ : 0 < δ) (hδR : δ ≤ R) {w : ℂ}
    (hw : Tendsto (fun n => F n (x + (R : ℂ) * I)) atTop (𝓝 w))
    (hlocal : TendstoLocallyUniformlyOn (fun n => laguerreProduct (F n) x)
      (fun _ => 0) atTop (Metric.ball 0 δ)) :
    TendstoLocallyUniformlyOn (fun n => laguerreProduct (F n) x)
      (fun _ => 0) atTop (Metric.ball 0 R) := by
  have hR : 0 < R := hδ.trans_le hδR
  have hzδ : (0 : ℂ) ∈ Metric.ball 0 δ := by simpa using hδ
  have hzR : (0 : ℂ) ∈ Metric.ball 0 R := by simpa using hR
  obtain ⟨q, hq, hqzero, hlim⟩ := TauCeti.vitali_of_tendsto Metric.isOpen_ball
    (convex_ball (0 : ℂ) R).isPreconnected
    (fun n => (differentiable_laguerreProduct (hF n).differentiable x).differentiableOn)
    (isLocallyBoundedOn_laguerreProduct_of_tendsto hF x R hw)
    (Metric.ball_subset_ball hδR) hzR (Metric.isOpen_ball.preperfect _ hzδ)
    (fun z hz => hlocal.tendsto_at hz)
  have heq := (hq.analyticOnNhd Metric.isOpen_ball).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball (0 : ℂ) R).isPreconnected hzR
      (Filter.eventually_of_mem (Metric.ball_mem_nhds (0 : ℂ) hδ) fun z hz => hqzero hz)
  exact hlim.congr_right heq

/-- A pointwise disk limit of Laguerre--Pólya functions which vanishes on the
real diameter vanishes on the whole disk. No local uniform convergence of
the original functions is assumed. -/
theorem eqOn_zero_of_tendsto_of_real_eq_zero {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hF : ∀ n, IsLaguerrePolya (F n)) {r : ℝ}
    (hpoint : ∀ z ∈ Metric.ball (0 : ℂ) r,
      Tendsto (fun n => F n z) atTop (𝓝 (g z)))
    (hzero : ∀ y : ℝ, (y : ℂ) ∈ Metric.ball (0 : ℂ) r → g y = 0) :
    Set.EqOn g 0 (Metric.ball 0 r) := by
  intro z hz
  have hzr : ‖z‖ < r := by simpa using hz
  let δ := (r - ‖z‖) / 4
  let R := |z.im| + δ
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδR : δ ≤ R := by dsimp [R]; linarith [abs_nonneg z.im]
  have hnormx : ‖(z.re : ℂ)‖ ≤ ‖z‖ := by simpa using abs_re_le_norm z
  have hsub : Metric.ball (z.re : ℂ) δ ⊆ Metric.ball (0 : ℂ) r := by
    intro u hu
    have huδ : ‖u - (z.re : ℂ)‖ < δ := by simpa [dist_eq_norm] using hu
    have huNorm := norm_add_le (u - (z.re : ℂ)) (z.re : ℂ)
    rw [sub_add_cancel] at huNorm
    have : ‖u‖ < r := by dsimp [δ] at huδ; linarith
    simpa using this
  have hlocal := tendstoLocallyUniformlyOn_laguerreProduct_zero hF z.re hδ
    (fun u hu => hpoint u (hsub hu)) (fun y hy => hzero y (hsub hy))
  have hnormabs : ‖(z.re : ℂ) + ((|z.im| : ℝ) : ℂ) * I‖ = ‖z‖ := by
    rw [norm_eq_sqrt_sq_add_sq, norm_eq_sqrt_sq_add_sq z]
    simp
  have hend : (z.re : ℂ) + (R : ℂ) * I ∈ Metric.ball (0 : ℂ) r := by
    have heq : (z.re : ℂ) + (R : ℂ) * I =
        ((z.re : ℂ) + ((|z.im| : ℝ) : ℂ) * I) + (δ : ℂ) * I := by
      dsimp [R]
      push_cast
      ring
    have hn := norm_add_le ((z.re : ℂ) + ((|z.im| : ℝ) : ℂ) * I) ((δ : ℂ) * I)
    rw [hnormabs] at hn
    have hnδ : ‖(δ : ℂ) * I‖ = δ := by simp [abs_of_pos hδ]
    rw [hnδ] at hn
    rw [Metric.mem_ball, dist_zero_right, heq]
    dsimp [δ] at hn
    linarith
  have hlim := tendstoLocallyUniformlyOn_laguerreProduct_zero_of_endpoint
    hF z.re hδ hδR (hpoint _ hend) hlocal
  have hymem : (z.im : ℂ) ∈ Metric.ball (0 : ℂ) R := by
    simp only [Metric.mem_ball, dist_zero_right, norm_real, Real.norm_eq_abs]
    dsimp [R]
    linarith
  have hnorm := ((hpoint z hz).norm.pow 2).ofReal
  have hprod : Tendsto (fun n => laguerreProduct (F n) z.re z.im) atTop
      (𝓝 ((‖g z‖ ^ 2 : ℝ) : ℂ)) := hnorm.congr fun n => by
    rw [laguerreProduct_ofReal (hF n).conj, re_add_im]
  have hnzero : ‖g z‖ ^ 2 = 0 := by
    exact_mod_cast tendsto_nhds_unique hprod (hlim.tendsto_at hymem)
  simpa using (sq_eq_zero_iff.mp hnzero)

end RealRooted
