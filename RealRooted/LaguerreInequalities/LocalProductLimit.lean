module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import RealRooted.LaguerreInequalities.Analytic
public import TauCeti.Analysis.Normed.Group.LocallyBounded
import RealRooted.LaguerreInequalities.ModulusBound
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import TauCeti.Analysis.Complex.Conformal.Vitali
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

/-!
# Local normality of symmetric products

Convergence of a Laguerre--Pólya sequence at one point above the real axis
bounds its symmetric products on a whole disk. Pointwise convergence on a
disk therefore gives locally uniform convergence of the symmetric products.
This assertion does not assume locally uniform convergence of the original
functions.
-/

public section

open Complex Filter Topology

namespace RealRooted

/-- Convergence at a single vertical endpoint locally bounds every symmetric
product centered at the corresponding real point. -/
theorem isLocallyBoundedOn_laguerreProduct_of_tendsto {F : ℕ → ℂ → ℂ}
    (hF : ∀ n, IsLaguerrePolya (F n)) (x R : ℝ) {w : ℂ}
    (hw : Tendsto (fun n => F n (x + (R : ℂ) * I)) atTop (𝓝 w)) :
    TauCeti.IsLocallyBoundedOn (fun n => laguerreProduct (F n) x) (Metric.ball 0 R) := by
  obtain ⟨C, _, hC⟩ := (Metric.isBounded_range_of_tendsto _ hw).exists_pos_norm_le
  apply TauCeti.isLocallyBoundedOn_of_forall_norm_le (C := C ^ 2)
  intro n z hz
  have hzR : ‖z‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hz
  exact ((hF n).norm_laguerreProduct_le x hzR.le).trans
    (pow_le_pow_left₀ (norm_nonneg _) (hC _ ⟨n, rfl⟩) 2)

/-- Pointwise convergence of Laguerre--Pólya functions on a disk centered on
the real axis implies locally uniform convergence of their symmetric products. -/
theorem tendstoLocallyUniformlyOn_laguerreProduct {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hF : ∀ n, IsLaguerrePolya (F n)) (x : ℝ) {r : ℝ} (hr : 0 < r)
    (hpoint : ∀ z ∈ Metric.ball (x : ℂ) r,
      Tendsto (fun n => F n z) atTop (𝓝 (g z))) :
    TendstoLocallyUniformlyOn (fun n => laguerreProduct (F n) x)
      (laguerreProduct g x) atTop (Metric.ball 0 r) := by
  have hb : TauCeti.IsLocallyBoundedOn (fun n => laguerreProduct (F n) x)
      (Metric.ball 0 r) := by
    rw [TauCeti.isLocallyBoundedOn_def]
    intro K hKr hK
    obtain ⟨R, hR, hKR⟩ := exists_pos_lt_subset_ball hr hK.isClosed hKr
    have hend : (x : ℂ) + (R : ℂ) * I ∈ Metric.ball (x : ℂ) r := by
      simpa [Metric.mem_ball, dist_eq_norm, norm_mul, abs_of_pos hR.1] using hR.2
    exact (TauCeti.isLocallyBoundedOn_def.mp
      (isLocallyBoundedOn_laguerreProduct_of_tendsto hF x R (hpoint _ hend))) K hKR hK
  apply TauCeti.tendstoLocallyUniformlyOn_of_isLocallyBoundedOn_of_forall_tendsto
    Metric.isOpen_ball
    (fun n => (differentiable_laguerreProduct (hF n).differentiable x).differentiableOn) hb
  intro z hz
  have hplus : (x : ℂ) + z * I ∈ Metric.ball (x : ℂ) r := by
    simpa [Metric.mem_ball, dist_eq_norm, norm_mul] using hz
  have hminus : (x : ℂ) - z * I ∈ Metric.ball (x : ℂ) r := by
    simpa [Metric.mem_ball, dist_eq_norm, norm_mul, sub_eq_add_neg] using hz
  exact (hpoint _ hplus).mul (hpoint _ hminus)

end RealRooted
