module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
import RealRooted.LaguerreInequalities.LocalProductLimit
import RealRooted.Mathlib.Topology.UniformSpace.LocallyUniformAvoidance
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Nonzero local limits of Laguerre--Pólya functions

A nonzero real value of a pointwise limit yields a common zero-free disk for
the approximants. Only their symmetric products are known to converge normally
at this stage.
-/

public section

open Complex Filter Topology

namespace RealRooted

private theorem ne_zero_of_laguerreProduct_ne_zero {f : ℂ → ℂ} {x : ℝ} {z : ℂ}
    (h : laguerreProduct f x ((z - (x : ℂ)) * (-I)) ≠ 0) : f z ≠ 0 := by
  have heq : (x : ℂ) + ((z - (x : ℂ)) * (-I)) * I = z := by
    rw [mul_assoc]
    simp
  rw [laguerreProduct, heq] at h
  exact (mul_ne_zero_iff.mp h).1

/-- A pointwise limit of Laguerre--Pólya functions with a nonzero value at a
real center gives a zero-free disk for both the limit and every sufficiently
late approximant. -/
theorem exists_ball_ne_zero_of_tendsto {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hF : ∀ n, IsLaguerrePolya (F n)) (x : ℝ) {r : ℝ} (hr : 0 < r)
    (hpoint : ∀ z ∈ Metric.ball (x : ℂ) r,
      Tendsto (fun n => F n z) atTop (𝓝 (g z))) (hg : g x ≠ 0) :
    ∃ δ > 0, (∀ z ∈ Metric.ball (x : ℂ) δ, g z ≠ 0) ∧
      ∀ᶠ n in atTop, ∀ z ∈ Metric.ball (x : ℂ) δ, F n z ≠ 0 := by
  have hlim := tendstoLocallyUniformlyOn_laguerreProduct hF x hr hpoint
  have hd := hlim.differentiableOn (Eventually.of_forall fun n =>
    (differentiable_laguerreProduct (hF n).differentiable x).differentiableOn)
    Metric.isOpen_ball
  have hz : (0 : ℂ) ∈ Metric.ball 0 r := by simpa using hr
  have hc := (hd.differentiableAt (Metric.isOpen_ball.mem_nhds hz)).continuousAt
  have hgprod : laguerreProduct g x 0 ≠ 0 := by simpa [laguerreProduct] using mul_ne_zero hg hg
  obtain ⟨V, hV, havoid⟩ := hlim.exists_eventually_ne
    (Metric.ball_mem_nhds (0 : ℂ) hr) hc hgprod
  have hgood : {z | laguerreProduct g x z ≠ 0} ∈ 𝓝 (0 : ℂ) := hc.eventually_ne hgprod
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem hV hgood)
  have hmem {z : ℂ} (hzδ : z ∈ Metric.ball (x : ℂ) δ) :
      (z - (x : ℂ)) * (-I) ∈ Metric.ball (0 : ℂ) δ := by
    simpa [Metric.mem_ball, dist_eq_norm, norm_mul] using hzδ
  refine ⟨δ, hδ, (fun z hzδ => ne_zero_of_laguerreProduct_ne_zero (hball (hmem hzδ)).2), ?_⟩
  filter_upwards [havoid] with n hn z hzδ
  exact ne_zero_of_laguerreProduct_ne_zero (hn _ (hball (hmem hzδ)).1)

end RealRooted
