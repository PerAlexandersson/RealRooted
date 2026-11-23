module

public import RealRooted.LaguerreInequalities.Analytic
public import TauCeti.Analysis.Complex.Pick.Nevanlinna
public import Mathlib.Analysis.Analytic.Order
import RealRooted.LaguerreInequalities.AtomicRepresentation
import RealRooted.LaguerreInequalities.MeasureSupport
import RealRooted.Mathlib.Analysis.Calculus.LogDeriv.Residue
import RealRooted.Mathlib.Analysis.Complex.Pick.Atoms

/-!
# Nevanlinna atom masses are zero multiplicities

The residue limit of the logarithmic derivative and the boundary limit of the
Nevanlinna integral identify every atom with the analytic zero multiplicity
divided by `1 + r^2`. In particular, the finite measure gives a summable weighted
sequence of zero multiplicities, without assuming an entire growth bound.
-/

public section

open Complex Filter MeasureTheory Set Topology
open scoped ComplexConjugate

namespace RealRooted

/-- Every singleton mass of a finite Nevanlinna measure representing a nonzero
entire function's negative logarithmic derivative is its zero multiplicity
divided by `1 + r^2`. The formula also holds at points that are not zeros. -/
theorem measureReal_singleton_eq_analyticOrderNatAt_div {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hne : f ≠ 0) {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    {b c : ℝ} (hrep : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet,
      -logDeriv f z = (b : ℂ) * z + ∫ x, TauCeti.nevanlinnaKernel z x ∂ρ + c)
    (r : ℝ) : ρ.real {r} = (analyticOrderNatAt f (r : ℂ) : ℝ) / (1 + r ^ 2) := by
  obtain ⟨w, hw⟩ := Function.ne_iff.mp hne
  have ha : AnalyticOnNhd ℂ f univ := fun z _ => hf.analyticAt z
  have hfin := ha.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (x := w) (y := (r : ℂ)) (mem_univ _) (mem_univ _)
    (by rw [(hf.analyticAt w).analyticOrderAt_eq_zero.mpr hw]; simp)
  have heq := tendsto_nhds_unique
    (TauCeti.tendsto_mul_im_of_eq_nevanlinnaKernel_add ρ b c r hrep)
    ((hf.analyticAt r).tendsto_mul_im_neg_logDeriv hfin)
  apply (eq_div_iff (by positivity : (1 + r ^ 2 : ℝ) ≠ 0)).mpr
  simpa only [mul_comm] using heq

/-- Generalized Laguerre inequalities imply summability of the zero multiplicities
weighted by `1 / (1 + r^2)`, with every real zero counted to its actual order. -/
theorem summable_analyticOrderNatAt_div_one_add_sq {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hc : ∀ z, f (conj z) = conj (f z)) (hne : f ≠ 0)
    (h : ∀ x n, 0 ≤ laguerreCoefficient f x n) :
    Summable (fun r : {x : ℝ | f x = 0} =>
      (analyticOrderNatAt f (r : ℂ) : ℝ) / (1 + (r : ℝ) ^ 2)) := by
  obtain ⟨ρ, b, hρ, _, hrep, hs, _⟩ := exists_nevanlinna_supported_on_zeros hf hc h
  let _ := hρ
  have heq := measureReal_singleton_eq_analyticOrderNatAt_div hf hne hrep
  simpa only [heq] using (hasSum_measureReal_real_zeros hf hne hs).summable

end RealRooted
