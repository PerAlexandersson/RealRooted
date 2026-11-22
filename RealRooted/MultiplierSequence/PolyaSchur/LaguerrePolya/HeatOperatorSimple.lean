module

import RealRooted.Mathlib.Analysis.Complex.HeatOperator.TimeDerivative

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya

public import RealRooted.Mathlib.Analysis.Complex.HeatOperator.Basic

import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.HeatOperator
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.HeatFlowStrict
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Zeros
import RealRooted.Mathlib.Analysis.Complex.HeatOperator.Nonzero

/-!
# Simple real zeros under entire backward heat evolution

Craven–Csordas (1994), Theorem 3.10: for a nonzero LP entire function of order
strictly below two, every positive backward heat time gives only simple real
zeros. The actual convergent heat series, its LP closure, its parameter heat
equations, and nonzero output have all been established before this application.
-/

public section

open Complex Filter Topology

namespace RealRooted

/-- Every zero of a positive-time entire heat image of a nonzero LP function
of order below two has nonzero derivative. -/
theorem IsLaguerrePolya.deriv_heatOperator_ne_zero {f : ℂ → ℂ} (hf : IsLaguerrePolya f)
    {ρ : ℝ} (horder : TauCeti.OrderLE f ρ) (hρ : ρ < 2) (hf0 : f ≠ 0)
    {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : Complex.heatOperator (t : ℂ) f z = 0) :
    _root_.deriv (Complex.heatOperator (t : ℂ) f) z ≠ 0 := by
  apply deriv_ne_zero_of_laguerrePolya_heat_flow_complex
    (u := fun s => Complex.heatOperator (s : ℂ) f) _ _ _ hz
  · filter_upwards [eventually_gt_nhds ht] with s hs
    exact hf.heatOperator horder hρ hs.le
  · simpa only [Pi.zero_apply] using
      Function.ne_iff.mp (Complex.heatOperator_ne_zero hf.differentiable horder hρ hf0 t)
  · intro x n
    exact hasDerivAt_re_iteratedDeriv_heatOperator hf.differentiable horder hρ t x n

/-- Craven–Csordas (1994), Theorem 3.10: positive backward heat evolution of a
nonzero LP input of order below two remains nonzero LP and has only simple real zeros. -/
theorem IsLaguerrePolya.heatOperator_simple_zeros {f : ℂ → ℂ} (hf : IsLaguerrePolya f)
    {ρ : ℝ} (horder : TauCeti.OrderLE f ρ) (hρ : ρ < 2) (hf0 : f ≠ 0)
    {t : ℝ} (ht : 0 < t) :
    IsLaguerrePolya (Complex.heatOperator (t : ℂ) f) ∧ Complex.heatOperator (t : ℂ) f ≠ 0 ∧
      ∀ z, Complex.heatOperator (t : ℂ) f z = 0 →
        z.im = 0 ∧ _root_.deriv (Complex.heatOperator (t : ℂ) f) z ≠ 0 := by
  have hLP := hf.heatOperator horder hρ ht.le
  have hn := Complex.heatOperator_ne_zero hf.differentiable horder hρ hf0 t
  exact ⟨hLP, hn, fun _ hz => ⟨hLP.im_eq_zero_of_eq_zero hn hz,
    hf.deriv_heatOperator_ne_zero horder hρ hf0 ht hz⟩⟩

end RealRooted
