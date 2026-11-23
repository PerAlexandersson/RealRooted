module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import TauCeti.Analysis.Complex.GrowthOrder
import RealRooted.Mathlib.Analysis.Complex.GrowthOrder.OfBound
import RealRooted.Mathlib.Analysis.Complex.LineIdentity
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.UniformDerivativeBounds
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative

/-!
# Growth order of Laguerre--Pólya functions

The quantitative Szász estimate gives a quadratic exponential bound after a
real translation to a nonzero value. Consequently every LP function has order
at most two, including functions vanishing at the origin and the zero function.
-/

public section

open Complex Filter Topology

namespace RealRooted

/-- Every Laguerre--Pólya function has growth order at most two. -/
theorem IsLaguerrePolya.orderLE_two {f : ℂ → ℂ} (hf : IsLaguerrePolya f) :
    TauCeti.OrderLE f 2 := by
  by_cases hf0 : f = 0
  · subst f
    exact TauCeti.orderLE_const 0 2
  have hreal : ∃ x : ℝ, f x ≠ 0 := by
    by_contra! hzero
    apply hf0
    have h := hf.analyticOnNhd.eqOn_zero_of_line_eq_zero
      (z₀ := 0) (v := 1) isPreconnected_univ (Set.mem_univ _) one_ne_zero
      (Eventually.of_forall fun x => by simpa using hzero x)
    exact funext fun z => h (Set.mem_univ z)
  obtain ⟨x, hx⟩ := hreal
  let g : ℂ → ℂ := fun z => f (z + x)
  have hg : IsLaguerrePolya g := by
    simpa only [Complex.ofReal_one, one_mul] using hf.comp_affine_real 1 x
  have hg0 : g 0 ≠ 0 := by simpa only [g, zero_add] using hx
  let K := max (max ‖g 0‖ ‖(g 0)⁻¹‖) (max ‖_root_.deriv g 0‖ ‖_root_.deriv (_root_.deriv g) 0‖)
  have h0 : ‖g 0‖ ≤ K := (le_max_left _ _).trans (le_max_left _ _)
  have hi : ‖(g 0)⁻¹‖ ≤ K := (le_max_right _ _).trans (le_max_left _ _)
  have h1 : ‖_root_.deriv g 0‖ ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have h2 : ‖_root_.deriv (_root_.deriv g) 0‖ ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨B, _, C, _, hbound⟩ :=
    exists_uniform_norm_bound_of_jet_bounds ((norm_nonneg _).trans h0)
  have hgo : TauCeti.OrderLE g 2 := TauCeti.orderLE_of_norm_le_mul_exp_rpow
    (by simpa only [Real.rpow_two] using hbound g hg hg0 h0 hi h1 h2)
  simpa only [g, one_mul, neg_add_cancel_right] using hgo.comp_mul_add 1 (-(x : ℂ))

end RealRooted
