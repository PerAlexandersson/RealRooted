module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
public import TauCeti.Analysis.Complex.GrowthOrder
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeIReverse
import RealRooted.MultiplierSequence.PolyaSchur.GeometricGrowth
import RealRooted.Mathlib.Analysis.Complex.TaylorGrowth
import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Star

/-!
# Exponential growth of positive Type-I functions

The PF multiplier sequence of Taylor derivatives has a geometric majorant,
including any initial zero prefix. Consequently every positive Type-I
Laguerre--Pólya function is of exponential type and has order at most one.
The zero function is included throughout.
-/

public section

open Complex Filter Topology Asymptotics Bornology

namespace RealRooted

/-- Every positive Type-I function has a global exponential majorant, with
no nonzero-at-zero assumption. -/
theorem IsLaguerrePolyaTypeI.exists_norm_le_mul_exp {f : ℂ → ℂ}
    (hf : IsLaguerrePolyaTypeI f) :
    ∃ C ≥ 0, ∃ A ≥ 0, ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (A * ‖z‖) := by
  let γ : ℕ → ℝ := fun n => (iteratedDeriv n f 0).re
  have hreal (n : ℕ) : iteratedDeriv n f 0 = (γ n : ℂ) :=
    (ofReal_re_iteratedDeriv_zero hf.toLaguerrePolya.conj n).symm
  have hγ := hf.isPFMultiplierSequence_of_iteratedDeriv_zero
    (fun n => by simpa only [← iteratedDeriv_eq_iterate] using hreal n)
  obtain ⟨C, hC, A, hA, hbound⟩ := hγ.exists_geometric_bound
  refine ⟨C, hC, A, hA, ?_⟩
  intro z
  have hc : ∀ n, ‖iteratedDeriv n f 0‖ ≤ C * A ^ n := by
    intro n
    rw [hreal n, norm_real, Real.norm_of_nonneg (hγ.nonneg n)]
    exact hbound n
  simpa only [sub_zero] using
    hf.toLaguerrePolya.differentiable.norm_le_mul_exp_of_iteratedDeriv_bound hc z

/-- Every positive Type-I Laguerre--Pólya function has order at most one,
including functions with an arbitrary zero at the origin and the zero function. -/
theorem IsLaguerrePolyaTypeI.orderLE_one {f : ℂ → ℂ} (hf : IsLaguerrePolyaTypeI f) :
    TauCeti.OrderLE f 1 := by
  obtain ⟨C, _, A, _, hbound⟩ := hf.exists_norm_le_mul_exp
  rw [TauCeti.orderLE_def]
  intro p hp
  have hb : f =O[cobounded ℂ] (fun z => Real.exp (A * ‖z‖)) := by
    apply IsBigO.of_bound C
    exact Eventually.of_forall fun z => by simpa using hbound z
  exact hb.trans (by simpa only [Real.rpow_one] using
    (TauCeti.isBigO_exp_mul_norm_rpow (E := ℂ) A hp))

end RealRooted
