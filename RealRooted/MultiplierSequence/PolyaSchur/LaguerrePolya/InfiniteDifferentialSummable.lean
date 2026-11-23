module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Basic
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.InfiniteDifferentialLocal
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Closure

/-!
# Globally convergent infinite differential images

The checked local pointwise operator theorem gives LP preservation of the
actual globally convergent series, without supplied order bounds.
-/

public section

open Complex Filter Topology

namespace RealRooted

/-- A globally convergent differential series with LP symbol and target
is itself LP. This is a global specialization of the checked local theorem. -/
theorem IsLaguerrePolya.infiniteDifferentialApply_of_summable {φ f : ℂ → ℂ}
    (hφ : IsLaguerrePolya φ) (hf : IsLaguerrePolya f)
    (hs : ∀ z : ℂ, Summable (fun n : ℕ =>
      iteratedDeriv n φ 0 * iteratedDeriv n f z / (n.factorial : ℂ))) :
    IsLaguerrePolya (infiniteDifferentialApply φ f) := by
  apply IsLaguerrePolya.of_forall_approx
  intro R ε hε
  obtain ⟨G, hG, heq⟩ := hφ.exists_eqOn_differential_series hf (r := R + 1)
    (g := infiniteDifferentialApply φ f) (fun z _ => (hs z).hasSum.tendsto_sum_nat)
  obtain ⟨p, hp, happrox⟩ := hG.exists_approx R hε
  refine ⟨p, hp, fun z hz => ?_⟩
  have hz' : z ∈ Metric.ball (0 : ℂ) (R + 1) := by
    simpa only [Metric.mem_ball, dist_zero_right] using hz.trans_lt (lt_add_one R)
  rw [← heq hz']
  exact happrox z hz

end RealRooted
