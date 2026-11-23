module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Polynomial
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.DifferentialMultiplicity
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.Mathlib.Analysis.Complex.CompactJets
import RealRooted.Mathlib.Analysis.Complex.PolynomialLimitCoeff

/-!
# Simplicity from growing finite differential factors

A common nonzero image of finite real-rooted operators cannot have a multiple
zero if their degrees diverge and their LP inputs converge locally uniformly
to a nonzero entire function. Multiplicity descent would force every fixed
Taylor derivative of the limit to vanish at that point.
-/

public section

open Complex Polynomial Filter Topology

namespace RealRooted

/-- Growing finite differential factors force simplicity of a common nonzero
image when the LP inputs have a nonzero entire locally uniform limit. -/
theorem deriv_ne_zero_of_differential_tails
    {g : ℕ → ℂ → ℂ} {f H : ℂ → ℂ} {p : ℕ → ℝ[X]}
    (hg : ∀ n, IsLaguerrePolya (g n))
    (hlim : TendstoLocallyUniformly g f atTop)
    (hf : Differentiable ℂ f) (hf0 : f ≠ 0)
    (hp : ∀ n, (p n).Splits)
    (hdeg : Tendsto (fun n => (p n).natDegree) atTop atTop)
    (hfac : ∀ n, H = ((p n).map ofRealHom).differentialApply (g n))
    (hH : H ≠ 0) {x : ℝ} (hx : H x = 0) : _root_.deriv H x ≠ 0 := by
  intro hd
  obtain ⟨j, hj⟩ := Complex.exists_iteratedDeriv_ne_zero hf hf0 (x : ℂ)
  have hzero : ∀ᶠ n in atTop, iteratedDeriv j (g n) x = 0 := by
    filter_upwards [(tendsto_atTop.mp hdeg) j] with n hn
    have hne : ∃ z, ((p n).map ofRealHom).differentialApply (g n) z ≠ 0 := by
      rw [← hfac n]
      simpa only [Pi.zero_apply] using Function.ne_iff.mp hH
    have hvan := (hg n).vanishing_of_differentialApply (hp n) hne (k := 2)
      (by decide) (by
        intro i hi
        rw [← hfac n]
        have hi' : i = 0 ∨ i = 1 := by lia
        rcases hi' with rfl | rfl
        · simpa only [iteratedDeriv_zero] using hx
        · simpa only [iteratedDeriv_one] using hd)
    exact hvan j (by lia)
  have hderiv := (tendstoLocallyUniformlyOn_univ.mpr
    (hlim.iteratedDeriv (fun n => (hg n).differentiable) j)).tendsto_at
      (Set.mem_univ (x : ℂ))
  have hzlim : Tendsto (fun n => iteratedDeriv j (g n) x) atTop (𝓝 (0 : ℂ)) :=
    (tendsto_congr' hzero).mpr tendsto_const_nhds
  exact hj (tendsto_nhds_unique hderiv hzlim)

end RealRooted
