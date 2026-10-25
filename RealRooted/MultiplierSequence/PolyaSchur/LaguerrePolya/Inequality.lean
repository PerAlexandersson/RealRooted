module

public import RealRooted.Mathlib.Analysis.Complex.LocallyUniformLimit
public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
public import RealRooted.Wronskian.Algebra

/-!
# Laguerre's inequality for Laguerre--Pólya functions

This leaf transports the polynomial Laguerre inequality through the locally
uniform limits in `IsLaguerrePolya`.
-/

@[expose] public section

open Filter Polynomial Topology

noncomputable section

namespace RealRooted

/-- **Laguerre's inequality** for a zero-aware Laguerre--Pólya function on the real axis.
The statement writes `_root_.deriv`, since `deriv` would resolve to `IsLaguerrePolya.deriv`. -/
theorem IsLaguerrePolya.laguerre_form_nonneg
    {f : ℂ → ℂ} (hf : IsLaguerrePolya f) (x : ℝ) :
    0 ≤ (_root_.deriv f (x : ℂ)).re ^ 2 - (f (x : ℂ)).re *
      (_root_.deriv (_root_.deriv f) (x : ℂ)).re := by
  rcases hf with ⟨p, hp, hlim⟩
  apply hlim.laguerre_form_nonneg
  · exact Eventually.of_forall fun n =>
      Polynomial.differentiable ((p n).map Complex.ofRealHom)
  · have hderiv : ∀ q : ℂ[X],
        _root_.deriv (fun z => q.eval z) = fun z => q.derivative.eval z :=
      fun q => funext fun _ => Polynomial.deriv q
    filter_upwards [] with n
    intro t
    have hre : ∀ q : ℝ[X], ((q.map Complex.ofRealHom).eval (t : ℂ)).re = q.eval t := by
      intro q
      rw [Polynomial.eval_map, show (t : ℂ) = Complex.ofRealHom t from rfl,
        Polynomial.eval₂_at_apply]
      rfl
    simp only [hderiv, Polynomial.derivative_map, hre]
    rcases hp n with hp | hp
    · simp [hp]
    · exact RealRooted.laguerre_form_nonneg hp t

end RealRooted
