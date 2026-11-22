module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.TypeI
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import RealRooted.Mathlib.Analysis.Complex.PolynomialLimitCoeff

/-!
# Type-I Laguerre--Pólya products

PF polynomials belong to the positive Type-I class, including the zero polynomial.
The class is closed under multiplication, so factors at the origin can be restored
after deleting initial zero Taylor coefficients.
-/

public section

open Polynomial Filter Topology

namespace RealRooted

/-- Differentiation preserves the positive Type-I class, including zero outputs. -/
theorem IsLaguerrePolyaTypeI.deriv {f : ℂ → ℂ} (hf : IsLaguerrePolyaTypeI f) :
    IsLaguerrePolyaTypeI (deriv f) := by
  obtain ⟨p, hp, hlim⟩ := hf
  refine ⟨fun n => (p n).derivative, fun n => (hp n).derivative, ?_⟩
  have h := hlim.iteratedDeriv (fun n => ((p n).map Complex.ofRealHom).differentiable) 1
  simpa only [Polynomial.iteratedDeriv_fun_eval, Polynomial.iterate_derivative_map,
    Function.iterate_one, iteratedDeriv_one] using h

/-- Every derivative of a positive Type-I function remains positive Type-I. -/
theorem IsLaguerrePolyaTypeI.iterate_deriv {f : ℂ → ℂ}
    (hf : IsLaguerrePolyaTypeI f) (n : ℕ) : IsLaguerrePolyaTypeI (iteratedDeriv n f) := by
  induction n with
  | zero => simpa using hf
  | succ n ih => simpa [iteratedDeriv_succ] using ih.deriv

/-- Every PF polynomial defines a Type-I Laguerre--Pólya function. -/
theorem IsPFPolynomial.isLaguerrePolyaTypeI {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsLaguerrePolyaTypeI (fun z : ℂ => (p.map Complex.ofRealHom).eval z) := by
  refine ⟨fun _ => p, fun _ => hp, ?_⟩
  intro u hu x
  refine ⟨Set.univ, univ_mem, ?_⟩
  filter_upwards [] with n y
  intro _
  exact refl_mem_uniformity hu

/-- The zero function belongs to the positive Type-I Laguerre--Pólya class. -/
@[simp]
theorem IsLaguerrePolyaTypeI.zero : IsLaguerrePolyaTypeI 0 := by
  simpa [Pi.zero_def] using IsPFPolynomial.zero.isLaguerrePolyaTypeI

/-- The positive Type-I Laguerre--Pólya class is closed under products. -/
theorem IsLaguerrePolyaTypeI.mul {f g : ℂ → ℂ}
    (hf : IsLaguerrePolyaTypeI f) (hg : IsLaguerrePolyaTypeI g) :
    IsLaguerrePolyaTypeI (f * g) := by
  obtain ⟨p, hp, hptend⟩ := hf
  obtain ⟨q, hq, hqtend⟩ := hg
  refine ⟨fun n => p n * q n, fun n => (hp n).mul (hq n), ?_⟩
  have hmul := hptend.mul₀ hqtend
    (hptend.continuous <| Filter.Frequently.of_forall fun n =>
      Polynomial.continuous ((p n).map Complex.ofRealHom))
    (hqtend.continuous <| Filter.Frequently.of_forall fun n =>
      Polynomial.continuous ((q n).map Complex.ofRealHom))
  simpa only [Pi.mul_def, Polynomial.map_mul, Polynomial.eval_mul] using hmul

end RealRooted
