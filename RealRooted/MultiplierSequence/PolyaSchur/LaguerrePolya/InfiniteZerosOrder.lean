module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import TauCeti.Analysis.Complex.GrowthOrder
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.FiniteZeros
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Derivative
import RealRooted.Mathlib.Analysis.Complex.GrowthOrder.PolynomialFactor
import TauCeti.Analysis.Complex.GrowthOrder.Exponential

/-!
# Infinitely many distinct zeros below order one

Finite zero extraction leaves a zero-free entire factor of the same growth
order. Below order one that factor is constant, so a nonpolynomial function
cannot have only finitely many distinct zeros.
-/

public section

open Complex Polynomial

namespace RealRooted

/-- A nonpolynomial LP function of order below one, nonzero at zero,
has infinitely many distinct real zeros. No simplicity assumption is made. -/
theorem IsLaguerrePolya.infinite_real_zeros_of_order_lt_one
    {f : ℂ → ℂ} (hf : IsLaguerrePolya f) (hf0 : f 0 ≠ 0)
    {rho : ℝ} (horder : TauCeti.OrderLE f rho) (hrho : rho < 1)
    (hnp : ∀ p : ℂ[X], f ≠ fun z => p.eval z) :
    Set.Infinite {x : ℝ | f x = 0} := by
  by_contra hfin
  obtain ⟨q, g, _, hq0, hg, hgnz, hfactor⟩ :=
    hf.exists_polynomial_factor_of_finite_zeros hf0 (Set.not_infinite.mp hfin)
  have hq : q.map ofRealHom ≠ 0 := by
    intro h
    have hh := congrArg (fun p : ℂ[X] => p.coeff 0) h
    simp only [coeff_map, coeff_zero, ofRealHom_eq_coe] at hh
    exact hq0 (ofReal_eq_zero.mp hh)
  have hgo : TauCeti.OrderLE g rho := by
    apply TauCeti.OrderLE.of_polynomial_mul (p := q.map ofRealHom) _ hq
    simpa only [← hfactor] using horder
  obtain ⟨p, hp, heq⟩ := hgo.exists_eq_cexp_polynomial_eval_of_forall_ne_zero
    hg.differentiable hgnz
  have hdegree : p.natDegree = 0 := by
    rw [Nat.floor_eq_zero.mpr hrho] at hp
    exact Nat.eq_zero_of_le_zero hp
  apply hnp (q.map ofRealHom * C (exp (p.coeff 0)))
  funext z
  rw [hfactor, heq, eq_C_of_natDegree_eq_zero hdegree]
  simp

end RealRooted
