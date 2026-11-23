module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import RealRooted.Mathlib.Analysis.Calculus.IteratedDeriv.Polynomial
public import RealRooted.Hermite.Poulain
import RealRooted.Mathlib.Analysis.Complex.PolynomialLimitCoeff

/-!
# Polynomial differential operators on entire Laguerre--Pólya functions

A real-rooted polynomial symbol acts on an entire Laguerre--Pólya target by a
finite linear combination of derivatives. The result remains in the class,
including the zero output. This is the finite-symbol case of the infinite
differential-operator theorem quoted by O'Sullivan as Theorem 3.6.
-/

public section

open Complex Polynomial Filter Topology

namespace RealRooted

/-- Evaluating the Hermite--Poulain polynomial operator agrees with applying the
same finite differential symbol to the complex polynomial function. -/
theorem differentialApply_eval_map (q p : ℝ[X]) (z : ℂ) :
    (q.map ofRealHom).differentialApply (fun w => (p.map ofRealHom).eval w) z =
      ((HermitePoulain.applyAsDifferentialOperator q p).map ofRealHom).eval z := by
  simp only [Polynomial.differentialApply, HermitePoulain.applyAsDifferentialOperator,
    natDegree_map_eq_of_injective ofRealHom.injective, coeff_map, iteratedDeriv_fun_eval,
    iterate_derivative_map, smul_eq_mul, Polynomial.map_sum, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]

/-- Every real-rooted polynomial differential symbol preserves the entire
Laguerre--Pólya class. Both a zero symbol and a zero output are allowed. -/
theorem IsLaguerrePolya.differentialApply {f : ℂ → ℂ} (hf : IsLaguerrePolya f)
    {q : ℝ[X]} (hq : q.Splits) : IsLaguerrePolya ((q.map ofRealHom).differentialApply f) := by
  by_cases hq0 : q = 0
  · simp only [hq0, Polynomial.map_zero, Polynomial.differentialApply_zero]
    exact IsLaguerrePolya.zero
  obtain ⟨p, hp, ht⟩ := hf
  refine ⟨fun n => HermitePoulain.applyAsDifferentialOperator q (p n), fun n => ?_, ?_⟩
  · by_cases hp0 : p n = 0
    · exact Or.inl (by simp [hp0])
    · exact HermitePoulain.applyAsDifferentialOperator_eq_zero_or_splits ⟨hq0, hq⟩
        ⟨hp0, (hp n).resolve_left hp0⟩
  · have hlim := Polynomial.tendstoLocallyUniformly_differentialApply
      (q.map ofRealHom) ht (fun n => (p n).map ofRealHom |>.differentiable)
    convert hlim using 1
    ext n z
    exact (differentialApply_eval_map q (p n) z).symm

end RealRooted
