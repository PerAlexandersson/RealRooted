module

public import RealRooted.Mathlib.NumberTheory.LSeries.RiemannXi.Theta
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Analysis.CStarAlgebra.Classes
import RealRooted.RiemannHypothesis.TotalPositivity
public import RealRooted.LaguerreInequalities.AuxiliaryProduct
public import RealRooted.Basic.Coefficients
import RealRooted.RiemannHypothesis
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.AuxiliaryCriterion
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.AuxiliaryInequality

/-!
# Fixed-auxiliary criteria for the Riemann hypothesis

Each admissible auxiliary is fixed independently. It is sufficient to test
all centers and Taylor indices for that one auxiliary.
-/

public section

open Complex Polynomial

namespace RealRooted

/-- Under RH every derivative shift of xi satisfies the inequalities of
every monic even auxiliary with nonnegative coefficients. -/
theorem auxiliaryCoefficient_riemannXiTheta_nonneg_of_even (hRH : RiemannHypothesis)
    {g : ℝ[X]} (hg : g.Monic) (he : ∀ k, Odd k → g.coeff k = 0)
    (hgn : HasNonnegCoeffs g) (n : ℕ) (x : ℝ) (k : ℕ) :
    0 ≤ auxiliaryCoefficient g (iteratedDeriv n riemannXiTheta) x k :=
  IsLaguerrePolya.auxiliaryCoefficient_nonneg
    (isLaguerrePolyaTypeI_iteratedDeriv_riemannXiTheta hRH n).toLaguerrePolya hg he hgn x k

/-- Any one admissible even auxiliary gives a full criterion for Mathlib's RH. -/
theorem riemannHypothesis_iff_auxiliaryCoefficient_nonneg {g : ℝ[X]}
    (hg : g.Monic) (he : ∀ k, Odd k → g.coeff k = 0) (hgn : HasNonnegCoeffs g)
    (ha : ∃ a ∈ (g.map ofRealHom).roots, a.im ≠ 0) :
    RiemannHypothesis ↔ ∀ x k, 0 ≤ auxiliaryCoefficient g riemannXiTheta x k := by
  constructor
  · intro h x k
    simpa only [iteratedDeriv_zero] using
      auxiliaryCoefficient_riemannXiTheta_nonneg_of_even h hg he hgn 0 x k
  · intro h
    apply riemannHypothesis_iff_riemannXiTheta_zeros.mpr
    exact fun _ hz ↦ im_eq_zero_of_auxiliaryCoefficient_nonneg differentiable_riemannXiTheta
      riemannXiTheta_conj (fun hzero ↦ riemannXiTheta_zero_ne_zero (congrFun hzero 0))
      hg he ha h hz

/-- Including every derivative shift preserves the same fixed-auxiliary RH criterion. -/
theorem riemannHypothesis_iff_auxiliaryCoefficient_shift_nonneg {g : ℝ[X]}
    (hg : g.Monic) (he : ∀ k, Odd k → g.coeff k = 0) (hgn : HasNonnegCoeffs g)
    (ha : ∃ a ∈ (g.map ofRealHom).roots, a.im ≠ 0) :
    RiemannHypothesis ↔
      ∀ n x k, 0 ≤ auxiliaryCoefficient g (iteratedDeriv n riemannXiTheta) x k := by
  constructor
  · exact fun h n x k ↦ auxiliaryCoefficient_riemannXiTheta_nonneg_of_even h hg he hgn n x k
  · intro h
    exact (riemannHypothesis_iff_auxiliaryCoefficient_nonneg hg he hgn ha).mpr
      (by simpa only [iteratedDeriv_zero] using h 0)

end RealRooted
