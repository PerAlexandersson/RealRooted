module

public import RealRooted.Hermite.Poulain
public import RealRooted.SimpleRoots
public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Operator
import RealRooted.Hermite.PoulainSimple
import RealRooted.Hermite.GaussianOperator
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.OperatorProduct

/-!
# Strict polynomial–Gaussian differential symbols

A finite real-rooted differential symbol nonzero at zero preserves simple
real roots. Combining this with strict Gaussian regularization handles
symbols `q(z) exp(a z + s z²)` with `s < 0` and `q(0) ≠ 0`.
-/

public section

open Polynomial Complex RealRooted.HermitePoulain

namespace RealRooted

/-- Finite real-rooted differential factors nonzero at zero preserve simple
real-rootedness, regardless of their degree. -/
theorem simple_operator_of_simple_input {q p : ℝ[X]}
    (hq : q.Splits) (hq0 : q.coeff 0 ≠ 0) (hp : IsSimpleRealRooted p) :
    IsSimpleRealRooted (applyAsDifferentialOperator q p) := by
  have hqne : q ≠ 0 := by intro hz; simp [hz] at hq0
  have hF0 : applyAsDifferentialOperator q p ≠ 0 := by
    intro hz
    have htop := congrArg (fun u : ℝ[X] => u.coeff p.natDegree) hz
    rw [coeff_applyAsDifferentialOperator_natDegree, coeff_zero, coeff_natDegree] at htop
    exact mul_ne_zero hq0 (leadingCoeff_ne_zero.mpr hp.1) htop
  refine ⟨hF0, (applyAsDifferentialOperator_eq_zero_or_splits
    ⟨hqne, hq⟩ ⟨hp.1, hp.2.1⟩).resolve_left hF0, ?_⟩
  intro r hr
  have hpos := (rootMultiplicity_pos hF0).mpr hr
  by_contra hnot
  have hm : 2 ≤ (applyAsDifferentialOperator q p).rootMultiplicity r := by lia
  have hback := rootMultiplicity_operator_eq_add_natDegree hq hq0 hp.1 hp.2.1 hm
  have hroot : p.IsRoot r := (rootMultiplicity_pos hp.1).mp (by lia)
  rw [hp.2.2 r hroot] at hback
  lia

/-- A real-rooted polynomial times a strictly negative Gaussian symbol
strictly regularizes every nonzero real-rooted polynomial input. -/
theorem simple_taylor_polynomial_gaussian {q p : ℝ[X]}
    (hq : q.Splits) (hq0 : q.coeff 0 ≠ 0) (a : ℝ) {s : ℝ} (hs : s < 0)
    (hp0 : p ≠ 0) (hp : p.Splits) :
    IsSimpleRealRooted (taylorDifferentialOperator
      (fun z => (q.map ofRealHom).eval z * exp ((a : ℂ) * z + (s : ℂ) * z ^ 2)) p) := by
  rw [taylorDifferentialOperator_polynomial_mul (by fun_prop)]
  exact simple_operator_of_simple_input hq hq0 (simple_taylor_exp_quadratic a hs hp0 hp)

end RealRooted
