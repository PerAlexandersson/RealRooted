module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya

import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Jensen

public import Mathlib.Analysis.Complex.Exponential
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.Closure
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.HeatFlow
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.OperatorProduct
import RealRooted.Hermite.GaussianOperator
import RealRooted.Hermite.PolynomialGaussian
import RealRooted.Hermite.ExponentialJensenMultiplicity
import RealRooted.SimpleRoots.Reflection
import RealRooted.Mathlib.Algebra.Polynomial.Reverse

/-!
# A boundary in the Jensen interlacing sign hypothesis

Craven–Csordas (1994), Proposition 4.1(1), ends: "if φ(x) ∈ L-P and all zeros
have the same sign, then the zeros of gn and gn−1 are interlacing."
Read as a hypothesis on zeros of the symbol alone, this is false when a
Gaussian factor is allowed. The checked example `(z+1) exp(-z²)` has sole
zero `-1`, belongs to LP, and is outside the excluded nonzero-slope
polynomial–exponential case. Yet its first two Jensen rows are `1+X` and
`1+2X-2X²`, which do not interlace. Positivity hypotheses on multiplier
coefficients provide the corrected sufficient condition in `JensenPositiveInterlacing`.
-/

@[expose] public section

open Polynomial Complex RealRooted.HermitePoulain

namespace RealRooted

/-- A Gaussian times one negative-root linear factor. -/
noncomputable def oneZeroGaussian (z : ℂ) : ℂ := (z + 1) * exp (-z ^ 2)

/-- The example is an LP function with exactly the one negative real zero. -/
private theorem oneZeroGaussian_data :
    IsLaguerrePolya oneZeroGaussian ∧ oneZeroGaussian 0 = 1 ∧
      ∀ z, oneZeroGaussian z = 0 ↔ z = -1 := by
  have hlin : IsLaguerrePolya (fun z : ℂ => z + 1) := by
    apply IsLaguerrePolya.of_forall_approx
    intro R ε hε
    refine ⟨X + C 1, Or.inr (Splits.X_add_C 1), ?_⟩
    intro z _
    simpa using hε
  refine ⟨?_, by simp [oneZeroGaussian], ?_⟩
  · change IsLaguerrePolya (fun z => (z + 1) * exp (-z ^ 2))
    simpa only [Pi.mul_def, ofReal_one, neg_one_mul] using
      hlin.mul (isLaguerrePolya_exp_neg_mul_sq (a := 1) (by norm_num))
  · intro z
    simp [oneZeroGaussian, exp_ne_zero, add_eq_zero_iff_eq_neg]

/-- The Gaussian raising formula gives all monomial differential images. -/
private theorem oneZeroGaussian_operator_power (d : ℕ) :
    taylorDifferentialOperator oneZeroGaussian (X ^ d) =
      (hermiteHomogeneous X (C (-1 : ℝ)) d).derivative +
        hermiteHomogeneous X (C (-1 : ℝ)) d := by
  have h := taylorDifferentialOperator_polynomial_mul
    (f := fun z => exp (((0 : ℝ) : ℂ) * z + ((-1 : ℝ) : ℂ) * z ^ 2))
    (by fun_prop) (X + C 1) (X ^ d)
  rw [taylor_exp_quadratic_X_pow 0 (-1), applyAsDifferentialOperator_X_add_C] at h
  change taylorDifferentialOperator (fun z => (z + 1) * exp (-z ^ 2)) (X ^ d) = _
  simpa using h

/-- Both low-degree Jensen rows can be evaluated exactly. -/
private theorem oneZeroGaussian_jensen_low :
    jensenPolynomial 1 (fun k => (iteratedDeriv k oneZeroGaussian 0).re) = X + 1 ∧
      jensenPolynomial 2 (fun k => (iteratedDeriv k oneZeroGaussian 0).re) =
        1 + C 2 * X - C 2 * X ^ 2 := by
  constructor
  · have h := congrArg (reflect 1) (oneZeroGaussian_operator_power 1)
    rw [taylorDifferentialOperator_X_pow, reflect_reflect] at h
    simpa [reflect_add] using h
  · have hbase : taylorDifferentialOperator oneZeroGaussian (X ^ 2) =
        C 2 * X + (X ^ 2 - C 2) := by
      rw [oneZeroGaussian_operator_power]
      norm_num [hermiteHomogeneous_add_two, C_ofNat]
      ring
    have h := congrArg (reflect 2) hbase
    rw [taylorDifferentialOperator_X_pow, reflect_reflect] at h
    norm_num [reflect_add, reflect_sub, reflect_X, revAt_eq_ite] at h
    convert h using 1
    ring

/-- The root `-1` of the linear row is below every root of the quadratic row. -/
private theorem not_interlaces_oneZeroGaussian_rows :
    ¬ Interlaces (X + 1 : ℝ[X]) (1 + C 2 * X - C 2 * X ^ 2) := by
  intro h
  obtain ⟨rs, ss, _, _, hrs, hss, hi⟩ := h.2.2.2
  have hssone : ss = [-1] := by
    apply Multiset.coe_eq_singleton.mp
    simpa only [← C_1, roots_X_add_C] using hss
  subst ss
  cases rs with
  | nil => simp [ListInterlaces] at hi
  | cons r rs =>
      cases rs with
      | nil => simp [ListInterlaces] at hi
      | cons t rs =>
          have hr : (1 + C 2 * X - C 2 * X ^ 2 : ℝ[X]).IsRoot r := by
            apply isRoot_of_mem_roots
            rw [← hrs]
            simp
          have hrle : r ≤ -1 := hi.1
          have he : 1 + 2 * r - 2 * r ^ 2 = 0 := by simpa [IsRoot.def] using hr
          nlinarith [sq_nonneg r]

/-- Gaussian regularization makes all Jensen rows simple, independently of
the false sign implication being tested. -/
private theorem oneZeroGaussian_simple (d : ℕ) :
    IsSimpleRealRooted (jensenPolynomial d (fun k => (iteratedDeriv k oneZeroGaussian 0).re)) := by
  have hF := simple_taylor_polynomial_gaussian (q := X + C 1) (Splits.X_add_C 1)
    (by simp) 0 (s := -1) (by norm_num) (pow_ne_zero d X_ne_zero) (Splits.X.pow d)
  have hsimple : IsSimpleRealRooted (taylorDifferentialOperator oneZeroGaussian (X ^ d)) := by
    change IsSimpleRealRooted
      (taylorDifferentialOperator (fun z => (z + 1) * exp (-z ^ 2)) (X ^ d))
    simpa using hF
  rw [taylorDifferentialOperator_X_pow] at hsimple
  have hsplit := (splits_reflect_iff (natDegree_jensenPolynomial_le d _)).mp hsimple.2.1
  have hconst :
      (jensenPolynomial d (fun k => (iteratedDeriv k oneZeroGaussian 0).re)).coeff 0 ≠ 0 := by
    simp [coeff_jensenPolynomial, oneZeroGaussian]
  refine ⟨?_, hsplit, hsimple.2.2.of_reflect hconst hsplit (natDegree_jensenPolynomial_le d _)⟩
  intro hz
  exact hconst (by simp [hz])

/-- The example is outside the exceptional polynomial–exponential class. -/
private theorem oneZeroGaussian_not_exp_polynomial (q : ℝ[X]) {a : ℝ} (ha : a ≠ 0) :
    oneZeroGaussian ≠ fun z => (q.map ofRealHom).eval z * exp ((a : ℂ) * z) := by
  intro heq
  have hq : q ≠ 0 := by
    intro hz
    have h := congrFun heq 0
    simp [oneZeroGaussian, hz] at h
  have hs := oneZeroGaussian_simple (q.natDegree + 2)
  rw [heq] at hs
  have hm := rootMultiplicity_jensen_polynomial_exp hq ha (q.natDegree + 2) (by lia)
  have hr := (rootMultiplicity_pos hs.1).mp (show 0 <
      (jensenPolynomial (q.natDegree + 2) (fun k =>
        (iteratedDeriv k
          (fun z => (q.map ofRealHom).eval z * exp ((a : ℂ) * z)) 0).re)).rootMultiplicity
          (-a⁻¹) from by rw [hm]; lia)
  have hsimple := hs.2.2 _ hr
  lia

/-- Same-sign zeros of the symbol alone do not imply consecutive Jensen
interlacing, even under the other hypotheses of the simple-Jensen theorem. -/
theorem oneZeroGaussian_counterexample :
    IsLaguerrePolya oneZeroGaussian ∧ oneZeroGaussian 0 = 1 ∧
      (∀ z, oneZeroGaussian z = 0 ↔ z = -1) ∧
      (∀ (q : ℝ[X]) (a : ℝ), a ≠ 0 →
        oneZeroGaussian ≠ fun z => (q.map ofRealHom).eval z * exp ((a : ℂ) * z)) ∧
      ¬ Interlaces (jensenPolynomial 1 (fun k => (iteratedDeriv k oneZeroGaussian 0).re))
        (jensenPolynomial 2 (fun k => (iteratedDeriv k oneZeroGaussian 0).re)) := by
  refine ⟨oneZeroGaussian_data.1, oneZeroGaussian_data.2.1, oneZeroGaussian_data.2.2,
    fun q _ ha => oneZeroGaussian_not_exp_polynomial q ha, ?_⟩
  rw [oneZeroGaussian_jensen_low.1, oneZeroGaussian_jensen_low.2]
  exact not_interlaces_oneZeroGaussian_rows

end RealRooted
