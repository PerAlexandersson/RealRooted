import RealRooted.AffineLineRestriction
import RealRooted.Mathlib.Algebra.MvPolynomial.Homogenize
import RealRooted.Mathlib.Algebra.MvPolynomial.Nonnegative

/-!
# Stability of the top homogeneous component

This file constructs a stable damping homotopy from a multivariate polynomial
toward its top homogeneous component. Root continuity will supply the endpoint.
-/

open Polynomial
open scoped BigOperators

namespace RealRooted

noncomputable section

/-- Dampen the degree-`k` homogeneous component by `δ ^ (totalDegree - k)`.
At positive `δ`, this is a nonzero scalar multiple of a positive coordinate
rescaling of the source polynomial. -/
def homogeneousTopApproximation {σ : Type*} (P : MvPolynomial σ ℝ)
    (δ : ℝ) : MvPolynomial σ ℝ :=
  ∑ k ∈ Finset.range (P.totalDegree + 1),
    MvPolynomial.C (δ ^ (P.totalDegree - k)) *
      MvPolynomial.homogeneousComponent k P

/-- Evaluating the damping homotopy is evaluation of ordinary homogenization
with the homogenizing coordinate specialized to the damping parameter. -/
theorem eval_homogeneousTopApproximation {σ : Type*}
    (P : MvPolynomial σ ℝ) (δ : ℝ) (z : σ → ℝ) :
    MvPolynomial.eval z (homogeneousTopApproximation P δ) =
      MvPolynomial.eval (fun o => Option.elim o δ z)
        (MvPolynomial.ordinaryHomogenization P P.totalDegree) := by
  rw [MvPolynomial.eval_ordinaryHomogenization]
  simp [homogeneousTopApproximation]

/-- Complexification commutes with the damping homotopy term by term. -/
theorem complexifyMv_homogeneousTopApproximation {σ : Type*}
    (P : MvPolynomial σ ℝ) (δ : ℝ) :
    complexifyMv (homogeneousTopApproximation P δ) =
      ∑ k ∈ Finset.range (P.totalDegree + 1),
        MvPolynomial.C ((δ : ℂ) ^ (P.totalDegree - k)) *
          MvPolynomial.homogeneousComponent k (complexifyMv P) := by
  unfold homogeneousTopApproximation complexifyMv
  simp [MvPolynomial.map_homogeneousComponent]

/-- At nonzero damping parameter, evaluation of the homotopy is a scalar
multiple of evaluation of the source at inversely rescaled coordinates. -/
theorem eval_complexifyMv_homogeneousTopApproximation {σ : Type*}
    (P : MvPolynomial σ ℝ) (δ : ℝ) (z : σ → ℂ) (hδ : δ ≠ 0) :
    MvPolynomial.eval z (complexifyMv (homogeneousTopApproximation P δ)) =
      (δ : ℂ) ^ P.totalDegree *
        MvPolynomial.eval (fun i => z i / (δ : ℂ)) (complexifyMv P) := by
  have htotal : (complexifyMv P).totalDegree = P.totalDegree := by
    unfold complexifyMv MvPolynomial.totalDegree
    rw [MvPolynomial.support_map_of_injective _ Complex.ofRealHom.injective]
  rw [complexifyMv_homogeneousTopApproximation]
  simp only [map_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C]
  rw [← MvPolynomial.eval_ordinaryHomogenization]
  rw [MvPolynomial.eval_ordinaryHomogenization_eq_pow_mul_eval_div
    (complexifyMv P) (by rw [htotal]) (by exact_mod_cast hδ)]

/-- Positive damping parameters preserve multivariate real stability. -/
theorem MvRealStable.homogeneousTopApproximation
    {σ : Type*} {P : MvPolynomial σ ℝ} (hP : MvRealStable P)
    {δ : ℝ} (hδ : 0 < δ) :
    MvRealStable (homogeneousTopApproximation P δ) := by
  intro z hz
  rw [eval_complexifyMv_homogeneousTopApproximation P δ z hδ.ne']
  apply mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hδ.ne'))
  apply hP
  intro i
  change 0 < (z i / (δ : ℂ)).im
  rw [Complex.div_ofReal_im]
  exact div_pos (hz i) hδ

end

end RealRooted
