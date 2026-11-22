module

public import RealRooted.OperatorMatrix.CommonInput
import RealRooted.OperatorMatrix.Directed
import RealRooted.OperatorMatrix.MixedLemma

/-!
# A mixed derivative and multiplication block

The block `[D, D; X D, I]` illustrates the common-input API for entries that need not commute.
The mixed differential lemma supplies its ordered output, including constants and repeated roots.

Source: unpublished manuscript, `full-operator-block-common-input-reduction.md`, and the
mixed differential lemma in `RealRooted.OperatorMatrix.MixedLemma`.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted.OperatorMatrix

/-- The mixed derivative block satisfies all three common-input tests. The column containing
`D` kills constants, so this instance includes a nontrivial zero-image boundary. -/
theorem commonInput_derivative_derivative_theta_id :
    CommonInputColumns derivative derivative
        ((LinearMap.mulLeft ℝ X).comp derivative) LinearMap.id ∧
      CommonInputProportional derivative derivative
        ((LinearMap.mulLeft ℝ X).comp derivative) LinearMap.id ∧
      CommonInputSuccessor derivative derivative
        ((LinearMap.mulLeft ℝ X).comp derivative) LinearMap.id := by
  apply (PreservesOrderedPFPair.iff_commonInput _ _ _ _).mp
  intro p q hp hq hpq
  have htop := isPFPolynomial_derivative_add_derivative_of_interl hp hq hpq
  have hbot := isPFPolynomial_add_X_mul_derivative_of_interl hp hq hpq
  have horder := interl_derivative_add_derivative_add_X_mul_derivative hp hq hpq
  simpa only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.id_apply, add_comm]
    using And.intro htop (And.intro hbot horder)

/-- The same common-input certificate works at every input cap, including zero. -/
example (N : ℕ) : PreservesOrderedPFPairUpTo N derivative derivative
    ((LinearMap.mulLeft ℝ X).comp derivative) LinearMap.id := by
  apply PreservesOrderedPFPair.upTo
  apply (PreservesOrderedPFPair.iff_commonInput _ _ _ _).mpr
  exact commonInput_derivative_derivative_theta_id

end RealRooted.OperatorMatrix
