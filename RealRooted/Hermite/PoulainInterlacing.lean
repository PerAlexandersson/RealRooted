import RealRooted.Hermite.Poulain
import RealRooted.OperatorPreservesInterlacing

/-!
# Hermite--Poulain operators preserve interlacing

Human statement:
https://www.symmetricfunctions.com/realRootedInterlacing.htm#hermitePoulainInterlacing

For a nonzero real-rooted `f`, the operator `g ↦ f(D) g` is real-linear and
preserves real-rootedness up to zero, by the Hermite--Poulain theorem.  The
operator-preserver theorem then shows that it maps interlacing pairs to
interlacing pairs, in one of the two orientations.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace HermitePoulain

/-- The operator `g ↦ f(D) g` as a real-linear map. -/
def differentialOperator (f : ℝ[X]) : ℝ[X] →ₗ[ℝ] ℝ[X] where
  toFun := applyAsDifferentialOperator f
  map_add' g h := by
    simp [applyAsDifferentialOperator, iterate_map_add, mul_add,
      Finset.sum_add_distrib]
  map_smul' c g := by
    simp [applyAsDifferentialOperator, smul_eq_C_mul, iterate_derivative_C_mul,
      Finset.mul_sum, mul_left_comm]

@[simp] theorem differentialOperator_apply (f g : ℝ[X]) :
    differentialOperator f g = applyAsDifferentialOperator f g :=
  rfl

/-- For nonzero real-rooted `f`, the operator `f(D)` preserves real-rootedness
up to zero. -/
theorem preservesRealRootedOrZero_differentialOperator {f : ℝ[X]}
    (hf : f ≠ 0 ∧ f.Splits) :
    PreservesRealRootedOrZero (differentialOperator f) :=
  fun _ hg ↦ differential_operator_preserves_real_rooted hf hg

/-- Hermite--Poulain operators preserve interlacing: if `f` is nonzero and
real-rooted and `g` and `h` interlace, then `f(D) g` and `f(D) h` interlace in
one of the two orientations, where the images may vanish. -/
theorem interl_or_interl_applyAsDifferentialOperator {f g h : ℝ[X]}
    (hf : f ≠ 0 ∧ f.Splits) (hgh : StrictInterl g h) :
    Interl (applyAsDifferentialOperator f g) (applyAsDifferentialOperator f h) ∨
      Interl (applyAsDifferentialOperator f h) (applyAsDifferentialOperator f g) :=
  operatorPreservesInterlacingPairsUpToOrder _
    (preservesRealRootedOrZero_differentialOperator hf) hgh

end HermitePoulain
end RealRooted
