import RealRooted.OperatorPreservesInterlacing

open Polynomial

/-!
# Operator preservers challenge entry point

Human statement:
https://www.symmetricfunctions.com/realRootedInterlacing.htm#operatorPreservesInterlacing

Catalog reference: P. Branden, "Iterated sequences and the geometry of zeros",
J. Reine Angew. Math. 658 (2011), Theorem 9 in the operator-preserver notes
cited by the catalog.

This module exposes the checked Obreschkoff-level theorem: a linear operator
that preserves real-rootedness up to zero preserves interlacing pairs up to the
orientation ambiguity of the current `Prec` convention.
-/

namespace RealRooted
namespace Challenges
namespace OperatorPreservers

/-- Challenge-facing name for operators preserving real-rootedness up to the
zero polynomial. -/
abbrev RealRootedPreserver (T : ℝ[X] →ₗ[ℝ] ℝ[X]) : Prop :=
  RealRooted.PreservesRealRootedOrZero T

/-- Challenge-facing name for preserving interlacing pairs, allowing zero
images and the orientation ambiguity of `Prec`. -/
abbrev InterlacingPreserverUpToOrder (T : ℝ[X] →ₗ[ℝ] ℝ[X]) : Prop :=
  RealRooted.PreservesInterlacingPairsUpToOrder0 T

/-- Real-rootedness-preserving linear operators preserve interlacing pairs up
to order and zero images. -/
theorem realRootedPreserver_preservesInterlacing :
    ∀ T : ℝ[X] →ₗ[ℝ] ℝ[X],
      RealRootedPreserver T →
      InterlacingPreserverUpToOrder T :=
  RealRooted.operatorPreservesInterlacingPairsUpToOrder

end OperatorPreservers
end Challenges
end RealRooted
