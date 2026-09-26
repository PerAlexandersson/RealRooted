import RealRooted.OperatorPreservesInterlacing

open Polynomial

/-!
# Operator preservers challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "operator-preservers"
authors = ["Brändén"]
years = [2011]

[[definitions]]
name = "RealRooted.PreservesRealRootedOrZero"
module = "RealRooted.OperatorPreservesInterlacing"

[[definitions]]
name = "RealRooted.PreservesInterlacingPairsUpToOrder0"
module = "RealRooted.OperatorPreservesInterlacing"

[[theorems]]
name = "RealRooted.Challenges.OperatorPreservers.realRootedPreserver_preservesInterlacing"
-->

<!-- realrooted-catalog-content -->
# Operators preserving interlacing

A real-linear operator that preserves real-rootedness up to zero also
preserves interlacing, up to reversing the orientation.

## References

P. Brändén, “Iterated sequences and the geometry of zeros,” *Journal für die
reine und angewandte Mathematik* 658 (2011), 115–131.  See also the
[operator-preserver overview on symmetricfunctions.com](https://www.symmetricfunctions.com/realRootedInterlacing.htm#operatorPreservesInterlacing).
<!-- /realrooted-catalog-content -->

Human statement:
https://www.symmetricfunctions.com/realRootedInterlacing.htm#operatorPreservesInterlacing

Catalog reference: P. Branden, "Iterated sequences and the geometry of zeros",
J. Reine Angew. Math. 658 (2011), Theorem 9 in the operator-preserver notes
cited by the catalog.

This module exposes the checked Obreschkoff-level theorem: a linear operator
that preserves real-rootedness up to zero preserves interlacing pairs up to the
orientation ambiguity of the current `StrictInterl` convention.
-/

namespace RealRooted
namespace Challenges
namespace OperatorPreservers

/-- Real-rootedness-preserving linear operators preserve interlacing pairs up
to order and zero images. -/
theorem realRootedPreserver_preservesInterlacing :
    ∀ T : ℝ[X] →ₗ[ℝ] ℝ[X],
      PreservesRealRootedOrZero T →
      PreservesInterlacingPairsUpToOrder0 T :=
  RealRooted.operatorPreservesInterlacingPairsUpToOrder

end OperatorPreservers
end Challenges
end RealRooted
