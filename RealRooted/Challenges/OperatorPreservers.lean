import RealRooted.OperatorPreservesInterlacing

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

open Polynomial

namespace RealRooted
namespace Challenges
namespace OperatorPreservers

/-- Real-rootedness-preserving linear operators preserve interlacing pairs up
to order and zero images. -/
theorem realRootedPreserver_preservesInterlacing :
    RealRooted.operatorPreservesInterlacingPairsUpToOrderStatement :=
  RealRooted.operatorPreservesInterlacingPairsUpToOrder

end OperatorPreservers
end Challenges
end RealRooted
