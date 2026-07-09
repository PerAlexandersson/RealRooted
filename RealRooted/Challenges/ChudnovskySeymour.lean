import RealRooted.HeilmannLieb

/-!
# Chudnovsky--Seymour challenge entry point

Human statement:
https://www.symmetricfunctions.com/realRootedGraphs.htm#clawFreeGraph

Original publication: M. Chudnovsky and P. Seymour, "The roots of the
independence polynomial of a clawfree graph", J. Combin. Theory Ser. B 97
(2007), 350--357.

This challenge-facing module exposes the graph-form Chudnovsky--Seymour theorem:
finite claw-free graphs have real-rooted independence polynomials.
-/

namespace RealRooted
namespace Challenges
namespace ChudnovskySeymour

universe u

/-- Finite claw-free graph independence polynomials are real-rooted. -/
theorem clawFree_indepPoly_splits :
    RealRooted.Graph.ClawFreeIndepPolySplitsStatement.{u} :=
  RealRooted.Graph.clawFree_indepPoly_splits

end ChudnovskySeymour
end Challenges
end RealRooted
