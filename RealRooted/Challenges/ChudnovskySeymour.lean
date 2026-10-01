import RealRooted.HeilmannLieb

open Polynomial

/-!
# Chudnovsky--Seymour challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "chudnovsky-seymour"
authors = ["Chudnovsky", "Seymour"]
years = [2007]

[[definitions]]
name = "RealRooted.Graph.ClawFree"
module = "RealRooted.Graph.ClawFree"
label = "Claw-free graph"

[[definitions]]
name = "RealRooted.Graph.indepPoly"
module = "RealRooted.Graph.IndependencePolynomial.Basic"
label = "Independence polynomial"

[[theorems]]
name = "RealRooted.Challenges.ChudnovskySeymour.clawFree_indepPoly_splits"
label = "Chudnovsky–Seymour: claw-free graphs have real-rooted independence polynomials"
-->

<!-- realrooted-catalog-content -->
# Claw-free independence polynomials

The independence polynomial counts independent vertex sets by cardinality.
Chudnovsky and Seymour proved that it is real-rooted for every finite
claw-free graph.

## References

M. Chudnovsky and P. Seymour, “The roots of the independence polynomial of a
clawfree graph,” *Journal of Combinatorial Theory, Series B* 97 (2007),
350–357.  See also the
[graph-polynomial context on symmetricfunctions.com](https://www.symmetricfunctions.com/realRootedGraphs.htm#clawFreeGraph).
<!-- /realrooted-catalog-content -->

Human statement:
https://www.symmetricfunctions.com/realRootedGraphs.htm#clawFreeGraph

Original publication: M. Chudnovsky and P. Seymour, "The roots of the
independence polynomial of a clawfree graph", J. Combin. Theory Ser. B 97
(2007), 350--357.

This module states the Chudnovsky--Seymour theorem for finite graphs.
-/

namespace RealRooted
namespace Challenges
namespace ChudnovskySeymour

universe u

/-- Finite claw-free graph independence polynomials are real-rooted. -/
theorem clawFree_indepPoly_splits :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : _root_.SimpleGraph V),
      RealRooted.Graph.ClawFree G → (RealRooted.Graph.indepPoly G).Splits :=
  RealRooted.Graph.clawFree_indepPoly_splits

end ChudnovskySeymour
end Challenges
end RealRooted
