module

public import RealRooted.HeilmannLieb
import RealRooted.Graph.IndependencePolynomial.ClawFree
public import RealRooted.Graph.IndependencePolynomial.Basic
public import RealRooted.Graph.ClawFree

public section

open Polynomial

/-!
# Chudnovsky--Seymour challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "chudnovsky-seymour"
formalized = "2026-07-09"
references = [
  "ChudnovskySeymour2007",
]
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
headline = true

[[theorems]]
name = "RealRooted.Graph.clawFree_weightedIndepPoly_splits"
module = "RealRooted.Graph.IndependencePolynomial.ClawFree"
label = "Weighted independence polynomials of claw-free graphs are real-rooted"
-->

<!-- realrooted-catalog-content -->
# Claw-free independence polynomials

The independence polynomial counts independent vertex sets by cardinality.
Chudnovsky and Seymour proved that it is real-rooted for every finite
claw-free graph [@ChudnovskySeymour2007].

The same holds for the weighted independence polynomial
$\sum_A x^{|A|}\prod_{v\in A}w(v)$ when all $w(v)\ge0$ (Engström; see the
[Heilmann–Lieb page](/RealRooted/theorems/heilmann-lieb/)).

## References

See [@ChudnovskySeymour2007] and the
[graph-polynomial context on symmetricfunctions.com](sf:clawFreeGraph).
<!-- /realrooted-catalog-content -->

Human statement:
sf:clawFreeGraph

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
theorem clawFree_indepPoly_splits {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) (hG : RealRooted.Graph.ClawFree G) :
    (RealRooted.Graph.indepPoly G).Splits :=
  RealRooted.Graph.clawFree_indepPoly_splits G hG

end ChudnovskySeymour
end Challenges
end RealRooted
