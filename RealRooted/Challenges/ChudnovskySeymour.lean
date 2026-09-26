import RealRooted.HeilmannLieb

open Polynomial

/-!
# Chudnovsky--Seymour challenge entry point

<!-- realrooted-catalog
version = 1
section = "theorems"
slug = "chudnovsky-seymour"

[[definitions]]
name = "RealRooted.Challenges.ChudnovskySeymour.ClawFreeGraph"

[[definitions]]
name = "RealRooted.Challenges.ChudnovskySeymour.IndependencePolynomial"

[[theorems]]
name = "RealRooted.Challenges.ChudnovskySeymour.clawFree_indepPoly_splits"
-->

<!-- realrooted-catalog-content -->
# Claw-free independence polynomials

The independence polynomial records independent vertex sets by cardinality.
The Chudnovsky–Seymour theorem states that the independence polynomial of
every finite claw-free graph has only real roots.  The selected Lean theorem
uses the repository’s finite-graph definitions and proves real splitting
directly for the resulting polynomial.

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

This challenge-facing module exposes the graph-form Chudnovsky--Seymour theorem:
finite claw-free graphs have real-rooted independence polynomials.
-/

namespace RealRooted
namespace Challenges
namespace ChudnovskySeymour

universe u

/-- Challenge-facing name for claw-free finite graphs. -/
abbrev ClawFreeGraph {V : Type u} (G : _root_.SimpleGraph V) : Prop :=
  RealRooted.Graph.ClawFree G

/-- Challenge-facing name for the independence polynomial. -/
noncomputable abbrev IndependencePolynomial
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : _root_.SimpleGraph V) : ℝ[X] :=
  RealRooted.Graph.indepPoly G

/-- Finite claw-free graph independence polynomials are real-rooted. -/
theorem clawFree_indepPoly_splits :
    ∀ {V : Type u} [Fintype V] [DecidableEq V]
      (G : _root_.SimpleGraph V),
      ClawFreeGraph G → (IndependencePolynomial G).Splits :=
  RealRooted.Graph.clawFree_indepPoly_splits

end ChudnovskySeymour
end Challenges
end RealRooted
