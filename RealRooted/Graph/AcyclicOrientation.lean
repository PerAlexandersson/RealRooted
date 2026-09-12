import Mathlib.Combinatorics.Digraph.Orientation
import Mathlib.Data.Fintype.Order
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Real.Basic

/-!
# Acyclic orientations and sink polynomials

This file supplies a finite relation model for orientations of a simple graph.
An orientation chooses exactly one direction on every edge.  We call it
acyclic when its directed relation admits a strictly increasing rank function;
for a finite relation this is the usual topological-order characterization.
-/

open Finset Polynomial

noncomputable section

namespace RealRooted
namespace Graph

universe u

/-- A Boolean direction choice with exactly one direction on every edge and
no direction on a nonedge. -/
structure Orientation {V : Type u} (G : _root_.SimpleGraph V) where
  dir : V → V → Bool
  dir_ne_of_adj : ∀ ⦃u v⦄, G.Adj u v → dir u v ≠ dir v u
  dir_eq_false_of_not_adj : ∀ ⦃u v⦄, ¬G.Adj u v → dir u v = false

instance {V : Type u} [Finite V] (G : _root_.SimpleGraph V) :
    Finite (Orientation G) :=
  Finite.of_injective (fun O : Orientation G ↦ O.dir) (by
    intro O P h
    cases O
    cases P
    simp_all)

namespace Orientation

variable {V : Type u} {G : _root_.SimpleGraph V}

/-- The directed edge relation selected by an orientation. -/
def Directed (O : Orientation G) (u v : V) : Prop :=
  O.dir u v = true

instance (O : Orientation G) : DecidableRel O.Directed :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ = true))

lemma directed_of_adj_iff_not_directed_reverse
    (O : Orientation G) {u v : V} (huv : G.Adj u v) :
    O.Directed u v ↔ ¬O.Directed v u := by
  have hne := O.dir_ne_of_adj huv
  simp only [Directed]
  cases huv_dir : O.dir u v <;> cases hvu_dir : O.dir v u <;> simp_all

lemma directed_adj (O : Orientation G) {u v : V} (huv : O.Directed u v) :
    G.Adj u v := by
  by_contra hnot
  have := O.dir_eq_false_of_not_adj hnot
  simp [Directed, this] at huv

lemma not_directed_self (O : Orientation G) (v : V) : ¬O.Directed v v := by
  intro hv
  exact (G.ne_of_adj (O.directed_adj hv)) rfl

/-- A finite orientation is acyclic when its directed relation has a
topological ranking. -/
def IsAcyclic (O : Orientation G) : Prop :=
  ∃ rank : V → ℕ, ∀ ⦃u v⦄, O.Directed u v → rank u < rank v

/-- A vertex is a sink when it has no outgoing directed edge. -/
def IsSink (O : Orientation G) (v : V) : Prop :=
  ∀ w, ¬O.Directed v w

variable [Fintype V] [DecidableEq V]

/-- Number of sinks in a finite orientation. -/
def sinkCount (O : Orientation G) : ℕ := by
  classical
  exact (Finset.univ.filter O.IsSink).card

variable [LinearOrder V]

/-- Number of naturally labelled ascents in a finite orientation. -/
def ascentCount (O : Orientation G) : ℕ :=
  ((Finset.univ ×ˢ Finset.univ).filter fun e : V × V =>
    e.1 < e.2 ∧ O.Directed e.1 e.2).card

end Orientation

section Polynomial

variable {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]

/-- The natural-order ascent-refined acyclic-orientation sink polynomial. -/
def acyclicSinkPolynomial (G : _root_.SimpleGraph V) (q : ℝ) : ℝ[X] := by
  classical
  letI : Fintype (Orientation G) := Fintype.ofFinite (Orientation G)
  exact ∑ O : Orientation G,
    if O.IsAcyclic then C (q ^ O.ascentCount) * X ^ O.sinkCount else 0

end Polynomial

end Graph
end RealRooted
