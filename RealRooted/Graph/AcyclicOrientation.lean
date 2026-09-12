import Mathlib.Combinatorics.Digraph.Orientation
import Mathlib.Data.Fintype.Order
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.BigOperators.Fin
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

@[ext]
theorem ext {O P : Orientation G} (hdir : O.dir = P.dir) : O = P := by
  cases O
  cases P
  simp_all

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

/-- Restrict an orientation along an adjacency-reflecting map. -/
def comap {W : Type*} {H : _root_.SimpleGraph W}
    (O : Orientation G) (f : W → V)
    (hadj : ∀ u v, H.Adj u v ↔ G.Adj (f u) (f v)) :
    Orientation H where
  dir u v := O.dir (f u) (f v)
  dir_ne_of_adj := by
    intro u v huv
    exact O.dir_ne_of_adj ((hadj u v).mp huv)
  dir_eq_false_of_not_adj := by
    intro u v huv
    apply O.dir_eq_false_of_not_adj
    exact fun h ↦ huv ((hadj u v).mpr h)

@[simp]
theorem comap_directed {W : Type*} {H : _root_.SimpleGraph W}
    (O : Orientation G) (f : W → V)
    (hadj : ∀ u v, H.Adj u v ↔ G.Adj (f u) (f v))
    (u v : W) :
    (O.comap f hadj).Directed u v ↔ O.Directed (f u) (f v) :=
  Iff.rfl

/-- A finite orientation is acyclic when its directed relation has a
topological ranking. -/
def IsAcyclic (O : Orientation G) : Prop :=
  ∃ rank : V → ℕ, ∀ ⦃u v⦄, O.Directed u v → rank u < rank v

theorem IsAcyclic.comap {W : Type*} {H : _root_.SimpleGraph W}
    {O : Orientation G} (hO : O.IsAcyclic) (f : W → V)
    (hadj : ∀ u v, H.Adj u v ↔ G.Adj (f u) (f v)) :
    (O.comap f hadj).IsAcyclic := by
  obtain ⟨rank, hrank⟩ := hO
  refine ⟨rank ∘ f, ?_⟩
  intro u v huv
  exact hrank huv

/-- Acyclic orientations as a finite subtype. -/
def AcyclicOrientation (G : _root_.SimpleGraph V) :=
  {O : Orientation G // O.IsAcyclic}

instance [Finite V] : Finite (AcyclicOrientation G) :=
  inferInstanceAs (Finite {O : Orientation G // O.IsAcyclic})

noncomputable instance [Finite V] : Fintype (AcyclicOrientation G) :=
  Fintype.ofFinite (AcyclicOrientation G)

/-- A chosen topological rank for a finite acyclic orientation. -/
noncomputable def AcyclicOrientation.topologicalRank
    (O : AcyclicOrientation G) : V → ℕ := by
  exact Classical.choose O.2

theorem AcyclicOrientation.directed_topologicalRank_lt
    (O : AcyclicOrientation G) {u v : V} (huv : O.1.Directed u v) :
    O.topologicalRank u < O.topologicalRank v :=
  Classical.choose_spec O.2 huv

/-- A vertex is a sink when it has no outgoing directed edge. -/
def IsSink (O : Orientation G) (v : V) : Prop :=
  ∀ w, ¬O.Directed v w

variable [Fintype V] [DecidableEq V]

/-- The finite set of sinks of an orientation. -/
def sinks (O : Orientation G) : Finset V := by
  classical
  exact Finset.univ.filter O.IsSink

omit [DecidableEq V] in
@[simp] theorem mem_sinks (O : Orientation G) (v : V) :
    v ∈ O.sinks ↔ O.IsSink v := by
  classical
  simp [sinks]

/-- Number of sinks in a finite orientation. -/
def sinkCount (O : Orientation G) : ℕ :=
  O.sinks.card

variable [LinearOrder V]

/-- Number of naturally labelled ascents in a finite orientation. -/
def ascentCount (O : Orientation G) : ℕ :=
  ∑ v : V, (Finset.univ.filter fun u : V =>
    u < v ∧ O.Directed u v).card

end Orientation

section Polynomial

variable {V : Type u} {G : _root_.SimpleGraph V}
  [Fintype V] [DecidableEq V] [LinearOrder V]

/-- The ascent- and sink-weighted monomial of one orientation. -/
def orientationMonomial (q : ℝ) (O : Orientation G) : ℝ[X] :=
  C (q ^ O.ascentCount) * X ^ O.sinkCount

/-- The natural-order ascent-refined acyclic-orientation sink polynomial. -/
def acyclicSinkPolynomial (G : _root_.SimpleGraph V) (q : ℝ) : ℝ[X] := by
  classical
  exact ∑ O : Orientation.AcyclicOrientation G,
    orientationMonomial q O.1

end Polynomial

end Graph
end RealRooted
