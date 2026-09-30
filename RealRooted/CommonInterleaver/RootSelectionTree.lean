import RealRooted.CommonInterleaver.RootSelection

/-!
# Finite interlacing-family trees

This file packages the finite rooted-tree form of MSS root selection. Leaves
are polynomial labels; every internal node is the sum of a nonempty list of
children whose node polynomials have a common degree-gap left interlacer.
-/

open Polynomial

noncomputable section

namespace RealRooted

open LiuOppositeSigns

/-- A finite rose tree with polynomial-labelled leaves. -/
inductive RootSelectionTree where
  | leaf (p : ℝ[X])
  | node (children : List RootSelectionTree)

namespace RootSelectionTree

/-- The polynomial at a node: a leaf label, or the sum of its child
polynomials. -/
def polynomial : RootSelectionTree → ℝ[X]
  | leaf p => p
  | node children => (children.map polynomial).sum

/-- The leaf labels below a node, in depth-first left-to-right order. -/
def leaves : RootSelectionTree → List ℝ[X]
  | leaf p => [p]
  | node children => (children.map leaves).flatten

/-- Validity data for a degree-`d` interlacing-family tree. Leaf splitting is
explicit, and an internal node must have at least one child. -/
inductive Valid (d : ℕ) : RootSelectionTree → Prop
  | leaf {p : ℝ[X]}
      (hdeg : p.natDegree = d) (hsplits : p.Splits)
      (hpos : HasPosLeadingCoeff p) :
      Valid d (.leaf p)
  | node {children : List RootSelectionTree}
      (hne : children ≠ [])
      (hchildren : ∀ child ∈ children, Valid d child)
      (hcommon : HasCommonLeftInterlacerOfDegree
        (children.map polynomial) d) :
      Valid d (.node children)

end RootSelectionTree

end RealRooted
