module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Basic.Real.Basic

@[expose] public noncomputable section

open Polynomial

namespace RealRooted

/-- A matrix of polynomials acts on a sequence by matrix-vector multiplication. -/
def matPolyAction (G : List (List ℝ[X])) (fs : List ℝ[X]) : List ℝ[X] :=
  G.map (fun row => (row.zipWith (· * ·) fs).sum)

@[simp] lemma length_matPolyAction (G : List (List ℝ[X])) (fs : List ℝ[X]) :
    (matPolyAction G fs).length = G.length := by
  simp [matPolyAction]

end RealRooted
