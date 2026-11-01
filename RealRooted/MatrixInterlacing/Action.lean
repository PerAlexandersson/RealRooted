module

import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Mul

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted

/-- A matrix of polynomials acts on a sequence by matrix-vector multiplication. -/
def matPolyAction (G : List (List ℝ[X])) (fs : List ℝ[X]) : List ℝ[X] :=
  G.map (fun row => (row.zipWith (· * ·) fs).sum)

@[simp] lemma length_matPolyAction (G : List (List ℝ[X])) (fs : List ℝ[X]) :
    (matPolyAction G fs).length = G.length := by
  simp [matPolyAction]

/-- The row-major list action agrees with matrix-vector multiplication. -/
theorem matPolyAction_ofFn {m n : ℕ} (G : Matrix (Fin m) (Fin n) ℝ[X])
    (fs : Fin n → ℝ[X]) :
    matPolyAction (List.ofFn fun i ↦ List.ofFn fun j ↦ G i j) (List.ofFn fs) =
      List.ofFn (G.mulVec fs) := by
  have hzip : ∀ (k : ℕ) (f g : Fin k → ℝ[X]),
      (List.ofFn f).zipWith (· * ·) (List.ofFn g) =
        List.ofFn fun i ↦ f i * g i := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro f g
      rw [List.ofFn_succ' f, List.ofFn_succ' g, List.ofFn_succ']
      simp only [List.concat_eq_append]
      rw [List.zipWith_append (by simp)]
      simp [ih]
  simp only [matPolyAction, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  change
    ((List.ofFn fun j ↦ G i j).zipWith (· * ·) (List.ofFn fs)).sum =
      G.mulVec fs i
  rw [hzip]
  simp only [List.sum_ofFn, Matrix.mulVec, dotProduct]

end RealRooted
