/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import TauCeti.Analysis.Contour.Residue.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import TauCeti.Analysis.Contour.Residue.Cycle
import TauCeti.Analysis.Contour.Curve.Rectangle
import TauCeti.Analysis.Contour.Winding.Number.Rectangle

/-!
# The residue theorem on a rectangle

The signed sum of the four edge integrals equals the sum of the interior
residues. The exceptional finite set may include points outside the rectangle;
these do not contribute. This specializes Tau Ceti's residue theorem for
null-homologous cycles using its winding-number calculation for rectangles.
-/

public section

open Complex Set
open scoped Real

namespace TauCeti.Contour

open scoped Classical in
/-- The residue theorem for a rectangle, written as four real interval integrals.
The lower left and upper right corners are `z` and `w`. -/
theorem integral_boundary_rect_eq_sum_residues {f : ℂ → ℂ} {S : Finset ℂ}
    {U : Set ℂ} {z w : ℂ} (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hU : IsOpen U) (hRU : Rectangle z w ⊆ U)
    (hf : DifferentiableOn ℂ f (U \ (↑S : Set ℂ)))
    (hmero : ∀ s ∈ S, s ∈ U → MeromorphicAt f s)
    (hS : ∀ s ∈ S, s ∉ frontier (Rectangle z w)) :
    (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) -
        (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
        I * (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) -
        I * (∫ y : ℝ in z.im..w.im, f (z.re + y * I)) =
      2 * π * I * ∑ s ∈ S with s ∈ Rectangle z w, residue f s := by
  classical
  have hfr : frontier (Rectangle z w) ⊆ U \ (↑S : Set ℂ) := by
    intro s hs
    exact ⟨hRU ((isClosed_rectangle z w).frontier_subset hs), fun h ↦ hS s h hs⟩
  have hcont : ContinuousOn f (frontier (Rectangle z w)) :=
    hf.continuousOn.mono hfr
  rw [← smul_eq_mul I, ← smul_eq_mul I, ← integral_rectBoundary hcont,
    classicalResidueTheorem_nullHomologous hU hf hmero
      (isPiecewiseC1On_rectBoundary z w) (fun t _ ↦ hRU (rectBoundary_mem_rectangle t))
      (by simp) (fun t _ h ↦ hS _ h (rectBoundary_mem_frontier t))
      (isNullHomologous_rectBoundary hRU), Finset.sum_filter]
  refine congrArg _ (Finset.sum_congr rfl fun s hs ↦ ?_)
  by_cases hmem : s ∈ Rectangle z w
  · rw [ite_eq_left hmem, windingNumber_rectBoundary_eq_one
      (mem_Ioo_reProdIm_of_mem_rectangle hre him hmem (hS s hs)), one_mul]
  · rw [ite_eq_right hmem, windingNumber_rectBoundary_eq_zero hmem, zero_mul]

end TauCeti.Contour
