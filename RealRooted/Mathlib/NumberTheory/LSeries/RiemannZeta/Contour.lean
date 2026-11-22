/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import Mathlib.NumberTheory.LSeries.ZetaZeros
public import Mathlib.Analysis.Analytic.Order
public import TauCeti.Analysis.Complex.Rectangle
import RealRooted.Mathlib.Analysis.Contour.Residue.Rectangle
import RealRooted.Mathlib.NumberTheory.LSeries.RiemannZeta.Residues
import TauCeti.NumberTheory.LSeries.CompletedRiemannZeta
import TauCeti.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Normed.Module.Convex

/-!
# A weighted contour formula for the zeros of zeta

On a rectangle containing `1` in its interior and with no zeta zeros on its
boundary, the integral of `-ζ'/ζ` times an analytic weight equals the weight
at `1` minus the weighted sum of the zero multiplicities. Only a neighborhood
of the rectangle is required for the weight. The identity is unconditional.
-/

public section

open Complex Set Metric
open scoped Real

namespace TauCeti.Contour

open scoped Classical in
/-- The four boundary integrals of an analytically weighted negative logarithmic
derivative of zeta count the enclosed zeros with their full multiplicities. -/
theorem integral_boundary_rect_neg_logDeriv_riemannZeta {g : ℂ → ℂ} {z w : ℂ}
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (h1 : (1 : ℂ) ∈ interior (Rectangle z w))
    (hg : AnalyticOnNhd ℂ g (Rectangle z w))
    (hbd : ∀ s ∈ frontier (Rectangle z w), riemannZeta s ≠ 0) :
    let f := fun s ↦ -logDeriv riemannZeta s * g s
    (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) -
        (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
        I * (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) -
        I * (∫ y : ℝ in z.im..w.im, f (z.re + y * I)) =
      2 * π * I * (g 1 -
        ∑ s ∈ (isCompact_rectangle z w).inter_riemannZetaZeros_finite.toFinset,
          (analyticOrderNatAt riemannZeta s : ℂ) * g s) := by
  classical
  dsimp only
  let R := Rectangle z w
  have hR : IsCompact R := isCompact_rectangle z w
  obtain ⟨δ, hδ, hδg⟩ := hR.exists_cthickening_subset_open (isOpen_analyticAt ℂ g) hg
  let K := cthickening δ R
  let U := thickening δ R
  let Z := (hR.cthickening (r := δ)).inter_riemannZetaZeros_finite.toFinset
  have hUK : U ⊆ K := thickening_subset_cthickening δ R
  have hRU : R ⊆ U := self_subset_thickening hδ R
  have h1R : (1 : ℂ) ∈ R := interior_subset h1
  have h1bd : (1 : ℂ) ∉ frontier R := disjoint_left.mp disjoint_interior_frontier h1
  have hZ (s : ℂ) : s ∈ Z ↔ s ∈ K ∧ riemannZeta s = 0 := by
    simp only [Z, Finite.mem_toFinset, mem_inter_iff, mem_riemannZetaZeros]
    rfl
  have h1Z : (1 : ℂ) ∉ Z := fun h ↦ riemannZeta_one_ne_zero ((hZ 1).mp h).2
  have hoff : DifferentiableOn ℂ (fun s ↦ -logDeriv riemannZeta s * g s)
      (U \ (↑(insert 1 Z) : Set ℂ)) := by
    intro s hs
    have hs1 : s ≠ 1 := fun h ↦ hs.2 (by simp [h])
    have hsζ : riemannZeta s ≠ 0 := fun h ↦
      hs.2 (Finset.mem_insert_of_mem ((hZ s).mpr ⟨hUK hs.1, h⟩))
    exact (((analyticOn_riemannZeta s hs1).logDeriv hsζ).neg.mul
      (hδg (hUK hs.1))).differentiableAt.differentiableWithinAt
  have hmero (s : ℂ) (_ : s ∈ insert 1 Z) (hs : s ∈ U) :
      MeromorphicAt (fun s ↦ -logDeriv riemannZeta s * g s) s :=
    ((meromorphic_riemannZeta s).deriv.div (meromorphic_riemannZeta s)).neg.mul
      (hδg (hUK hs)).meromorphicAt
  have hS (s : ℂ) (hs : s ∈ insert 1 Z) : s ∉ frontier R := by
    rcases Finset.mem_insert.mp hs with rfl | hs
    · exact h1bd
    · exact fun h ↦ hbd s h ((hZ s).mp hs).2
  rw [integral_boundary_rect_eq_sum_residues hre him isOpen_thickening hRU hoff hmero hS]
  congr 1
  rw [Finset.filter_insert, ite_eq_left h1R, Finset.sum_insert
    (fun h ↦ h1Z (Finset.mem_filter.mp h).1),
    residue_neg_logDeriv_riemannZeta_mul_one (hg 1 h1R)]
  have hfilter : Z.filter (· ∈ R) = hR.inter_riemannZetaZeros_finite.toFinset := by
    ext s
    simp only [Finset.mem_filter, hZ, Finite.mem_toFinset, mem_inter_iff,
      mem_riemannZetaZeros]
    exact ⟨fun h ↦ ⟨h.2, h.1.2⟩, fun h ↦ ⟨⟨hUK (hRU h.1), h.2⟩, h.1⟩⟩
  rw [hfilter, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  have hs' := hR.inter_riemannZetaZeros_finite.mem_toFinset.mp hs
  have hs1 : s ≠ 1 := fun h ↦ riemannZeta_one_ne_zero (h ▸ hs'.2)
  rw [residue_neg_logDeriv_riemannZeta_mul hs1 (hg s hs'.1), neg_mul]

end TauCeti.Contour
