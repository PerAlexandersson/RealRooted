module

import RealRooted.Mathlib.Data.List.Interleave
import RealRooted.ReciprocalShift.Interlacing
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.Data.NNRat.Floor
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Data.List.Interleave
import Mathlib.Tactic
public import Mathlib.Basic.Real.Basic

/-!
# Inversion and interleaving of reciprocal roots

This module transports interleaving lists of strictly negative real numbers
through reciprocal inversion and reversal. Zero-tail padding is deliberately a
separate layer.
-/

public section

namespace RealRooted

/-- Inversion and reversal swap two equally long interleaving lists of
strictly negative real numbers. -/
theorem interleaves_reverse_map_one_div_of_length_eq
    (A B : List ℝ) (hAneg : ∀ x ∈ A, x < 0) (hBneg : ∀ x ∈ B, x < 0)
    (hlen : A.length = B.length) (h : List.Interleaves (· ≤ ·) A B) :
    List.Interleaves (· ≤ ·) (B.reverse.map (fun x ↦ 1 / x))
      (A.reverse.map (fun x ↦ 1 / x)) := by
  have hmap : List.Interleaves (fun x y : ℝ ↦ y ≤ x)
      (A.map fun x ↦ 1 / x) (B.map fun x ↦ 1 / x) := by
    refine h.map_of_mem (fun x ↦ 1 / x) ?_
    intro a b ha hb hab
    have hbneg : b < 0 := by
      rcases hb with hb | hb
      · exact hAneg b hb
      · exact hBneg b hb
    exact one_div_antitone_of_nonpos hbneg hab
  have hlen' : (A.map fun x ↦ 1 / x).length = (B.map fun x ↦ 1 / x).length := by
    simpa using hlen
  have hreverse := (List.interleaves_reverse_reverse_of_length_eq_length
    (r := (· ≤ ·)) (l₁ := B.map fun x ↦ 1 / x) (l₂ := A.map fun x ↦ 1 / x)
    hlen'.symm).mpr hmap
  simpa only [Function.swap, List.map_reverse] using hreverse

/-- Inversion and reversal preserve the orientation of an interleaving when
the right-hand list has one additional strictly negative entry. -/
theorem interleaves_reverse_map_one_div_of_length_add_one_eq
    (A B : List ℝ) (hAneg : ∀ x ∈ A, x < 0) (hBneg : ∀ x ∈ B, x < 0)
    (hlen : A.length + 1 = B.length) (h : List.Interleaves (· ≤ ·) A B) :
    List.Interleaves (· ≤ ·) (A.reverse.map (fun x ↦ 1 / x))
      (B.reverse.map (fun x ↦ 1 / x)) := by
  have hmap : List.Interleaves (fun x y : ℝ ↦ y ≤ x)
      (A.map fun x ↦ 1 / x) (B.map fun x ↦ 1 / x) := by
    refine h.map_of_mem (fun x ↦ 1 / x) ?_
    intro a b ha hb hab
    have hbneg : b < 0 := by
      rcases hb with hb | hb
      · exact hAneg b hb
      · exact hBneg b hb
    exact one_div_antitone_of_nonpos hbneg hab
  have hlen' : (A.map fun x ↦ 1 / x).length + 1 =
      (B.map fun x ↦ 1 / x).length := by
    simpa using hlen
  have hreverse := (List.interleaves_reverse_reverse_of_length_eq_length_add_one
    (r := (· ≤ ·)) (l₁ := A.map fun x ↦ 1 / x) (l₂ := B.map fun x ↦ 1 / x)
    hlen').mpr hmap
  simpa only [Function.swap, List.map_reverse] using hreverse

end RealRooted
