/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.Tail
public import Mathlib.Basic.Real.Basic
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.FiniteMoment
import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.FiniteAtomicNorms

/-!
# Stieltjes fractions of finite positive atomic moments

Shifting moments multiplies the weight at a node by that node. For a finite
nonnegative support, this deletes only the origin. The two exact finite
Hankel ranks therefore differ by at most one, as required by the terminating
Euler–Gauss theorem.
-/

public section

open Polynomial

namespace PowerSeries

/-- Shifting finite nonnegative moments removes only the origin. -/
private theorem shifted_finset_moments (s : Finset ℝ) (w : ℝ → ℝ) :
    (fun k => ∑ x ∈ s, w x * x ^ (k + 1)) =
      (fun k => ∑ x ∈ s.erase 0, (w x * x) * x ^ k) := by
  classical
  funext k
  calc
    _ = ∑ x ∈ s, (w x * x) * x ^ k := by
      apply Finset.sum_congr rfl
      intro x _
      rw [pow_succ']
      ring
    _ = _ := by
      symm
      apply Finset.sum_subset (Finset.erase_subset _ _)
      intro x hxs hxt
      have hx : x = 0 := by
        by_contra hx
        exact hxt (Finset.mem_erase.mpr ⟨hx, hxs⟩)
      simp [hx]

/-- A nonempty finite positive support supplies the two terminating moment ranks. -/
private theorem finite_atomic_fraction_nonempty (s : Finset ℝ) (w : ℝ → ℝ)
    (hne : s.Nonempty) (hx : ∀ x ∈ s, 0 ≤ x) (hw : ∀ x ∈ s, 0 < w x) :
    ∃ a : ℕ → ℝ, (∀ k, 0 ≤ a k) ∧
      mk (fun k => ∑ x ∈ s, w x * x ^ k) =
        C (∑ x ∈ s, w x) * stieltjesTail a 0 := by
  classical
  let m : ℕ → ℝ := fun k => ∑ x ∈ s, w x * x ^ k
  let t := s.erase 0
  have hshift : (fun k => m (k + 1)) =
      (fun k => ∑ x ∈ t, (w x * x) * x ^ k) := shifted_finset_moments s w
  have hwshift (x : ℝ) (hxt : x ∈ t) : 0 < w x * x := by
    have hxs := (Finset.mem_erase.mp hxt).2
    have hxn := (Finset.mem_erase.mp hxt).1
    exact mul_pos (hw x hxs) (lt_of_le_of_ne (hx x hxs) (Ne.symm hxn))
  have hMN : t.card ≤ s.card := Finset.card_erase_le
  have hNM : s.card ≤ t.card + 1 := by
    by_cases hzero : 0 ∈ s
    · exact le_of_eq (Finset.card_erase_add_one hzero).symm
    · simp only [t, Finset.erase_eq_of_notMem hzero]
      lia
  have hpos (n : ℕ) (hn : n ≤ s.card) : (momentHankelMatrix m n).PosDef :=
    momentHankelMatrix_finset_sum_posDef s id w (Function.injective_id.injOn) hw n hn
  have hs (n : ℕ) (hn : n ≤ t.card) :
      (momentHankelMatrix (fun k => m (k + 1)) n).PosDef := by
    rw [hshift]
    exact momentHankelMatrix_finset_sum_posDef t id (fun x => w x * x)
      (Function.injective_id.injOn) hwshift n hn
  have hz (p : ℝ[X]) : momentPairing m p (monicMomentPolynomial m s.card) = 0 :=
    momentPairing_finset_sum_card_eq_zero s id w (Function.injective_id.injOn) hw p
  have hzshift (p : ℝ[X]) : momentPairing (fun k => m (k + 1)) p
      (monicMomentPolynomial (fun k => m (k + 1)) t.card) = 0 := by
    rw [hshift]
    exact momentPairing_finset_sum_card_eq_zero t id (fun x => w x * x)
      (Function.injective_id.injOn) hwshift p
  obtain ⟨_, a, ha, hstop, hf⟩ := exists_stieltjesTail_of_finite_hankel m s.card t.card
    hne.card_pos hMN hNM hpos hs hz hzshift
  refine ⟨a, ?_, ?_⟩
  · intro k
    rcases lt_or_ge k (s.card + t.card - 1) with hk | hk
    · exact (ha k hk).le
    · rw [hstop k hk]
  · simpa only [m, pow_zero, mul_one] using hf

/-- Every finite positive weighted set of nonnegative nodes has a nonnegative
formal Stieltjes fraction. Empty support and an atom at zero are included. -/
theorem exists_stieltjesTail_finset_moments (s : Finset ℝ) (w : ℝ → ℝ)
    (hx : ∀ x ∈ s, 0 ≤ x) (hw : ∀ x ∈ s, 0 < w x) :
    ∃ a : ℕ → ℝ, (∀ k, 0 ≤ a k) ∧
      mk (fun k => ∑ x ∈ s, w x * x ^ k) =
        C (∑ x ∈ s, w x) * stieltjesTail a 0 := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · refine ⟨fun _ => 0, fun _ => le_rfl, ?_⟩
    ext k
    simp only [Finset.sum_empty, map_zero, zero_mul, coeff_mk]
  · exact finite_atomic_fraction_nonempty s w hne hx hw

end PowerSeries
