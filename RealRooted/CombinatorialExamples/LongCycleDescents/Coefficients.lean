/-
Copyright (c) 2026 Bowen Zuo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bowen Zuo
-/
module

public import RealRooted.CombinatorialExamples.LongCycleDescents.DynamicProgramming
public import Mathlib.Basic.Real.Basic
import RealRooted.CombinatorialExamples.LongCycleDescents.Numerator
import Mathlib.Tactic

/-!
# Exact coefficient reconstruction from the positive necklace product

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

@[expose] public section

namespace RealRooted.LongCycleDescents.Necklace

open Polynomial Finset RealRooted.LongCycleDescents
open scoped Classical

/-- Cache all alphabet sizes needed by the degree-n numerator inversion. -/
def descentAlphabetTable (n k : ℕ) : Array ℕ :=
  Array.ofFn fun r : Fin n ↦ positiveCountDP n (r.val + 1) k

/-- Determine one coefficient from the cached positive counts. -/
def descentNumeratorCell (n r : ℕ) (letters : Array ℕ) : ℤ :=
  ((List.range (r + 1)).map fun a ↦
    (-1 : ℤ)^a * Nat.fast_choose (n + 1) a * letters.getD (r - a) 0).sum

/-- The exact integer numerator, in ascending order, with length n. -/
def descentRowDP (n k : ℕ) : List ℤ :=
  let letters := descentAlphabetTable n k
  List.ofFn fun r : Fin n ↦ descentNumeratorCell n r.val letters

private theorem alphabetTable_at {n r : ℕ} (h : r < n) (k : ℕ) :
    (descentAlphabetTable n k).getD r 0 = positiveCountDP n (r + 1) k := by
  unfold descentAlphabetTable
  let f (j : Fin n) := positiveCountDP n (j.val + 1) k
  change (Array.ofFn f).getD r 0 = _
  have hr : r < (Array.ofFn f).size := by simpa using h
  rw [Array.getD, dite_eq_left hr]
  change (Array.ofFn f)[r]'hr = _
  rw [Array.getElem_ofFn]

/-- Each reconstructed integer coefficient counts the original restricted permutations. -/
theorem descentNumeratorCell_correct {n r : ℕ} (hn : 0 < n) (hr : r < n) (k : ℕ) :
    descentNumeratorCell n r (descentAlphabetTable n k) =
      (descentPolynomial n k).coeff r := by
  unfold descentNumeratorCell
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  rw [coeff_descentPolynomial_from_necklaces hn hr k]
  apply sum_congr rfl
  intro a _
  have h : r - a < n := (Nat.sub_le r a).trans_lt hr
  rw [alphabetTable_at h, card_necklaceContent_eq_positiveCountDP, ← Nat.choose_eq_fast_choose]

private theorem row_coeff_zero_past {n r : ℕ} (hn : 0 < n) (hr : n ≤ r) (k : ℕ) :
    (descentPolynomial n k).coeff r = 0 := by
  rw [coeff_descentPolynomial]
  apply sum_eq_zero
  intro σ _
  apply ite_eq_right
  rintro ⟨_, eq⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have bound : σ.descentCount ≤ m := by
    rw [descents_eq_card]
    exact (card_filter_le _ _).trans_eq (by simp)
  lia

/-- Interpret an ascending coefficient list as a real polynomial. -/
noncomputable def coefficientPolynomial : List ℤ → Polynomial ℝ
  | [] => 0
  | a :: as => C (a : ℝ) + X * coefficientPolynomial as

/-- Reading a polynomial coefficient recovers the corresponding list entry, or zero past the end. -/
theorem coeff_coefficientPolynomial (cs : List ℤ) (j : ℕ) :
    (coefficientPolynomial cs).coeff j = (cs[j]?.getD 0 : ℤ) := by
  induction cs generalizing j with
  | nil => simp [coefficientPolynomial]
  | cons c cs ih =>
    cases j with
    | zero => simp [coefficientPolynomial]
    | succ j =>
      rw [coefficientPolynomial, coeff_add, coeff_C, ite_eq_right (Nat.succ_ne_zero j),
        coeff_X_mul, zero_add, ih]
      simp

/-- The DP list represents the real form of the original descent row. -/
theorem coefficientPolynomial_descentRowDP {n : ℕ} (hn : 0 < n) (k : ℕ) :
    coefficientPolynomial (descentRowDP n k) = (descentPolynomial n k).map (Int.castRingHom ℝ) := by
  ext r
  rw [coeff_coefficientPolynomial, coeff_map]
  by_cases hr : r < n
  · let f (i : Fin n) := descentNumeratorCell n i.val (descentAlphabetTable n k)
    change ((List.ofFn f)[r]?.getD 0 : ℝ) = _
    have hl : r < (List.ofFn f).length := by simpa using hr
    rw [List.getElem?_eq_getElem hl, List.getElem_ofFn]
    change (descentNumeratorCell n r (descentAlphabetTable n k) : ℝ) = _
    rw [descentNumeratorCell_correct hn hr]
    rfl
  · have hl : (descentRowDP n k).length ≤ r := by simpa [descentRowDP] using Nat.le_of_not_gt hr
    rw [List.getElem?_eq_none hl, row_coeff_zero_past hn (Nat.le_of_not_gt hr)]
    simp

private theorem coefficientPolynomial_append_zero (cs : List ℤ) : coefficientPolynomial (cs ++
  [0]) = coefficientPolynomial cs := by
  induction cs with
  | nil => simp [coefficientPolynomial]
  | cons a tail ih => simp [coefficientPolynomial, ih]

/-- A checked coefficient list reads the original real row as X times its quotient. -/
theorem row_eq_of_checkedCoeffs {n k : ℕ} (hn : 0 < n) {cs : List ℤ}
    (checked : descentRowDP n k = (0 :: cs) ++ [0]) :
    (descentPolynomial n k).map (Int.castRingHom ℝ) = X * coefficientPolynomial cs := by
  rw [← coefficientPolynomial_descentRowDP hn k, checked, coefficientPolynomial_append_zero]
  simp [coefficientPolynomial]

end RealRooted.LongCycleDescents.Necklace
