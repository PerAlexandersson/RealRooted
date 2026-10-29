/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

import RealRooted.Laguerre.Roots
public import RealRooted.SimpleRoots
public import RealRooted.Mathlib.RingTheory.Polynomial.Laguerre.Differential

import RealRooted.MaWang.StrictStep
import RealRooted.QuadraticInterlacingClosure
import RealRooted.CommonInterleaver.RightPencil
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Finite combinations of monic Laguerre polynomials

This file proves the bandwidth-one case of Durán's criterion for finite
combinations of consecutive monic Laguerre polynomials.  The auxiliary
polynomial is `X - C γ`; its unique root is `γ`, so the criterion is the
sharp inequality `γ < α + 1`.

The normalization is the monic classical polynomial
`(-1)^n n! L_n^(α)(X)`.  It is obtained from the library's sign-reversed
normalization by reflection at the origin.

Reference: A. J. Durán, *Zeros of linear combinations of Laguerre
polynomials*, Theorem 1.3, arXiv:2507.22425.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace Polynomial

universe u

variable {R : Type u} [CommRing R]

/-- The classical monic generalized Laguerre polynomial
`(-1)^n n! L_n^(α)(X)`. -/
noncomputable def monicLaguerre (n : ℕ) (α : R) : R[X] :=
  C ((-1 : R) ^ n) * (generalizedLaguerre n α).comp (-X)

/-- The zeroth classical monic Laguerre polynomial is one. -/
@[simp] theorem monicLaguerre_zero (α : R) :
    monicLaguerre 0 α = 1 := by
  simp [monicLaguerre]

/-- The first classical monic Laguerre polynomial is `X - (α + 1)`. -/
@[simp] theorem monicLaguerre_one (α : R) :
    monicLaguerre 1 α = X - C (α + 1) := by
  simp [monicLaguerre]
  ring

/-- The degree-one auxiliary polynomial in Durán's criterion. -/
noncomputable def laguerreAuxiliaryOne (γ : R) : R[X] :=
  X - C γ

/-- The degree-one Durán auxiliary polynomial has the unique root `γ`. -/
@[simp] theorem laguerreAuxiliaryOne_isRoot_iff [IsDomain R] (γ x : R) :
    (laguerreAuxiliaryOne γ).IsRoot x ↔ x = γ := by
  simp only [laguerreAuxiliaryOne, IsRoot.def, eval_sub, eval_X, eval_C]
  exact sub_eq_zero

/-- A combination of two consecutive classical monic Laguerre polynomials,
the `K = 1` family in Durán's Theorem 1.3. -/
noncomputable def laguerreCombinationOne (n : ℕ) (α γ : R) : R[X] :=
  monicLaguerre n α + C γ * monicLaguerre (n - 1) α

end Polynomial

namespace RealRooted

/-- The sign-reversed bandwidth-one combination is one Laguerre raising step. -/
theorem generalizedLaguerre_sub_prev_eq_raisingStep
    {n : ℕ} (hn : 1 ≤ n) (α γ : ℝ) :
    generalizedLaguerre n α - C γ * generalizedLaguerre (n - 1) α =
      laguerreRaisingStep ((n : ℝ) + α - γ)
        (generalizedLaguerre (n - 1) α) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  simp only [Nat.one_add, Nat.succ_sub_one]
  rw [generalizedLaguerre_succ]
  simp only [laguerreRaisingStep]
  norm_num only [Nat.cast_succ]
  simp only [map_add, map_sub]
  ring

/-- Reflection identifies the classical bandwidth-one combination with the
sign-reversed difference used in the proof. -/
theorem laguerreCombinationOne_comp_neg_X
    {n : ℕ} (hn : 1 ≤ n) (α γ : ℝ) :
    (laguerreCombinationOne n α γ).comp (-X) =
      C ((-1 : ℝ) ^ n) *
        (generalizedLaguerre n α -
          C γ * generalizedLaguerre (n - 1) α) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  simp only [Nat.one_add, Nat.succ_sub_one, laguerreCombinationOne,
    monicLaguerre, add_comp, mul_comp, C_comp,
    comp_neg_X_comp_neg_X, pow_succ]
  rw [C_mul, C_neg]
  norm_num
  ring

private theorem hasNonnegCoeffs_laguerreRaisingStep
    {a : ℝ} (ha : 0 ≤ a) {p : ℝ[X]} (hp : HasNonnegCoeffs p) :
    HasNonnegCoeffs (laguerreRaisingStep a p) := by
  intro k
  rw [coeff_laguerreRaisingStep]
  split_ifs with hk
  · subst k
    simpa using mul_nonneg ha (hp 0)
  · exact add_nonneg (hp (k - 1))
      (mul_nonneg (by positivity) (hp k))

/-- Durán's bandwidth-one criterion in the sign-reversed normalization:
the combination has simple negative roots and strictly interlaces the
preceding Laguerre polynomial. -/
theorem generalizedLaguerre_sub_prev_strict_package
    {n : ℕ} (hn : 2 ≤ n) {α γ : ℝ} (hα : -1 < α)
    (hγ : γ < α + 1) :
    let F := generalizedLaguerre n α -
      C γ * generalizedLaguerre (n - 1) α
    StrictInterl (generalizedLaguerre (n - 1) α) F ∧
      HasSimpleRoots F ∧ ∀ r ∈ F.roots, r < 0 := by
  dsimp
  let p := generalizedLaguerre (n - 1) α
  let a := (n : ℝ) + α - γ
  have hn1 : 1 ≤ n := by lia
  have hpdeg : p.natDegree = n - 1 := by simp [p]
  have hpdegpos : 1 ≤ p.natDegree := by rw [hpdeg]; lia
  have ha : 0 < a := by
    dsimp [a]
    have hncast : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hstep := generalizedLaguerre_sub_prev_eq_raisingStep hn1 α γ
  let F := generalizedLaguerre n α - C γ * generalizedLaguerre (n - 1) α
  have hFdegree_le : F.natDegree ≤ n := by
    dsimp [F]
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · simp
    · exact (natDegree_C_mul_le γ _).trans (by simp)
  have hFcoeff : F.coeff n = 1 := by
    dsimp [F]
    rw [coeff_sub, coeff_C_mul, coeff_generalizedLaguerre,
      ite_eq_left le_rfl, coeff_generalizedLaguerre,
      ite_eq_right (by lia : ¬n ≤ n - 1)]
    simp
  have hFmonic : F.Monic :=
    monic_of_natDegree_le_of_coeff_eq_one n hFdegree_le hFcoeff
  have hFdegree : F.natDegree = n :=
    natDegree_eq_of_le_of_coeff_ne_zero hFdegree_le (by simp [hFcoeff])
  have hmonic : (laguerreRaisingStep a p).Monic := by
    rw [← hstep]
    exact hFmonic
  have hdegree : (laguerreRaisingStep a p).natDegree = p.natDegree + 1 := by
    rw [← hstep, hFdegree, hpdeg]
    lia
  have hpair := strictInterl_and_hasSimpleRoots_of_interlaces_eval_mul_neg_succ
    (generalizedLaguerre_splits (n - 1) hα.le)
    (hasPosLeadingCoeff_of_monic (monic_generalizedLaguerre (n - 1) α))
    (hasPosLeadingCoeff_of_monic hmonic) hpdegpos hdegree
    (generalizedLaguerre_hasSimpleRoots (n - 1) hα.le)
    (u := X + C a) (v := X) (by simp [laguerreRaisingStep]; ring)
    (by
      intro r hr
      simpa using generalizedLaguerre_roots_neg (n - 1) hα r
        ((Polynomial.mem_roots
          (monic_generalizedLaguerre (n - 1) α).ne_zero).mpr hr))
  rw [hstep]
  refine ⟨hpair.1, hpair.2, ?_⟩
  apply roots_neg_of_hasNonnegCoeffs_of_coeff_zero_ne
    (hasNonnegCoeffs_laguerreRaisingStep ha.le
      (generalizedLaguerre_hasNonnegCoeffs (n - 1) hα.le))
  have hp0 : p.coeff 0 ≠ 0 := by
    dsimp [p]
    rw [coeff_zero_eq_eval_zero, generalizedLaguerre_eval_zero]
    exact (ascPochhammer_pos (n - 1) (α + 1) (by linarith)).ne'
  rw [coeff_laguerreRaisingStep]
  norm_num
  exact ⟨ha.ne', hp0⟩

/-- Durán's Theorem 1.3 for bandwidth one.  If the unique auxiliary root
`γ` lies below `α + 1`, every admissible combination has only positive,
simple real roots. -/
theorem laguerreCombinationOne_splits_simple_roots_pos
    {n : ℕ} (hn : 1 ≤ n) {α γ : ℝ} (hα : -1 < α)
    (hγ : γ < α + 1) :
    (laguerreCombinationOne n α γ).Splits ∧
      HasSimpleRoots (laguerreCombinationOne n α γ) ∧
      ∀ r ∈ (laguerreCombinationOne n α γ).roots, 0 < r := by
  rcases hn.eq_or_lt with rfl | hnlt
  · have hcomb : laguerreCombinationOne 1 α γ =
        X - C (α + 1 - γ) := by
      simp [laguerreCombinationOne]
      ring
    rw [hcomb]
    refine ⟨Polynomial.Splits.of_degree_le_one
      (degree_X_sub_C_le (α + 1 - γ)), ?_, ?_⟩
    · apply HasSimpleRoots.of_roots_nodup (X_sub_C_ne_zero _)
      rw [roots_X_sub_C]
      simp
    · intro r hr
      rw [roots_X_sub_C] at hr
      simp only [Multiset.mem_singleton] at hr
      subst r
      linarith
  · have hn2 : 2 ≤ n := by lia
    let F := generalizedLaguerre n α -
      C γ * generalizedLaguerre (n - 1) α
    have hpack := generalizedLaguerre_sub_prev_strict_package hn2 hα hγ
    have href := laguerreCombinationOne_comp_neg_X hn α γ
    have hsign : (-1 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
    have hcompSplits :
        ((laguerreCombinationOne n α γ).comp (-X)).Splits := by
      rw [href]
      exact hpack.1.2.1.2.C_mul _
    have hsplits : (laguerreCombinationOne n α γ).Splits := by
      have h := hcompSplits.comp_neg_X
      simpa [comp_neg_X_comp_neg_X] using h
    have hcompSimple :
        HasSimpleRoots ((laguerreCombinationOne n α γ).comp (-X)) := by
      rw [href]
      exact hpack.2.1.C_mul hsign
    have hsimple : HasSimpleRoots (laguerreCombinationOne n α γ) := by
      have h := hcompSimple.comp_C_mul_X_add_C
        (a := (-1 : ℝ)) (b := 0) (by norm_num)
      simpa [comp_neg_X_comp_neg_X] using h
    refine ⟨hsplits, hsimple, ?_⟩
    intro r hr
    have hrroot : (laguerreCombinationOne n α γ).IsRoot r :=
      (Polynomial.mem_roots hsimple.ne_zero).mp hr
    have hcompRoot :
        ((laguerreCombinationOne n α γ).comp (-X)).IsRoot (-r) := by
      rw [Polynomial.IsRoot.def] at hrroot ⊢
      simpa [eval_comp] using hrroot
    have hFroot : F.IsRoot (-r) := by
      rw [href] at hcompRoot
      rw [Polynomial.IsRoot.def] at hcompRoot ⊢
      simpa [F, hsign] using hcompRoot
    have hFmem : -r ∈ F.roots :=
      (Polynomial.mem_roots hpack.2.1.ne_zero).mpr hFroot
    linarith [hpack.2.2 (-r) hFmem]

/-- Auxiliary-polynomial form of the bandwidth-one criterion. -/
theorem laguerreCombinationOne_splits_simple_roots_pos_of_auxiliary
    {n : ℕ} (hn : 1 ≤ n) {α γ : ℝ} (hα : -1 < α)
    (hQ : ∀ x, (laguerreAuxiliaryOne γ).IsRoot x → x < α + 1) :
    (laguerreCombinationOne n α γ).Splits ∧
      HasSimpleRoots (laguerreCombinationOne n α γ) ∧
      ∀ r ∈ (laguerreCombinationOne n α γ).roots, 0 < r := by
  apply laguerreCombinationOne_splits_simple_roots_pos hn hα
  exact hQ γ ((laguerreAuxiliaryOne_isRoot_iff γ γ).2 rfl)

/-- The concrete coefficient `γ = -1` satisfies Durán's bandwidth-one
criterion throughout the classical range. -/
theorem laguerreCombinationOne_neg_one_splits_simple_roots_pos
    {n : ℕ} (hn : 1 ≤ n) {α : ℝ} (hα : -1 < α) :
    (laguerreCombinationOne n α (-1)).Splits ∧
      HasSimpleRoots (laguerreCombinationOne n α (-1)) ∧
      ∀ r ∈ (laguerreCombinationOne n α (-1)).roots, 0 < r :=
  laguerreCombinationOne_splits_simple_roots_pos hn hα (by linarith)

/-- The concrete coefficient `γ = 1` satisfies Durán's bandwidth-one
criterion when `α > 0`. -/
theorem laguerreCombinationOne_one_splits_simple_roots_pos
    {n : ℕ} (hn : 1 ≤ n) {α : ℝ} (hα : 0 < α) :
    (laguerreCombinationOne n α 1).Splits ∧
      HasSimpleRoots (laguerreCombinationOne n α 1) ∧
      ∀ r ∈ (laguerreCombinationOne n α 1).roots, 0 < r :=
  laguerreCombinationOne_splits_simple_roots_pos hn (by linarith) (by linarith)

end RealRooted
