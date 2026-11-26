/-
Copyright (c) 2026 Bowen Zuo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bowen Zuo
-/
module

public import RealRooted.CombinatorialExamples.LongCycleDescents.Basic
public import RealRooted.Basic.Coefficients
import RealRooted.CombinatorialExamples.EulerianStatistic
import RealRooted.Applications.EulerianCompendium.DerangementReciprocal
import Mathlib.Tactic

/-!
# Nonvanishing, root signs, and the two classical cutoffs

We reuse the existing Eulerian and derangement descent theorems at cutoffs one
and two. The nonvanishing and nonpositive-root assertions hold for every cutoff
and for all nonzero nonnegative mixtures, independently of a sign certificate.

Adapted from Bowen Zuo, cycle-minimum-descent-real-roots v1.0.0 (Apache-2.0)
-/

@[expose] public section

noncomputable section

namespace RealRooted.LongCycleDescents

open Polynomial Finset

/-- The original integer permutation sum, with real coefficients. -/
def realDescentPolynomial (n k : ℕ) : ℝ[X] :=
  (descentPolynomial n k).map (Int.castRingHom ℝ)

/-- Nonnegative combinations over all the cutoffs in the manuscript's second theorem. -/
def mixture (n : ℕ) (w : ℕ → ℝ) : ℝ[X] :=
  ∑ k ∈ Icc 1 n, C (w k) * realDescentPolynomial n k

/-- Cutoff one imposes no cycle restriction. -/
theorem hasLongCycles_one {n : ℕ} (σ : Equiv.Perm (Fin n)) : HasLongCycles 1 σ := by
  intro x j hj hk
  lia

/-- Cutoff two is exactly the derangement condition on the original labels. -/
theorem hasLongCycles_two_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    HasLongCycles 2 σ ↔ ∀ i, σ i ≠ i := by
  refine ⟨fun h ↦ ne_fixed_of_allowed h (by decide), ?_⟩
  intro h i j hj hk
  have eq : j = 1 := by lia
  simpa only [eq, pow_one] using h i

/-- The full cyclic rotation is allowed whenever the cutoff is at most the size. -/
theorem hasLongCycles_finRotate {n k : ℕ} (hk : k ≤ n) :
    HasLongCycles k (finRotate n) := by
  by_cases hn : 2 ≤ n
  · have support := support_finRotate_of_le hn
    have cycle := isCycle_finRotate_of_le hn
    have order : orderOf (finRotate n) = n := by
      rw [cycle.orderOf, support, card_univ, Fintype.card_fin]
    intro x j hj hjk
    have hx : x ∈ (finRotate n).support := by rw [support]; exact mem_univ _
    rw [← cycle.support_pow_of_pos_of_lt_orderOf hj (by rw [order]; exact hjk.trans_le hk),
      Equiv.Perm.mem_support] at hx
    exact hx
  · intro x j hj hjk
    lia

/-- Every coefficient counts a set of original permutations and is nonnegative. -/
theorem realDescentPolynomial_hasNonnegCoeffs (n k : ℕ) :
    HasNonnegCoeffs (realDescentPolynomial n k) := by
  classical
  intro i
  rw [realDescentPolynomial, coeff_map, coeff_descentPolynomial]
  change 0 ≤ (↑(∑ σ : Equiv.Perm (Fin n),
    if HasLongCycles k σ ∧ σ.descentCount = i then (1 : ℤ) else 0) : ℝ)
  exact_mod_cast (sum_nonneg (fun σ (_ : σ ∈ univ) ↦
    show (0 : ℤ) ≤ if HasLongCycles k σ ∧ σ.descentCount = i then 1 else 0 from by
      split <;> norm_num))

open Classical in
/-- Evaluation at one counts exactly the permutations satisfying the cycle cutoff. -/
theorem realDescentPolynomial_eval_one (n k : ℕ) :
    (realDescentPolynomial n k).eval 1 =
      ((univ.filter fun σ : Equiv.Perm (Fin n) ↦ HasLongCycles k σ).card : ℝ) := by
  classical
  simp only [realDescentPolynomial, descentPolynomial, Polynomial.map_sum,
    Polynomial.eval_finsetSum]
  simp only [apply_ite, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_zero,
    eval_pow, eval_X, one_pow, eval_zero]
  simp only [sum_boole]

/-- There is at least one allowed permutation at every cutoff up to the size. -/
theorem realDescentPolynomial_eval_one_pos {n k : ℕ} (hk : k ≤ n) :
    0 < (realDescentPolynomial n k).eval 1 := by
  classical
  rw [realDescentPolynomial_eval_one]
  exact_mod_cast (card_pos.mpr ⟨finRotate n,
    mem_filter.mpr ⟨mem_univ _, hasLongCycles_finRotate hk⟩⟩)

/-- Every original row with a cutoff up to the size is nonzero. -/
theorem realDescentPolynomial_ne_zero {n k : ℕ} (hk : k ≤ n) :
    realDescentPolynomial n k ≠ 0 := by
  intro hz
  have pos := realDescentPolynomial_eval_one_pos hk
  rw [hz, eval_zero] at pos
  exact lt_irrefl _ pos

/-- Every real root of an original row is nonpositive, independently of splitting. -/
theorem realDescentPolynomial_roots_nonpos (n k : ℕ) :
    ∀ z ∈ (realDescentPolynomial n k).roots, z ≤ 0 :=
  roots_nonpos_of_hasNonnegCoeffs (realDescentPolynomial_hasNonnegCoeffs n k)

/-- Nonnegative weights preserve the nonnegative coefficient property. -/
theorem mixture_hasNonnegCoeffs {n : ℕ} {w : ℕ → ℝ}
    (hw : ∀ k ∈ Icc 1 n, 0 ≤ w k) : HasNonnegCoeffs (mixture n w) := by
  apply hasNonnegCoeffs_finsetSum
  intro k hk
  exact (hasNonnegCoeffs_C (hw k hk)).mul (realDescentPolynomial_hasNonnegCoeffs n k)

/-- A nonzero nonnegative choice of weights gives a nonzero original mixture. -/
theorem mixture_ne_zero {n : ℕ} {w : ℕ → ℝ}
    (hw : ∀ k ∈ Icc 1 n, 0 ≤ w k) (pos : ∃ k ∈ Icc 1 n, 0 < w k) :
    mixture n w ≠ 0 := by
  have atOne : 0 < (mixture n w).eval 1 := by
    simp only [mixture, Polynomial.eval_finsetSum, eval_mul, eval_C]
    apply sum_pos'
    · intro k hk
      exact mul_nonneg (hw k hk) (realDescentPolynomial_eval_one_pos (mem_Icc.mp hk).2).le
    · obtain ⟨k, hk, hp⟩ := pos
      exact ⟨k, hk, mul_pos hp (realDescentPolynomial_eval_one_pos (mem_Icc.mp hk).2)⟩
  intro hz
  rw [hz, eval_zero] at atOne
  exact lt_irrefl _ atOne

/-- Every real root of every nonnegative original mixture is nonpositive. -/
theorem mixture_roots_nonpos {n : ℕ} {w : ℕ → ℝ}
    (hw : ∀ k ∈ Icc 1 n, 0 ≤ w k) : ∀ z ∈ (mixture n w).roots, z ≤ 0 :=
  roots_nonpos_of_hasNonnegCoeffs (mixture_hasNonnegCoeffs hw)

/-- Cutoff one splits by the existing permutation Eulerian theorem. -/
theorem realDescentPolynomial_one_splits {n : ℕ} (hn : 0 < n) :
    (realDescentPolynomial n 1).Splits := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have eq : realDescentPolynomial (m + 1) 1 =
      ((univ : Finset (Equiv.Perm (Fin (m + 1)))).genPoly
        Equiv.Perm.descentCount : ℝ[X]) := by
    classical
    simp only [realDescentPolynomial, descentPolynomial, hasLongCycles_one, ite_true,
      Polynomial.map_sum, Polynomial.map_pow, Polynomial.map_X, genPoly]
  rw [eq]
  exact (isRealRooted_genPoly_univ_descentCount m).2

/-- Cutoff two splits by the existing theorem for actual derangement descents. -/
theorem realDescentPolynomial_two_splits {n : ℕ} (hn : 2 ≤ n) :
    (realDescentPolynomial n 2).Splits := by
  have eq : realDescentPolynomial n 2 = EulerianCompendium.derangementDescentPolynomial n := by
    classical
    simp only [realDescentPolynomial, descentPolynomial, Polynomial.map_sum,
      EulerianCompendium.derangementDescentPolynomial, hasLongCycles_two_iff,
      apply_ite, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_zero]
  rw [eq]
  exact EulerianCompendium.derangementDescentPolynomial_splits n hn

end RealRooted.LongCycleDescents

end
