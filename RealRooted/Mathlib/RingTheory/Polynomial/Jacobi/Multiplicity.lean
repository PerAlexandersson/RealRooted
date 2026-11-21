/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Mathlib.RingTheory.Polynomial.Jacobi
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Basic.Complex.Basic
import RealRooted.Mathlib.Algebra.Polynomial.DifferentialEquation.Indicial
import RealRooted.Mathlib.Algebra.Polynomial.DifferentialEquation.SecondOrder
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.Tactic

/-!
# Endpoint multiplicities of shifted Jacobi polynomials

The nonzero hypothesis is essential and no exact degree hypothesis is imposed.
Source: unpublished proof notes in RealRooted issue #2341, Corollary 5 and
Proposition 6 in its comment on two negative parameters.
-/

public section

namespace Polynomial

/-- The polynomial binomial endpoint value vanishes exactly at the indicated
negative integers, including when the range is empty. -/
theorem choose_add_nat_eq_zero_iff (n : ℕ) (α : ℝ) :
    Ring.choose ((n : ℝ) + α) n = 0 ↔
      ∃ m : ℕ, 1 ≤ m ∧ m ≤ n ∧ α = -(m : ℝ) := by
  have hform : Ring.choose ((n : ℝ) + α) n =
      (n.factorial : ℝ)⁻¹ * (ascPochhammer ℝ n).eval (α + 1) := by
    rw [Ring.choose_eq_smul, smul_eq_mul, ← eval₂_smulOneHom_eq_smeval, ← eval_map,
      descPochhammer_map, descPochhammer_eval_eq_ascPochhammer]
    congr 2
    ring
  rw [hform, mul_eq_zero, inv_eq_zero]
  simp only [Nat.cast_eq_zero, Nat.factorial_ne_zero, false_or,
    ascPochhammer_eval_eq_zero_iff]
  constructor
  · rintro ⟨k, hk, hα⟩
    refine ⟨k + 1, by lia, by lia, ?_⟩
    push_cast
    linarith
  · rintro ⟨m, hm, hmn, rfl⟩
    refine ⟨m - 1, by lia, ?_⟩
    rw [Nat.cast_sub hm]
    ring

/-- Zero is a Jacobi root exactly at the negative integer left endpoint parameters. -/
theorem isRoot_zero_shiftedJacobi_iff (n : ℕ) (α β : ℝ) :
    (shiftedJacobi n α β).IsRoot 0 ↔
      ∃ m : ℕ, 1 ≤ m ∧ m ≤ n ∧ α = -(m : ℝ) := by
  rw [IsRoot.def, shiftedJacobi_eval_zero, choose_add_nat_eq_zero_iff]

/-- One is a Jacobi root exactly at the negative integer right endpoint parameters. -/
theorem isRoot_one_shiftedJacobi_iff (n : ℕ) (α β : ℝ) :
    (shiftedJacobi n α β).IsRoot 1 ↔
      ∃ m : ℕ, 1 ≤ m ∧ m ≤ n ∧ β = -(m : ℝ) := by
  rw [IsRoot.def, shiftedJacobi_eval_one, mul_eq_zero]
  simp only [pow_ne_zero n (by norm_num : (-1 : ℝ) ≠ 0), false_or,
    choose_add_nat_eq_zero_iff]

/-- The shifted Jacobi degree is at most its index at every real parameter. -/
theorem natDegree_shiftedJacobi_le (n : ℕ) (α β : ℝ) :
    (shiftedJacobi n α β).natDegree ≤ n := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro k hk
  simp [coeff_shiftedJacobi, Nat.not_le_of_lt hk]

/-- The parameter at a zero endpoint root is the negative of its multiplicity. -/
theorem rootMultiplicity_zero_add_shiftedJacobi
    (n : ℕ) (α β : ℝ) (hne : shiftedJacobi n α β ≠ 0)
    (hr : (shiftedJacobi n α β).IsRoot 0) :
    ((shiftedJacobi n α β).rootMultiplicity 0 : ℝ) + α = 0 := by
  have h := rootMultiplicity_sub_one_mul_eval_derivative_add_eq_zero hne
    (shiftedJacobi_differential_equation n α β) (r := 0) (by simp) hr
  simpa using h

/-- The parameter at a one endpoint root is the negative of its multiplicity. -/
theorem rootMultiplicity_one_add_shiftedJacobi
    (n : ℕ) (α β : ℝ) (hne : shiftedJacobi n α β ≠ 0)
    (hr : (shiftedJacobi n α β).IsRoot 1) :
    ((shiftedJacobi n α β).rootMultiplicity 1 : ℝ) + β = 0 := by
  have h := rootMultiplicity_sub_one_mul_eval_derivative_add_eq_zero hne
    (shiftedJacobi_differential_equation n α β) (r := 1) (by simp) hr
  simp at h
  linarith

/-- Exact left endpoint multiplicity for every nonzero shifted Jacobi polynomial. -/
theorem rootMultiplicity_zero_shiftedJacobi_eq_iff
    (n m : ℕ) (α β : ℝ) (hne : shiftedJacobi n α β ≠ 0)
    (hm : 1 ≤ m) (hmn : m ≤ n) :
    (shiftedJacobi n α β).rootMultiplicity 0 = m ↔ α = -(m : ℝ) := by
  constructor
  · intro h
    have hr := (rootMultiplicity_pos hne).mp (by rw [h]; lia)
    have := rootMultiplicity_zero_add_shiftedJacobi n α β hne hr
    rw [h] at this
    linarith
  · intro hα
    have hr : (shiftedJacobi n α β).IsRoot 0 := by
      rw [IsRoot.def, shiftedJacobi_eval_zero]
      exact (choose_add_nat_eq_zero_iff n α).mpr ⟨m, hm, hmn, hα⟩
    have := rootMultiplicity_zero_add_shiftedJacobi n α β hne hr
    exact Nat.cast_injective (R := ℝ) (by linarith)

/-- Exact right endpoint multiplicity for every nonzero shifted Jacobi polynomial. -/
theorem rootMultiplicity_one_shiftedJacobi_eq_iff
    (n m : ℕ) (α β : ℝ) (hne : shiftedJacobi n α β ≠ 0)
    (hm : 1 ≤ m) (hmn : m ≤ n) :
    (shiftedJacobi n α β).rootMultiplicity 1 = m ↔ β = -(m : ℝ) := by
  constructor
  · intro h
    have hr := (rootMultiplicity_pos hne).mp (by rw [h]; lia)
    have := rootMultiplicity_one_add_shiftedJacobi n α β hne hr
    rw [h] at this
    linarith
  · intro hβ
    have hr : (shiftedJacobi n α β).IsRoot 1 := by
      rw [IsRoot.def, shiftedJacobi_eval_one,
        (choose_add_nat_eq_zero_iff n β).mpr ⟨m, hm, hmn, hβ⟩, mul_zero]
    have := rootMultiplicity_one_add_shiftedJacobi n α β hne hr
    exact Nat.cast_injective (R := ℝ) (by linarith)

/-- A nonzero Jacobi polynomial has zero left multiplicity outside the negative endpoint set. -/
theorem rootMultiplicity_zero_shiftedJacobi_eq_zero_iff
    (n : ℕ) (α β : ℝ) (hne : shiftedJacobi n α β ≠ 0) :
    (shiftedJacobi n α β).rootMultiplicity 0 = 0 ↔
      ∀ m : ℕ, 1 ≤ m → m ≤ n → α ≠ -(m : ℝ) := by
  rw [rootMultiplicity_eq_zero_iff]
  simp only [isRoot_zero_shiftedJacobi_iff, hne, imp_false]
  push Not
  rfl

/-- A nonzero Jacobi polynomial has zero right multiplicity outside the negative endpoint set. -/
theorem rootMultiplicity_one_shiftedJacobi_eq_zero_iff
    (n : ℕ) (α β : ℝ) (hne : shiftedJacobi n α β ≠ 0) :
    (shiftedJacobi n α β).rootMultiplicity 1 = 0 ↔
      ∀ m : ℕ, 1 ≤ m → m ≤ n → β ≠ -(m : ℝ) := by
  rw [rootMultiplicity_eq_zero_iff]
  simp only [isRoot_one_shiftedJacobi_iff, hne, imp_false]
  push Not
  rfl

/-- Every complex root away from the two singular endpoints is simple. -/
theorem rootMultiplicity_map_shiftedJacobi_le_one
    (n : ℕ) (α β : ℝ) (hne : shiftedJacobi n α β ≠ 0)
    (r : ℂ) (hr0 : r ≠ 0) (hr1 : r ≠ 1) :
    ((shiftedJacobi n α β).map Complex.ofRealHom).rootMultiplicity r ≤ 1 := by
  let p := (shiftedJacobi n α β).map Complex.ofRealHom
  have hp : p ≠ 0 := (Polynomial.map_ne_zero_iff Complex.ofReal_injective).mpr hne
  have hode := congrArg (map Complex.ofRealHom)
    (shiftedJacobi_differential_equation n α β)
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_one, ← Polynomial.derivative_map,
    Polynomial.map_C, Polynomial.map_zero] at hode
  by_cases hr : p.IsRoot r
  · have hder := eval_derivative_ne_zero_of_second_order_ode hp (A := X * (1 - X)) hode hr
      (by simpa using mul_ne_zero hr0 (sub_ne_zero.mpr (Ne.symm hr1)))
    by_contra hmult
    have h := (one_lt_rootMultiplicity_iff_isRoot hp).mp (show 1 < p.rootMultiplicity r by
      dsimp [p]; lia)
    exact hder h.2
  · exact (rootMultiplicity_eq_zero hr).le.trans (by lia)

/-- Multiplicities at distinct points use disjoint occurrences in the root multiset. -/
private theorem endpoint_multiplicities_le_natDegree (p : ℝ[X]) :
    p.rootMultiplicity 0 + p.rootMultiplicity 1 ≤ p.natDegree := by
  classical
  have h : Multiset.replicate (p.rootMultiplicity 0) (0 : ℝ) +
      Multiset.replicate (p.rootMultiplicity 1) (1 : ℝ) ≤ p.roots := by
    rw [Multiset.le_iff_count]
    intro r
    by_cases h0 : r = 0
    · subst r
      simp [Multiset.count_replicate, count_roots]
    by_cases h1 : r = 1
    · subst r
      simp [Multiset.count_replicate, count_roots]
    · simp [Multiset.count_replicate, Ne.symm h0, Ne.symm h1]
  have hc := Multiset.card_le_card h
  simp only [Multiset.card_add, Multiset.card_replicate] at hc
  exact hc.trans (card_roots' p)

/-- The standard shifted Jacobi polynomial vanishes identically exactly when
both parameters are negative integers in range whose absolute values sum above `n`. -/
theorem shiftedJacobi_eq_zero_iff (n : ℕ) (α β : ℝ) :
    shiftedJacobi n α β = 0 ↔
      ∃ p q : ℕ, 1 ≤ p ∧ p ≤ n ∧ 1 ≤ q ∧ q ≤ n ∧
        α = -(p : ℝ) ∧ β = -(q : ℝ) ∧ n < p + q := by
  constructor
  · intro hz
    have h0 : Ring.choose ((n : ℝ) + α) n = 0 := by
      simpa using congrArg (eval (0 : ℝ)) hz
    have h1 : Ring.choose ((n : ℝ) + β) n = 0 := by
      have h := congrArg (eval (1 : ℝ)) hz
      simpa only [shiftedJacobi_eval_one, eval_zero, mul_eq_zero,
        pow_ne_zero n (neg_ne_zero.mpr (one_ne_zero : (1 : ℝ) ≠ 0)), false_or] using h
    obtain ⟨p, hp, hpn, hα⟩ := (choose_add_nat_eq_zero_iff n α).mp h0
    obtain ⟨q, hq, hqn, hβ⟩ := (choose_add_nat_eq_zero_iff n β).mp h1
    refine ⟨p, q, hp, hpn, hq, hqn, hα, hβ, ?_⟩
    by_contra hs
    have hs' : (p : ℝ) + q ≤ n := by exact_mod_cast (show p + q ≤ n by lia)
    have hc : 0 < Ring.choose ((n : ℝ) + α + β + n) n := by
      apply ring_choose_pos
      rw [hα, hβ]
      linarith
    have ht := congrArg (fun f : ℝ[X] => f.coeff n) hz
    simp only [coeff_shiftedJacobi, le_refl, ite_true, Nat.sub_self,
      Ring.choose_zero_right, mul_one, coeff_zero] at ht
    exact (mul_ne_zero (pow_ne_zero n (by norm_num)) hc.ne') ht
  · rintro ⟨p, q, hp, hpn, hq, hqn, hα, hβ, hs⟩
    by_contra hne
    have hm0 := (rootMultiplicity_zero_shiftedJacobi_eq_iff n p α β hne hp hpn).mpr hα
    have hm1 := (rootMultiplicity_one_shiftedJacobi_eq_iff n q α β hne hq hqn).mpr hβ
    have hdeg := (endpoint_multiplicities_le_natDegree (shiftedJacobi n α β)).trans
      (natDegree_shiftedJacobi_le n α β)
    rw [hm0, hm1] at hdeg
    lia

/-- Squarefreeness at all real parameters for a nonzero Jacobi polynomial;
complexification ensures that nonreal repeated roots are also excluded. -/
theorem squarefree_shiftedJacobi_iff
    (n : ℕ) (α β : ℝ) (hne : shiftedJacobi n α β ≠ 0) :
    Squarefree (shiftedJacobi n α β) ↔
      (∀ m : ℕ, 2 ≤ m → m ≤ n → α ≠ -(m : ℝ)) ∧
      (∀ m : ℕ, 2 ≤ m → m ≤ n → β ≠ -(m : ℝ)) := by
  classical
  rw [← PerfectField.separable_iff_squarefree]
  constructor
  · intro h
    constructor
    · intro m hm hmn hα
      have hmult := rootMultiplicity_le_one_of_separable h (0 : ℝ)
      rw [(rootMultiplicity_zero_shiftedJacobi_eq_iff n m α β hne (by lia) hmn).mpr hα]
        at hmult
      lia
    · intro m hm hmn hβ
      have hmult := rootMultiplicity_le_one_of_separable h (1 : ℝ)
      rw [(rootMultiplicity_one_shiftedJacobi_eq_iff n m α β hne (by lia) hmn).mpr hβ]
        at hmult
      lia
  · rintro ⟨hα, hβ⟩
    have hbound (r : ℝ) : (shiftedJacobi n α β).rootMultiplicity r ≤ n := by
      have h := natDegree_le_of_dvd
        (pow_rootMultiplicity_dvd (shiftedJacobi n α β) r) hne
      simpa using h.trans (natDegree_shiftedJacobi_le n α β)
    have h0 : (shiftedJacobi n α β).rootMultiplicity 0 ≤ 1 := by
      by_contra hm
      have hroot := (rootMultiplicity_pos hne).mp (show
        0 < (shiftedJacobi n α β).rootMultiplicity 0 by lia)
      have hid := rootMultiplicity_zero_add_shiftedJacobi n α β hne hroot
      exact hα _ (by lia) (hbound 0) (by linarith)
    have h1 : (shiftedJacobi n α β).rootMultiplicity 1 ≤ 1 := by
      by_contra hm
      have hroot := (rootMultiplicity_pos hne).mp (show
        0 < (shiftedJacobi n α β).rootMultiplicity 1 by lia)
      have hid := rootMultiplicity_one_add_shiftedJacobi n α β hne hroot
      exact hβ _ (by lia) (hbound 1) (by linarith)
    rw [← separable_map Complex.ofRealHom]
    apply (nodup_roots_iff_of_splits
      ((Polynomial.map_ne_zero_iff Complex.ofReal_injective).mpr hne)
      (IsAlgClosed.splits _)).mp
    apply Multiset.nodup_iff_count_le_one.mpr
    intro r
    rw [count_roots]
    by_cases hr0 : r = 0
    · subst r
      simpa using ((eq_rootMultiplicity_map (p := shiftedJacobi n α β)
        (f := Complex.ofRealHom) Complex.ofReal_injective (0 : ℝ)).ge.trans h0)
    by_cases hr1 : r = 1
    · subst r
      simpa using ((eq_rootMultiplicity_map (p := shiftedJacobi n α β)
        (f := Complex.ofRealHom) Complex.ofReal_injective (1 : ℝ)).ge.trans h1)
    exact rootMultiplicity_map_shiftedJacobi_le_one n α β hne r hr0 hr1

end Polynomial
