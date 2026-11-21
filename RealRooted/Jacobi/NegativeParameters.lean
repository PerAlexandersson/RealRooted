/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Mathlib.RingTheory.Polynomial.Jacobi
public import Mathlib.Algebra.Polynomial.Roots
import RealRooted.Jacobi
import RealRooted.Mathlib.RingTheory.Polynomial.Jacobi.NegativeParameters
import RealRooted.Mathlib.RingTheory.Polynomial.Jacobi.Multiplicity
import Mathlib.Tactic

/-!
# Root geometry with two negative integer Jacobi parameters

The zero case is separate from the nonzero endpoint factorization. In the latter,
the remaining positive-parameter Jacobi factor has simple roots in `(0,1)`.
Source: unpublished proof notes in the comment on RealRooted issue #2341,
Corollary 8.
-/

public section

open Polynomial

namespace RealRooted

/-- Two negative integer parameters in range give either the zero polynomial
or a polynomial splitting over the reals. -/
theorem shiftedJacobi_neg_nat_neg_nat_splits
    (n p q : ℕ) (hp : p ≤ n) (hq : q ≤ n) :
    (shiftedJacobi n (-(p : ℝ)) (-(q : ℝ))).Splits := by
  by_cases hs : p + q ≤ n
  · rw [shiftedJacobi_neg_nat_neg_nat n p q hs]
    have hp' : (-1 : ℝ) < p := by have := Nat.cast_nonneg (α := ℝ) p; linarith
    have hq' : (-1 : ℝ) < q := by have := Nat.cast_nonneg (α := ℝ) q; linarith
    have hx : (X : ℝ[X]).Splits := Splits.X
    have h1 : (1 - X : ℝ[X]).Splits := by
      have heq : (1 - X : ℝ[X]) = -(X - C 1) := by simp
      rw [heq]
      exact (Splits.X_sub_C 1).neg
    exact ((hx.pow p).mul ((h1.pow q).mul (shiftedJacobi_splits _ hp' hq'))).C_mul _
  · have hz := (shiftedJacobi_eq_zero_iff n (-(p : ℝ)) (-(q : ℝ))).mpr
      ⟨p, q, by lia, hp, by lia, hq, rfl, rfl, by lia⟩
    rw [hz]
    exact Splits.zero

/-- In the nonzero range, every root is an endpoint or belongs to the open unit interval. -/
theorem isRoot_shiftedJacobi_neg_nat_neg_nat
    (n p q : ℕ) (hs : p + q ≤ n) {r : ℝ}
    (hr : (shiftedJacobi n (-(p : ℝ)) (-(q : ℝ))).IsRoot r) :
    r = 0 ∨ r = 1 ∨ r ∈ Set.Ioo (0 : ℝ) 1 := by
  by_cases hr0 : r = 0
  · exact Or.inl hr0
  by_cases hr1 : r = 1
  · exact Or.inr (Or.inl hr1)
  right; right
  rw [shiftedJacobi_neg_nat_neg_nat n p q hs, IsRoot.def] at hr
  simp only [eval_mul, eval_C, eval_pow, eval_X, eval_sub, eval_one, mul_eq_zero] at hr
  have hroot : (shiftedJacobi (n - (p + q)) (p : ℝ) q).IsRoot r := by
    rcases hr with hsign | hx | h1 | hroot
    · exact (pow_ne_zero p (by norm_num : (-1 : ℝ) ≠ 0) hsign).elim
    · exact (pow_ne_zero p hr0 hx).elim
    · exact (pow_ne_zero q (sub_ne_zero.mpr (Ne.symm hr1)) h1).elim
    · exact hroot
  exact shiftedJacobi_isRoot_mem_Ioo _
    (by have := Nat.cast_nonneg (α := ℝ) p; linarith)
    (by have := Nat.cast_nonneg (α := ℝ) q; linarith) hroot

/-- In the nonzero range, the degree is exactly the index, even though arbitrary
Jacobi parameters can cause degree drops. -/
theorem natDegree_shiftedJacobi_neg_nat_neg_nat
    (n p q : ℕ) (hs : p + q ≤ n) :
    (shiftedJacobi n (-(p : ℝ)) (-(q : ℝ))).natDegree = n := by
  rw [shiftedJacobi_neg_nat_neg_nat n p q hs]
  have hp : (-1 : ℝ) < p := by have := Nat.cast_nonneg (α := ℝ) p; linarith
  have hq : (-1 : ℝ) < q := by have := Nat.cast_nonneg (α := ℝ) q; linarith
  have hR := shiftedJacobi_ne_zero (n - (p + q)) hp hq
  have hb : (1 - X : ℝ[X]) = -(X - C 1) := by simp
  have h1 : (1 - X : ℝ[X]) ≠ 0 := by rw [hb]; exact neg_ne_zero.mpr (X_sub_C_ne_zero 1)
  rw [natDegree_C_mul (pow_ne_zero p (by norm_num)),
    natDegree_mul (pow_ne_zero p X_ne_zero) (mul_ne_zero (pow_ne_zero q h1) hR),
    natDegree_mul (pow_ne_zero q h1) hR, natDegree_pow, natDegree_pow,
    natDegree_X, mul_one, hb, natDegree_neg, natDegree_X_sub_C, mul_one,
    natDegree_shiftedJacobi _ hp hq]
  lia

/-- The two-endpoint factor is nonzero when the endpoint exponents fit within the degree. -/
theorem shiftedJacobi_neg_nat_neg_nat_ne_zero
    (n p q : ℕ) (hs : p + q ≤ n) : shiftedJacobi n (-(p : ℝ)) (-(q : ℝ)) ≠ 0 := by
  intro hz
  obtain ⟨p', q', _, _, _, _, hp, hq, hsum⟩ :=
    (shiftedJacobi_eq_zero_iff n (-(p : ℝ)) (-(q : ℝ))).mp hz
  have hpp : p = p' := by exact_mod_cast neg_injective hp
  have hqq : q = q' := by exact_mod_cast neg_injective hq
  lia

/-- Exact left endpoint multiplicity, including exponent zero. -/
theorem rootMultiplicity_zero_shiftedJacobi_neg_nat_neg_nat
    (n p q : ℕ) (hs : p + q ≤ n) :
    (shiftedJacobi n (-(p : ℝ)) (-(q : ℝ))).rootMultiplicity 0 = p := by
  by_cases hp : p = 0
  · subst p
    apply rootMultiplicity_eq_zero
    simp [IsRoot.def, Ring.choose_natCast]
  exact (rootMultiplicity_zero_shiftedJacobi_eq_iff n p _ _
    (shiftedJacobi_neg_nat_neg_nat_ne_zero n p q hs) (by lia) (by lia)).mpr rfl

/-- Exact right endpoint multiplicity, including exponent zero. -/
theorem rootMultiplicity_one_shiftedJacobi_neg_nat_neg_nat
    (n p q : ℕ) (hs : p + q ≤ n) :
    (shiftedJacobi n (-(p : ℝ)) (-(q : ℝ))).rootMultiplicity 1 = q := by
  by_cases hq : q = 0
  · subst q
    apply rootMultiplicity_eq_zero
    simp [IsRoot.def, Ring.choose_natCast]
  exact (rootMultiplicity_one_shiftedJacobi_eq_iff n q _ _
    (shiftedJacobi_neg_nat_neg_nat_ne_zero n p q hs) (by lia) (by lia)).mpr rfl

/-- Every interior root is simple in the nonzero two-negative-parameter range. -/
theorem rootMultiplicity_shiftedJacobi_neg_nat_neg_nat_le_one
    (n p q : ℕ) (hs : p + q ≤ n) {r : ℝ} (hr0 : r ≠ 0) (hr1 : r ≠ 1) :
    (shiftedJacobi n (-(p : ℝ)) (-(q : ℝ))).rootMultiplicity r ≤ 1 := by
  have hc := rootMultiplicity_map_shiftedJacobi_le_one n (-(p : ℝ)) (-(q : ℝ))
    (shiftedJacobi_neg_nat_neg_nat_ne_zero n p q hs) (r : ℂ)
    (by exact_mod_cast hr0) (by exact_mod_cast hr1)
  exact (eq_rootMultiplicity_map (f := Complex.ofRealHom)
    Complex.ofReal_injective r).le.trans (by simpa using hc)

/-- There are exactly `n-p-q` interior roots, counted with multiplicity. The preceding
simplicity theorem shows that these roots are distinct. -/
theorem card_roots_Ioo_shiftedJacobi_neg_nat_neg_nat
    (n p q : ℕ) (hs : p + q ≤ n) :
    ((shiftedJacobi n (-(p : ℝ)) (-(q : ℝ))).roots.filter
      (fun r => r ∈ Set.Ioo (0 : ℝ) 1)).card = n - (p + q) := by
  classical
  let f := shiftedJacobi n (-(p : ℝ)) (-(q : ℝ))
  have h0 : f.roots.count 0 = p := by
    rw [count_roots]
    exact rootMultiplicity_zero_shiftedJacobi_neg_nat_neg_nat n p q hs
  have h1 : f.roots.count 1 = q := by
    rw [count_roots]
    exact rootMultiplicity_one_shiftedJacobi_neg_nat_neg_nat n p q hs
  have hsplit : f.Splits := shiftedJacobi_neg_nat_neg_nat_splits n p q (by lia) (by lia)
  have hcard : f.roots.card = n := by
    rw [← hsplit.natDegree_eq_card_roots]
    exact natDegree_shiftedJacobi_neg_nat_neg_nat n p q hs
  have hpart : f.roots.filter (fun r => r ∈ Set.Ioo (0 : ℝ) 1) +
      Multiset.replicate p 0 + Multiset.replicate q 1 = f.roots := by
    ext r
    by_cases hr0 : r = 0
    · subst r
      simp [Multiset.count_add, Multiset.count_replicate, h0]
    by_cases hr1 : r = 1
    · subst r
      simp [Multiset.count_add, Multiset.count_replicate, h1]
    by_cases hr : r ∈ f.roots
    · have hloc := isRoot_shiftedJacobi_neg_nat_neg_nat n p q hs (isRoot_of_mem_roots hr)
      have hi : r ∈ Set.Ioo (0 : ℝ) 1 := hloc.resolve_left hr0 |>.resolve_left hr1
      simp only [Multiset.count_add, Multiset.count_filter_of_pos hi]
      simp [Multiset.count_replicate, Ne.symm hr0, Ne.symm hr1]
    · simp [Multiset.count_add, Multiset.count_filter, Multiset.count_replicate,
        Multiset.count_eq_zero.mpr hr, Ne.symm hr0, Ne.symm hr1]
  have hc := congrArg Multiset.card hpart
  simp only [Multiset.card_add, Multiset.card_replicate, hcard] at hc
  dsimp [f] at hc
  lia

end RealRooted
