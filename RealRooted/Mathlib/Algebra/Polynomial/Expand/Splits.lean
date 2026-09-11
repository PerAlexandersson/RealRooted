module

public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Tactic

public import RealRooted.Mathlib.Algebra.Polynomial.Splits.Complex

@[expose] public section

/-!
# Splitness under squaring expansion

This file records the zero-aware real-root geometry of `Polynomial.expand` at
the squaring map.  A split polynomial whose roots are nonnegative stays split
under this expansion, and splitness of the expansion forces its source roots
to be nonnegative.
-/

open Polynomial

namespace Polynomial

noncomputable section

/-- Expanding a split real polynomial along the squaring map preserves
splitness when every root is nonnegative. -/
theorem splits_expand_two_of_splits_of_forall_roots_nonneg (p : ℝ[X])
    (hp : p.Splits) (hroots : ∀ r ∈ p.roots, 0 ≤ r) :
    (expand ℝ 2 p).Splits := by
  by_cases hp0 : p = 0
  · simp [hp0]
  rw [hp.eq_prod_roots, map_mul, expand_C, map_multiset_prod]
  refine (Splits.C _).mul (Splits.multisetProd ?_)
  rw [Multiset.map_map]
  intro f hf
  rw [Multiset.mem_map] at hf
  obtain ⟨r, hr, rfl⟩ := hf
  change (expand ℝ 2 (X - C r)).Splits
  simp only [expand_eq_comp_X_pow, comp, eval₂_sub, eval₂_X, eval₂_C]
  have hsq : (Real.sqrt r) ^ 2 = r := Real.sq_sqrt (hroots r hr)
  rw [show X ^ 2 - C r = (X - C (Real.sqrt r)) * (X + C (Real.sqrt r)) by
    calc
      X ^ 2 - C r = X ^ 2 - C ((Real.sqrt r) ^ 2) := by rw [hsq]
      _ = (X - C (Real.sqrt r)) * (X + C (Real.sqrt r)) := by
        rw [map_pow]
        ring]
  exact (Splits.X_sub_C _).mul (Splits.X_add_C _)

/-- If the squaring expansion of a real polynomial splits, then the source
polynomial splits and all of its roots are nonnegative. -/
theorem splits_and_forall_roots_nonneg_of_splits_expand_two (p : ℝ[X])
    (h : (expand ℝ 2 p).Splits) :
    p.Splits ∧ ∀ r ∈ p.roots, 0 ≤ r := by
  by_cases hp0 : p = 0
  · simp [hp0]
  constructor
  · apply splits_of_all_roots_real
    intro z hz
    obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq z (by norm_num : 0 < 2)
    have hwroot : ((expand ℝ 2 p).map Complex.ofRealHom).IsRoot w := by
      rw [IsRoot, map_expand, expand_eq_comp_X_pow, eval_comp, eval_pow,
        eval_X, hw]
      exact hz
    obtain ⟨t, ht⟩ := h.mem_range_of_isRoot
      ((expand_ne_zero (by norm_num : 0 < 2)).mpr hp0) hwroot
    rw [← hw, ← ht]
    change ((t : ℂ) ^ 2).im = 0
    rw [← Complex.ofReal_pow]
    exact Complex.ofReal_im _
  · intro r hr
    have hr0 : p.eval r = 0 := (mem_roots hp0).mp hr
    obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (r : ℂ) (by norm_num : 0 < 2)
    have hrc : (p.map Complex.ofRealHom).eval (r : ℂ) = 0 := by
      change (p.map Complex.ofRealHom).eval (Complex.ofRealHom r) = 0
      rw [eval_map, eval₂_hom]
      exact congrArg Complex.ofRealHom hr0
    have hwroot : ((expand ℝ 2 p).map Complex.ofRealHom).IsRoot w := by
      rw [IsRoot, map_expand, expand_eq_comp_X_pow, eval_comp, eval_pow,
        eval_X, hw]
      exact hrc
    obtain ⟨t, ht⟩ := h.mem_range_of_isRoot
      ((expand_ne_zero (by norm_num : 0 < 2)).mpr hp0) hwroot
    have hrt : r = t ^ 2 := by
      apply Complex.ofReal_injective
      rw [← hw, ← ht]
      norm_num
    rw [hrt]
    positivity

/-- If `X` times the squaring expansion of a real polynomial splits, then the
source polynomial splits and all of its roots are nonnegative. -/
theorem splits_and_forall_roots_nonneg_of_splits_X_mul_expand_two (p : ℝ[X])
    (h : (X * expand ℝ 2 p).Splits) :
    p.Splits ∧ ∀ r ∈ p.roots, 0 ≤ r :=
  splits_and_forall_roots_nonneg_of_splits_expand_two p h.of_X_mul

end

end Polynomial
