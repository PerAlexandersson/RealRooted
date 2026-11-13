/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.Polynomial.Roots

/-!
# Additions to Mathlib.Algebra.Polynomial.Roots

This file contains polynomial-root lemmas intended for upstreaming to Mathlib.
-/

public section

open Polynomial

namespace Polynomial

variable {R : Type*} [CommRing R] [IsDomain R]

/-- A root multiplicity is at most the degree of its polynomial. -/
lemma rootMultiplicity_le_natDegree (p : R[X]) (a : R) :
    p.rootMultiplicity a ≤ p.natDegree := by
  classical
  exact (count_roots p).symm.le.trans
    ((Multiset.count_le_card a p.roots).trans (card_roots' p))

/-- Multiplication by a nonzero constant does not change a root multiplicity. -/
lemma rootMultiplicity_C_mul {c a : R} (hc : c ≠ 0) (p : R[X]) :
    (C c * p).rootMultiplicity a = p.rootMultiplicity a := by
  obtain rfl | hp := eq_or_ne p 0
  · simp
  rw [rootMultiplicity_mul (mul_ne_zero (C_ne_zero.mpr hc) hp), rootMultiplicity_C, zero_add]

/-- Multiplying a polynomial by `X` does not change the sum of its roots. -/
@[simp] theorem sum_roots_X_mul (p : R[X]) :
    (X * p).roots.sum = p.roots.sum := by
  by_cases hp : p = 0
  · simp [hp]
  rw [roots_mul (mul_ne_zero X_ne_zero hp), roots_X]
  simp

/-- The number of roots of a composition, counted with multiplicity, is at most
its inner degree times the number of roots of its outer polynomial. -/
theorem card_roots_comp_le {f g : R[X]} (hf : f ≠ 0) (hg : g.natDegree ≠ 0) :
    (f.comp g).roots.card ≤ g.natDegree * f.roots.card := by
  classical
  obtain ⟨q, hfactor, _, hqroots⟩ := exists_prod_multiset_X_sub_C_mul f
  have hq : q ≠ 0 := by
    intro hzero
    simp [hzero] at hfactor
    exact hf hfactor.symm
  have hcomp : f.comp g ≠ 0 := by
    rw [Ne, comp_eq_zero_iff]
    rintro (hzero | ⟨_, hconstant⟩)
    · exact hf hzero
    · exact hg (by rw [hconstant, natDegree_C])
  have hqcomp : (q.comp g).roots = 0 := by
    apply Multiset.eq_zero_of_forall_notMem
    intro x hx
    have hroot : q.IsRoot (g.eval x) := by
      simpa only [IsRoot, eval_comp] using isRoot_of_mem_roots hx
    have hmem := (mem_roots hq).mpr hroot
    simp only [hqroots, Multiset.notMem_zero] at hmem
  have hfactorcomp :
      f.comp g = ((f.roots.map fun a => X - C a).prod).comp g * q.comp g := by
    rw [← mul_comp, hfactor]
  rw [hfactorcomp] at hcomp ⊢
  rw [roots_mul hcomp, hqcomp, add_zero]
  calc
    _ ≤ (((f.roots.map fun a => X - C a).prod).comp g).natDegree := card_roots' _
    _ = g.natDegree * f.roots.card := by
      rw [natDegree_comp, natDegree_multiset_prod_X_sub_C_eq_card, Nat.mul_comm]

end Polynomial
