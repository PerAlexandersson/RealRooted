/-
Copyright (c) 2026 The RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The RealRooted contributors
-/
module

public import RealRooted.PFPolynomial
public import Mathlib.Analysis.Complex.Basic
import RealRooted.Mathlib.Analysis.Complex.LinearProductFinite


/-!
# Normalized PF polynomials and finite-support linear products
-/

public section

open Polynomial Complex

namespace RealRooted

/-- A finitely supported nonnegative family of linear slopes is exactly a
real PF polynomial with constant coefficient one, evaluated over the complex numbers. -/
theorem exists_isPFPolynomial_eval_eq_tprod {a : ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hs : (Function.support a).Finite) :
    ∃ p : ℝ[X], IsPFPolynomial p ∧ p.coeff 0 = 1 ∧
      ∀ z : ℂ, (p.map ofRealHom).eval z = ∏' i, (1 + (a i : ℂ) * z) := by
  classical
  let s := hs.toFinset
  let p : ℝ[X] := ∏ i ∈ s, (1 + C (a i) * X)
  have hp : IsPFPolynomial p := by
    apply Finset.prod_induction _ IsPFPolynomial (fun _ _ => IsPFPolynomial.mul)
      IsPFPolynomial.one
    intro i hi
    have hai : 0 < a i := lt_of_le_of_ne (ha i)
      (Ne.symm (hs.mem_toFinset.mp hi))
    simpa only [C_0, sub_zero, C_1, add_comm] using
      IsPFPolynomial.C_mul_X_add_C_sub_C hai zero_le_one (le_refl (0 : ℝ))
  refine ⟨p, hp, ?_, fun z => ?_⟩
  · simp only [p, coeff_zero_eq_eval_zero, eval_prod, eval_add, eval_one,
      eval_mul, eval_C, eval_X, mul_zero, add_zero, Finset.prod_const_one]
  · rw [tprod_eq_prod (s := s) (fun i hi => by
      have hai : a i = 0 := by
        by_contra hne
        exact hi (hs.mem_toFinset.mpr hne)
      simp only [hai, ofReal_zero, zero_mul, add_zero])]
    simp only [p, Polynomial.map_prod, Polynomial.map_add, Polynomial.map_one,
      Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, eval_prod, eval_add,
      eval_one, eval_mul, eval_C, eval_X, ofRealHom_eq_coe]

/-- A normalized PF polynomial has an exact finitely supported nonnegative
linear-product representation, with multiplicities retained. -/
theorem IsPFPolynomial.exists_finite_support_tprod {p : ℝ[X]}
    (hp : IsPFPolynomial p) (h0 : p.coeff 0 = 1) :
    ∃ a : ℕ → ℝ, (∀ i, 0 ≤ a i) ∧ (Function.support a).Finite ∧
      ∀ z : ℂ, (p.map ofRealHom).eval z = ∏' i, (1 + (a i : ℂ) * z) := by
  classical
  obtain ⟨s, hs, -, hprod⟩ := hp.exists_pos_multiset_prod_one_add_C_mul_X h0
  let I := s.toEnumFinset
  have hpos (i : I) : 0 ≤ i.val.1 :=
    (hs i.val.1 (Multiset.mem_of_mem_toEnumFinset i.property)).le
  obtain ⟨a, ha, hfin, heq⟩ :=
    Complex.exists_finite_support_tprod_eq_prod (fun i : I => i.val.1) hpos
  refine ⟨a, ha, hfin, fun z => ?_⟩
  rw [heq, hprod, Multiset.prod_map_eq_prod_toEnumFinset]
  simp only [Polynomial.map_prod, Polynomial.map_add, Polynomial.map_one,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, eval_prod, eval_add,
    eval_one, eval_mul, eval_C, eval_X, ofRealHom_eq_coe]
  exact (Finset.prod_attach _ _).symm

end RealRooted
