import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Splits

/-!
# Roots of reversed polynomials

Root transport for `Polynomial.reverse`, including the zero-root case omitted
by the usual nonzero-constant-coefficient formulation.
-/

open Finset

noncomputable section

namespace Polynomial

variable {K : Type*} [Field K]

local instance : DecidableEq K := Classical.decEq K

/-- The reversal of a nonzero monic linear factor is a nonzero scalar times
the monic factor at the inverse root. -/
theorem reverse_X_sub_C_eq (r : K) (hr : r ≠ 0) :
    (X - C r : K[X]).reverse = C (-r) * (X - C r⁻¹) := by
  ext n
  rcases n with _ | _ | n <;>
    simp [Polynomial.reverse, Polynomial.coeff_one, Polynomial.coeff_X,
      Polynomial.coeff_C, hr]

/-- Reversal of a nonzero monic linear factor has the inverse root. -/
theorem roots_reverse_X_sub_C (r : K) (hr : r ≠ 0) :
    (X - C r : K[X]).reverse.roots = {r⁻¹} := by
  rw [reverse_X_sub_C_eq r hr, Polynomial.roots_C_mul]
  · simp
  · grind

private theorem reverse_prod_X_sub_C_ne_zero (s : Multiset K) :
    ((s.map fun r => (X - C r : K[X])).prod).reverse ≠ 0 := by
  rw [Ne, Polynomial.reverse_eq_zero]
  refine Multiset.prod_ne_zero ?_
  rw [Multiset.mem_map]
  rintro ⟨r, -, hr⟩
  exact X_sub_C_ne_zero r (by assumption)

private theorem roots_reverse_prod_X_sub_C (s : Multiset K) :
    ((s.map fun r => (X - C r : K[X])).prod).reverse.roots =
      (s.filter fun r => r ≠ 0).map (·⁻¹) := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp [Polynomial.reverse]
  | cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, Polynomial.reverse_mul_of_domain]
      by_cases ha : a = 0
      · simp_all [Polynomial.reverse]
      · rw [Multiset.filter_cons_of_pos (p := fun r ↦ r ≠ 0) s ha, Multiset.map_cons]
        have hleft : (X - C a : K[X]).reverse ≠ 0 := by
          rw [reverse_X_sub_C_eq a ha]
          exact mul_ne_zero (Polynomial.C_ne_zero.mpr (neg_ne_zero.mpr ha))
            (Polynomial.X_sub_C_ne_zero a⁻¹)
        rw [Polynomial.roots_mul (mul_ne_zero hleft (reverse_prod_X_sub_C_ne_zero s)),
          roots_reverse_X_sub_C a ha, ih]
        simp

/-- If `p` splits over a field, the roots of `p.reverse` are the inverses of
the nonzero roots of `p`, retaining multiplicity. -/
theorem roots_reverse_eq_filter_map_inv {p : K[X]}
    (hp_ne : p ≠ 0) (hp_splits : p.Splits) :
    p.reverse.roots = (p.roots.filter fun r => r ≠ 0).map (·⁻¹) := by
  classical
  have hlead : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp_ne
  conv_lhs => rw [Polynomial.Splits.eq_prod_roots hp_splits]
  rw [Polynomial.reverse_mul_of_domain, Polynomial.reverse_C,
    Polynomial.roots_C_mul _ hlead, roots_reverse_prod_X_sub_C]

end Polynomial
