import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Splits

/-!
# Reversal toolkit for degree-drop root-continuity

This file collects algebraic facts about `Polynomial.reverse` used by the
degree-drop endpoint behind issue #42.  The analytic endpoint concerns a family
`f + C μ * g` whose degree drops as `μ → 0`; after reversal, roots escaping to
infinity become ordinary roots near zero.
-/

open Polynomial

namespace RealRooted.DegreeDropReversal

variable {K : Type*} [Field K]

/-- Reversal sends a monic linear factor `X + C a` to a polynomial that still
splits. -/
theorem splits_reverse_X_add_C (a : K) :
    (X + C a).reverse.Splits :=
  Polynomial.Splits.of_natDegree_le_one <|
    (Polynomial.reverse_natDegree_le (X + C a)).trans <| by
      rw [Polynomial.natDegree_X_add_C]

/-- Reversal preserves `Splits` over a field. -/
theorem splits_reverse {p : K[X]} (h : p.Splits) :
    p.reverse.Splits := by
  induction h using Submonoid.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · simp
    · exact splits_reverse_X_add_C a
  | one =>
    exact Polynomial.Splits.of_natDegree_le_one <|
      (Polynomial.reverse_natDegree_le (1 : K[X])).trans <| by simp
  | mul x y _ _ ihx ihy =>
    rw [Polynomial.reverse_mul_of_domain]
    exact ihx.mul ihy

set_option linter.flexible false in
/-- Reflecting a polynomial at a degree `N` at least its own `natDegree` factors
a power of `X` out of its reversal. -/
theorem reflect_eq_X_pow_mul_reverse {R : Type*} [Semiring R] (f : R[X]) {N : ℕ}
    (hN : f.natDegree ≤ N) :
    reflect N f = X ^ (N - f.natDegree) * f.reverse := by
  ext n
  by_cases hn : n ≤ N <;> by_cases hNn : n ≥ N - f.natDegree <;>
    simp_all +decide [Polynomial.coeff_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_reverse]
  · rw [Finset.sum_eq_single (N - f.natDegree, n - (N - f.natDegree))] <;>
      simp_all +decide [Finset.mem_antidiagonal, revAt]
    · grind
    · lia
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by lia)]
    exact Eq.symm (Finset.sum_eq_zero fun x hx => if_neg (by
      linarith [Finset.mem_antidiagonal.mp hx,
        Nat.sub_add_cancel (by linarith : f.natDegree ≤ N)]))
  · rw [Finset.sum_eq_single (N - f.natDegree, n - (N - f.natDegree))] <;>
      simp_all +decide [revAt]
    · rw [if_neg hn.not_ge, if_neg hn.not_ge, Polynomial.coeff_eq_zero_of_natDegree_lt]
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by lia)]
      · linarith
    · lia
  · linarith

end RealRooted.DegreeDropReversal
