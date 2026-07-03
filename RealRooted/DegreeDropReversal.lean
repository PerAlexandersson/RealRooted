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

/-- Reflection is linear on a polynomial family `f + C μ * g`. -/
theorem reflect_add_C_mul {R : Type*} [Semiring R] (f g : R[X]) (μ : R) (N : ℕ) :
    reflect N (f + C μ * g) = reflect N f + C μ * reflect N g := by
  rw [Polynomial.reflect_add, Polynomial.reflect_C_mul]

/-- Degree-padded reversal form of a reflected affine polynomial family. -/
theorem reflect_add_C_mul_eq_X_pow_mul_reverse_add_C_mul_X_pow_mul_reverse
    {R : Type*} [Semiring R] (f g : R[X]) (μ : R) {N : ℕ}
    (hfN : f.natDegree ≤ N) (hgN : g.natDegree ≤ N) :
    reflect N (f + C μ * g) =
      X ^ (N - f.natDegree) * f.reverse + C μ * (X ^ (N - g.natDegree) * g.reverse) := by
  rw [reflect_add_C_mul, reflect_eq_X_pow_mul_reverse f hfN,
    reflect_eq_X_pow_mul_reverse g hgN]

/-- When `g` has the reflecting degree exactly, the reflected family has only
the lower-degree member padded by a power of `X`. -/
theorem reflect_add_C_mul_eq_X_pow_mul_reverse_add_C_mul_reverse
    (f g : K[X]) (μ : K) {N : ℕ} (hfN : f.natDegree ≤ N) (hgN : g.natDegree = N) :
    reflect N (f + C μ * g) = X ^ (N - f.natDegree) * f.reverse + C μ * g.reverse := by
  rw [reflect_add_C_mul_eq_X_pow_mul_reverse_add_C_mul_X_pow_mul_reverse f g μ hfN
    (le_of_eq hgN)]
  simp [hgN]

/-- Multiplying the reverse of a split polynomial by the degree-padding power
of `X` still splits. -/
theorem splits_X_pow_mul_reverse {p : K[X]} (h : p.Splits) (N : ℕ) :
    (X ^ (N - p.natDegree) * p.reverse).Splits :=
  (Polynomial.Splits.X_pow (N - p.natDegree)).mul (splits_reverse h)

/-- Reflection at any degree at least `p.natDegree` preserves splitting. -/
theorem splits_reflect_of_splits {p : K[X]} (h : p.Splits) {N : ℕ}
    (hN : p.natDegree ≤ N) :
    (reflect N p).Splits := by
  rw [reflect_eq_X_pow_mul_reverse p hN]
  exact splits_X_pow_mul_reverse h N

end RealRooted.DegreeDropReversal
