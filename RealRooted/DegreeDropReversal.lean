import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Polynomial.FieldDivision

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

/-- If the constant coefficient is nonzero, reflecting at any degree bound
puts a nonzero coefficient in the top reflected degree. -/
theorem natDegree_reflect_eq_of_coeff_zero_ne {R : Type*} [Semiring R]
    {p : R[X]} {N : ℕ} (hN : p.natDegree ≤ N) (h0 : p.coeff 0 ≠ 0) :
    (reflect N p).natDegree = N := by
  refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
  · exact Polynomial.natDegree_reflect_le.trans <| by rw [max_eq_left hN]
  · simpa [Polynomial.revAt_le le_rfl] using h0

/-- Under the same hypotheses, the leading coefficient of the reflected
polynomial is the original constant coefficient. -/
theorem leadingCoeff_reflect_eq_coeff_zero_of_natDegree_le {R : Type*} [Semiring R]
    {p : R[X]} {N : ℕ} (hN : p.natDegree ≤ N) (h0 : p.coeff 0 ≠ 0) :
    (reflect N p).leadingCoeff = p.coeff 0 := by
  rw [Polynomial.leadingCoeff, natDegree_reflect_eq_of_coeff_zero_ne hN h0]
  simp

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

/-- Degree-padded reversal form of a reflected affine polynomial family, when
the second member has exactly the reflecting degree. -/
theorem reflect_add_C_mul_eq_X_pow_reverse_add_C_mul_reverse
    {R : Type*} [Semiring R] (f g : R[X]) (μ : R) {N : ℕ}
    (hfN : f.natDegree ≤ N) (hgN : g.natDegree = N) :
    reflect N (f + C μ * g) = X ^ (N - f.natDegree) * f.reverse + C μ * g.reverse := by
  rw [reflect_add_C_mul_eq_X_pow_mul_reverse_add_C_mul_X_pow_mul_reverse f g μ hfN
    (le_of_eq hgN)]
  simp [hgN]

/-- Multiplying the reverse of a split polynomial by the degree-padding power
of `X` still splits. -/
theorem splits_X_pow_mul_reverse {p : K[X]} (h : p.Splits) (N : ℕ) :
    (X ^ (N - p.natDegree) * p.reverse).Splits :=
  (Polynomial.Splits.X_pow (N - p.natDegree)).mul (splits_reverse h)

/-- Interface-shaped version of `splits_X_pow_mul_reverse`; the degree bound is
not needed for the proof but is often available at call sites. -/
theorem splits_X_pow_mul_reverse_of_splits {p : K[X]} (h : p.Splits) {N : ℕ}
    (_hN : p.natDegree ≤ N) :
    (X ^ (N - p.natDegree) * p.reverse).Splits :=
  splits_X_pow_mul_reverse h N

/-- Reflection at any degree at least `p.natDegree` preserves splitting. -/
theorem splits_reflect_of_splits {p : K[X]} (h : p.Splits) {N : ℕ}
    (hN : p.natDegree ≤ N) :
    (reflect N p).Splits := by
  rw [reflect_eq_X_pow_mul_reverse p hN]
  exact splits_X_pow_mul_reverse_of_splits h hN

/-- For polynomials of degree at most `N`, reflection preserves and reflects
splitting. -/
theorem splits_reflect_iff {p : K[X]} {N : ℕ} (hN : p.natDegree ≤ N) :
    (reflect N p).Splits ↔ p.Splits := by
  refine ⟨?_, fun h => splits_reflect_of_splits h hN⟩
  intro h
  have hreflect_deg : (reflect N p).natDegree ≤ N :=
    Polynomial.natDegree_reflect_le.trans <| by rw [max_eq_left hN]
  simpa using splits_reflect_of_splits h hreflect_deg

/-- Reversal preserves and reflects splitting over a field. -/
theorem splits_reverse_iff {p : K[X]} :
    p.reverse.Splits ↔ p.Splits := by
  simpa [Polynomial.reverse] using
    (splits_reflect_iff (p := p) (N := p.natDegree) le_rfl)

/-- If the reverse of a polynomial splits, then the original polynomial splits. -/
theorem splits_of_reverse {p : K[X]} (h : p.reverse.Splits) :
    p.Splits :=
  splits_reverse_iff.mp h

/-- Multiplying by a power of `X` does not change whether a polynomial splits. -/
theorem splits_X_pow_mul_iff {p : K[X]} (k : ℕ) :
    (X ^ k * p).Splits ↔ p.Splits :=
  Polynomial.splits_mul_iff_right (pow_ne_zero k Polynomial.X_ne_zero)
    (Polynomial.Splits.X_pow k)

/-- Multiplying by one factor of `X` does not change whether a polynomial
splits. -/
theorem splits_X_mul_iff {p : K[X]} : (X * p).Splits ↔ p.Splits := by
  rw [← pow_one (X : K[X])]
  exact splits_X_pow_mul_iff (p := p) 1

/-- A polynomial with zero constant coefficient is `X` times its `divX`
quotient. -/
theorem eq_X_mul_divX_of_coeff_zero {p : K[X]} (h0 : p.coeff 0 = 0) :
    p = X * p.divX := by
  have h := Polynomial.X_mul_divX_add p
  rw [h0, Polynomial.C_0, add_zero] at h
  exact h.symm

/-- If the constant coefficient is zero, splitting is equivalent to splitting
after dividing by `X`. -/
theorem splits_iff_divX_splits_of_coeff_zero {p : K[X]} (h0 : p.coeff 0 = 0) :
    p.Splits ↔ p.divX.Splits := by
  conv_lhs => rw [eq_X_mul_divX_of_coeff_zero h0]
  exact splits_X_mul_iff (p := p.divX)

/-- If the constant coefficient is zero, splitting of `p.divX` lifts back to
splitting of `p`. -/
theorem splits_of_divX_splits_of_coeff_zero {p : K[X]} (h0 : p.coeff 0 = 0)
    (hdiv : p.divX.Splits) : p.Splits :=
  (splits_iff_divX_splits_of_coeff_zero h0).2 hdiv

/-- The reflected degree-padded family splits if and only if the original
family splits. -/
theorem splits_reflected_family_iff {a b : K} {f g : K[X]} {N : ℕ}
    (hfN : f.natDegree ≤ N) (hgN : g.natDegree = N) :
    (C a * (X ^ (N - f.natDegree) * f.reverse) + C b * g.reverse).Splits ↔
      (C a * f + C b * g).Splits := by
  have hle : (C a * f + C b * g).natDegree ≤ N :=
    (Polynomial.natDegree_add_le _ _).trans <|
      max_le
        ((Polynomial.natDegree_C_mul_le a f).trans hfN)
        ((Polynomial.natDegree_C_mul_le b g).trans hgN.le)
  have hreflect :
      reflect N (C a * f + C b * g) =
        C a * (X ^ (N - f.natDegree) * f.reverse) + C b * g.reverse := by
    rw [Polynomial.reflect_add, Polynomial.reflect_C_mul, Polynomial.reflect_C_mul,
      reflect_eq_X_pow_mul_reverse f hfN, reflect_eq_X_pow_mul_reverse g hgN.le]
    simp [hgN]
  rw [← hreflect]
  exact splits_reflect_iff hle

end RealRooted.DegreeDropReversal
