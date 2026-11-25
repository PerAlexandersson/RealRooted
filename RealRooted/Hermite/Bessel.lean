module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Basic.Real.Basic
import RealRooted.Hermite.Poulain
import RealRooted.Hermite.BesselOperatorFamily

/-!
# The Bessel differential transform

We identify the finite action of the Bessel symbol `J₀(2D)` with the
`lambda = 1`, `r = 0` instance of the finite Bessel operator family. The
real-rootedness theorem follows from that general preservation result.
-/

@[expose] public section

open Finset Polynomial

noncomputable section

namespace RealRooted.HermitePoulain

private theorem splits_derivative_sub {p : ℝ[X]} (hp : p.Splits) (r : ℝ) :
    (derivative p - C r * p).Splits := by
  by_cases hp0 : p = 0
  · simp [hp0]
  have hs := applyAsDifferentialOperator_eq_zero_or_splits
    (f := X + C (-r)) (g := p)
    ⟨(monic_X_add_C (-r)).ne_zero, Splits.X_add_C (-r)⟩ ⟨hp0, hp⟩
  rw [applyAsDifferentialOperator_X_add_C] at hs
  rcases hs with hs | hs
  · rw [show derivative p - C r * p = 0 by simpa [sub_eq_add_neg] using hs]
    exact Splits.zero
  · simpa [sub_eq_add_neg] using hs

/-- The constant-coefficient operator `c D²`. -/
def sqDifferentialOperator (c : ℝ) : Module.End ℝ ℝ[X] :=
  c • ((derivative : Module.End ℝ ℝ[X]) * derivative)

private theorem splits_sq_sub {q : ℝ[X]} (hq : q.Splits) {c a : ℝ}
    (hc : 0 < c) (ha : 0 ≤ a) :
    (c • derivative (derivative q) - a • q).Splits := by
  set s := Real.sqrt (a / c)
  have hs : c * s ^ 2 = a := by
    rw [Real.sq_sqrt (div_nonneg ha hc.le)]
    field_simp
  have h := splits_derivative_sub (splits_derivative_sub hq (-s)) s
  have heq :
      c • derivative (derivative q) - a • q =
        C c * (derivative (derivative q - C (-s) * q) -
          C s * (derivative q - C (-s) * q)) := by
    simp only [derivative_sub, derivative_mul, derivative_C, smul_eq_C_mul,
      ← hs, map_mul, map_pow, map_neg]
    ring
  rw [heq]
  exact h.C_mul c

private theorem aeval_sqDifferentialOperator_prod_splits
    (s : Multiset ℝ) (hr : ∀ r ∈ s, 0 ≤ r) {c : ℝ} (hc : 0 < c)
    {p : ℝ[X]} (hp : p.Splits) :
    ((aeval (sqDifferentialOperator c) (s.map (X - C ·)).prod :
      Module.End ℝ ℝ[X]) p).Splits := by
  induction s using Multiset.induction_on with
  | empty => simpa using hp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, map_mul, mul_apply_eq_comp]
    simpa [sqDifferentialOperator, Module.algebraMap_end_apply] using
      splits_sq_sub (ih (fun r hr' => hr r (Multiset.mem_cons_of_mem hr'))) hc
        (hr a (Multiset.mem_cons_self _ _))

/-- If `L` has only nonnegative real roots, then the Laguerre--Pólya operator
`L(c D²)` preserves real-rootedness for `c > 0`.

The proof was found by Aristotle (Harmonic). -/
theorem aeval_sqDifferentialOperator_splits {L : ℝ[X]} (hL : L.Splits)
    (hr : ∀ r ∈ L.roots, 0 ≤ r) {c : ℝ} (hc : 0 < c)
    {p : ℝ[X]} (hp : p.Splits) :
    ((aeval (sqDifferentialOperator c) L : Module.End ℝ ℝ[X]) p).Splits := by
  rw [hL.eq_prod_roots, map_mul, aeval_C, mul_apply_eq_comp,
    Module.algebraMap_end_apply, smul_eq_C_mul]
  exact (aeval_sqDifferentialOperator_prod_splits _ hr hc hp).C_mul _

/-- The finite action of the Bessel symbol
`J₀(2D) = ∑ k, (-1)^k D^(2*k)/(k!)²` on a polynomial. -/
def besselDifferentialTransform (p : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ range (p.natDegree / 2 + 1),
    C ((-1 : ℝ) ^ k / (Nat.factorial k : ℝ) ^ 2) * derivative^[2 * k] p

/-- The Bessel differential transform `J₀(2D)` sends every real-rooted
real polynomial to a real-rooted polynomial, as a finite Bessel operator.

The original approximation proof was found by Aristotle (Harmonic). -/
theorem besselDifferentialTransform_splits {p : ℝ[X]} (hp : p.Splits) :
    (besselDifferentialTransform p).Splits := by
  have heq : besselDifferentialTransform p = besselOperator 1 0 p := by
    ext j
    rw [besselDifferentialTransform, finsetSum_coeff, coeff_besselOperator]
    simp only [coeff_C_mul, coeff_iterate_derivative, nsmul_eq_mul, add_zero,
      pow_two, mul_assoc]
    apply Finset.sum_subset (range_subset_range.mpr (by lia))
    intro k _ hk
    simp only [mem_range] at hk
    rw [coeff_eq_zero_of_natDegree_lt (by lia), mul_zero, mul_zero]
  rw [heq]
  exact besselOperator_splits (by norm_num) 0 hp

end RealRooted.HermitePoulain
