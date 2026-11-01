module

public import RealRooted.CombinatorialExamples.Touchard
public import RealRooted.Mathlib.Algebra.Polynomial.Reverse
import RealRooted.Basic.AffineInterlacing
import RealRooted.Interlacing.Reversal
import RealRooted.Recurrence.Uniqueness
import RealRooted.WagnerX.NonnegativeRoots

/-!
# Translated and reflected Touchard recurrences

This module identifies two first-order derivative recurrences with affine and
reciprocal images of the Touchard polynomials.  The identifications transfer
interlacing, splitting, coefficient signs, and root regions from the canonical
Touchard family.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- A family with the translated Touchard recurrence is the corresponding
translation of the Touchard family. -/
theorem eq_touchard_comp_X_add_C_of_recurrence
    {P : ℕ → ℝ[X]} (r : ℝ)
    (hzero : P 0 = 1)
    (hrec : ∀ n : ℕ,
      P (n + 1) = (X + C r) * (P n + (P n).derivative))
    (n : ℕ) :
    P n = (touchard n).comp (X + C r) := by
  let Q : ℕ → ℝ[X] := fun m ↦ (touchard m).comp (X + C r)
  have hQzero : Q 0 = 1 := by
    simp [Q, touchard_zero]
  have hQrec : ∀ m : ℕ,
      Q (m + 1) = (X + C r) * (Q m + (Q m).derivative) := by
    intro m
    simp only [Q, touchard_succ, mul_comp, X_comp, add_comp,
      Polynomial.derivative_comp, derivative_add, derivative_X, derivative_C,
      add_zero]
    ring_nf
  exact sequence_eq_of_same_lag_one_recurrence
    (fun _ p ↦ (X + C r) * (p + p.derivative))
    (hzero.trans hQzero.symm) hrec hQrec n

/-- Consecutive rows of a translated Touchard recurrence interlace. -/
theorem interlaces_of_touchard_comp_X_add_C_recurrence
    {P : ℕ → ℝ[X]} (r : ℝ)
    (hzero : P 0 = 1)
    (hrec : ∀ n : ℕ,
      P (n + 1) = (X + C r) * (P n + (P n).derivative))
    (n : ℕ) :
    Interlaces (P n) (P (n + 1)) := by
  rw [eq_touchard_comp_X_add_C_of_recurrence r hzero hrec n,
    eq_touchard_comp_X_add_C_of_recurrence r hzero hrec (n + 1)]
  exact interlaces_comp_X_add_C (interlaces_touchard_succ n) r

/-- Every row of a translated Touchard recurrence splits over the reals. -/
theorem splits_of_touchard_comp_X_add_C_recurrence
    {P : ℕ → ℝ[X]} (r : ℝ)
    (hzero : P 0 = 1)
    (hrec : ∀ n : ℕ,
      P (n + 1) = (X + C r) * (P n + (P n).derivative))
    (n : ℕ) :
    (P n).Splits := by
  rw [eq_touchard_comp_X_add_C_of_recurrence r hzero hrec n]
  exact (isRealRooted_touchard n).2.comp_X_add_C r

/-- Every root in row `n` of a translated Touchard recurrence is at most
`-r`. -/
theorem roots_le_neg_of_touchard_comp_X_add_C_recurrence
    {P : ℕ → ℝ[X]} (r : ℝ)
    (hzero : P 0 = 1)
    (hrec : ∀ n : ℕ,
      P (n + 1) = (X + C r) * (P n + (P n).derivative))
    (n : ℕ) :
    ∀ x ∈ (P n).roots, x ≤ -r := by
  intro x hx
  rw [eq_touchard_comp_X_add_C_of_recurrence r hzero hrec n,
    roots_comp_X_add_C] at hx
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
  have := roots_nonpos_touchard_of_isRealRooted y hy
  linarith

/-- Every row of a translated Touchard recurrence is monic. -/
theorem monic_of_touchard_comp_X_add_C_recurrence
    {P : ℕ → ℝ[X]} (r : ℝ)
    (hzero : P 0 = 1)
    (hrec : ∀ n : ℕ,
      P (n + 1) = (X + C r) * (P n + (P n).derivative))
    (n : ℕ) :
    (P n).Monic := by
  rw [eq_touchard_comp_X_add_C_of_recurrence r hzero hrec n]
  exact (monic_touchard n).comp_X_add_C r

/-- A nonnegatively translated Touchard recurrence has nonnegative
coefficients. -/
theorem hasNonnegCoeffs_of_touchard_comp_X_add_C_recurrence
    {P : ℕ → ℝ[X]} {r : ℝ} (hr : 0 ≤ r)
    (hzero : P 0 = 1)
    (hrec : ∀ n : ℕ,
      P (n + 1) = (X + C r) * (P n + (P n).derivative))
    (n : ℕ) :
    HasNonnegCoeffs (P n) := by
  rw [eq_touchard_comp_X_add_C_of_recurrence r hzero hrec n]
  exact hasNonnegCoeffs_comp_X_add_C_of_roots_le
    (touchard_posLeadingCoeff n) (isRealRooted_touchard n).2
    (fun x hx ↦ (roots_nonpos_touchard_of_isRealRooted x hx).trans hr)

/-- A family satisfying the reciprocal Touchard recurrence is the reflection
of the Touchard family at its ambient index. -/
theorem eq_reflect_touchard_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hrec : ∀ n : ℕ,
      P (n + 1) = (1 + C (n : ℝ) * X) * P n - X ^ 2 * (P n).derivative)
    (n : ℕ) :
    P n = reflect n (touchard n) := by
  have hmodel : ∀ m : ℕ, P m = reflect (0 + m) (touchard m) := by
    apply eq_reflect_of_secondOrderDerivativeRecurrence
      (P := P) (R := touchard) (D₀ := 0)
      (A₂ := fun _ ↦ 0) (A₁ := fun _ ↦ -X ^ 2)
      (A₀ := fun m ↦ 1 + C (m : ℝ) * X)
      (B₂ := fun _ ↦ 0) (B₁ := fun _ ↦ X) (B₀ := fun _ ↦ X)
    · intro m
      rw [hrec]
      ring
    · intro m
      rw [touchard_succ]
      ring
    · intro m
      simp
    · intro m
      compute_degree!
    · intro m
      compute_degree!
    · intro m
      simp
    · intro m
      simp [Polynomial.reflect_neg]
    · intro m
      have hlinear : reflect 1 (1 + C (m : ℝ) * X) = C (m : ℝ) + X := by
        rw [Polynomial.reflect_add]
        have hm : reflect 1 (C (m : ℝ) * X) = C (m : ℝ) := by
          rw [show X = X ^ 1 by simp, Polynomial.reflect_C_mul_X_pow]
          norm_num
        rw [hm]
        simp
        ring
      rw [hlinear]
      simp [Polynomial.reflect_neg]
    · intro m
      rw [natDegree_touchard]
      simp
    · simpa [touchard_zero] using hzero
  simpa using hmodel n

/-- Every row of a reciprocal Touchard recurrence splits over the reals. -/
theorem splits_of_reflect_touchard_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hrec : ∀ n : ℕ,
      P (n + 1) = (1 + C (n : ℝ) * X) * P n - X ^ 2 * (P n).derivative)
    (n : ℕ) :
    (P n).Splits := by
  rw [eq_reflect_touchard_of_recurrence hzero hrec n]
  exact Polynomial.Splits.reflect (isRealRooted_touchard n).2
    (natDegree_touchard n).le

/-- A reciprocal Touchard recurrence has nonnegative coefficients. -/
theorem hasNonnegCoeffs_of_reflect_touchard_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hrec : ∀ n : ℕ,
      P (n + 1) = (1 + C (n : ℝ) * X) * P n - X ^ 2 * (P n).derivative)
    (n : ℕ) :
    HasNonnegCoeffs (P n) := by
  rw [eq_reflect_touchard_of_recurrence hzero hrec n]
  exact (touchard_nonnegCoeffs n).reflect n

/-- Every root of a reciprocal Touchard recurrence is nonpositive. -/
theorem roots_nonpos_of_reflect_touchard_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hrec : ∀ n : ℕ,
      P (n + 1) = (1 + C (n : ℝ) * X) * P n - X ^ 2 * (P n).derivative)
    (n : ℕ) :
    ∀ x ∈ (P n).roots, x ≤ 0 := by
  exact roots_nonpos_of_hasNonnegCoeffs
    (hasNonnegCoeffs_of_reflect_touchard_recurrence hzero hrec n)

/-- Every reciprocal Touchard row has constant coefficient one. -/
theorem coeff_zero_eq_one_of_reflect_touchard_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hrec : ∀ n : ℕ,
      P (n + 1) = (1 + C (n : ℝ) * X) * P n - X ^ 2 * (P n).derivative)
    (n : ℕ) :
    (P n).coeff 0 = 1 := by
  rw [eq_reflect_touchard_of_recurrence hzero hrec n, Polynomial.coeff_reflect,
    Polynomial.revAt_le (Nat.zero_le n), Nat.sub_zero,
    coeff_touchard_eq_stirlingSecond, Nat.stirlingSecond_self]
  norm_num

/-- The positive-index reciprocal Touchard row `n + 1` has degree `n`. -/
theorem natDegree_eq_of_reflect_touchard_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hrec : ∀ n : ℕ,
      P (n + 1) = (1 + C (n : ℝ) * X) * P n - X ^ 2 * (P n).derivative)
    (n : ℕ) :
    (P (n + 1)).natDegree = n := by
  rw [eq_reflect_touchard_of_recurrence hzero hrec (n + 1)]
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [Polynomial.coeff_reflect]
    by_cases hkn : k ≤ n + 1
    · have hk_eq : k = n + 1 := by lia
      subst k
      simp [coeff_touchard_eq_stirlingSecond]
    · rw [Polynomial.revAt_eq_self_of_lt (by lia),
        Polynomial.coeff_eq_zero_of_natDegree_lt]
      rw [natDegree_touchard]
      lia
  · rw [Polynomial.coeff_reflect, Polynomial.revAt_le (by lia),
      show n + 1 - n = 1 by lia, coeff_touchard_eq_stirlingSecond,
      Nat.stirlingSecond_one_right]
    norm_num

/-- Every positive-index reciprocal Touchard row is monic. -/
theorem monic_of_reflect_touchard_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hrec : ∀ n : ℕ,
      P (n + 1) = (1 + C (n : ℝ) * X) * P n - X ^ 2 * (P n).derivative)
    (n : ℕ) :
    (P (n + 1)).Monic := by
  rw [Polynomial.Monic.def, Polynomial.leadingCoeff,
    natDegree_eq_of_reflect_touchard_recurrence hzero hrec n,
    eq_reflect_touchard_of_recurrence hzero hrec (n + 1),
    Polynomial.coeff_reflect, Polynomial.revAt_le (by lia),
    show n + 1 - n = 1 by lia, coeff_touchard_eq_stirlingSecond,
    Nat.stirlingSecond_one_right]
  norm_num

end RealRooted
