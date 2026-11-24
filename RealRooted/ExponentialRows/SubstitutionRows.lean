module

public import RealRooted.ExponentialRows.SubstitutionKernel
public import RealRooted.ExponentialRows.ProductInsertion
import RealRooted.Mathlib.RingTheory.PowerSeries.ExponentialSubstitution
import RealRooted.Mathlib.RingTheory.PowerSeries.FiniteSubstitution
import Mathlib.Tactic

/-!
# Substitution of marked series in insertion rows

We identify the generic insertion recurrence with `n! [z^n] exp(A(z) + t B(z))`
for arbitrary zero-constant formal series, then apply the kernel transform
coefficientwise. These identities do not require nonnegative coefficients.

Source: unpublished manuscript (RealRooted issue #2415), Theorem 1,
https://github.com/PerAlexandersson/RealRooted/issues/2415.
-/

@[expose] public section

open Polynomial Finset

namespace RealRooted.ExponentialRows

private theorem constantCoeff_map_C (S : PowerSeries ℝ) :
    PowerSeries.constantCoeff (PowerSeries.map C S) = C (PowerSeries.constantCoeff S) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]

/-- Block weights of `exp(A(z) + t B(z))`, allowing arbitrary formal series. -/
noncomputable def affineBlockWeights (A B : PowerSeries ℝ) (r : ℕ) : ℝ[X] :=
  C ((r.factorial : ℝ) * PowerSeries.coeff r A) +
    C ((r.factorial : ℝ) * PowerSeries.coeff r B) * X

/-- With no marked singleton term, the general affine weights recover the
existing polynomial marked-block interface. -/
theorem affineBlockWeights_X_eq_markedBlockWeights {B : ℝ[X]}
    (hB : B.coeff 1 = 0) :
    affineBlockWeights PowerSeries.X (B : PowerSeries ℝ) = markedBlockWeights B := by
  funext r
  by_cases hr : r = 1
  · subst r
    simp [affineBlockWeights, markedBlockWeights, hB]
  · simp [affineBlockWeights, markedBlockWeights, hr, PowerSeries.coeff_X]

/-- The block-weight exponent is exactly `A(z) + t B(z)`. -/
theorem blockWeightSeries_affineBlockWeights {A B : PowerSeries ℝ}
    (hA : PowerSeries.constantCoeff A = 0) (hB : PowerSeries.constantCoeff B = 0) :
    blockWeightSeries (affineBlockWeights A B) =
      PowerSeries.map C A + PowerSeries.C X * PowerSeries.map C B := by
  apply factorialCoeff_ext
  intro n
  cases n with
  | zero =>
    simp [factorialCoeff, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      constantCoeff_map_C, hA, hB]
  | succ n =>
    rw [factorialCoeff_blockWeightSeries]
    simp only [affineBlockWeights, factorialCoeff, map_add, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_map, map_mul]
    ring

/-- The insertion series separates into the unmarked prefactor and marked kernel. -/
theorem insertionSeries_affineBlockWeights {A B : PowerSeries ℝ}
    (hA : PowerSeries.constantCoeff A = 0) (hB : PowerSeries.constantCoeff B = 0) :
    insertionSeries (affineBlockWeights A B) =
      PowerSeries.map C ((PowerSeries.exp ℝ).subst A) * exponentialKernel B := by
  have hAmap : PowerSeries.constantCoeff (PowerSeries.map C A) = 0 := by
    simp [constantCoeff_map_C, hA]
  have hmap : PowerSeries.map C ((PowerSeries.exp ℝ).subst A) =
      (PowerSeries.exp ℝ[X]).subst (PowerSeries.map C A) := by
    change MvPowerSeries.map C ((PowerSeries.exp ℝ).subst A) = _
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hA),
      PowerSeries.map_exp]
    rfl
  rw [insertionSeries, blockWeightSeries_affineBlockWeights hA hB,
    PowerSeries.subst_exp_add hAmap (constantCoeff_kernelArgument hB), hmap]
  rfl

/-- Nonnegative polynomial block weights give nonnegative insertion rows. -/
theorem hasNonnegCoeffs_insertionRow {w : ℕ → ℝ[X]}
    (hw : ∀ r, HasNonnegCoeffs (w r)) (n : ℕ) :
    HasNonnegCoeffs (insertionRow w n) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero => simpa using hasNonnegCoeffs_one
    | succ n =>
      rw [insertionRow_succ]
      apply hasNonnegCoeffs_finsetSum
      intro k hk
      exact (hasNonnegCoeffs_C_mul (by positivity) (hw _)).mul
        (ih (n - k) (by have := mem_range.mp hk; lia))

/-- Nonnegative unmarked and marked series give nonnegative insertion rows. -/
theorem hasNonnegCoeffs_insertionRow_affineBlockWeights {A B : PowerSeries ℝ}
    (hA : ∀ r, 0 ≤ PowerSeries.coeff r A) (hB : ∀ r, 0 ≤ PowerSeries.coeff r B)
    (n : ℕ) : HasNonnegCoeffs (insertionRow (affineBlockWeights A B) n) := by
  apply hasNonnegCoeffs_insertionRow
  intro r
  exact (hasNonnegCoeffs_C (mul_nonneg (by positivity) (hA r))).add
    (hasNonnegCoeffs_C_mul (mul_nonneg (by positivity) (hB r)) hasNonnegCoeffs_X)


/-- The insertion definition is the literal factorial-scaled formal exponential. -/
theorem insertionRow_affineBlockWeights_eq_exponential {A B : PowerSeries ℝ}
    (hA : PowerSeries.constantCoeff A = 0) (hB : PowerSeries.constantCoeff B = 0) (n : ℕ) :
    insertionRow (affineBlockWeights A B) n =
      factorialCoeff ((PowerSeries.exp ℝ[X]).subst
        (PowerSeries.map C A + PowerSeries.C X * PowerSeries.map C B)) n := by
  rw [insertionRow_eq_factorialCoeff, insertionSeries,
    blockWeightSeries_affineBlockWeights hA hB]

/-- A linear map commutes with formal substitution by a scalar series. -/
private theorem linearMap_coeff_subst (T : ℝ[X] →ₗ[ℝ] ℝ[X])
    (f : PowerSeries ℝ[X]) {B : PowerSeries ℝ}
    (hB : PowerSeries.constantCoeff B = 0) (n : ℕ) :
    T (PowerSeries.coeff n (f.subst (PowerSeries.map C B))) =
      PowerSeries.coeff n
        ((PowerSeries.mk fun k => T (PowerSeries.coeff k f)).subst (PowerSeries.map C B)) := by
  have hBmap : PowerSeries.constantCoeff (PowerSeries.map C B) = 0 := by
    simp [constantCoeff_map_C, hB]
  rw [PowerSeries.coeff_subst_eq_sum_range _ _ hBmap, map_sum,
    PowerSeries.coeff_subst_eq_sum_range _ _ hBmap]
  apply sum_congr rfl
  intro k _
  rw [← map_pow, PowerSeries.coeff_map, PowerSeries.coeff_mk]
  rw [mul_comm _ (C _), Polynomial.linearMap_C_mul, mul_comm]

/-- A linear map commutes with multiplication by a scalar formal series. -/
private theorem linearMap_coeff_scalar_mul (T : ℝ[X] →ₗ[ℝ] ℝ[X])
    (A : PowerSeries ℝ) (f : PowerSeries ℝ[X]) (n : ℕ) :
    T (PowerSeries.coeff n (PowerSeries.map C A * f)) = PowerSeries.coeff n
      (PowerSeries.map C A * PowerSeries.mk fun k => T (PowerSeries.coeff k f)) := by
  rw [PowerSeries.coeff_mul, map_sum, PowerSeries.coeff_mul]
  apply sum_congr rfl
  intro i _
  rw [PowerSeries.coeff_map, Polynomial.linearMap_C_mul, PowerSeries.coeff_mk]

/-- Composing the kernel in its series variable substitutes the marked series. -/
theorem exponentialKernel_subst {B P : PowerSeries ℝ}
    (hB : PowerSeries.constantCoeff B = 0) (hP : PowerSeries.constantCoeff P = 0) :
    (exponentialKernel P).subst (PowerSeries.map C B) = exponentialKernel (P.subst B) := by
  have hBmap : PowerSeries.constantCoeff (PowerSeries.map C B) = 0 := by
    simp [constantCoeff_map_C, hB]
  have hsB := PowerSeries.HasSubst.of_constantCoeff_zero' hBmap
  have hsP := PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_kernelArgument hP)
  have hmap : PowerSeries.map C (P.subst B) =
      (PowerSeries.map C P).subst (PowerSeries.map C B) := by
    change MvPowerSeries.map C (P.subst B) = _
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hB)]
    rfl
  rw [exponentialKernel, PowerSeries.subst_comp_subst_apply hsP hsB]
  rw [PowerSeries.subst_mul hsB, PowerSeries.subst_C, ← hmap]
  rfl

/-- Applying the exponential substitution operator to an affine insertion row
replaces its marked series by `P(B)`, with the same unmarked series. -/
theorem exponentialSubstitution_insertionRow {A B P : PowerSeries ℝ}
    (hA : PowerSeries.constantCoeff A = 0) (hB : PowerSeries.constantCoeff B = 0)
    (hP : PowerSeries.constantCoeff P = 0) (n : ℕ) :
    exponentialSubstitution P (insertionRow (affineBlockWeights A B) n) =
      insertionRow (affineBlockWeights A (P.subst B)) n := by
  have hPB : PowerSeries.constantCoeff (P.subst B) = 0 := by
    rw [PowerSeries.constantCoeff_eq,
      PowerSeries.constantCoeff_subst_of_constantCoeff_zero hB]
    exact hP
  rw [insertionRow_eq_factorialCoeff, insertionRow_eq_factorialCoeff,
    insertionSeries_affineBlockWeights hA hB, insertionSeries_affineBlockWeights hA hPB,
    factorialCoeff, factorialCoeff, Polynomial.linearMap_C_mul]
  congr 1
  rw [linearMap_coeff_scalar_mul (exponentialSubstitution P)
    ((PowerSeries.exp ℝ).subst A) (exponentialKernel B) n]
  have hkernel : (PowerSeries.mk fun k => exponentialSubstitution P
      (PowerSeries.coeff k (exponentialKernel B))) = exponentialKernel (P.subst B) := by
    have hX : exponentialKernel B =
        (exponentialKernel (PowerSeries.X : PowerSeries ℝ)).subst (PowerSeries.map C B) := by
      rw [exponentialKernel_subst hB (by simp),
        PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' hB)]
    rw [hX]
    apply PowerSeries.ext
    intro k
    rw [PowerSeries.coeff_mk, linearMap_coeff_subst _ _ hB,
      exponentialSubstitution_coeff_kernel_X P, exponentialKernel_subst hB hP]
  rw [hkernel]

end RealRooted.ExponentialRows
