import RealRooted.Applications.OEIS.InversePeaks
import RealRooted.DerivativeRecurrence.QuadraticSeed
import RealRooted.GammaPencil.Intertwining
import RealRooted.GammaTransform.RootMap

/-!
# Denominator-free type-B lift of the inverse-peak recurrence

We scale the inverse-peak gamma polynomial by four and apply the gamma
transform in ambient degree `m + 1`.  This is the polynomial represented by
the usual rational-substitution display.  No type-B or left-peak
combinatorial interpretation is asserted here.
-/

open Polynomial

noncomputable section

namespace RealRooted.Applications.OEIS

/-- The inverse-peak gamma polynomial after the substitution `X ↦ 4X`. -/
def scaledInversePeakGamma (m : ℕ) : ℝ[X] :=
  (inversePeakEulerian m).comp (C 4 * X)

/-- The denominator-free type-B lift in ambient degree `m + 1`. -/
def inversePeakTypeB (m : ℕ) : ℝ[X] :=
  gammaTransform (m + 1) (scaledInversePeakGamma m)

@[simp]
theorem scaledInversePeakGamma_coeff (m k : ℕ) :
    (scaledInversePeakGamma m).coeff k =
      (inversePeakEulerian m).coeff k * 4 ^ k := by
  exact Polynomial.comp_C_mul_X_coeff

@[simp]
theorem scaledInversePeakGamma_coeff_zero (m : ℕ) :
    (scaledInversePeakGamma m).coeff 0 = 1 := by
  rw [scaledInversePeakGamma_coeff, inversePeakEulerian_coeff_zero]
  norm_num

@[simp]
theorem scaledInversePeakGamma_natDegree (m : ℕ) :
    (scaledInversePeakGamma m).natDegree = (m + 1) / 2 := by
  rw [scaledInversePeakGamma, natDegree_comp,
    inversePeakEulerian_natDegree]
  norm_num

/-- Scaling by four preserves coefficient nonnegativity. -/
theorem scaledInversePeakGamma_hasNonnegCoeffs (m : ℕ) :
    HasNonnegCoeffs (scaledInversePeakGamma m) := by
  intro k
  rw [scaledInversePeakGamma_coeff]
  exact mul_nonneg ((inversePeakEulerian_hasNonnegCoeffs m) k) (by positivity)

/-- The denominator-free definition is exactly the rational-substitution
formula away from its unique apparent pole. -/
theorem inversePeakTypeB_eval_eq_rational_substitution (m : ℕ) {x : ℝ}
    (hx : x ≠ -1) :
    (inversePeakTypeB m).eval x =
      (1 + x) ^ (m + 1) *
        (inversePeakEulerian m).eval (4 * x / (1 + x) ^ 2) := by
  rw [inversePeakTypeB,
    eval_gammaTransform_eq_mul_eval_gammaUntransform
      (by rw [scaledInversePeakGamma_natDegree]) hx]
  rw [scaledInversePeakGamma, eval_comp]
  simp only [eval_mul, eval_C, eval_X]
  congr 1
  field_simp

private theorem scaledInversePeakGamma_recurrence (n : ℕ) :
    scaledInversePeakGamma (n + 2) =
      C 2 * gammaOperator (n + 2) (scaledInversePeakGamma (n + 1)) +
        C (-1) * scaledInversePeakGamma (n + 1) +
          C 4 * (X * scaledInversePeakGamma n) := by
  apply Polynomial.funext
  intro x
  simp only [scaledInversePeakGamma, gammaOperator_apply,
    eval_add, eval_mul, eval_C, eval_X, eval_comp]
  rw [inversePeakEulerian_recurrence, derivative_comp]
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_one,
    eval_zero, eval_pow, eval_comp, derivative_mul, derivative_C,
    derivative_X, zero_mul, mul_one]
  push_cast
  ring

/-- The type-B differential recurrence, in two-step natural-number form. -/
theorem inversePeakTypeB_recurrence (n : ℕ) :
    inversePeakTypeB (n + 2) =
      (C 2 * X + C (-2) * X ^ 2) * (inversePeakTypeB (n + 1)).derivative +
        (C 1 + C ((2 * n : ℕ) + 5 : ℝ) * X) * inversePeakTypeB (n + 1) +
          C 4 * X * inversePeakTypeB n := by
  rw [inversePeakTypeB, scaledInversePeakGamma_recurrence,
    gammaTransform_add, gammaTransform_add, gammaTransform_C_mul,
    gammaTransform_C_mul, gammaTransform_C_mul]
  rw [← gammaEulerianStep_gammaTransform (n + 2)
    (scaledInversePeakGamma (n + 1)) (by rw [scaledInversePeakGamma_natDegree])]
  rw [gammaTransform_pad_one (d := n + 2)
      (γ := scaledInversePeakGamma (n + 1))
      (by rw [scaledInversePeakGamma_natDegree]),
    gammaTransform_X_mul_two]
  have hcur :
      gammaTransform (n + 2) (scaledInversePeakGamma (n + 1)) =
        inversePeakTypeB (n + 1) := rfl
  have hprev : gammaTransform (n + 1) (scaledInversePeakGamma n) =
      inversePeakTypeB n := rfl
  rw [hcur, hprev]
  rw [gammaEulerianStep_apply]
  push_cast
  norm_num [map_ofNat, map_add, map_mul, map_natCast]
  ring

/-- The displayed recurrence with current index `m ≥ 1`. -/
theorem inversePeakTypeB_recurrence_succ (m : ℕ) (hm : 1 ≤ m) :
    inversePeakTypeB (m + 1) =
      (C 2 * X + C (-2) * X ^ 2) * (inversePeakTypeB m).derivative +
        (C 1 + C ((2 * m : ℕ) + 3 : ℝ) * X) * inversePeakTypeB m +
          C 4 * X * inversePeakTypeB (m - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hcoeff : ((2 * (n + 1) : ℕ) : ℝ) + 3 =
      ((2 * n : ℕ) : ℝ) + 5 := by
    push_cast
    ring
  rw [show 1 + n = n + 1 by lia, hcoeff]
  simpa using inversePeakTypeB_recurrence n

@[simp]
theorem inversePeakTypeB_zero : inversePeakTypeB 0 = 1 + X := by
  norm_num [inversePeakTypeB, scaledInversePeakGamma, inversePeakEulerian,
    gammaTransform, gammaBasisTerm, Finset.sum_range_succ, map_ofNat]
  ring_nf

@[simp]
theorem inversePeakTypeB_one :
    inversePeakTypeB 1 = 1 + C 6 * X + X ^ 2 := by
  norm_num [inversePeakTypeB, scaledInversePeakGamma, inversePeakEulerian,
    gammaTransform, gammaBasisTerm, Finset.sum_range_succ, map_ofNat,
    coeff_one]
  ring_nf

/-- Every coefficient is nonnegative. -/
theorem inversePeakTypeB_hasNonnegCoeffs (m : ℕ) :
    HasNonnegCoeffs (inversePeakTypeB m) :=
  hasNonnegCoeffs_gammaTransform (scaledInversePeakGamma_hasNonnegCoeffs m)

/-- Coefficients are positive throughout the ambient degree box. -/
theorem inversePeakTypeB_coeff_pos (m k : ℕ) (hk : k ≤ m + 1) :
    0 < (inversePeakTypeB m).coeff k := by
  apply coeff_gammaTransform_pos_of_nonneg_of_coeff_zero_pos
    (scaledInversePeakGamma_hasNonnegCoeffs m)
  · simp
  · exact hk

/-- The type-B lift has full ambient degree `m + 1`. -/
@[simp]
theorem inversePeakTypeB_natDegree (m : ℕ) :
    (inversePeakTypeB m).natDegree = m + 1 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact natDegree_gammaTransform_le (m + 1) (scaledInversePeakGamma m)
  · rw [inversePeakTypeB, coeff_ambient_gammaTransform]
    simp

/-- Coefficients are positive exactly on the degree support. -/
theorem inversePeakTypeB_coeff_pos_iff (m k : ℕ) :
    0 < (inversePeakTypeB m).coeff k ↔ k ≤ m + 1 := by
  constructor
  · intro hpos
    by_contra hk
    have hzero : (inversePeakTypeB m).coeff k = 0 :=
      coeff_eq_zero_of_natDegree_lt (by
        rw [inversePeakTypeB_natDegree]
        lia)
    rw [hzero] at hpos
    linarith
  · exact inversePeakTypeB_coeff_pos m k

/-- Every row has positive leading coefficient. -/
theorem inversePeakTypeB_hasPosLeadingCoeff (m : ℕ) :
    HasPosLeadingCoeff (inversePeakTypeB m) := by
  rw [HasPosLeadingCoeff, leadingCoeff, inversePeakTypeB_natDegree]
  exact inversePeakTypeB_coeff_pos m (m + 1) le_rfl

/-- Every real root is strictly negative. -/
theorem inversePeakTypeB_root_neg (m : ℕ) {r : ℝ}
    (hr : (inversePeakTypeB m).IsRoot r) : r < 0 := by
  have hpos := inversePeakTypeB_hasPosLeadingCoeff m
  have hrle := isRoot_nonpos_of_hasNonnegCoeffs
    (inversePeakTypeB_hasNonnegCoeffs m) hpos.ne_zero hr
  apply lt_of_le_of_ne hrle
  intro hr0
  subst r
  rw [Polynomial.IsRoot.def, ← coeff_zero_eq_eval_zero] at hr
  have hcoeff := inversePeakTypeB_coeff_pos m 0 (by simp)
  linarith

private theorem inversePeakTypeB_degree_step (n : ℕ) :
    (inversePeakTypeB (n + 1)).natDegree =
      (inversePeakTypeB n).natDegree + 1 := by
  simp

private theorem inversePeakTypeB_base_strictInterl :
    StrictInterl (inversePeakTypeB 0) (inversePeakTypeB 1) := by
  rw [inversePeakTypeB_zero, inversePeakTypeB_one]
  have hpoly : (1 + C 6 * X + X ^ 2 : ℝ[X]) =
      1 + X * C 6 + X ^ 2 := by
    ring
  rw [hpoly]
  exact strictInterl_one_add_X_quadratic_of_two_le 6 (by norm_num)

private theorem inversePeakTypeB_base_noCommon :
    ∀ r, (inversePeakTypeB 1).IsRoot r →
      ¬ (inversePeakTypeB 0).IsRoot r := by
  intro r hr1 hr0
  rw [inversePeakTypeB_zero, Polynomial.IsRoot.def] at hr0
  rw [inversePeakTypeB_one, Polynomial.IsRoot.def] at hr1
  simp only [eval_add, eval_one, eval_X, eval_mul, eval_C, eval_pow] at hr0 hr1
  nlinarith

/-- Consecutive type-B rows are in proper position and share no real root. -/
theorem inversePeakTypeB_strictInterl_and_noCommonRoot (n : ℕ) :
    StrictInterl (inversePeakTypeB n) (inversePeakTypeB (n + 1)) ∧
      ∀ r, (inversePeakTypeB (n + 1)).IsRoot r →
        ¬ (inversePeakTypeB n).IsRoot r := by
  apply strictInterl_and_noCommonRoot_of_quadratic_lag_degree_step
    (P := inversePeakTypeB) (a := 2) (b := 2) (c := 4)
    (Q := fun m => C 1 + C ((2 * m : ℕ) + 5 : ℝ) * X)
  · norm_num
  · norm_num
  · norm_num
  · intro m
    exact Or.inr (inversePeakTypeB_degree_step m)
  · intro m
    rw [inversePeakTypeB_natDegree]
    lia
  · exact inversePeakTypeB_hasPosLeadingCoeff
  · intro m r hr
    exact inversePeakTypeB_root_neg m hr
  · exact inversePeakTypeB_base_strictInterl
  · exact inversePeakTypeB_base_noCommon
  · exact inversePeakTypeB_recurrence

/-- Consecutive type-B rows are in proper position. -/
theorem inversePeakTypeB_strictInterl (n : ℕ) :
    StrictInterl (inversePeakTypeB n) (inversePeakTypeB (n + 1)) :=
  (inversePeakTypeB_strictInterl_and_noCommonRoot n).1

/-- Consecutive type-B rows have no common real root. -/
theorem inversePeakTypeB_noCommonRoot (n : ℕ) (r : ℝ)
    (hr : (inversePeakTypeB (n + 1)).IsRoot r) :
    ¬ (inversePeakTypeB n).IsRoot r :=
  (inversePeakTypeB_strictInterl_and_noCommonRoot n).2 r hr

/-- Every type-B row splits over the reals. -/
theorem inversePeakTypeB_splits (n : ℕ) : (inversePeakTypeB n).Splits :=
  (inversePeakTypeB_strictInterl n).1.2

/-- Consecutive type-B rows strictly interlace. -/
theorem inversePeakTypeB_interlaces (n : ℕ) :
    Interlaces (inversePeakTypeB n) (inversePeakTypeB (n + 1)) :=
  (inversePeakTypeB_strictInterl n).toInterlaces (inversePeakTypeB_degree_step n).symm

/-- Every type-B row has simple real roots. -/
theorem inversePeakTypeB_hasSimpleRoots (n : ℕ) :
    HasSimpleRoots (inversePeakTypeB n) :=
  ((inversePeakTypeB_strictInterl n).hasSimpleRoots_of_no_common_root fun r hr =>
    inversePeakTypeB_noCommonRoot n r hr.2 hr.1).1

/-! ## Deprecated proper-position names -/

@[deprecated inversePeakTypeB_strictInterl_and_noCommonRoot
  (since := "2026-09-26")]
alias inversePeakTypeB_prec_and_noCommonRoot :=
  inversePeakTypeB_strictInterl_and_noCommonRoot

@[deprecated inversePeakTypeB_strictInterl (since := "2026-09-26")]
alias inversePeakTypeB_prec := inversePeakTypeB_strictInterl

end RealRooted.Applications.OEIS
