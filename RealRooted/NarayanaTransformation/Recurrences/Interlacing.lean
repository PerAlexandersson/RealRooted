module

import RealRooted.NarayanaTransformation.Recurrences.Identities
import RealRooted.NarayanaTransformation.Rectangular.Preservation
public import RealRooted.NarayanaTransformation.Coefficients
import RealRooted.LiuWangRecursion
import RealRooted.MaWang.Strong
import RealRooted.Linear

/-!
# Generalized Narayana recurrence interlacing
-/

public section

open Polynomial Finset

noncomputable section

namespace RealRooted

theorem narayanaPolynomial_no_common_root (m : ℕ) :
    ∀ (n : ℕ) (r : ℝ), (narayanaPolynomial m (n + 1)).IsRoot r →
      ¬ (narayanaPolynomial m n).IsRoot r := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      intro r hr₂ hr₁
      have hr_ne : r ≠ 1 := fun h => (narayanaPolynomial_eval_one_pos m (n + 1)).ne' (h ▸ hr₁)
      have : (C ((n : ℝ) + 2 * m + 2) * narayanaPolynomial m (n + 2)).eval r =
          (C ((2 * n : ℝ) + 2 * m + 3) * ((1 + X) * narayanaPolynomial m (n + 1)) -
            C ((n : ℝ) + 1) * ((1 - X) ^ 2 * narayanaPolynomial m n)).eval r :=
        congrArg (eval r) (narayanaPolynomial_pure_rec m n)
      simp only [eval_mul, eval_C, eval_sub, eval_add, eval_pow, eval_one, eval_X] at this
      rw [hr₂, hr₁] at this
      have : (1 - r) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm hr_ne))
      have : ((n : ℝ) + 1) ≠ 0 := by positivity
      simp_all

theorem strictInterl_narayanaPolynomial_one_two (m : ℕ) :
    StrictInterl (narayanaPolynomial m 1) (narayanaPolynomial m 2) := by
  apply MaWang.strictInterl_of_interlaces_eval_mul_neg_succ
    (interlaces_one_linear (natDegree_narayanaPolynomial m 1))
    hasPosLeadingCoeff_one (hasPosLeadingCoeff_narayanaPolynomial m 2)
    (by simp only [natDegree_narayanaPolynomial])
  intro r hr
  have hr' : r = -1 := by
    simp only [narayanaPolynomial_one, IsRoot.def, eval_add, eval_X, eval_C] at hr
    linarith
  subst r
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  simp only [narayanaPolynomial_two, eval_add, eval_pow, eval_X, eval_mul, eval_C,
    eval_one, mul_one]
  have hratio : 2 < 2 * ((m : ℝ) + 2) / ((m : ℝ) + 1) :=
    (lt_div_iff₀ hm).mpr (by linarith)
  nlinarith

lemma two_mul_sub_two_mul_sq_nonpos_of_nonpos {r : ℝ} (hr : r ≤ 0) :
    (C (2 : ℝ) * X - C (2 : ℝ) * X ^ 2).eval r ≤ 0 := by
  simp only [eval_mul, eval_C, eval_sub, eval_pow, eval_X]
  nlinarith

/-- Consecutive positive-degree generalized Narayana polynomials are in proper
position.  This exposes the full Liu--Wang conclusion already constructed by
the recurrence proof below, rather than retaining only real-rootedness. -/
theorem strictInterl_narayanaPolynomial_succ (m n : ℕ) :
    StrictInterl (narayanaPolynomial m (n + 1)) (narayanaPolynomial m (n + 2)) := by
  set P : ℕ → ℝ[X] := fun k => narayanaPolynomial m (k + 1) with hP
  have hpos (k : ℕ) : HasPosLeadingCoeff (P k) :=
    hasPosLeadingCoeff_narayanaPolynomial m (k + 1)
  have hdeg_succ (k : ℕ) : (P k).natDegree + 1 = (P (k + 1)).natDegree := by
    simp only [hP, natDegree_narayanaPolynomial]
  have hno (k : ℕ) (r : ℝ) (hr : (P (k + 1)).IsRoot r) : ¬ (P k).IsRoot r :=
    narayanaPolynomial_no_common_root m (k + 1) r hr
  have hrec (k : ℕ) :
      P (k + 2) =
        (C (((k + 1 : ℕ) : ℝ) + 2 * m + 2)⁻¹ *
          (C (((k + 1 : ℕ) : ℝ) + 2 * m + 2)
            + C ((3 * (k + 1 : ℕ) : ℝ) + 2 * m + 4) * X)) * P (k + 1)
        + (C (((k + 1 : ℕ) : ℝ) + 2 * m + 2)⁻¹ *
            (C (2 : ℝ) * X - C (2 : ℝ) * X ^ 2)) *
            (P (k + 1)).derivative
        + 0 * P k := by
    grind [narayanaPolynomial_deriv_lag_rec m (k + 1)]
  have hbase : StrictInterl (P 0) (P 1) := strictInterl_narayanaPolynomial_one_two m
  have hV_nonpos (k : ℕ) (r : ℝ) (hr : (P (k + 1)).IsRoot r) :
      (C (((k + 1 : ℕ) : ℝ) + 2 * m + 2)⁻¹ *
        (C (2 : ℝ) * X - C (2 : ℝ) * X ^ 2)).eval r ≤ 0 := by
    rw [eval_mul, eval_C]
    have : 0 ≤ (((k + 1 : ℕ) : ℝ) + 2 * m + 2)⁻¹ := by positivity
    exact mul_nonpos_of_nonneg_of_nonpos this
      (two_mul_sub_two_mul_sq_nonpos_of_nonpos (narayanaPolynomial_root_nonpos hr))
  have hW_nonpos (k : ℕ) (r : ℝ) (_ : (P (k + 1)).IsRoot r) :
      (0 : ℝ[X]).eval r ≤ 0 := by
    simp
  have hbuild := LiuWang.strictInterl_derivative_lag_sequence
    (P := P)
    (U := fun k ↦ C (((k + 1 : ℕ) : ℝ) + 2 * m + 2)⁻¹ *
      (C (((k + 1 : ℕ) : ℝ) + 2 * m + 2) +
        C ((3 * (k + 1 : ℕ) : ℝ) + 2 * m + 4) * X))
    (V := fun k => C (((k + 1 : ℕ) : ℝ) + 2 * m + 2)⁻¹ *
      (C (2 : ℝ) * X - C (2 : ℝ) * X ^ 2))
    (W := fun _ => 0)
    hbase hpos hrec hV_nonpos hW_nonpos hdeg_succ hno
  simpa [P] using hbuild n

end RealRooted
