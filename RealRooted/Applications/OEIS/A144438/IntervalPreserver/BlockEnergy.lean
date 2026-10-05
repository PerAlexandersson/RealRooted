import RealRooted.Applications.OEIS.A144438.IntervalPreserver.StrictStep
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Block quadratic-form estimates for the A144438 residue energy

The arrowhead proof only uses one inverse-matrix fact.  This file states it
without matrices: complete the square in the diagonal block and apply a
weighted finite Cauchy--Schwarz inequality.  This is the algebraic content of
the formula for `bᵀ C⁻¹ b`.
-/

open BigOperators

noncomputable section

namespace RealRooted.Applications.OEIS

/-- Finite weighted Cauchy--Schwarz, in the division form used after
completing the block quadratic form. -/
theorem a144438_weighted_cauchy {ι : Type*} [Fintype ι]
    (w u v : ι → ℝ) (hw : ∀ i, 0 < w i) :
    (∑ i, u i * v i) ^ 2 ≤
      (∑ i, u i ^ 2 / w i) * ∑ i, w i * v i ^ 2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i ↦ u i / Real.sqrt (w i))
    (fun i ↦ Real.sqrt (w i) * v i)
  have hsqrt : ∀ i, Real.sqrt (w i) ≠ 0 := by
    intro i
    exact ne_of_gt (Real.sqrt_pos.2 (hw i))
  have hleft :
      ∑ i, (u i / Real.sqrt (w i)) * (Real.sqrt (w i) * v i) =
        ∑ i, u i * v i := by
    apply Finset.sum_congr rfl
    intro i _
    field_simp [hsqrt i]
  have hfirst :
      ∑ i, (u i / Real.sqrt (w i)) ^ 2 = ∑ i, u i ^ 2 / w i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [div_pow, Real.sq_sqrt (hw i).le]
  have hsecond :
      ∑ i, (Real.sqrt (w i) * v i) ^ 2 = ∑ i, w i * v i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_pow, Real.sq_sqrt (hw i).le]
  rwa [hleft, hfirst, hsecond] at hcs

/-- Completing the diagonal block expresses the quadratic denominator as a
sum of positive weighted squares plus its Schur complement. -/
theorem a144438_block_quadratic_eq {ι : Type*} [Fintype ι]
    (J c y : ι → ℝ) (β x : ℝ) (hJ : ∀ i, J i ≠ 0) :
    (∑ i, J i * y i ^ 2) + 2 * x * (∑ i, c i * y i) + β * x ^ 2 =
      (∑ i, J i * (y i + x * c i / J i) ^ 2) +
        (β - ∑ i, c i ^ 2 / J i) * x ^ 2 := by
  have hterm : ∀ i,
      J i * (y i + x * c i / J i) ^ 2 =
        J i * y i ^ 2 + 2 * x * (c i * y i) + x ^ 2 * (c i ^ 2 / J i) := by
    intro i
    field_simp [hJ i]
    ring
  symm
  calc
    (∑ i, J i * (y i + x * c i / J i) ^ 2) +
          (β - ∑ i, c i ^ 2 / J i) * x ^ 2 =
        (∑ i, (J i * y i ^ 2 + 2 * x * (c i * y i) +
          x ^ 2 * (c i ^ 2 / J i))) +
            (β - ∑ i, c i ^ 2 / J i) * x ^ 2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact hterm i
    _ = (∑ i, J i * y i ^ 2) +
          2 * x * (∑ i, c i * y i) + β * x ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      have hcross :
          ∑ i, 2 * x * (c i * y i) = 2 * x * ∑ i, c i * y i := by
        rw [Finset.mul_sum]
      have hsquare :
          ∑ i, x ^ 2 * (c i ^ 2 / J i) =
            x ^ 2 * ∑ i, c i ^ 2 / J i := by
        rw [Finset.mul_sum]
      rw [hcross, hsquare]
      ring

/-- The completed block form is strictly positive when its diagonal weights
and Schur complement are positive and the bottom coordinate is nonzero. -/
theorem a144438_block_quadratic_pos {ι : Type*} [Fintype ι]
    (J c y : ι → ℝ) (β x : ℝ)
    (hJ : ∀ i, 0 < J i)
    (hS : 0 < β - ∑ i, c i ^ 2 / J i) (hx : x ≠ 0) :
    0 < (∑ i, J i * y i ^ 2) + 2 * x * (∑ i, c i * y i) + β * x ^ 2 := by
  rw [a144438_block_quadratic_eq J c y β x (fun i ↦ (hJ i).ne')]
  have hsum : 0 ≤ ∑ i, J i * (y i + x * c i / J i) ^ 2 := by
    exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (hJ i).le (sq_nonneg _)
  have hbottom : 0 < (β - ∑ i, c i ^ 2 / J i) * x ^ 2 := by
    exact mul_pos hS (sq_pos_of_ne_zero hx)
  linarith

/-- Block Cauchy--Schwarz after completion of squares.  The first factor on
the right is exactly the scalar expression later identified with
`bᵀ C⁻¹ b`. -/
theorem a144438_block_cauchy {ι : Type*} [Fintype ι]
    (J c z y : ι → ℝ) (a β x : ℝ)
    (hJ : ∀ i, 0 < J i)
    (hS : 0 < β - ∑ i, c i ^ 2 / J i) :
    (a * (∑ i, z i * y i) + x) ^ 2 ≤
      (a ^ 2 * (∑ i, z i ^ 2 / J i) +
          (1 - a * (∑ i, z i * c i / J i)) ^ 2 /
            (β - ∑ i, c i ^ 2 / J i)) *
        ((∑ i, J i * y i ^ 2) +
          2 * x * (∑ i, c i * y i) + β * x ^ 2) := by
  let S : ℝ := β - ∑ i, c i ^ 2 / J i
  let w : Option ι → ℝ
    | none => S
    | some i => J i
  let u : Option ι → ℝ
    | none => 1 - a * (∑ i, z i * c i / J i)
    | some i => a * z i
  let v : Option ι → ℝ
    | none => x
    | some i => y i + x * c i / J i
  have hw : ∀ q, 0 < w q := by
    intro q
    cases q with
    | none => exact hS
    | some i => exact hJ i
  have hcs := a144438_weighted_cauchy w u v hw
  simp only [Fintype.sum_option, w, u, v] at hcs
  have hlinear :
      (1 - a * (∑ i, z i * c i / J i)) * x +
          ∑ i, a * z i * (y i + x * c i / J i) =
        a * (∑ i, z i * y i) + x := by
    have hsumExpand :
        ∑ i, a * z i * (y i + x * c i / J i) =
          a * (∑ i, z i * y i) +
            a * x * (∑ i, z i * c i / J i) := by
      simp_rw [mul_add, Finset.sum_add_distrib]
      congr 1
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
    rw [hsumExpand]
    ring
  have hnorm :
      (1 - a * (∑ i, z i * c i / J i)) ^ 2 / S +
          ∑ i, (a * z i) ^ 2 / J i =
        a ^ 2 * (∑ i, z i ^ 2 / J i) +
          (1 - a * (∑ i, z i * c i / J i)) ^ 2 / S := by
    have hsumNorm :
        ∑ i, (a * z i) ^ 2 / J i = a ^ 2 * ∑ i, z i ^ 2 / J i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsumNorm]
    ring
  have hquad :
      S * x ^ 2 + ∑ i, J i * (y i + x * c i / J i) ^ 2 =
        (∑ i, J i * y i ^ 2) +
          2 * x * (∑ i, c i * y i) + β * x ^ 2 := by
    dsimp [S]
    simpa only [add_comm] using
      (a144438_block_quadratic_eq J c y β x
        (fun i ↦ (hJ i).ne')).symm
  rw [hlinear, hnorm, hquad] at hcs
  exact hcs

end RealRooted.Applications.OEIS
