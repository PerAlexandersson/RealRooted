import RealRooted.Applications.OEIS.A144438.IntervalPreserver.ResidueDerivative
import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Weighted.DiagonalRootStep

/-! # Finite block identities at a weighted diagonal successor root -/

open BigOperators

noncomputable section

namespace RealRooted.Applications.OEIS

/-- The weighted companion numerator is the block quadratic form. -/
theorem weightedDeco_successor_block_eq {ι : Type*} [Fintype ι]
    (r ω t v z : ι → ℝ) (a w n ρ : ℝ)
    (hρ : ∀ i, ρ - r i ≠ 0)
    (hzt : ∀ i, z i * v i = t i)
    (hmass : ∑ i, v i ^ 2 / (ρ - r i) = (∑ i, ω i) + 1 + ρ + a) :
    (∑ i, (1 - r i) * (v i / (ρ - r i)) ^ 2) +
          2 * (∑ i, (-v i + w * a / 2 * z i) * (v i / (ρ - r i))) +
          (2 + w + (∑ i, ω i) - n * a) =
      (1 - ρ) * (1 + ∑ i, v i ^ 2 / (ρ - r i) ^ 2) +
        w * (1 + a * ∑ i, t i / (ρ - r i)) - (n + 1) * a := by
  have hterm : ∀ i,
      (1 - r i) * (v i / (ρ - r i)) ^ 2 +
          2 * ((-v i + w * a / 2 * z i) * (v i / (ρ - r i))) =
        (1 - ρ) * (v i ^ 2 / (ρ - r i) ^ 2) -
          v i ^ 2 / (ρ - r i) + w * a * (t i / (ρ - r i)) := by
    intro i
    rw [← hzt i]
    field_simp [hρ i]
    ring
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [← Finset.mul_sum]
  rw [hmass]
  ring

/-- The lag numerator at a successor root. -/
theorem weightedDeco_successor_lag_eq {ι : Type*} [Fintype ι]
    (t : ι → ℝ) (a : ℝ) :
    1 + a * ∑ i, t i = 1 + ∑ i, a * t i := by
  rw [Finset.mul_sum]

/-- The completed block estimate in the exact rootwise quotient form used by
the scaled-energy induction. -/
theorem weightedDeco_rootwise_block_bound {ι : Type*} [Fintype ι]
    (J c z y : ι → ℝ) (a β w D : ℝ)
    (hJ : ∀ i, 0 < J i)
    (hS : 0 < β - ∑ i, c i ^ 2 / J i)
    (hw : 0 ≤ w) (hD : 0 < D) :
    let A := (∑ i, J i * y i ^ 2) + 2 * (∑ i, c i * y i) + β
    let L := a * (∑ i, z i * y i) + 1
    let B := a ^ 2 * (∑ i, z i ^ 2 / J i) +
      (1 - a * (∑ i, z i * c i / J i)) ^ 2 /
        (β - ∑ i, c i ^ 2 / J i)
    0 < A ∧ w * (L / D) ^ 2 / (A / D) ≤ w * B / D := by
  dsimp only
  let A := (∑ i, J i * y i ^ 2) + 2 * (∑ i, c i * y i) + β
  let L := a * (∑ i, z i * y i) + 1
  let B := a ^ 2 * (∑ i, z i ^ 2 / J i) +
    (1 - a * (∑ i, z i * c i / J i)) ^ 2 /
      (β - ∑ i, c i ^ 2 / J i)
  have hA : 0 < A := by
    dsimp [A]
    simpa only [one_pow, one_mul, mul_one] using
      a144438_block_quadratic_pos J c y β 1 hJ hS one_ne_zero
  have hcs : L ^ 2 ≤ B * A := by
    dsimp [L, B, A]
    simpa only [one_pow, mul_one] using
      a144438_block_cauchy J c z y a β 1 hJ hS
  constructor
  · exact hA
  · have hwcs : w * L ^ 2 ≤ w * (B * A) :=
      mul_le_mul_of_nonneg_left hcs hw
    have hDA : 0 < D * A := mul_pos hD hA
    have hleft : w * (L / D) ^ 2 / (A / D) = w * L ^ 2 / (D * A) := by
      field_simp [hD.ne', hA.ne']
    have hright : w * B / D = w * (B * A) / (D * A) := by
      field_simp [hD.ne', hA.ne']
    rw [hleft, hright, div_le_div_iff₀ hDA hDA]
    nlinarith

end RealRooted.Applications.OEIS
