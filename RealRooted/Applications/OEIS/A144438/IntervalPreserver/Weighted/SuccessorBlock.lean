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

end RealRooted.Applications.OEIS
