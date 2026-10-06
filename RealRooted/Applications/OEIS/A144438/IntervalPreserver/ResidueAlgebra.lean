import RealRooted.Applications.OEIS.A144438.IntervalPreserver.BlockEnergy
import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Energy

/-!
# Finite residue algebra for the A144438 Schur complement

This file checks the algebra that converts the completed block quadratic form
to the endpoint parameters `η`, `κ`, and the original-variable residue
energy.  It is independent of the later spectral/rootwise realization.
-/

open BigOperators

noncomputable section

namespace RealRooted.Applications.OEIS

/-- Expanding the off-diagonal block against the normalized lag vector. -/
theorem a144438_normalized_offDiagonal_eq {ι : Type*} [Fintype ι]
    (r t v z : ι → ℝ) (a : ℝ)
    (hzt : ∀ i, z i * v i = t i) :
    ∑ i, z i * (-v i + a / 2 * z i) / (1 - r i) =
      -(∑ i, t i / (1 - r i)) +
        a / 2 * ∑ i, z i ^ 2 / (1 - r i) := by
  have hterm : ∀ i,
      z i * (-v i + a / 2 * z i) / (1 - r i) =
        -(t i / (1 - r i)) + a / 2 * (z i ^ 2 / (1 - r i)) := by
    intro i
    rw [mul_add]
    have hneg : z i * -v i = -t i := by rw [mul_neg, hzt i]
    rw [hneg]
    ring
  simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    ← Finset.mul_sum]

/-- The `v`-square sum is the total companion mass minus its evaluation at
one. -/
theorem a144438_normalized_v_sq_eq {ι : Type*} [Fintype ι]
    (r w v : ι → ℝ) (hr : ∀ i, r i < 0)
    (hvsq : ∀ i, v i ^ 2 = (-r i) * w i) :
    ∑ i, v i ^ 2 / (1 - r i) =
      (∑ i, w i) - ∑ i, w i / (1 - r i) := by
  have hterm : ∀ i,
      v i ^ 2 / (1 - r i) = w i - w i / (1 - r i) := by
    intro i
    rw [hvsq i]
    have hJne : 1 - r i ≠ 0 := (by linarith [hr i] : 0 < 1 - r i).ne'
    field_simp [hJne]
    ring
  simp_rw [hterm, Finset.sum_sub_distrib]

/-- Expansion of the squared off-diagonal block. -/
theorem a144438_offDiagonal_sq_eq {ι : Type*} [Fintype ι]
    (r t v z : ι → ℝ) (a : ℝ)
    (hzt : ∀ i, z i * v i = t i) :
    ∑ i, (-v i + a / 2 * z i) ^ 2 / (1 - r i) =
      (∑ i, v i ^ 2 / (1 - r i)) -
        a * (∑ i, t i / (1 - r i)) +
          a ^ 2 / 4 * ∑ i, z i ^ 2 / (1 - r i) := by
  have hterm : ∀ i,
      (-v i + a / 2 * z i) ^ 2 / (1 - r i) =
        v i ^ 2 / (1 - r i) - a * (t i / (1 - r i)) +
          a ^ 2 / 4 * (z i ^ 2 / (1 - r i)) := by
    intro i
    rw [← hzt i]
    ring
  simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum]

end RealRooted.Applications.OEIS
