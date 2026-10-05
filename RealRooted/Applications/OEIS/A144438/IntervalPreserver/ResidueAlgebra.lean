import RealRooted.Applications.OEIS.A144438.IntervalPreserver.BlockEnergy
import RealRooted.Applications.OEIS.A144438.IntervalPreserver.ResidueSums

/-!
# Finite residue algebra for the A144438 Schur complement

This file checks the algebra that converts the completed block quadratic form
to the endpoint parameters `η`, `κ`, and the original-variable residue
energy.  It is independent of the later spectral/rootwise realization.
-/

open BigOperators

noncomputable section

namespace RealRooted.Applications.OEIS

/-- Replacing `vᵢ²` by `(-rᵢ)wᵢ` turns the normalized `z`-square sum into
the original-variable residue energy. -/
theorem a144438_normalized_energy_eq {ι : Type*} [Fintype ι]
    (r w t v z : ι → ℝ)
    (hr : ∀ i, r i < 0)
    (hv : ∀ i, 0 < v i)
    (hvsq : ∀ i, v i ^ 2 = (-r i) * w i)
    (hz : ∀ i, z i = t i / v i) :
    ∑ i, z i ^ 2 / (1 - r i) =
      ∑ i, t i ^ 2 / (w i * (-r i) * (1 - r i)) := by
  apply Finset.sum_congr rfl
  intro i _
  rw [hz i]
  have hvne := (hv i).ne'
  have hJne : 1 - r i ≠ 0 := (by linarith [hr i] : 0 < 1 - r i).ne'
  have hden : w i * (-r i) * (1 - r i) = v i ^ 2 * (1 - r i) := by
    rw [hvsq i]
    ring
  rw [hden]
  field_simp [hvne, hJne]

/-- The mixed normalized sum is the lag residue sum. -/
theorem a144438_normalized_mixed_eq {ι : Type*} [Fintype ι]
    (r t v z : ι → ℝ) (hv : ∀ i, v i ≠ 0)
    (hz : ∀ i, z i = t i / v i) :
    ∑ i, z i * v i / (1 - r i) = ∑ i, t i / (1 - r i) := by
  apply Finset.sum_congr rfl
  intro i _
  rw [hz i]
  field_simp [hv i]

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

/-- Exact Schur-complement identity corresponding to equations (18)--(19). -/
theorem a144438_residue_schur_eq {ι : Type*} [Fintype ι]
    (r w t v z : ι → ℝ) (a n η κ E : ℝ)
    (hr : ∀ i, r i < 0)
    (hvsq : ∀ i, v i ^ 2 = (-r i) * w i)
    (hzt : ∀ i, z i * v i = t i)
    (hcompanion : ∑ i, w i / (1 - r i) = n - η + κ)
    (hlag : ∑ i, t i / (1 - r i) = κ)
    (henergy : ∑ i, z i ^ 2 / (1 - r i) = E) :
    3 + (∑ i, w i) - n * a -
        ∑ i, (-v i + a / 2 * z i) ^ 2 / (1 - r i) =
      3 + n * (1 - a) - η + (1 + a) * κ - a ^ 2 * E / 4 := by
  rw [a144438_offDiagonal_sq_eq r t v z a hzt,
    a144438_normalized_v_sq_eq r w v hr hvsq,
    hcompanion, hlag, henergy]
  ring

/-- Exact completed-square norm identity corresponding to equation (25). -/
theorem a144438_residue_block_norm_eq {ι : Type*} [Fintype ι]
    (r t v z : ι → ℝ) (a κ E S : ℝ)
    (hzt : ∀ i, z i * v i = t i)
    (hlag : ∑ i, t i / (1 - r i) = κ)
    (henergy : ∑ i, z i ^ 2 / (1 - r i) = E) :
    a ^ 2 * (∑ i, z i ^ 2 / (1 - r i)) +
        (1 - a * (∑ i, z i * (-v i + a / 2 * z i) / (1 - r i))) ^ 2 / S =
      a ^ 2 * E + (1 + a * κ - a ^ 2 * E / 2) ^ 2 / S := by
  rw [a144438_normalized_offDiagonal_eq r t v z a hzt, hlag, henergy]
  ring

/-- The endpoint and energy bounds make the residue Schur complement
uniformly positive, in the exact finite-sum notation. -/
theorem a144438_residue_schur_gt {ι : Type*} [Fintype ι]
    (r w t v z : ι → ℝ) (a n η κ E : ℝ)
    (hr : ∀ i, r i < 0)
    (hvsq : ∀ i, v i ^ 2 = (-r i) * w i)
    (hzt : ∀ i, z i * v i = t i)
    (hcompanion : ∑ i, w i / (1 - r i) = n - η + κ)
    (hlag : ∑ i, t i / (1 - r i) = κ)
    (henergy : ∑ i, z i ^ 2 / (1 - r i) = E)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hκ0 : 0 ≤ κ)
    (hη : η < 1) (hE0 : 0 ≤ E) (hE1 : E ≤ 1) (hn : 0 ≤ n) :
    7 / 4 < 3 + (∑ i, w i) - n * a -
      ∑ i, (-v i + a / 2 * z i) ^ 2 / (1 - r i) := by
  rw [a144438_residue_schur_eq r w t v z a n η κ E hr hvsq hzt
    hcompanion hlag henergy]
  exact a144438_schur_complement_gt ha0 ha1 hκ0 hη hE0 hE1 hn

end RealRooted.Applications.OEIS
