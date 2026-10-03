import RealRooted.Applications.OEIS.A144438.IntervalPreserver.ResidueAlgebra
import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Weighted.ResidueSums

/-! # Finite residue algebra for the weighted Schur complement -/

open BigOperators

noncomputable section

namespace RealRooted.Applications.OEIS

theorem weightedDeco_residue_schur_eq {ι : Type*} [Fintype ι]
    (r ω t v z : ι → ℝ) (a w n η κ E H : ℝ)
    (hr : ∀ i, r i < 0)
    (hvsq : ∀ i, v i ^ 2 = (-r i) * ω i)
    (hzt : ∀ i, z i * v i = t i)
    (hcompanion : ∑ i, ω i / (1 - r i) = n - η + w * κ)
    (hlag : ∑ i, t i / (1 - r i) = κ)
    (henergy : ∑ i, z i ^ 2 / (1 - r i) = E)
    (hscaled : w * E = H) :
    2 + w + (∑ i, ω i) - n * a -
        ∑ i, (-v i + w * a / 2 * z i) ^ 2 / (1 - r i) =
      2 + w + n * (1 - a) - η + w * (1 + a) * κ -
        w * a ^ 2 * H / 4 := by
  rw [a144438_offDiagonal_sq_eq r t v z (w * a) hzt,
    a144438_normalized_v_sq_eq r ω v hr hvsq,
    hcompanion, hlag, henergy]
  rw [← hscaled]
  ring

theorem weightedDeco_residue_block_norm_eq {ι : Type*} [Fintype ι]
    (r t v z : ι → ℝ) (a w κ E H S : ℝ)
    (hzt : ∀ i, z i * v i = t i)
    (hlag : ∑ i, t i / (1 - r i) = κ)
    (henergy : ∑ i, z i ^ 2 / (1 - r i) = E)
    (hscaled : w * E = H) :
    w * (a ^ 2 * (∑ i, z i ^ 2 / (1 - r i)) +
        (1 - a * (∑ i,
          z i * (-v i + w * a / 2 * z i) / (1 - r i))) ^ 2 / S) =
      a ^ 2 * H +
        w * (1 + a * κ - a ^ 2 * H / 2) ^ 2 / S := by
  rw [a144438_normalized_offDiagonal_eq r t v z (w * a) hzt,
    hlag, henergy]
  rw [← hscaled]
  ring

/-- The weighted Schur complement is positive under the scaled invariant. -/
theorem weightedDeco_schur_pos {a w κ η H n : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hκ0 : 0 ≤ κ) (hη : η < 1) (hH0 : 0 ≤ H) (hH1 : H ≤ 1)
    (hn : 0 ≤ n) :
    0 < 2 + w + n * (1 - a) - η + w * (1 + a) * κ -
      w * a ^ 2 * H / 4 := by
  have haSquare : a ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg ha0 (sub_nonneg.mpr ha1)]
  have hwH : w * H ≤ 1 := by
    have : w * H ≤ w := by
      simpa using mul_le_mul_of_nonneg_left hH1 hw0
    linarith
  have hwaH : w * a ^ 2 * H ≤ 1 := by
    have haH : a ^ 2 * H ≤ H := by
      simpa using mul_le_mul_of_nonneg_right haSquare hH0
    have := mul_le_mul_of_nonneg_left haH hw0
    nlinarith
  have hnTerm : 0 ≤ n * (1 - a) := mul_nonneg hn (sub_nonneg.mpr ha1)
  have hκTerm : 0 ≤ w * (1 + a) * κ := by positivity
  nlinarith

end RealRooted.Applications.OEIS
