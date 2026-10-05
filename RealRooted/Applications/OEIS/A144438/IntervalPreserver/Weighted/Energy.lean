import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Energy
import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Weighted.Endpoints
import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Weighted.ScalarBounds

/-! # Scaled residue energy for the weighted diagonal family -/

open Polynomial

noncomputable section

namespace RealRooted.Applications.OEIS

/-- The invariant used in the uniform proof is `w` times the residue energy. -/
def weightedDecoScaledEnergy (w : ℝ) (p h k : ℝ[X]) : ℝ :=
  w * a144438ResidueEnergy p h k

theorem weightedDecoResidueEnergy_base (w a : ℝ) :
    a144438ResidueEnergy (weightedDecoDiagonal w 1 a)
      (weightedDecoDiagonalCompanion w 1 a) (weightedDecoDiagonalLag w 1 a) =
        1 / ((2 + w) * (1 + a) * (2 + a)) := by
  rw [weightedDecoDiagonal_one, weightedDecoDiagonalCompanion_one,
    weightedDecoDiagonalLag_one]
  have hpoly : X + C (1 + a) = X - C (-(1 + a)) := by
    simp only [map_add, map_one, map_neg]
    ring
  rw [hpoly, a144438ResidueEnergy, roots_X_sub_C]
  simp only [neg_add_rev, Multiset.toFinset_singleton, eval_one, map_add,
    map_neg, map_one, derivative_sub, derivative_X, derivative_C, neg_zero,
    derivative_one, add_zero, sub_zero, ne_eq, one_ne_zero, not_false_eq_true,
    div_self, one_pow, div_one, mul_neg, neg_mul, one_div, inv_neg,
    mul_inv_rev, Finset.sum_neg_distrib, Finset.sum_singleton]
  rw [eval_add, eval_C, eval_C]
  rw [show 1 - (-a + -1) = 2 + a by ring,
    show -a + -1 = -(1 + a) by ring, inv_neg]
  ring

theorem weightedDecoScaledEnergy_base_le_one_sixth {w a : ℝ}
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (ha0 : 0 ≤ a) :
    weightedDecoScaledEnergy w (weightedDecoDiagonal w 1 a)
      (weightedDecoDiagonalCompanion w 1 a)
      (weightedDecoDiagonalLag w 1 a) ≤ 1 / 6 := by
  rw [weightedDecoScaledEnergy, weightedDecoResidueEnergy_base]
  have hwDen : 0 < 2 + w := by linarith
  have haDen : 0 < (1 + a) * (2 + a) := by positivity
  have hden : 0 < (2 + w) * (1 + a) * (2 + a) := by positivity
  rw [div_eq_mul_inv, ← mul_assoc]
  have hratio : w / (2 + w) ≤ 1 / 3 := by
    rw [div_le_iff₀ hwDen]
    nlinarith
  have hrest : 1 / ((1 + a) * (2 + a)) ≤ 1 / 2 := by
    rw [div_le_iff₀ haDen]
    nlinarith
  have hratio0 : 0 ≤ w / (2 + w) := div_nonneg hw0 hwDen.le
  have hrest0 : 0 ≤ 1 / ((1 + a) * (2 + a)) := by positivity
  have hmul := mul_le_mul hratio hrest hrest0 (by norm_num : 0 ≤ (1 : ℝ) / 3)
  rw [div_eq_mul_inv] at hratio hrest hmul ⊢
  field_simp [hwDen.ne', haDen.ne', hden.ne'] at hmul ⊢
  nlinarith

theorem weightedDecoScaledEnergy_base_le_one {w a : ℝ}
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (ha0 : 0 ≤ a) :
    weightedDecoScaledEnergy w (weightedDecoDiagonal w 1 a)
      (weightedDecoDiagonalCompanion w 1 a)
      (weightedDecoDiagonalLag w 1 a) ≤ 1 := by
  linarith [weightedDecoScaledEnergy_base_le_one_sixth hw0 hw1 ha0]

end RealRooted.Applications.OEIS
