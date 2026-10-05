import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Weighted.SuccessorResidues

/-!
# Direct weighted residue algebra

This is the square-root-free form of the block calculation.  The positive
diagonal weight is `(1-r) * V`, where `V = (-r) * ω`.
-/

open BigOperators

noncomputable section

namespace RealRooted.Applications.OEIS

theorem weightedDeco_direct_mass_eq {ι : Type*} [Fintype ι]
    (r ω V : ι → ℝ) (a ρ : ℝ)
    (hρ : ∀ i, ρ - r i ≠ 0)
    (hV : ∀ i, V i = (-r i) * ω i)
    (hroot : 1 + ρ + a + ρ * ∑ i, ω i / (ρ - r i) = 0) :
    ∑ i, V i / (ρ - r i) = (∑ i, ω i) + 1 + ρ + a := by
  have hterm : ∀ i,
      V i / (ρ - r i) = ω i - ρ * (ω i / (ρ - r i)) := by
    intro i
    rw [hV i]
    field_simp [hρ i]
    ring
  simp_rw [hterm, Finset.sum_sub_distrib, ← Finset.mul_sum]
  linarith

theorem weightedDeco_direct_successor_block_eq {ι : Type*} [Fintype ι]
    (r ω t V : ι → ℝ) (a w n ρ : ℝ)
    (hρ : ∀ i, ρ - r i ≠ 0)
    (hmass : ∑ i, V i / (ρ - r i) = (∑ i, ω i) + 1 + ρ + a) :
    (∑ i, (1 - r i) * V i * (1 / (ρ - r i)) ^ 2) +
          2 * (∑ i, (-V i + w * a / 2 * t i) * (1 / (ρ - r i))) +
          (2 + w + (∑ i, ω i) - n * a) =
      (1 - ρ) * (1 + ∑ i, V i / (ρ - r i) ^ 2) +
        w * (1 + a * ∑ i, t i / (ρ - r i)) - (n + 1) * a := by
  have hterm : ∀ i,
      (1 - r i) * V i * (1 / (ρ - r i)) ^ 2 +
          2 * ((-V i + w * a / 2 * t i) * (1 / (ρ - r i))) =
        (1 - ρ) * (V i / (ρ - r i) ^ 2) -
          V i / (ρ - r i) + w * a * (t i / (ρ - r i)) := by
    intro i
    field_simp [hρ i]
    ring
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [← Finset.mul_sum]
  rw [hmass]
  ring

theorem weightedDeco_direct_energy_eq {ι : Type*} [Fintype ι]
    (r ω t V : ι → ℝ) (hV : ∀ i, V i = (-r i) * ω i) :
    ∑ i, t i ^ 2 / ((1 - r i) * V i) =
      ∑ i, t i ^ 2 / (ω i * (-r i) * (1 - r i)) := by
  apply Finset.sum_congr rfl
  intro i _
  rw [hV i]
  congr 1
  ring

theorem weightedDeco_direct_mixed_eq {ι : Type*} [Fintype ι]
    (r t V : ι → ℝ) (a w : ℝ)
    (hr : ∀ i, r i < 0) (hV : ∀ i, V i ≠ 0) :
    ∑ i, t i * (-V i + w * a / 2 * t i) / ((1 - r i) * V i) =
      -(∑ i, t i / (1 - r i)) +
        w * a / 2 * ∑ i, t i ^ 2 / ((1 - r i) * V i) := by
  have hterm : ∀ i,
      t i * (-V i + w * a / 2 * t i) / ((1 - r i) * V i) =
        -(t i / (1 - r i)) +
          w * a / 2 * (t i ^ 2 / ((1 - r i) * V i)) := by
    intro i
    have hJ : 1 - r i ≠ 0 := (by linarith [hr i] : 0 < 1 - r i).ne'
    field_simp [hJ, hV i]
  simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    ← Finset.mul_sum]

theorem weightedDeco_direct_offDiagonal_sq_eq {ι : Type*} [Fintype ι]
    (r t V : ι → ℝ) (a w : ℝ)
    (hr : ∀ i, r i < 0) (hV : ∀ i, V i ≠ 0) :
    ∑ i, (-V i + w * a / 2 * t i) ^ 2 / ((1 - r i) * V i) =
      (∑ i, V i / (1 - r i)) -
        w * a * (∑ i, t i / (1 - r i)) +
          w ^ 2 * a ^ 2 / 4 *
            ∑ i, t i ^ 2 / ((1 - r i) * V i) := by
  have hterm : ∀ i,
      (-V i + w * a / 2 * t i) ^ 2 / ((1 - r i) * V i) =
        V i / (1 - r i) - w * a * (t i / (1 - r i)) +
          w ^ 2 * a ^ 2 / 4 * (t i ^ 2 / ((1 - r i) * V i)) := by
    intro i
    have hJ : 1 - r i ≠ 0 := (by linarith [hr i] : 0 < 1 - r i).ne'
    field_simp [hJ, hV i]
    ring
  simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum]

theorem weightedDeco_direct_V_sum_eq {ι : Type*} [Fintype ι]
    (r ω V : ι → ℝ) (hr : ∀ i, r i < 0)
    (hV : ∀ i, V i = (-r i) * ω i) :
    ∑ i, V i / (1 - r i) =
      (∑ i, ω i) - ∑ i, ω i / (1 - r i) := by
  have hterm : ∀ i, V i / (1 - r i) = ω i - ω i / (1 - r i) := by
    intro i
    rw [hV i]
    have hJ : 1 - r i ≠ 0 := (by linarith [hr i] : 0 < 1 - r i).ne'
    field_simp [hJ]
    ring
  simp_rw [hterm, Finset.sum_sub_distrib]

theorem weightedDeco_direct_schur_eq {ι : Type*} [Fintype ι]
    (r ω t V : ι → ℝ) (a w n η κ E H : ℝ)
    (hr : ∀ i, r i < 0) (hVeq : ∀ i, V i = (-r i) * ω i)
    (hV : ∀ i, V i ≠ 0)
    (hcompanion : ∑ i, ω i / (1 - r i) = n - η + w * κ)
    (hlag : ∑ i, t i / (1 - r i) = κ)
    (henergy : ∑ i, t i ^ 2 / ((1 - r i) * V i) = E)
    (hscaled : w * E = H) :
    2 + w + (∑ i, ω i) - n * a -
        ∑ i, (-V i + w * a / 2 * t i) ^ 2 / ((1 - r i) * V i) =
      2 + w + n * (1 - a) - η + w * (1 + a) * κ -
        w * a ^ 2 * H / 4 := by
  rw [weightedDeco_direct_offDiagonal_sq_eq r t V a w hr hV,
    weightedDeco_direct_V_sum_eq r ω V hr hVeq,
    hcompanion, hlag, henergy, ← hscaled]
  ring

theorem weightedDeco_direct_block_norm_eq {ι : Type*} [Fintype ι]
    (r t V : ι → ℝ) (a w κ E H S : ℝ)
    (hr : ∀ i, r i < 0) (hV : ∀ i, V i ≠ 0)
    (hlag : ∑ i, t i / (1 - r i) = κ)
    (henergy : ∑ i, t i ^ 2 / ((1 - r i) * V i) = E)
    (hscaled : w * E = H) :
    w * (a ^ 2 * (∑ i, t i ^ 2 / ((1 - r i) * V i)) +
        (1 - a * (∑ i,
          t i * (-V i + w * a / 2 * t i) / ((1 - r i) * V i))) ^ 2 / S) =
      a ^ 2 * H + w * (1 + a * κ - a ^ 2 * H / 2) ^ 2 / S := by
  rw [weightedDeco_direct_mixed_eq r t V a w hr hV, hlag, henergy,
    ← hscaled]
  ring

end RealRooted.Applications.OEIS
