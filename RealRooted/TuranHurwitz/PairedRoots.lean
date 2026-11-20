module

public import RealRooted.TuranHurwitz.FormalParity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Pairing a root along opposite formal flows

The denominator has constant coefficient one. We prove the factor identity
by clearing this formal unit and then performing polynomial algebra.
-/

public section

namespace RealRooted.TuranHurwitz

local notation "S" => complexTanhSeries

/-- The disk parameter attached to a root in the paired flow. -/
@[expose] noncomputable def pairedParameter (u r : ℂ) : ℂ :=
  ((1 - r * u) / (u - r)) ^ 2

/-- Clearing the denominator in one root factor of the formal flow. -/
theorem formalFlow_sub_mul_denominator (u r : ℂ) :
    (1 - PowerSeries.C u * S) * (formalFlow u - PowerSeries.C r) =
      PowerSeries.C (u - r) - PowerSeries.C (1 - r * u) * S := by
  have hcancel := PowerSeries.mul_inv_cancel (flowDenominator u) (by simp)
  dsimp [formalFlow, flowDenominator] at hcancel ⊢
  simp only [map_sub, map_one, map_mul]
  linear_combination (PowerSeries.C u - S) * hcancel

/-- Clearing the denominator in the root factor at reversed formal time. -/
theorem reverse_formalFlow_sub_mul_denominator (u r : ℂ) :
    (1 + PowerSeries.C u * S) *
        (PowerSeries.rescale (-1) (formalFlow u) - PowerSeries.C r) =
      PowerSeries.C (u - r) + PowerSeries.C (1 - r * u) * S := by
  have hcancel := PowerSeries.mul_inv_cancel (1 + PowerSeries.C u * S) (by simp)
  rw [rescale_neg_formalFlow]
  simp only [map_sub, map_one, map_mul]
  linear_combination (PowerSeries.C u + S) * hcancel

/-- Pairing one root at opposite formal times gives its quadratic kernel factor. -/
theorem formalFlow_root_pair (u r : ℂ) (hur : u - r ≠ 0) :
    (formalFlow u - PowerSeries.C r) *
        (PowerSeries.rescale (-1) (formalFlow u) - PowerSeries.C r) =
      PowerSeries.C ((u - r) ^ 2) *
        (1 - PowerSeries.C (pairedParameter u r) * S ^ 2) *
          (1 - PowerSeries.C (u ^ 2) * S ^ 2)⁻¹ := by
  let B : PowerSeries ℂ := 1 - PowerSeries.C (u ^ 2) * S ^ 2
  have hBzero : PowerSeries.constantCoeff B = 1 := by simp [B]
  have hB : B ≠ 0 := by
    intro heq
    have hc := congrArg PowerSeries.constantCoeff heq
    rw [hBzero, map_zero] at hc
    exact one_ne_zero hc
  have hcancel := PowerSeries.mul_inv_cancel B (by rw [hBzero]; exact one_ne_zero)
  have hfactor : B = (1 - PowerSeries.C u * S) * (1 + PowerSeries.C u * S) := by
    dsimp [B]
    rw [map_pow]
    ring
  have heta : PowerSeries.C ((u - r) ^ 2) *
      PowerSeries.C (pairedParameter u r) = PowerSeries.C ((1 - r * u) ^ 2) := by
    rw [← map_mul]
    congr 1
    dsimp [pairedParameter]
    field_simp
  change _ = PowerSeries.C ((u - r) ^ 2) *
    (1 - PowerSeries.C (pairedParameter u r) * S ^ 2) * B⁻¹
  apply mul_left_cancel₀ hB
  calc
    _ = ((1 - PowerSeries.C u * S) * (formalFlow u - PowerSeries.C r)) *
        ((1 + PowerSeries.C u * S) *
          (PowerSeries.rescale (-1) (formalFlow u) - PowerSeries.C r)) := by
            rw [hfactor]
            ring
    _ = (PowerSeries.C (u - r) - PowerSeries.C (1 - r * u) * S) *
        (PowerSeries.C (u - r) + PowerSeries.C (1 - r * u) * S) := by
          rw [formalFlow_sub_mul_denominator, reverse_formalFlow_sub_mul_denominator]
    _ = PowerSeries.C ((u - r) ^ 2) *
        (1 - PowerSeries.C (pairedParameter u r) * S ^ 2) := by
          simp only [map_pow] at heta ⊢
          linear_combination (S ^ 2) * heta
    _ = _ := by
      calc
        _ = PowerSeries.C ((u - r) ^ 2) *
          (1 - PowerSeries.C (pairedParameter u r) * S ^ 2) * (B * B⁻¹) := by
            rw [hcancel, mul_one]
        _ = _ := by ring

end RealRooted.TuranHurwitz
