import RealRooted.Applications.OEIS.A144438.IntervalPreserver.ScalarBounds
import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Weighted.Basic

/-!
# Scalar bounds for the weighted residue-energy induction

The weighted proof carries the scaled energy `H = w * E`.  This avoids any
division by `w` and includes the Eulerian endpoint `w = 0`.
-/

namespace RealRooted.Applications.OEIS

/-- Raising the scaled energy to one increases the weighted block bound. -/
private theorem weightedDeco_scalar_energy_mono {a w κ H s : ℝ}
    (hw0 : 0 ≤ w) (hH1 : H ≤ 1)
    (hden : 0 < s - w * a ^ 2 / 4) :
    a ^ 2 * H + w * (1 + a * κ - a ^ 2 * H / 2) ^ 2 /
        (s - w * a ^ 2 * H / 4) ≤
      a ^ 2 + w * (1 + a * κ - a ^ 2 / 2) ^ 2 /
        (s - w * a ^ 2 / 4) := by
  have hdenH : 0 < s - w * a ^ 2 * H / 4 := by
    have hwSquare : 0 ≤ w * a ^ 2 := mul_nonneg hw0 (sq_nonneg a)
    nlinarith [mul_le_mul_of_nonneg_left hH1 hwSquare]
  have hleft :
      a ^ 2 * H + w * (1 + a * κ - a ^ 2 * H / 2) ^ 2 /
          (s - w * a ^ 2 * H / 4) =
        (w * (1 + a * κ) ^ 2 +
            a ^ 2 * H * (s - w * (1 + a * κ))) /
          (s - w * a ^ 2 * H / 4) := by
    apply (eq_div_iff hdenH.ne').2
    rw [add_mul, div_mul_cancel₀ _ hdenH.ne']
    ring
  have hright :
      a ^ 2 + w * (1 + a * κ - a ^ 2 / 2) ^ 2 /
          (s - w * a ^ 2 / 4) =
        (w * (1 + a * κ) ^ 2 +
            a ^ 2 * (s - w * (1 + a * κ))) /
          (s - w * a ^ 2 / 4) := by
    apply (eq_div_iff hden.ne').2
    rw [add_mul, div_mul_cancel₀ _ hden.ne']
    ring
  rw [hleft, hright, div_le_div_iff₀ hdenH hden]
  have hcross :
      (w * (1 + a * κ) ^ 2 + a ^ 2 * (s - w * (1 + a * κ))) *
            (s - w * a ^ 2 * H / 4) -
          (w * (1 + a * κ) ^ 2 +
              a ^ 2 * H * (s - w * (1 + a * κ))) *
            (s - w * a ^ 2 / 4) =
        a ^ 2 * (1 - H) * (s - w * (1 + a * κ) / 2) ^ 2 := by
    ring
  have hcrossNonneg :
      0 ≤ a ^ 2 * (1 - H) * (s - w * (1 + a * κ) / 2) ^ 2 := by
    positivity
  nlinarith

/-- The complete weighted scalar estimate for the scaled energy `H = wE`. -/
theorem weightedDeco_residue_energy_scalar_lt {a w κ H s : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1 / 2) (hH1 : H ≤ 1)
    (hs : 1 + w + w * (1 + a) * κ < s) :
    a ^ 2 * H + w * (1 + a * κ - a ^ 2 * H / 2) ^ 2 /
        (s - w * a ^ 2 * H / 4) < 1 + a := by
  let L := 1 + w + w * (1 + a) * κ
  let D := 2 + (1 + a) * κ - a ^ 2 / 4
  have haSquare : a ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg ha0 (sub_nonneg.mpr ha1)]
  have hdenL : 0 < L - w * a ^ 2 / 4 := by
    have hwa : w * a ^ 2 ≤ w := by
      simpa using mul_le_mul_of_nonneg_left haSquare hw0
    have hκTerm : 0 ≤ w * (1 + a) * κ := by positivity
    dsimp [L]
    nlinarith
  have hdenS : 0 < s - w * a ^ 2 / 4 := by linarith
  have hmono := weightedDeco_scalar_energy_mono
    (a := a) (w := w) (κ := κ) (H := H) (s := s) hw0 hH1 hdenS
  have hsToL :
      a ^ 2 + w * (1 + a * κ - a ^ 2 / 2) ^ 2 /
          (s - w * a ^ 2 / 4) ≤
        a ^ 2 + w * (1 + a * κ - a ^ 2 / 2) ^ 2 /
          (L - w * a ^ 2 / 4) := by
    have hnum : 0 ≤ w * (1 + a * κ - a ^ 2 / 2) ^ 2 := by positivity
    have hquot :
        w * (1 + a * κ - a ^ 2 / 2) ^ 2 / (s - w * a ^ 2 / 4) ≤
          w * (1 + a * κ - a ^ 2 / 2) ^ 2 / (L - w * a ^ 2 / 4) :=
      div_le_div_of_nonneg_left hnum hdenL (by linarith)
    linarith
  have hdenD : 0 < D := by
    dsimp [D]
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 + a) hκ0]
  have hscale :
      w * (1 + a * κ - a ^ 2 / 2) ^ 2 /
          (L - w * a ^ 2 / 4) ≤
        (1 + a * κ - a ^ 2 / 2) ^ 2 / D := by
    rw [div_le_div_iff₀ hdenL hdenD]
    have hgap : 0 ≤ (L - w * a ^ 2 / 4) - w * D := by
      dsimp [L, D]
      nlinarith
    have hprod :
        0 ≤ (1 + a * κ - a ^ 2 / 2) ^ 2 *
          ((L - w * a ^ 2 / 4) - w * D) := by
      positivity
    nlinarith
  have hend := a144438_scalar_endpoint_lt ha0 ha1 hκ0 hκ1
  dsimp [D] at hscale
  have hscaleAdd :
      a ^ 2 + w * (1 + a * κ - a ^ 2 / 2) ^ 2 /
          (L - w * a ^ 2 / 4) ≤
        a ^ 2 + (1 + a * κ - a ^ 2 / 2) ^ 2 /
          (2 + (1 + a) * κ - a ^ 2 / 4) := by
    linarith
  exact lt_of_le_of_lt (hmono.trans (hsToL.trans hscaleAdd)) hend

end RealRooted.Applications.OEIS
