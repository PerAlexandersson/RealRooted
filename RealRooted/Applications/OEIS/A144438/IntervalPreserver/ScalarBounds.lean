import RealRooted.Applications.OEIS.A144438.IntervalPreserver.Basic

/-!
# Scalar bounds for the A144438 residue-energy induction

This file proves the elementary inequality that closes the matrix estimate in
the diagonal argument.  It is kept separate from the spectral construction so
that the analytic layer can use one checked scalar endpoint.
-/

namespace RealRooted.Applications.OEIS

/-- The polynomial remainder in the final scalar comparison is nonnegative on
the parameter rectangle `0 ≤ a ≤ 1`, `0 ≤ κ ≤ 1 / 2`. -/
theorem a144438_scalar_remainder_nonneg {a κ : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1 / 2) :
    0 ≤ 3 * a / 2 - 5 * a ^ 2 / 4 - a ^ 3 / 4 + κ - a ^ 2 * κ ^ 2 := by
  have haFactor : 0 ≤ a * (1 - a) * (a + 6) / 4 := by positivity
  have hκFactor : 0 ≤ κ * (1 - a ^ 2 * κ) := by
    have : 0 ≤ 1 - a ^ 2 * κ := by nlinarith [sq_nonneg a]
    positivity
  nlinarith

/-- The endpoint expression occurring after the energy and Schur-complement
reductions is strictly smaller than `1 + a`. -/
theorem a144438_scalar_endpoint_lt {a κ : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1 / 2) :
    a ^ 2 + (1 + a * κ - a ^ 2 / 2) ^ 2 /
        (2 + (1 + a) * κ - a ^ 2 / 4) < 1 + a := by
  have hden : 0 < 2 + (1 + a) * κ - a ^ 2 / 4 := by
    nlinarith [sq_nonneg a, mul_nonneg (by linarith) hκ0]
  have hrem := a144438_scalar_remainder_nonneg ha0 ha1 hκ0 hκ1
  have hquot :
      (1 + a * κ - a ^ 2 / 2) ^ 2 /
          (2 + (1 + a) * κ - a ^ 2 / 4) < 1 + a - a ^ 2 := by
    rw [div_lt_iff₀ hden]
    nlinarith
  linarith

/-- Increasing the energy variable up to one can only increase the rational
matrix bound. -/
private theorem a144438_scalar_energy_mono {a κ E s : ℝ}
    (ha0 : 0 ≤ a) (hκ0 : 0 ≤ κ) (_hE0 : 0 ≤ E) (hE1 : E ≤ 1)
    (hs : 1 + a * κ < s) (hden : 0 < s - a ^ 2 / 4) :
    a ^ 2 * E + (1 + a * κ - a ^ 2 * E / 2) ^ 2 /
        (s - a ^ 2 * E / 4) ≤
      a ^ 2 + (1 + a * κ - a ^ 2 / 2) ^ 2 /
        (s - a ^ 2 / 4) := by
  have hdenE : 0 < s - a ^ 2 * E / 4 := by
    nlinarith [sq_nonneg a,
      mul_le_mul_of_nonneg_left hE1 (sq_nonneg a)]
  have hleft :
      a ^ 2 * E + (1 + a * κ - a ^ 2 * E / 2) ^ 2 /
          (s - a ^ 2 * E / 4) =
        ((1 + a * κ) ^ 2 + a ^ 2 * E * (s - (1 + a * κ))) /
          (s - a ^ 2 * E / 4) := by
    apply (eq_div_iff hdenE.ne').2
    rw [add_mul, div_mul_cancel₀ _ hdenE.ne']
    ring
  have hright :
      a ^ 2 + (1 + a * κ - a ^ 2 / 2) ^ 2 /
          (s - a ^ 2 / 4) =
        ((1 + a * κ) ^ 2 + a ^ 2 * (s - (1 + a * κ))) /
          (s - a ^ 2 / 4) := by
    apply (eq_div_iff hden.ne').2
    rw [add_mul, div_mul_cancel₀ _ hden.ne']
    ring
  rw [hleft, hright, div_le_div_iff₀ hdenE hden]
  have hslope : 0 ≤ a ^ 2 * (s - (1 + a * κ)) := by positivity
  have ht : 0 < 1 + a * κ := by positivity
  have hs0 : 0 < s := lt_trans ht hs
  have hcross :
      ((1 + a * κ) ^ 2 + a ^ 2 * (s - (1 + a * κ))) *
            (s - a ^ 2 * E / 4) -
          ((1 + a * κ) ^ 2 + a ^ 2 * E * (s - (1 + a * κ))) *
            (s - a ^ 2 / 4) =
        a ^ 2 * (1 - E) *
          ((1 + a * κ) ^ 2 / 4 + (s - (1 + a * κ)) * s) := by
    ring
  have hcrossNonneg :
      0 ≤ a ^ 2 * (1 - E) *
        ((1 + a * κ) ^ 2 / 4 + (s - (1 + a * κ)) * s) := by
    positivity
  nlinarith

/-- Increasing the Schur-complement parameter decreases the endpoint rational
bound. -/
private theorem a144438_scalar_schur_antitone {a κ s L : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hκ0 : 0 ≤ κ)
    (hLs : L < s) (_htL : 1 + a * κ < L)
    (hdenL : 0 < L - a ^ 2 / 4) :
    a ^ 2 + (1 + a * κ - a ^ 2 / 2) ^ 2 /
        (s - a ^ 2 / 4) <
      a ^ 2 + (1 + a * κ - a ^ 2 / 2) ^ 2 /
        (L - a ^ 2 / 4) := by
  have hdenS : 0 < s - a ^ 2 / 4 := by linarith
  have hsquare : 0 < (1 + a * κ - a ^ 2 / 2) ^ 2 := by
    apply sq_pos_of_pos
    have haSquare : a ^ 2 ≤ 1 := by nlinarith [mul_nonneg ha0 (sub_nonneg.mpr ha1)]
    nlinarith [mul_nonneg ha0 hκ0]
  have hrecip :
      (1 + a * κ - a ^ 2 / 2) ^ 2 / (s - a ^ 2 / 4) <
        (1 + a * κ - a ^ 2 / 2) ^ 2 / (L - a ^ 2 / 4) := by
    exact div_lt_div_of_pos_left hsquare hdenL (by linarith)
  linarith

/-- The complete scalar estimate used to prove
`bᵀ C⁻¹ b < 1 + a` in the residue-energy step. -/
theorem a144438_residue_energy_scalar_lt {a κ E s : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1 / 2)
    (hE0 : 0 ≤ E) (hE1 : E ≤ 1)
    (hs : 2 + (1 + a) * κ < s) :
    a ^ 2 * E + (1 + a * κ - a ^ 2 * E / 2) ^ 2 /
        (s - a ^ 2 * E / 4) < 1 + a := by
  let L := 2 + (1 + a) * κ
  have htL : 1 + a * κ < L := by
    dsimp [L]
    nlinarith
  have hdenL : 0 < L - a ^ 2 / 4 := by
    have haSquare : a ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg ha0 (sub_nonneg.mpr ha1)]
    dsimp [L]
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 + a) hκ0]
  have hdenS : 0 < s - a ^ 2 / 4 := by nlinarith
  calc
    a ^ 2 * E + (1 + a * κ - a ^ 2 * E / 2) ^ 2 /
          (s - a ^ 2 * E / 4) ≤
        a ^ 2 + (1 + a * κ - a ^ 2 / 2) ^ 2 /
          (s - a ^ 2 / 4) :=
      a144438_scalar_energy_mono ha0 hκ0 hE0 hE1 (lt_trans htL hs) hdenS
    _ < a ^ 2 + (1 + a * κ - a ^ 2 / 2) ^ 2 /
          (L - a ^ 2 / 4) :=
      a144438_scalar_schur_antitone ha0 ha1 hκ0 hs htL hdenL
    _ < 1 + a := by
      dsimp [L]
      exact a144438_scalar_endpoint_lt ha0 ha1 hκ0 hκ1

/-- The scalar Schur complement in the positive companion matrix is uniformly
larger than `7/4`. -/
theorem a144438_schur_complement_gt {a κ η E n : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hκ0 : 0 ≤ κ)
    (hη : η < 1) (hE0 : 0 ≤ E) (hE1 : E ≤ 1) (hn : 0 ≤ n) :
    7 / 4 <
      3 + n * (1 - a) - η + (1 + a) * κ - a ^ 2 * E / 4 := by
  have haSquare : a ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg ha0 (sub_nonneg.mpr ha1)]
  have haE : a ^ 2 * E ≤ 1 := by
    exact (mul_le_mul haSquare hE1 hE0 (by positivity)).trans (by norm_num)
  have hnTerm : 0 ≤ n * (1 - a) := mul_nonneg hn (sub_nonneg.mpr ha1)
  have hκTerm : 0 ≤ (1 + a) * κ := mul_nonneg (by linarith) hκ0
  nlinarith

end RealRooted.Applications.OEIS
