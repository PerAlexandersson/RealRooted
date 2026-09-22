import RealRooted.JacobiDeformation.JacobiMomentTransport

/-!
# Coefficients of normalized shifted Jacobi polynomials
-/

open Polynomial

noncomputable section

namespace RealRooted.JacobiDeformation

private theorem choose_mul_factorial_eq_risingFactorial
    (j : ℕ) {c d : ℝ} (i : ℕ) :
    Ring.choose ((j : ℝ) + c + d - 2 + i) i * (i.factorial : ℝ) =
      risingFactorial ((j : ℝ) + c + d - 1) i := by
  rw [Ring.choose_eq_smul, smul_eq_mul]
  change (i.factorial : ℝ)⁻¹ *
      (descPochhammer ℤ i).smeval ((j : ℝ) + c + d - 2 + i) *
        (i.factorial : ℝ) =
      risingFactorial ((j : ℝ) + c + d - 1) i
  field_simp [Nat.factorial_ne_zero]
  rw [descPochhammer_smeval_eq_ascPochhammer,
    ascPochhammer_smeval_eq_eval]
  change (ascPochhammer ℝ i).eval
      ((j : ℝ) + c + d - 2 + (i : ℝ) - (i : ℝ) + 1) =
    (ascPochhammer ℝ i).eval ((j : ℝ) + c + d - 1)
  congr 1
  ring

/-- The in-range coefficient of the shifted Jacobi polynomial normalized at
zero, in the positive source parameters `c,d`. -/
theorem coeff_normalizedShiftedJacobi_of_le
    {c d : ℝ} (hc : 0 < c) (_hd : 0 < d) {i j : ℕ} (hij : i ≤ j) :
    (normalizedShiftedJacobi j c d).coeff i =
      (-1 : ℝ) ^ i * (j.choose i : ℝ) *
        risingFactorial ((j : ℝ) + c + d - 1) i / risingFactorial c i := by
  have hnorm : 0 < Ring.choose ((j : ℝ) + c - 1) j := by
    apply ring_choose_pos
    linarith
  have hrise : 0 < risingFactorial c i := risingFactorial_pos i hc
  have hfirst := choose_mul_risingFactorial_eq_choose_mul_fallingFactorial
    hc hij
  have hsecond := choose_mul_factorial_eq_risingFactorial j (c := c) (d := d) i
  have hnat : (j.choose i : ℝ) * (i.factorial : ℝ) =
      fallingFactorial (j : ℝ) i := by
    rw [Nat.cast_choose_eq_descPochhammer_div]
    field_simp [Nat.factorial_ne_zero]
    rfl
  rw [normalizedShiftedJacobi, coeff_C_mul, coeff_shiftedJacobi,
    if_pos hij]
  field_simp [hnorm.ne', hrise.ne', Nat.factorial_ne_zero]
  calc
    Ring.choose ((j : ℝ) + (c - 1)) (j - i) *
          Ring.choose ((j : ℝ) + (c - 1) + (d - 1) + i) i *
          risingFactorial c i =
        Ring.choose ((j : ℝ) + (c - 1) + (d - 1) + i) i *
          (Ring.choose ((j : ℝ) + c - 1) (j - i) *
            risingFactorial c i) := by ring
    _ = Ring.choose ((j : ℝ) + (c - 1) + (d - 1) + i) i *
          (Ring.choose ((j : ℝ) + c - 1) j *
            fallingFactorial (j : ℝ) i) := by rw [hfirst]
    _ = Ring.choose ((j : ℝ) + c - 1) j * (j.choose i : ℝ) *
          (Ring.choose ((j : ℝ) + c + d - 2 + i) i *
            (i.factorial : ℝ)) := by rw [← hnat]; ring
    _ = Ring.choose ((j : ℝ) + c - 1) j * (j.choose i : ℝ) *
          risingFactorial ((j : ℝ) + c + d - 1) i := by rw [hsecond]

/-- Coefficients above the Jacobi degree vanish after normalization. -/
theorem coeff_normalizedShiftedJacobi_of_lt
    (j : ℕ) (c d : ℝ) {i : ℕ} (hji : j < i) :
    (normalizedShiftedJacobi j c d).coeff i = 0 := by
  rw [normalizedShiftedJacobi, coeff_C_mul, coeff_shiftedJacobi,
    if_neg (Nat.not_le.mpr hji), mul_zero]

end RealRooted.JacobiDeformation
