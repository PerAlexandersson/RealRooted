module

public import RealRooted.TuranHurwitz.Laguerre.Reduction
import RealRooted.TuranHurwitz.ReciprocalRisingConvolution
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The nonzero top coefficient in part (ii)

The reciprocal rising-factorial convolution gives a strictly positive
coefficient of degree `2*m + 2*n` in every extended Turán expression.
-/

public section

open Polynomial

namespace RealRooted.TuranHurwitz

/-- The leading coefficient of every part (ii) row has a reciprocal rising normalization. -/
theorem leadingCoeff_laguerreFamily {c : LaguerreParameters} (hc : c.Admissible) (j : ℕ) :
    (laguerreFamily c j).leadingCoeff =
      (c.b₂ / c.sigma) ^ j / rising (1 / c.sigma) j := by
  have hratio : c.b₂ / c.a₁ ≠ 0 := (div_pos hc.b₂_pos hc.a₁_pos).ne'
  have hYdegree : (laguerreVariable c).natDegree = 1 := by
    rw [laguerreVariable, natDegree_C_mul hratio]
    exact natDegree_X_add_C _
  have hYleading : (laguerreVariable c).leadingCoeff = c.b₂ / c.a₁ := by
    simp [laguerreVariable, laguerreShift, leadingCoeff_mul]
  rw [laguerreFamily_eq_generalizedLaguerre hc, leadingCoeff_mul,
    leadingCoeff_C, leadingCoeff_comp (by rw [hYdegree]; decide),
    leadingCoeff_generalizedLaguerre, natDegree_generalizedLaguerre,
    hYleading, one_mul, laguerreScale]
  rw [div_mul_eq_mul_div, ← mul_pow]
  congr 2
  field_simp [hc.a₁_pos.ne', hc.sigma_pos.ne']

/-- Every part (ii) Turán polynomial lies in the same explicit degree box. -/
theorem natDegree_turan_laguerreFamily_le {c : LaguerreParameters} (hc : c.Admissible)
    (m n : ℕ) : (turan m n (laguerreFamily c)).natDegree ≤ 2 * m + 2 * n := by
  rw [turan]
  apply natDegree_sum_le_of_forall_le
  intro j hj
  have hjle : j ≤ 2 * n := by simpa using Finset.mem_range.mp hj
  apply (natDegree_C_mul_le _ _).trans
  apply natDegree_mul_le.trans
  rw [(laguerreFamily_natDegree_and_leadingCoeff_pos hc (m + j)).1,
    (laguerreFamily_natDegree_and_leadingCoeff_pos hc (m + 2 * n - j)).1]
  lia

/-- The top coefficient is the positive value computed in Shi's nonzero lemma. -/
theorem coeff_turan_laguerreFamily_top {c : LaguerreParameters} (hc : c.Admissible)
    (m n : ℕ) :
    (turan m n (laguerreFamily c)).coeff (2 * m + 2 * n) =
      (c.b₂ / c.sigma) ^ (2 * m + 2 * n) /
        ((n.factorial : ℝ) * rising (1 / c.sigma) m ^ 2 *
          rising (1 / c.sigma + m) n * rising (1 / c.sigma + m) (2 * n)) := by
  let b := 1 / c.sigma
  let v := c.b₂ / c.sigma
  have hb : 0 < b := one_div_pos.mpr hc.sigma_pos
  have hterm (j : ℕ) (hj : j ≤ 2 * n) :
      (C ((-1 : ℝ) ^ (n + j) /
          ((j.factorial : ℝ) * ((2 * n - j).factorial : ℝ))) *
        (laguerreFamily c (m + j) * laguerreFamily c (m + 2 * n - j))).coeff
          (2 * m + 2 * n) =
        ((-1 : ℝ) ^ n * v ^ (2 * m + 2 * n) / rising b m ^ 2) *
          ((-1 : ℝ) ^ j / ((j.factorial : ℝ) * ((2 * n - j).factorial : ℝ) *
            rising (b + m) j * rising (b + m) (2 * n - j))) := by
    have hd₁ := (laguerreFamily_natDegree_and_leadingCoeff_pos hc (m + j)).1
    have hd₂ := (laguerreFamily_natDegree_and_leadingCoeff_pos hc (m + 2 * n - j)).1
    have hadd : (m + j) + (m + 2 * n - j) = 2 * m + 2 * n := by lia
    have hc₁ : (laguerreFamily c (m + j)).coeff (m + j) =
        (laguerreFamily c (m + j)).leadingCoeff := by
      simpa only [hd₁] using (coeff_natDegree (p := laguerreFamily c (m + j)))
    have hc₂ : (laguerreFamily c (m + 2 * n - j)).coeff (m + 2 * n - j) =
        (laguerreFamily c (m + 2 * n - j)).leadingCoeff := by
      simpa only [hd₂] using (coeff_natDegree (p := laguerreFamily c (m + 2 * n - j)))
    have hmul :
        (laguerreFamily c (m + j) * laguerreFamily c (m + 2 * n - j)).coeff
          (2 * m + 2 * n) =
        (laguerreFamily c (m + j)).leadingCoeff *
          (laguerreFamily c (m + 2 * n - j)).leadingCoeff := by
      rw [← hadd, coeff_mul_add_eq_of_natDegree_le hd₁.le hd₂.le, hc₁, hc₂]
    rw [coeff_C_mul, hmul, leadingCoeff_laguerreFamily hc, leadingCoeff_laguerreFamily hc]
    rw [show m + 2 * n - j = m + (2 * n - j) by lia,
      rising_add, rising_add, pow_add]
    change _ = _
    have hvpow : v ^ (m + j) * v ^ (m + (2 * n - j)) =
        v ^ (2 * m + 2 * n) := by rw [← pow_add]; congr 1; lia
    have hfj : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
    have hfk : ((2 * n - j).factorial : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (2 * n - j)
    dsimp [b, v] at hvpow ⊢
    field_simp [(rising_pos hb m).ne',
      (rising_pos (add_pos_of_pos_of_nonneg hb (Nat.cast_nonneg m)) j).ne',
      (rising_pos (add_pos_of_pos_of_nonneg hb (Nat.cast_nonneg m)) (2 * n - j)).ne']
    rw [hvpow]
  rw [turan, finsetSum_coeff]
  calc
    _ = ((-1 : ℝ) ^ n * v ^ (2 * m + 2 * n) / rising b m ^ 2) *
        ∑ j ∈ Finset.range (2 * n + 1),
          (-1 : ℝ) ^ j / ((j.factorial : ℝ) * ((2 * n - j).factorial : ℝ) *
            rising (b + m) j * rising (b + m) (2 * n - j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      exact hterm j (by simpa using Finset.mem_range.mp hj)
    _ = _ := by
      rw [alternating_inverse_rising_convolution
        (add_pos_of_pos_of_nonneg hb (Nat.cast_nonneg m))]
      have hsign : ((-1 : ℝ) ^ n) ^ 2 = 1 := by
        rw [pow_two, ← mul_pow]
        norm_num
      dsimp [b, v]
      field_simp
      rw [hsign, one_mul]

/-- The top coefficient is strictly positive, so the limiting polynomial cannot vanish. -/
theorem coeff_turan_laguerreFamily_top_pos {c : LaguerreParameters} (hc : c.Admissible)
    (m n : ℕ) : 0 < (turan m n (laguerreFamily c)).coeff (2 * m + 2 * n) := by
  rw [coeff_turan_laguerreFamily_top hc]
  have hb := one_div_pos.mpr hc.sigma_pos
  exact div_pos (pow_pos (div_pos hc.b₂_pos hc.sigma_pos) _)
    (mul_pos (mul_pos (mul_pos (by exact_mod_cast Nat.factorial_pos n)
      (pow_pos (rising_pos hb m) _))
      (rising_pos (add_pos_of_pos_of_nonneg hb (Nat.cast_nonneg m)) n))
      (rising_pos (add_pos_of_pos_of_nonneg hb (Nat.cast_nonneg m)) (2 * n)))

/-- Every part (ii) Turán polynomial is nonzero, including the case `n = 0`. -/
theorem turan_laguerreFamily_ne_zero {c : LaguerreParameters} (hc : c.Admissible) (m n : ℕ) :
    turan m n (laguerreFamily c) ≠ 0 := by
  intro h
  have := coeff_turan_laguerreFamily_top_pos hc m n
  simp [h] at this

end RealRooted.TuranHurwitz
