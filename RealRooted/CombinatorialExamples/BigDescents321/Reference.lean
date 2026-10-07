import RealRooted.CombinatorialExamples.BigDescents321.Gegenbauer
import RealRooted.Favard
import RealRooted.Interlacing.OuterDifference
import Mathlib.Basic.Real.Basic

/-!
# The reference Gegenbauer family as a Favard instance

The Gegenbauer polynomials `G_j = C_j^(3/2)` have leading coefficient
`ℓ_j = (2j+1)! / (2^j (j!)²)`, and the monic `p_j = G_j / ℓ_j` satisfy the symmetric Favard
recurrence `p_(j+2) = c p_(j+1) - γ_(j+1) p_j` with
`γ_m = m(m + 2) / ((2m + 1)(2m + 3)) ∈ (0, 1/4)`.

## Main results

* `satisfiesFavardRecurrence_refMonicQ`, `satisfiesFavardRecurrence_refMonic`: the Favard
  recurrence over `ℚ` and over `ℝ`.
* `refMonic_splits`, `refMonic_roots_nodup`: `p_k` is real-rooted with simple roots.
* `abs_lt_one_of_isRoot_refMonic`: every root lies in `(-1, 1)`.
* `eval_mul_derivative_pos_of_isRoot_refMonic`: `p_k(a) p_(k+1)'(a) > 0` at roots of `p_(k+1)`.
* `gegen_eq`, `gegenReal_eq`: `G_j = ℓ_j p_j`.
-/

open Polynomial

noncomputable section

namespace RealRooted.BigDescents321

/-- The leading coefficients `ℓ_0 = 1`, `ℓ_(j+1) = ℓ_j (2j + 3)/(j + 1)` of `G_j`. -/
def gegenLead : ℕ → ℚ
  | 0 => 1
  | j + 1 => gegenLead j * (2 * j + 3) / (j + 1)

theorem gegenLead_pos (j : ℕ) : 0 < gegenLead j := by
  induction j with
  | zero => simp [gegenLead]
  | succ j ih => rw [gegenLead]; positivity

/-- The monic reference polynomials `p_j = G_j / ℓ_j` over `ℚ`. -/
def refMonicQ (j : ℕ) : ℚ[X] := C (gegenLead j)⁻¹ * gegen j

/-- The recurrence coefficients `γ_m = m(m + 2) / ((2m + 1)(2m + 3))`. -/
def refGammaQ (m : ℕ) : ℚ := m * (m + 2) / ((2 * m + 1) * (2 * m + 3))

theorem satisfiesFavardRecurrence_refMonicQ :
    SatisfiesFavardRecurrence refMonicQ (fun _ ↦ 0) refGammaQ := by
  refine ⟨?_, ?_, fun n ↦ ?_⟩
  · simp [refMonicQ, gegenLead]
  · simp only [refMonicQ, gegen_one, gegenLead]
    norm_num
    rw [show (3 : ℚ[X]) = C 3 from (map_ofNat C 3).symm, ← mul_assoc, ← C_mul]
    norm_num
  · have h := gegen_rec n
    simp only [refMonicQ, map_zero, sub_zero]
    have hl0 := gegenLead_pos n
    have hl1 := gegenLead_pos (n + 1)
    have hl2 := gegenLead_pos (n + 2)
    have r1 : gegenLead (n + 1) = gegenLead n * (2 * n + 3) / (n + 1) := by
      rw [gegenLead]
    have r2 : gegenLead (n + 2) = gegenLead (n + 1) * (2 * n + 5) / (n + 2) := by
      rw [gegenLead]; push_cast; ring
    have e1 : C (gegenLead (n + 2))⁻¹ * (2 * n + 5 : ℚ[X]) =
        C (gegenLead (n + 1))⁻¹ * (n + 2 : ℚ[X]) := by
      rw [show (2 * n + 5 : ℚ[X]) = C ((2 * n + 5 : ℚ)) by
        rw [map_add, map_mul, map_ofNat C, map_ofNat C, map_natCast],
        show (n + 2 : ℚ[X]) = C ((n + 2 : ℚ)) by rw [map_add, map_ofNat C, map_natCast],
        ← C_mul, ← C_mul, r2]
      congr 1
      field_simp
    have e2 : C (gegenLead (n + 2))⁻¹ * (n + 3 : ℚ[X]) =
        C (refGammaQ (n + 1)) * C (gegenLead n)⁻¹ * (n + 2 : ℚ[X]) := by
      rw [show (n + 3 : ℚ[X]) = C ((n + 3 : ℚ)) by rw [map_add, map_ofNat C, map_natCast],
        show (n + 2 : ℚ[X]) = C ((n + 2 : ℚ)) by rw [map_add, map_ofNat C, map_natCast],
        ← C_mul, ← C_mul, ← C_mul, r2, r1, refGammaQ]
      congr 1
      push_cast
      field_simp
      ring
    apply mul_left_cancel₀ (show (n + 2 : ℚ[X]) ≠ 0 by
      rw [show (n + 2 : ℚ[X]) = C ((n + 2 : ℚ)) by rw [map_add, map_ofNat C, map_natCast]]
      exact C_ne_zero.mpr (by positivity))
    linear_combination C (gegenLead (n + 2))⁻¹ * h + X * gegen (n + 1) * e1 -
      gegen n * e2

theorem gegen_eq (j : ℕ) : gegen j = C (gegenLead j) * refMonicQ j := by
  rw [refMonicQ, ← mul_assoc, ← C_mul, mul_inv_cancel₀ (gegenLead_pos j).ne', C_1, one_mul]

/-- `G_j` over `ℝ`. -/
def gegenReal (j : ℕ) : ℝ[X] := (gegen j).map (algebraMap ℚ ℝ)

/-- The monic reference polynomials over `ℝ`. -/
def refMonic (j : ℕ) : ℝ[X] := (refMonicQ j).map (algebraMap ℚ ℝ)

/-- `γ_m` in `ℝ`. -/
def refGamma (m : ℕ) : ℝ := refGammaQ m

theorem refGamma_pos {m : ℕ} (hm : m ≠ 0) : 0 < refGamma m := by
  have : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  simp only [refGamma, refGammaQ]; push_cast; positivity

theorem refGamma_le_quarter (m : ℕ) : refGamma m ≤ 1 / 4 := by
  simp only [refGamma, refGammaQ]
  push_cast
  rw [div_le_iff₀ (by positivity)]
  nlinarith

theorem satisfiesFavardRecurrence_refMonic :
    SatisfiesFavardRecurrence refMonic (fun _ ↦ 0) refGamma := by
  have h := satisfiesFavardRecurrence_refMonicQ.map (algebraMap ℚ ℝ)
  simp only [map_zero] at h
  exact h

theorem refGamma_succ_pos (n : ℕ) : 0 < refGamma (n + 1) := refGamma_pos (Nat.succ_ne_zero n)

theorem eval_refMonic_add_two (n : ℕ) (x : ℝ) :
    (refMonic (n + 2)).eval x = x * (refMonic (n + 1)).eval x - refGamma (n + 1) *
      (refMonic n).eval x := by
  rw [satisfiesFavardRecurrence_refMonic.2.2 n]
  simp

/-- For `c ≥ 1`: `0 < p_j(c)`, `0 < p_(j+1)(c)` and `p_j(c) ≤ 2 p_(j+1)(c)`. -/
private theorem refMonic_pos_aux {x : ℝ} (hx : 1 ≤ x) (j : ℕ) :
    0 < (refMonic j).eval x ∧ 0 < (refMonic (j + 1)).eval x ∧
      (refMonic j).eval x ≤ 2 * (refMonic (j + 1)).eval x := by
  induction j with
  | zero =>
    have h0 : (refMonic 0).eval x = 1 := by rw [satisfiesFavardRecurrence_refMonic.1]; simp
    have h1 : (refMonic 1).eval x = x := by rw [satisfiesFavardRecurrence_refMonic.2.1]; simp
    rw [h0, h1]; refine ⟨by norm_num, by linarith, by linarith⟩
  | succ j ih =>
    obtain ⟨hp0, hp1, hle⟩ := ih
    rw [eval_refMonic_add_two]
    have hg := refGamma_le_quarter (j + 1)
    have hg0 := (refGamma_succ_pos j).le
    refine ⟨hp1, ?_, ?_⟩ <;> nlinarith [mul_le_mul_of_nonneg_right hx hp1.le,
      mul_le_mul_of_nonneg_right hg hp0.le]

theorem eval_refMonic_pos {x : ℝ} (hx : 1 ≤ x) (j : ℕ) : 0 < (refMonic j).eval x :=
  (refMonic_pos_aux hx j).1

theorem eval_neg_refMonic (j : ℕ) (x : ℝ) :
    (refMonic j).eval (-x) = (-1) ^ j * (refMonic j).eval x := by
  induction j using Nat.twoStepInduction with
  | zero => rw [satisfiesFavardRecurrence_refMonic.1]; simp
  | one => rw [satisfiesFavardRecurrence_refMonic.2.1]; simp
  | more j ih ih1 =>
    rw [eval_refMonic_add_two, eval_refMonic_add_two, ih, ih1]
    ring

theorem abs_lt_one_of_isRoot_refMonic {j : ℕ} {a : ℝ} (ha : (refMonic j).IsRoot a) :
    |a| < 1 := by
  by_contra h
  push Not at h
  rcases le_or_gt 0 a with ha0 | ha0
  · rw [abs_of_nonneg ha0] at h
    exact (eval_refMonic_pos h j).ne' ha
  · rw [abs_of_neg ha0] at h
    have := eval_neg_refMonic j (-a)
    rw [neg_neg, ha.eq_zero] at this
    have hpos := eval_refMonic_pos h j
    have hs : (-1 : ℝ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
    exact hpos.ne' ((mul_eq_zero.mp this.symm).resolve_left hs)

theorem refMonic_splits (j : ℕ) : (refMonic j).Splits :=
  (isRealRooted_of_favard satisfiesFavardRecurrence_refMonic refGamma_succ_pos j).2

theorem refMonic_roots_nodup (j : ℕ) : (refMonic j).roots.Nodup :=
  roots_nodup_of_favard satisfiesFavardRecurrence_refMonic refGamma_succ_pos j

/-- At a root of `p_(k+1)`, the values `p_k(a)` and `p_(k+1)'(a)` have the same strict sign. -/
theorem eval_mul_derivative_pos_of_isRoot_refMonic {k : ℕ} {a : ℝ}
    (ha : (refMonic (k + 1)).IsRoot a) :
    0 < (refMonic k).eval a * (refMonic (k + 1)).derivative.eval a :=
  (favardInterlacing satisfiesFavardRecurrence_refMonic refGamma_succ_pos k)
    |>.eval_mul_derivative_pos_of_right_root_of_no_common
      (by unfold HasPosLeadingCoeff; rw [satisfiesFavardRecurrence_refMonic.monic k]; exact one_pos)
      (by unfold HasPosLeadingCoeff; rw [satisfiesFavardRecurrence_refMonic.monic (k + 1)]
          exact one_pos)
      (noCommonRoot_succ_of_favard satisfiesFavardRecurrence_refMonic refGamma_succ_pos k) ha

theorem gegenReal_eq (j : ℕ) : gegenReal j = C (gegenLead j : ℝ) * refMonic j := by
  rw [gegenReal, refMonic, gegen_eq, Polynomial.map_mul, map_C]
  rfl

end RealRooted.BigDescents321
