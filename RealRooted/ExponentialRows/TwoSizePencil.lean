module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Basic.Real.Basic
import RealRooted.QuadraticRoot
import Mathlib.Tactic

/-!
# The exact affine two-size pencil boundary

For `p = a + bt` and `q = c + dt`, every pencil `p² + λq` with
`0 ≤ λ ≤ M`, for any fixed `M > 0`, splits exactly when `ad ≥ bc`.
Thus the Hermite interval `[0, ∞)` and the ordered Chebyshev interval
`[0, 4]` give the same algebraic boundary. This module proves the pencil
criterion; it does not identify the all-row necessity with the pencil test.

Source: unpublished manuscript, RealRooted issues #2415 and #2590, round two:
https://github.com/PerAlexandersson/RealRooted/issues/2415#issuecomment-7136509900.
-/

public section

open Polynomial

namespace RealRooted.ExponentialRows

/-- The two-size affine pencil has an explicit quadratic expansion. -/
private theorem affine_pencil_eq (a b c d l : ℝ) :
    (C a + C b * X) ^ 2 + C l * (C c + C d * X) =
      C (b ^ 2) * X ^ 2 + C (2 * a * b + l * d) * X + C (a ^ 2 + l * c) := by
  simp only [map_add, map_mul, map_pow, map_ofNat]
  ring

/-- The boundary `ad ≥ bc` makes every nonnegative affine two-size pencil split.
The constant coefficient of the second weight may have either sign. -/
theorem splits_affine_pencil_of_le {a b c d l : ℝ}
    (hb : 0 ≤ b) (hl : 0 ≤ l) (hdet : b * c ≤ a * d) :
    ((C a + C b * X) ^ 2 + C l * (C c + C d * X)).Splits := by
  rw [affine_pencil_eq]
  apply quadraticPoly_splits_of_discrim_nonneg_or_linear
  rw [discrim]
  have h : 0 ≤ 4 * l * b * (a * d - b * c) := by positivity
  nlinarith [sq_nonneg (l * d)]

/-- Outside the two-size boundary, a nonsplitting pencil exists in every
positive interval starting at zero. This is an exact symbolic obstruction. -/
theorem exists_not_splits_affine_pencil {a b c d M : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) (hM : 0 < M)
    (hdet : a * d < b * c) :
    ∃ l : ℝ, 0 < l ∧ l ≤ M ∧
      ¬ ((C a + C b * X) ^ 2 + C l * (C c + C d * X)).Splits := by
  have hbpos : 0 < b := by
    by_contra h
    have hbzero : b = 0 := le_antisymm (le_of_not_gt h) hb
    rw [hbzero, zero_mul] at hdet
    exact (not_lt_of_ge (mul_nonneg ha hd)) hdet
  let u := b * (b * c - a * d)
  have hu : 0 < u := mul_pos hbpos (sub_pos.mpr hdet)
  let v := u / (d ^ 2 + u + 1)
  have hden : 0 < d ^ 2 + u + 1 := by positivity
  have hv : 0 < v := div_pos hu hden
  have hveq : v * (d ^ 2 + u + 1) = u := div_mul_cancel₀ _ hden.ne'
  have hvd : v * d ^ 2 < u := by nlinarith
  let l := min M v
  have hl : 0 < l := lt_min hM hv
  have hld : l * d ^ 2 < u :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right (min_le_right M v) (sq_nonneg d)) hvd
  refine ⟨l, hl, min_le_left M v, ?_⟩
  rw [affine_pencil_eq]
  apply quadraticPoly_not_splits_of_discrim_neg (pow_ne_zero _ hbpos.ne')
  rw [discrim]
  have hdisc : (2 * a * b + l * d) ^ 2 - 4 * b ^ 2 * (a ^ 2 + l * c) =
      l * (l * d ^ 2 - 4 * u) := by
    dsimp only [u]
    ring
  rw [hdisc]
  exact mul_neg_of_pos_of_neg hl (by linarith)

/-- The affine two-size pencil test on any positive bounded interval is
exactly `ad ≥ bc`. The coefficient `c` need not be nonnegative. -/
theorem forall_splits_affine_pencil_iff {a b c d M : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) (hM : 0 < M) :
    (∀ l : ℝ, 0 ≤ l → l ≤ M →
      ((C a + C b * X) ^ 2 + C l * (C c + C d * X)).Splits) ↔ b * c ≤ a * d := by
  constructor
  · intro h
    by_contra hdet
    obtain ⟨l, hl, hlM, hbad⟩ :=
      exists_not_splits_affine_pencil ha hb hd hM (lt_of_not_ge hdet)
    exact hbad (h l hl.le hlM)
  · intro hdet l hl _
    exact splits_affine_pencil_of_le hb hl hdet

/-- Testing every nonnegative pencil parameter gives the same exact boundary
as testing the ordered interval `[0,4]`. -/
theorem forall_nonneg_splits_affine_pencil_iff {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) :
    (∀ l : ℝ, 0 ≤ l →
      ((C a + C b * X) ^ 2 + C l * (C c + C d * X)).Splits) ↔ b * c ≤ a * d := by
  constructor
  · intro h
    exact (forall_splits_affine_pencil_iff ha hb hd (M := 4) (by norm_num)).mp
      (fun l hl _ => h l hl)
  · intro hdet l hl
    exact splits_affine_pencil_of_le hb hl hdet

end RealRooted.ExponentialRows
