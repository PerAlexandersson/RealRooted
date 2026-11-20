module

public import RealRooted.EffectiveBKW.Tail
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bounding two real residual modes

The cofactor roots in the path-cube application have opposite signs. A unit-circle
inequality bounds their normalized residues directly by a geometric tail. This
avoids infinite-series evaluation in the pointwise remainder estimate.
-/

@[expose] public section

namespace RealRooted.EffectiveBKW.PathCube.RationalSeries

/-- The reversed cubic numerator in normalized reciprocal-root coordinates. -/
noncomputable def numeratorValue (a b c x : ℝ) : ℝ := x ^ 3 + a * x ^ 2 + b * x + c

/-- The numerator weights after extracting the smallest geometric power. -/
noncomputable def geometricWeight (q β₁ β₂ β₃ : ℝ) (k : ℕ) : ℝ :=
  q ^ (k + 3) + β₁ * q ^ (k + 2) + β₂ * q ^ (k + 1) + β₃ * q ^ k

/-- The normalized squared distance from a real point to a unit complex root. -/
noncomputable def pairDistance (a c x : ℝ) : ℝ := (x - a) ^ 2 + c ^ 2

/-- A unit-circle identity controls the sine divided by squared distance. -/
theorem mul_one_sub_sq_le_pairDistance {a c : ℝ}
    (hu : a ^ 2 + c ^ 2 = 1) (hc : 0 ≤ c) (x : ℝ) :
    c * (1 - x ^ 2) ≤ pairDistance a c x := by
  have he : (1 + c) * (pairDistance a c x - c * (1 - x ^ 2)) =
      ((1 + c) * x - a) ^ 2 := by
    dsimp [pairDistance]
    linear_combination c * hu
  have hprod : 0 ≤ (1 + c) * (pairDistance a c x - c * (1 - x ^ 2)) := by
    rw [he]
    exact sq_nonneg _
  have hpos : 0 < 1 + c := by linarith
  have hdiff := nonneg_of_mul_nonneg_right hprod hpos
  linarith

/-- On a smaller real disk, the normalized sine/distance ratio is uniformly bounded. -/
theorem div_pairDistance_le {a c q x : ℝ} (hu : a ^ 2 + c ^ 2 = 1)
    (hc : 0 < c) (hq : 0 ≤ q) (hq1 : q < 1) (hx : |x| ≤ q) :
    c / pairDistance a c x ≤ 1 / (1 - q ^ 2) := by
  have hq2 : 0 < 1 - q ^ 2 := by nlinarith
  have hd : 0 < pairDistance a c x := by dsimp [pairDistance]; positivity
  have hx2 : x ^ 2 ≤ q ^ 2 := by
    have hmul := mul_nonneg (sub_nonneg.mpr hx)
      (show 0 ≤ q + |x| by positivity)
    nlinarith [sq_abs x]
  apply (div_le_div_iff₀ hd hq2).mpr
  have h := mul_one_sub_sq_le_pairDistance hu hc.le x
  nlinarith [mul_nonneg hc.le (sub_nonneg.mpr hx2)]

/-- Bound the normalized cubic numerator times a geometric power by the weights. -/
theorem abs_numeratorValue_mul_pow_le {a b c β₁ β₂ β₃ q x : ℝ}
    (ha : |a| ≤ β₁) (hb : |b| ≤ β₂) (hc : |c| ≤ β₃)
    (hx : |x| ≤ q) (k : ℕ) :
    |numeratorValue a b c x| * |x| ^ (k + 1) ≤
      |x| * geometricWeight q β₁ β₂ β₃ k := by
  have hβ₁ : 0 ≤ β₁ := (abs_nonneg a).trans ha
  have hβ₂ : 0 ≤ β₂ := (abs_nonneg b).trans hb
  have hβ₃ : 0 ≤ β₃ := (abs_nonneg c).trans hc
  have hnum : |numeratorValue a b c x| ≤ |x| ^ 3 + β₁ * |x| ^ 2 + β₂ * |x| + β₃ := by
    calc
      _ ≤ |x ^ 3 + a * x ^ 2 + b * x| + |c| := abs_add_le _ _
      _ ≤ (|x ^ 3 + a * x ^ 2| + |b * x|) + |c| := by gcongr; exact abs_add_le _ _
      _ ≤ ((|x ^ 3| + |a * x ^ 2|) + |b * x|) + |c| := by gcongr; exact abs_add_le _ _
      _ ≤ _ := by simp only [abs_mul, abs_pow]; gcongr
  calc
    _ ≤ (|x| ^ 3 + β₁ * |x| ^ 2 + β₂ * |x| + β₃) * |x| ^ (k + 1) :=
      mul_le_mul_of_nonneg_right hnum (pow_nonneg (abs_nonneg x) _)
    _ = |x| * (|x| ^ (k + 3) + β₁ * |x| ^ (k + 2) +
        β₂ * |x| ^ (k + 1) + β₃ * |x| ^ k) := by
      simp only [pow_add, pow_one]
      ring
    _ ≤ _ := by unfold geometricWeight; gcongr

/-- A single real residual mode is controlled by its share of the root separation. -/
theorem real_mode_bound {a c q x s u v w β₁ β₂ β₃ : ℝ}
    (hu : a ^ 2 + c ^ 2 = 1) (hc : 0 < c) (hq : 0 ≤ q) (hq1 : q < 1)
    (hx : |x| ≤ q) (hs : 0 < s) (h₁ : |u| ≤ β₁) (h₂ : |v| ≤ β₂)
    (h₃ : |w| ≤ β₃) (k : ℕ) :
    c * |numeratorValue u v w x / (pairDistance a c x * s)| * |x| ^ (k + 1) ≤
      geometricWeight q β₁ β₂ β₃ k / (1 - q ^ 2) * (|x| / s) := by
  have hd : 0 < pairDistance a c x := by dsimp [pairDistance]; positivity
  have hnum := abs_numeratorValue_mul_pow_le h₁ h₂ h₃ hx k
  have hratio := div_pairDistance_le hu hc hq hq1 hx
  rw [abs_div, abs_mul, abs_of_pos hd, abs_of_pos hs]
  calc
    _ = (c / pairDistance a c x) *
        (|numeratorValue u v w x| * |x| ^ (k + 1)) / s := by ring
    _ ≤ (c / pairDistance a c x) *
        (|x| * geometricWeight q β₁ β₂ β₃ k) / s := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hnum (div_nonneg hc.le hd.le)) hs.le
    _ ≤ (1 / (1 - q ^ 2)) * (|x| * geometricWeight q β₁ β₂ β₃ k) / s := by
      apply div_le_div_of_nonneg_right _ hs.le
      apply mul_le_mul_of_nonneg_right hratio
      exact (mul_nonneg (abs_nonneg _) (pow_nonneg (abs_nonneg _) _)).trans hnum
    _ = _ := by ring

/-- The geometric bound is smaller than the already verified quadratic majorant tail. -/
theorem geometric_le_majorantTail {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (M : ℕ) :
    q ^ M / (1 - q ^ 2) ≤ majorantTail q 2 M := by
  rw [majorantTail_two hq hq1]
  have hpos : 0 < 1 - q := sub_pos.mpr hq1
  have hq2 : 0 < 1 - q ^ 2 := by nlinarith
  have hfac : 1 ≤ (M : ℝ) + 1 - M * q := by
    nlinarith [mul_nonneg (Nat.cast_nonneg M : (0 : ℝ) ≤ M) hpos.le]
  have hden : (1 - q) ^ 2 ≤ 1 - q ^ 2 := by nlinarith [mul_nonneg hq hpos.le]
  apply (div_le_div_iff₀ hq2 (sq_pos_of_pos hpos)).mpr
  calc
    _ ≤ q ^ M * (1 - q ^ 2) := mul_le_mul_of_nonneg_left hden (pow_nonneg hq M)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hq2.le
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hfac (pow_nonneg hq M)

/-- The coefficient of a real cofactor mode, in normalized coordinates. -/
noncomputable def realResidue (a c u v w x y : ℝ) : ℝ :=
  numeratorValue u v w x / (pairDistance a c x * (x - y))

/-- The sum of the two real residual modes. -/
noncomputable def modeRemainder (a c u v w x y : ℝ) (n : ℕ) : ℝ :=
  realResidue a c u v w x y * x ^ n + realResidue a c u v w y x * y ^ n

/-- Opposite signs make the two separation weights sum to one. -/
theorem two_real_modes_bound {a c q x y u v w β₁ β₂ β₃ : ℝ}
    (hu : a ^ 2 + c ^ 2 = 1) (hc : 0 < c) (hq : 0 ≤ q) (hq1 : q < 1)
    (hx : 0 < x) (hy : y < 0) (hxq : |x| ≤ q) (hyq : |y| ≤ q)
    (h₁ : |u| ≤ β₁) (h₂ : |v| ≤ β₂) (h₃ : |w| ≤ β₃) (k : ℕ) :
    c * |modeRemainder a c u v w x y (k + 1)| ≤
      geometricWeight q β₁ β₂ β₃ k / (1 - q ^ 2) := by
  have hs : 0 < x - y := by linarith
  have hX := real_mode_bound hu hc hq hq1 hxq hs h₁ h₂ h₃ k
  have hY := real_mode_bound hu hc hq hq1 hyq hs h₁ h₂ h₃ k
  have hswap : |numeratorValue u v w y / (pairDistance a c y * (x - y))| =
      |realResidue a c u v w y x| := by
    unfold realResidue
    rw [show y - x = -(x - y) by ring, mul_neg, div_neg, abs_neg]
  rw [hswap] at hY
  change c * |realResidue a c u v w x y| * |x| ^ (k + 1) ≤ _ at hX
  have htri : |modeRemainder a c u v w x y (k + 1)| ≤
      |realResidue a c u v w x y| * |x| ^ (k + 1) +
        |realResidue a c u v w y x| * |y| ^ (k + 1) := by
    simpa only [modeRemainder, abs_mul, abs_pow] using
      abs_add_le (realResidue a c u v w x y * x ^ (k + 1))
        (realResidue a c u v w y x * y ^ (k + 1))
  have hweights : |x| / (x - y) + |y| / (x - y) = 1 := by
    rw [abs_of_pos hx, abs_of_neg hy, ← add_div, ← sub_eq_add_neg, div_self hs.ne']
  calc
    _ ≤ c * (|realResidue a c u v w x y| * |x| ^ (k + 1) +
        |realResidue a c u v w y x| * |y| ^ (k + 1)) :=
      mul_le_mul_of_nonneg_left htri hc.le
    _ = c * |realResidue a c u v w x y| * |x| ^ (k + 1) +
        c * |realResidue a c u v w y x| * |y| ^ (k + 1) := by ring
    _ ≤ geometricWeight q β₁ β₂ β₃ k / (1 - q ^ 2) * (|x| / (x - y)) +
        geometricWeight q β₁ β₂ β₃ k / (1 - q ^ 2) * (|y| / (x - y)) := add_le_add hX hY
    _ = _ := by rw [← mul_add, hweights, mul_one]

/-- The direct residue majorant is bounded by the existing four-weight tail. -/
theorem geometricWeight_div_le_tail {q β₁ β₂ β₃ : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    (h₁ : 0 ≤ β₁) (h₂ : 0 ≤ β₂) (h₃ : 0 ≤ β₃) (k : ℕ) :
    geometricWeight q β₁ β₂ β₃ k / (1 - q ^ 2) ≤
      tail q [1, β₁, β₂, β₃] 2 (k + 1) := by
  have hsub₁ : k + 1 + 2 - 1 = k + 2 := by lia
  have hsub₂ : k + 1 + 2 - 2 = k + 1 := by lia
  have hsub₃ : k + 1 + 2 - 3 = k := by lia
  calc
    _ = q ^ (k + 3) / (1 - q ^ 2) + β₁ * (q ^ (k + 2) / (1 - q ^ 2)) +
        β₂ * (q ^ (k + 1) / (1 - q ^ 2)) + β₃ * (q ^ k / (1 - q ^ 2)) := by
      unfold geometricWeight
      ring
    _ ≤ majorantTail q 2 (k + 3) + β₁ * majorantTail q 2 (k + 2) +
        β₂ * majorantTail q 2 (k + 1) + β₃ * majorantTail q 2 k := by
      exact add_le_add (add_le_add (add_le_add (geometric_le_majorantTail hq hq1 _)
        (mul_le_mul_of_nonneg_left (geometric_le_majorantTail hq hq1 _) h₁))
        (mul_le_mul_of_nonneg_left (geometric_le_majorantTail hq hq1 _) h₂))
        (mul_le_mul_of_nonneg_left (geometric_le_majorantTail hq hq1 _) h₃)
    _ = _ := by
      norm_num [tail, Finset.sum_range_succ, List.getD, hsub₁, hsub₂, hsub₃]

/-- The two real cofactor modes satisfy the same uniform tail estimate consumed
by the effective BKW domination supplier. -/
theorem two_real_modes_le_tail {a c q x y u v w β₁ β₂ β₃ : ℝ}
    (hu : a ^ 2 + c ^ 2 = 1) (hc : 0 < c) (hq : 0 ≤ q) (hq1 : q < 1)
    (hx : 0 < x) (hy : y < 0) (hxq : |x| ≤ q) (hyq : |y| ≤ q)
    (h₁ : |u| ≤ β₁) (h₂ : |v| ≤ β₂) (h₃ : |w| ≤ β₃) (k : ℕ) :
    c * |modeRemainder a c u v w x y (k + 1)| ≤
      tail q [1, β₁, β₂, β₃] 2 (k + 1) :=
  (two_real_modes_bound hu hc hq hq1 hx hy hxq hyq h₁ h₂ h₃ k).trans
    (geometricWeight_div_le_tail hq hq1 ((abs_nonneg u).trans h₁)
      ((abs_nonneg v).trans h₂) ((abs_nonneg w).trans h₃) k)

end RealRooted.EffectiveBKW.PathCube.RationalSeries
