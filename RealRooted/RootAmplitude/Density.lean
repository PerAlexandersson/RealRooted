import RealRooted.RootAmplitude.Convex
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Log-gap density criteria for root-amplitude convexity

A reciprocal bound on consecutive logarithmic gaps yields convexity of a
positive root-magnitude sequence. The module also provides perturbative and
outer-region forms of that criterion.
-/

namespace RealRooted.RootAmplitude

open Real

/-! ### The Padé bound -/

/-- `(2 - b) e^b ≤ 2 + b` for `0 ≤ b ≤ 1`, from the degree-three Taylor bound. -/
theorem sub_mul_exp_le {b : ℝ} (h0 : 0 ≤ b) (h1 : b ≤ 1) :
    (2 - b) * Real.exp b ≤ 2 + b := by
  have hb := Real.exp_bound' h0 h1 (n := 3) (by norm_num)
  have hsum : ∑ m ∈ Finset.range 3, b ^ m / (Nat.factorial m) = 1 + b + b ^ 2 / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hsum] at hb
  norm_num [Nat.factorial] at hb
  nlinarith [hb, h0, h1, sq_nonneg b, pow_nonneg h0 3, pow_nonneg h0 4]

/-- The `[1/1]` Padé bound `1 - exp (-b) ≤ 2b / (2 + b)` for `b ≥ 0`. -/
theorem one_sub_exp_neg_le {b : ℝ} (hb : 0 ≤ b) :
    1 - Real.exp (-b) ≤ 2 * b / (2 + b) := by
  have h2b : (0 : ℝ) < 2 + b := by linarith
  have hE : (0 : ℝ) < Real.exp (-b) := Real.exp_pos _
  have key : 2 - b ≤ (2 + b) * Real.exp (-b) := by
    rcases le_or_gt 2 b with hcase | hcase
    · nlinarith [hE]
    rcases le_or_gt 1 b with hcase1 | hcase1
    · have h1 : 2 - b ≤ Real.exp 1 * Real.exp (-b) := by
        have h := Real.add_one_le_exp (1 - b)
        rw [show (1 : ℝ) - b = 1 + -b by ring, Real.exp_add] at h
        linarith
      have he : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
      nlinarith [hE, h1, he]
    · have hpade := sub_mul_exp_le hb (le_of_lt hcase1)
      have hEE : Real.exp b * Real.exp (-b) = 1 := by
        rw [← Real.exp_add]
        simp
      nlinarith [hE, hpade, hEE, Real.exp_pos b]
  rw [le_div_iff₀ h2b]
  nlinarith [key]

/-! ### The criterion -/

/-- The reciprocal criterion `1 / a ≤ 1 / b + 1 / 2` implies
`2b / (2 + b) ≤ a`. -/
theorem le_of_inv_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : 1 / a ≤ 1 / b + 1 / 2) : 2 * b / (2 + b) ≤ a := by
  have h2b : (0 : ℝ) < 2 + b := by linarith
  have hrw : 1 / b + 1 / 2 = (2 + b) / (2 * b) := by field_simp
  rw [hrw, div_le_div_iff₀ ha (by positivity)] at h
  rw [div_le_iff₀ h2b]
  nlinarith [h, ha, hb]

/-- A logarithmic-gap criterion forces convexity at the corresponding index. -/
theorem gap_le_gap_of_criterion (g : ℕ → ℝ) (hpos : ∀ i, 0 < g i) (k : ℕ)
    (hb : 0 ≤ Real.log (g (k + 1) / g k))
    (hcrit : 2 * Real.log (g (k + 1) / g k) / (2 + Real.log (g (k + 1) / g k))
      ≤ Real.log (g (k + 2) / g (k + 1))) :
    gap g k ≤ gap g (k + 1) := by
  have hgk : 0 < g k := hpos k
  have hgk1 : 0 < g (k + 1) := hpos (k + 1)
  have hgk2 : 0 < g (k + 2) := hpos (k + 2)
  set b : ℝ := Real.log (g (k + 1) / g k) with hbdef
  set a : ℝ := Real.log (g (k + 2) / g (k + 1)) with hadef
  have hga : g (k + 2) = g (k + 1) * Real.exp a := by
    rw [hadef, Real.exp_log (by positivity)]
    field_simp
  have hgb : g k = g (k + 1) * Real.exp (-b) := by
    rw [Real.exp_neg, hbdef, Real.exp_log (by positivity)]
    field_simp
  have hpade := one_sub_exp_neg_le hb
  have hea : a ≤ Real.exp a - 1 := by linarith [Real.add_one_le_exp a]
  have hchain : 1 - Real.exp (-b) ≤ Real.exp a - 1 :=
    le_trans hpade (le_trans hcrit hea)
  change g (k + 1) - g k ≤ g (k + 2) - g (k + 1)
  rw [hga, hgb]
  nlinarith [hgk1, hchain]

/-- The reciprocal logarithmic-gap criterion also forces convexity. -/
theorem gap_le_gap_of_inv_criterion (g : ℕ → ℝ) (hpos : ∀ i, 0 < g i) (k : ℕ)
    (hb : 0 < Real.log (g (k + 1) / g k))
    (ha : 0 < Real.log (g (k + 2) / g (k + 1)))
    (hcrit : 1 / Real.log (g (k + 2) / g (k + 1))
      ≤ 1 / Real.log (g (k + 1) / g k) + 1 / 2) :
    gap g k ≤ gap g (k + 1) :=
  gap_le_gap_of_criterion g hpos k (le_of_lt hb) (le_of_inv_le ha hb hcrit)

/-! ### Transferring the criterion from a model -/

/-- Moving a positive quantity by at most `e < d / 2` moves its reciprocal by
at most `2e / d²`. -/
theorem abs_inv_sub_inv_le {d d' e : ℝ} (hd : 0 < d) (he : 0 ≤ e) (hlt : e < d / 2)
    (h : |d' - d| ≤ e) : |1 / d' - 1 / d| ≤ 2 * e / d ^ 2 := by
  have hb := abs_le.mp h
  have hd' : d / 2 < d' := by linarith [hb.1]
  have hd'pos : 0 < d' := by linarith
  have hrw : 1 / d' - 1 / d = (d - d') / (d' * d) := by
    field_simp
  rw [hrw, abs_div, abs_of_pos (by positivity : (0 : ℝ) < d' * d)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have habs : |d - d'| ≤ e := by
    rw [abs_sub_comm]
    exact h
  have hk1 : |d - d'| * d ^ 2 ≤ e * d ^ 2 := by
    nlinarith [habs, sq_nonneg d]
  have hk2 : e * d ^ 2 ≤ 2 * e * (d' * d) := by
    nlinarith [mul_nonneg he (le_of_lt hd), hd', hd, he]
  linarith

/-- A model reciprocal-gap estimate transfers through a uniform additive
perturbation of the two gaps. -/
theorem inv_gap_diff_transfer {D D' d d' e C dmin : ℝ}
    (hdmin : 0 < dmin) (hD : dmin ≤ D) (hD' : dmin ≤ D')
    (he : 0 ≤ e) (hlt : e < dmin / 2)
    (hd : |d - D| ≤ e) (hd' : |d' - D'| ≤ e)
    (hmodel : 1 / D' - 1 / D ≤ C) :
    1 / d' - 1 / d ≤ C + 4 * e / dmin ^ 2 := by
  have hDpos : 0 < D := lt_of_lt_of_le hdmin hD
  have hD'pos : 0 < D' := lt_of_lt_of_le hdmin hD'
  have h1 : |1 / d - 1 / D| ≤ 2 * e / D ^ 2 :=
    abs_inv_sub_inv_le hDpos he (by linarith) hd
  have h2 : |1 / d' - 1 / D'| ≤ 2 * e / D' ^ 2 :=
    abs_inv_sub_inv_le hD'pos he (by linarith) hd'
  have hb1 := abs_le.mp h1
  have hb2 := abs_le.mp h2
  have hs1 : 2 * e / D ^ 2 ≤ 2 * e / dmin ^ 2 := by
    refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
    nlinarith
  have hs2 : 2 * e / D' ^ 2 ≤ 2 * e / dmin ^ 2 := by
    refine div_le_div_of_nonneg_left (by linarith) (by positivity) ?_
    nlinarith
  have hfin : 1 / d' - 1 / d
      ≤ (1 / D' - 1 / D) + (2 * e / D' ^ 2 + 2 * e / D ^ 2) := by
    linarith [hb1.1, hb2.2]
  have hfin2 : (2 * e / D' ^ 2 + 2 * e / D ^ 2) ≤ 4 * e / dmin ^ 2 := by
    have hsplit : (4 : ℝ) * e / dmin ^ 2 = 2 * e / dmin ^ 2 + 2 * e / dmin ^ 2 := by
      ring
    rw [hsplit]
    linarith [hs1, hs2]
  linarith [hfin, hfin2, hmodel]

/-! ### The outer-region criterion -/

/-- The reciprocal criterion holds outright when the upper gap is at least two. -/
theorem inv_criterion_of_two_le {b a : ℝ} (hb : 0 < b) (ha : 2 ≤ a) :
    1 / a ≤ 1 / b + 1 / 2 := by
  have h1 : 1 / a ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have h2 : 0 < 1 / b := by positivity
  linarith

/-- A sufficiently large upper logarithmic gap forces convexity without a
quantitative lower-gap estimate. -/
theorem gap_le_gap_of_two_le (g : ℕ → ℝ) (hpos : ∀ i, 0 < g i) (k : ℕ)
    (hb : 0 < Real.log (g (k + 1) / g k))
    (ha : 2 ≤ Real.log (g (k + 2) / g (k + 1))) :
    gap g k ≤ gap g (k + 1) :=
  gap_le_gap_of_inv_criterion g hpos k hb (by linarith) (inv_criterion_of_two_le hb ha)

end RealRooted.RootAmplitude
