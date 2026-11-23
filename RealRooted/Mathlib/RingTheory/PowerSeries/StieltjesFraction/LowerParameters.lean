/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.LowerSupportParameters

/-!
# Lowering the initial Stieltjes parameter

A nonnegative initial parameter can be replaced by any smaller nonnegative
value without changing any numerator. This is the reduction in Sokal-Walrad,
arXiv:2404.12131v1, proof of Theorem 2(c)-(b), equations (14)-(18).
The construction also works when the shift is zero or an odd parameter vanishes.
-/

public section

namespace PowerSeries

/-- Even parameters after lowering the initial value to `r`. -/
@[expose] noncomputable def lowerStieltjesParameters
    (c r : ℝ) (u v : ℕ → ℝ) : ℕ → ℝ
  | 0 => r
  | k + 1 => u (k + 1) *
      (v k / (v k + c * (u k - lowerStieltjesParameters c r u v k))) *
      ((1 + lowerStieltjesParameters c r u v k) / (1 + u k))

/-- Lowering the initial value keeps every even parameter between zero and
its original value. -/
theorem lowerStieltjesParameters_bounds {c r : ℝ} (hc : 0 ≤ c)
    {u v : ℕ → ℝ} (hu : ∀ k, 0 ≤ u k) (hv : ∀ k, 0 ≤ v k)
    (hr : 0 ≤ r) (hru : r ≤ u 0) (n : ℕ) :
    0 ≤ lowerStieltjesParameters c r u v n ∧
      lowerStieltjesParameters c r u v n ≤ u n := by
  induction n with
  | zero => exact ⟨hr, hru⟩
  | succ n ih =>
      let w := lowerStieltjesParameters c r u v n
      let V := v n + c * (u n - w)
      have hw : 0 ≤ w := ih.1
      have hwu : w ≤ u n := ih.2
      have hvV : v n ≤ V := le_add_of_nonneg_right (mul_nonneg hc (sub_nonneg.mpr hwu))
      have hV : 0 ≤ V := (hv n).trans hvV
      have h1 : 0 < 1 + u n := add_pos_of_pos_of_nonneg zero_lt_one (hu n)
      change 0 ≤ u (n + 1) * (v n / V) * ((1 + w) / (1 + u n)) ∧
        u (n + 1) * (v n / V) * ((1 + w) / (1 + u n)) ≤ u (n + 1)
      by_cases hz : V = 0
      · simp only [hz, div_zero, mul_zero, zero_mul]
        exact ⟨le_rfl, hu _⟩
      · have hVp : 0 < V := lt_of_le_of_ne hV (Ne.symm hz)
        have hA : 0 ≤ v n / V := div_nonneg (hv n) hV
        have hAle : v n / V ≤ 1 := (div_le_one hVp).mpr hvV
        have hB : 0 ≤ (1 + w) / (1 + u n) :=
          div_nonneg (add_nonneg zero_le_one hw) h1.le
        have hBle : (1 + w) / (1 + u n) ≤ 1 :=
          (div_le_one h1).mpr (by linarith)
        refine ⟨mul_nonneg (mul_nonneg (hu _) hA) hB, ?_⟩
        calc
          u (n + 1) * (v n / V) * ((1 + w) / (1 + u n)) ≤
              u (n + 1) * (v n / V) := by
            simpa only [mul_one] using
              mul_le_mul_of_nonneg_left hBle (mul_nonneg (hu _) hA)
          _ ≤ u (n + 1) := by
            simpa only [mul_one] using mul_le_mul_of_nonneg_left hAle (hu _)

/-- The odd parameters increase as the initial even parameter is lowered. -/
theorem le_lowerStieltjesOddParameter {c r : ℝ} (hc : 0 ≤ c)
    {u v : ℕ → ℝ} (hu : ∀ k, 0 ≤ u k) (hv : ∀ k, 0 ≤ v k)
    (hr : 0 ≤ r) (hru : r ≤ u 0) (k : ℕ) :
    v k ≤ v k + c * (u k - lowerStieltjesParameters c r u v k) :=
  le_add_of_nonneg_right (mul_nonneg hc
    (sub_nonneg.mpr (lowerStieltjesParameters_bounds hc hu hv hr hru k).2))

/-- Lowering the initial parameter preserves every displayed numerator,
including those after a terminating zero. -/
theorem shiftedStieltjesNumerators_lower {c r : ℝ} (hc : 0 ≤ c)
    {u v : ℕ → ℝ} (hu : ∀ k, 0 ≤ u k) (hv : ∀ k, 0 ≤ v k)
    (hr : 0 ≤ r) (hru : r ≤ u 0) :
    shiftedStieltjesNumerators c (lowerStieltjesParameters c r u v)
        (fun k => v k + c * (u k - lowerStieltjesParameters c r u v k)) =
      shiftedStieltjesNumerators c u v := by
  funext n
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
  · subst n
    simp only [shiftedStieltjesNumerators_even]
    ring
  · subst n
    rw [shiftedStieltjesNumerators_odd, shiftedStieltjesNumerators_odd]
    let w := lowerStieltjesParameters c r u v k
    let V := v k + c * (u k - w)
    have hw : 0 ≤ w := (lowerStieltjesParameters_bounds hc hu hv hr hru k).1
    have hvV : v k ≤ V := le_lowerStieltjesOddParameter hc hu hv hr hru k
    have h1 : 1 + w ≠ 0 := by positivity
    have h2 : 1 + u k ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one (hu k))
    change V * (u (k + 1) * (v k / V) * ((1 + w) / (1 + u k))) / (1 + w) =
      v k * u (k + 1) / (1 + u k)
    by_cases hV : V = 0
    · have hv0 : v k = 0 := le_antisymm (by simpa only [hV] using hvV) (hv k)
      simp only [hV, hv0, div_zero, zero_div, mul_zero, zero_mul]
    · field_simp [hV, h1, h2]

/-- Any smaller nonnegative initial parameter admits a full nonnegative
parametrization with exactly the same numerator sequence. -/
theorem exists_lower_stieltjesParameters {c r : ℝ} (hc : 0 ≤ c)
    {u v : ℕ → ℝ} (hu : ∀ k, 0 ≤ u k) (hv : ∀ k, 0 ≤ v k)
    (hr : 0 ≤ r) (hru : r ≤ u 0) :
    ∃ u' v' : ℕ → ℝ, u' 0 = r ∧
      (∀ k, 0 ≤ u' k ∧ u' k ≤ u k) ∧ (∀ k, v k ≤ v' k) ∧
      shiftedStieltjesNumerators c u' v' = shiftedStieltjesNumerators c u v := by
  exact ⟨lowerStieltjesParameters c r u v,
    fun k => v k + c * (u k - lowerStieltjesParameters c r u v k), rfl,
    lowerStieltjesParameters_bounds hc hu hv hr hru,
    le_lowerStieltjesOddParameter hc hu hv hr hru,
    shiftedStieltjesNumerators_lower hc hu hv hr hru⟩

end PowerSeries
