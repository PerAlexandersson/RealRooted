/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.AdmissibleParameters

/-!
# Bounded representatives of active Stieltjes parameters

After a terminating numerator, parameters can be set to zero without changing
the active equations. For a positive shift this gives coordinatewise compact
bounds from the prescribed even-indexed numerators.
-/

public section

namespace PowerSeries

/-- Without terminating numerators, active-prefix admissibility is precisely
the full-index parameter formulation. -/
theorem mem_admissibleStieltjesParameters_iff_of_ne_zero
    {a : ℕ → ℝ} (ha : ∀ n, a n ≠ 0) (c r : ℝ) :
    r ∈ admissibleStieltjesParameters c a ↔
      ∃ u v : ℕ → ℝ, u 0 = r ∧ (∀ k, 0 ≤ u k) ∧ (∀ k, 0 ≤ v k) ∧
        a = shiftedStieltjesNumerators c u v := by
  constructor
  · rintro ⟨u, v, hu0, hu, hv, hp⟩
    exact ⟨u, v, hu0, hu, hv, funext fun n => hp n (fun i _ => ha i)⟩
  · rintro ⟨u, v, hu0, hu, hv, heq⟩
    exact ⟨u, v, hu0, hu, hv, fun n _ => congrFun heq n⟩

/-- Remove the inactive even-parameter tail after the first terminating numerator. -/
@[expose] noncomputable def activeStieltjesParameters (a u : ℕ → ℝ) (k : ℕ) : ℝ := by
  classical
  exact if ∀ i < 2 * k, a i ≠ 0 then u k else 0

/-- The initial parameter always belongs to the active prefix. -/
@[simp] theorem activeStieltjesParameters_zero (a u : ℕ → ℝ) :
    activeStieltjesParameters a u 0 = u 0 := by
  simp [activeStieltjesParameters]

/-- Removing inactive parameters preserves their nonnegativity. -/
theorem activeStieltjesParameters_nonneg (a : ℕ → ℝ) {u : ℕ → ℝ}
    (hu : ∀ k, 0 ≤ u k) (k : ℕ) : 0 ≤ activeStieltjesParameters a u k := by
  classical
  unfold activeStieltjesParameters
  split_ifs
  · exact hu k
  · exact le_rfl

/-- The parameter equations remain valid throughout the active prefix after
both parameter tails are removed. -/
theorem shiftedStieltjesNumerators_active {a u v : ℕ → ℝ} {c : ℝ}
    (hp : ∀ n, (∀ i < n, a i ≠ 0) → a n = shiftedStieltjesNumerators c u v n) :
    ∀ n, (∀ i < n, a i ≠ 0) → a n = shiftedStieltjesNumerators c
      (activeStieltjesParameters a u) (activeStieltjesParameters a v) n := by
  classical
  intro n hn
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
  · subst n
    simpa only [shiftedStieltjesNumerators_even, activeStieltjesParameters,
      ite_eq_left hn] using hp (2 * k) hn
  · subst n
    have hprev : ∀ i < 2 * k, a i ≠ 0 := fun i hi => hn i (by lia)
    rw [shiftedStieltjesNumerators_odd]
    simp only [activeStieltjesParameters, ite_eq_left hprev]
    by_cases hz : a (2 * k + 1) = 0
    · have hnext : ¬ ∀ i < 2 * (k + 1), a i ≠ 0 := by
        intro h
        exact h (2 * k + 1) (by lia) hz
      simp only [ite_eq_right hnext, mul_zero, zero_div, hz]
    · have hnext : ∀ i < 2 * (k + 1), a i ≠ 0 := by
        intro i hi
        by_cases hlt : i < 2 * k + 1
        · exact hn i hlt
        · have heq : i = 2 * k + 1 := by lia
          simpa only [heq] using hz
      simpa only [ite_eq_left hnext, shiftedStieltjesNumerators_odd] using hp (2 * k + 1) hn

/-- Positive shifts bound the truncated parameters by fixed finite coordinate intervals. -/
theorem activeStieltjesParameters_bounds {a u v : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (hu : ∀ k, 0 ≤ u k) (hv : ∀ k, 0 ≤ v k)
    (hp : ∀ n, (∀ i < n, a i ≠ 0) → a n = shiftedStieltjesNumerators c u v n)
    (k : ℕ) :
    activeStieltjesParameters a u k ∈ Set.Icc 0 (max 0 (a (2 * k) / c)) ∧
      activeStieltjesParameters a v k ∈ Set.Icc 0 (max 0 (a (2 * k))) := by
  classical
  have hu0 := hu k
  have hv0 := hv k
  by_cases hact : ∀ i < 2 * k, a i ≠ 0
  · have heq : a (2 * k) = c * (1 + u k) + v k := by
      simpa only [shiftedStieltjesNumerators_even] using hp (2 * k) hact
    have huB : u k ≤ a (2 * k) / c := (le_div_iff₀ hc).mpr (by nlinarith)
    have hvB : v k ≤ a (2 * k) := by nlinarith
    simp only [activeStieltjesParameters, ite_eq_left hact]
    exact ⟨⟨hu0, huB.trans (le_max_right _ _)⟩,
      ⟨hv0, hvB.trans (le_max_right _ _)⟩⟩
  · simp only [activeStieltjesParameters, ite_eq_right hact]
    exact ⟨⟨le_rfl, le_max_left _ _⟩, ⟨le_rfl, le_max_left _ _⟩⟩

/-- Every admissible initial parameter has representatives in a fixed compact
product of intervals, even when the numerator sequence terminates. -/
theorem exists_bounded_activeStieltjesParameters {a : ℕ → ℝ} {c r : ℝ} (hc : 0 < c)
    (hr : r ∈ admissibleStieltjesParameters c a) :
    ∃ u v : ℕ → ℝ, u 0 = r ∧
      (∀ k, u k ∈ Set.Icc 0 (max 0 (a (2 * k) / c))) ∧
      (∀ k, v k ∈ Set.Icc 0 (max 0 (a (2 * k)))) ∧
      ∀ n, (∀ i < n, a i ≠ 0) → a n = shiftedStieltjesNumerators c u v n := by
  obtain ⟨u, v, hu0, hu, hv, hp⟩ := hr
  exact ⟨activeStieltjesParameters a u, activeStieltjesParameters a v,
    by simpa only [activeStieltjesParameters_zero] using hu0,
    fun k => (activeStieltjesParameters_bounds hc hu hv hp k).1,
    fun k => (activeStieltjesParameters_bounds hc hu hv hp k).2,
    shiftedStieltjesNumerators_active hp⟩

end PowerSeries
