/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.AdmissibleParameters
import RealRooted.Mathlib.RingTheory.PowerSeries.StieltjesFraction.BoundedParameters

/-!
# Compactness of the admissible initial parameters

Cross-multiplying the active odd equations gives polynomial closed constraints.
Bounded representatives place all parameters in a compact product of intervals.
Projection to the initial coordinate then proves compactness, including the
terminating case of the corrected Sokal-Walrad Remark 2 criterion.
-/

public section

namespace PowerSeries

/-- Even and odd parameter sequences. -/
private abbrev ParameterPair := (ℕ → ℝ) × (ℕ → ℝ)

/-- The active numerator equations with denominators cleared. -/
private def parameterEquations (c : ℝ) (a : ℕ → ℝ) : Set ParameterPair :=
  {p | ∀ k,
    ((∀ i < 2 * k, a i ≠ 0) → a (2 * k) = c * (1 + p.1 k) + p.2 k) ∧
    ((∀ i < 2 * k + 1, a i ≠ 0) →
      a (2 * k + 1) * (1 + p.1 k) = p.2 k * p.1 (k + 1))}

/-- Each active equation is a closed polynomial constraint. -/
private theorem isClosed_parameterEquations (c : ℝ) (a : ℕ → ℝ) :
    IsClosed (parameterEquations c a) := by
  have heq : parameterEquations c a = ⋂ k : ℕ, {p : ParameterPair |
      ((∀ i < 2 * k, a i ≠ 0) → a (2 * k) = c * (1 + p.1 k) + p.2 k) ∧
      ((∀ i < 2 * k + 1, a i ≠ 0) →
        a (2 * k + 1) * (1 + p.1 k) = p.2 k * p.1 (k + 1))} := by
    ext p
    simp only [parameterEquations, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [heq]
  refine isClosed_iInter fun k => ?_
  exact (isClosed_imp isOpen_const (isClosed_eq (by fun_prop) (by fun_prop))).and
    (isClosed_imp isOpen_const (isClosed_eq (by fun_prop) (by fun_prop)))

/-- Nonnegative even parameters make clearing the denominators reversible. -/
private theorem mem_parameterEquations_iff {c : ℝ} {a u v : ℕ → ℝ}
    (hu : ∀ k, 0 ≤ u k) :
    (u, v) ∈ parameterEquations c a ↔
      ∀ n, (∀ i < n, a i ≠ 0) → a n = shiftedStieltjesNumerators c u v n := by
  have hden (k : ℕ) : 1 + u k ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one (hu k))
  constructor
  · intro hp n hn
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
    · subst n
      simpa only [shiftedStieltjesNumerators_even] using (hp k).1 hn
    · subst n
      rw [shiftedStieltjesNumerators_odd]
      exact (eq_div_iff (hden k)).mpr ((hp k).2 hn)
  · intro hp k
    constructor
    · intro hk
      simpa only [shiftedStieltjesNumerators_even] using hp (2 * k) hk
    · intro hk
      apply (eq_div_iff (hden k)).mp
      simpa only [shiftedStieltjesNumerators_odd] using hp (2 * k + 1) hk

/-- For a positive shift, the corrected active-prefix admissible set is compact.
No assumption of nontermination or existence of a representing measure is needed. -/
theorem isCompact_admissibleStieltjesParameters {c : ℝ} (hc : 0 < c) (a : ℕ → ℝ) :
    IsCompact (admissibleStieltjesParameters c a) := by
  let K : Set ParameterPair :=
    {u : ℕ → ℝ | ∀ k, u k ∈ Set.Icc 0 (max 0 (a (2 * k) / c))} ×ˢ
      {v : ℕ → ℝ | ∀ k, v k ∈ Set.Icc 0 (max 0 (a (2 * k)))}
  have hK : IsCompact K :=
    (isCompact_pi_infinite fun _ => isCompact_Icc).prod
      (isCompact_pi_infinite fun _ => isCompact_Icc)
  have heq : admissibleStieltjesParameters c a =
      (fun p : ParameterPair => p.1 0) '' (K ∩ parameterEquations c a) := by
    ext r
    constructor
    · intro hr
      obtain ⟨u, v, hu0, hu, hv, hp⟩ := exists_bounded_activeStieltjesParameters hc hr
      refine ⟨(u, v), ⟨⟨hu, hv⟩, ?_⟩, hu0⟩
      exact (mem_parameterEquations_iff (fun k => (hu k).1)).mpr hp
    · rintro ⟨⟨u, v⟩, ⟨⟨hu, hv⟩, hp⟩, hu0⟩
      exact ⟨u, v, hu0, fun k => (hu k).1, fun k => (hv k).1,
        (mem_parameterEquations_iff (fun k => (hu k).1)).mp hp⟩
  rw [heq]
  exact (hK.inter_right (isClosed_parameterEquations c a)).image (by fun_prop)

/-- A nonempty admissible set is a closed interval with an attained maximum. -/
theorem admissibleStieltjesParameters_eq_Icc {c : ℝ} (hc : 0 < c) {a : ℕ → ℝ}
    (hne : (admissibleStieltjesParameters c a).Nonempty) :
    ∃ M : ℝ, 0 ≤ M ∧ M ≤ a 0 / c - 1 ∧
      admissibleStieltjesParameters c a = Set.Icc 0 M := by
  obtain ⟨M, hM⟩ := (isCompact_admissibleStieltjesParameters hc a).exists_isGreatest hne
  refine ⟨M, nonneg_of_mem_admissibleStieltjesParameters hM.1,
    mem_admissibleStieltjesParameters_le hc hM.1, ?_⟩
  ext r
  constructor
  · intro hr
    exact ⟨nonneg_of_mem_admissibleStieltjesParameters hr, hM.2 hr⟩
  · intro hr
    exact mem_admissibleStieltjesParameters_of_le hc.le hM.1 hr.1 hr.2

/-- A normalized lower-support moment sequence has a nonempty closed interval
of admissible initial parameters, with all inactive tails treated existentially. -/
theorem exists_Icc_admissibleStieltjesParameters {c : ℝ} (hc : 0 < c)
    {a : ℕ → ℝ}
    (hmom : ∃ mu : MeasureTheory.Measure ℝ, (∀ᵐ x ∂mu, c ≤ x) ∧
      ∀ n : ℕ, MeasureTheory.Integrable (fun x : ℝ => x ^ n) mu ∧
        (∫ x : ℝ, x ^ n ∂mu) = coeff n (stieltjesTail a 0)) :
    ∃ M : ℝ, 0 ≤ M ∧ M ≤ a 0 / c - 1 ∧
      admissibleStieltjesParameters c a = Set.Icc 0 M :=
  admissibleStieltjesParameters_eq_Icc hc
    ⟨0, zero_mem_admissibleStieltjesParameters hc.le hmom⟩

end PowerSeries
