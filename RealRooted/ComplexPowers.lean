import Mathlib

/-!
# Recurrence of powers on the complex unit circle

This file proves a compactness consequence for powers of a nonreal unit
complex number. Some positive power has real part strictly larger than the
real part of the original number.
-/

open Filter Metric Set

namespace Complex

/-- A nonreal point on the unit circle has a positive power with strictly
larger real part. -/
theorem exists_pos_pow_re_gt_of_norm_eq_one {w : ℂ}
    (hw : ‖w‖ = 1) (him : w.im ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ w.re < (w ^ m).re := by
  have hmem : ∀ n : ℕ, w ^ n ∈ closedBall 0 1 := by
    intro n
    simp [mem_closedBall, dist_eq_norm, norm_pow, hw]
  obtain ⟨l, hlmem, φ, hφ, hlim⟩ :=
    (isCompact_closedBall (0 : ℂ) 1).tendsto_subseq hmem
  have hlim' : Tendsto (fun n ↦ w ^ φ n) atTop (nhds l) := by
    simpa [Function.comp_def] using hlim
  have hlnorm : ‖l‖ = 1 := by
    have hnormlim : Tendsto (fun n ↦ ‖w ^ φ n‖) atTop (nhds ‖l‖) :=
      hlim'.norm
    have hconst : (fun n ↦ ‖w ^ φ n‖) = fun _ : ℕ ↦ (1 : ℝ) := by
      funext n
      simp [norm_pow, hw]
    rw [hconst] at hnormlim
    exact tendsto_nhds_unique hnormlim tendsto_const_nhds
  have hlne : l ≠ 0 := norm_ne_zero_iff.mp (by simp [hlnorm])
  let d : ℕ → ℕ := fun n ↦ φ (n + 1) - φ n
  have hdpos : ∀ n, 0 < d n := by
    intro n
    exact Nat.sub_pos_of_lt (hφ (Nat.lt_succ_self n))
  have hpoweq : ∀ n, w ^ d n = w ^ φ (n + 1) / w ^ φ n := by
    intro n
    apply (eq_div_iff (pow_ne_zero _ (norm_ne_zero_iff.mp (by simp [hw])))).2
    rw [← pow_add]
    congr 1
    exact Nat.sub_add_cancel (Nat.le_of_lt (hφ (Nat.lt_succ_self n)))
  have hnum : Tendsto (fun n ↦ w ^ φ (n + 1)) atTop (nhds l) := by
    simpa only [Function.comp_def] using hlim'.comp (tendsto_add_atTop_nat 1)
  have hpowlim : Tendsto (fun n ↦ w ^ d n) atTop (nhds 1) := by
    have hdiv := hnum.div hlim' hlne
    have hdiv' : Tendsto (fun n ↦ w ^ φ (n + 1) / w ^ φ n) atTop (nhds 1) := by
      rw [div_self hlne] at hdiv
      change Tendsto (fun n ↦ w ^ φ (n + 1) / w ^ φ n) atTop (nhds 1) at hdiv
      exact hdiv
    exact hdiv'.congr' (Eventually.of_forall fun n ↦ (hpoweq n).symm)
  have hwre : w.re < 1 := by
    calc
      w.re ≤ |w.re| := le_abs_self _
      _ < ‖w‖ := Complex.abs_re_lt_norm.mpr him
      _ = 1 := hw
  have hrelim : Tendsto (fun n ↦ (w ^ d n).re) atTop (nhds 1) :=
    Complex.continuous_re.continuousAt.tendsto.comp hpowlim
  obtain ⟨n, hn⟩ := ((tendsto_order.1 hrelim).1 w.re hwre).exists
  exact ⟨d n, hdpos n, hn⟩

end Complex
