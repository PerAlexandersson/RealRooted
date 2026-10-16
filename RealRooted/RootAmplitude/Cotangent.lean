module

public import RealRooted.RootAmplitude.Density
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Cotangent model for logarithmic root gaps

For the model spectrum `-pi cot t`, the change in reciprocal consecutive gaps
has a closed form.  Its uniform upper bound verifies the log-gap density
criterion for the exponential of any equally spaced sample of the spectrum.
-/

@[expose] public noncomputable section

namespace RealRooted.RootAmplitude

/-- The cotangent model spectrum in logarithmic coordinates. -/
def cotangentModel (t : ℝ) : ℝ :=
  -Real.pi * (Real.cos t / Real.sin t)

/-- A gap in the cotangent model, in product form. -/
theorem cotangentModel_sub_eq (t h : ℝ) (ht : Real.sin t ≠ 0)
    (hth : Real.sin (t + h) ≠ 0) :
    cotangentModel (t + h) - cotangentModel t =
      Real.pi * Real.sin h / (Real.sin t * Real.sin (t + h)) := by
  have hsin :
      Real.sin (t + h) * Real.cos t - Real.cos (t + h) * Real.sin t =
        Real.sin h := by
    rw [← Real.sin_sub]
    ring_nf
  unfold cotangentModel
  field_simp
  linear_combination hsin

/-- The difference of reciprocal consecutive cotangent-model gaps. -/
theorem inv_cotangentModel_gap_diff_eq (t h : ℝ)
    (ht : Real.sin t ≠ 0) (hth : Real.sin (t + h) ≠ 0)
    (ht2h : Real.sin (t + 2 * h) ≠ 0) (hh : Real.sin h ≠ 0) :
    1 / (cotangentModel (t + 2 * h) - cotangentModel (t + h)) -
        1 / (cotangentModel (t + h) - cotangentModel t) =
      Real.sin (2 * (t + h)) / Real.pi := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hgap₁ := cotangentModel_sub_eq t h ht hth
  have hgap₂ :
      cotangentModel (t + 2 * h) - cotangentModel (t + h) =
        Real.pi * Real.sin h /
          (Real.sin (t + h) * Real.sin (t + 2 * h)) := by
    simpa only [show t + h + h = t + 2 * h by ring] using
      cotangentModel_sub_eq (t + h) h hth
        (by rw [show t + h + h = t + 2 * h by ring]; exact ht2h)
  have hhalfSub : (t + 2 * h - t) / 2 = h := by ring
  have hhalfAdd : (t + 2 * h + t) / 2 = t + h := by ring
  have hsinSub :
      Real.sin (t + 2 * h) - Real.sin t =
        2 * Real.cos (t + h) * Real.sin h := by
    rw [Real.sin_sub_sin, hhalfSub, hhalfAdd]
    ring
  have hnum :
      Real.sin (t + h) * Real.sin (t + 2 * h) -
          Real.sin t * Real.sin (t + h) =
        Real.sin (t + h) * (2 * Real.cos (t + h) * Real.sin h) := by
    rw [← hsinSub]
    ring
  rw [hgap₁, hgap₂, one_div_div, one_div_div, Real.sin_two_mul,
    div_sub_div_same, hnum]
  field_simp

/-- Reciprocal consecutive cotangent-model gaps differ by at most `1 / 2`. -/
theorem inv_cotangentModel_gap_diff_le (t h : ℝ)
    (ht : Real.sin t ≠ 0) (hth : Real.sin (t + h) ≠ 0)
    (ht2h : Real.sin (t + 2 * h) ≠ 0) (hh : Real.sin h ≠ 0) :
    1 / (cotangentModel (t + 2 * h) - cotangentModel (t + h)) -
        1 / (cotangentModel (t + h) - cotangentModel t) ≤ 1 / 2 := by
  rw [inv_cotangentModel_gap_diff_eq t h ht hth ht2h hh]
  have hsin := Real.sin_le_one (2 * (t + h))
  have hpi := Real.pi_gt_three
  rw [div_le_div_iff₀ Real.pi_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- Equally spaced samples of the exponentiated cotangent model have
nondecreasing gaps. -/
theorem gap_exp_cotangentModel_le (θ : ℕ → ℝ) (h : ℝ)
    (hstep : ∀ j, θ (j + 1) = θ j + h) (k : ℕ)
    (hk : Real.sin (θ k) ≠ 0) (hk1 : Real.sin (θ (k + 1)) ≠ 0)
    (hk2 : Real.sin (θ (k + 2)) ≠ 0) (hh : Real.sin h ≠ 0)
    (hgap₀ : 0 < cotangentModel (θ (k + 1)) - cotangentModel (θ k))
    (hgap₁ : 0 < cotangentModel (θ (k + 2)) - cotangentModel (θ (k + 1))) :
    gap (fun j => Real.exp (cotangentModel (θ j))) k ≤
      gap (fun j => Real.exp (cotangentModel (θ j))) (k + 1) := by
  have hθ1 : θ (k + 1) = θ k + h := hstep k
  have hθ2 : θ (k + 2) = θ k + 2 * h := by
    rw [show k + 2 = (k + 1) + 1 from rfl, hstep (k + 1), hθ1]
    ring
  have hpos : ∀ i, 0 < Real.exp (cotangentModel (θ i)) :=
    fun i => Real.exp_pos _
  have hlog : ∀ i : ℕ,
      Real.log
          (Real.exp (cotangentModel (θ (i + 1))) /
            Real.exp (cotangentModel (θ i))) =
        cotangentModel (θ (i + 1)) - cotangentModel (θ i) := by
    intro i
    rw [← Real.exp_sub, Real.log_exp]
  refine gap_le_gap_of_inv_criterion
    (fun j => Real.exp (cotangentModel (θ j))) hpos k ?_ ?_ ?_
  · rw [hlog k]
    exact hgap₀
  · rw [hlog (k + 1)]
    exact hgap₁
  · rw [hlog k, hlog (k + 1), hθ1, hθ2]
    have hbound := inv_cotangentModel_gap_diff_le (θ k) h hk
      (by simpa only [hθ1] using hk1) (by simpa only [hθ2] using hk2) hh
    linarith

end RealRooted.RootAmplitude
