module

public import RealRooted.EffectiveBKW.PathCube.Basic
import RealRooted.EffectiveBKW.Exterior
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Closing the path-cube root count by the exterior sign

A positive-index row has degree equal to the number of phase samples. Its
monicity supplies the additional leftmost root once those samples are known.
The construction of the samples remains an independent instance obligation.
-/

public section

namespace RealRooted.EffectiveBKW.PathCube

/-- Decreasing samples with alternating signs give the full root conclusion,
using the monic far-left sign for the additional root. -/
theorem row_splits_nodup_of_alternating {r : ℕ} (s : Fin (r + 1) → ℝ)
    (hs : StrictAnti s)
    (hsign : ∀ j, 0 < (-1 : ℝ) ^ (j.val : ℤ) * (row (r + 1)).eval (s j)) :
    (row (r + 1)).natDegree = r + 1 ∧ (row (r + 1)).Splits ∧
      (row (r + 1)).roots.Nodup ∧ ∀ x ∈ (row (r + 1)).roots, x < 0 := by
  have hlast : 0 < (-1 : ℝ) ^ r * (row (r + 1)).eval (s (Fin.last r)) := by
    simpa using hsign (Fin.last r)
  have hleft : (-1 : ℝ) ^ (r + 1) * (row (r + 1)).eval (s (Fin.last r)) < 0 := by
    rw [pow_succ]
    nlinarith
  have hlc : 0 < (row (r + 1)).leadingCoeff := by
    rw [(row_monic (r + 1)).leadingCoeff]
    norm_num
  obtain ⟨hsp, hnd⟩ := splits_nodup_of_strictAnti_alternating_of_leftEscape
    (L := 0) (row_natDegree (r + 1)) hlc s hs (by simpa using hsign) hleft
  exact ⟨row_natDegree (r + 1), hsp, hnd, row_roots_neg (r + 1)⟩

end RealRooted.EffectiveBKW.PathCube
