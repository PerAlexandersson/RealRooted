import RealRooted.Compatibility.CutTransform
import RealRooted.Compatibility.LeanderTransform
import RealRooted.ParkingFunctions.Descents.WeakLeftPeakFactorization

/-!
# The P/Q cut transform for weak left peaks

The two terminal states of the weak-left-peak recurrence become the generic
`P/Q` cut transform after forming `P = N + D` and `Q = X * N + D`.  The final
example distinguishes this transform from Leander's diagonal-omitting
transform already for a two-letter alphabet.
-/

open Polynomial

namespace RealRooted.ParkingFunctions

noncomputable section

/-- The next unmarked pair mix is exactly the unmarked `P/Q` cut output. -/
theorem terminalPairMixReal_succ_eq_cutTransformP
    (m r : ℕ) (j : Fin m) :
    terminalPairMixReal m (r + 1) j =
      cutTransformP (terminalPairMixReal m r)
        (terminalXPairMixReal m r) j := by
  rw [terminalPairMixReal_eq, terminalNonDescentReal_succ,
    terminalDescentReal_succ]
  rfl

/-- The next marked pair mix is exactly the marked `P/Q` cut output. -/
theorem terminalXPairMixReal_succ_eq_cutTransformQ
    (m r : ℕ) (j : Fin m) :
    terminalXPairMixReal m (r + 1) j =
      cutTransformQ (terminalPairMixReal m r)
        (terminalXPairMixReal m r) j := by
  rw [terminalXPairMixReal_eq, terminalNonDescentReal_succ,
    terminalDescentReal_succ]
  rfl

/-- The two-letter base pair family is `[2, 2]`. -/
theorem terminalPairMixReal_two_zero :
    terminalPairMixReal 2 0 = ![C 2, C 2] := by
  have hlt : ({x : Fin 2 | (0 : Fin 2) < x} : Finset (Fin 2)).card = 1 := by
    decide
  have hle : ({x : Fin 2 | x ≤ (1 : Fin 2)} : Finset (Fin 2)).card = 2 := by
    decide
  funext j
  fin_cases j
  · norm_num [terminalPairMixReal, terminalNonDescentReal,
      terminalDescentReal,
      literalWordWeakLeftPeakTerminalNonDescentRefined_zero,
      literalWordWeakLeftPeakTerminalDescentRefined_zero,
      Fin.sum_univ_two, hlt, hle]
    simp only [Polynomial.C_ofNat]
  · norm_num [terminalPairMixReal, terminalNonDescentReal,
      terminalDescentReal,
      literalWordWeakLeftPeakTerminalNonDescentRefined_zero,
      literalWordWeakLeftPeakTerminalDescentRefined_zero,
      Fin.sum_univ_two, hlt, hle]
    simp only [Polynomial.C_ofNat]

/-- The two-letter base marked pair family is `[X + 1, 2X]`. -/
theorem terminalXPairMixReal_two_zero :
    terminalXPairMixReal 2 0 = ![X + 1, C 2 * X] := by
  have hlt : ({x : Fin 2 | (0 : Fin 2) < x} : Finset (Fin 2)).card = 1 := by
    decide
  have hle : ({x : Fin 2 | x ≤ (1 : Fin 2)} : Finset (Fin 2)).card = 2 := by
    decide
  funext j
  fin_cases j
  · norm_num [terminalXPairMixReal, terminalNonDescentReal,
      terminalDescentReal,
      literalWordWeakLeftPeakTerminalNonDescentRefined_zero,
      literalWordWeakLeftPeakTerminalDescentRefined_zero,
      Fin.sum_univ_two, hlt, hle]
  · norm_num [terminalXPairMixReal, terminalNonDescentReal,
      terminalDescentReal,
      literalWordWeakLeftPeakTerminalNonDescentRefined_zero,
      literalWordWeakLeftPeakTerminalDescentRefined_zero,
      Fin.sum_univ_two, hlt, hle]
    simp only [Polynomial.C_ofNat]
    ring

/-- At the first two-letter cut, the next `P` output is `2 + 2X`. -/
theorem cutTransformP_two_base_zero :
    cutTransformP (terminalPairMixReal 2 0)
        (terminalXPairMixReal 2 0) 0 = C 2 + C 2 * X := by
  rw [terminalPairMixReal_two_zero, terminalXPairMixReal_two_zero]
  simp [cutTransformP, cutPrefix, cutStrictSuffix, Fin.sum_univ_two]

/-- The complete unmarked two-letter family after one cut update. -/
theorem terminalPairMixReal_two_one :
    terminalPairMixReal 2 1 = ![C 2 + C 2 * X, C 4] := by
  funext j
  fin_cases j
  · rw [terminalPairMixReal_succ_eq_cutTransformP,
      terminalPairMixReal_two_zero, terminalXPairMixReal_two_zero]
    simp [cutTransformP, cutPrefix, cutStrictSuffix, Fin.sum_univ_two]
  · rw [terminalPairMixReal_succ_eq_cutTransformP,
      terminalPairMixReal_two_zero, terminalXPairMixReal_two_zero]
    simp [cutTransformP, cutPrefix, cutStrictSuffix, Fin.sum_univ_two]
    simp only [Polynomial.C_ofNat]
    ring

/-- The complete marked two-letter family after one cut update. -/
theorem terminalXPairMixReal_two_one :
    terminalXPairMixReal 2 1 = ![C 4 * X, C 4 * X] := by
  funext j
  fin_cases j
  · rw [terminalXPairMixReal_succ_eq_cutTransformQ,
      terminalPairMixReal_two_zero, terminalXPairMixReal_two_zero]
    simp [cutTransformQ, cutPrefix, cutStrictSuffix, Fin.sum_univ_two]
    simp only [Polynomial.C_ofNat]
    ring
  · rw [terminalXPairMixReal_succ_eq_cutTransformQ,
      terminalPairMixReal_two_zero, terminalXPairMixReal_two_zero]
    simp [cutTransformQ, cutPrefix, cutStrictSuffix, Fin.sum_univ_two]
    simp only [Polynomial.C_ofNat]
    ring

/-- In the reversed-`P`, then `Q`, convention, the first updated family is
`[4, 2 + 2X, 4X, 4X]`. -/
theorem terminalPQOrderReal_two_one :
    terminalPQOrderReal 2 1 =
      [C 4, C 2 + C 2 * X, C 4 * X, C 4 * X] := by
  rw [terminalPQOrderReal, terminalPairMixReal_two_one,
    terminalXPairMixReal_two_one]
  rfl

/-- The first Leander output on the same ordered base family is `3 + 3X`. -/
theorem leanderTransform_two_base_order_zero :
    leanderTransform
        (![C 2, C 2, X + 1, C 2 * X] : Fin 4 → ℝ[X]) 0 =
      C 3 + C 3 * X := by
  simp [leanderTransform, Fin.sum_univ_four]
  simp only [Polynomial.C_ofNat]
  ring

/-- The weak-left-peak cut update is not literally Leander's transform.
Already the first output differs for the two-letter base family. -/
theorem cutTransform_two_base_ne_leanderTransform :
    cutTransformP (terminalPairMixReal 2 0)
        (terminalXPairMixReal 2 0) 0 ≠
      leanderTransform
        (![C 2, C 2, X + 1, C 2 * X] : Fin 4 → ℝ[X]) 0 := by
  rw [cutTransformP_two_base_zero, leanderTransform_two_base_order_zero]
  intro h
  have := congrArg (fun p : ℝ[X] => p.coeff 0) h
  norm_num at this

end

end RealRooted.ParkingFunctions
