import RealRooted.Compatibility.NDCutPreservation
import RealRooted.ParkingFunctions.Descents.WeakLeftPeakOrderedCut

/-!
# Structural N/D preservation for the weak-left-peak recurrence

The checked terminal-state recurrence is exactly one generic structural cut
step, so the generic preservation theorem supplies an induction-ready witness.
-/

namespace RealRooted.ParkingFunctions

noncomputable section

/-- The next terminal non-descent family is the generic successor N family. -/
theorem terminalNonDescentReal_succ_eq_ndCutNextN (m r : ℕ) :
    terminalNonDescentReal m (r + 1) =
      ndCutNextN (terminalNonDescentReal m r) (terminalDescentReal m r) := by
  funext j
  exact terminalNonDescentReal_succ m r j

/-- The next terminal descent family is the generic successor D family. -/
theorem terminalDescentReal_succ_eq_ndCutNextD (m r : ℕ) :
    terminalDescentReal m (r + 1) =
      ndCutNextD (terminalNonDescentReal m r) (terminalDescentReal m r) := by
  funext j
  exact terminalDescentReal_succ m r j

/-- One checked weak-left-peak terminal-state step preserves the complete
structural invariant. This is the direct induction step for the application. -/
theorem terminalND_orderedNDCutCompatible_succ (m r : ℕ)
    (h : OrderedNDCutCompatible (terminalNonDescentReal m r)
      (terminalDescentReal m r)) :
    OrderedNDCutCompatible (terminalNonDescentReal m (r + 1))
      (terminalDescentReal m (r + 1)) := by
  rw [terminalNonDescentReal_succ_eq_ndCutNextN,
    terminalDescentReal_succ_eq_ndCutNextD]
  exact h.next

end

end RealRooted.ParkingFunctions
