import RealRooted.Compatibility.NDCutStateClosure
import RealRooted.Compatibility.NDCutThresholdClosure

/-!
# Preservation of the structural N/D cut invariant

This module combines the two independent successor closures: ordered P/Q
compatibility controls the next N/D state order, while the old N/D state order
controls the next P/Q cut package through the marker-one threshold matrix.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The successor non-descent state is the inclusive prefix of the unmarked
pair mix. -/
def ndCutNextN {m : ℕ} (N D : Fin m → ℝ[X]) (j : Fin m) : ℝ[X] :=
  cutPrefix (ndCutP N D) j

/-- The successor descent state is the strict suffix of the marked pair mix. -/
def ndCutNextD {m : ℕ} (N D : Fin m → ℝ[X]) (j : Fin m) : ℝ[X] :=
  cutStrictSuffix (ndCutQ N D) j

/-- The successor unmarked pair mix is exactly the generic unmarked cut
output. -/
theorem ndCutP_next {m : ℕ} (N D : Fin m → ℝ[X]) :
    ndCutP (ndCutNextN N D) (ndCutNextD N D) =
      cutTransformP (ndCutP N D) (ndCutQ N D) := by
  rfl

/-- The successor marked pair mix is exactly the generic marked cut output. -/
theorem ndCutQ_next {m : ℕ} (N D : Fin m → ℝ[X]) :
    ndCutQ (ndCutNextN N D) (ndCutNextD N D) =
      cutTransformQ (ndCutP N D) (ndCutQ N D) := by
  rfl

/-- One structural cut step preserves the complete ordered N/D invariant. -/
theorem OrderedNDCutCompatible.next {m : ℕ} {N D : Fin m → ℝ[X]}
    (h : OrderedNDCutCompatible N D) :
    OrderedNDCutCompatible (ndCutNextN N D) (ndCutNextD N D) := by
  refine ⟨?_, ?_⟩
  · rw [ndCutP_next, ndCutQ_next]
    exact h.cutOutputs_orderedCutCompatible
  · exact h.cutCompatible.ndCutStateInterlacing

end RealRooted
