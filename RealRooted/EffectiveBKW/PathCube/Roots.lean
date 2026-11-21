module

public import RealRooted.EffectiveBKW.PathCube.Basic
import RealRooted.EffectiveBKW.PathCube.BranchFacts
import RealRooted.EffectiveBKW.PathCube.PointwiseSigns
import RealRooted.EffectiveBKW.PathCube.PhaseConclusion

/-!
# The path-cube row theorem
-/

public section

namespace RealRooted.EffectiveBKW.PathCube

/-- Every path-cube transfer row has its expected degree and distinct negative real roots. -/
theorem row_splits_nodup (r : ℕ) :
    (row r).natDegree = r ∧ (row r).Splits ∧ (row r).roots.Nodup ∧
      ∀ x ∈ (row r).roots, x < 0 := by
  exact row_splits_nodup_of_check branch_check
    (fun _ ht ↦ conditionG1_pos ht) (fun _ ht ↦ conditionG2_pos ht)
    (fun _ ht ↦ pointwisePlus_pos ht) (fun _ ht ↦ pointwiseMinus_pos ht)
    (fun _ ht ↦ conditionWIND_pos ht) r

end RealRooted.EffectiveBKW.PathCube
