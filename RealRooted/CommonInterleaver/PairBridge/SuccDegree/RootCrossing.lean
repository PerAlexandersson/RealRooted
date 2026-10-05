import RealRooted.CommonInterleaver.PairBridge.SuccDegree.RootCount

/-!
# Pair bridge succ-degree root crossing

Conversion from ascending list interlacing to the descending root-crossing endpoint.
-/

open Polynomial

noncomputable section

namespace RealRooted

private lemma succCross_getD_mono
    {rs : List ℝ} (hrs : rs.Pairwise (· ≤ ·))
    {i j : ℕ} (hij : i ≤ j) (hj : j < rs.length) :
    rs.getD i 0 ≤ rs.getD j 0 := by
  have hi : i < rs.length := by lia
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj]
  simp only [Option.getD_some]
  rcases lt_or_eq_of_le hij with hij' | rfl
  · exact List.pairwise_iff_get.mp hrs ⟨i, hi⟩ ⟨j, hj⟩ hij'
  · simp

/-- Differ-by-one weak interlacing of ascending root lists gives the two
descending-root crossing inequalities in the succ-degree shape consumed by
`rootSlotInterval_inter_nonempty_of_crossing`. -/
theorem rootCrossing_of_listInterlaces {ss rs : List ℝ}
    (hrs_pw : rs.Pairwise (· ≤ ·))
    (hlen : ss.length + 1 = rs.length)
    (hint : ListInterlaces ss rs) :
    (∀ j, 1 ≤ j → j ≤ ss.length →
        rs.reverse.getD j 0 ≤ ss.reverse.getD (j - 1) 0) ∧
    (∀ j, 1 ≤ j → j < ss.length →
        ss.reverse.getD j 0 ≤ rs.reverse.getD (j - 1) 0) := by
  obtain ⟨hA, hB⟩ := listInterlaces_getD_bounds ss rs hint hlen
  refine ⟨?_, ?_⟩
  · intro j hj1 hj2
    have hjr : j < rs.length := by lia
    have hjs : j - 1 < ss.length := by lia
    rw [getD_reverse_eq rs j hjr, getD_reverse_eq ss (j - 1) hjs]
    have e1 : rs.length - 1 - j = ss.length - j := by lia
    have e2 : ss.length - 1 - (j - 1) = ss.length - j := by lia
    rw [e1, e2]
    exact hA (ss.length - j) (by lia)
  · intro j hj1 hj2
    have hjs : j < ss.length := by lia
    have hjr : j - 1 < rs.length := by lia
    rw [getD_reverse_eq ss j hjs, getD_reverse_eq rs (j - 1) hjr]
    set i := ss.length - 1 - j with hi
    have e2 : rs.length - 1 - (j - 1) = i + 2 := by lia
    rw [e2]
    have hstep := hB i (by lia)
    have hmono : rs.getD (i + 1) 0 ≤ rs.getD (i + 2) 0 :=
      succCross_getD_mono hrs_pw (by lia) (by lia)
    exact le_trans hstep hmono

end RealRooted
