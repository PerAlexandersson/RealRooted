/-
# Succ-degree root slots

Root-slot intersections for succ-degree crossings.
-/
import RealRooted.AffineFamily
import RealRooted.CommonInterleaver.AffineBoundary
import RealRooted.CommonInterleaver.IntervalLemmas
import RealRooted.AllCombo
import RealRooted.CommonInterleaverSeq
import RealRooted.DegreeDropDivXPrec
import RealRooted.DegreeDropReversal
import RealRooted.PFPolynomial
import RealRooted.PosCombo
import RealRooted.RootContinuity
import RealRooted.SuccDegreeLeftEndpoint

open Polynomial

noncomputable section

namespace RealRooted

/-- **Combinatorial core of the succ-degree slot bound.**

For descending real lists `rf` (length `n`) and `rg` (length `n + 1`), if the
roots weave - `hc1`: for `1 ≤ j ≤ n`, `rg`'s `j`-th element is `≤` `rf`'s
`(j-1)`-th; `hc2`: for `1 ≤ j < n`, `rf`'s `j`-th is `≤` `rg`'s `(j-1)`-th -
then for every common slot `j ≤ n` the descending slot intervals of `rf` and
`rg` intersect. This turns the analytic converse-Obreschkoff content into two
clean root inequalities. (`List.getD _ _ 0` avoids in-bounds side goals.) -/
theorem rootSlotInterval_inter_nonempty_of_crossing
    (rf rg : List ℝ)
    (hrf : rf.Pairwise (· ≥ ·)) (hrg : rg.Pairwise (· ≥ ·))
    (hlen : rg.length = rf.length + 1)
    (hc1 : ∀ j, 1 ≤ j → j ≤ rf.length → rg.getD j 0 ≤ rf.getD (j - 1) 0)
    (hc2 : ∀ j, 1 ≤ j → j < rf.length → rf.getD j 0 ≤ rg.getD (j - 1) 0)
    (j : ℕ) (hjf : j < rf.length + 1) (hjg : j < rg.length + 1) :
    (rootSlotInterval rf ⟨j, hjf⟩ ∩ rootSlotInterval rg ⟨j, hjg⟩).Nonempty := by
  have hgetD : ∀ {rs : List ℝ} {i : ℕ} (hi : i < rs.length), rs.getD i 0 = rs[i] :=
    fun hi => by simp [hi]
  have hstep : ∀ {rs : List ℝ}, rs.Pairwise (· ≥ ·) → ∀ {i : ℕ} (hi : i + 1 < rs.length),
      rs[i + 1] ≤ rs[i] := fun hrs i hi => by
    simpa using get_le_get_of_pairwise_ge hrs
      (i := ⟨i, by lia⟩) (j := ⟨i + 1, hi⟩) (by simp [Fin.le_def])
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · rcases rg with _ | ⟨s, rg⟩
    · simp at hlen
    rcases rf with _ | ⟨r, rf⟩
    · exact ⟨s, by simp [rootSlotInterval]⟩
    · exact ⟨max r s, by simp [rootSlotInterval]⟩
  have hjg' : j ≠ rg.length := by lia
  by_cases hjn : j = rf.length
  · obtain ⟨l, r, rfl⟩ :=
      (List.eq_nil_or_concat' rf).resolve_left (by rintro rfl; simp at hjn; lia)
    simp only [List.length_append, List.length_singleton] at hjn hlen hjf
    subst hjn
    have hc := hc1 (l.length + 1) (by lia) (by simp)
    rw [hgetD (by lia), hgetD (by simp)] at hc
    refine ⟨rg[l.length + 1], ?_, ?_⟩
    · simpa [rootSlotInterval] using hc
    · simpa [rootSlotInterval, hj0.ne', hjg'] using hstep hrg (i := l.length) (by lia)
  · have hc₁ := hc1 j hj0 (by lia)
    have hc₂ := hc2 j hj0 (by lia)
    rw [hgetD (by lia), hgetD (by lia)] at hc₁ hc₂
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by lia⟩
    simpa [rootSlotInterval, hjn, hjg'] using
      icc_inter_icc_nonempty_of_crossing (hstep hrf (by lia)) (hstep hrg (by lia)) hc₂ hc₁

end RealRooted
