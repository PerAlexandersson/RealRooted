import RealRooted.CommonInterleaver.RootSelection

/-!
# Finite interlacing-family trees

This file packages the finite rooted-tree form of MSS root selection. Leaves
are polynomial labels; every internal node is the sum of a nonempty list of
children whose node polynomials have a common degree-gap left interlacer.
-/

open Polynomial

noncomputable section

namespace RealRooted

open LiuOppositeSigns

/-- A finite rose tree with polynomial-labelled leaves. -/
inductive RootSelectionTree where
  | leaf (p : ℝ[X])
  | node (children : List RootSelectionTree)

namespace RootSelectionTree

/-- The polynomial at a node: a leaf label, or the sum of its child
polynomials. -/
def polynomial : RootSelectionTree → ℝ[X]
  | leaf p => p
  | node children => (children.map polynomial).sum

/-- The leaf labels below a node, in depth-first left-to-right order. -/
def leaves : RootSelectionTree → List ℝ[X]
  | leaf p => [p]
  | node children => (children.map leaves).flatten

/-- Validity data for a degree-`d` interlacing-family tree. Leaf splitting is
explicit, and an internal node must have at least one child. -/
inductive Valid (d : ℕ) : RootSelectionTree → Prop
  | leaf {p : ℝ[X]}
      (hdeg : p.natDegree = d) (hsplits : p.Splits)
      (hpos : HasPosLeadingCoeff p) :
      Valid d (.leaf p)
  | node {children : List RootSelectionTree}
      (hne : children ≠ [])
      (hchildren : ∀ child ∈ children, Valid d child)
      (hcommon : HasCommonLeftInterlacerOfDegree
        (children.map polynomial) d) :
      Valid d (.node children)

/-- Every node polynomial in a valid tree has the common degree, positive
leading coefficient, and splitness. -/
theorem Valid.polynomial_data {d : ℕ} {t : RootSelectionTree}
    (ht : Valid d t) :
    t.polynomial.natDegree = d ∧
      HasPosLeadingCoeff t.polynomial ∧ t.polynomial.Splits := by
  induction ht with
  | leaf hdeg hsplits hpos => simpa [polynomial] using And.intro hdeg ⟨hpos, hsplits⟩
  | @node children hne hchildren hcommon ih =>
      have hdeg : ∀ p ∈ children.map polynomial, p.natDegree = d := by
        intro p hp
        rcases List.mem_map.mp hp with ⟨child, hchild, rfl⟩
        exact (ih child hchild).1
      have hpos : ∀ p ∈ children.map polynomial, HasPosLeadingCoeff p := by
        intro p hp
        rcases List.mem_map.mp hp with ⟨child, hchild, rfl⟩
        exact (ih child hchild).2.1
      have hchildren_ne : children.map polynomial ≠ [] := by simpa using hne
      have hw_nonneg :
          ∀ ap ∈ (children.map polynomial).map (fun p => ((1 : ℝ), p)),
            0 ≤ ap.1 := by simp
      have hw_deg :
          ∀ ap ∈ (children.map polynomial).map (fun p => ((1 : ℝ), p)),
            ap.2.natDegree = d := by
        intro ap hap
        rcases List.mem_map.mp hap with ⟨p, hp, rfl⟩
        exact hdeg p hp
      have hw_pos :
          ∀ ap ∈ (children.map polynomial).map (fun p => ((1 : ℝ), p)),
            HasPosLeadingCoeff ap.2 := by
        intro ap hap
        rcases List.mem_map.mp hap with ⟨p, hp, rfl⟩
        exact hpos p hp
      have hw_exists :
          ∃ ap ∈ (children.map polynomial).map (fun p => ((1 : ℝ), p)),
            0 < ap.1 := by
        rcases List.exists_mem_of_ne_nil (children.map polynomial) hchildren_ne with
          ⟨p, hp⟩
        exact ⟨(1, p), List.mem_map.mpr ⟨p, hp, rfl⟩, by norm_num⟩
      have hsum_pos : HasPosLeadingCoeff (children.map polynomial).sum := by
        rw [← weightedSum_map_one]
        exact hasPosLeadingCoeff_weightedSum _ hw_nonneg hw_pos hw_exists
      have hsum_deg : (children.map polynomial).sum.natDegree = d := by
        rw [← weightedSum_map_one]
        exact natDegree_weightedSum_eq_of_nonneg_of_sameDegree
          hw_nonneg hw_deg hw_pos hw_exists
      rcases hcommon with ⟨h, hh_deg, hhprec⟩
      have hprec : Prec h (children.map polynomial).sum :=
        prec_sum_left_of_common_left_signed
          (children.map polynomial) h hhprec hpos hchildren_ne
      exact ⟨by simpa [polynomial] using hsum_deg,
        by simpa [polynomial] using hsum_pos,
        by simpa [polynomial] using hprec.2.1.2⟩

/-- MSS finite-tree selection: some leaf has largest root at most the largest
root of the polynomial at the root node. -/
theorem Valid.exists_leaf_largestRoot_le {d : ℕ} {t : RootSelectionTree}
    (ht : Valid d t) (hd_pos : 0 < d) :
    ∃ p ∈ t.leaves, ∃ rp rt,
      IsLargestRoot p rp ∧ IsLargestRoot t.polynomial rt ∧ rp ≤ rt := by
  induction ht with
  | leaf hdeg hsplits hpos =>
      obtain ⟨r, hr⟩ :=
        LiuOppositeSigns.exists_isLargestRoot hpos.ne_zero hsplits (by lia)
      exact ⟨_, by simp [leaves], r, r, hr, by simpa [polynomial] using hr, le_rfl⟩
  | @node children hne hchildren hcommon ih =>
      have hdeg : ∀ p ∈ children.map polynomial, p.natDegree = d := by
        intro p hp
        rcases List.mem_map.mp hp with ⟨child, hchild, rfl⟩
        exact (hchildren child hchild).polynomial_data.1
      have hpos : ∀ p ∈ children.map polynomial, HasPosLeadingCoeff p := by
        intro p hp
        rcases List.mem_map.mp hp with ⟨child, hchild, rfl⟩
        exact (hchildren child hchild).polynomial_data.2.1
      have hchildren_ne : children.map polynomial ≠ [] := by simpa using hne
      obtain ⟨q, hq, rq, rt, hrq, hrt, hrq_le⟩ :=
        exists_mem_largestRoot_le_sum hcommon hdeg hpos hchildren_ne
      rcases List.mem_map.mp hq with ⟨child, hchild, rfl⟩
      obtain ⟨p, hp, rp, rq', hrp, hrq', hrp_le⟩ := ih child hchild
      have hchild_ne : child.polynomial ≠ 0 :=
        (hchildren child hchild).polynomial_data.2.1.ne_zero
      have hrq_eq : rq' = rq := hrq'.unique hchild_ne hrq
      exact ⟨p, by
          simp only [leaves, List.mem_flatten, List.mem_map]
          exact ⟨child.leaves, ⟨child, hchild, rfl⟩, hp⟩,
        rp, rt, hrp, by simpa [polynomial] using hrt,
        hrp_le.trans (hrq_eq.le.trans hrq_le)⟩

end RootSelectionTree

end RealRooted
