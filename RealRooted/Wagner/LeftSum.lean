import RealRooted.WagnerRightSum

/-!
# Wagner (2): Common-left addition theorems

If h ≪ f and h ≪ g with positive leading coefficients, then h ≪ (f + g).
Includes SumCompatibleLeft for recursive n-summand assembly.
-/

open Polynomial Filter

noncomputable section

namespace RealRooted

section

/-- Wagner (2): if `h` interlaces both `f` and `g`, and `f` and `g` have positive
leading coefficients, then `h` interlaces `f + g`.

Neither real-rootedness of `f + g` nor coprimeness of `f` and `g` is assumed.
The proof adjoins a root `r` to the right of all roots, applies Wagner (1) to
`f, g ≪ (X - r) h`, and removes the extra root again. -/
theorem StrictInterl.add_of_left {f g h : ℝ[X]}
    (hhf : StrictInterl h f) (hhg : StrictInterl h g)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g) :
    StrictInterl h (f + g) := by
  wlog hh_pos : HasPosLeadingCoeff h generalizing h
  · have hneg_pos : HasPosLeadingCoeff (C (-1 : ℝ) * h) := by
      have hlt : h.leadingCoeff < 0 :=
        lt_of_le_of_ne (not_lt.mp hh_pos) (leadingCoeff_ne_zero.mpr hhf.1.1)
      unfold HasPosLeadingCoeff
      rw [leadingCoeff_mul, leadingCoeff_C]
      linarith
    have hback := (this (hhf.C_mul_left (by norm_num)) (hhg.C_mul_left (by norm_num))
      hneg_pos).C_mul_left (show (-1 : ℝ) ≠ 0 by norm_num)
    rwa [← mul_assoc, ← C_mul, neg_one_mul, neg_neg, C_1, one_mul] at hback
  obtain ⟨r, hh_le, hf_le, hg_le⟩ : ∃ r : ℝ, (∀ s ∈ h.roots, s ≤ r) ∧
      (∀ s ∈ f.roots, s ≤ r) ∧ ∀ s ∈ g.roots, s ≤ r := by
    obtain ⟨r₁, hr₁⟩ := exists_root_upper_bound h
    obtain ⟨r₂, hr₂⟩ := exists_root_upper_bound f
    obtain ⟨r₃, hr₃⟩ := exists_root_upper_bound g
    exact ⟨max r₁ (max r₂ r₃), fun s hs => le_max_of_le_left (hr₁ s hs),
      fun s hs => le_max_of_le_right (le_max_of_le_left (hr₂ s hs)),
      fun s hs => le_max_of_le_right (le_max_of_le_right (hr₃ s hs))⟩
  have hright : ∀ p : ℝ[X], StrictInterl h p → HasPosLeadingCoeff p →
      (∀ s ∈ p.roots, s ≤ r) → StrictInterl p ((X - C r) * h) := by
    intro p hp hp_pos hp_le
    rcases hp.natDegree_eq_or_eq_succ with hdeg | hdeg
    · exact hp.mul_X_sub_C_of_sameDegree_of_roots_le r hdeg.symm hh_pos hp_pos hh_le hp_le
    · exact (strictInterl_iff_strictInterl_mul_X_sub_C_of_roots_le r hp.1.2 hp.2.1.2
        hh_pos hp_pos hh_le hp_le hdeg.symm).mp hp
  have hsum : StrictInterl (f + g) ((X - C r) * h) :=
    StrictInterl.add_of_right_of_posLeadingCoeff (hright f hhf hf_pos hf_le)
      (hright g hhg hg_pos hg_le) hf_pos hg_pos
  have hsum_pos : HasPosLeadingCoeff (f + g) := by
    rcases lt_trichotomy f.natDegree g.natDegree with hlt | heq | hgt
    · exact hasPosLeadingCoeff_add_of_natDegree_lt_right hlt hg_pos
    · exact hasPosLeadingCoeff_add_of_same_natDegree heq hf_pos hg_pos
    · exact hasPosLeadingCoeff_add_of_natDegree_lt_left hgt hf_pos
  have hsum_le : ∀ s ∈ (f + g).roots, s ≤ r :=
    hsum.roots_le_of_right (roots_le_X_sub_C_mul hhf.1.2 hh_le)
  have hXh_deg : ((X - C r) * h).natDegree = h.natDegree + 1 := by
    rw [natDegree_mul (X_sub_C_ne_zero r) hhf.1.1, natDegree_X_sub_C]
    lia
  rcases hsum.natDegree_eq_or_eq_succ with hdeg | hdeg
  · exact (strictInterl_iff_strictInterl_mul_X_sub_C_of_roots_le r hhf.1.2 hsum.1.2
      hh_pos hsum_pos hh_le hsum_le (by lia)).mpr hsum
  · exact hsum.of_mul_X_sub_C_of_sameDegree_of_roots_le (by lia) hh_pos hsum_pos hh_le
      hsum_le

/-- Recursive compatibility data for iterating Wagner (2) along a nonempty
list. Each new head term must be interlaced by the same left bound and have
positive leading coefficient; by `StrictInterl.add_of_left`, no real-rootedness
or coprimeness condition on the partial sums is needed. -/
inductive SumCompatibleLeft (h : ℝ[X]) : List ℝ[X] → Prop
  | singleton {p : ℝ[X]}
      (hstrictInterl : StrictInterl h p) (hpos : HasPosLeadingCoeff p) :
      SumCompatibleLeft h [p]
  | cons {p : ℝ[X]} {l : List ℝ[X]}
      (hstrictInterl : StrictInterl h p) (hpos : HasPosLeadingCoeff p)
      (hl : SumCompatibleLeft h l) :
      SumCompatibleLeft h (p :: l)

namespace SumCompatibleLeft

lemma hasPosLeadingCoeff_sum {h : ℝ[X]} :
    ∀ {l : List ℝ[X]}, SumCompatibleLeft h l → HasPosLeadingCoeff l.sum
  | _, singleton _ hpos => by
      simp_all
  | _, @cons _ p l _ hpos hl => by
      have htail_pos : HasPosLeadingCoeff l.sum := hasPosLeadingCoeff_sum hl
      rcases lt_trichotomy p.natDegree l.sum.natDegree with hlt | heq | hgt
      · simpa using hasPosLeadingCoeff_add_of_natDegree_lt_right hlt htail_pos
      · simpa [List.sum_cons] using hasPosLeadingCoeff_add_of_same_natDegree heq hpos htail_pos
      · simpa using hasPosLeadingCoeff_add_of_natDegree_lt_left hgt hpos

lemma toStrictInterl {h : ℝ[X]} :
    ∀ {l : List ℝ[X]}, SumCompatibleLeft h l → StrictInterl h l.sum
  | _, singleton hstrictInterl _ => by
      simp_all
  | _, @cons _ p l hstrictInterl hpos hl =>
      StrictInterl.add_of_left hstrictInterl (toStrictInterl hl)
        hpos (hasPosLeadingCoeff_sum hl)

end SumCompatibleLeft

end
end RealRooted
