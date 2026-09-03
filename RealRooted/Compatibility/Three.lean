import RealRooted.ChudnovskySeymour

/-!
# Three-polynomial compatibility assembly

This module packages the three-member Chudnovsky--Seymour argument used when
one member of a pair is replaced by a nonnegative sum of two pairwise
compatible polynomials.
-/

open Polynomial

noncomputable section

namespace RealRooted

namespace Compatible

/-- If `a`, `b`, and `c` are pairwise compatible positive-leading
nonnegative-coefficient split polynomials, then replacing `a` by
`a + r * b` for `r ≥ 0` preserves compatibility with `c`. -/
theorem add_C_mul_left_of_pairwise_three
    {a b c : ℝ[X]} {r : ℝ} (hr : 0 ≤ r)
    (ha : a ≠ 0 ∧ a.Splits) (hb : b ≠ 0 ∧ b.Splits) (hc : c ≠ 0 ∧ c.Splits)
    (hapos : HasPosLeadingCoeff a) (hbpos : HasPosLeadingCoeff b)
    (hcpos : HasPosLeadingCoeff c) (hann : HasNonnegCoeffs a)
    (hbnn : HasNonnegCoeffs b) (hcnn : HasNonnegCoeffs c)
    (hab : Compatible a b) (hac : Compatible a c) (hbc : Compatible b c) :
    Compatible (a + C r * b) c := by
  let fs : List ℝ[X] := [a, b, c]
  have hrr : ∀ f ∈ fs, f ≠ 0 ∧ f.Splits := by
    intro f hf
    simp only [fs, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl <;> simp_all
  have hpos : ∀ f ∈ fs, HasPosLeadingCoeff f := by
    intro f hf
    simp only [fs, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · exact hapos
    · exact hbpos
    · exact hcpos
  have hnn : ∀ f ∈ fs, HasNonnegCoeffs f := by
    intro f hf
    simp only [fs, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · exact hann
    · exact hbnn
    · exact hcnn
  have hpair : PairwiseCompatible fs := by
    apply pairwiseCompatible_of_forall_mem
    intro f hf g hg
    simp only [fs, List.mem_cons, List.not_mem_nil, or_false] at hf hg
    rcases hf with rfl | rfl | rfl <;> rcases hg with rfl | rfl | rfl
    · exact Compatible.self_of_splits ha.2
    · exact hab
    · exact hac
    · exact hab.comm
    · exact Compatible.self_of_splits hb.2
    · exact hbc
    · exact hac.comm
    · exact hbc.comm
    · exact Compatible.self_of_splits hc.2
  have hfam : FamilyCompatible fs :=
    (chudnovskySeymour_pairwiseCompatible_iff_familyCompatible_nonnegCoeffs
      (fs := fs) hrr hpos hnn).1 hpair
  intro α β hα hβ
  let ws : List (ℝ × ℝ[X]) := [(α, a), (α * r, b), (β, c)]
  have hmem : ∀ ap ∈ ws, ap.2 ∈ fs := by
    intro ap hap
    simp only [ws, List.mem_cons, List.not_mem_nil, or_false] at hap
    rcases hap with rfl | rfl | rfl <;> simp [fs]
  have hnonneg : ∀ ap ∈ ws, 0 ≤ ap.1 := by
    intro ap hap
    simp only [ws, List.mem_cons, List.not_mem_nil, or_false] at hap
    rcases hap with rfl | rfl | rfl
    · exact hα
    · exact mul_nonneg hα hr
    · exact hβ
  have hsum : weightedSum ws = C α * (a + C r * b) + C β * c := by
    simp only [ws, weightedSum_cons, weightedSum_nil]
    rw [map_mul]
    ring
  simpa [hsum] using hfam ws hmem hnonneg

/-- Unscaled specialization of `Compatible.add_C_mul_left_of_pairwise_three`. -/
theorem add_left_of_pairwise_three {a b c : ℝ[X]}
    (ha : a ≠ 0 ∧ a.Splits) (hb : b ≠ 0 ∧ b.Splits) (hc : c ≠ 0 ∧ c.Splits)
    (hapos : HasPosLeadingCoeff a) (hbpos : HasPosLeadingCoeff b)
    (hcpos : HasPosLeadingCoeff c) (hann : HasNonnegCoeffs a)
    (hbnn : HasNonnegCoeffs b) (hcnn : HasNonnegCoeffs c)
    (hab : Compatible a b) (hac : Compatible a c) (hbc : Compatible b c) :
    Compatible (a + b) c := by
  simpa using add_C_mul_left_of_pairwise_three
    (r := 1) zero_le_one ha hb hc hapos hbpos hcpos hann hbnn hcnn hab hac hbc

end Compatible

end RealRooted
