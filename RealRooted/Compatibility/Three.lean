import RealRooted.ChudnovskySeymour.Core

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
nonnegative-coefficient split polynomials, then every nonnegative conic
recombination of `a` and `b` remains compatible with `c`. -/
theorem C_mul_add_C_mul_left_of_pairwise_three
    {a b c : ℝ[X]} {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (ha : a ≠ 0 ∧ a.Splits) (hb : b ≠ 0 ∧ b.Splits) (hc : c ≠ 0 ∧ c.Splits)
    (hapos : HasPosLeadingCoeff a) (hbpos : HasPosLeadingCoeff b)
    (hcpos : HasPosLeadingCoeff c) (hann : HasNonnegCoeffs a)
    (hbnn : HasNonnegCoeffs b) (hcnn : HasNonnegCoeffs c)
    (hab : Compatible a b) (hac : Compatible a c) (hbc : Compatible b c) :
    Compatible (C s * a + C t * b) c := by
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
  let ws : List (ℝ × ℝ[X]) := [(α * s, a), (α * t, b), (β, c)]
  have hmem : ∀ ap ∈ ws, ap.2 ∈ fs := by
    intro ap hap
    simp only [ws, List.mem_cons, List.not_mem_nil, or_false] at hap
    rcases hap with rfl | rfl | rfl <;> simp [fs]
  have hnonneg : ∀ ap ∈ ws, 0 ≤ ap.1 := by
    intro ap hap
    simp only [ws, List.mem_cons, List.not_mem_nil, or_false] at hap
    rcases hap with rfl | rfl | rfl
    · exact mul_nonneg hα hs
    · exact mul_nonneg hα ht
    · exact hβ
  have hsum :
      weightedSum ws = C α * (C s * a + C t * b) + C β * c := by
    simp only [ws, weightedSum_cons, weightedSum_nil]
    rw [map_mul, map_mul]
    ring
  simpa [hsum] using hfam ws hmem hnonneg

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
  simpa using C_mul_add_C_mul_left_of_pairwise_three
    (s := 1) (t := r) zero_le_one hr ha hb hc hapos hbpos hcpos
      hann hbnn hcnn hab hac hbc

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

/-- If both `f` and its `X`-multiple are compatible with `g`, then the
nonnegative-coefficient pair is directed as `f ≪ g`.

The three pairwise compatibilities among `X * f`, `f`, and `g` give the
positive affine family required by `strictInterl_of_affine_family_nonneg`. -/
theorem prec_of_compatible_and_X_mul_left
    {f g : ℝ[X]}
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hf_nonneg : HasNonnegCoeffs f) (hg_nonneg : HasNonnegCoeffs g)
    (hfg : Compatible f g) (hXfg : Compatible (X * f) g) :
    StrictInterl f g := by
  have hf_pos : HasPosLeadingCoeff f := hf_nonneg.pos_leadingCoeff hf0
  have hg_pos : HasPosLeadingCoeff g := hg_nonneg.pos_leadingCoeff hg0
  have hf_rr : f ≠ 0 ∧ f.Splits := hfg.isRealRooted_left hf_pos
  have hg_rr : g ≠ 0 ∧ g.Splits := hfg.isRealRooted_right hg_pos
  have hXf_rr : X * f ≠ 0 ∧ (X * f).Splits :=
    hXfg.isRealRooted_left hf_pos.X_mul
  apply strictInterl_of_affine_family_nonneg hf0 hg0 hf_nonneg hg_nonneg
  intro s t hs ht
  have hcompat : Compatible (C s * (X * f) + C t * f) g :=
    Compatible.C_mul_add_C_mul_left_of_pairwise_three
      hs.le ht.le hXf_rr hf_rr hg_rr hf_pos.X_mul hf_pos hg_pos
      hf_nonneg.X_mul hf_nonneg hg_nonneg
      (Compatible.self_X_mul_of_splits hf_rr.2).comm hXfg hfg
  have hrewrite :
      C s * (X * f) + C t * f = (C s * X + C t) * f := by
    ring
  have hne : (C s * (X * f) + C t * f) + g ≠ 0 := by
    rw [hrewrite]
    exact add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero
      (hasNonnegCoeffs_affine_mul hs.le ht.le hf_nonneg) hg_nonneg hg_rr.1
  exact ⟨by simpa [hrewrite] using hne,
    by simpa [hrewrite] using hcompat.splits_add hne⟩

end RealRooted
