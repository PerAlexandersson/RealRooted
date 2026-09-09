import RealRooted.InterlacingSequenceBasic
import RealRooted.WagnerX.NonnegativeRoots

/-!
# Simultaneous nonnegative translation of finite interlacing sequences

A finite family of split real polynomials with positive leading coefficients
can be translated by one common amount so that every member has nonnegative
coefficients. Translation preserves both strict and zero-aware proper position,
so the same normalization applies to finite interlacing sequences.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- A finite list of real polynomials has one common upper bound for all of its
real roots. -/
theorem exists_common_root_upper_bound (fs : List ℝ[X]) :
    ∃ r : ℝ, ∀ p ∈ fs, ∀ s ∈ p.roots, s ≤ r := by
  induction fs with
  | nil => exact ⟨0, by simp⟩
  | cons p fs ih =>
      obtain ⟨rp, hp⟩ := exists_root_upper_bound p
      obtain ⟨rfs, hfs⟩ := ih
      refine ⟨max rp rfs, ?_⟩
      intro q hq s hs
      rcases List.mem_cons.mp hq with rfl | hq
      · exact (hp s hs).trans (le_max_left _ _)
      · exact (hfs q hq s hs).trans (le_max_right _ _)

/-- A finite list of split positive-leading real polynomials can be translated
simultaneously to have nonnegative coefficients. -/
theorem exists_comp_X_add_C_hasNonnegCoeffs (fs : List ℝ[X])
    (hfs : ∀ p ∈ fs, HasPosLeadingCoeff p ∧ p.Splits) :
    ∃ r : ℝ, ∀ p ∈ fs, HasNonnegCoeffs (p.comp (X + C r)) := by
  obtain ⟨r, hr⟩ := exists_common_root_upper_bound fs
  refine ⟨r, ?_⟩
  intro p hp
  exact hasNonnegCoeffs_comp_X_add_C_of_roots_le
    (hfs p hp).1 (hfs p hp).2 (hr p hp)

/-- Simultaneous translation is an equivalence for zero-aware proper
position. -/
theorem prec0_comp_X_add_C_iff {f g : ℝ[X]} (r : ℝ) :
    Prec0 (f.comp (X + C r)) (g.comp (X + C r)) ↔ Prec0 f g := by
  simp only [Prec0, Polynomial.comp_X_add_C_eq_zero_iff,
    prec_comp_X_add_C_iff]

/-- Simultaneous translation is an equivalence for finite interlacing
sequences. -/
theorem isInterlacingSeq_map_comp_X_add_C_iff (fs : List ℝ[X]) (r : ℝ) :
    IsInterlacingSeq (fs.map fun p => p.comp (X + C r)) ↔
      IsInterlacingSeq fs := by
  rw [isInterlacingSeq_iff_pairwise, isInterlacingSeq_iff_pairwise,
    List.pairwise_map]
  simp only [prec_comp_X_add_C_iff]

/-- Filtering out zero polynomials commutes with simultaneous translation. -/
theorem filter_map_comp_X_add_C_ne_zero (fs : List ℝ[X]) (r : ℝ) :
    (fs.map fun p => p.comp (X + C r)).filter (· ≠ 0) =
      (fs.filter (· ≠ 0)).map fun p => p.comp (X + C r) := by
  rw [List.filter_map]
  congr 2
  funext p
  simp only [Function.comp_apply, Polynomial.comp_X_add_C_ne_zero_iff]

/-- A finite positive-leading split interlacing sequence has a simultaneous
translation into the nonnegative-coefficient interlacing class. -/
theorem exists_comp_X_add_C_isInterlacingSeqNonneg (fs : List ℝ[X])
    (hfs_real : ∀ p ∈ fs, HasPosLeadingCoeff p ∧ p.Splits)
    (hfs : IsInterlacingSeq fs) :
    ∃ r : ℝ,
      IsInterlacingSeqNonneg (fs.map fun p => p.comp (X + C r)) := by
  obtain ⟨r, hnonneg⟩ := exists_comp_X_add_C_hasNonnegCoeffs fs hfs_real
  refine ⟨r, ?_, (isInterlacingSeq_map_comp_X_add_C_iff fs r).2 hfs⟩
  intro q hq
  rcases List.mem_map.mp hq with ⟨p, hp, rfl⟩
  exact ⟨isRealRooted_comp_X_add_C (hfs_real p hp).1.ne_zero
    (hfs_real p hp).2 r, hnonneg p hp⟩

end RealRooted
