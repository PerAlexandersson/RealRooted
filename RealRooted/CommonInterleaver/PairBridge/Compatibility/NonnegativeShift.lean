import RealRooted.CommonInterleaver.PairBridge.Compatibility

/-!
# Chudnovsky--Seymour for two polynomials

Translating a split pair far enough makes its coefficients nonnegative, which
reduces the two-polynomial common-interleaver theorem to the nonnegative case.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- A common right interleaver is invariant under translating both inputs. -/
theorem pairHasCommonInterleaver_comp_X_add_C_iff
    {f g : ℝ[X]} (r : ℝ) :
    (∃ h : ℝ[X],
      StrictInterl (f.comp (X + C r)) h ∧
        StrictInterl (g.comp (X + C r)) h) ↔
      ∃ h : ℝ[X], StrictInterl f h ∧ StrictInterl g h := by
  constructor
  · rintro ⟨h, hf, hg⟩
    have key : (h.comp (X + C (-r))).comp (X + C r) = h := by
      rw [comp_assoc]
      simp
    exact ⟨h.comp (X + C (-r)),
      (StrictInterl.comp_X_add_C_iff r).mp (by rw [key]; exact hf),
      (StrictInterl.comp_X_add_C_iff r).mp (by rw [key]; exact hg)⟩
  · rintro ⟨h, hf, hg⟩
    exact ⟨h.comp (X + C r), hf.comp_X_add_C r, hg.comp_X_add_C r⟩

private theorem posComboPairHasCommonInterleaver_via_nonnegShift
    {f g : ℝ[X]}
    (_hf_rr_ne : f ≠ 0) (hf_rr_splits : f.Splits)
    (_hg_rr_ne : g ≠ 0) (hg_rr_splits : g.Splits)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hNonneg :
      ∀ {F G : ℝ[X]},
        HasPosLeadingCoeff F →
        HasPosLeadingCoeff G →
        HasNonnegCoeffs F →
        HasNonnegCoeffs G →
        PosComboRealRooted F G →
        ∃ h : ℝ[X], StrictInterl F h ∧ StrictInterl G h) :
    ∃ h : ℝ[X], StrictInterl f h ∧ StrictInterl g h := by
  obtain ⟨rf, hrf⟩ := exists_root_upper_bound f
  obtain ⟨rg, hrg⟩ := exists_root_upper_bound g
  let r : ℝ := max rf rg
  let f' : ℝ[X] := f.comp (X + C r)
  let g' : ℝ[X] := g.comp (X + C r)
  have hf'_pos : HasPosLeadingCoeff f' := by simpa [f'] using hf_pos.comp_X_add_C r
  have hg'_pos : HasPosLeadingCoeff g' := by simpa [g'] using hg_pos.comp_X_add_C r
  have hfnn : HasNonnegCoeffs f' := by
    refine hasNonnegCoeffs_comp_X_add_C_of_roots_le hf_pos hf_rr_splits ?_
    grind
  have hgnn : HasNonnegCoeffs g' := by
    refine hasNonnegCoeffs_comp_X_add_C_of_roots_le hg_pos hg_rr_splits ?_
    grind
  have hfg' : PosComboRealRooted f' g' := by
    intro α β hα hβ
    simpa [f', g'] using hfg.comp_X_add_C r hα hβ
  apply (pairHasCommonInterleaver_comp_X_add_C_iff (f := f) (g := g) r).1
  simpa [f', g'] using hNonneg hf'_pos hg'_pos hfnn hgnn hfg'

/-- Degree-bounded common-interleaver endpoint for positive-leading split
positive-combination pairs.  Translating both polynomials far enough makes the
shifted coefficients nonnegative without changing their degrees, so the
nonnegative unordered degree-bounded reduction applies to the shifted pair; the
resulting common right interleaver is translated back. -/
theorem posComboPairHasCommonInterleaver_of_natDegree_le_reduction_unordered_via_nonnegShift
    {N : ℕ}
    (hterminal :
      ∀ ⦃f g : ℝ[X]⦄,
        HasPosLeadingCoeff f →
        HasPosLeadingCoeff g →
        HasNonnegCoeffs f →
        HasNonnegCoeffs g →
        PosComboRealRooted f g →
        f.natDegree ≤ g.natDegree →
        g.natDegree ≤ f.natDegree + 1 →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        g.natDegree ≤ N →
        ∃ h : ℝ[X], StrictInterl f h ∧ StrictInterl g h)
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_splits : f.Splits)
    (hg_splits : g.Splits)
    (hfg : PosComboRealRooted f g)
    (hfdeg : f.natDegree ≤ N)
    (hgdeg : g.natDegree ≤ N) :
    ∃ h : ℝ[X], StrictInterl f h ∧ StrictInterl g h := by
  obtain ⟨rf, hrf⟩ := exists_root_upper_bound f
  obtain ⟨rg, hrg⟩ := exists_root_upper_bound g
  let r : ℝ := max rf rg
  let f' : ℝ[X] := f.comp (X + C r)
  let g' : ℝ[X] := g.comp (X + C r)
  have hf'_pos : HasPosLeadingCoeff f' := by simpa [f'] using hf_pos.comp_X_add_C r
  have hg'_pos : HasPosLeadingCoeff g' := by simpa [g'] using hg_pos.comp_X_add_C r
  have hfnn : HasNonnegCoeffs f' := by
    refine hasNonnegCoeffs_comp_X_add_C_of_roots_le hf_pos hf_splits ?_
    grind
  have hgnn : HasNonnegCoeffs g' := by
    refine hasNonnegCoeffs_comp_X_add_C_of_roots_le hg_pos hg_splits ?_
    grind
  have hfg' : PosComboRealRooted f' g' := by
    intro α β hα hβ
    simpa [f', g'] using hfg.comp_X_add_C r hα hβ
  have hfdeg' : f'.natDegree ≤ N := by
    have hdeg_eq : f'.natDegree = f.natDegree := by simp [f', Polynomial.natDegree_comp]
    lia
  have hgdeg' : g'.natDegree ≤ N := by
    have hdeg_eq : g'.natDegree = g.natDegree := by simp [g', Polynomial.natDegree_comp]
    lia
  apply (pairHasCommonInterleaver_comp_X_add_C_iff (f := f) (g := g) r).1
  simpa [f', g'] using
    posComboPairHasCommonInterleaver_of_natDegree_le_reduction_unordered
      (N := N) hterminal hf'_pos hg'_pos hfnn hgnn hfg' hfdeg' hgdeg'

/-- Positive-combination degree-`≤ 2` pair endpoint.  Translate both
polynomials far enough to make the shifted roots nonpositive, apply the
nonnegative-coefficient degree-`≤ 2` endpoint, and translate the common right
interleaver back. -/
theorem posComboPairHasCommonInterleaver_of_natDegree_le_two
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_splits : f.Splits)
    (hg_splits : g.Splits)
    (hfg : PosComboRealRooted f g)
    (hfdeg : f.natDegree ≤ 2)
    (hgdeg : g.natDegree ≤ 2) :
    ∃ h : ℝ[X], StrictInterl f h ∧ StrictInterl g h :=
  posComboPairHasCommonInterleaver_of_natDegree_le_reduction_unordered_via_nonnegShift
    (N := 2)
    (fun {_f _g} hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno hgdeg =>
      posComboNoCommonPairHasCommonInterleaver_of_natDegree_le_two
        hf_pos hg_pos hfnn hgnn hfg hdeg_lo hdeg_hi hno hgdeg)
    hf_pos hg_pos hf_splits hg_splits hfg hfdeg hgdeg

/-- Compatibility-level degree-`≤ 2` two-polynomial Chudnovsky--Seymour
endpoint. -/
theorem compatiblePairHasCommonInterleaver_of_natDegree_le_two
    {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : Compatible f g)
    (hfdeg : f.natDegree ≤ 2)
    (hgdeg : g.natDegree ≤ 2) :
    ∃ h : ℝ[X], StrictInterl f h ∧ StrictInterl g h :=
  posComboPairHasCommonInterleaver_of_natDegree_le_two hf_pos hg_pos
    (hfg.isRealRooted_left hf_pos).2
    (hfg.isRealRooted_right hg_pos).2
    (hfg.toPosComboRealRooted hf_pos hg_pos) hfdeg hgdeg

/-- Two split polynomials with positive leading coefficients whose positive
combinations are real-rooted have a common interleaver.  Translating both far
enough makes their coefficients nonnegative, where
`posComboPairHasCommonInterleaver_of_nonnegCoeffs` applies; the common
interleaver is translated back. -/
theorem posComboPairHasCommonInterleaver_of_splits
    {f g : ℝ[X]} (hf_splits : f.Splits) (hg_splits : g.Splits)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g) :
    ∃ h : ℝ[X], StrictInterl f h ∧ StrictInterl g h :=
  posComboPairHasCommonInterleaver_via_nonnegShift
    hf_pos.ne_zero hf_splits hg_pos.ne_zero hg_splits hf_pos hg_pos hfg
    (fun {_ _} hF_pos hG_pos hFnn hGnn hFG =>
      posComboPairHasCommonInterleaver_of_nonnegCoeffs hF_pos hG_pos hFnn hGnn hFG)

/-- **Chudnovsky--Seymour for two polynomials.** Compatible polynomials with
positive leading coefficients have a common interleaver. -/
theorem chudnovskySeymour_compatiblePairHasCommonInterleaver
    ⦃f g : ℝ[X]⦄ (hf : HasPosLeadingCoeff f) (hg : HasPosLeadingCoeff g)
    (h : Compatible f g) :
    ∃ k : ℝ[X], StrictInterl f k ∧ StrictInterl g k :=
  posComboPairHasCommonInterleaver_of_splits
    (h.isRealRooted_left hf).2 (h.isRealRooted_right hg).2 hf hg
    (h.toPosComboRealRooted hf hg)

end RealRooted
