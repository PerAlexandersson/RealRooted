import RealRooted.BrandenVecchi.ChowInterlacingSign
import RealRooted.BrandenVecchi.ReflectionInterlacing
import RealRooted.Interlacing.OuterDifference
import RealRooted.PosCombo

/-!
# The Chow quotient in a reflection-interlacing pair

This file assembles the quotient step in Brändén--Vecchi, Lemma 4.11.
The generic signed outer-difference theorem first places the reflection
difference to the right of the middle polynomial.  We then remove its exact
factor `X - 1`, treating both possible degree cases, and recover
nonnegative coefficients from the resulting root order.
-/

open Polynomial

noncomputable section

namespace RealRooted

private lemma listInterlaces_right_le_of_left_lt_of_mem
    {ss rs : List ℝ} {c : ℝ} (hint : ListInterlaces ss rs)
    (hleft : ∀ s ∈ ss, s < c) (hc : c ∈ rs) :
    ∀ r ∈ rs, r ≤ c := by
  induction ss generalizing rs with
  | nil =>
      cases rs with
      | nil => simp at hc
      | cons r rs =>
          cases rs with
          | nil =>
              have hcr : c = r := by simpa using hc
              have hr : r = c := hcr.symm
              subst r
              simp
          | cons r₂ rs => simp [ListInterlaces] at hint
  | cons s ss ih =>
      cases rs with
      | nil => simp at hc
      | cons r₁ rs =>
          cases rs with
          | nil => simp [ListInterlaces] at hint
          | cons r₂ rs =>
              rcases hint with ⟨hr₁s, hsr₂, htail⟩
              rcases List.mem_cons.mp hc with hc | hc
              · subst r₁
                exfalso
                linarith [hleft s (by simp)]
              · have htail_le := ih htail
                  (fun x hx => hleft x (by simp [hx])) hc
                intro x hx
                rcases List.mem_cons.mp hx with rfl | hx
                · exact hr₁s.trans (hsr₂.trans (htail_le r₂ (by simp)))
                · exact htail_le x hx

private lemma listAlternates_right_le_of_left_lt_of_mem
    {ss rs : List ℝ} {c : ℝ} (halt : ListAlternates ss rs)
    (hleft : ∀ s ∈ ss, s < c) (hc : c ∈ rs) :
    ∀ r ∈ rs, r ≤ c := by
  cases ss with
  | nil =>
      cases rs <;> simp [ListAlternates] at halt hc
  | cons s ss =>
      cases rs with
      | nil => simp at hc
      | cons r rs =>
          exact listInterlaces_right_le_of_left_lt_of_mem halt.2
            (fun x hx => hleft x (by simp [hx])) hc

/-- If the roots of the left member of a proper-position pair lie strictly
below a root `c` of the right member, then `c` is an upper bound for all roots
of the right member. -/
theorem roots_le_of_prec_of_left_roots_lt_of_right_root
    {f g : ℝ[X]} {c : ℝ} (hprec : Prec f g)
    (hleft : ∀ r ∈ f.roots, r < c) (hc : g.IsRoot c) :
    ∀ r ∈ g.roots, r ≤ c := by
  rcases hprec with ⟨hf, hg, ss, rs, _hss_sorted, _hrs_sorted,
    hss_eq, hrs_eq, hshape⟩
  have hleft' : ∀ r ∈ ss, r < c := by
    intro r hr
    apply hleft r
    rw [← hss_eq]
    exact Multiset.mem_coe.mpr hr
  have hc' : c ∈ rs := by
    apply Multiset.mem_coe.mp
    rw [hrs_eq]
    exact (mem_roots hg.1).mpr hc
  have hrs_le : ∀ r ∈ rs, r ≤ c := by
    rcases hshape with ⟨_, hint⟩ | ⟨_, halt⟩
    · exact listInterlaces_right_le_of_left_lt_of_mem hint hleft' hc'
    · exact listAlternates_right_le_of_left_lt_of_mem halt hleft' hc'
  intro r hr
  apply hrs_le r
  apply Multiset.mem_coe.mp
  rwa [hrs_eq]

namespace BrandenVecchi

namespace IsReflectionInterlacingSeq

/-- A nonzero first member strictly precedes its reflection in the closed
two-member sequence. -/
theorem strictSelfReflect {n : ℕ} {f g : ℝ[X]}
    (h : IsReflectionInterlacingSeq n [f, g]) (hf_ne : f ≠ 0) :
    Prec f (f.reflect n) := by
  have href_ne : f.reflect n ≠ 0 := by
    intro href_zero
    exact hf_ne (Polynomial.reflect_eq_zero_iff.mp href_zero)
  have hclosed := h.closedSequence
  have hfref0 : Prec0 f (f.reflect n) := by
    simpa [reflectionClosure] using
      hclosed.interlacingSeq0.prec0
        (i := (⟨0, by simp [reflectionClosure]⟩ :
          Fin (reflectionClosure n [f, g]).length))
        (j := (⟨3, by simp [reflectionClosure]⟩ :
          Fin (reflectionClosure n [f, g]).length)) (by simp)
  exact hfref0.toPrec_of_ne hf_ne href_ne

/-- The three strict proper-position relations carried by the two-member
reflection closure, once its original members are known to be nonzero. -/
theorem strictTriple {n : ℕ} {f g : ℝ[X]}
    (h : IsReflectionInterlacingSeq n [f, g])
    (hf_ne : f ≠ 0) (hg_ne : g ≠ 0) :
    Prec f g ∧ Prec g (f.reflect n) ∧ Prec f (f.reflect n) := by
  have href_ne : f.reflect n ≠ 0 := by
    intro href_zero
    exact hf_ne (Polynomial.reflect_eq_zero_iff.mp href_zero)
  have hclosed := h.closedSequence
  have hfg0 : Prec0 f g := by
    simpa [reflectionClosure] using
      hclosed.interlacingSeq0.prec0
        (i := (⟨0, by simp [reflectionClosure]⟩ :
          Fin (reflectionClosure n [f, g]).length))
        (j := (⟨1, by simp [reflectionClosure]⟩ :
          Fin (reflectionClosure n [f, g]).length)) (by simp)
  have hgref0 : Prec0 g (f.reflect n) := by
    simpa [reflectionClosure] using
      hclosed.interlacingSeq0.prec0
        (i := (⟨1, by simp [reflectionClosure]⟩ :
          Fin (reflectionClosure n [f, g]).length))
        (j := (⟨3, by simp [reflectionClosure]⟩ :
          Fin (reflectionClosure n [f, g]).length)) (by simp)
  exact ⟨hfg0.toPrec_of_ne hf_ne hg_ne,
    hgref0.toPrec_of_ne hg_ne href_ne,
    h.strictSelfReflect hf_ne⟩

end IsReflectionInterlacingSeq

/-- Strict Chow-quotient bridge for an ordered middle polynomial.  The
reflection-interlacing application uses either the second member or the first
member itself as `g`. -/
theorem chowS_nonnegCoeffs_and_prec_of_triple
    {n : ℕ} {f g : ℝ[X]} (hdegree : f.natDegree ≤ n)
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hfg : Prec f g) (hgref : Prec g (f.reflect n))
    (hfref : Prec f (f.reflect n))
    (hS_ne : Polynomial.chowS n f ≠ 0) :
    HasNonnegCoeffs (Polynomial.chowS n f) ∧
      Prec (Polynomial.chowS n f) g := by
  let S : ℝ[X] := Polynomial.chowS n f
  let fr : ℝ[X] := f.reflect n
  have hf_pos : HasPosLeadingCoeff f := hfnn.pos_leadingCoeff hfg.1.1
  have hg_pos : HasPosLeadingCoeff g := hgnn.pos_leadingCoeff hfg.2.1.1
  have hfrnn : HasNonnegCoeffs fr := by
    simpa [fr] using hfnn.reflect n
  have hfr_pos : HasPosLeadingCoeff fr :=
    hfrnn.pos_leadingCoeff hgref.2.1.1
  have hS_pos : HasPosLeadingCoeff S := by
    have hsign := chowS_eq_zero_or_hasPosLeadingCoeff hdegree hfnn hfref
    rcases hsign with hzero | hpos
    · exact (hS_ne hzero).elim
    · exact hpos
  have houter : Prec g (fr - f) :=
    prec_sub_of_prec_triple_of_posLeadingCoeff
      hfg hgref hfref hf_pos hg_pos hfr_pos (by
        have hmul := Polynomial.X_sub_one_mul_chowS n f hdegree
        have hfactor_pos : HasPosLeadingCoeff ((X - C 1) * S) :=
          hasPosLeadingCoeff_X_sub_C_mul hS_pos
        simpa [S, fr] using hmul.symm ▸ hfactor_pos)
  have hfactor : (X - C 1) * S = fr - f := by
    simpa [S, fr] using Polynomial.X_sub_one_mul_chowS n f hdegree
  have hS_dvd : S ∣ fr - f := by
    refine ⟨X - C 1, ?_⟩
    rw [← hfactor]
    ring
  have hS_rr : S ≠ 0 ∧ S.Splits :=
    isRealRooted_of_dvd houter.2.1.1 houter.2.1.2 hS_ne hS_dvd
  have hg_nonpos : ∀ r ∈ g.roots, r ≤ 0 :=
    roots_nonpos_of_nonneg_coeffs hfg.2.1.2 hgnn
  have hdiff_root_one : (fr - f).IsRoot 1 := by
    rw [← hfactor]
    simp [Polynomial.IsRoot.def]
  have hdiff_le_one : ∀ r ∈ (fr - f).roots, r ≤ 1 :=
    roots_le_of_prec_of_left_roots_lt_of_right_root houter
      (fun r hr => by linarith [hg_nonpos r hr]) hdiff_root_one
  have hS_le_one : ∀ r ∈ S.roots, r ≤ 1 := by
    intro r hr
    apply hdiff_le_one r
    apply (mem_roots houter.2.1.1).mpr
    exact IsRoot.of_dvd hS_dvd ((mem_roots hS_ne).mp hr)
  have hg_le_one : ∀ r ∈ g.roots, r ≤ 1 := by
    intro r hr
    linarith [hg_nonpos r hr]
  have hfactor_prec : Prec g ((X - C 1) * S) := by
    rw [hfactor]
    exact houter
  have hfactor_deg : ((X - C 1) * S).natDegree = S.natDegree + 1 := by
    rw [natDegree_mul (X_sub_C_ne_zero 1) hS_ne, natDegree_X_sub_C]
    lia
  have hSg : Prec S g := by
    rcases hfactor_prec.natDegree_eq_or_eq_succ with hsame | hsucc
    · have hdeg : S.natDegree + 1 = g.natDegree := by lia
      exact (prec_iff_prec_mul_X_sub_C_of_roots_le
        1 hS_rr.2 hfg.2.1.2 hS_pos hg_pos hS_le_one hg_le_one hdeg).mpr
          hfactor_prec
    · have hdeg : S.natDegree = g.natDegree := by lia
      exact prec_of_prec_mul_X_sub_C_of_sameDegree_of_roots_le
        1 hfactor_prec hdeg hS_pos hg_pos hS_le_one hg_le_one
  have hS_nonpos : ∀ r ∈ S.roots, r ≤ 0 :=
    roots_le_of_prec_right hSg hg_nonpos
  exact ⟨((hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos hS_rr.2).2
    ⟨hS_pos, hS_nonpos⟩).1, hSg⟩

/-- A nonzero Chow quotient strictly precedes the nonzero second member of a
two-member reflection-interlacing sequence and has nonnegative coefficients. -/
theorem IsReflectionInterlacingSeq.chowS_nonnegCoeffs_and_prec
    {n : ℕ} {f g : ℝ[X]} (h : IsReflectionInterlacingSeq n [f, g])
    (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hS_ne : Polynomial.chowS n f ≠ 0) :
    HasNonnegCoeffs (Polynomial.chowS n f) ∧
      Prec (Polynomial.chowS n f) g := by
  have htriple := h.strictTriple hf_ne hg_ne
  exact chowS_nonnegCoeffs_and_prec_of_triple
    (h.natDegree_le (by simp))
    (h.closedSequence.nonnegCoeffs f (by simp [reflectionClosure]))
    (h.closedSequence.nonnegCoeffs g (by simp [reflectionClosure]))
    htriple.1 htriple.2.1 htriple.2.2 hS_ne

/-- The Chow quotient of the first member of a reflection-interlacing pair
has nonnegative coefficients, including when the quotient vanishes. -/
theorem IsReflectionInterlacingSeq.chowS_nonnegCoeffs
    {n : ℕ} {f g : ℝ[X]} (h : IsReflectionInterlacingSeq n [f, g]) :
    HasNonnegCoeffs (Polynomial.chowS n f) := by
  by_cases hf_ne : f ≠ 0
  · by_cases hS_ne : Polynomial.chowS n f ≠ 0
    · have hfref := h.strictSelfReflect hf_ne
      exact (chowS_nonnegCoeffs_and_prec_of_triple
        (h.natDegree_le (by simp))
        (h.closedSequence.nonnegCoeffs f (by simp [reflectionClosure]))
        (h.closedSequence.nonnegCoeffs f (by simp [reflectionClosure]))
        (prec_refl hf_ne hfref.1.2) hfref hfref hS_ne).1
    · rw [not_ne_iff.mp hS_ne]
      exact hasNonnegCoeffs_zero
  · have hf_zero : f = 0 := not_ne_iff.mp hf_ne
    subst f
    simp [Polynomial.chowS, hasNonnegCoeffs_zero]

/-- Zero-aware Chow-quotient endpoint for a two-member
reflection-interlacing sequence. -/
theorem IsReflectionInterlacingSeq.chowS_prec0
    {n : ℕ} {f g : ℝ[X]} (h : IsReflectionInterlacingSeq n [f, g]) :
    Prec0 (Polynomial.chowS n f) g := by
  by_cases hS_ne : Polynomial.chowS n f ≠ 0
  · by_cases hg_ne : g ≠ 0
    · have hf_ne : f ≠ 0 := by
        intro hf_zero
        subst f
        simp [Polynomial.chowS] at hS_ne
      exact (h.chowS_nonnegCoeffs_and_prec hf_ne hg_ne hS_ne).2.toPrec0
    · have hg_zero : g = 0 := not_ne_iff.mp hg_ne
      rw [hg_zero]
      exact prec0_zero_right _
  · have hS_zero : Polynomial.chowS n f = 0 := not_ne_iff.mp hS_ne
    rw [hS_zero]
    exact prec0_zero_left g

/-- Complete zero-aware quotient package: the Chow quotient has nonnegative
coefficients and precedes the second member in `Prec0`. -/
theorem IsReflectionInterlacingSeq.chowS_nonnegCoeffs_and_prec0
    {n : ℕ} {f g : ℝ[X]} (h : IsReflectionInterlacingSeq n [f, g]) :
    HasNonnegCoeffs (Polynomial.chowS n f) ∧
      Prec0 (Polynomial.chowS n f) g :=
  ⟨h.chowS_nonnegCoeffs, h.chowS_prec0⟩

end BrandenVecchi

end RealRooted
