module

import RealRooted.BrandenVecchi.ChowInterlacingQuotient
import RealRooted.CommonInterleaver.RootDesc
public import RealRooted.BrandenVecchi.ReflectionInterlacing
public import RealRooted.Mathlib.Algebra.Polynomial.Chow
import RealRooted.PFPolynomial
import RealRooted.WagnerX.NonnegativeRoots
import RealRooted.Linear
import Mathlib.Data.List.GetD

/-!
# The four-term Chow reflection-interlacing extension

This file proves Branden--Vecchi, Lemma 4.12, in the project's zero-aware
form.  The proof follows the source's seven-term chain.  The literal
`reflectionClosure` contains the self-reflected middle polynomial twice;
this harmless duplicate is retained so the result uses the canonical list
predicate.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

private theorem pairwise_interl_of_filter_ne_zero_pairwise_strictInterl :
    ∀ fs : List ℝ[X], (fs.filter (· ≠ 0)).Pairwise StrictInterl → fs.Pairwise Interl
  | [], _ => by simp
  | f :: fs, h => by
      by_cases hf : f = 0
      · subst f
        constructor
        · exact fun _ _ => interl_zero_left _
        · exact pairwise_interl_of_filter_ne_zero_pairwise_strictInterl fs (by simpa using h)
      · have h' : (f :: fs.filter (· ≠ 0)).Pairwise StrictInterl := by
          simpa [List.filter_cons, hf] using h
        rcases List.pairwise_cons.mp h' with ⟨hhead, htail⟩
        apply List.pairwise_cons.2
        refine ⟨?_, pairwise_interl_of_filter_ne_zero_pairwise_strictInterl fs htail⟩
        intro g hg
        by_cases hg_zero : g = 0
        · exact Or.inr (Or.inl hg_zero)
        · exact (hhead g (by simp [hg, hg_zero])).toInterl

private theorem isInterlacingSeq0NonnegRealRooted_of_filter_ne_zero
    {fs : List ℝ[X]} (hstrict : IsInterlacingSeqNonneg (fs.filter (· ≠ 0)))
    (hnonneg : ∀ p ∈ fs, HasNonnegCoeffs p)
    (hreal : ∀ p ∈ fs, p ≠ 0 → p.Splits) :
    IsInterlacingSeq0NonnegRealRooted fs := by
  refine ⟨⟨?_, hnonneg⟩, ?_⟩
  · rw [isInterlacingSeq0_iff_pairwise]
    exact pairwise_interl_of_filter_ne_zero_pairwise_strictInterl fs
      (isInterlacingSeq_iff_pairwise.mp hstrict.2)
  · exact fun p hp hp_ne => ⟨hp_ne, hreal p hp hp_ne⟩

private theorem isInterlacingSeqNonneg_of_getD_chain
    {fs : List ℝ[X]} (hlen : 2 ≤ fs.length)
    (hnonneg : ∀ p ∈ fs, HasNonnegCoeffs p)
    (hcons : ∀ k, k < fs.length - 1 →
      StrictInterl (fs.getD k 0) (fs.getD (k + 1) 0))
    (hend : StrictInterl (fs.getD 0 0) (fs.getD (fs.length - 1) 0)) :
    IsInterlacingSeqNonneg fs := by
  let F : ℕ → ℝ[X] := fun k => fs.getD k 0
  have hall := strictInterl_chain_of_consecutive_of_endpoint F 0 (fs.length - 1)
    (fun k _ hk => hcons k hk) hend
  refine ⟨?_, ?_⟩
  · intro p hp
    rcases List.get_of_mem hp with ⟨i, rfl⟩
    have hi : i.val ≤ fs.length - 1 := by lia
    have hii := hall i.val i.val (by simp) le_rfl hi
    have hget : F i.val = fs.get i :=
      List.getD_eq_getElem fs 0 i.isLt
    exact ⟨by simpa [hget] using hii.1, hnonneg _ (List.get_mem fs i)⟩
  · rw [isInterlacingSeq_iff_pairwise, List.pairwise_iff_get]
    intro i j hij
    have hi : i.val ≤ fs.length - 1 := by lia
    have hj : j.val ≤ fs.length - 1 := by lia
    have hij' := hall i.val j.val (by simp) hij.le hj
    have hgeti : F i.val = fs.get i :=
      List.getD_eq_getElem fs 0 i.isLt
    have hgetj : F j.val = fs.get j :=
      List.getD_eq_getElem fs 0 j.isLt
    simpa [hgeti, hgetj] using hij'

/-- Two nonnegative polynomials form an interlacing sequence when they strictly interlace. -/
private theorem isInterlacingSeqNonneg_pair {a b : ℝ[X]}
    (ha : HasNonnegCoeffs a) (hb : HasNonnegCoeffs b) (hab : StrictInterl a b) :
    IsInterlacingSeqNonneg [a, b] := by
  apply isInterlacingSeqNonneg_of_getD_chain (by simp)
  · simp_all
  · intro k hk
    simp at hk
    have : k = 0 := by lia
    simpa [this]
  · simpa

/-- A four-term strict chain with interlacing endpoints is an interlacing sequence. -/
private theorem isInterlacingSeqNonneg_four {a b c d : ℝ[X]}
    (ha : HasNonnegCoeffs a) (hb : HasNonnegCoeffs b)
    (hc : HasNonnegCoeffs c) (hd : HasNonnegCoeffs d)
    (hab : StrictInterl a b) (hbc : StrictInterl b c) (hcd : StrictInterl c d)
    (had : StrictInterl a d) : IsInterlacingSeqNonneg [a, b, c, d] := by
  apply isInterlacingSeqNonneg_of_getD_chain (by simp)
  · simp_all
  · intro k hk
    simp at hk
    interval_cases k <;> simpa
  · simpa

/-- A six-term strict chain with interlacing endpoints is an interlacing sequence. -/
private theorem isInterlacingSeqNonneg_six {a b c d e f : ℝ[X]}
    (ha : HasNonnegCoeffs a) (hb : HasNonnegCoeffs b)
    (hc : HasNonnegCoeffs c) (hd : HasNonnegCoeffs d)
    (he : HasNonnegCoeffs e) (hf : HasNonnegCoeffs f)
    (hab : StrictInterl a b) (hbc : StrictInterl b c) (hcd : StrictInterl c d)
    (hde : StrictInterl d e) (hef : StrictInterl e f) (haf : StrictInterl a f) :
    IsInterlacingSeqNonneg [a, b, c, d, e, f] := by
  apply isInterlacingSeqNonneg_of_getD_chain (by simp)
  · simp_all
  · intro k hk
    simp at hk
    interval_cases k <;> simpa
  · simpa

/-- An eight-term strict chain with interlacing endpoints is an interlacing sequence. -/
private theorem isInterlacingSeqNonneg_eight {a b c d e f g h : ℝ[X]}
    (ha : HasNonnegCoeffs a) (hb : HasNonnegCoeffs b)
    (hc : HasNonnegCoeffs c) (hd : HasNonnegCoeffs d)
    (he : HasNonnegCoeffs e) (hf : HasNonnegCoeffs f)
    (hg : HasNonnegCoeffs g) (hh : HasNonnegCoeffs h)
    (hab : StrictInterl a b) (hbc : StrictInterl b c) (hcd : StrictInterl c d)
    (hde : StrictInterl d e) (hef : StrictInterl e f) (hfg : StrictInterl f g)
    (hgh : StrictInterl g h) (hah : StrictInterl a h) :
    IsInterlacingSeqNonneg [a, b, c, d, e, f, g, h] := by
  apply isInterlacingSeqNonneg_of_getD_chain (by simp)
  · simp_all
  · intro k hk
    simp at hk
    interval_cases k <;> simpa
  · simpa

namespace BrandenVecchi

/-- Removing the zero terms from the abstract eight-term Chow chain leaves a strict chain. -/
private theorem filter_chow_chain_isInterlacingSeqNonneg
    {S f g q gr fr XS : ℝ[X]}
    (hSnn : HasNonnegCoeffs S) (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g) (hqnn : HasNonnegCoeffs q)
    (hgrnn : HasNonnegCoeffs gr) (hfrnn : HasNonnegCoeffs fr)
    (hXSnn : HasNonnegCoeffs XS)
    (hSf0 : Interl S f) (hfg0 : Interl f g) (hgq0 : Interl g q)
    (hqgr0 : Interl q gr) (hgrfr0 : Interl gr fr) (hffr0 : Interl f fr)
    (hfrXS0 : Interl fr XS) (hSXS0 : Interl S XS) (hggr0 : Interl g gr)
    (hfr_ne : f ≠ 0 → fr ≠ 0) (hgr_ne : g ≠ 0 → gr ≠ 0)
    (hq_ne : g ≠ 0 → q ≠ 0) (hXS_ne : S ≠ 0 → XS ≠ 0)
    (hf_zero : f = 0 → S = 0 ∧ fr = 0 ∧ XS = 0)
    (hg_zero : g = 0 → q = 0 ∧ gr = 0)
    (hXS_zero : S = 0 → XS = 0) :
    IsInterlacingSeqNonneg ([S, f, g, q, q, gr, fr, XS].filter (· ≠ 0)) := by
  by_cases hf : f ≠ 0
  · have hfr := hfr_ne hf
    by_cases hg : g ≠ 0
    · have hgr := hgr_ne hg
      have hq := hq_ne hg
      have hfg := hfg0.toStrictInterl_of_ne hf hg
      have hgq := hgq0.toStrictInterl_of_ne hg hq
      have hqq := StrictInterl.refl hq hgq.2.1.2
      have hqgr := hqgr0.toStrictInterl_of_ne hq hgr
      have hgrfr := hgrfr0.toStrictInterl_of_ne hgr hfr
      by_cases hS : S ≠ 0
      · have hXS := hXS_ne hS
        have hfull := isInterlacingSeqNonneg_eight hSnn hfnn hgnn hqnn hqnn
          hgrnn hfrnn hXSnn (hSf0.toStrictInterl_of_ne hS hf) hfg hgq hqq hqgr
          hgrfr (hfrXS0.toStrictInterl_of_ne hfr hXS)
          (hSXS0.toStrictInterl_of_ne hS hXS)
        simpa [hf, hg, hq, hfr, hgr, hS, hXS] using hfull
      · have hS0 : S = 0 := not_ne_iff.mp hS
        have hXS0 := hXS_zero hS0
        have hmiddle := isInterlacingSeqNonneg_six hfnn hgnn hqnn hqnn hgrnn
          hfrnn hfg hgq hqq hqgr hgrfr (hffr0.toStrictInterl_of_ne hf hfr)
        simpa [hf, hg, hq, hfr, hgr, hS0, hXS0] using hmiddle
    · have hg0 : g = 0 := not_ne_iff.mp hg
      obtain ⟨hq0, hgr0⟩ := hg_zero hg0
      by_cases hS : S ≠ 0
      · have hXS := hXS_ne hS
        have hends := isInterlacingSeqNonneg_four hSnn hfnn hfrnn hXSnn
          (hSf0.toStrictInterl_of_ne hS hf) (hffr0.toStrictInterl_of_ne hf hfr)
          (hfrXS0.toStrictInterl_of_ne hfr hXS) (hSXS0.toStrictInterl_of_ne hS hXS)
        simpa [hf, hfr, hg0, hq0, hgr0, hS, hXS] using hends
      · have hS0 : S = 0 := not_ne_iff.mp hS
        have hXS0 := hXS_zero hS0
        have hends := isInterlacingSeqNonneg_pair hfnn hfrnn
          (hffr0.toStrictInterl_of_ne hf hfr)
        simpa [hf, hfr, hg0, hq0, hgr0, hS0, hXS0] using hends
  · have hf0 : f = 0 := not_ne_iff.mp hf
    obtain ⟨hS0, hfr0, hXS0⟩ := hf_zero hf0
    by_cases hg : g ≠ 0
    · have hgr := hgr_ne hg
      have hq := hq_ne hg
      have hgq := hgq0.toStrictInterl_of_ne hg hq
      have hqgr := hqgr0.toStrictInterl_of_ne hq hgr
      have hmiddle := isInterlacingSeqNonneg_four hgnn hqnn hqnn hgrnn hgq
        (StrictInterl.refl hq hgq.2.1.2) hqgr (hggr0.toStrictInterl_of_ne hg hgr)
      simpa [hf0, hS0, hfr0, hXS0, hg, hq, hgr] using hmiddle
    · have hg0 : g = 0 := not_ne_iff.mp hg
      obtain ⟨hq0, hgr0⟩ := hg_zero hg0
      simp [hf0, hS0, hfr0, hXS0, hg0, hq0, hgr0, IsInterlacingSeqNonneg,
        IsInterlacingSeq]

/-- The four original pair relations read from a two-term reflection closure. -/
private theorem IsReflectionInterlacingSeq.extension_pair_relations
    {n : ℕ} {f g : ℝ[X]} (h : IsReflectionInterlacingSeq n [f, g]) :
    Interl f g ∧ Interl g (g.reflect n) ∧ Interl (g.reflect n) (f.reflect n) ∧
      Interl f (f.reflect n) := by
  have hseq := h.closedSequence.interlacingSeq0
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [reflectionClosure] using
      hseq.interl
        (i := (⟨0, by simp [reflectionClosure]⟩ : Fin (reflectionClosure n [f, g]).length))
        (j := (⟨1, by simp [reflectionClosure]⟩ : Fin (reflectionClosure n [f, g]).length))
        (by simp)
  · simpa [reflectionClosure] using
      hseq.interl
        (i := (⟨1, by simp [reflectionClosure]⟩ : Fin (reflectionClosure n [f, g]).length))
        (j := (⟨2, by simp [reflectionClosure]⟩ : Fin (reflectionClosure n [f, g]).length))
        (by simp)
  · simpa [reflectionClosure] using
      hseq.interl
        (i := (⟨2, by simp [reflectionClosure]⟩ : Fin (reflectionClosure n [f, g]).length))
        (j := (⟨3, by simp [reflectionClosure]⟩ : Fin (reflectionClosure n [f, g]).length))
        (by simp)
  · simpa [reflectionClosure] using
      hseq.interl
        (i := (⟨0, by simp [reflectionClosure]⟩ : Fin (reflectionClosure n [f, g]).length))
        (j := (⟨3, by simp [reflectionClosure]⟩ : Fin (reflectionClosure n [f, g]).length))
        (by simp)

/-- The two quotient relations supplied by a singleton reflection-interlacing
sequence.  This is the zero-aware form of the two uses of Lemma 4.11 in the
proof of Branden--Vecchi, Lemma 4.12. -/
theorem IsReflectionInterlacingSeq.chowS_nonnegCoeffs_and_interl_self_reflect
    {n : ℕ} {f : ℝ[X]} (h : IsReflectionInterlacingSeq n [f]) :
    HasNonnegCoeffs (chowS n f) ∧
      Interl (chowS n f) f ∧ Interl (chowS n f) (f.reflect n) := by
  let S : ℝ[X] := chowS n f
  let fr : ℝ[X] := f.reflect n
  have hdegree : f.natDegree ≤ n := h.natDegree_le (by simp)
  have hfnn : HasNonnegCoeffs f :=
    h.closedSequence.nonnegCoeffs f (by simp [reflectionClosure])
  have hfrnn : HasNonnegCoeffs fr := by
    simpa [fr] using hfnn.reflect n
  have hfref0 : Interl f fr := by
    simpa [fr, reflectionClosure] using
      h.closedSequence.interlacingSeq0.interl
        (i := (⟨0, by simp [reflectionClosure]⟩ :
          Fin (reflectionClosure n [f]).length))
        (j := (⟨1, by simp [reflectionClosure]⟩ :
          Fin (reflectionClosure n [f]).length)) (by simp)
  by_cases hS_ne : S ≠ 0
  · have hf_ne : f ≠ 0 := by
      intro hf_zero
      subst f
      exact hS_ne (by simp [S, chowS])
    have hfr_ne : fr ≠ 0 := by
      intro hfr_zero
      exact hf_ne ((reflect_eq_zero_iff (f := f) (N := n)).mp
        (by simpa [fr] using hfr_zero))
    have hfref : StrictInterl f fr := hfref0.toStrictInterl_of_ne hf_ne hfr_ne
    have hSf := chowS_nonnegCoeffs_and_strictInterl_of_triple hdegree hfnn hfnn
      (StrictInterl.refl hf_ne hfref.1.2) hfref hfref (by simpa [S] using hS_ne)
    have hSfr := chowS_nonnegCoeffs_and_strictInterl_of_triple hdegree hfnn hfrnn
      hfref (StrictInterl.refl hfr_ne hfref.2.1.2) hfref (by simpa [S] using hS_ne)
    exact ⟨by simpa [S] using hSf.1, hSf.2.toInterl, hSfr.2.toInterl⟩
  · have hS_zero : S = 0 := not_ne_iff.mp hS_ne
    exact ⟨by simpa [S, hS_zero] using hasNonnegCoeffs_zero,
      by simpa [S, hS_zero] using interl_zero_left f,
      by simpa [S, fr, hS_zero] using interl_zero_left fr⟩

/-- The right endpoint in Lemma 4.12 is fixed by reflection at the original
bound. -/
theorem reflect_X_mul_chowS_add_self {n : ℕ} {g : ℝ[X]}
    (hdegree : g.natDegree ≤ n) :
    (X * chowS n g + g).reflect n = X * chowS n g + g := by
  have hq : X * chowS n g + g = chowS n g + g.reflect n := by
    have hfactor := X_sub_one_mul_chowS n g hdegree
    calc
      X * chowS n g + g =
          chowS n g + ((X - 1) * chowS n g + g) := by ring
      _ = chowS n g + g.reflect n := by rw [hfactor]; ring
  calc
    (X * chowS n g + g).reflect n =
        (chowS n g + g.reflect n).reflect n := congrArg (reflect n) hq
    _ = (chowS n g).reflect n + (g.reflect n).reflect n := reflect_add _ _ _
    _ = X * chowS n g + g := by rw [reflect_chowS n g hdegree, reflect_reflect]

/-- The nonzero terms in the seven-edge Chow extension form a strict interlacing sequence. -/
private theorem IsReflectionInterlacingSeq.chowSExtension_filter_ne_zero
    {n : ℕ} {f g : ℝ[X]} (h : IsReflectionInterlacingSeq n [f, g]) :
    IsInterlacingSeqNonneg
      ([chowS n f, f, g, X * chowS n g + g, X * chowS n g + g,
        g.reflect n, f.reflect n, X * chowS n f].filter (· ≠ 0)) := by
  let S := chowS n f
  let T := chowS n g
  let fr := f.reflect n
  let gr := g.reflect n
  let q := X * T + g
  let XS := X * S
  have hfdegree : f.natDegree ≤ n := h.natDegree_le (by simp)
  have hgdegree : g.natDegree ≤ n := h.natDegree_le (by simp)
  have hfnn := h.closedSequence.nonnegCoeffs f (by simp [reflectionClosure])
  have hgnn := h.closedSequence.nonnegCoeffs g (by simp [reflectionClosure])
  have hfrnn : HasNonnegCoeffs fr := by simpa [fr] using hfnn.reflect n
  have hgrnn : HasNonnegCoeffs gr := by simpa [gr] using hgnn.reflect n
  obtain ⟨hfg0, hggr0, hgrfr0, hffr0⟩ := h.extension_pair_relations
  have hSpack := IsReflectionInterlacingSeq.chowS_nonnegCoeffs_and_interl_self_reflect
    (h.sublist (by simp) : IsReflectionInterlacingSeq n [f])
  have hTpack := IsReflectionInterlacingSeq.chowS_nonnegCoeffs_and_interl_self_reflect
    (h.sublist (by simp) : IsReflectionInterlacingSeq n [g])
  have hSnn : HasNonnegCoeffs S := by simpa [S] using hSpack.1
  have hTnn : HasNonnegCoeffs T := by simpa [T] using hTpack.1
  have hSf0 : Interl S f := by simpa [S] using hSpack.2.1
  have hSfr0 : Interl S fr := by simpa [S, fr] using hSpack.2.2
  have hTg0 : Interl T g := by simpa [T] using hTpack.2.1
  have hTgr0 : Interl T gr := by simpa [T, gr] using hTpack.2.2
  have hXTnn := hTnn.X_mul
  have hXSnn : HasNonnegCoeffs XS := by simpa [XS] using hSnn.X_mul
  have hqnn : HasNonnegCoeffs q := by simpa [q] using hXTnn.add hgnn
  have hq_alt : q = T + gr := by
    have hfactor := X_sub_one_mul_chowS n g hgdegree
    dsimp [q, T, gr]
    rw [show X * chowS n g + g =
      chowS n g + ((X - 1) * chowS n g + g) by ring, hfactor]
    ring
  have hgq0 : Interl g q := by
    simpa [q] using interl_add_right_of_common_left_of_nonneg
      (interl_mul_X_of_interl hTg0 hTnn hgnn) (Interl.refl fun hg ↦
        h.closedSequence.splits (by simp [reflectionClosure]) hg) hXTnn hgnn
  have hqgr0 : Interl q gr := by
    rw [hq_alt]
    exact interl_add_left_of_common_right_of_nonneg hTgr0
      (Interl.refl fun hgr ↦ h.closedSequence.splits
        (by simp [gr, reflectionClosure]) hgr) hTnn hgrnn
  have hfrXS0 : Interl fr XS := by
    simpa [XS] using interl_mul_X_of_interl hSfr0 hSnn hfrnn
  have hSreal : S ≠ 0 → S.Splits := fun hS ↦
    (hSf0.toStrictInterl_of_ne hS fun hf ↦ hS (by simp [S, hf, chowS])).1.2
  have hSXS0 : Interl S XS := by
    simpa [XS] using interl_mul_X_of_interl (Interl.refl hSreal) hSnn hSnn
  apply filter_chow_chain_isInterlacingSeqNonneg hSnn hfnn hgnn hqnn hgrnn hfrnn
    hXSnn hSf0 hfg0 hgq0 hqgr0 hgrfr0 hffr0 hfrXS0 hSXS0 hggr0
  · exact fun hf hfr ↦ hf ((reflect_eq_zero_iff (N := n) (f := f)).mp
      (by simpa [fr] using hfr))
  · exact fun hg hgr ↦ hg ((reflect_eq_zero_iff (N := n) (f := g)).mp
      (by simpa [gr] using hgr))
  · exact fun hg ↦ add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero hXTnn hgnn hg
  · simp [XS]
  · intro hf
    subst f
    simp [S, fr, XS, chowS]
  · intro hg
    subst g
    simp [q, T, gr, chowS]
  · intro hS
    simp [XS, hS]

/-- Every term of the explicit Chow extension has nonnegative coefficients. -/
private theorem IsReflectionInterlacingSeq.chowSExtension_nonnegCoeffs
    {n : ℕ} {f g : ℝ[X]} (h : IsReflectionInterlacingSeq n [f, g]) :
    ∀ p ∈ [chowS n f, f, g, X * chowS n g + g, X * chowS n g + g,
      g.reflect n, f.reflect n, X * chowS n f], HasNonnegCoeffs p := by
  have hfnn := h.closedSequence.nonnegCoeffs f (by simp [reflectionClosure])
  have hgnn := h.closedSequence.nonnegCoeffs g (by simp [reflectionClosure])
  have hSnn :=
    (IsReflectionInterlacingSeq.chowS_nonnegCoeffs_and_interl_self_reflect
      (h.sublist (by simp) : IsReflectionInterlacingSeq n [f])).1
  have hTnn :=
    (IsReflectionInterlacingSeq.chowS_nonnegCoeffs_and_interl_self_reflect
      (h.sublist (by simp) : IsReflectionInterlacingSeq n [g])).1
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hSnn
  · exact hfnn
  · exact hgnn
  · exact hTnn.X_mul.add hgnn
  · exact hTnn.X_mul.add hgnn
  · exact hgnn.reflect n
  · exact hfnn.reflect n
  · exact hSnn.X_mul

/-- Every polynomial in the four-term Chow extension has degree at most the reflection bound. -/
private theorem IsReflectionInterlacingSeq.chowSExtension_natDegree_le
    {n : ℕ} {f g : ℝ[X]} (h : IsReflectionInterlacingSeq n [f, g]) :
    ∀ p ∈ [chowS n f, f, g, X * chowS n g + g], p.natDegree ≤ n := by
  have hfdegree : f.natDegree ≤ n := h.natDegree_le (by simp)
  have hgdegree : g.natDegree ≤ n := h.natDegree_le (by simp)
  have hSdegree := natDegree_chowS_le n f hfdegree
  have hTdegree := natDegree_chowS_le n g hgdegree
  have hgrdegree : (g.reflect n).natDegree ≤ n :=
    natDegree_reflect_le.trans (max_le le_rfl hgdegree)
  have hfactor := X_sub_one_mul_chowS n g hgdegree
  have hq : X * chowS n g + g = chowS n g + g.reflect n := by
    calc
      X * chowS n g + g =
          chowS n g + ((X - 1) * chowS n g + g) := by ring
      _ = chowS n g + g.reflect n := by rw [hfactor]; ring
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact hSdegree
  · exact hfdegree
  · exact hgdegree
  · rw [hq]
    exact (natDegree_add_le _ _).trans (max_le hTdegree hgrdegree)

/-- The reflected Chow extension is a zero-aware nonnegative interlacing sequence. -/
private theorem IsReflectionInterlacingSeq.chowSExtension_closedSequence
    {n : ℕ} {f g : ℝ[X]} (h : IsReflectionInterlacingSeq n [f, g]) :
    IsInterlacingSeq0NonnegRealRooted
      (reflectionClosure n [chowS n f, f, g, X * chowS n g + g]) := by
  let closed := [chowS n f, f, g, X * chowS n g + g, X * chowS n g + g,
    g.reflect n, f.reflect n, X * chowS n f]
  have hstrict : IsInterlacingSeqNonneg (closed.filter (· ≠ 0)) := by
    simpa [closed] using h.chowSExtension_filter_ne_zero
  have hnonneg : ∀ p ∈ closed, HasNonnegCoeffs p := by
    simpa [closed] using h.chowSExtension_nonnegCoeffs
  have hreal : ∀ p ∈ closed, p ≠ 0 → p.Splits := by
    intro p hp hp_ne
    exact hstrict.splits (by simp [closed, hp, hp_ne])
  have hclosed := isInterlacingSeq0NonnegRealRooted_of_filter_ne_zero
    hstrict hnonneg hreal
  have hfdegree : f.natDegree ≤ n := h.natDegree_le (by simp)
  have hgdegree : g.natDegree ≤ n := h.natDegree_le (by simp)
  have hrefS : (chowS n f).reflect n = X * chowS n f := reflect_chowS n f hfdegree
  have hrefq : (X * chowS n g + g).reflect n = X * chowS n g + g :=
    reflect_X_mul_chowS_add_self hgdegree
  have hclosure :
      reflectionClosure n [chowS n f, f, g, X * chowS n g + g] = closed := by
    simp [reflectionClosure, closed, hrefS, hrefq]
  exact hclosure.symm ▸ hclosed

/-- Branden--Vecchi, Lemma 4.12: adjoining the two Chow endpoints to a
two-member reflection-interlacing sequence preserves reflection interlacing.
The theorem is zero-aware, so either Chow quotient is allowed to vanish. -/
theorem IsReflectionInterlacingSeq.chowSExtension
    {n : ℕ} {f g : ℝ[X]} (h : IsReflectionInterlacingSeq n [f, g]) :
    IsReflectionInterlacingSeq n
      [chowS n f, f, g, X * chowS n g + g] := by
  exact ⟨h.chowSExtension_natDegree_le, h.chowSExtension_closedSequence⟩

end BrandenVecchi

end RealRooted
