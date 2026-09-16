import RealRooted.BrandenVecchi.ChowInterlacingQuotient
import RealRooted.CommonInterleaver.RootDesc

/-!
# The four-term Chow reflection-interlacing extension

This file proves Branden--Vecchi, Lemma 4.12, in the project's zero-aware
form.  The proof follows the source's seven-term chain.  The literal
`reflectionClosure` contains the self-reflected middle polynomial twice;
this harmless duplicate is retained so the result uses the canonical list
predicate.
-/

open Polynomial

noncomputable section

namespace RealRooted

private theorem prec0_refl_of_splits_or_zero {p : ℝ[X]}
    (hp : p ≠ 0 → p.Splits) : Prec0 p p := by
  by_cases hp_zero : p = 0
  · exact Or.inl hp_zero
  · exact (prec_refl hp_zero (hp hp_zero)).toPrec0

private theorem add_ne_zero_of_nonnegCoeffs_of_right_ne_zero
    {p q : ℝ[X]} (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q)
    (hq_ne : q ≠ 0) : p + q ≠ 0 := by
  let d : ℕ := q.natDegree
  have hp_coeff : 0 ≤ p.coeff d := hp d
  have hq_pos : 0 < q.coeff d := by
    have hq_lc : 0 < q.leadingCoeff := hq.pos_leadingCoeff hq_ne
    simpa [d] using hq_lc
  intro hsum_zero
  have hcoeff_zero : (p + q).coeff d = 0 := by simp [hsum_zero]
  rw [coeff_add] at hcoeff_zero
  linarith

private theorem pairwise_prec0_of_filter_ne_zero_pairwise_prec :
    ∀ fs : List ℝ[X], (fs.filter (· ≠ 0)).Pairwise Prec → fs.Pairwise Prec0
  | [], _ => by simp
  | f :: fs, h => by
      by_cases hf : f = 0
      · subst f
        constructor
        · exact fun _ _ => prec0_zero_left _
        · exact pairwise_prec0_of_filter_ne_zero_pairwise_prec fs (by simpa using h)
      · have h' : (f :: fs.filter (· ≠ 0)).Pairwise Prec := by
          simpa [List.filter_cons, hf] using h
        rcases List.pairwise_cons.mp h' with ⟨hhead, htail⟩
        apply List.pairwise_cons.2
        refine ⟨?_, pairwise_prec0_of_filter_ne_zero_pairwise_prec fs htail⟩
        intro g hg
        by_cases hg_zero : g = 0
        · exact Or.inr (Or.inl hg_zero)
        · exact (hhead g (by simp [hg, hg_zero])).toPrec0

private theorem isInterlacingSeq0NonnegRealRooted_of_filter_ne_zero
    {fs : List ℝ[X]} (hstrict : IsInterlacingSeqNonneg (fs.filter (· ≠ 0)))
    (hnonneg : ∀ p ∈ fs, HasNonnegCoeffs p)
    (hreal : ∀ p ∈ fs, p ≠ 0 → p.Splits) :
    IsInterlacingSeq0NonnegRealRooted fs := by
  refine ⟨⟨?_, hnonneg⟩, ?_⟩
  · rw [isInterlacingSeq0_iff_pairwise]
    exact pairwise_prec0_of_filter_ne_zero_pairwise_prec fs
      (isInterlacingSeq_iff_pairwise.mp hstrict.2)
  · exact fun p hp hp_ne => ⟨hp_ne, hreal p hp hp_ne⟩

private theorem isInterlacingSeqNonneg_of_getD_chain
    {fs : List ℝ[X]} (hlen : 2 ≤ fs.length)
    (hnonneg : ∀ p ∈ fs, HasNonnegCoeffs p)
    (hcons : ∀ k, k < fs.length - 1 →
      Prec (fs.getD k 0) (fs.getD (k + 1) 0))
    (hend : Prec (fs.getD 0 0) (fs.getD (fs.length - 1) 0)) :
    IsInterlacingSeqNonneg fs := by
  let F : ℕ → ℝ[X] := fun k => fs.getD k 0
  have hall := prec_chain_of_consecutive_of_endpoint F 0 (fs.length - 1)
    (fun k _ hk => hcons k hk) hend
  refine ⟨?_, ?_⟩
  · intro p hp
    rcases List.get_of_mem hp with ⟨i, rfl⟩
    have hi : i.val ≤ fs.length - 1 := by lia
    have hii := hall i.val i.val (by simp) le_rfl hi
    have hget : F i.val = fs.get i := by
      exact List.getD_eq_getElem fs 0 i.isLt
    exact ⟨by simpa [hget] using hii.1, hnonneg _ (List.get_mem fs i)⟩
  · rw [isInterlacingSeq_iff_pairwise, List.pairwise_iff_get]
    intro i j hij
    have hi : i.val ≤ fs.length - 1 := by lia
    have hj : j.val ≤ fs.length - 1 := by lia
    have hij' := hall i.val j.val (by simp) hij.le hj
    have hgeti : F i.val = fs.get i := by
      exact List.getD_eq_getElem fs 0 i.isLt
    have hgetj : F j.val = fs.get j := by
      exact List.getD_eq_getElem fs 0 j.isLt
    simpa [hgeti, hgetj] using hij'

namespace BrandenVecchi

/-- The two quotient relations supplied by a singleton reflection-interlacing
sequence.  This is the zero-aware form of the two uses of Lemma 4.11 in the
proof of Branden--Vecchi, Lemma 4.12. -/
theorem IsReflectionInterlacingSeq.chowS_nonnegCoeffs_and_prec0_self_reflect
    {n : ℕ} {f : ℝ[X]} (h : IsReflectionInterlacingSeq n [f]) :
    HasNonnegCoeffs (chowS n f) ∧
      Prec0 (chowS n f) f ∧ Prec0 (chowS n f) (f.reflect n) := by
  let S : ℝ[X] := chowS n f
  let fr : ℝ[X] := f.reflect n
  have hdegree : f.natDegree ≤ n := h.natDegree_le (by simp)
  have hfnn : HasNonnegCoeffs f :=
    h.closedSequence.nonnegCoeffs f (by simp [reflectionClosure])
  have hfrnn : HasNonnegCoeffs fr := by
    simpa [fr] using hfnn.reflect n
  have hfref0 : Prec0 f fr := by
    simpa [fr, reflectionClosure] using
      h.closedSequence.interlacingSeq0.prec0
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
    have hfref : Prec f fr := hfref0.toPrec_of_ne hf_ne hfr_ne
    have hSf := chowS_nonnegCoeffs_and_prec_of_triple hdegree hfnn hfnn
      (prec_refl hf_ne hfref.1.2) hfref hfref (by simpa [S] using hS_ne)
    have hSfr := chowS_nonnegCoeffs_and_prec_of_triple hdegree hfnn hfrnn
      hfref (prec_refl hfr_ne hfref.2.1.2) hfref (by simpa [S] using hS_ne)
    exact ⟨by simpa [S] using hSf.1, hSf.2.toPrec0, hSfr.2.toPrec0⟩
  · have hS_zero : S = 0 := not_ne_iff.mp hS_ne
    exact ⟨by simpa [S, hS_zero] using hasNonnegCoeffs_zero,
      by simpa [S, hS_zero] using prec0_zero_left f,
      by simpa [S, fr, hS_zero] using prec0_zero_left fr⟩

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

/-- Branden--Vecchi, Lemma 4.12: adjoining the two Chow endpoints to a
two-member reflection-interlacing sequence preserves reflection interlacing.
The theorem is zero-aware, so either Chow quotient is allowed to vanish. -/
theorem IsReflectionInterlacingSeq.chowSExtension
    {n : ℕ} {f g : ℝ[X]} (h : IsReflectionInterlacingSeq n [f, g]) :
    IsReflectionInterlacingSeq n
      [chowS n f, f, g, X * chowS n g + g] := by
  let S : ℝ[X] := chowS n f
  let T : ℝ[X] := chowS n g
  let fr : ℝ[X] := f.reflect n
  let gr : ℝ[X] := g.reflect n
  let q : ℝ[X] := X * T + g
  let XS : ℝ[X] := X * S
  have hfdegree : f.natDegree ≤ n := h.natDegree_le (by simp)
  have hgdegree : g.natDegree ≤ n := h.natDegree_le (by simp)
  have hSdegree : S.natDegree ≤ n := by
    simpa [S] using natDegree_chowS_le n f hfdegree
  have hTdegree : T.natDegree ≤ n := by
    simpa [T] using natDegree_chowS_le n g hgdegree
  have hfrdegree : fr.natDegree ≤ n := by
    exact (by
      simpa [fr] using (natDegree_reflect_le (N := n) (p := f)).trans
        (max_le le_rfl hfdegree))
  have hgrdegree : gr.natDegree ≤ n := by
    exact (by
      simpa [gr] using (natDegree_reflect_le (N := n) (p := g)).trans
        (max_le le_rfl hgdegree))
  have hfnn : HasNonnegCoeffs f :=
    h.closedSequence.nonnegCoeffs f (by simp [reflectionClosure])
  have hgnn : HasNonnegCoeffs g :=
    h.closedSequence.nonnegCoeffs g (by simp [reflectionClosure])
  have hfrnn : HasNonnegCoeffs fr := by simpa [fr] using hfnn.reflect n
  have hgrnn : HasNonnegCoeffs gr := by simpa [gr] using hgnn.reflect n
  have hfreal : f ≠ 0 → f.Splits := fun hf_ne =>
    h.closedSequence.splits (by simp [reflectionClosure]) hf_ne
  have hgreal : g ≠ 0 → g.Splits := fun hg_ne =>
    h.closedSequence.splits (by simp [reflectionClosure]) hg_ne
  have hfrreal : fr ≠ 0 → fr.Splits := fun hfr_ne =>
    h.closedSequence.splits (by simp [fr, reflectionClosure]) hfr_ne
  have hgrreal : gr ≠ 0 → gr.Splits := fun hgr_ne =>
    h.closedSequence.splits (by simp [gr, reflectionClosure]) hgr_ne
  have hfg0 : Prec0 f g := by
    simpa [reflectionClosure] using
      h.closedSequence.interlacingSeq0.prec0
        (i := (⟨0, by simp [reflectionClosure]⟩ :
          Fin (reflectionClosure n [f, g]).length))
        (j := (⟨1, by simp [reflectionClosure]⟩ :
          Fin (reflectionClosure n [f, g]).length)) (by simp)
  have hggr0 : Prec0 g gr := by
    simpa [gr, reflectionClosure] using
      h.closedSequence.interlacingSeq0.prec0
        (i := (⟨1, by simp [reflectionClosure]⟩ :
          Fin (reflectionClosure n [f, g]).length))
        (j := (⟨2, by simp [reflectionClosure]⟩ :
          Fin (reflectionClosure n [f, g]).length)) (by simp)
  have hgrfr0 : Prec0 gr fr := by
    simpa [fr, gr, reflectionClosure] using
      h.closedSequence.interlacingSeq0.prec0
        (i := (⟨2, by simp [reflectionClosure]⟩ :
          Fin (reflectionClosure n [f, g]).length))
        (j := (⟨3, by simp [reflectionClosure]⟩ :
          Fin (reflectionClosure n [f, g]).length)) (by simp)
  have hffr0 : Prec0 f fr := by
    simpa [fr, reflectionClosure] using
      h.closedSequence.interlacingSeq0.prec0
        (i := (⟨0, by simp [reflectionClosure]⟩ :
          Fin (reflectionClosure n [f, g]).length))
        (j := (⟨3, by simp [reflectionClosure]⟩ :
          Fin (reflectionClosure n [f, g]).length)) (by simp)
  have hf_single : IsReflectionInterlacingSeq n [f] :=
    h.sublist (by simp)
  have hg_single : IsReflectionInterlacingSeq n [g] :=
    h.sublist (by simp)
  have hSpack := hf_single.chowS_nonnegCoeffs_and_prec0_self_reflect
  have hTpack := hg_single.chowS_nonnegCoeffs_and_prec0_self_reflect
  have hSnn : HasNonnegCoeffs S := by simpa [S] using hSpack.1
  have hTnn : HasNonnegCoeffs T := by simpa [T] using hTpack.1
  have hSf0 : Prec0 S f := by simpa [S] using hSpack.2.1
  have hSfr0 : Prec0 S fr := by simpa [S, fr] using hSpack.2.2
  have hTg0 : Prec0 T g := by simpa [T] using hTpack.2.1
  have hTgr0 : Prec0 T gr := by simpa [T, gr] using hTpack.2.2
  have hXTnn : HasNonnegCoeffs (X * T) := hTnn.X_mul
  have hXSnn : HasNonnegCoeffs XS := by simpa [XS] using hSnn.X_mul
  have hqnn : HasNonnegCoeffs q := by
    simpa [q] using hXTnn.add hgnn
  have hq_alt : q = T + gr := by
    have hfactor := X_sub_one_mul_chowS n g hgdegree
    dsimp [q, T, gr]
    calc
      X * chowS n g + g =
          chowS n g + ((X - 1) * chowS n g + g) := by ring
      _ = chowS n g + g.reflect n := by rw [hfactor]; ring
  have hqdegree : q.natDegree ≤ n := by
    rw [hq_alt]
    exact (natDegree_add_le T gr).trans (max_le hTdegree hgrdegree)
  have hgq0 : Prec0 g q := by
    have hgXT0 := prec0_mul_X_of_prec0 hTg0 hTnn hgnn
    have hgg0 := prec0_refl_of_splits_or_zero hgreal
    simpa [q] using
      prec0_add_right_of_common_left_of_nonneg hgXT0 hgg0 hXTnn hgnn
  have hqgr0 : Prec0 q gr := by
    have hgrgr0 := prec0_refl_of_splits_or_zero hgrreal
    rw [hq_alt]
    exact prec0_add_left_of_common_right_of_nonneg hTgr0 hgrgr0 hTnn hgrnn
  have hfrXS0 : Prec0 fr XS := by
    simpa [XS] using prec0_mul_X_of_prec0 hSfr0 hSnn hfrnn
  have hSreal : S ≠ 0 → S.Splits := by
    intro hS_ne
    have hf_ne : f ≠ 0 := by
      intro hf_zero
      subst f
      exact hS_ne (by simp [S, chowS])
    exact (hSf0.toPrec_of_ne hS_ne hf_ne).1.2
  have hSXS0 : Prec0 S XS := by
    have hSS0 := prec0_refl_of_splits_or_zero hSreal
    simpa [XS] using prec0_mul_X_of_prec0 hSS0 hSnn hSnn
  have hqreal : q ≠ 0 → q.Splits := by
    intro hq_ne
    have hg_ne : g ≠ 0 := by
      intro hg_zero
      subst g
      exact hq_ne (by simp [q, T, chowS])
    exact (hgq0.toPrec_of_ne hg_ne hq_ne).2.1.2
  have hXSreal : XS ≠ 0 → XS.Splits := by
    intro hXS_ne
    have hS_ne : S ≠ 0 := fun hS_zero => hXS_ne (by simp [XS, hS_zero])
    exact (isRealRooted_X_mul hS_ne (hSreal hS_ne)).2
  let closed : List ℝ[X] := [S, f, g, q, q, gr, fr, XS]
  have hclosed_nonneg : ∀ p ∈ closed, HasNonnegCoeffs p := by
    intro p hp
    simp only [closed, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hSnn
    · exact hfnn
    · exact hgnn
    · exact hqnn
    · exact hqnn
    · exact hgrnn
    · exact hfrnn
    · exact hXSnn
  have hclosed_real : ∀ p ∈ closed, p ≠ 0 → p.Splits := by
    intro p hp
    simp only [closed, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hSreal
    · exact hfreal
    · exact hgreal
    · exact hqreal
    · exact hqreal
    · exact hgrreal
    · exact hfrreal
    · exact hXSreal
  have hstrict : IsInterlacingSeqNonneg (closed.filter (· ≠ 0)) := by
    by_cases hf_ne : f ≠ 0
    · have hfr_ne : fr ≠ 0 := by
        intro hfr_zero
        exact hf_ne ((reflect_eq_zero_iff (f := f) (N := n)).mp
          (by simpa [fr] using hfr_zero))
      by_cases hg_ne : g ≠ 0
      · have hgr_ne : gr ≠ 0 := by
          intro hgr_zero
          exact hg_ne ((reflect_eq_zero_iff (f := g) (N := n)).mp
            (by simpa [gr] using hgr_zero))
        have hq_ne : q ≠ 0 := by
          exact add_ne_zero_of_nonnegCoeffs_of_right_ne_zero hXTnn hgnn hg_ne
        have hfg := hfg0.toPrec_of_ne hf_ne hg_ne
        have hgq := hgq0.toPrec_of_ne hg_ne hq_ne
        have hqq := prec_refl hq_ne (hqreal hq_ne)
        have hqgr := hqgr0.toPrec_of_ne hq_ne hgr_ne
        have hgrfr := hgrfr0.toPrec_of_ne hgr_ne hfr_ne
        have hffr := hffr0.toPrec_of_ne hf_ne hfr_ne
        by_cases hS_ne : S ≠ 0
        · have hXS_ne : XS ≠ 0 := by simp [XS, hS_ne]
          have hSf := hSf0.toPrec_of_ne hS_ne hf_ne
          have hfrXS := hfrXS0.toPrec_of_ne hfr_ne hXS_ne
          have hSXS := hSXS0.toPrec_of_ne hS_ne hXS_ne
          have hfull : IsInterlacingSeqNonneg [S, f, g, q, q, gr, fr, XS] := by
            apply isInterlacingSeqNonneg_of_getD_chain (by simp)
            · intro p hp
              exact hclosed_nonneg p (by simpa [closed] using hp)
            · intro k hk
              simp at hk
              interval_cases k
              · simpa using hSf
              · simpa using hfg
              · simpa using hgq
              · simpa using hqq
              · simpa using hqgr
              · simpa using hgrfr
              · simpa using hfrXS
            · simpa using hSXS
          simpa [closed, hf_ne, hg_ne, hq_ne, hfr_ne, hgr_ne, hS_ne, hXS_ne]
            using hfull
        · have hS_zero : S = 0 := not_ne_iff.mp hS_ne
          have hXS_zero : XS = 0 := by simp [XS, hS_zero]
          have hmiddle : IsInterlacingSeqNonneg [f, g, q, q, gr, fr] := by
            apply isInterlacingSeqNonneg_of_getD_chain (by simp)
            · intro p hp
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
              rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
              · exact hfnn
              · exact hgnn
              · exact hqnn
              · exact hqnn
              · exact hgrnn
              · exact hfrnn
            · intro k hk
              simp at hk
              interval_cases k
              · simpa using hfg
              · simpa using hgq
              · simpa using hqq
              · simpa using hqgr
              · simpa using hgrfr
            · simpa using hffr
          simpa [closed, hf_ne, hg_ne, hq_ne, hfr_ne, hgr_ne, hS_zero,
            hXS_zero] using hmiddle
      · have hg_zero : g = 0 := not_ne_iff.mp hg_ne
        have hgr_zero : gr = 0 := by simp [gr, hg_zero]
        have hq_zero : q = 0 := by simp [q, T, hg_zero, chowS]
        have hffr := hffr0.toPrec_of_ne hf_ne hfr_ne
        by_cases hS_ne : S ≠ 0
        · have hXS_ne : XS ≠ 0 := by simp [XS, hS_ne]
          have hSf := hSf0.toPrec_of_ne hS_ne hf_ne
          have hfrXS := hfrXS0.toPrec_of_ne hfr_ne hXS_ne
          have hSXS := hSXS0.toPrec_of_ne hS_ne hXS_ne
          have hends : IsInterlacingSeqNonneg [S, f, fr, XS] := by
            apply isInterlacingSeqNonneg_of_getD_chain (by simp)
            · intro p hp
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
              rcases hp with rfl | rfl | rfl | rfl
              · exact hSnn
              · exact hfnn
              · exact hfrnn
              · exact hXSnn
            · intro k hk
              simp at hk
              interval_cases k
              · simpa using hSf
              · simpa using hffr
              · simpa using hfrXS
            · simpa using hSXS
          simpa [closed, hf_ne, hfr_ne, hS_ne, hXS_ne, hg_zero, hgr_zero,
            hq_zero] using hends
        · have hS_zero : S = 0 := not_ne_iff.mp hS_ne
          have hXS_zero : XS = 0 := by simp [XS, hS_zero]
          have hends : IsInterlacingSeqNonneg [f, fr] := by
            apply isInterlacingSeqNonneg_of_getD_chain (by simp)
            · intro p hp
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
              rcases hp with rfl | rfl
              · exact hfnn
              · exact hfrnn
            · intro k hk
              simp at hk
              have hk_zero : k = 0 := by lia
              subst k
              simpa using hffr
            · simpa using hffr
          simpa [closed, hf_ne, hfr_ne, hg_zero, hgr_zero, hq_zero, hS_zero,
            hXS_zero] using hends
    · have hf_zero : f = 0 := not_ne_iff.mp hf_ne
      have hfr_zero : fr = 0 := by simp [fr, hf_zero]
      have hS_zero : S = 0 := by simp [S, hf_zero, chowS]
      have hXS_zero : XS = 0 := by simp [XS, hS_zero]
      by_cases hg_ne : g ≠ 0
      · have hgr_ne : gr ≠ 0 := by
          intro hgr_zero
          exact hg_ne ((reflect_eq_zero_iff (f := g) (N := n)).mp
            (by simpa [gr] using hgr_zero))
        have hq_ne : q ≠ 0 :=
          add_ne_zero_of_nonnegCoeffs_of_right_ne_zero hXTnn hgnn hg_ne
        have hgq := hgq0.toPrec_of_ne hg_ne hq_ne
        have hqq := prec_refl hq_ne (hqreal hq_ne)
        have hqgr := hqgr0.toPrec_of_ne hq_ne hgr_ne
        have hggr := hggr0.toPrec_of_ne hg_ne hgr_ne
        have hmiddle : IsInterlacingSeqNonneg [g, q, q, gr] := by
          apply isInterlacingSeqNonneg_of_getD_chain (by simp)
          · intro p hp
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
            rcases hp with rfl | rfl | rfl | rfl
            · exact hgnn
            · exact hqnn
            · exact hqnn
            · exact hgrnn
          · intro k hk
            simp at hk
            interval_cases k
            · simpa using hgq
            · simpa using hqq
            · simpa using hqgr
          · simpa using hggr
        simpa [closed, hf_zero, hfr_zero, hS_zero, hXS_zero, hg_ne, hgr_ne,
          hq_ne] using hmiddle
      · have hg_zero : g = 0 := not_ne_iff.mp hg_ne
        simp [closed, hf_zero, hg_zero, hfr_zero, hS_zero, hXS_zero, gr, q, T,
          chowS, IsInterlacingSeqNonneg, IsInterlacingSeq]
  have hclosed : IsInterlacingSeq0NonnegRealRooted closed :=
    isInterlacingSeq0NonnegRealRooted_of_filter_ne_zero
      hstrict hclosed_nonneg hclosed_real
  refine ⟨?_, ?_⟩
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact hSdegree
    · exact hfdegree
    · exact hgdegree
    · exact hqdegree
  · have hrefS : S.reflect n = XS := by
      simpa [S, XS] using reflect_chowS n f hfdegree
    have hrefq : q.reflect n = q := by
      simpa [q, T] using reflect_X_mul_chowS_add_self hgdegree
    have hclosure : reflectionClosure n [S, f, g, q] = closed := by
      simp [reflectionClosure, closed, hrefS, hrefq, fr, gr]
    simpa [S, T, q] using hclosure.symm ▸ hclosed

end BrandenVecchi

end RealRooted
