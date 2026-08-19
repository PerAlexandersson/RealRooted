import RealRooted.Basic
import RealRooted.DegreeDropReversal

/-!
# Degree-drop `divX` orientation for the right-zero branch

This file isolates the list-level degree-drop step behind the right-zero lead
branch in issue #42.  If `g.coeff 0 = 0`, then `g = X * g.divX`; when the
extra zero root is the rightmost root, a differ-by-one interlacing `Prec f g`
turns into a same-degree alternation `Prec (g.divX) f`.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Roots of a nonzero polynomial with zero constant coefficient are exactly
the roots of its `divX` quotient together with one extra root at `0`.

This is the standalone version of the same fact used in
`RealRooted.CommonInterleaverTwo`. -/
theorem roots_eq_zero_cons_divX_of_coeff_zero {f : ℝ[X]}
    (hf : f ≠ 0) (hf0 : f.coeff 0 = 0) :
    f.roots = 0 ::ₘ f.divX.roots := by
  have hX : f = X * f.divX := DegreeDropReversal.eq_X_mul_divX_of_coeff_zero hf0
  have hne : X * f.divX ≠ 0 := by grind
  conv_lhs => rw [hX]
  rw [Polynomial.roots_mul hne, Polynomial.roots_X, Multiset.singleton_add]

theorem roots_eq_zero_cons_divX_of_coeff_zero' {f : ℝ[X]}
    (hf : f ≠ 0) (hf0 : f.coeff 0 = 0) :
    f.roots = 0 ::ₘ f.divX.roots :=
  roots_eq_zero_cons_divX_of_coeff_zero hf hf0

/-- List-free additive root-count form of `roots_eq_zero_cons_divX_of_coeff_zero`. -/
lemma card_divX_roots_succ_eq_card_roots_of_coeff_zero {g : ℝ[X]}
    (hg : g ≠ 0) (hg0 : g.coeff 0 = 0) :
    Multiset.card g.divX.roots + 1 = Multiset.card g.roots := by
  rw [roots_eq_zero_cons_divX_of_coeff_zero hg hg0]
  simp

/-- Degree-keyed form of `card_divX_roots_succ_eq_card_roots_of_coeff_zero`. -/
lemma card_divX_roots_succ_eq_natDegree_of_coeff_zero {g : ℝ[X]}
    (hg : g ≠ 0) (hg0 : g.coeff 0 = 0) (hgs : g.Splits) :
    Multiset.card g.divX.roots + 1 = g.natDegree := by
  rw [card_divX_roots_succ_eq_card_roots_of_coeff_zero hg hg0,
    card_roots_of_splits hgs]

/-- Succ-degree form of `card_divX_roots_succ_eq_natDegree_of_coeff_zero`,
keyed to the lower-degree endpoint. -/
lemma card_divX_roots_eq_natDegree_of_succDegree_of_coeff_zero {f g : ℝ[X]}
    (hg : g ≠ 0) (hg0 : g.coeff 0 = 0) (hgs : g.Splits)
    (hdeg : g.natDegree = f.natDegree + 1) :
    Multiset.card g.divX.roots = f.natDegree := by
  have hcard := card_divX_roots_succ_eq_natDegree_of_coeff_zero hg hg0 hgs
  simp_all

/-- Root-list bookkeeping for the right-zero `divX` branch.

If a nonempty list `rs` enumerates the roots of a nonzero polynomial `g`,
`g.coeff 0 = 0`, and the last entry of `rs` is the zero root, then dropping
that final entry leaves exactly the roots of `g.divX`. -/
lemma divX_roots_eq_dropLast_of_coeff_zero {g : ℝ[X]} {rs : List ℝ}
    (hg : g ≠ 0) (hg0 : g.coeff 0 = 0)
    (hrs_eq : (↑rs : Multiset ℝ) = g.roots)
    (hrs_ne : rs ≠ [])
    (hlast : rs.getLast hrs_ne = 0) :
    (↑(rs.dropLast) : Multiset ℝ) = g.divX.roots := by
  have hsplit : rs.dropLast ++ [rs.getLast hrs_ne] = rs :=
    List.dropLast_append_getLast hrs_ne
  have e1 : (↑rs : Multiset ℝ) = (0 : ℝ) ::ₘ ↑(rs.dropLast) := by
    conv_lhs => rw [← hsplit]
    rw [hlast]
    simp
  have e2 : (↑rs : Multiset ℝ) = (0 : ℝ) ::ₘ g.divX.roots := by
    rw [hrs_eq, roots_eq_zero_cons_divX_of_coeff_zero hg hg0]
  rw [e1] at e2
  exact (Multiset.cons_inj_right (0 : ℝ)).mp e2

/-- Root-count form of `divX_roots_eq_dropLast_of_coeff_zero`. -/
lemma divX_rootCount_eq_length_pred_of_coeff_zero {g : ℝ[X]} {rs : List ℝ}
    (hg : g ≠ 0) (hg0 : g.coeff 0 = 0)
    (hrs_eq : (↑rs : Multiset ℝ) = g.roots)
    (hrs_ne : rs ≠ [])
    (hlast : rs.getLast hrs_ne = 0) :
    Multiset.card g.divX.roots = rs.length - 1 := by
  have hdivX_roots : (↑(rs.dropLast) : Multiset ℝ) = g.divX.roots :=
    divX_roots_eq_dropLast_of_coeff_zero hg hg0 hrs_eq hrs_ne hlast
  rw [← hdivX_roots, Multiset.coe_card, List.length_dropLast]

/-- Additive root-count form of `divX_rootCount_eq_length_pred_of_coeff_zero`.

This avoids downstream reasoning about truncated subtraction in the right-zero
degree-drop branch. -/
lemma divX_rootCount_succ_eq_length_of_coeff_zero {g : ℝ[X]} {rs : List ℝ}
    (hg : g ≠ 0) (hg0 : g.coeff 0 = 0)
    (hrs_eq : (↑rs : Multiset ℝ) = g.roots)
    (hrs_ne : rs ≠ [])
    (hlast : rs.getLast hrs_ne = 0) :
    Multiset.card g.divX.roots + 1 = rs.length := by
  rw [divX_rootCount_eq_length_pred_of_coeff_zero hg hg0 hrs_eq hrs_ne hlast]
  grind

/-- List-level factorization behind the right-zero degree drop.

For equal-length lists, `ss` interlaces the one-longer list `ts ++ [m]` exactly
when `ts` alternates with `ss` and the appended element `m` dominates every
entry of `ss`.  The domination clause is automatic in the forward direction:
the interlacing chain forces every `s ∈ ss` below the last entry `m`.

This single `Iff` packages the two directions of the right-zero degree drop that
were previously proved as separate one-directional helpers, removing the
duplication between the reduction `listAlternates_dropLast_of_listInterlaces`
and the reconstruction used in
`prec_of_prec_divX_left_of_hasNonnegCoeffs_coeff_zero`. -/
lemma listInterlaces_append_singleton_iff {m : ℝ} :
    ∀ {ss ts : List ℝ}, ss.length = ts.length →
      (ListInterlaces ss (ts ++ [m]) ↔
        ListAlternates ts ss ∧ ∀ s ∈ ss, s ≤ m) := by
  intro ss
  induction ss with
  | nil =>
      intro ts hlen
      cases ts with
      | nil => simp [ListInterlaces, ListAlternates]
      | cons _ _ => simp at hlen
  | cons s ss' ih =>
      intro ts hlen
      cases ts with
      | nil => simp at hlen
      | cons t ts' =>
          cases ts' with
          | nil =>
              cases ss' with
              | nil =>
                  simp only [List.nil_append, List.cons_append, List.mem_singleton]
                  constructor
                  · rintro ⟨hts, hsm, _⟩
                    exact ⟨⟨hts, by simp [ListInterlaces]⟩, by
                      simp_all⟩
                  · rintro ⟨⟨hts, _⟩, hsm⟩
                    exact ⟨hts, hsm s rfl, by simp [ListInterlaces]⟩
              | cons _ _ => simp at hlen
          | cons t₂ ts'' =>
              cases ss' with
              | nil => simp at hlen
              | cons s' ss'' =>
                  have hlen' : (s' :: ss'').length = (t₂ :: ts'').length := by grind
                  have hstep := ih (ts := t₂ :: ts'') hlen'
                  rw [List.cons_append, List.cons_append] at *
                  constructor
                  · rintro ⟨hts, hst₂, htail⟩
                    obtain ⟨halt_tail, hbound_tail⟩ := hstep.mp htail
                    refine ⟨⟨hts, hst₂, halt_tail⟩, ?_⟩
                    intro x hx
                    rcases List.mem_cons.mp hx with rfl | hx'
                    · have ht₂s' : t₂ ≤ s' := halt_tail.1
                      exact le_trans hst₂
                        (le_trans ht₂s' (hbound_tail s' (by simp)))
                    · grind
                  · rintro ⟨⟨hts, hst₂, halt_tail⟩, hbound⟩
                    refine ⟨hts, hst₂, ?_⟩
                    exact hstep.mpr
                      ⟨halt_tail, fun x hx => hbound x (by simp [hx])⟩

/-- Reconstruction wrapper for `listInterlaces_append_singleton_iff`.

For equal-length lists, if `ts` alternates with `ss` and the appended element
`m` dominates every entry of `ss`, then `ss` interlaces `ts ++ [m]`. -/
lemma listInterlaces_append_singleton_of_listAlternates {m : ℝ}
    {ss ts : List ℝ} (hlen : ss.length = ts.length)
    (halt : ListAlternates ts ss) (hbound : ∀ s ∈ ss, s ≤ m) :
    ListInterlaces ss (ts ++ [m]) :=
  (listInterlaces_append_singleton_iff hlen).mpr ⟨halt, hbound⟩

/-- Alternation wrapper for `listInterlaces_append_singleton_iff`.

For equal-length lists, if `ss` interlaces `ts ++ [m]`, then `ts` alternates
with `ss`. -/
lemma listAlternates_of_listInterlaces_append_singleton {m : ℝ}
    {ss ts : List ℝ} (hlen : ss.length = ts.length)
    (h : ListInterlaces ss (ts ++ [m])) :
    ListAlternates ts ss :=
  ((listInterlaces_append_singleton_iff hlen).mp h).1

/-- In a succ-degree right-zero configuration, `g.divX` has the same degree as
the lower-degree endpoint `f`. -/
lemma natDegree_divX_eq_of_succDegree {f g : ℝ[X]}
    (hdeg : g.natDegree = f.natDegree + 1) :
    g.divX.natDegree = f.natDegree := by
  rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one, hdeg, Nat.add_sub_cancel]

/-- In a right-zero succ-degree configuration, the degree and root count of
`g.divX` both align with the lower-degree endpoint `f`. -/
lemma natDegree_and_card_divX_roots_eq_natDegree_of_succDegree_of_coeff_zero
    {f g : ℝ[X]}
    (hg : g ≠ 0) (hg0 : g.coeff 0 = 0) (hg_split : g.Splits)
    (hdeg : g.natDegree = f.natDegree + 1) :
    g.divX.natDegree = f.natDegree ∧ Multiset.card g.divX.roots = f.natDegree :=
  ⟨natDegree_divX_eq_of_succDegree hdeg,
    card_divX_roots_eq_natDegree_of_succDegree_of_coeff_zero hg hg0 hg_split hdeg⟩

/-- Domination wrapper for `listInterlaces_append_singleton_iff`.

For equal-length lists, if `ss` interlaces `ts ++ [m]`, then `m` dominates
every entry of `ss`. -/
lemma forall_le_of_listInterlaces_append_singleton {m : ℝ} {ss ts : List ℝ}
    (hlen : ss.length = ts.length) (h : ListInterlaces ss (ts ++ [m])) :
    ∀ s ∈ ss, s ≤ m :=
  ((listInterlaces_append_singleton_iff hlen).mp h).2

/-- If `ss` interlaces the strictly longer list `rs`, then dropping the
rightmost element of `rs` leaves an equal-length pair that alternates. -/
lemma listAlternates_dropLast_of_listInterlaces {ss rs : List ℝ}
    (hlen : ss.length + 1 = rs.length) (h : ListInterlaces ss rs) :
    ListAlternates rs.dropLast ss := by
  have hrs_ne : rs ≠ [] := by grind
  have hsplit : rs.dropLast ++ [rs.getLast hrs_ne] = rs :=
    List.dropLast_append_getLast hrs_ne
  have hlen' : ss.length = rs.dropLast.length := by grind
  apply listAlternates_of_listInterlaces_append_singleton hlen'
  rw [hsplit]
  grind

/-- Right-zero degree-drop reduction at the `Prec` level.

In the succ-degree configuration `g.natDegree = f.natDegree + 1`, if `g` has
nonnegative coefficients and `g.coeff 0 = 0`, then a differ-by-one interlacing
`Prec f g` collapses, after removing the zero root of `g`, to the same-degree
alternation `Prec (g.divX) f`. -/
theorem prec_divX_left_of_prec_of_hasNonnegCoeffs_coeff_zero
    {f g : ℝ[X]}
    (hprec : Prec f g)
    (hgnn : HasNonnegCoeffs g)
    (hg0 : g.coeff 0 = 0)
    (hdeg : g.natDegree = f.natDegree + 1) :
    Prec (g.divX) f := by
  obtain ⟨hf, hg, ss, rs, hss_sorted, hrs_sorted, hss_eq, hrs_eq, hshape⟩ := hprec
  have hss_len : ss.length = f.natDegree := by
    rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hf.2]
  have hrs_len : rs.length = g.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hg.2]
  have hlen1 : ss.length + 1 = rs.length := by simp_all
  have hInter : ListInterlaces ss rs := by simp_all
  have hrs_ne : rs ≠ [] := by grind
  set m := rs.getLast hrs_ne with hm
  have hm_mem : m ∈ rs := List.getLast_mem hrs_ne
  have hm_root : m ∈ g.roots := by
    rw [← hrs_eq]
    exact Multiset.mem_coe.mpr hm_mem
  have hm_nonpos : m ≤ 0 := roots_nonpos_of_hasNonnegCoeffs hgnn m hm_root
  have h0_root : (0 : ℝ) ∈ g.roots := by
    rw [Polynomial.mem_roots']
    refine ⟨hg.1, ?_⟩
    rw [Polynomial.IsRoot.def, ← Polynomial.coeff_zero_eq_eval_zero]
    simp_all
  have h0_mem : (0 : ℝ) ∈ rs := by
    have : (0 : ℝ) ∈ (↑rs : Multiset ℝ) := by simp_all
    exact Multiset.mem_coe.mp this
  have h0_le_m : (0 : ℝ) ≤ m := by
    have := List.Pairwise.rel_getLast hrs_sorted h0_mem
    simp_all
  have hm0 : m = 0 := le_antisymm hm_nonpos h0_le_m
  have hdivX_roots : (↑(rs.dropLast) : Multiset ℝ) = g.divX.roots :=
    divX_roots_eq_dropLast_of_coeff_zero hg.1 hg0 hrs_eq hrs_ne (hm.symm.trans hm0)
  have hdrop_sorted : (rs.dropLast).Pairwise (· ≤ ·) :=
    List.Pairwise.sublist (List.dropLast_sublist rs) hrs_sorted
  have hlen_eq : (rs.dropLast).length = ss.length := by simp_all
  have hAlt : ListAlternates (rs.dropLast) ss :=
    listAlternates_dropLast_of_listInterlaces hlen1 hInter
  have hdivX_ne : g.divX ≠ 0 := by
    intro hz
    have hgX : g = X * g.divX := DegreeDropReversal.eq_X_mul_divX_of_coeff_zero hg0
    grind
  have hdivX_split : g.divX.Splits :=
    (DegreeDropReversal.splits_iff_divX_splits_of_coeff_zero hg0).1 hg.2
  exact ⟨⟨hdivX_ne, hdivX_split⟩, hf, rs.dropLast, ss, hdrop_sorted, hss_sorted,
    hdivX_roots, hss_eq, Or.inr ⟨hlen_eq, hAlt⟩⟩

/-- Right-zero degree-drop reconstruction at the `Prec` level.

This is the converse of `prec_divX_left_of_prec_of_hasNonnegCoeffs_coeff_zero`.
In the succ-degree configuration `g.natDegree = f.natDegree + 1`, if both `f`
and `g` have nonnegative coefficients and `g.coeff 0 = 0`, then the same-degree
alternation `Prec (g.divX) f` reassembles, after restoring the zero root of `g`,
into the differ-by-one interlacing `Prec f g`.

Together with `prec_divX_left_of_prec_of_hasNonnegCoeffs_coeff_zero` this shows
that on the right-zero lead branch the sharper orientation target `Prec f g` and
the `divX` orientation target `Prec (g.divX) f` are equivalent. -/
theorem prec_of_prec_divX_left_of_hasNonnegCoeffs_coeff_zero
    {f g : ℝ[X]}
    (hprec : Prec (g.divX) f)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hg0 : g.coeff 0 = 0)
    (hdeg : g.natDegree = f.natDegree + 1) :
    Prec f g := by
  obtain ⟨hdivX, hf, aa, bb, haa_sorted, hbb_sorted, haa_eq, hbb_eq, hshape⟩ :=
    hprec
  have haa_len : aa.length = g.divX.natDegree := by
    rw [← Multiset.coe_card, haa_eq, card_roots_of_splits hdivX.2]
  have hbb_len : bb.length = f.natDegree := by
    rw [← Multiset.coe_card, hbb_eq, card_roots_of_splits hf.2]
  have hdivX_deg : g.divX.natDegree = f.natDegree :=
    natDegree_divX_eq_of_succDegree hdeg
  have hAlt : ListAlternates aa bb := by simp_all
  have hgX : g = X * g.divX :=
    DegreeDropReversal.eq_X_mul_divX_of_coeff_zero hg0
  have hg_ne : g ≠ 0 := by
    rw [hgX]
    exact mul_ne_zero X_ne_zero hdivX.1
  have hg_split : g.Splits :=
    (DegreeDropReversal.splits_iff_divX_splits_of_coeff_zero hg0).2 hdivX.2
  have hf_nonpos : ∀ u ∈ bb, u ≤ 0 := by
    intro u hu
    have hmem : u ∈ f.roots := by rw [← hbb_eq]; exact Multiset.mem_coe.mpr hu
    exact roots_nonpos_of_hasNonnegCoeffs hfnn u hmem
  have hg_roots : g.roots = (0 : ℝ) ::ₘ g.divX.roots :=
    roots_eq_zero_cons_divX_of_coeff_zero hg_ne hg0
  have hdivX_nonpos : ∀ a ∈ aa, a ≤ 0 := by
    intro a ha
    have hmem : a ∈ g.divX.roots := by rw [← haa_eq]; exact Multiset.mem_coe.mpr ha
    have hmem' : a ∈ g.roots := by grind
    exact roots_nonpos_of_hasNonnegCoeffs hgnn a hmem'
  have hrs_sorted : (aa ++ [(0 : ℝ)]).Pairwise (· ≤ ·) := by grind
  have hrs_eq : (↑(aa ++ [(0 : ℝ)]) : Multiset ℝ) = g.roots := by
    rw [hg_roots, ← haa_eq]
    simp
  refine ⟨hf, ⟨hg_ne, hg_split⟩, bb, aa ++ [(0 : ℝ)], hbb_sorted, hrs_sorted,
    hbb_eq, hrs_eq, Or.inl ⟨?_, ?_⟩⟩
  · grind
  · apply listInterlaces_append_singleton_of_listAlternates
      (m := (0 : ℝ)) (halt := hAlt) (hbound := hf_nonpos)
    grind

/-- Right-zero degree-drop equivalence at the `Prec` level.

This packages `prec_divX_left_of_prec_of_hasNonnegCoeffs_coeff_zero` and its
converse `prec_of_prec_divX_left_of_hasNonnegCoeffs_coeff_zero` into a single
`Iff`.  In the succ-degree configuration `g.natDegree = f.natDegree + 1`, if both
`f` and `g` have nonnegative coefficients and `g.coeff 0 = 0`, then the sharper
differ-by-one orientation target `Prec f g` and the same-degree `divX`
orientation target `Prec (g.divX) f` are equivalent.

This is the form easiest for the right-zero lead branch challenge wrappers to
consume: either orientation can be discharged from the other with a single
`.mp`/`.mpr`. -/
theorem prec_iff_prec_divX_left_of_hasNonnegCoeffs_coeff_zero
    {f g : ℝ[X]}
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hg0 : g.coeff 0 = 0)
    (hdeg : g.natDegree = f.natDegree + 1) :
    Prec f g ↔ Prec (g.divX) f :=
  ⟨fun hprec =>
      prec_divX_left_of_prec_of_hasNonnegCoeffs_coeff_zero hprec hgnn hg0 hdeg,
   fun hprec =>
      prec_of_prec_divX_left_of_hasNonnegCoeffs_coeff_zero hprec hfnn hgnn hg0
        hdeg⟩

/-- Bundle the same-degree data for the right-zero succ-degree divX reduction. -/
lemma sameDegreePair_divX_data_of_succDegree_of_coeff_zero
    {f g : ℝ[X]}
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hg : g ≠ 0) (hg_split : g.Splits)
    (hg0 : g.coeff 0 = 0) (hdeg : g.natDegree = f.natDegree + 1) :
    (g.divX.natDegree = f.natDegree ∧ Multiset.card g.divX.roots = f.natDegree)
      ∧ (Prec f g ↔ Prec (g.divX) f) :=
  ⟨natDegree_and_card_divX_roots_eq_natDegree_of_succDegree_of_coeff_zero
      hg hg0 hg_split hdeg,
   prec_iff_prec_divX_left_of_hasNonnegCoeffs_coeff_zero hfnn hgnn hg0 hdeg⟩

/-- Orientation projection from the bundled right-zero succ-degree divX data. -/
lemma sameDegreePair_divX_prec_iff_of_succDegree_of_coeff_zero
    {f g : ℝ[X]}
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hg : g ≠ 0) (hg_split : g.Splits)
    (hg0 : g.coeff 0 = 0) (hdeg : g.natDegree = f.natDegree + 1) :
    Prec f g ↔ Prec (g.divX) f :=
  (sameDegreePair_divX_data_of_succDegree_of_coeff_zero
    hfnn hgnn hg hg_split hg0 hdeg).2

/-- Forward orientation projection from the right-zero succ-degree divX
equivalence. -/
lemma sameDegreePair_divX_prec_forward_of_succDegree_of_coeff_zero
    {f g : ℝ[X]}
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hg : g ≠ 0) (hg_split : g.Splits)
    (hg0 : g.coeff 0 = 0) (hdeg : g.natDegree = f.natDegree + 1)
    (hprec : Prec f g) :
    Prec (g.divX) f :=
  (sameDegreePair_divX_prec_iff_of_succDegree_of_coeff_zero
    hfnn hgnn hg hg_split hg0 hdeg).mp hprec

/-- Backward orientation projection from the right-zero succ-degree divX
equivalence. -/
lemma sameDegreePair_divX_prec_backward_of_succDegree_of_coeff_zero
    {f g : ℝ[X]}
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hg : g ≠ 0) (hg_split : g.Splits)
    (hg0 : g.coeff 0 = 0) (hdeg : g.natDegree = f.natDegree + 1)
    (hprec : Prec (g.divX) f) :
    Prec f g :=
  (sameDegreePair_divX_prec_iff_of_succDegree_of_coeff_zero
    hfnn hgnn hg hg_split hg0 hdeg).mpr hprec

/-- Same-degree data projection from the bundled right-zero succ-degree divX data. -/
lemma sameDegreePair_divX_natDegree_eq_of_succDegree_of_coeff_zero
    {f g : ℝ[X]}
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hg : g ≠ 0) (hg_split : g.Splits)
    (hg0 : g.coeff 0 = 0) (hdeg : g.natDegree = f.natDegree + 1) :
    g.divX.natDegree = f.natDegree ∧ Multiset.card g.divX.roots = f.natDegree :=
  (sameDegreePair_divX_data_of_succDegree_of_coeff_zero
    hfnn hgnn hg hg_split hg0 hdeg).1

/-- Nat-degree component projection from the bundled right-zero succ-degree
`divX` data. -/
lemma sameDegreePair_divX_natDegree_component_eq_of_succDegree_of_coeff_zero
    {f g : ℝ[X]}
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hg : g ≠ 0) (hg_split : g.Splits)
    (hg0 : g.coeff 0 = 0) (hdeg : g.natDegree = f.natDegree + 1) :
    g.divX.natDegree = f.natDegree :=
  (sameDegreePair_divX_natDegree_eq_of_succDegree_of_coeff_zero
    hfnn hgnn hg hg_split hg0 hdeg).1

/-- Root-cardinality projection from the bundled right-zero succ-degree
`divX` data. -/
lemma sameDegreePair_divX_roots_card_eq_of_succDegree_of_coeff_zero
    {f g : ℝ[X]}
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hg : g ≠ 0) (hg_split : g.Splits)
    (hg0 : g.coeff 0 = 0) (hdeg : g.natDegree = f.natDegree + 1) :
    Multiset.card g.divX.roots = f.natDegree :=
  (sameDegreePair_divX_natDegree_eq_of_succDegree_of_coeff_zero
    hfnn hgnn hg hg_split hg0 hdeg).2

/-- Nat-degree projection from the bundled right-zero succ-degree `divX` data. -/
lemma sameDegreePair_divX_natDegree_only_eq_of_succDegree_of_coeff_zero
    {f g : ℝ[X]}
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hg : g ≠ 0) (hg_split : g.Splits)
    (hg0 : g.coeff 0 = 0) (hdeg : g.natDegree = f.natDegree + 1) :
    g.divX.natDegree = f.natDegree :=
  (sameDegreePair_divX_natDegree_eq_of_succDegree_of_coeff_zero
    hfnn hgnn hg hg_split hg0 hdeg).1

/-! ## Splitting / real-rooted transport across the right-zero `divX` step

The main degree-drop theorems above re-derive `g.divX ≠ 0` and `g.divX.Splits`
inline every time they need the lower endpoint to be a genuine real-rooted
polynomial.  The next few lemmas expose those two facts (and their bundled
`(≠ 0 ∧ Splits)` form, matching the first component of `Prec`) as standalone
wrappers, so downstream `CommonInterleaverTwo`/endpoint-sign call sites can hand
the real-rooted data straight to `Prec`/`Prec0` without local reshuffling. -/

/-- Removing the common zero root keeps the quotient nonzero: if `g ≠ 0` and
`g.coeff 0 = 0` then `g.divX ≠ 0`. -/
lemma divX_ne_zero_of_coeff_zero {g : ℝ[X]}
    (hg : g ≠ 0) (hg0 : g.coeff 0 = 0) :
    g.divX ≠ 0 := by
  intro hz
  have hgX : g = X * g.divX :=
    DegreeDropReversal.eq_X_mul_divX_of_coeff_zero hg0
  grind

/-- Removing the common zero root preserves splitting: if `g.coeff 0 = 0` and
`g.Splits` then `g.divX.Splits`.  Directional wrapper for
`DegreeDropReversal.splits_iff_divX_splits_of_coeff_zero`. -/
lemma divX_splits_of_splits_of_coeff_zero {g : ℝ[X]}
    (hg0 : g.coeff 0 = 0) (hgs : g.Splits) :
    g.divX.Splits :=
  (DegreeDropReversal.splits_iff_divX_splits_of_coeff_zero hg0).1 hgs

/-- Bundled real-rooted transport for the right-zero `divX` step.

If `g` is a nonzero split polynomial with `g.coeff 0 = 0`, then so is `g.divX`.
The conclusion is stated in the `(≠ 0 ∧ Splits)` shape used as the first
component of `Prec`, so it can be dropped directly into a `Prec (g.divX) _`
witness. -/
lemma divX_realRooted_of_coeff_zero {g : ℝ[X]}
    (hg : g ≠ 0) (hg0 : g.coeff 0 = 0) (hgs : g.Splits) :
    g.divX ≠ 0 ∧ g.divX.Splits :=
  ⟨divX_ne_zero_of_coeff_zero hg hg0, divX_splits_of_splits_of_coeff_zero hg0 hgs⟩

/-! ## Proper-position facts for the removed zero root -/

/-- The removed root really is a root: a nonzero polynomial with vanishing
constant coefficient has `0` among its roots. -/
lemma zero_mem_roots_of_coeff_zero {g : ℝ[X]}
    (hg : g ≠ 0) (hg0 : g.coeff 0 = 0) :
    (0 : ℝ) ∈ g.roots := by
  rw [Polynomial.mem_roots']
  refine ⟨hg, ?_⟩
  rw [Polynomial.IsRoot.def, ← Polynomial.coeff_zero_eq_eval_zero]
  simp_all

/-- Proper-position fact for the closed-segment/common-interleaver route: with
nonnegative coefficients every root of `g.divX` is `≤ 0`, since the roots of
`g.divX` sit among the (nonpositive) roots of `g`. -/
lemma divX_roots_nonpos_of_hasNonnegCoeffs {g : ℝ[X]}
    (hg : g ≠ 0) (hgnn : HasNonnegCoeffs g) (hg0 : g.coeff 0 = 0) :
    ∀ a ∈ g.divX.roots, a ≤ 0 := by
  intro a ha
  have hmem : a ∈ g.roots := by
    rw [roots_eq_zero_cons_divX_of_coeff_zero hg hg0]
    simp_all
  exact roots_nonpos_of_hasNonnegCoeffs hgnn a hmem

/-! ## `Prec0`-level right-zero degree drop -/

/-- `Prec0` form of `prec_divX_left_of_prec_of_hasNonnegCoeffs_coeff_zero`.

On the right-zero lead branch, a differ-by-one interlacing `Prec f g` collapses,
after removing the zero root of `g`, to the relaxed same-degree relation
`Prec0 (g.divX) f`.  This is the form consumed by the `Prec0`-based
generalized-Sturm/common-interleaver call sites. -/
theorem prec0_divX_left_of_prec_of_hasNonnegCoeffs_coeff_zero
    {f g : ℝ[X]}
    (hprec : Prec f g)
    (hgnn : HasNonnegCoeffs g)
    (hg0 : g.coeff 0 = 0)
    (hdeg : g.natDegree = f.natDegree + 1) :
    Prec0 (g.divX) f :=
  (prec_divX_left_of_prec_of_hasNonnegCoeffs_coeff_zero hprec hgnn hg0 hdeg).toPrec0

/-! ## Downstream-friendly right-zero branch packages

The `CommonInterleaverTwo`/endpoint-sign call sites on the right-zero lead
branch need several facts at once: the collapsed `Prec0` orientation for the
reduced pair, the real-rooted `(≠ 0 ∧ Splits)` data for the quotient `g.divX`,
the witness that `0` genuinely sits among the roots of `g`, and the sign
information that every root of `g.divX` is nonpositive.
-/

/-- Real-rooted transport for the quotient, driven by the `Prec` witness. -/
lemma divX_realRooted_of_prec_coeff_zero {f g : ℝ[X]}
    (hprec : Prec f g) (hg0 : g.coeff 0 = 0) :
    g.divX ≠ 0 ∧ g.divX.Splits :=
  divX_realRooted_of_coeff_zero hprec.2.1.1 hg0 hprec.2.1.2

/-- The removed zero root really is a root of `g`, driven by the `Prec` witness. -/
lemma zero_mem_roots_of_prec_coeff_zero {f g : ℝ[X]}
    (hprec : Prec f g) (hg0 : g.coeff 0 = 0) :
    (0 : ℝ) ∈ g.roots :=
  zero_mem_roots_of_coeff_zero hprec.2.1.1 hg0

/-- Every root of the quotient is nonpositive, driven by the `Prec` witness. -/
lemma divX_roots_nonpos_of_prec_hasNonnegCoeffs {f g : ℝ[X]}
    (hprec : Prec f g) (hgnn : HasNonnegCoeffs g) (hg0 : g.coeff 0 = 0) :
    ∀ a ∈ g.divX.roots, a ≤ 0 :=
  divX_roots_nonpos_of_hasNonnegCoeffs hprec.2.1.1 hgnn hg0

/-- Bundled right-zero degree-drop package. -/
theorem rightZeroDivX_package_of_prec_of_hasNonnegCoeffs_coeff_zero
    {f g : ℝ[X]}
    (hprec : Prec f g)
    (hgnn : HasNonnegCoeffs g)
    (hg0 : g.coeff 0 = 0)
    (hdeg : g.natDegree = f.natDegree + 1) :
    Prec0 (g.divX) f
      ∧ (g.divX ≠ 0 ∧ g.divX.Splits)
      ∧ (0 : ℝ) ∈ g.roots
      ∧ (∀ a ∈ g.divX.roots, a ≤ 0) :=
  ⟨prec0_divX_left_of_prec_of_hasNonnegCoeffs_coeff_zero hprec hgnn hg0 hdeg,
    divX_realRooted_of_prec_coeff_zero hprec hg0,
    zero_mem_roots_of_prec_coeff_zero hprec hg0,
    divX_roots_nonpos_of_prec_hasNonnegCoeffs hprec hgnn hg0⟩

/-- Orientation projection from the bundled right-zero degree-drop package. -/
theorem rightZeroDivX_prec0_of_prec_of_hasNonnegCoeffs_coeff_zero
    {f g : ℝ[X]}
    (hprec : Prec f g) (hgnn : HasNonnegCoeffs g)
    (hg0 : g.coeff 0 = 0) (hdeg : g.natDegree = f.natDegree + 1) :
    Prec0 (g.divX) f :=
  (rightZeroDivX_package_of_prec_of_hasNonnegCoeffs_coeff_zero
    hprec hgnn hg0 hdeg).1

/-- Real-rooted projection from the bundled right-zero degree-drop package. -/
theorem rightZeroDivX_realRooted_of_prec_of_hasNonnegCoeffs_coeff_zero
    {f g : ℝ[X]}
    (hprec : Prec f g) (hgnn : HasNonnegCoeffs g)
    (hg0 : g.coeff 0 = 0) (hdeg : g.natDegree = f.natDegree + 1) :
    g.divX ≠ 0 ∧ g.divX.Splits :=
  (rightZeroDivX_package_of_prec_of_hasNonnegCoeffs_coeff_zero
    hprec hgnn hg0 hdeg).2.1

/-- Zero-root-membership projection from the bundled right-zero degree-drop package. -/
theorem rightZeroDivX_zero_mem_roots_of_prec_of_hasNonnegCoeffs_coeff_zero
    {f g : ℝ[X]}
    (hprec : Prec f g) (hgnn : HasNonnegCoeffs g)
    (hg0 : g.coeff 0 = 0) (hdeg : g.natDegree = f.natDegree + 1) :
    (0 : ℝ) ∈ g.roots :=
  (rightZeroDivX_package_of_prec_of_hasNonnegCoeffs_coeff_zero
    hprec hgnn hg0 hdeg).2.2.1

/-- Nonpositive-roots projection from the bundled right-zero degree-drop package. -/
theorem rightZeroDivX_roots_nonpos_of_prec_of_hasNonnegCoeffs_coeff_zero
    {f g : ℝ[X]}
    (hprec : Prec f g) (hgnn : HasNonnegCoeffs g)
    (hg0 : g.coeff 0 = 0) (hdeg : g.natDegree = f.natDegree + 1) :
    ∀ a ∈ g.divX.roots, a ≤ 0 :=
  (rightZeroDivX_package_of_prec_of_hasNonnegCoeffs_coeff_zero
    hprec hgnn hg0 hdeg).2.2.2

end RealRooted
