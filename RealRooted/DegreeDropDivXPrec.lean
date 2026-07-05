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
  have hne : X * f.divX ≠ 0 := by
    rw [← hX]
    exact hf
  conv_lhs => rw [hX]
  rw [Polynomial.roots_mul hne, Polynomial.roots_X, Multiset.singleton_add]

theorem roots_eq_zero_cons_divX_of_coeff_zero' {f : ℝ[X]}
    (hf : f ≠ 0) (hf0 : f.coeff 0 = 0) :
    f.roots = 0 ::ₘ f.divX.roots :=
  roots_eq_zero_cons_divX_of_coeff_zero hf hf0

/-- Auxiliary list-combinatorial core of the right-zero degree drop.

If `ss` interlaces a list obtained by appending one last element to `ts`, then
`ts` alternates with `ss`. -/
private lemma listAlternates_append_singleton_aux {m : ℝ} :
    ∀ {ss ts : List ℝ}, ss.length = ts.length →
      ListInterlaces ss (ts ++ [m]) → ListAlternates ts ss := by
  intro ss
  induction ss with
  | nil =>
      intro ts hlen _
      cases ts with
      | nil => simp [ListAlternates]
      | cons _ _ => simp at hlen
  | cons s ss' ih =>
      intro ts hlen hI
      cases ts with
      | nil => simp at hlen
      | cons t ts' =>
          rw [List.cons_append] at hI
          cases ts' with
          | nil =>
              cases ss' with
              | nil =>
                  simp only [List.nil_append] at hI
                  obtain ⟨h1, _, _⟩ := hI
                  exact ⟨h1, by simp [ListInterlaces]⟩
              | cons _ _ => simp at hlen
          | cons t₂ ts'' =>
              cases ss' with
              | nil => simp at hlen
              | cons s' ss'' =>
                  obtain ⟨hts, hst₂, htail⟩ := hI
                  have hlen' : (s' :: ss'').length = (t₂ :: ts'').length := by
                    simpa using hlen
                  obtain ⟨ht₂s', hrectail⟩ := ih hlen' htail
                  exact ⟨hts, hst₂, ht₂s', hrectail⟩

/-- If `ss` interlaces the strictly longer list `rs`, then dropping the
rightmost element of `rs` leaves an equal-length pair that alternates. -/
lemma listAlternates_dropLast_of_listInterlaces {ss rs : List ℝ}
    (hlen : ss.length + 1 = rs.length) (h : ListInterlaces ss rs) :
    ListAlternates rs.dropLast ss := by
  have hrs_ne : rs ≠ [] := by
    intro hc
    rw [hc] at hlen
    simp at hlen
  have hsplit : rs.dropLast ++ [rs.getLast hrs_ne] = rs :=
    List.dropLast_append_getLast hrs_ne
  apply listAlternates_append_singleton_aux (m := rs.getLast hrs_ne)
  · have hd : rs.dropLast.length = rs.length - 1 := by
      simp [List.length_dropLast]
    lia
  · rw [hsplit]
    exact h

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
  have hlen1 : ss.length + 1 = rs.length := by
    rw [hss_len, hrs_len, hdeg]
  have hInter : ListInterlaces ss rs := by
    rcases hshape with ⟨_, hI⟩ | ⟨hbad, _⟩
    · exact hI
    · exfalso
      rw [hss_len, hrs_len, hdeg] at hbad
      lia
  have hrs_ne : rs ≠ [] := by
    intro hc
    rw [hc] at hlen1
    simp at hlen1
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
    exact hg0
  have h0_mem : (0 : ℝ) ∈ rs := by
    have : (0 : ℝ) ∈ (↑rs : Multiset ℝ) := by
      rw [hrs_eq]
      exact h0_root
    exact Multiset.mem_coe.mp this
  have h0_le_m : (0 : ℝ) ≤ m := by
    have := List.Pairwise.rel_getLast hrs_sorted h0_mem
    simpa [hm] using this
  have hm0 : m = 0 := le_antisymm hm_nonpos h0_le_m
  have hsplit : rs.dropLast ++ [m] = rs := List.dropLast_append_getLast hrs_ne
  have hdivX_roots : (↑(rs.dropLast) : Multiset ℝ) = g.divX.roots := by
    have e1 : (↑rs : Multiset ℝ) = (0 : ℝ) ::ₘ ↑(rs.dropLast) := by
      conv_lhs => rw [← hsplit]
      rw [hm0]
      simp
    have e2 : (↑rs : Multiset ℝ) = (0 : ℝ) ::ₘ g.divX.roots := by
      rw [hrs_eq, roots_eq_zero_cons_divX_of_coeff_zero hg.1 hg0]
    rw [e1] at e2
    exact (Multiset.cons_inj_right (0 : ℝ)).mp e2
  have hdrop_sorted : (rs.dropLast).Pairwise (· ≤ ·) :=
    List.Pairwise.sublist (List.dropLast_sublist rs) hrs_sorted
  have hlen_eq : (rs.dropLast).length = ss.length := by
    have hd : rs.dropLast.length = rs.length - 1 := by
      simp [List.length_dropLast]
    lia
  have hAlt : ListAlternates (rs.dropLast) ss :=
    listAlternates_dropLast_of_listInterlaces hlen1 hInter
  have hdivX_ne : g.divX ≠ 0 := by
    intro hz
    have hgX : g = X * g.divX := DegreeDropReversal.eq_X_mul_divX_of_coeff_zero hg0
    rw [hz, mul_zero] at hgX
    exact hg.1 hgX
  have hdivX_split : g.divX.Splits :=
    (DegreeDropReversal.splits_iff_divX_splits_of_coeff_zero hg0).1 hg.2
  exact ⟨⟨hdivX_ne, hdivX_split⟩, hf, rs.dropLast, ss, hdrop_sorted, hss_sorted,
    hdivX_roots, hss_eq, Or.inr ⟨hlen_eq, hAlt⟩⟩

/-- List-level converse of `listAlternates_dropLast_of_listInterlaces`.

If `us` alternates with the equal-length list `ts` and `m` dominates every entry
of `us`, then `us` interlaces the strictly longer list `ts ++ [m]`. -/
private lemma listInterlaces_append_singleton_of_listAlternates {m : ℝ} :
    ∀ {ts us : List ℝ}, ts.length = us.length →
      ListAlternates ts us → (∀ u ∈ us, u ≤ m) →
      ListInterlaces us (ts ++ [m]) := by
  intro ts
  induction ts with
  | nil =>
      intro us hlen _ _
      cases us with
      | nil => simp [ListInterlaces]
      | cons _ _ => simp at hlen
  | cons t ts' ih =>
      intro us hlen halt hle
      cases us with
      | nil => simp at hlen
      | cons u us' =>
          obtain ⟨htu, hI⟩ := halt
          cases ts' with
          | nil =>
              cases us' with
              | nil =>
                  exact ⟨htu, hle u (by simp), by simp [ListInterlaces]⟩
              | cons _ _ => simp at hlen
          | cons t₂ ts'' =>
              cases us' with
              | nil => simp at hlen
              | cons u₂ us'' =>
                  obtain ⟨hut₂, ht₂u₂, hItail⟩ := hI
                  rw [List.cons_append, List.cons_append]
                  refine ⟨htu, hut₂, ?_⟩
                  have := ih (us := u₂ :: us'') (by simpa using hlen)
                    ⟨ht₂u₂, hItail⟩ (fun x hx => hle x (by simp [hx]))
                  rwa [List.cons_append] at this

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
  have hdivX_deg : g.divX.natDegree = f.natDegree := by
    rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one, hdeg, Nat.add_sub_cancel]
  have hAlt : ListAlternates aa bb := by
    rcases hshape with ⟨hbad, _⟩ | ⟨_, halt⟩
    · exfalso
      rw [haa_len, hbb_len, hdivX_deg] at hbad
      lia
    · exact halt
  have hgX : g = X * g.divX :=
    DegreeDropReversal.eq_X_mul_divX_of_coeff_zero hg0
  have hg_ne : g ≠ 0 := by
    rw [hgX]
    exact mul_ne_zero X_ne_zero hdivX.1
  have hg_split : g.Splits :=
    (DegreeDropReversal.splits_iff_divX_splits_of_coeff_zero hg0).2 hdivX.2
  have hf_nonpos : ∀ u ∈ bb, u ≤ 0 := by
    intro u hu
    have hmem : u ∈ f.roots := by
      rw [← hbb_eq]; exact Multiset.mem_coe.mpr hu
    exact roots_nonpos_of_hasNonnegCoeffs hfnn u hmem
  have hg_roots : g.roots = (0 : ℝ) ::ₘ g.divX.roots :=
    roots_eq_zero_cons_divX_of_coeff_zero hg_ne hg0
  have hdivX_nonpos : ∀ a ∈ aa, a ≤ 0 := by
    intro a ha
    have hmem : a ∈ g.divX.roots := by
      rw [← haa_eq]; exact Multiset.mem_coe.mpr ha
    have hmem' : a ∈ g.roots := by
      rw [hg_roots]; exact Multiset.mem_cons_of_mem hmem
    exact roots_nonpos_of_hasNonnegCoeffs hgnn a hmem'
  have hrs_sorted : (aa ++ [(0 : ℝ)]).Pairwise (· ≤ ·) := by
    rw [List.pairwise_append]
    refine ⟨haa_sorted, by simp, ?_⟩
    intro x hx y hy
    simp only [List.mem_singleton] at hy
    subst hy
    exact hdivX_nonpos x hx
  have hrs_eq : (↑(aa ++ [(0 : ℝ)]) : Multiset ℝ) = g.roots := by
    rw [hg_roots, ← haa_eq]
    simp
  refine ⟨hf, ⟨hg_ne, hg_split⟩, bb, aa ++ [(0 : ℝ)], hbb_sorted, hrs_sorted,
    hbb_eq, hrs_eq, Or.inl ⟨?_, ?_⟩⟩
  · rw [List.length_append, haa_len, hbb_len, hdivX_deg]
    simp
  · exact listInterlaces_append_singleton_of_listAlternates
      (by rw [haa_len, hbb_len, hdivX_deg]) hAlt hf_nonpos

end RealRooted
