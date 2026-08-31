import RealRooted.Linear

/-!
# Affine transformations of legacy interlacing

This module records the elementary translations and reflections of the legacy
`Interlaces` predicate.  New code should generally prefer `Prec`, but these
lemmas let existing root-list applications transform an interlacing witness
without reconstructing its sorted lists.
-/

open Polynomial

noncomputable section

namespace RealRooted

private lemma pairwise_reverse_map_neg {l : List ℝ} (h : l.Pairwise (· ≤ ·)) :
    (l.map Neg.neg).reverse.Pairwise (· ≤ ·) := by
  rw [List.pairwise_reverse, List.pairwise_map]
  simpa only [neg_le_neg_iff] using h

private lemma interleaves_map_neg {ss rs : List ℝ}
    (h : List.Interleaves (fun x y : ℝ => x ≤ y) ss rs) :
    List.Interleaves (fun x y : ℝ => y ≤ x) (ss.map Neg.neg) (rs.map Neg.neg) := by
  induction h with
  | nil_nil => exact .nil_nil
  | nil_singleton a => exact .nil_singleton _
  | @cons_symm l₁ l₂ b hl a hab ih =>
      exact .cons_symm ih (by simpa using neg_le_neg hab)

private lemma interlaces_reverse_map_neg {ss rs : List ℝ}
    (h : ListInterlaces ss rs) (hlen : ss.length + 1 = rs.length) :
    ListInterlaces (ss.map Neg.neg).reverse (rs.map Neg.neg).reverse := by
  have hi := interleaves_of_listInterlaces_of_length hlen h
  have him := interleaves_map_neg hi
  have hlen' : (ss.map Neg.neg).length + 1 = (rs.map Neg.neg).length := by
    simpa using hlen
  change List.Interleaves (Function.swap (fun x y : ℝ => x ≤ y))
      (ss.map Neg.neg) (rs.map Neg.neg) at him
  have hir := (List.interleaves_reverse_reverse_of_length_add_one_eq_length
    (r := fun x y : ℝ => x ≤ y) hlen').2 him
  have hlen'' : ((ss.map Neg.neg).reverse).length + 1 =
      ((rs.map Neg.neg).reverse).length := by
    simpa using hlen
  exact listInterlaces_of_interleaves_of_length hlen'' hir

/-- Reflection through the origin preserves legacy interlacing. -/
lemma interlaces_comp_neg_X {g f : ℝ[X]} (h : Interlaces g f) :
    Interlaces (g.comp (-X)) (f.comp (-X)) := by
  rcases h with
    ⟨⟨hfne, hfs⟩, ⟨hgne, hgs⟩, hdeg, ⟨rs, ss, hrs, hss, hfr, hgsr, hlist⟩⟩
  have comp_ne : ∀ {p : ℝ[X]}, p ≠ 0 → p.comp (-X) ≠ 0 := by
    intro p hp
    rw [Ne, Polynomial.comp_eq_zero_iff]
    intro hh
    rcases hh with hh | ⟨_, hq⟩
    · exact hp hh
    · have hc := congrArg (fun q : ℝ[X] => q.coeff 1) hq
      simp at hc
  refine ⟨⟨comp_ne hfne, hfs.comp_neg_X⟩,
    ⟨comp_ne hgne, hgs.comp_neg_X⟩, ?_,
    ⟨(rs.map Neg.neg).reverse, (ss.map Neg.neg).reverse, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simpa [Polynomial.natDegree_comp] using hdeg
  · exact pairwise_reverse_map_neg hrs
  · exact pairwise_reverse_map_neg hss
  · rw [Polynomial.roots_comp_neg_X]
    calc
      (↑(rs.map Neg.neg).reverse : Multiset ℝ) = Multiset.map Neg.neg (↑rs) := by
        simp
      _ = Multiset.map Neg.neg f.roots := by rw [hfr]
  · rw [Polynomial.roots_comp_neg_X]
    calc
      (↑(ss.map Neg.neg).reverse : Multiset ℝ) = Multiset.map Neg.neg (↑ss) := by
        simp
      _ = Multiset.map Neg.neg g.roots := by rw [hgsr]
  · have hrslen : rs.length = f.natDegree := by
      have hc : (↑rs : Multiset ℝ).card = f.natDegree := by
        rw [hfr, card_roots_of_splits hfs]
      simpa using hc
    have hsslen : ss.length = g.natDegree := by
      have hc : (↑ss : Multiset ℝ).card = g.natDegree := by
        rw [hgsr, card_roots_of_splits hgs]
      simpa using hc
    exact interlaces_reverse_map_neg hlist (by lia)

/-- Translation of the variable preserves legacy interlacing. -/
lemma interlaces_comp_X_add_C {g f : ℝ[X]} (h : Interlaces g f) (r : ℝ) :
    Interlaces (g.comp (X + C r)) (f.comp (X + C r)) := by
  rcases h with
    ⟨⟨hfne, hfs⟩, ⟨hgne, hgs⟩, hdeg, ⟨rs, ss, hrs, hss, hfr, hgsr, hlist⟩⟩
  refine ⟨⟨(Polynomial.comp_X_add_C_ne_zero_iff).2 hfne, hfs.comp_X_add_C r⟩,
    ⟨(Polynomial.comp_X_add_C_ne_zero_iff).2 hgne, hgs.comp_X_add_C r⟩, ?_,
    ⟨rs.map (· - r), ss.map (· - r), ?_, ?_, ?_, ?_, ?_⟩⟩
  · simpa [Polynomial.natDegree_comp] using hdeg
  · exact pairwise_map_sub_const hrs r
  · exact pairwise_map_sub_const hss r
  · rw [roots_comp_X_add_C]
    calc
      (↑(rs.map (· - r)) : Multiset ℝ) = Multiset.map (· - r) (↑rs) := by simp
      _ = Multiset.map (· - r) f.roots := by rw [hfr]
  · rw [roots_comp_X_add_C]
    calc
      (↑(ss.map (· - r)) : Multiset ℝ) = Multiset.map (· - r) (↑ss) := by simp
      _ = Multiset.map (· - r) g.roots := by rw [hgsr]
  · exact listInterlaces_map_sub_const hlist r

/-- A reflection followed by a translation preserves legacy interlacing. -/
lemma interlaces_comp_neg_X_sub_C {g f : ℝ[X]} (h : Interlaces g f) (r : ℝ) :
    Interlaces (g.comp (-X - C r)) (f.comp (-X - C r)) := by
  have ht := interlaces_comp_X_add_C (interlaces_comp_neg_X h) r
  simpa [Polynomial.comp_assoc, add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using ht

end RealRooted
