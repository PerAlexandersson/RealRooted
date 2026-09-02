import RealRooted.InterlacingSequenceBasic
import RealRooted.WeightedSum
import RealRooted.PosCombo

/-!
# Common interleavers: descending roots

The common-interleaver predicates, canonical descending root sequences, their
indexwise characterisation of `Prec`, and the consecutive-chain lemma.
-/

open Polynomial

noncomputable section

namespace RealRooted

section

/-- A list of polynomials has a common interleaver if all of its members
interlace a single polynomial on the right. This is Brändén's "common
interleaver" language from Handbook §7.8. -/
def HasCommonInterleaver (fs : List ℝ[X]) : Prop :=
  ∃ h : ℝ[X], ∀ f ∈ fs, Prec f h

/-- Pairwise common-interleaver condition: every pair in the list admits some
common right interleaver. This is the hypothesis occurring in the
Chudnovsky--Seymour theorem. -/
def PairwiseHasCommonInterleaver (fs : List ℝ[X]) : Prop :=
  ∀ (i j : Fin fs.length), i < j →
    ∃ h : ℝ[X], Prec (fs.get i) h ∧ Prec (fs.get j) h

/-- Left-oriented common interleaver: all members are interlaced by a single
polynomial on the left. This is the orientation naturally used by the mixed
product family in Brändén 7.8.3 and by Wagner's left-sum theorem. -/
def HasCommonLeftInterleaver (fs : List ℝ[X]) : Prop :=
  ∃ h : ℝ[X], ∀ f ∈ fs, Prec h f

/-- Pairwise left-oriented common interleaver condition. -/
def PairwiseHasCommonLeftInterleaver (fs : List ℝ[X]) : Prop :=
  ∀ (i j : Fin fs.length), i < j →
    ∃ h : ℝ[X], Prec h (fs.get i) ∧ Prec h (fs.get j)

/-- Descending root sequence used in the Chudnovsky--Seymour interval proof. -/
def rootSeqDesc (f : ℝ[X]) : List ℝ :=
  (f.roots.sort (· ≤ ·)).reverse

@[simp] lemma rootSeqDesc_length {f : ℝ[X]} (hf : f.Splits) :
    (rootSeqDesc f).length = f.natDegree := by
  simp [rootSeqDesc, card_roots_of_splits hf]

@[simp] lemma rootSeqDesc_eq_nil {f : ℝ[X]} (hf : f.Splits) :
    rootSeqDesc f = [] ↔ f.natDegree = 0 := by simp [← List.length_eq_zero_iff, hf]

protected lemma CommonInterleaver.rootSeqDesc_ne_nil_of_natDegree_pos
    {f : ℝ[X]} (hf : f.Splits) (hpos : 0 < f.natDegree) :
    rootSeqDesc f ≠ [] := by
  apply List.ne_nil_of_length_pos
  simpa [rootSeqDesc_length hf] using hpos

protected lemma CommonInterleaver.rootSeqDesc_reverse_ne_nil_of_natDegree_pos
    {f : ℝ[X]} (hf : f.Splits) (hpos : 0 < f.natDegree) :
    (rootSeqDesc f).reverse ≠ [] :=
  List.reverse_ne_nil_iff.mpr
    (CommonInterleaver.rootSeqDesc_ne_nil_of_natDegree_pos hf hpos)

lemma rootSeqDesc_pairwise {f : ℝ[X]} :
    (rootSeqDesc f).Pairwise (· ≥ ·) := by
  simpa [rootSeqDesc] using (Multiset.pairwise_sort (s := f.roots) (r := (· ≤ ·))).reverse

lemma rootSeqDesc_eq_reverse_of_pairwise
    {f : ℝ[X]} {rs : List ℝ}
    (hrs : rs.Pairwise (· ≤ ·))
    (hrs_eq : (↑rs : Multiset ℝ) = f.roots) :
    rootSeqDesc f = rs.reverse := by
  letI : Std.Antisymm ((· ≥ ·) : ℝ → ℝ → Prop) :=
    ⟨fun _ _ hab hba => le_antisymm hba hab⟩
  apply (List.Perm.eq_of_pairwise' (r := ((· ≥ ·) : ℝ → ℝ → Prop)))
  · simpa [rootSeqDesc] using (Multiset.pairwise_sort (s := f.roots) (r := (· ≤ ·))).reverse
  · grind
  · exact Multiset.coe_eq_coe.mp (by simp [rootSeqDesc, hrs_eq, Multiset.sort_eq])

/-- The canonical descending root sequence is the roots sorted in decreasing order. -/
lemma rootSeqDesc_eq_sort_ge (f : ℝ[X]) :
    rootSeqDesc f = f.roots.sort (· ≥ ·) := by
  have hpair :
      ((f.roots.sort (· ≥ ·)).reverse).Pairwise (· ≤ ·) := by
    simpa using
      (Multiset.pairwise_sort (s := f.roots) (r := (· ≥ ·))).reverse
  have hroots :
      (↑((f.roots.sort (· ≥ ·)).reverse) : Multiset ℝ) = f.roots := by
    simp [Multiset.sort_eq]
  simpa using
    (rootSeqDesc_eq_reverse_of_pairwise (f := f)
      (rs := (f.roots.sort (· ≥ ·)).reverse) hpair hroots)

/-!
### A descending-root index characterisation of `Prec`

`Prec f g` is defined through *ascending* sorted root lists.  For the chaining
argument below it is much more convenient to index roots from the right, i.e.
by the canonical descending root sequence `rootSeqDesc`.  The two lemmas
`desc_bounds_of_interlacing_shape` and `interlacing_shape_of_desc_bounds` translate the
list-level interlacing patterns into (and out of) the uniform descending
inequalities

* `f⟨l⟩ ≤ g⟨l⟩`  for `l < deg f`,
* `g⟨l+1⟩ ≤ f⟨l⟩` for `l < deg f` and `l + 1 < deg g`,

which hold simultaneously in the equal-degree and the differ-by-one case.
-/

lemma getD_reverse_eq (l : List ℝ) (j : ℕ) (hj : j < l.length) :
    l.reverse.getD j 0 = l.getD (l.length - 1 - j) 0 := by
  have hj' : j < l.reverse.length := by simpa using hj
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hj', List.getElem?_eq_getElem (show l.length - 1 - j < l.length by
      lia)]
  simp [List.getElem_reverse]

lemma desc_bounds_of_interlacing_shape (ss rs : List ℝ)
    (h : (ss.length + 1 = rs.length ∧ ListInterlaces ss rs) ∨
      (ss.length = rs.length ∧ ListAlternates ss rs)) :
    (∀ j, j < ss.length → ss.reverse.getD j 0 ≤ rs.reverse.getD j 0) ∧
      (∀ j, j < ss.length → j + 1 < rs.length →
        rs.reverse.getD (j + 1) 0 ≤ ss.reverse.getD j 0) := by
  rcases h with ⟨hlen, hI⟩ | ⟨hlen, hA⟩
  · obtain ⟨b1, b2⟩ := listInterlaces_getD_bounds ss rs hI hlen
    refine ⟨?_, ?_⟩
    · intro j hj
      rw [getD_reverse_eq ss j hj, getD_reverse_eq rs j (by lia),
        show rs.length - 1 - j = ss.length - 1 - j + 1 by lia]
      exact b2 _ (by lia)
    · intro j hj hj2
      rw [getD_reverse_eq rs (j + 1) hj2, getD_reverse_eq ss j hj,
        show rs.length - 1 - (j + 1) = ss.length - 1 - j by lia]
      exact b1 _ (by lia)
  · obtain ⟨a1, a2⟩ := listAlternates_getD_bounds ss rs hA hlen
    refine ⟨?_, ?_⟩
    · intro j hj
      rw [getD_reverse_eq ss j hj, getD_reverse_eq rs j (by lia),
        show rs.length - 1 - j = ss.length - 1 - j by lia]
      exact a1 _ (by lia)
    · intro j hj hj2
      rw [getD_reverse_eq rs (j + 1) hj2, getD_reverse_eq ss j hj,
        show ss.length - 1 - j = rs.length - 1 - (j + 1) + 1 by lia]
      exact a2 _ (by lia)

lemma interlacing_shape_of_desc_bounds (ss rs : List ℝ)
    (hlen : rs.length = ss.length ∨ rs.length = ss.length + 1)
    (h1 : ∀ j, j < ss.length → ss.reverse.getD j 0 ≤ rs.reverse.getD j 0)
    (h2 : ∀ j, j < ss.length → j + 1 < rs.length →
      rs.reverse.getD (j + 1) 0 ≤ ss.reverse.getD j 0) :
    (ss.length + 1 = rs.length ∧ ListInterlaces ss rs) ∨
      (ss.length = rs.length ∧ ListAlternates ss rs) := by
  rcases hlen with hd | hd
  · refine Or.inr ⟨by lia, ?_⟩
    refine listAlternates_of_getD_bounds _ _ (by lia) ?_ ?_
    · intro i hi
      have key := h1 (ss.length - 1 - i) (by lia)
      rw [getD_reverse_eq ss _ (show ss.length - 1 - i < ss.length by lia),
        getD_reverse_eq rs _ (show ss.length - 1 - i < rs.length by lia),
        show ss.length - 1 - (ss.length - 1 - i) = i by lia,
        show rs.length - 1 - (ss.length - 1 - i) = i by lia] at key
      exact key
    · intro i hi
      have key := h2 (ss.length - 1 - (i + 1)) (by lia) (by lia)
      rw [getD_reverse_eq rs _ (show ss.length - 1 - (i + 1) + 1 < rs.length by lia),
        getD_reverse_eq ss _ (show ss.length - 1 - (i + 1) < ss.length by lia),
        show rs.length - 1 - (ss.length - 1 - (i + 1) + 1) = i by lia,
        show ss.length - 1 - (ss.length - 1 - (i + 1)) = i + 1 by lia] at key
      exact key
  · refine Or.inl ⟨by lia, ?_⟩
    refine listInterlaces_of_getD_bounds _ _ (by lia) ?_ ?_
    · intro i hi
      have key := h2 (ss.length - 1 - i) (by lia) (by lia)
      rw [getD_reverse_eq rs _ (show ss.length - 1 - i + 1 < rs.length by lia),
        getD_reverse_eq ss _ (show ss.length - 1 - i < ss.length by lia),
        show rs.length - 1 - (ss.length - 1 - i + 1) = i by lia,
        show ss.length - 1 - (ss.length - 1 - i) = i by lia] at key
      exact key
    · intro i hi
      have key := h1 (ss.length - 1 - i) (by lia)
      rw [getD_reverse_eq ss _ (show ss.length - 1 - i < ss.length by lia),
        getD_reverse_eq rs _ (show ss.length - 1 - i < rs.length by lia),
        show ss.length - 1 - (ss.length - 1 - i) = i by lia,
        show rs.length - 1 - (ss.length - 1 - i) = i + 1 by lia] at key
      exact key

/-- Descending-root characterisation of `Prec`: writing `f⟨l⟩` for the `l`-th
largest root of `f`, `f ≪ g` holds exactly when both are real-rooted, the
degrees differ by at most one (with `g` the larger), and the descending root
sequences satisfy `f⟨l⟩ ≤ g⟨l⟩` and `g⟨l+1⟩ ≤ f⟨l⟩`. -/
theorem prec_iff_rootSeqDesc {f g : ℝ[X]} :
    Prec f g ↔
      (f ≠ 0 ∧ f.Splits) ∧ (g ≠ 0 ∧ g.Splits) ∧
        (g.natDegree = f.natDegree ∨ g.natDegree = f.natDegree + 1) ∧
        (∀ l, l < f.natDegree →
          (rootSeqDesc f).getD l 0 ≤ (rootSeqDesc g).getD l 0) ∧
        (∀ l, l < f.natDegree → l + 1 < g.natDegree →
          (rootSeqDesc g).getD (l + 1) 0 ≤ (rootSeqDesc f).getD l 0) := by
  constructor
  · rintro ⟨hf, hg, ss, rs, hss_p, hrs_p, hss_eq, hrs_eq, hshape⟩
    have hssL : ss.length = f.natDegree := by
      rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hf.2]
    have hrsL : rs.length = g.natDegree := by
      rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hg.2]
    have hSf : rootSeqDesc f = ss.reverse := rootSeqDesc_eq_reverse_of_pairwise hss_p hss_eq
    have hSg : rootSeqDesc g = rs.reverse := rootSeqDesc_eq_reverse_of_pairwise hrs_p hrs_eq
    obtain ⟨d1, d2⟩ := desc_bounds_of_interlacing_shape ss rs hshape
    refine ⟨hf, hg, ?_, ?_, ?_⟩
    · rcases hshape with ⟨hlen, -⟩ | ⟨hlen, -⟩
      · exact Or.inr (by lia)
      · exact Or.inl (by lia)
    · intro l hl
      rw [hSf, hSg]
      exact d1 l (by lia)
    · intro l hl hl2
      rw [hSf, hSg]
      exact d2 l (by lia) (by lia)
  · rintro ⟨hf, hg, hdeg, h1, h2⟩
    have hSf : rootSeqDesc f = (f.roots.sort (· ≤ ·)).reverse := rfl
    have hSg : rootSeqDesc g = (g.roots.sort (· ≤ ·)).reverse := rfl
    have hssL : (f.roots.sort (· ≤ ·)).length = f.natDegree := by
      rw [Multiset.length_sort, card_roots_of_splits hf.2]
    have hrsL : (g.roots.sort (· ≤ ·)).length = g.natDegree := by
      rw [Multiset.length_sort, card_roots_of_splits hg.2]
    refine ⟨hf, hg, f.roots.sort (· ≤ ·), g.roots.sort (· ≤ ·),
      Multiset.pairwise_sort .., Multiset.pairwise_sort .., Multiset.sort_eq ..,
      Multiset.sort_eq .., ?_⟩
    have hlen : (g.roots.sort (· ≤ ·)).length = (f.roots.sort (· ≤ ·)).length ∨
        (g.roots.sort (· ≤ ·)).length = (f.roots.sort (· ≤ ·)).length + 1 := by
      rcases hdeg with h | h
      · exact Or.inl (by lia)
      · exact Or.inr (by lia)
    refine interlacing_shape_of_desc_bounds _ _ hlen ?_ ?_
    · intro l hl
      have := h1 l (by lia)
      rwa [hSf, hSg] at this
    · intro l hl hl2
      have := h2 l (by lia) (by lia)
      rwa [hSf, hSg] at this

/-- **Chain lemma.**  If `F a ≪ F (a+1) ≪ ⋯ ≪ F b` is a chain of consecutive
interlacings and additionally the two extremes satisfy `F a ≪ F b`, then every
pair `F i ≪ F j` with `a ≤ i ≤ j ≤ b` interlaces.  This is the substitute for
transitivity of `≪`, which fails in general. -/
theorem prec_chain_of_consecutive_of_endpoint (F : ℕ → ℝ[X]) (a b : ℕ)
    (hcons : ∀ k, a ≤ k → k < b → Prec (F k) (F (k + 1)))
    (hext : Prec (F a) (F b)) :
    ∀ i j, a ≤ i → i ≤ j → j ≤ b → Prec (F i) (F j) := by
  obtain ⟨-, -, hdab, -, hextD⟩ := prec_iff_rootSeqDesc.1 hext
  have hdab' : (F b).natDegree ≤ (F a).natDegree + 1 := by rcases hdab with h | h <;> lia
  have hrr : ∀ k, a ≤ k → k ≤ b → (F k ≠ 0 ∧ (F k).Splits) := by
    intro k hak hkb
    rcases Nat.lt_or_ge k b with h | h
    · exact (hcons k hak h).1
    · rw [show k = b by lia]
      exact hext.2.1
  have hstep : ∀ k, a ≤ k → k < b →
      (F k).natDegree ≤ (F (k + 1)).natDegree ∧
        (∀ l, l < (F k).natDegree →
          (rootSeqDesc (F k)).getD l 0 ≤ (rootSeqDesc (F (k + 1))).getD l 0) := by
    intro k hak hkb
    obtain ⟨-, -, hd, hr, -⟩ := prec_iff_rootSeqDesc.1 (hcons k hak hkb)
    exact ⟨by rcases hd with h | h <;> lia, hr⟩
  have hmono : ∀ i j, a ≤ i → i ≤ j → j ≤ b →
      (F i).natDegree ≤ (F j).natDegree ∧
        (∀ l, l < (F i).natDegree →
          (rootSeqDesc (F i)).getD l 0 ≤ (rootSeqDesc (F j)).getD l 0) := by
    intro i j hai hij
    obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by lia⟩
    clear hij
    induction d with
    | zero => exact fun _ => ⟨le_rfl, fun _ _ => le_rfl⟩
    | succ d ihd =>
        intro hkb
        obtain ⟨hd1, hr1⟩ := ihd (by lia)
        obtain ⟨hd2, hr2⟩ := hstep (i + d) (by lia) (by lia)
        exact ⟨le_trans hd1 hd2, fun l hl => le_trans (hr1 l hl) (hr2 l (by lia))⟩
  intro i j hai hij hjb
  have hib : i ≤ b := by lia
  obtain ⟨hdij, hrij⟩ := hmono i j hai hij hjb
  obtain ⟨hdai, hrai⟩ := hmono a i le_rfl hai hib
  obtain ⟨hdjb, hrjb⟩ := hmono j b (by lia) hjb le_rfl
  refine prec_iff_rootSeqDesc.2 ⟨hrr i hai hib, hrr j (by lia) hjb, by lia, hrij, ?_⟩
  intro l hl hl2
  have hla : l < (F a).natDegree := by lia
  calc (rootSeqDesc (F j)).getD (l + 1) 0
      ≤ (rootSeqDesc (F b)).getD (l + 1) 0 := hrjb (l + 1) hl2
    _ ≤ (rootSeqDesc (F a)).getD l 0 := hextD l hla (by lia)
    _ ≤ (rootSeqDesc (F i)).getD l 0 := hrai l hla

end
end RealRooted
