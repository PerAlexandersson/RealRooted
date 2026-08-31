import RealRooted.CommonInterleaver.Finite

/-!
# Common interleavers: sequence construction

Root-sequence common interleaver predicates, their finite-Helly construction,
and pairwise right and left upgrade lemmas.
-/

open Polynomial

noncomputable section

namespace RealRooted

section

/-- Root-sequence common interleaver used for the Chudnovsky--Seymour proof.
The sequence `ps` is written in descending order and its `j`th entry lies in the
`j`th admissible interval of every root sequence in the family. -/
def HasCommonInterleaverSeq (fs : List ℝ[X]) : Prop :=
  ∀ j : ℕ, ∃ x : ℝ, ∀ f ∈ fs, ∀ hjf : j < (rootSeqDesc f).length + 1,
    x ∈ rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩

/-- Shifted root-sequence common interleaver used for the left-oriented
Chudnovsky--Seymour proof.  The sequence is written in descending order, and
its `j`th entry lies in the shifted slot `j + 1` of every root sequence in the
family. -/
def HasCommonLeftInterleaverSeq (fs : List ℝ[X]) : Prop :=
  ∀ j : ℕ, ∃ x : ℝ, ∀ f ∈ fs, ∀ hjf : j + 1 < (rootSeqDesc f).length + 1,
    x ∈ rootSlotInterval (rootSeqDesc f) ⟨j + 1, hjf⟩

private def slotSetAt (j : ℕ) (f : ℝ[X]) : Set ℝ :=
  if hj : j < (rootSeqDesc f).length + 1 then
    rootSlotInterval (rootSeqDesc f) ⟨j, hj⟩
  else
    Set.univ

private lemma slotSetAt_nonempty (j : ℕ) (f : ℝ[X]) :
    (slotSetAt j f).Nonempty := by
  unfold slotSetAt
  by_cases hj : j < (rootSeqDesc f).length + 1
  · simpa [hj] using
      rootSlotInterval_nonempty (rs := rootSeqDesc f) (rootSeqDesc_pairwise) ⟨j, hj⟩
  · simp [hj]

private lemma slotSetAt_ordConnected (j : ℕ) (f : ℝ[X]) :
    Set.OrdConnected (slotSetAt j f) := by
  unfold slotSetAt
  by_cases hj : j < (rootSeqDesc f).length + 1
  · simpa [hj] using
      rootSlotInterval_ordConnected (rs := rootSeqDesc f) ⟨j, hj⟩
  · simpa [hj] using Set.ordConnected_univ

private def leftSlotSetAt (j : ℕ) (f : ℝ[X]) : Set ℝ :=
  if hj : j < (rootSeqDesc f).length then
    rootSlotInterval (rootSeqDesc f) ⟨j + 1, Nat.succ_lt_succ hj⟩
  else
    Set.univ

private lemma leftSlotSetAt_nonempty (j : ℕ) (f : ℝ[X]) :
    (leftSlotSetAt j f).Nonempty := by
  unfold leftSlotSetAt
  by_cases hj : j < (rootSeqDesc f).length
  · simpa [hj] using
      rootSlotInterval_nonempty (rs := rootSeqDesc f) (rootSeqDesc_pairwise)
        ⟨j + 1, Nat.succ_lt_succ hj⟩
  · simp [hj]

private lemma leftSlotSetAt_ordConnected (j : ℕ) (f : ℝ[X]) :
    Set.OrdConnected (leftSlotSetAt j f) := by
  unfold leftSlotSetAt
  by_cases hj : j < (rootSeqDesc f).length
  · simpa [hj] using
      rootSlotInterval_ordConnected (rs := rootSeqDesc f)
        ⟨j + 1, Nat.succ_lt_succ hj⟩
  · simpa [hj] using Set.ordConnected_univ

/-- Finite-Helly wrapper for the left-oriented shifted-slot construction.

Once pairwise shifted root-slot intervals meet for every pair in the family,
the one-dimensional Helly property produces a common shifted-slot sequence. -/
theorem hasCommonLeftInterleaverSeq_of_pairwise_shiftedSlotIntersections
    {fs : List ℝ[X]}
    (hpair : ∀ (i k : Fin fs.length), i < k →
      ∀ j : ℕ,
        ∀ (hji : j + 1 < (rootSeqDesc (fs.get i)).length + 1)
          (hjk : j + 1 < (rootSeqDesc (fs.get k)).length + 1),
          (rootSlotInterval (rootSeqDesc (fs.get i)) ⟨j + 1, hji⟩ ∩
            rootSlotInterval (rootSeqDesc (fs.get k)) ⟨j + 1, hjk⟩).Nonempty) :
    HasCommonLeftInterleaverSeq fs := by
  intro j
  let ss : List (Set ℝ) := fs.map (leftSlotSetAt j)
  have hss_len : ss.length = fs.length := by simp [ss]
  have hne : ∀ s ∈ ss, s.Nonempty := by
    intro s hs
    rcases List.mem_map.mp hs with ⟨f, _hf, rfl⟩
    exact leftSlotSetAt_nonempty j f
  have hconn : ∀ s ∈ ss, Set.OrdConnected s := by
    intro s hs
    rcases List.mem_map.mp hs with ⟨f, _hf, rfl⟩
    exact leftSlotSetAt_ordConnected j f
  have hpair_sets : ss.Pairwise (fun s t => (s ∩ t).Nonempty) := by
    refine List.pairwise_iff_get.2 ?_
    intro i k hik
    let i' : Fin fs.length := ⟨i.1, by rw [← hss_len]; exact i.2⟩
    let k' : Fin fs.length := ⟨k.1, by rw [← hss_len]; exact k.2⟩
    have hik' : i' < k' := by simpa [i', k'] using hik
    let fi : ℝ[X] := fs.get i'
    let fk : ℝ[X] := fs.get k'
    have hget_i : ss.get i = leftSlotSetAt j fi := by simp [ss, i', fi, List.get_eq_getElem]
    have hget_k : ss.get k = leftSlotSetAt j fk := by simp [ss, k', fk, List.get_eq_getElem]
    rw [hget_i, hget_k]
    by_cases hjfi : j < (rootSeqDesc fi).length
    · by_cases hjfk : j < (rootSeqDesc fk).length
      · rw [show leftSlotSetAt j fi =
            rootSlotInterval (rootSeqDesc fi) ⟨j + 1, Nat.succ_lt_succ hjfi⟩ by
              simp [leftSlotSetAt, hjfi],
          show leftSlotSetAt j fk =
            rootSlotInterval (rootSeqDesc fk) ⟨j + 1, Nat.succ_lt_succ hjfk⟩ by
              simp [leftSlotSetAt, hjfk]]
        simpa [fi, fk] using
          hpair i' k' hik' j (Nat.succ_lt_succ hjfi) (Nat.succ_lt_succ hjfk)
      · simpa [leftSlotSetAt, hjfi, hjfk] using
          rootSlotInterval_nonempty (rs := rootSeqDesc fi) (rootSeqDesc_pairwise)
            ⟨j + 1, Nat.succ_lt_succ hjfi⟩
    · by_cases hjfk : j < (rootSeqDesc fk).length
      · simpa [leftSlotSetAt, hjfi, hjfk] using
          rootSlotInterval_nonempty (rs := rootSeqDesc fk) (rootSeqDesc_pairwise)
            ⟨j + 1, Nat.succ_lt_succ hjfk⟩
      · simp [leftSlotSetAt, hjfi, hjfk]
  rcases listInter_nonempty_of_pairwise_ordConnected ss hne hconn hpair_sets with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  intro f hf hjf
  have hx_all := mem_listInter.mp hx
  have hmem_slot : x ∈ leftSlotSetAt j f := by grind
  have hj : j < (rootSeqDesc f).length := Nat.lt_of_succ_lt_succ hjf
  simpa [leftSlotSetAt, hj] using hmem_slot

/-- Atomic shifted-slot membership input for a left `Prec` relation.

This is the direct left-oriented analogue of
`CommonInterleaver.RootSlots.mem_rootSlotInterval_of_prec`:
if `Prec h f`, then each descending root of the inner polynomial `h` lies in
the shifted slot of the outer polynomial `f`. -/
def PrecLeftShiftedSlotStatement : Prop :=
  ∀ {h f : ℝ[X]} (hhf : Prec h f) (j : Fin h.natDegree),
    (rootSeqDesc h).get ⟨j.1, by
      simp [rootSeqDesc_length hhf.1.2, j.2]⟩ ∈
      rootSlotInterval (rootSeqDesc f)
        ⟨j.1 + 1, by
          have hdeg := hhf.natDegree_le
          have hjf : j.1 < f.natDegree := lt_of_lt_of_le j.2 hdeg
          simpa [rootSeqDesc_length hhf.2.1.2] using Nat.succ_lt_succ hjf⟩

/-- Atomic left `Prec` shifted-slot membership. -/
theorem precLeftShiftedSlot : PrecLeftShiftedSlotStatement := by
  intro h f hhf j
  exact CommonInterleaver.RootSlots.mem_shifted_rootSlotInterval_of_prec hhf j

/-- Geometric shifted-slot consequence of a common left interleaver.

This is the remaining local geometric input in the left-oriented finite-family
upgrade: if `h` is a common left interleaver of `f` and `g`, then the shifted
root slots of `f` and `g` meet. -/
def CommonLeftInterleaverShiftedSlotStatement : Prop :=
  ∀ {h f g : ℝ[X]},
    Prec h f →
    Prec h g →
    ∀ j : ℕ,
      ∀ (hjf : j + 1 < (rootSeqDesc f).length + 1)
        (hjg : j + 1 < (rootSeqDesc g).length + 1),
        (rootSlotInterval (rootSeqDesc f) ⟨j + 1, hjf⟩ ∩
          rootSlotInterval (rootSeqDesc g) ⟨j + 1, hjg⟩).Nonempty

/-- The common-left-interleaver shifted-slot statement follows from the atomic
left `Prec` shifted-slot membership input. -/
theorem commonLeftInterleaverShiftedSlot_of_precLeft
    (hleft : PrecLeftShiftedSlotStatement) :
    CommonLeftInterleaverShiftedSlotStatement := by
  intro h f g hhf hhg j hjf hjg
  let jf : Fin ((rootSeqDesc f).length + 1) := ⟨j + 1, hjf⟩
  let jg : Fin ((rootSeqDesc g).length + 1) := ⟨j + 1, hjg⟩
  change (rootSlotInterval (rootSeqDesc f) jf ∩
    rootSlotInterval (rootSeqDesc g) jg).Nonempty
  have hhf_lower := hhf.natDegree_le
  have hhf_upper := hhf.natDegree_le_succ
  have hhg_lower := hhg.natDegree_le
  have hhg_upper := hhg.natDegree_le_succ
  by_cases hjh : j < h.natDegree
  · let jh : Fin h.natDegree := ⟨j, hjh⟩
    let x : ℝ := (rootSeqDesc h).get ⟨j, by
      simpa [rootSeqDesc_length hhf.1.2] using hjh⟩
    have hmem_f : x ∈ rootSlotInterval (rootSeqDesc f) jf := by
      simpa [x, jf, jh] using hleft hhf jh
    have hmem_g : x ∈ rootSlotInterval (rootSeqDesc g) jg := by
      simpa [x, jg, jh] using hleft hhg jh
    exact ⟨x, ⟨hmem_f, hmem_g⟩⟩
  · have hjf_nat : j < f.natDegree := by
      have hjf' : j < (rootSeqDesc f).length := Nat.lt_of_succ_lt_succ hjf
      simpa [rootSeqDesc_length hhf.2.1.2] using hjf'
    have hjg_nat : j < g.natDegree := by
      have hjg' : j < (rootSeqDesc g).length := Nat.lt_of_succ_lt_succ hjg
      simpa [rootSeqDesc_length hhg.2.1.2] using hjg'
    have hj_eq_h : j = h.natDegree := by lia
    have hf_eq_h : f.natDegree = h.natDegree + 1 := by lia
    have hg_eq_h : g.natDegree = h.natDegree + 1 := by lia
    have hf_pos : 0 < f.natDegree := by lia
    have hg_pos : 0 < g.natDegree := by lia
    have hrevf_ne : (rootSeqDesc f).reverse ≠ [] :=
      CommonInterleaver.rootSeqDesc_reverse_ne_nil_of_natDegree_pos hhf.2.1.2 hf_pos
    have hrevg_ne : (rootSeqDesc g).reverse ≠ [] :=
      CommonInterleaver.rootSeqDesc_reverse_ne_nil_of_natDegree_pos hhg.2.1.2 hg_pos
    let af : ℝ := ((rootSeqDesc f).reverse).get ⟨0, by grind⟩
    let ag : ℝ := ((rootSeqDesc g).reverse).get ⟨0, by grind⟩
    have hslot_f : rootSlotInterval (rootSeqDesc f) jf = Set.Iic af := by
      simpa [af, jf, hj_eq_h, hf_eq_h, hhf.2.1.2] using
        CommonInterleaver.RootSlots.rootSlotInterval_last_eq_reverse_get_zero
          (rs := rootSeqDesc f) (List.reverse_ne_nil_iff.mp hrevf_ne)
    have hslot_g : rootSlotInterval (rootSeqDesc g) jg = Set.Iic ag := by
      simpa [ag, jg, hj_eq_h, hg_eq_h, hhg.2.1.2] using
        CommonInterleaver.RootSlots.rootSlotInterval_last_eq_reverse_get_zero
          (rs := rootSeqDesc g) (List.reverse_ne_nil_iff.mp hrevg_ne)
    simp_all

/-- Common-left-interleaver shifted-slot intersections. -/
theorem commonLeftInterleaverShiftedSlot :
    CommonLeftInterleaverShiftedSlotStatement :=
  commonLeftInterleaverShiftedSlot_of_precLeft precLeftShiftedSlot

/-- A pairwise common-left-interleaver hypothesis gives the pairwise shifted
root-slot intersections, assuming the geometric shifted-slot input. -/
theorem pairwise_shiftedSlotIntersections_of_pairwiseHasCommonLeftInterleaver
    {fs : List ℝ[X]}
    (hslot : CommonLeftInterleaverShiftedSlotStatement)
    (hpair : PairwiseHasCommonLeftInterleaver fs) :
    ∀ (i k : Fin fs.length), i < k →
      ∀ j : ℕ,
        ∀ (hji : j + 1 < (rootSeqDesc (fs.get i)).length + 1)
          (hjk : j + 1 < (rootSeqDesc (fs.get k)).length + 1),
          (rootSlotInterval (rootSeqDesc (fs.get i)) ⟨j + 1, hji⟩ ∩
            rootSlotInterval (rootSeqDesc (fs.get k)) ⟨j + 1, hjk⟩).Nonempty := by
  intro i k hik j hji hjk
  obtain ⟨h, hhi, hhk⟩ := hpair i k hik
  exact hslot hhi hhk j hji hjk

/-- Finite-family shifted-slot sequence from pairwise common left interleavers,
modulo the local geometric shifted-slot input. -/
theorem hasCommonLeftInterleaverSeq_of_pairwiseHasCommonLeftInterleaver_of_shiftedSlot
    {fs : List ℝ[X]}
    (hslot : CommonLeftInterleaverShiftedSlotStatement)
    (hpair : PairwiseHasCommonLeftInterleaver fs) :
    HasCommonLeftInterleaverSeq fs :=
  hasCommonLeftInterleaverSeq_of_pairwise_shiftedSlotIntersections
    (pairwise_shiftedSlotIntersections_of_pairwiseHasCommonLeftInterleaver hslot hpair)

/-- Finite-family shifted-slot sequence from pairwise common left interleavers. -/
theorem hasCommonLeftInterleaverSeq_of_pairwiseHasCommonLeftInterleaver
    {fs : List ℝ[X]}
    (hpair : PairwiseHasCommonLeftInterleaver fs) :
    HasCommonLeftInterleaverSeq fs :=
  hasCommonLeftInterleaverSeq_of_pairwiseHasCommonLeftInterleaver_of_shiftedSlot
    commonLeftInterleaverShiftedSlot hpair

/-- Chudnovsky--Seymour `3.6.2 → 3.6.3`, in the formulation needed for the
product-sum theorem: pairwise common interleavers imply a global common
interleaving sequence. The intended proof follows the reference in
`References/proof_of_the_lemma_chudnovsky_seymour_2007.{md,tex}` via the
finite Helly property for intervals on `ℝ`. -/
theorem hasCommonInterleaverSeq_of_pairwiseHasCommonInterleaver
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, f.Splits)
    (hpair : PairwiseHasCommonInterleaver fs) :
    HasCommonInterleaverSeq fs := by
  intro j
  let ss : List (Set ℝ) := fs.map (slotSetAt j)
  have hss_len : ss.length = fs.length := by simp [ss]
  have hne : ∀ s ∈ ss, s.Nonempty := by
    intro s hs
    rcases List.mem_map.mp hs with ⟨f, hf, rfl⟩
    exact slotSetAt_nonempty j f
  have hconn : ∀ s ∈ ss, Set.OrdConnected s := by
    intro s hs
    rcases List.mem_map.mp hs with ⟨f, hf, rfl⟩
    exact slotSetAt_ordConnected j f
  have hpair_sets : ss.Pairwise (fun s t => (s ∩ t).Nonempty) := by
    refine List.pairwise_iff_get.2 ?_
    intro i k hik
    let i' : Fin fs.length := ⟨i.1, by lia⟩
    let k' : Fin fs.length := ⟨k.1, by lia⟩
    have hik' : i' < k' := by simpa [i', k'] using hik
    let fi : ℝ[X] := fs.get i'
    let fk : ℝ[X] := fs.get k'
    have hget_i : ss.get i = slotSetAt j fi := by simp [ss, i', fi, List.get_eq_getElem]
    have hget_k : ss.get k = slotSetAt j fk := by simp [ss, k', fk, List.get_eq_getElem]
    rw [hget_i, hget_k]
    have hfi_rr : fi.Splits := hrr fi (List.get_mem _ _)
    have hfk_rr : fk.Splits := hrr fk (List.get_mem _ _)
    by_cases hjfi : j < (rootSeqDesc fi).length + 1
    · by_cases hjfk : j < (rootSeqDesc fk).length + 1
      · have hjfi' : j < fi.natDegree + 1 := by simpa [hfi_rr] using hjfi
        have hjfk' : j < fk.natDegree + 1 := by simpa [rootSeqDesc_length hfk_rr] using hjfk
        rcases hpair i' k' hik' with ⟨hh, hfi_h, hfk_h⟩
        simpa [slotSetAt, hjfi, hjfk] using!
          (rootSlotInterval_inter_nonempty_of_commonInterleaver hfi_h hfk_h j hjfi' hjfk')
      · simpa [slotSetAt, hjfi, hjfk] using
          (rootSlotInterval_nonempty (rs := rootSeqDesc fi) (rootSeqDesc_pairwise) ⟨j, hjfi⟩)
    · by_cases hjfk : j < (rootSeqDesc fk).length + 1
      · simpa [slotSetAt, hjfi, hjfk] using
          (rootSlotInterval_nonempty (rs := rootSeqDesc fk) (rootSeqDesc_pairwise) ⟨j, hjfk⟩)
      · simp [slotSetAt, hjfi, hjfk]
  rcases listInter_nonempty_of_pairwise_ordConnected ss hne hconn hpair_sets with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  intro f hf hjf
  have hx_all := (mem_listInter.mp hx)
  have hmem_slot : x ∈ slotSetAt j f := by grind
  simpa [slotSetAt, hjf] using hmem_slot

end
end RealRooted
