import RealRooted.CommonInterleaver.FamilyUpgrade

/-!
# Common interleavers and Chudnovsky--Seymour theorem

The pairwise common-interleaver APIs and slot-data closure theorems. The
descending-root construction and finite-family upgrades live in dedicated
children.
-/

open Polynomial

noncomputable section

namespace RealRooted

section

/-- Public wrapper around the descending-root polynomial constructor used in
slot-based closure arguments. -/
def polyOfDescRootsDesc (xs : List ℝ) : ℝ[X] :=
  CommonInterleaver.polyOfDescRoots xs

@[simp] theorem roots_polyOfDescRootsDesc (xs : List ℝ) :
    (polyOfDescRootsDesc xs).roots = (↑xs : Multiset ℝ) := by
  simpa [polyOfDescRootsDesc] using CommonInterleaver.roots_polyOfDescRoots xs

@[simp] theorem rootSeqDesc_polyOfDescRootsDesc_eq
    {xs : List ℝ} (hxs : xs.Pairwise (· ≥ ·)) :
    rootSeqDesc (polyOfDescRootsDesc xs) = xs := by
  simpa [polyOfDescRootsDesc] using
    CommonInterleaver.rootSeqDesc_polyOfDescRoots_eq hxs

/-- Public lower-bound wrapper for a point lying in a root slot. -/
theorem rootSlot_lower_bound_of_mem
    {rs : List ℝ} (hrs : rs ≠ []) {j : ℕ} (hj : j < rs.length) {x : ℝ}
    (hx : x ∈ rootSlotInterval rs ⟨j, by lia⟩) :
    rs.get ⟨j, hj⟩ ≤ x :=
  CommonInterleaver.RootSlots.rootSlot_lower_bound hrs hj hx

/-- Public upper-bound wrapper for a point lying in a root slot. -/
theorem rootSlot_upper_bound_of_mem
    {rs : List ℝ} (hrs : rs ≠ []) {j : ℕ} (hj0 : 0 < j) (hj : j ≤ rs.length)
    {x : ℝ}
    (hx : x ∈ rootSlotInterval rs ⟨j, by lia⟩) :
    x ≤ rs.get ⟨j - 1, by lia⟩ :=
  CommonInterleaver.RootSlots.rootSlot_upper_bound hrs hj0 hj hx

/-- Points in later root slots are weakly below points in earlier root slots.
This public wrapper exposes the monotonicity fact used in the slot-based
common-interleaver construction. -/
theorem le_of_mem_rootSlotInterval_of_lt
    {rs : List ℝ} (hrs_ne : rs ≠ []) (hrs : rs.Pairwise (· ≥ ·))
    {i j : ℕ} (hij : i < j) (hj : j < rs.length + 1)
    {x y : ℝ}
    (hx : x ∈ rootSlotInterval rs ⟨i, by lia⟩)
    (hy : y ∈ rootSlotInterval rs ⟨j, hj⟩) :
    y ≤ x :=
  CommonInterleaver.RootSlots.le_of_mem_rootSlots_of_lt hrs_ne hrs hij hj hx hy

private lemma get_ofFn_eq_apply
    {α : Type*} {n : ℕ} {x : Fin n → α} {xs : List α}
    (hxs : xs = List.ofFn x) {j : ℕ} (hj : j < xs.length) :
    xs.get ⟨j, hj⟩ = x ⟨j, by simpa [hxs] using hj⟩ := by
  subst xs
  change (List.ofFn x)[j] = x ⟨j, by simpa using hj⟩
  convert (List.getElem_ofFn (f := x) (i := j) (by simpa using hj)) using 2

private lemma pairwise_ge_of_rootSlot_points
    {f : ℝ[X]} (hf : f.Splits) {n : ℕ} (hn : n = f.natDegree + 1)
    (x : Fin n → ℝ)
    (hslot : ∀ j (hj : j < n),
      x ⟨j, hj⟩ ∈ rootSlotInterval (rootSeqDesc f)
        ⟨j, by
          have : j < f.natDegree + 1 := by simpa [hn] using hj
          simpa [rootSeqDesc_length hf] using this⟩) :
    (List.ofFn x).Pairwise (· ≥ ·) := by
  refine List.pairwise_ofFn.2 ?_
  intro i j hij
  have hroot_ne : rootSeqDesc f ≠ [] :=
    CommonInterleaver.rootSeqDesc_ne_nil_of_natDegree_pos hf (by lia)
  have hi_slot : i.1 < (rootSeqDesc f).length + 1 := by
    have : i.1 < f.natDegree + 1 := by simpa [hn] using i.2
    simpa [rootSeqDesc_length hf] using this
  have hj_slot : j.1 < (rootSeqDesc f).length + 1 := by
    have : j.1 < f.natDegree + 1 := by simpa [hn] using j.2
    simpa [rootSeqDesc_length hf] using this
  have hxi : x i ∈ rootSlotInterval (rootSeqDesc f) ⟨i.1, hi_slot⟩ := by
    simpa using hslot i.1 i.2
  have hxj : x j ∈ rootSlotInterval (rootSeqDesc f) ⟨j.1, hj_slot⟩ := by
    simpa using hslot j.1 j.2
  exact
    le_of_mem_rootSlotInterval_of_lt
      (rs := rootSeqDesc f)
      hroot_ne
      rootSeqDesc_pairwise
      (i := i.1) (j := j.1)
      (by simpa using hij)
      (by simpa using hj_slot)
      hxi hxj

private lemma pairwise_ge_of_shifted_rootSlot_points
    {f : ℝ[X]} (hf : f.Splits) {n : ℕ} (hn : n = f.natDegree)
    (x : Fin n → ℝ)
    (hslot : ∀ j (hj : j < n),
      x ⟨j, hj⟩ ∈ rootSlotInterval (rootSeqDesc f)
        ⟨j + 1, by
          have : j < f.natDegree := by simpa [hn] using hj
          simpa [rootSeqDesc_length hf] using Nat.succ_lt_succ this⟩) :
    (List.ofFn x).Pairwise (· ≥ ·) := by
  refine List.pairwise_ofFn.2 ?_
  intro i j hij
  have hroot_ne : rootSeqDesc f ≠ [] :=
    CommonInterleaver.rootSeqDesc_ne_nil_of_natDegree_pos hf (by lia)
  have hi_slot : i.1 + 1 < (rootSeqDesc f).length + 1 := by
    have : i.1 < f.natDegree := by simpa [hn] using i.2
    simpa [rootSeqDesc_length hf] using Nat.succ_lt_succ this
  have hj_slot : j.1 + 1 < (rootSeqDesc f).length + 1 := by
    have : j.1 < f.natDegree := by simpa [hn] using j.2
    simpa [rootSeqDesc_length hf] using Nat.succ_lt_succ this
  have hxi : x i ∈ rootSlotInterval (rootSeqDesc f) ⟨i.1 + 1, hi_slot⟩ := by
    simpa using hslot i.1 i.2
  have hxj : x j ∈ rootSlotInterval (rootSeqDesc f) ⟨j.1 + 1, hj_slot⟩ := by
    simpa using hslot j.1 j.2
  exact
    le_of_mem_rootSlotInterval_of_lt
      (rs := rootSeqDesc f)
      hroot_ne
      rootSeqDesc_pairwise
      (i := i.1 + 1) (j := j.1 + 1)
      (by lia)
      (by simpa using hj_slot)
      hxi hxj

/-- In a `Prec` witness, the `j`th descending root of the right polynomial lies
in the `j`th admissible slot of the left polynomial. -/
theorem mem_rootSlotInterval_of_prec_desc
    {f g : ℝ[X]} (hfg : Prec f g) (j : Fin g.natDegree) :
    (rootSeqDesc g).get ⟨j.1, by
      rcases hfg with ⟨_, hg, _, _, _, _, _, _, _⟩
      simp [rootSeqDesc, card_roots_of_splits hg.2]⟩ ∈ rootSlotInterval (rootSeqDesc f)
      ⟨j.1, by
        have hdeg := hfg.natDegree_le_succ
        rcases hfg with ⟨hf, hg, _, _, _, _, _, _, _⟩
        simpa [hf, hg] using lt_of_lt_of_le j.2 hdeg⟩ :=
  CommonInterleaver.RootSlots.mem_rootSlotInterval_of_prec hfg j

/-- A common right interleaver gives matching shifted-slot intersections for a
close-degree pair.  For all but the last shifted slot we use the corresponding
root of the common right interleaver; the final lower-tail slots meet
automatically. -/
theorem shiftedSlotIntersections_of_commonInterleaver
    {f g h : ℝ[X]}
    (hfh : Prec f h) (hgh : Prec g h) :
    ∀ j : ℕ,
      ∀ (hjf : j + 1 < (rootSeqDesc f).length + 1)
        (hjg : j + 1 < (rootSeqDesc g).length + 1),
        (rootSlotInterval (rootSeqDesc f) ⟨j + 1, hjf⟩ ∩
          rootSlotInterval (rootSeqDesc g) ⟨j + 1, hjg⟩).Nonempty := by
  intro j hjf hjg
  let jf : Fin ((rootSeqDesc f).length + 1) := ⟨j + 1, hjf⟩
  let jg : Fin ((rootSeqDesc g).length + 1) := ⟨j + 1, hjg⟩
  change (rootSlotInterval (rootSeqDesc f) jf ∩
    rootSlotInterval (rootSeqDesc g) jg).Nonempty
  have hfh_lower := hfh.natDegree_le
  have hfh_upper := hfh.natDegree_le_succ
  have hgh_lower := hgh.natDegree_le
  have hgh_upper := hgh.natDegree_le_succ
  have hjf_nat : j < f.natDegree := by
    have hjf' : j < (rootSeqDesc f).length := Nat.lt_of_succ_lt_succ hjf
    simpa [rootSeqDesc_length hfh.1.2] using hjf'
  have hjg_nat : j < g.natDegree := by
    have hjg' : j < (rootSeqDesc g).length := Nat.lt_of_succ_lt_succ hjg
    simpa [rootSeqDesc_length hgh.1.2] using hjg'
  by_cases hjh : j + 1 < h.natDegree
  · let jh : Fin h.natDegree := ⟨j + 1, hjh⟩
    let x : ℝ := (rootSeqDesc h).get ⟨j + 1, by
      simpa [rootSeqDesc_length hfh.2.1.2] using hjh⟩
    have hmem_f : x ∈ rootSlotInterval (rootSeqDesc f) jf := by
      simpa [x, jf, jh] using mem_rootSlotInterval_of_prec_desc hfh jh
    have hmem_g : x ∈ rootSlotInterval (rootSeqDesc g) jg := by
      simpa [x, jg, jh] using mem_rootSlotInterval_of_prec_desc hgh jh
    exact ⟨x, hmem_f, hmem_g⟩
  · have hjh_le : h.natDegree ≤ j + 1 := by exact Nat.le_of_not_gt hjh
    have hjh_ge : j + 1 ≤ h.natDegree := by exact (Nat.succ_le_iff.mpr hjf_nat).trans hfh_lower
    have hjh_eq : j + 1 = h.natDegree := le_antisymm hjh_ge hjh_le
    have hf_eq_h : f.natDegree = h.natDegree := by lia
    have hg_eq_h : g.natDegree = h.natDegree := by lia
    have hf_pos : 0 < f.natDegree := by lia
    have hg_pos : 0 < g.natDegree := by lia
    have hrevf_ne : (rootSeqDesc f).reverse ≠ [] :=
      CommonInterleaver.rootSeqDesc_reverse_ne_nil_of_natDegree_pos hfh.1.2 hf_pos
    have hrevg_ne : (rootSeqDesc g).reverse ≠ [] :=
      CommonInterleaver.rootSeqDesc_reverse_ne_nil_of_natDegree_pos hgh.1.2 hg_pos
    let af : ℝ := ((rootSeqDesc f).reverse).get ⟨0, by grind⟩
    let ag : ℝ := ((rootSeqDesc g).reverse).get ⟨0, by grind⟩
    have hslot_f : rootSlotInterval (rootSeqDesc f) jf = Set.Iic af := by
      simpa [af, jf, hjh_eq, hf_eq_h, hfh.1.2] using
        CommonInterleaver.RootSlots.rootSlotInterval_last_eq_reverse_get_zero
          (rs := rootSeqDesc f) (List.reverse_ne_nil_iff.mp hrevf_ne)
    have hslot_g : rootSlotInterval (rootSeqDesc g) jg = Set.Iic ag := by
      simpa [ag, jg, hjh_eq, hg_eq_h, hgh.1.2] using
        CommonInterleaver.RootSlots.rootSlotInterval_last_eq_reverse_get_zero
          (rs := rootSeqDesc g) (List.reverse_ne_nil_iff.mp hrevg_ne)
    rw [hslot_f, hslot_g]
    exact ⟨min af ag, min_le_left af ag, min_le_right af ag⟩

/-- Slot data against `rootSeqDesc f` reconstructs a `Prec` witness with the
descending-root polynomial built from those slot choices. -/
theorem prec_of_slots_polyOfDescRootsDesc
    {f : ℝ[X]} {xs : List ℝ} (hf₀ : f ≠ 0) (hf : f.Splits)
    (hxs : xs.Pairwise (· ≥ ·))
    (hdeg_lo : f.natDegree ≤ xs.length)
    (hdeg_hi : xs.length ≤ f.natDegree + 1)
    (hslot : ∀ j (hj : j < xs.length),
      xs.get ⟨j, hj⟩ ∈ rootSlotInterval (rootSeqDesc f)
        ⟨j, by
          have : j < f.natDegree + 1 := lt_of_lt_of_le hj hdeg_hi
          simpa [hf] using this⟩) :
    Prec f (polyOfDescRootsDesc xs) := by
  simpa [polyOfDescRootsDesc] using
    CommonInterleaver.prec_of_slots_polyOfDescRoots hf₀ hf hxs hdeg_lo hdeg_hi hslot

/-- Shifted slot data against `rootSeqDesc f` reconstructs a left `Prec` witness
with the descending-root polynomial built from those slot choices. -/
theorem prec_left_of_shifted_slots_polyOfDescRootsDesc
    {f : ℝ[X]} {xs : List ℝ} (hf₀ : f ≠ 0) (hf : f.Splits)
    (hxs : xs.Pairwise (· ≥ ·))
    (hdeg_lo : xs.length ≤ f.natDegree)
    (hdeg_hi : f.natDegree ≤ xs.length + 1)
    (hslot : ∀ j (hj : j < xs.length),
      xs.get ⟨j, hj⟩ ∈ rootSlotInterval (rootSeqDesc f)
        ⟨j + 1, by
          have : j < f.natDegree := lt_of_lt_of_le hj hdeg_lo
          simpa [rootSeqDesc_length hf] using Nat.succ_lt_succ this⟩) :
    Prec (polyOfDescRootsDesc xs) f := by
  simpa [polyOfDescRootsDesc] using
    CommonInterleaver.prec_left_of_shifted_slots_polyOfDescRoots
      hf₀ hf hxs hdeg_lo hdeg_hi hslot

private lemma prec_polyOfDescRootsDesc_of_ofFn_slots
    {f : ℝ[X]} {n : ℕ} {x : Fin n → ℝ}
    (hf₀ : f ≠ 0) (hf : f.Splits)
    (hxs : (List.ofFn x).Pairwise (· ≥ ·))
    (hdeg_lo : f.natDegree ≤ n)
    (hdeg_hi : n ≤ f.natDegree + 1)
    (hslot : ∀ j (hj : j < n),
      x ⟨j, hj⟩ ∈ rootSlotInterval (rootSeqDesc f)
        ⟨j, by
          have : j < f.natDegree + 1 := lt_of_lt_of_le hj hdeg_hi
          simpa [rootSeqDesc_length hf] using this⟩) :
    Prec f (polyOfDescRootsDesc (List.ofFn x)) := by
  refine
    prec_of_slots_polyOfDescRootsDesc hf₀ hf hxs
      (by simpa using hdeg_lo)
      (by simpa using hdeg_hi)
      ?_
  intro j hj
  rw [get_ofFn_eq_apply (x := x) (xs := List.ofFn x) rfl hj]
  exact hslot j (by simpa using hj)

/-- Common abstraction behind the same- and succ-degree slot-intersection
constructors. -/
theorem pairHasCommonInterleaver_of_slotIntersections
    {f g : ℝ[X]} (hf₀ : f ≠ 0) (hg₀ : g ≠ 0) (hf : f.Splits) (hg : g.Splits)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1)
    (hslot :
      ∀ j (hj : j < f.natDegree + 1),
        (rootSlotInterval (rootSeqDesc f) ⟨j, by simpa [hf] using hj⟩ ∩
          rootSlotInterval (rootSeqDesc g)
            ⟨j, by
              have : j < g.natDegree + 1 := by lia
              simpa [hg] using this⟩).Nonempty) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  classical
  let n : ℕ := f.natDegree + 1
  let x : Fin n → ℝ := fun j =>
    Classical.choose (hslot j.1 (by simpa [n] using j.2))
  let xs : List ℝ := List.ofFn x
  have hxs_pair : xs.Pairwise (· ≥ ·) := by
    refine pairwise_ge_of_rootSlot_points hf (n := n) (by simp [n]) x ?_
    intro j hj
    have hraw := (Classical.choose_spec (hslot j (by simpa [n] using hj))).1
    simpa [x] using hraw
  let h : ℝ[X] := polyOfDescRootsDesc xs
  refine ⟨h, ?_, ?_⟩
  · simpa [h, xs] using
      prec_polyOfDescRootsDesc_of_ofFn_slots hf₀ hf hxs_pair
        (by simp [n]) (by simp [n])
        (fun j hj => by
          have hraw := (Classical.choose_spec (hslot j (by simpa [n] using hj))).1
          simpa [x] using hraw)
  · simpa [h, xs] using
      prec_polyOfDescRootsDesc_of_ofFn_slots hg₀ hg hxs_pair
        (by simp only [n]; lia) (by simp only [n]; lia)
        (fun j hj => by
          have hraw := (Classical.choose_spec (hslot j (by simpa [n] using hj))).2
          simpa [x] using hraw)

/-- Matching nonempty shifted root-slot intersections for two close-degree
real-rooted polynomials produce a common left interleaver.  This is the
left-oriented analogue of `pairHasCommonInterleaver_of_slotIntersections`. -/
theorem pairHasCommonLeftInterleaver_of_shiftedSlotIntersections
    {f g : ℝ[X]} (hf₀ : f ≠ 0) (hg₀ : g ≠ 0) (hf : f.Splits) (hg : g.Splits)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1)
    (hslot :
      ∀ j (hj : j < f.natDegree),
        (rootSlotInterval (rootSeqDesc f)
            ⟨j + 1, by simpa [rootSeqDesc_length hf] using Nat.succ_lt_succ hj⟩ ∩
          rootSlotInterval (rootSeqDesc g)
            ⟨j + 1, by
              have : j < g.natDegree := lt_of_lt_of_le hj hdeg_lo
              simpa [rootSeqDesc_length hg] using Nat.succ_lt_succ this⟩).Nonempty) :
    ∃ h : ℝ[X], Prec h f ∧ Prec h g := by
  classical
  let n : ℕ := f.natDegree
  let x : Fin n → ℝ := fun j =>
    Classical.choose (hslot j.1 (by exact j.2))
  let xs : List ℝ := List.ofFn x
  have hxs_pair : xs.Pairwise (· ≥ ·) := by
    refine pairwise_ge_of_shifted_rootSlot_points hf (n := n) (by simp [n]) x ?_
    intro j hj
    have hraw := (Classical.choose_spec (hslot j (by simpa [n] using hj))).1
    simpa [x] using hraw
  let h : ℝ[X] := polyOfDescRootsDesc xs
  refine ⟨h, ?_, ?_⟩
  · simpa [h, xs] using
      prec_left_of_shifted_slots_polyOfDescRootsDesc hf₀ hf hxs_pair
        (by simp [xs, n]) (by simp [xs, n])
        (fun j hj => by
          have hjf : j < f.natDegree := by simpa [xs, n] using hj
          have hraw := (Classical.choose_spec (hslot j hjf)).1
          simpa [x, xs] using hraw)
  · simpa [h, xs] using
      prec_left_of_shifted_slots_polyOfDescRootsDesc hg₀ hg hxs_pair
        (by simpa [xs, n] using hdeg_lo) (by simpa [xs, n] using hdeg_hi)
        (fun j hj => by
          have hjf : j < f.natDegree := by simpa [xs, n] using hj
          have hraw := (Classical.choose_spec (hslot j hjf)).2
          simpa [x, xs] using hraw)

/-- A common right interleaver for a close-degree pair produces a common left
interleaver. -/
theorem pairHasCommonLeftInterleaver_of_commonInterleaver
    {f g h : ℝ[X]}
    (hfh : Prec f h) (hgh : Prec g h)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1) :
    ∃ l : ℝ[X], Prec l f ∧ Prec l g :=
  pairHasCommonLeftInterleaver_of_shiftedSlotIntersections
    hfh.1.1 hgh.1.1 hfh.1.2 hgh.1.2 hdeg_lo hdeg_hi <|
    fun j hj => by
      have hjf : j + 1 < (rootSeqDesc f).length + 1 := by
        simpa [rootSeqDesc_length hfh.1.2] using Nat.succ_lt_succ hj
      have hjg : j + 1 < (rootSeqDesc g).length + 1 := by
        have : j < g.natDegree := lt_of_lt_of_le hj hdeg_lo
        simpa [rootSeqDesc_length hgh.1.2] using Nat.succ_lt_succ this
      exact shiftedSlotIntersections_of_commonInterleaver hfh hgh j hjf hjg

/-- Matching nonempty root-slot intersections for two same-degree real-rooted
polynomials produce a common right interleaver.  This isolates the constructive
part of the same-degree Chudnovsky--Seymour gap from the remaining
mathematical slot-intersection theorem. -/
theorem pairHasCommonInterleaver_of_sameDegree_slotIntersections
    {f g : ℝ[X]} (hf₀ : f ≠ 0) (hg₀ : g ≠ 0) (hf : f.Splits) (hg : g.Splits)
    (hdeg : g.natDegree = f.natDegree)
    (hslot :
      ∀ j (hj : j < f.natDegree + 1),
        (rootSlotInterval (rootSeqDesc f) ⟨j, by simpa [hf] using hj⟩ ∩
          rootSlotInterval (rootSeqDesc g)
            ⟨j, by
              have : j < g.natDegree + 1 := by lia
              simpa [hg] using this⟩).Nonempty) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  pairHasCommonInterleaver_of_slotIntersections hf₀ hg₀ hf hg
    hdeg.ge (by lia) hslot

/-- Matching nonempty root-slot intersections for a succ-degree pair of
real-rooted polynomials produce a common right interleaver.  When `g` has
degree exactly one larger than `f`, the constructed interleaver has degree
`g.natDegree`. -/
theorem pairHasCommonInterleaver_of_succDegree_slotIntersections
    {f g : ℝ[X]} (hf₀ : f ≠ 0) (hg₀ : g ≠ 0) (hf : f.Splits) (hg : g.Splits)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hslot :
      ∀ j (hj : j < f.natDegree + 1),
        (rootSlotInterval (rootSeqDesc f) ⟨j, by simpa [hf] using hj⟩ ∩
          rootSlotInterval (rootSeqDesc g)
            ⟨j, by
              have : j < g.natDegree + 1 := by lia
              simpa [hg] using this⟩).Nonempty) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  pairHasCommonInterleaver_of_slotIntersections hf₀ hg₀ hf hg
    (by lia) hdeg.le hslot

/-- Succ-degree slot-intersection constructor with the degree equality oriented
as `f.natDegree + 1 = g.natDegree`. -/
theorem pairHasCommonInterleaver_of_natDegree_succ_eq_slotIntersections
    {f g : ℝ[X]} (hf₀ : f ≠ 0) (hg₀ : g ≠ 0) (hf : f.Splits) (hg : g.Splits)
    (hdeg : f.natDegree + 1 = g.natDegree)
    (hslot :
      ∀ j (hj : j < f.natDegree + 1),
        (rootSlotInterval (rootSeqDesc f) ⟨j, by simpa [hf] using hj⟩ ∩
          rootSlotInterval (rootSeqDesc g)
            ⟨j, by
              have : j < g.natDegree + 1 := by lia
              simpa [hg] using this⟩).Nonempty) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  pairHasCommonInterleaver_of_succDegree_slotIntersections
    hf₀ hg₀ hf hg hdeg.symm hslot

/-- Same-degree slot-intersection constructor with the degree equality oriented
as `f.natDegree = g.natDegree`. -/
theorem pairHasCommonInterleaver_of_natDegree_eq_slotIntersections
    {f g : ℝ[X]} (hf₀ : f ≠ 0) (hg₀ : g ≠ 0) (hf : f.Splits) (hg : g.Splits)
    (hdeg : f.natDegree = g.natDegree)
    (hslot :
      ∀ j (hj : j < f.natDegree + 1),
        (rootSlotInterval (rootSeqDesc f) ⟨j, by simpa [hf] using hj⟩ ∩
          rootSlotInterval (rootSeqDesc g)
            ⟨j, by
              have : j < g.natDegree + 1 := by lia
              simpa [hg] using this⟩).Nonempty) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  pairHasCommonInterleaver_of_sameDegree_slotIntersections hf₀ hg₀ hf hg hdeg.symm hslot

/-- Succ-degree slot-intersection constructor taking the endpoint-reduction
slot-data hypothesis with explicit root-sequence bounds. -/
theorem pairHasCommonInterleaver_of_natDegree_succ_eq_slotData
    {f g : ℝ[X]} (hf₀ : f ≠ 0) (hg₀ : g ≠ 0) (hf : f.Splits) (hg : g.Splits)
    (hdeg : f.natDegree + 1 = g.natDegree)
    (hslot :
      ∀ j, j < f.natDegree + 1 →
        ∀ (hjf : j < (rootSeqDesc f).length + 1)
          (hjg : j < (rootSeqDesc g).length + 1),
          (rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ ∩
            rootSlotInterval (rootSeqDesc g) ⟨j, hjg⟩).Nonempty) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  pairHasCommonInterleaver_of_natDegree_succ_eq_slotIntersections
    hf₀ hg₀ hf hg hdeg (fun j hj => hslot j hj _ _)

/-- Same-degree slot-intersection constructor taking the endpoint-reduction
slot-data hypothesis with explicit root-sequence bounds. -/
theorem pairHasCommonInterleaver_of_natDegree_eq_slotData
    {f g : ℝ[X]} (hf₀ : f ≠ 0) (hg₀ : g ≠ 0) (hf : f.Splits) (hg : g.Splits)
    (hdeg : f.natDegree = g.natDegree)
    (hslot :
      ∀ j, j < f.natDegree + 1 →
        ∀ (hjf : j < (rootSeqDesc f).length + 1)
          (hjg : j < (rootSeqDesc g).length + 1),
          (rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ ∩
            rootSlotInterval (rootSeqDesc g) ⟨j, hjg⟩).Nonempty) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  pairHasCommonInterleaver_of_natDegree_eq_slotIntersections
    hf₀ hg₀ hf hg hdeg (fun j hj => hslot j hj _ _)

/-- Succ-degree slot-intersection constructor in the endpoint-reduction
slot-data shape, with degree hypothesis oriented as
`g.natDegree = f.natDegree + 1`. -/
theorem pairHasCommonInterleaver_of_succDegree_slotData
    {f g : ℝ[X]} (hf₀ : f ≠ 0) (hg₀ : g ≠ 0) (hf : f.Splits) (hg : g.Splits)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hslot :
      ∀ j, j < f.natDegree + 1 →
        ∀ (hjf : j < (rootSeqDesc f).length + 1)
          (hjg : j < (rootSeqDesc g).length + 1),
          (rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ ∩
            rootSlotInterval (rootSeqDesc g) ⟨j, hjg⟩).Nonempty) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  pairHasCommonInterleaver_of_succDegree_slotIntersections
    hf₀ hg₀ hf hg hdeg (fun j hj => hslot j hj _ _)

/-- Degree-gap wrapper for the common slot-intersection constructor. -/
theorem pairHasCommonInterleaver_of_degreeGap_slotIntersections
    {f g : ℝ[X]} (hf₀ : f ≠ 0) (hg₀ : g ≠ 0) (hf : f.Splits) (hg : g.Splits)
    (hdeg : g.natDegree = f.natDegree ∨ g.natDegree = f.natDegree + 1)
    (hslot :
      ∀ j (hj : j < f.natDegree + 1),
        (rootSlotInterval (rootSeqDesc f) ⟨j, by simpa [hf] using hj⟩ ∩
          rootSlotInterval (rootSeqDesc g)
            ⟨j, by
              have : j < g.natDegree + 1 := by rcases hdeg with hdeg | hdeg <;> lia
              simpa [hg] using this⟩).Nonempty) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  pairHasCommonInterleaver_of_slotIntersections hf₀ hg₀ hf hg
    (by rcases hdeg with hdeg | hdeg <;> lia)
    (by rcases hdeg with hdeg | hdeg <;> lia)
    hslot

/-- Degree-gap slot-data wrapper for the common interleaver constructor. -/
theorem pairHasCommonInterleaver_of_degreeGap_slotData
    {f g : ℝ[X]} (hf₀ : f ≠ 0) (hg₀ : g ≠ 0) (hf : f.Splits) (hg : g.Splits)
    (hdeg : g.natDegree = f.natDegree ∨ g.natDegree = f.natDegree + 1)
    (hslot :
      ∀ j, j < f.natDegree + 1 →
        ∀ (hjf : j < (rootSeqDesc f).length + 1)
          (hjg : j < (rootSeqDesc g).length + 1),
          (rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ ∩
            rootSlotInterval (rootSeqDesc g) ⟨j, hjg⟩).Nonempty) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  pairHasCommonInterleaver_of_degreeGap_slotIntersections
    hf₀ hg₀ hf hg hdeg (fun j hj => hslot j hj _ _)

/-- List-level packaging of the exact degree-gap slot-intersection common
interleaver constructor. -/
theorem hasCommonInterleaver_pair_of_degreeGap_slotIntersections
    {f g : ℝ[X]} (hf₀ : f ≠ 0) (hg₀ : g ≠ 0) (hf : f.Splits) (hg : g.Splits)
    (hdeg : g.natDegree = f.natDegree ∨ g.natDegree = f.natDegree + 1)
    (hslot :
      ∀ j (hj : j < f.natDegree + 1),
        (rootSlotInterval (rootSeqDesc f) ⟨j, by simpa [hf] using hj⟩ ∩
          rootSlotInterval (rootSeqDesc g)
            ⟨j, by
              have : j < g.natDegree + 1 := by rcases hdeg with hdeg | hdeg <;> lia
              simpa [hg] using this⟩).Nonempty) :
    HasCommonInterleaver [f, g] := by
  obtain ⟨h, hfh, hgh⟩ :=
    pairHasCommonInterleaver_of_degreeGap_slotIntersections
      hf₀ hg₀ hf hg hdeg hslot
  exact ⟨h, by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil] at hp
    rcases hp with rfl | hp
    · exact hfh
    · rcases hp with rfl | hp
      · exact hgh
      · cases hp⟩

/-- List-level packaging of the exact degree-gap slot-data common interleaver
constructor. -/
theorem hasCommonInterleaver_pair_of_degreeGap_slotData
    {f g : ℝ[X]} (hf₀ : f ≠ 0) (hg₀ : g ≠ 0) (hf : f.Splits) (hg : g.Splits)
    (hdeg : g.natDegree = f.natDegree ∨ g.natDegree = f.natDegree + 1)
    (hslot :
      ∀ j, j < f.natDegree + 1 →
        ∀ (hjf : j < (rootSeqDesc f).length + 1)
          (hjg : j < (rootSeqDesc g).length + 1),
          (rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ ∩
            rootSlotInterval (rootSeqDesc g) ⟨j, hjg⟩).Nonempty) :
    HasCommonInterleaver [f, g] := by
  obtain ⟨h, hfh, hgh⟩ :=
    pairHasCommonInterleaver_of_degreeGap_slotData
      hf₀ hg₀ hf hg hdeg hslot
  exact ⟨h, by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil] at hp
    rcases hp with rfl | hp
    · exact hfh
    · rcases hp with rfl | hp
      · exact hgh
      · cases hp⟩

/-- List-level packaging of the succ-degree slot-data common interleaver
constructor. -/
theorem hasCommonInterleaver_pair_of_succDegree_slotData
    {f g : ℝ[X]} (hf₀ : f ≠ 0) (hg₀ : g ≠ 0) (hf : f.Splits) (hg : g.Splits)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hslot :
      ∀ j, j < f.natDegree + 1 →
        ∀ (hjf : j < (rootSeqDesc f).length + 1)
          (hjg : j < (rootSeqDesc g).length + 1),
          (rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ ∩
            rootSlotInterval (rootSeqDesc g) ⟨j, hjg⟩).Nonempty) :
    HasCommonInterleaver [f, g] := by
  obtain ⟨h, hfh, hgh⟩ :=
    pairHasCommonInterleaver_of_succDegree_slotData
      hf₀ hg₀ hf hg hdeg hslot
  exact ⟨h, by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil] at hp
    rcases hp with rfl | hp
    · exact hfh
    · rcases hp with rfl | hp
      · exact hgh
      · cases hp⟩

/-- List-level packaging of the same-degree slot-data common interleaver
constructor. -/
theorem hasCommonInterleaver_pair_of_sameDegree_slotData
    {f g : ℝ[X]} (hf₀ : f ≠ 0) (hg₀ : g ≠ 0) (hf : f.Splits) (hg : g.Splits)
    (hdeg : f.natDegree = g.natDegree)
    (hslot :
      ∀ j, j < f.natDegree + 1 →
        ∀ (hjf : j < (rootSeqDesc f).length + 1)
          (hjg : j < (rootSeqDesc g).length + 1),
          (rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ ∩
            rootSlotInterval (rootSeqDesc g) ⟨j, hjg⟩).Nonempty) :
    HasCommonInterleaver [f, g] := by
  obtain ⟨h, hfh, hgh⟩ :=
    pairHasCommonInterleaver_of_natDegree_eq_slotData
      hf₀ hg₀ hf hg hdeg hslot
  exact ⟨h, by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil] at hp
    rcases hp with rfl | hp
    · exact hfh
    · rcases hp with rfl | hp
      · exact hgh
      · cases hp⟩

/-- Inequality-form degree-gap slot-data wrapper for the common interleaver constructor. -/
theorem pairHasCommonInterleaver_of_degreeGap_le_slotData
    {f g : ℝ[X]} (hf₀ : f ≠ 0) (hg₀ : g ≠ 0) (hf : f.Splits) (hg : g.Splits)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1)
    (hslot :
      ∀ j, j < f.natDegree + 1 →
        ∀ (hjf : j < (rootSeqDesc f).length + 1)
          (hjg : j < (rootSeqDesc g).length + 1),
          (rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ ∩
            rootSlotInterval (rootSeqDesc g) ⟨j, hjg⟩).Nonempty) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  have hdeg : g.natDegree = f.natDegree ∨ g.natDegree = f.natDegree + 1 := by lia
  exact pairHasCommonInterleaver_of_degreeGap_slotData
    hf₀ hg₀ hf hg hdeg hslot

/-- Bundled-inequality degree-gap slot-data wrapper for the common interleaver
constructor. -/
theorem pairHasCommonInterleaver_of_degreeGap_le_slotData_and
    {f g : ℝ[X]} (hf₀ : f ≠ 0) (hg₀ : g ≠ 0) (hf : f.Splits) (hg : g.Splits)
    (hdeg : f.natDegree ≤ g.natDegree ∧ g.natDegree ≤ f.natDegree + 1)
    (hslot :
      ∀ j, j < f.natDegree + 1 →
        ∀ (hjf : j < (rootSeqDesc f).length + 1)
          (hjg : j < (rootSeqDesc g).length + 1),
          (rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ ∩
            rootSlotInterval (rootSeqDesc g) ⟨j, hjg⟩).Nonempty) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  pairHasCommonInterleaver_of_degreeGap_le_slotData
    hf₀ hg₀ hf hg hdeg.1 hdeg.2 hslot

/-- List-level packaging of the bundled degree-gap slot-data common interleaver
constructor. -/
theorem hasCommonInterleaver_pair_of_degreeGap_le_slotData_and
    {f g : ℝ[X]} (hf₀ : f ≠ 0) (hg₀ : g ≠ 0) (hf : f.Splits) (hg : g.Splits)
    (hdeg : f.natDegree ≤ g.natDegree ∧ g.natDegree ≤ f.natDegree + 1)
    (hslot :
      ∀ j, j < f.natDegree + 1 →
        ∀ (hjf : j < (rootSeqDesc f).length + 1)
          (hjg : j < (rootSeqDesc g).length + 1),
          (rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ ∩
            rootSlotInterval (rootSeqDesc g) ⟨j, hjg⟩).Nonempty) :
    HasCommonInterleaver [f, g] := by
  obtain ⟨h, hfh, hgh⟩ :=
    pairHasCommonInterleaver_of_degreeGap_le_slotData_and
      hf₀ hg₀ hf hg hdeg hslot
  exact ⟨h, by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil] at hp
    rcases hp with rfl | hp
    · exact hfh
    · rcases hp with rfl | hp
      · exact hgh
      · cases hp⟩

/-- List-level packaging of the unbundled degree-gap slot-data common
interleaver constructor. -/
theorem hasCommonInterleaver_pair_of_degreeGap_le_slotData
    {f g : ℝ[X]} (hf₀ : f ≠ 0) (hg₀ : g ≠ 0) (hf : f.Splits) (hg : g.Splits)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1)
    (hslot :
      ∀ j, j < f.natDegree + 1 →
        ∀ (hjf : j < (rootSeqDesc f).length + 1)
          (hjg : j < (rootSeqDesc g).length + 1),
          (rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ ∩
            rootSlotInterval (rootSeqDesc g) ⟨j, hjg⟩).Nonempty) :
    HasCommonInterleaver [f, g] := by
  obtain ⟨h, hfh, hgh⟩ :=
    pairHasCommonInterleaver_of_degreeGap_le_slotData
      hf₀ hg₀ hf hg hdeg_lo hdeg_hi hslot
  exact ⟨h, by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil] at hp
    rcases hp with rfl | hp
    · exact hfh
    · rcases hp with rfl | hp
      · exact hgh
      · cases hp⟩

/-- Inequality-form degree-gap slot-intersection wrapper for the common
interleaver constructor. -/
theorem pairHasCommonInterleaver_of_degreeGap_le_slotIntersections
    {f g : ℝ[X]} (hf₀ : f ≠ 0) (hg₀ : g ≠ 0) (hf : f.Splits) (hg : g.Splits)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1)
    (hslot :
      ∀ j (hj : j < f.natDegree + 1),
        (rootSlotInterval (rootSeqDesc f) ⟨j, by simpa [hf] using hj⟩ ∩
          rootSlotInterval (rootSeqDesc g)
            ⟨j, by
              have : j < g.natDegree + 1 := by lia
              simpa [hg] using this⟩).Nonempty) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  have hdeg : g.natDegree = f.natDegree ∨ g.natDegree = f.natDegree + 1 := by lia
  exact pairHasCommonInterleaver_of_degreeGap_slotIntersections
    hf₀ hg₀ hf hg hdeg hslot

/-- Bundled-inequality degree-gap slot-intersection wrapper for the common
interleaver constructor. -/
theorem pairHasCommonInterleaver_of_degreeGap_le_slotIntersections_and
    {f g : ℝ[X]} (hf₀ : f ≠ 0) (hg₀ : g ≠ 0) (hf : f.Splits) (hg : g.Splits)
    (hdeg : f.natDegree ≤ g.natDegree ∧ g.natDegree ≤ f.natDegree + 1)
    (hslot :
      ∀ j (hj : j < f.natDegree + 1),
        (rootSlotInterval (rootSeqDesc f) ⟨j, by simpa [hf] using hj⟩ ∩
          rootSlotInterval (rootSeqDesc g)
            ⟨j, by
              have : j < g.natDegree + 1 := by lia
              simpa [hg] using this⟩).Nonempty) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  pairHasCommonInterleaver_of_degreeGap_le_slotIntersections
    hf₀ hg₀ hf hg hdeg.1 hdeg.2 hslot

/-- List-level packaging of the bundled degree-gap slot-intersection common
interleaver constructor. -/
theorem hasCommonInterleaver_pair_of_degreeGap_le_slotIntersections_and
    {f g : ℝ[X]} (hf₀ : f ≠ 0) (hg₀ : g ≠ 0) (hf : f.Splits) (hg : g.Splits)
    (hdeg : f.natDegree ≤ g.natDegree ∧ g.natDegree ≤ f.natDegree + 1)
    (hslot :
      ∀ j (hj : j < f.natDegree + 1),
        (rootSlotInterval (rootSeqDesc f) ⟨j, by simpa [hf] using hj⟩ ∩
          rootSlotInterval (rootSeqDesc g)
            ⟨j, by
              have : j < g.natDegree + 1 := by lia
              simpa [hg] using this⟩).Nonempty) :
    HasCommonInterleaver [f, g] := by
  obtain ⟨h, hfh, hgh⟩ :=
    pairHasCommonInterleaver_of_degreeGap_le_slotIntersections_and
      hf₀ hg₀ hf hg hdeg hslot
  exact ⟨h, by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil] at hp
    rcases hp with rfl | hp
    · exact hfh
    · rcases hp with rfl | hp
      · exact hgh
      · cases hp⟩

/-- List-level packaging of the unbundled degree-gap slot-intersection common
interleaver constructor. -/
theorem hasCommonInterleaver_pair_of_degreeGap_le_slotIntersections
    {f g : ℝ[X]} (hf₀ : f ≠ 0) (hg₀ : g ≠ 0) (hf : f.Splits) (hg : g.Splits)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1)
    (hslot :
      ∀ j (hj : j < f.natDegree + 1),
        (rootSlotInterval (rootSeqDesc f) ⟨j, by simpa [hf] using hj⟩ ∩
          rootSlotInterval (rootSeqDesc g)
            ⟨j, by
              have : j < g.natDegree + 1 := by lia
              simpa [hg] using this⟩).Nonempty) :
    HasCommonInterleaver [f, g] := by
  obtain ⟨h, hfh, hgh⟩ :=
    pairHasCommonInterleaver_of_degreeGap_le_slotIntersections
      hf₀ hg₀ hf hg hdeg_lo hdeg_hi hslot
  exact ⟨h, by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil] at hp
    rcases hp with rfl | hp
    · exact hfh
    · rcases hp with rfl | hp
      · exact hgh
      · cases hp⟩

/-- Degree-zero edge case of `pairHasCommonInterleaver_of_slotIntersections`. -/
theorem pairHasCommonInterleaver_of_natDegree_eq_zero
    {f g : ℝ[X]} (hf₀ : f ≠ 0) (hg₀ : g ≠ 0) (hf : f.Splits) (hg : g.Splits)
    (hfdeg : f.natDegree = 0) (hgdeg : g.natDegree ≤ 1) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  refine pairHasCommonInterleaver_of_slotIntersections hf₀ hg₀ hf hg
    (by lia) (by lia) ?_
  intro j hj
  have hflen : (rootSeqDesc f).length = 0 := by rw [rootSeqDesc_length hf, hfdeg]
  rw [CommonInterleaver.RootSlots.rootSlotInterval_eq_univ_of_length_eq_zero hflen, Set.univ_inter]
  exact rootSlotInterval_nonempty (rootSeqDesc g) rootSeqDesc_pairwise _

/-! ### Two-element pair wrappers -/

/-- `HasCommonInterleaver [f, g]` is exactly the existence of a common right
interleaver for the pair `f`, `g`. -/
theorem hasCommonInterleaver_pair {f g : ℝ[X]} :
    HasCommonInterleaver [f, g] ↔ ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨h, hh f (by simp), hh g (by simp)⟩
  · rintro ⟨h, hfh, hgh⟩
    refine ⟨h, ?_⟩
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact hfh
    · exact hgh

/-- `HasCommonLeftInterleaver [f, g]` is exactly the existence of a common
left interleaver for the pair `f`, `g`. -/
theorem hasCommonLeftInterleaver_pair {f g : ℝ[X]} :
    HasCommonLeftInterleaver [f, g] ↔ ∃ h : ℝ[X], Prec h f ∧ Prec h g := by
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨h, hh f (by simp), hh g (by simp)⟩
  · rintro ⟨h, hfh, hgh⟩
    refine ⟨h, ?_⟩
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact hfh
    · exact hgh

/-- For a two-element list, the pairwise common-interleaver condition reduces
to the single existential over the one nontrivial pair. -/
theorem pairwiseHasCommonInterleaver_pair {f g : ℝ[X]} :
    PairwiseHasCommonInterleaver [f, g] ↔
      ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  constructor
  · intro H
    obtain ⟨h, hfh, hgh⟩ := H ⟨0, by simp⟩ ⟨1, by simp⟩ (by simp)
    exact ⟨h, hfh, hgh⟩
  · rintro ⟨h, hfh, hgh⟩
    intro i j hij
    obtain ⟨i, hi⟩ := i
    obtain ⟨j, hj⟩ := j
    simp only [List.length_cons, List.length_nil] at hi hj
    match i, hi, j, hj, hij with
    | 0, _, 1, _, _ => exact ⟨h, hfh, hgh⟩
    | 0, _, 0, _, hij => exact absurd hij (by simp)
    | 1, _, 0, _, hij => exact absurd hij (by simp)
    | 1, _, 1, _, hij => exact absurd hij (by simp)

/-- For a two-element list, the pairwise common-left-interleaver condition
reduces to the single existential over the one nontrivial pair. -/
theorem pairwiseHasCommonLeftInterleaver_pair {f g : ℝ[X]} :
    PairwiseHasCommonLeftInterleaver [f, g] ↔
      ∃ h : ℝ[X], Prec h f ∧ Prec h g := by
  constructor
  · intro H
    obtain ⟨h, hfh, hgh⟩ := H ⟨0, by simp⟩ ⟨1, by simp⟩ (by simp)
    exact ⟨h, hfh, hgh⟩
  · rintro ⟨h, hfh, hgh⟩
    intro i j hij
    obtain ⟨i, hi⟩ := i
    obtain ⟨j, hj⟩ := j
    simp only [List.length_cons, List.length_nil] at hi hj
    match i, hi, j, hj, hij with
    | 0, _, 1, _, _ => exact ⟨h, hfh, hgh⟩
    | 0, _, 0, _, hij => exact absurd hij (by simp)
    | 1, _, 0, _, hij => exact absurd hij (by simp)
    | 1, _, 1, _, hij => exact absurd hij (by simp)

/-! #### Existential-shape bridges for downstream pair endpoints -/

/-- Swap the two polynomials in a right common-interleaver existential. -/
theorem pairHasCommonInterleaver_symm {f g : ℝ[X]}
    (h : ∃ h : ℝ[X], Prec f h ∧ Prec g h) :
    ∃ h : ℝ[X], Prec g h ∧ Prec f h := by
  obtain ⟨w, hf, hg⟩ := h
  exact ⟨w, hg, hf⟩

/-- Swap the two polynomials in a left common-interleaver existential. -/
theorem pairHasCommonLeftInterleaver_symm {f g : ℝ[X]}
    (h : ∃ h : ℝ[X], Prec h f ∧ Prec h g) :
    ∃ h : ℝ[X], Prec h g ∧ Prec h f := by
  obtain ⟨w, hf, hg⟩ := h
  exact ⟨w, hg, hf⟩

/-- Extract the pair existential from `HasCommonInterleaver [f, g]`. -/
theorem pairHasCommonInterleaver_of_hasCommonInterleaver_pair {f g : ℝ[X]}
    (h : HasCommonInterleaver [f, g]) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  hasCommonInterleaver_pair.1 h

/-- Package the pair existential as `HasCommonInterleaver [f, g]`. -/
theorem hasCommonInterleaver_pair_of_pairHasCommonInterleaver {f g : ℝ[X]}
    (h : ∃ h : ℝ[X], Prec f h ∧ Prec g h) :
    HasCommonInterleaver [f, g] :=
  hasCommonInterleaver_pair.2 h

/-- Extract the left pair existential from `HasCommonLeftInterleaver [f, g]`. -/
theorem pairHasCommonLeftInterleaver_of_hasCommonLeftInterleaver_pair
    {f g : ℝ[X]} (h : HasCommonLeftInterleaver [f, g]) :
    ∃ h : ℝ[X], Prec h f ∧ Prec h g :=
  hasCommonLeftInterleaver_pair.1 h

/-- Package the left pair existential as `HasCommonLeftInterleaver [f, g]`. -/
theorem hasCommonLeftInterleaver_pair_of_pairHasCommonLeftInterleaver
    {f g : ℝ[X]} (h : ∃ h : ℝ[X], Prec h f ∧ Prec h g) :
    HasCommonLeftInterleaver [f, g] :=
  hasCommonLeftInterleaver_pair.2 h

/-- Extract the pair existential from `PairwiseHasCommonInterleaver [f, g]`. -/
theorem pairHasCommonInterleaver_of_pairwiseHasCommonInterleaver_pair
    {f g : ℝ[X]} (h : PairwiseHasCommonInterleaver [f, g]) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h :=
  pairwiseHasCommonInterleaver_pair.1 h

/-- Package the pair existential as `PairwiseHasCommonInterleaver [f, g]`. -/
theorem pairwiseHasCommonInterleaver_pair_of_pairHasCommonInterleaver
    {f g : ℝ[X]} (h : ∃ h : ℝ[X], Prec f h ∧ Prec g h) :
    PairwiseHasCommonInterleaver [f, g] :=
  pairwiseHasCommonInterleaver_pair.2 h

/-- Extract the left pair existential from pairwise left common-interleavers. -/
theorem pairHasCommonLeftInterleaver_of_pairwiseHasCommonLeftInterleaver_pair
    {f g : ℝ[X]} (h : PairwiseHasCommonLeftInterleaver [f, g]) :
    ∃ h : ℝ[X], Prec h f ∧ Prec h g :=
  pairwiseHasCommonLeftInterleaver_pair.1 h

/-- Package the left pair existential as pairwise left common-interleavers. -/
theorem pairwiseHasCommonLeftInterleaver_pair_of_pairHasCommonLeftInterleaver
    {f g : ℝ[X]} (h : ∃ h : ℝ[X], Prec h f ∧ Prec h g) :
    PairwiseHasCommonLeftInterleaver [f, g] :=
  pairwiseHasCommonLeftInterleaver_pair.2 h

/-- For a pair, global and pairwise right common-interleaver data coincide. -/
theorem hasCommonInterleaver_pair_iff_pairwiseHasCommonInterleaver_pair
    {f g : ℝ[X]} :
    HasCommonInterleaver [f, g] ↔ PairwiseHasCommonInterleaver [f, g] :=
  hasCommonInterleaver_pair.trans pairwiseHasCommonInterleaver_pair.symm

/-- For a pair, global and pairwise left common-interleaver data coincide. -/
theorem hasCommonLeftInterleaver_pair_iff_pairwiseHasCommonLeftInterleaver_pair
    {f g : ℝ[X]} :
    HasCommonLeftInterleaver [f, g] ↔ PairwiseHasCommonLeftInterleaver [f, g] :=
  hasCommonLeftInterleaver_pair.trans pairwiseHasCommonLeftInterleaver_pair.symm

/-- Reversing a weak zero-aware interlacing sequence with nonnegative
coefficients preserves the same structure. -/
lemma IsInterlacingSeq0Nonneg.reverse {fs : List ℝ[X]}
    (hfs : IsInterlacingSeq0Nonneg fs) :
    fs.reverse.Pairwise (fun f g => Prec0 g f) ∧
    ∀ f ∈ fs.reverse, HasNonnegCoeffs f :=
  ⟨hfs.1.reverse, fun f hf => hfs.2 f (by simpa using hf)⟩

end
end RealRooted
