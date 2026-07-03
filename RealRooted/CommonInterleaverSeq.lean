import RealRooted.InterlacingSequenceBasic
import RealRooted.WeightedSum
import RealRooted.PosCombo

/-!
# Common interleavers and Chudnovsky-Seymour theorem

Root-slot interval machinery, the finite Helly lemma (`listInter`), `csDegree`,
the Chudnovsky-Seymour pairwise-to-global common-interleaver upgrade, and the
`polyOfDescRoots` construction.
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

private lemma rootSeqDesc_ne_nil_of_natDegree_pos
    {f : ℝ[X]} (hf : f.Splits) (hpos : 0 < f.natDegree) :
    rootSeqDesc f ≠ [] := by
  apply List.ne_nil_of_length_pos
  simpa [rootSeqDesc_length hf] using hpos

private lemma rootSeqDesc_reverse_ne_nil_of_natDegree_pos
    {f : ℝ[X]} (hf : f.Splits) (hpos : 0 < f.natDegree) :
    (rootSeqDesc f).reverse ≠ [] :=
  List.reverse_ne_nil_iff.mpr (rootSeqDesc_ne_nil_of_natDegree_pos hf hpos)

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

/-- The `j`th Chudnovsky--Seymour interval attached to a descending root
sequence `rs = [r₁, ..., r_d]`.

With zero-based indexing:
- slot `0` is `[r₁, +∞)`,
- interior slots are `[r_{j+1}, r_j]`,
- the last slot is `(-∞, r_d]`. -/
def rootSlotInterval (rs : List ℝ) (j : Fin (rs.length + 1)) : Set ℝ :=
  if h0 : j.1 = 0 then
    match rs with
    | [] => Set.univ
    | r :: _ => Set.Ici r
  else if hj : j.1 = rs.length then
    match rs.reverse with
    | [] => Set.univ
    | r :: _ => Set.Iic r
  else
    Set.Icc (rs.get ⟨j.1, by lia⟩) (rs.get ⟨j.1 - 1, by lia⟩)

private lemma rootSlotInterval_eq_univ_of_length_eq_zero
    {rs : List ℝ} (hrs : rs.length = 0) (j : Fin (rs.length + 1)) :
    rootSlotInterval rs j = Set.univ := by
  have hrs_nil : rs = [] := List.length_eq_zero_iff.mp hrs
  subst rs
  rcases j with ⟨j, hj⟩
  simp at hj
  have hj0 : j = 0 := by lia
  subst j
  simp [rootSlotInterval]

private lemma rootSlotInterval_inter_nonempty_of_lengths_eq_zero
    {rs ss : List ℝ} (hrs : rs.length = 0) (hss : ss.length = 0)
    (jr : Fin (rs.length + 1)) (js : Fin (ss.length + 1)) :
    (rootSlotInterval rs jr ∩ rootSlotInterval ss js).Nonempty := by
  refine ⟨0, ?_, ?_⟩
  · rw [rootSlotInterval_eq_univ_of_length_eq_zero hrs jr]
    simp
  · rw [rootSlotInterval_eq_univ_of_length_eq_zero hss js]
    simp

lemma rootSlotInterval_nonempty (rs : List ℝ) (hrs : rs.Pairwise (· ≥ ·))
    (j : Fin (rs.length + 1)) : (rootSlotInterval rs j).Nonempty := by
  unfold rootSlotInterval
  by_cases h0 : j.1 = 0
  · cases rs with
    | nil =>
        simp
    | cons r rs =>
        simp_all
  · by_cases hj : j.1 = rs.length
    · by_cases hrs_nil : rs = []
      · simp_all
      · obtain ⟨r, tl, hrev⟩ := List.exists_cons_of_ne_nil
          ((List.reverse_ne_nil_iff.mpr hrs_nil))
        simp_all
    · refine ⟨rs.get ⟨j.1, by lia⟩, ?_⟩
      simp only [h0, ↓reduceDIte, hj, List.get_eq_getElem, Set.mem_Icc, Std.le_refl, true_and]
      have hjlt : j.1 < rs.length := by lia
      let jm1 : Fin rs.length := ⟨j.1 - 1, by lia⟩
      let jj : Fin rs.length := ⟨j.1, hjlt⟩
      have hpair := List.pairwise_iff_get.mp hrs
      have hlt : jm1 < jj := by grind
      grind

lemma rootSlotInterval_ordConnected (rs : List ℝ) (j : Fin (rs.length + 1)) :
    Set.OrdConnected (rootSlotInterval rs j) := by
  unfold rootSlotInterval
  by_cases h0 : j.1 = 0
  · cases rs with
    | nil =>
        simpa [h0] using Set.ordConnected_univ
    | cons r rs =>
        simpa [h0] using (Set.ordConnected_Ici : Set.OrdConnected (Set.Ici r))
  · by_cases hj : j.1 = rs.length
    · by_cases hrs_nil : rs = []
      · simp_all
      · obtain ⟨r, tl, hrev⟩ := List.exists_cons_of_ne_nil
          ((List.reverse_ne_nil_iff.mpr hrs_nil))
        simpa [h0, hj, hrev, hrs_nil] using (Set.ordConnected_Iic : Set.OrdConnected (Set.Iic r))
    · simpa [h0, hj] using
        (Set.ordConnected_Icc : Set.OrdConnected
          (Set.Icc (rs.get ⟨j.1, by lia⟩) (rs.get ⟨j.1 - 1, by lia⟩)))

lemma rootSlotInterval_congr
    {xs ys : List ℝ}
    {jx : Fin (xs.length + 1)}
    {jy : Fin (ys.length + 1)}
    (hxy : xs = ys)
    (hji : jx.1 = jy.1) :
    rootSlotInterval xs jx = rootSlotInterval ys jy := by
  subst hxy
  grind

lemma mem_rootSlotInterval_congr
    {xs ys : List ℝ} {x : ℝ}
    {jx : Fin (xs.length + 1)}
    {jy : Fin (ys.length + 1)}
    (hxy : xs = ys)
    (hji : jx.1 = jy.1) :
    x ∈ rootSlotInterval xs jx ↔ x ∈ rootSlotInterval ys jy := by
  rw [rootSlotInterval_congr hxy hji]

private lemma reverse_get_zero_eq_getLast {xs : List ℝ} (hxs : xs ≠ []) :
    xs.reverse.get ⟨0, by grind⟩ =
      xs.getLast hxs := by
  grind

private lemma reverse_get_last_eq_get_zero {xs : List ℝ} (hxs : xs ≠ []) :
    xs.reverse.get ⟨xs.length - 1, by
      simpa [List.length_reverse] using
        (Nat.sub_lt (List.length_pos_iff_ne_nil.mpr hxs) (by lia : 0 < 1))⟩ =
      xs.get ⟨0, List.length_pos_iff_ne_nil.mpr hxs⟩ := by
  simp

private lemma get_reverse_eq_get_sub {xs : List ℝ} {k : ℕ} (hk : k < xs.length) :
    xs.reverse.get ⟨k, by simp_all⟩ =
      xs.get ⟨xs.length - 1 - k, by lia⟩ := by
  simp

private lemma rootSlotInterval_zero_of_ne_nil {rs : List ℝ} (hrs : rs ≠ []) :
    rootSlotInterval rs
      ⟨0, by lia⟩ =
      Set.Ici (rs.get ⟨0, List.length_pos_iff_ne_nil.mpr hrs⟩) := by
  cases rs with
  | nil =>
      lia
  | cons r rs =>
      simp [rootSlotInterval]

private lemma rootSlotInterval_reverse_zero {xs : List ℝ} (hxs : xs ≠ []) :
    rootSlotInterval xs.reverse
      ⟨0, by lia⟩ =
      Set.Ici (xs.getLast hxs) := by
  rw [rootSlotInterval_zero_of_ne_nil (List.reverse_ne_nil_iff.mpr hxs)]
  grind

private lemma rootSlotInterval_reverse_last {xs : List ℝ} (hxs : xs ≠ []) :
    rootSlotInterval xs.reverse
      ⟨xs.length, by simp⟩ =
      Set.Iic (xs.get ⟨0, List.length_pos_iff_ne_nil.mpr hxs⟩) := by
  cases xs with
  | nil =>
      lia
  | cons x xs =>
      have hsimp :
          rootSlotInterval (x :: xs).reverse
            ⟨(x :: xs).length, by simp [List.length_reverse]⟩ =
            Set.Iic (((x :: xs).reverse.reverse).get ⟨0, by simp⟩) := by
        simp [rootSlotInterval]
      simp_all

private lemma rootSlotInterval_last_of_ne_nil {rs : List ℝ} (hrs : rs ≠ []) :
    rootSlotInterval rs
      ⟨rs.length, by lia⟩ =
      Set.Iic (rs.get ⟨rs.length - 1, by
        simpa using (Nat.sub_lt (List.length_pos_iff_ne_nil.mpr hrs) (by lia : 0 < 1))⟩) := by
  have h := rootSlotInterval_reverse_last (xs := rs.reverse)
    (List.reverse_ne_nil_iff.mpr hrs)
  have hcongr :
      rootSlotInterval rs.reverse.reverse
        ⟨rs.length, by simp⟩
        =
      rootSlotInterval rs
        ⟨rs.length, by lia⟩ := by
    apply rootSlotInterval_congr
    · simp
    · lia
  calc
    rootSlotInterval rs
        ⟨rs.length, by lia⟩
        =
      rootSlotInterval rs.reverse.reverse
        ⟨rs.length, by simp⟩ := by
          exact hcongr.symm
    _ = Set.Iic (rs.get ⟨rs.length - 1, by
          simpa using
            (Nat.sub_lt (List.length_pos_iff_ne_nil.mpr hrs) (by lia : 0 < 1))⟩) := by
          simpa [List.length_reverse] using h

private lemma mem_rootSlotInterval_zero_lower {rs : List ℝ} (hrs : rs ≠ []) {x : ℝ}
    (hx : x ∈ rootSlotInterval rs
      ⟨0, by lia⟩) :
    rs.get ⟨0, List.length_pos_iff_ne_nil.mpr hrs⟩ ≤ x := by
  rw [rootSlotInterval_zero_of_ne_nil hrs] at hx
  simp_all

private lemma mem_rootSlotInterval_last_upper {rs : List ℝ} (hrs : rs ≠ []) {x : ℝ}
    (hx : x ∈ rootSlotInterval rs
      ⟨rs.length, by lia⟩) :
    x ≤ rs.getLast hrs := by
  have hlast :
      rs.get ⟨rs.length - 1, by
        simpa using (Nat.sub_lt (List.length_pos_iff_ne_nil.mpr hrs) (by lia : 0 < 1))⟩
        = rs.getLast hrs := by
    grind
  rw [rootSlotInterval_last_of_ne_nil hrs] at hx
  simp_all

private lemma mem_rootSlotInterval_interior_bounds
    {rs : List ℝ} {j : ℕ} (hj0 : 0 < j) (hj : j < rs.length) {x : ℝ}
    (hx : x ∈ rootSlotInterval rs ⟨j, by lia⟩) :
    rs.get ⟨j, hj⟩ ≤ x ∧ x ≤ rs.get ⟨j - 1, by lia⟩ := by
  unfold rootSlotInterval at hx
  have h0 : ¬ j = 0 := by lia
  have hlast : ¬ j = rs.length := by lia
  simpa [h0, hlast] using hx

private lemma getLast_eq_get_lastIndex {rs : List ℝ} (hrs : rs ≠ []) :
    rs.getLast hrs =
      rs.get ⟨rs.length - 1, by
        simpa using (Nat.sub_lt (List.length_pos_iff_ne_nil.mpr hrs) (by lia : 0 < 1))⟩ := by
  grind

private lemma rootSlotInterval_last_eq_reverse_get_zero {rs : List ℝ} (hrs : rs ≠ []) :
    rootSlotInterval rs
      ⟨rs.length, by lia⟩ =
      Set.Iic (rs.reverse.get ⟨0, by grind⟩) := by
  rw [rootSlotInterval_last_of_ne_nil hrs]
  rw [reverse_get_zero_eq_getLast hrs, getLast_eq_get_lastIndex hrs]

private lemma rootSlot_lower_bound
    {rs : List ℝ} (hrs : rs ≠ []) {j : ℕ} (hj : j < rs.length) {x : ℝ}
    (hx : x ∈ rootSlotInterval rs ⟨j, by lia⟩) :
    rs.get ⟨j, hj⟩ ≤ x := by
  by_cases hj0 : j = 0
  · subst hj0
    simpa using mem_rootSlotInterval_zero_lower (rs := rs) hrs hx
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    exact (mem_rootSlotInterval_interior_bounds (rs := rs) hjpos hj hx).1

private lemma rootSlot_upper_bound
    {rs : List ℝ} (hrs : rs ≠ []) {j : ℕ} (hj0 : 0 < j) (hj : j ≤ rs.length) {x : ℝ}
    (hx : x ∈ rootSlotInterval rs ⟨j, by lia⟩) :
    x ≤ rs.get ⟨j - 1, by lia⟩ := by
  by_cases hlast : j = rs.length
  · have hx_last : x ∈ rootSlotInterval rs
        ⟨rs.length, by simp⟩ := by
      simp_all
    have hlast_up : x ≤ rs.getLast hrs := mem_rootSlotInterval_last_upper (rs := rs) hrs hx_last
    have hlast_idx :
        rs.getLast hrs = rs.get ⟨j - 1, by lia⟩ := by
      calc
        rs.getLast hrs = rs.get ⟨rs.length - 1, by
          simp_all⟩ :=
            getLast_eq_get_lastIndex (rs := rs) hrs
        _ = rs.get ⟨j - 1, by lia⟩ := by
            simp_all
    simp_all
  · have hj_lt : j < rs.length := lt_of_le_of_ne hj hlast
    exact (mem_rootSlotInterval_interior_bounds (rs := rs) (j := j) hj0 hj_lt hx).2

private lemma le_of_mem_adjacent_rootSlots
    {rs : List ℝ} (hrs : rs ≠ []) {j : ℕ} (hj : j + 1 < rs.length + 1)
    {x y : ℝ}
    (hx : x ∈ rootSlotInterval rs ⟨j, by lia⟩)
    (hy : y ∈ rootSlotInterval rs ⟨j + 1, hj⟩) :
    y ≤ x := by
  have hj_lt : j < rs.length := by lia
  have hx_lower : rs.get ⟨j, hj_lt⟩ ≤ x :=
    rootSlot_lower_bound (rs := rs) hrs hj_lt hx
  by_cases hlast : j + 1 = rs.length
  · have hy_last : y ≤ rs.getLast hrs := by
      have hy' : y ∈ rootSlotInterval rs
          ⟨rs.length, by simp⟩ := by
        simpa [hlast] using hy
      exact mem_rootSlotInterval_last_upper (rs := rs) hrs hy'
    have hidx : rs.getLast hrs = rs.get ⟨j, hj_lt⟩ := by
      have hlastIdx : j = rs.length - 1 := by lia
      calc
        rs.getLast hrs = rs.get ⟨rs.length - 1, by
          simpa using (Nat.sub_lt (List.length_pos_iff_ne_nil.mpr hrs) (by simp : 0 < 1))⟩ :=
            getLast_eq_get_lastIndex (rs := rs) hrs
        _ = rs.get ⟨j, hj_lt⟩ := by
            simp_all
    exact le_trans (hidx ▸ hy_last) hx_lower
  · have hj1_lt : j + 1 < rs.length := by lia
    have hy_bounds :=
      mem_rootSlotInterval_interior_bounds (rs := rs) (j := j + 1) (by lia) hj1_lt hy
    have hy_upper : y ≤ rs.get ⟨j, hj_lt⟩ := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hy_bounds.2
    exact le_trans hy_upper hx_lower

lemma get_le_get_of_pairwise_ge
    {rs : List ℝ} (hrs : rs.Pairwise (· ≥ ·))
    {i j : Fin rs.length} (hij : i ≤ j) :
    rs.get j ≤ rs.get i := by
  rcases lt_or_eq_of_le hij with hij' | rfl
  · simpa using (List.pairwise_iff_get.mp hrs i j hij')
  · simp

private lemma le_of_mem_rootSlots_of_lt
    {rs : List ℝ} (hrs_ne : rs ≠ []) (hrs : rs.Pairwise (· ≥ ·))
    {i j : ℕ} (hij : i < j) (hj : j < rs.length + 1)
    {x y : ℝ}
    (hx : x ∈ rootSlotInterval rs ⟨i, by lia⟩)
    (hy : y ∈ rootSlotInterval rs ⟨j, hj⟩) :
    y ≤ x := by
  have hi_lt : i < rs.length := by lia
  have hx_lower : rs.get ⟨i, hi_lt⟩ ≤ x :=
    rootSlot_lower_bound (rs := rs) hrs_ne hi_lt hx
  by_cases hlast : j = rs.length
  · have hy_last : y ≤ rs.getLast hrs_ne := by
      have hy' : y ∈ rootSlotInterval rs
          ⟨rs.length, by simp⟩ := by
        simpa [hlast] using hy
      exact mem_rootSlotInterval_last_upper (rs := rs) hrs_ne hy'
    have hlast_idx :
        rs.getLast hrs_ne =
          rs.get ⟨rs.length - 1, by
            simpa using (Nat.sub_lt (List.length_pos_iff_ne_nil.mpr hrs_ne)
              (by simp : 0 < 1))⟩ :=
      getLast_eq_get_lastIndex (rs := rs) hrs_ne
    have htail_le_hi :
        rs.get ⟨rs.length - 1, by
          simpa using (Nat.sub_lt (List.length_pos_iff_ne_nil.mpr hrs_ne)
            (by simp : 0 < 1))⟩ ≤
          rs.get ⟨i, hi_lt⟩ := get_le_get_of_pairwise_ge hrs (Nat.le_pred_of_lt hi_lt)
    exact le_trans (hlast_idx ▸ hy_last) (le_trans htail_le_hi hx_lower)
  · have hj_lt : j < rs.length := by lia
    have hj_pos : 0 < j := by lia
    have hy_bounds :=
      mem_rootSlotInterval_interior_bounds (rs := rs) (j := j) hj_pos hj_lt hy
    have hy_upper : y ≤ rs.get ⟨j - 1, by lia⟩ := hy_bounds.2
    have hmid : rs.get ⟨j - 1, by lia⟩ ≤ rs.get ⟨i, hi_lt⟩ :=
      get_le_get_of_pairwise_ge hrs <| Fin.le_def.2 <| Nat.le_pred_of_lt hij
    exact le_trans hy_upper (le_trans hmid hx_lower)

private lemma listInterlaces_get_bounds
    {ss rs : List ℝ}
    (hint : ListInterlaces ss rs)
    {k : ℕ}
    (hks : k < ss.length)
    (hkr : k + 1 < rs.length) :
    rs.get ⟨k, lt_trans (Nat.lt_succ_self k) hkr⟩ ≤ ss.get ⟨k, hks⟩ ∧
    ss.get ⟨k, hks⟩ ≤ rs.get ⟨k + 1, hkr⟩ := by
  induction ss generalizing rs k with
  | nil => grind
  | cons s ss ih =>
  cases rs with
  | nil => grind
  | cons r₁ rs' =>
  cases rs' with
  | nil => grind
  | cons r₂ rs'' =>
  rcases hint with ⟨hr₁s, hsr₂, htail⟩
  simp_all
  grind

private lemma listInterlaces_of_index_bounds
    {ss rs : List ℝ}
    (hlen : ss.length + 1 = rs.length)
    (hlower : ∀ k (hk : k < ss.length),
      rs.get ⟨k, by
        lia⟩ ≤ ss.get ⟨k, hk⟩)
    (hupper : ∀ k (hk : k < ss.length),
      ss.get ⟨k, hk⟩ ≤ rs.get ⟨k + 1, by
        lia⟩) :
    ListInterlaces ss rs := by
  induction ss generalizing rs with
  | nil =>
      cases rs with
      | nil =>
          lia
      | cons r rs =>
          cases rs with
          | nil =>
              simp [ListInterlaces]
          | cons r₂ rs' =>
              simp at hlen
  | cons s ss ih =>
      cases rs with
      | nil =>
          simp at hlen
      | cons r₁ rs =>
          cases rs with
          | nil =>
              simp at hlen
          | cons r₂ rs' =>
              have hlen' : ss.length + 1 = (r₂ :: rs').length := by
                simpa using Nat.succ.inj hlen
              have hr₁s : r₁ ≤ s := by simpa using hlower 0 (by simp)
              have hs_r₂ : s ≤ r₂ := by simpa using hupper 0 (by simp)
              have hlower' : ∀ k (hk : k < ss.length),
                  (r₂ :: rs').get ⟨k, by
                    lia⟩ ≤ ss.get ⟨k, hk⟩ := by
                intro k hk
                have hk' : k + 1 < (s :: ss).length := by simpa using Nat.succ_lt_succ hk
                simpa using hlower (k + 1) hk'
              have hupper' : ∀ k (hk : k < ss.length),
                  ss.get ⟨k, hk⟩ ≤ (r₂ :: rs').get ⟨k + 1, by
                    lia⟩ := by
                intro k hk
                have hk' : k + 1 < (s :: ss).length := by simpa using Nat.succ_lt_succ hk
                simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                  hupper (k + 1) hk'
              exact ⟨hr₁s, hs_r₂, ih hlen' hlower' hupper'⟩

private lemma listAlternates_of_index_bounds
    {ss rs : List ℝ}
    (hlen : ss.length = rs.length)
    (hlower : ∀ k (hk : k < ss.length),
      ss.get ⟨k, hk⟩ ≤ rs.get ⟨k, by lia⟩)
    (hupper : ∀ k (hk : k + 1 < ss.length),
      rs.get ⟨k, by
        lia⟩ ≤ ss.get ⟨k + 1, hk⟩) :
    ListAlternates ss rs := by
  induction ss generalizing rs with
  | nil =>
      cases rs with
      | nil =>
          simp [ListAlternates]
      | cons r rs =>
          simp at hlen
  | cons s ss ih =>
      cases rs with
      | nil =>
          simp at hlen
      | cons r rs =>
          have hlen' : ss.length = rs.length := by simpa using Nat.succ.inj hlen
          have hs_r : s ≤ r := by simpa using hlower 0 (by simp)
          have hinter : ListInterlaces ss (r :: rs) := by
            refine listInterlaces_of_index_bounds ?_ ?_ ?_
            · simpa using hlen
            · intro k hk
              have hk' : k + 1 < (s :: ss).length := by simpa using Nat.succ_lt_succ hk
              simpa using hupper k hk'
            · intro k hk
              have hk' : k + 1 < (s :: ss).length := by simpa using Nat.succ_lt_succ hk
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                hlower (k + 1) hk'
          exact ⟨hs_r, hinter⟩

private lemma listAlternates_get_lower
    {ss rs : List ℝ}
    (halt : ListAlternates ss rs)
    {k : ℕ}
    (hks : k < ss.length)
    (hkr : k < rs.length) :
    ss.get ⟨k, hks⟩ ≤ rs.get ⟨k, hkr⟩ := by
  induction ss generalizing rs k with
  | nil =>
      grind
  | cons s ss ih =>
      cases rs with
      | nil =>
          grind
      | cons r rs' =>
          rcases halt with ⟨hsr, htail⟩
          cases k with
          | zero =>
              simp_all
          | succ k =>
              have hks' : k < ss.length := by
                simp_all
              have hkr' : k < rs'.length := by
                simp_all
              simpa using (listInterlaces_get_bounds htail hks'
                (by lia)).2

private lemma listAlternates_get_upper
    {ss rs : List ℝ}
    (halt : ListAlternates ss rs)
    {k : ℕ}
    (hk : k + 1 < ss.length)
    (hkr : k < rs.length) :
    rs.get ⟨k, hkr⟩ ≤ ss.get ⟨k + 1, hk⟩ := by
  induction ss generalizing rs k with
  | nil => grind
  | cons s ss ih =>
  cases rs with
  | nil => grind
  | cons r rs' =>
  rcases halt with ⟨hsr, htail⟩
  cases ss with
  | nil => grind
  | cons s₂ ss₂ =>
  cases rs' with
  | nil => cases htail
  | cons r₂ rs₂ =>
  rcases htail with ⟨hr_s₂, hs₂_r₂, htail'⟩
  cases k with
  | zero => grind
  | succ k =>
  simp_all
  have halt' : ListAlternates (s₂ :: ss₂) (r₂ :: rs₂) := ⟨hs₂_r₂, htail'⟩
  grind

private lemma mem_rootSlotInterval_reverse_of_listInterlaces_interior
    {ss rs : List ℝ}
    (hlen : ss.length + 1 = rs.length)
    (hint : ListInterlaces ss rs)
    {j : Fin rs.length}
    (h0 : j.1 ≠ 0)
    (hlast : j.1 ≠ ss.length) :
    rs.reverse.get ⟨j.1, by simp [List.length_reverse]⟩ ∈ rootSlotInterval ss.reverse
      ⟨j.1, by simp [List.length_reverse, hlen]⟩ := by
  have hj_pos : 0 < j.1 := Nat.pos_of_ne_zero h0
  have hjss : j.1 < ss.length := by lia
  have hnot_last : ¬ j.1 = ss.length := hlast
  let k : Fin rs.length := ⟨rs.length - 1 - j.1, by lia⟩
  let klow : Fin ss.length := ⟨ss.length - 1 - j.1, by lia⟩
  let khigh : Fin ss.length := ⟨ss.length - j.1, by lia⟩
  have hrs_rev :
      rs.reverse.get ⟨j.1, by simp [List.length_reverse]⟩ = rs.get k := by
    simp [k]
  have hss_rev_lo :
      ss.reverse.get ⟨j.1, by simp_all⟩ = ss.get klow := by
    simp [klow]
  have hpred' : j.1 - 1 < ss.length := by lia
  have hpred : j.1 - 1 < ss.reverse.length := by
    simp_all
  let kupper : Fin ss.length := ⟨ss.length - 1 - (j.1 - 1), by lia⟩
  have hkupper_eq : kupper = khigh := by
    apply Fin.ext
    simp [kupper, khigh]
    lia
  have hss_rev_hi :
      ss.reverse.get ⟨j.1 - 1, hpred⟩ = ss.get khigh := by
    rw [show ss.get khigh = ss.get kupper by simp [hkupper_eq]]
    simp [kupper]
  have hslot :
      rootSlotInterval ss.reverse
        ⟨j.1, by simp [List.length_reverse, hlen]⟩ =
        Set.Icc (ss.reverse.get ⟨j.1, by simp_all⟩)
          (ss.reverse.get ⟨j.1 - 1, hpred⟩) := by
    simp [rootSlotInterval, h0, hnot_last, List.length_reverse]
  rw [hslot, hrs_rev, hss_rev_lo, hss_rev_hi]
  have hklow_succ_lt : klow.1 + 1 < rs.length := by
    simp [klow]
    lia
  have hb_low := listInterlaces_get_bounds hint klow.2 hklow_succ_lt
  have hidx_low :
      (⟨klow.1 + 1, hklow_succ_lt⟩ : Fin rs.length) = k := by
    apply Fin.ext
    simp [klow, k]
    lia
  have hlower : ss.get klow ≤ rs.get k := by
    simp_all
  have hkhigh_succ_lt : khigh.1 + 1 < rs.length := by
    simp [khigh]
    lia
  have hb_high := listInterlaces_get_bounds hint khigh.2 hkhigh_succ_lt
  have hidx_high :
      (⟨khigh.1, lt_trans (Nat.lt_succ_self khigh.1) hkhigh_succ_lt⟩ : Fin rs.length) = k := by
    apply Fin.ext
    simp [khigh, k]
    lia
  simp_all

private lemma mem_rootSlotInterval_reverse_of_listInterlaces_zero
    {ss rs : List ℝ}
    (hss : ss.Pairwise (· ≤ ·))
    (hrs : rs.Pairwise (· ≤ ·))
    (hlen : ss.length + 1 = rs.length)
    (hint : ListInterlaces ss rs) :
    rs.reverse.get ⟨0, by
      grind⟩ ∈
      rootSlotInterval ss.reverse
        ⟨0, by
          lia⟩ := by
  cases ss with
  | nil =>
      simp [rootSlotInterval] at hlen ⊢
  | cons s ss =>
      have hss_ne : (s :: ss) ≠ [] := by lia
      have hrs_pos : 0 < rs.length := by lia
      have hrs_ne : rs ≠ [] := List.length_pos_iff_ne_nil.mp hrs_pos
      rw [rootSlotInterval_reverse_zero hss_ne]
      rw [reverse_get_zero_eq_getLast hrs_ne]
      exact Set.mem_Ici.mpr <|
        listInterlaces_all_le_getLast hrs_ne hrs hint _ (List.getLast_mem hss_ne)

private lemma mem_rootSlotInterval_reverse_of_listInterlaces_last
    {ss rs : List ℝ}
    (hlen : ss.length + 1 = rs.length)
    (hint : ListInterlaces ss rs)
    (hss_ne : ss ≠ []) :
    rs.reverse.get ⟨ss.length, by
      grind⟩ ∈
      rootSlotInterval ss.reverse
        ⟨ss.length, by
          simp⟩ := by
  have hrs_pos : 0 < rs.length := by lia
  have hrs_ne : rs ≠ [] := List.length_pos_iff_ne_nil.mp hrs_pos
  rw [rootSlotInterval_reverse_last hss_ne]
  have hidx :
      (⟨ss.length, by
        grind⟩ : Fin rs.reverse.length) =
      ⟨rs.length - 1, by
        simp_all⟩ := by
    have hsub : ss.length = rs.length - 1 := by lia
    simp_all
  rw [hidx]
  rw [reverse_get_last_eq_get_zero hrs_ne]
  apply Set.mem_Iic.mpr
  have hss_pos : 0 < ss.length := List.length_pos_iff_ne_nil.mpr hss_ne
  have hb :=
    listInterlaces_get_bounds hint (k := 0)
      (by simp_all)
      (by simp_all)
  simp_all

private lemma mem_rootSlotInterval_reverse_of_listInterlaces
    {ss rs : List ℝ}
    (hss : ss.Pairwise (· ≤ ·))
    (hrs : rs.Pairwise (· ≤ ·))
    (hlen : ss.length + 1 = rs.length)
    (hint : ListInterlaces ss rs)
    (j : Fin rs.length) :
    rs.reverse.get ⟨j.1, by simp [List.length_reverse]⟩ ∈ rootSlotInterval ss.reverse
      ⟨j.1, by simp [List.length_reverse, hlen]⟩ := by
  by_cases h0 : j.1 = 0
  · have hj :
        j = ⟨0, by
          lia⟩ := by
      grind
    simpa [hj] using mem_rootSlotInterval_reverse_of_listInterlaces_zero hss hrs hlen hint
  · by_cases hlast : j.1 = ss.length
    · have hss_ne : ss ≠ [] := by simp_all
      have hj :
          j = ⟨ss.length, by
            lia⟩ := by
        grind
      simpa [hj] using
        mem_rootSlotInterval_reverse_of_listInterlaces_last hlen hint hss_ne
    · exact
        mem_rootSlotInterval_reverse_of_listInterlaces_interior hlen hint h0 hlast

private lemma mem_rootSlotInterval_reverse_of_listAlternates_interior
    {ss rs : List ℝ}
    (hlen : ss.length = rs.length)
    (halt : ListAlternates ss rs)
    {j : Fin rs.length}
    (h0 : j.1 ≠ 0) :
    rs.reverse.get ⟨j.1, by simp [List.length_reverse]⟩ ∈ rootSlotInterval ss.reverse
      ⟨j.1, by simp [List.length_reverse, hlen]⟩ := by
  have hjss : j.1 < ss.length := by lia
  have hnot_last : ¬ j.1 = ss.length := ne_of_lt hjss
  let k : Fin ss.length := ⟨ss.length - 1 - j.1, by lia⟩
  have hk_succ : k.1 + 1 < ss.length := by
    simp [k]
    lia
  let ks : Fin ss.length := ⟨k.1 + 1, hk_succ⟩
  let kr : Fin rs.length := ⟨rs.length - 1 - j.1, by lia⟩
  have hkr_eq : kr.1 = k.1 := by simp [kr, k, hlen]
  have hks_eq : ks.1 = ss.length - j.1 := by
    simp [ks, k]
    lia
  have hrs_rev :
      rs.reverse.get ⟨j.1, by simp [List.length_reverse]⟩ = rs.get kr := by
    simp [kr]
  have hss_rev_lo :
      ss.reverse.get ⟨j.1, by simp [List.length_reverse, hlen]⟩ = ss.get k := by
    simp [k, hlen]
  have hpred' : j.1 - 1 < ss.length := by lia
  have hpred : j.1 - 1 < ss.reverse.length := by
    simp_all
  let kupper : Fin ss.length := ⟨ss.length - 1 - (j.1 - 1), by
    lia⟩
  have hkupper_eq : kupper = ks := by
    apply Fin.ext
    simp [kupper, ks, k]
    lia
  have hss_rev_hi :
      ss.reverse.get ⟨j.1 - 1, hpred⟩ = ss.get ks := by
    rw [show ss.get ks = ss.get kupper by simp [hkupper_eq]]
    simp [kupper, hlen]
  have hslot :
      rootSlotInterval ss.reverse
        ⟨j.1, by simp [List.length_reverse, hlen]⟩ =
        Set.Icc (ss.reverse.get ⟨j.1, by simp [List.length_reverse, hlen]⟩)
          (ss.reverse.get ⟨j.1 - 1, hpred⟩) := by
    simp [rootSlotInterval, h0, hnot_last, List.length_reverse]
  rw [hslot, hrs_rev, hss_rev_lo, hss_rev_hi]
  rw [show kr = ⟨k.1, by simpa [hkr_eq] using kr.2⟩ by
    apply Fin.ext
    simp_all]
  have hk_lower : ss.get k ≤ rs.get ⟨k.1, by simpa [hkr_eq] using kr.2⟩ :=
    listAlternates_get_lower halt k.2 (by simpa [hkr_eq] using kr.2)
  have hk_upper : rs.get ⟨k.1, by simpa [hkr_eq] using kr.2⟩ ≤ ss.get ks := by
    have hk_rs : k.1 < rs.length := by simpa [hkr_eq] using kr.2
    simpa [ks] using listAlternates_get_upper halt hk_succ hk_rs
  simp_all

private lemma mem_rootSlotInterval_reverse_of_listAlternates_zero
    {ss rs : List ℝ}
    (hss : ss.Pairwise (· ≤ ·))
    (hrs : rs.Pairwise (· ≤ ·))
    (hlen : ss.length = rs.length)
    (halt : ListAlternates ss rs)
    (hrs_ne : rs ≠ []) :
    rs.reverse.get ⟨0, by
      grind⟩ ∈
      rootSlotInterval ss.reverse
        ⟨0, by
          lia⟩ := by
  cases ss with
  | nil =>
      grind
  | cons s ss =>
      have hss_ne : (s :: ss) ≠ [] := by lia
      have hrs_ne : rs ≠ [] := by lia
      rw [rootSlotInterval_reverse_zero hss_ne]
      rw [reverse_get_zero_eq_getLast hrs_ne]
      exact Set.mem_Ici.mpr <|
        listAlternates_all_le_getLast hrs_ne hrs halt _ (List.getLast_mem hss_ne)

private lemma mem_rootSlotInterval_reverse_of_listAlternates
    {ss rs : List ℝ}
    (hss : ss.Pairwise (· ≤ ·))
    (hrs : rs.Pairwise (· ≤ ·))
    (hlen : ss.length = rs.length)
    (halt : ListAlternates ss rs)
    (j : Fin rs.length) :
    rs.reverse.get ⟨j.1, by simp [List.length_reverse]⟩ ∈ rootSlotInterval ss.reverse
      ⟨j.1, by simp [List.length_reverse, hlen]⟩ := by
  by_cases h0 : j.1 = 0
  · have hj :
        j = ⟨0, by
          lia⟩ := by
      apply Fin.ext
      lia
    have hrs_ne : rs ≠ [] := List.length_pos_iff_ne_nil.mp (by lia)
    simpa [hj] using mem_rootSlotInterval_reverse_of_listAlternates_zero hss hrs hlen halt hrs_ne
  · exact mem_rootSlotInterval_reverse_of_listAlternates_interior hlen halt h0

/-- Slot transport from an ascending `Prec` witness to the descending
Chudnovsky--Seymour interval language. This is the core bridge needed to turn
pairwise common interleavers into pairwise-intersecting slot intervals. -/
private lemma mem_rootSlotInterval_of_prec_witness
    {ss rs : List ℝ}
    (hss : ss.Pairwise (· ≤ ·)) (hrs : rs.Pairwise (· ≤ ·))
    (hshape : (ss.length + 1 = rs.length ∧ ListInterlaces ss rs) ∨
      (ss.length = rs.length ∧ ListAlternates ss rs))
    (j : Fin rs.length) :
    rs.reverse.get ⟨j.1, by simp [List.length_reverse]⟩ ∈
      rootSlotInterval ss.reverse
        ⟨j.1, by
          grind⟩ := by
  rcases hshape with ⟨hlen, hint⟩ | ⟨hlen, halt⟩
  · simpa using mem_rootSlotInterval_reverse_of_listInterlaces hss hrs hlen hint j
  · simpa using mem_rootSlotInterval_reverse_of_listAlternates hss hrs hlen halt j

private lemma mem_rootSlotInterval_of_prec
    {f g : ℝ[X]} (hfg : Prec f g) (j : Fin g.natDegree) :
    (rootSeqDesc g).get ⟨j.1, by
      rcases hfg with ⟨_, hg, _, _, _, _, _, _, _⟩
      simp [rootSeqDesc, card_roots_of_splits hg.2]⟩ ∈ rootSlotInterval (rootSeqDesc f)
      ⟨j.1, by
        rcases hfg with ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩
        have hdeg := (natDegree_bounds_of_prec ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩).2
        simpa [hf.2, hg.2] using lt_of_lt_of_le j.2 hdeg⟩ := by
  rcases hfg with ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩
  have hss_desc : rootSeqDesc f = ss.reverse := rootSeqDesc_eq_reverse_of_pairwise hss hss_eq
  have hrs_desc : rootSeqDesc g = rs.reverse := rootSeqDesc_eq_reverse_of_pairwise hrs hrs_eq
  have hdeg := (natDegree_bounds_of_prec ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩).2
  have hss_len : ss.length = f.natDegree := by
    rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hf.2]
  have hrs_len : rs.length = g.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hg.2]
  let jg_desc : Fin (rootSeqDesc g).length := ⟨j.1, by
    simp [rootSeqDesc, card_roots_of_splits hg.2]⟩
  let jg_rev : Fin rs.reverse.length := ⟨j.1, by
    simp [List.length_reverse, hrs_len]⟩
  let jf_desc : Fin ((rootSeqDesc f).length + 1) := ⟨j.1, by
    grind⟩
  let jf_rev : Fin (ss.reverse.length + 1) := ⟨j.1, by
    grind⟩
  have hmem_rev : rs.reverse.get jg_rev ∈ rootSlotInterval ss.reverse jf_rev :=
    mem_rootSlotInterval_of_prec_witness hss hrs hshape ⟨j.1, by lia⟩
  lia

/-- Finite intersection of a list of sets. -/
def listInter : List (Set ℝ) → Set ℝ
  | [] => Set.univ
  | s :: ss => s ∩ listInter ss

lemma mem_listInter {ss : List (Set ℝ)} {x : ℝ} :
    x ∈ listInter ss ↔ ∀ s ∈ ss, x ∈ s := by
  induction ss with
  | nil =>
      simp [listInter]
  | cons s ss ih =>
      simp [listInter, ih]

/-- Finite Helly property for intervals on `ℝ`, formulated for `OrdConnected`
sets: a finite pairwise-intersecting family of intervals has nonempty total
intersection. -/
lemma listInter_nonempty_of_pairwise_ordConnected
    (ss : List (Set ℝ))
    (hne : ∀ s ∈ ss, s.Nonempty)
    (hconn : ∀ s ∈ ss, Set.OrdConnected s)
    (hpair : ss.Pairwise fun s t => (s ∩ t).Nonempty) :
    (listInter ss).Nonempty := by
  induction ss with
  | nil =>
      simp [listInter]
  | cons s ss ih =>
      cases ss with
      | nil =>
          simpa [listInter] using hne s (by simp)
      | cons t ts =>
          have hhead : ∀ u ∈ t :: ts, (s ∩ u).Nonempty := (List.pairwise_cons.mp hpair).1
          have htail : (t :: ts).Pairwise fun s t => (s ∩ t).Nonempty :=
            (List.pairwise_cons.mp hpair).2
          have htail_ne : (listInter (t :: ts)).Nonempty := by
            simp_all
          rcases htail_ne with ⟨x, hx⟩
          by_cases hxs : x ∈ s
          · exact ⟨x, by simpa [listInter, hxs] using hx⟩
          · let ys : List ℝ := (List.attach (t :: ts)).map
              (fun u => Classical.choose (hhead u.1 u.2))
            have hys_pos : 0 < ys.length := by simp [ys]
            have hy_mem_s : ∀ y ∈ ys, y ∈ s := by grind
            have hx_mem : ∀ u ∈ t :: ts, x ∈ u :=
              fun u hu => (mem_listInter.mp hx) u hu
            let y0 : ℝ := Classical.choose (hhead t (by simp))
            have hy0s : y0 ∈ s := (Classical.choose_spec (hhead t (by simp))).1
            have hy0_side : y0 < x ∨ x < y0 := by grind
            rcases hy0_side with hy0lt | hxy0
            · let y : ℝ := ys.maximum_of_length_pos hys_pos
              have hy_mem : y ∈ ys := List.maximum_of_length_pos_mem hys_pos
              have hys : y ∈ s := hy_mem_s y hy_mem
              have hall_lt : ∀ z ∈ ys, z < x := by
                intro z hz
                have hzs : z ∈ s := hy_mem_s z hz
                by_cases hzx : z < x
                · lia
                · have hxz : x < z := by grind
                  have hx_in_s : x ∈ s := (hconn s (by simp)).out hy0s hzs ⟨hy0lt.le, hxz.le⟩
                  lia
              refine ⟨y, ?_⟩
              rw [mem_listInter]
              intro u hu
              have hu' : u = s ∨ u ∈ t :: ts := by simp_all
              rcases hu' with rfl | hu
              · lia
              · let yu : ℝ := Classical.choose (hhead u hu)
                have hyu_mem : yu ∈ ys := by
                  have hmem_attach : (⟨u, hu⟩ : {v // v ∈ t :: ts}) ∈ (t :: ts).attach := by
                    grind
                  grind
                have hyu_le : yu ≤ y := List.le_maximum_of_length_pos_of_mem hyu_mem hys_pos
                have hy_lt : y < x := hall_lt y hy_mem
                have hyu_u : yu ∈ u := (Classical.choose_spec (hhead u hu)).2
                have hx_u : x ∈ u := hx_mem u hu
                exact (hconn u (by lia)).out hyu_u hx_u ⟨hyu_le, hy_lt.le⟩
            · let y : ℝ := ys.minimum_of_length_pos hys_pos
              have hy_mem : y ∈ ys := List.minimum_of_length_pos_mem hys_pos
              have hys : y ∈ s := hy_mem_s y hy_mem
              have hall_gt : ∀ z ∈ ys, x < z := by
                intro z hz
                have hzs : z ∈ s := hy_mem_s z hz
                by_cases hxz : x < z
                · lia
                · have hzx : z < x := by grind
                  have hx_in_s : x ∈ s := (hconn s (by simp)).out hzs hy0s ⟨hzx.le, hxy0.le⟩
                  lia
              refine ⟨y, ?_⟩
              rw [mem_listInter]
              intro u hu
              have hu' : u = s ∨ u ∈ t :: ts := by simp_all
              rcases hu' with rfl | hu
              · lia
              · let yu : ℝ := Classical.choose (hhead u hu)
                have hyu_mem : yu ∈ ys := by
                  have hmem_attach : (⟨u, hu⟩ : {v // v ∈ t :: ts}) ∈ (t :: ts).attach := by
                    grind
                  grind
                have hle_yu : y ≤ yu := List.minimum_of_length_pos_le_of_mem hyu_mem hys_pos
                have hx_lt : x < y := hall_gt y hy_mem
                have hyu_u : yu ∈ u := (Classical.choose_spec (hhead u hu)).2
                have hx_u : x ∈ u := hx_mem u hu
                exact (hconn u (by lia)).out hx_u hyu_u ⟨hx_lt.le, hle_yu⟩

/-- The target length `d` in the Chudnovsky--Seymour construction: the maximum
degree occurring in the family. -/
def csDegree (fs : List ℝ[X]) : ℕ :=
  (fs.map Polynomial.natDegree).foldr max 0

lemma natDegree_le_csDegree {fs : List ℝ[X]} {f : ℝ[X]} (hf : f ∈ fs) :
    f.natDegree ≤ csDegree fs := by
  unfold csDegree
  exact List.le_max_of_le (by grind) le_rfl

lemma csDegree_eq_zero_of_nil : csDegree ([] : List ℝ[X]) = 0 := by
  simp [csDegree]

lemma exists_mem_csDegree_of_ne_nil {fs : List ℝ[X]} (hfs : fs ≠ []) :
    ∃ f ∈ fs, f.natDegree = csDegree fs := by
  induction fs with
  | nil =>
      lia
  | cons f fs ih =>
      cases fs with
      | nil =>
          refine ⟨f, by simp, by simp [csDegree]⟩
      | cons g gs =>
          by_cases htail : csDegree (g :: gs) ≤ f.natDegree
          · refine ⟨f, by simp, ?_⟩
            simpa [csDegree] using htail
          · have hne_tail : g :: gs ≠ [] := by lia
            obtain ⟨p, hp, hpdeg⟩ := ih hne_tail
            refine ⟨p, by simp [hp], ?_⟩
            have hltail : f.natDegree ≤ csDegree (g :: gs) := by lia
            rw [hpdeg]
            simpa [csDegree] using hltail

lemma natDegree_ge_csDegree_sub_one_of_pairwiseHasCommonInterleaver
    {fs : List ℝ[X]} {f g : ℝ[X]}
    (hf : f ∈ fs) (hg : g ∈ fs)
    (hpair : PairwiseHasCommonInterleaver fs) :
    f.natDegree ≤ g.natDegree + 1 := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hf
  obtain ⟨j, hgj⟩ := List.mem_iff_get.1 hg
  rcases lt_trichotomy i j with hij | rfl | hji
  · obtain ⟨h, hfh, hgh⟩ := hpair i j hij
    rw [← hgj]
    exact le_trans (natDegree_bounds_of_prec hfh).1 (natDegree_bounds_of_prec hgh).2
  · lia
  · obtain ⟨h, hgh, hfh⟩ := hpair j i hji
    rw [← hgj]
    exact le_trans (natDegree_bounds_of_prec hfh).1 (natDegree_bounds_of_prec hgh).2

lemma csDegree_le_natDegree_succ_of_pairwiseHasCommonInterleaver
    {fs : List ℝ[X]} {f : ℝ[X]}
    (hfs : fs ≠ [])
    (hf : f ∈ fs)
    (hpair : PairwiseHasCommonInterleaver fs) :
    csDegree fs ≤ f.natDegree + 1 := by
  obtain ⟨g, hg, hgmax⟩ := exists_mem_csDegree_of_ne_nil hfs
  have hbound :=
    natDegree_ge_csDegree_sub_one_of_pairwiseHasCommonInterleaver (f := g) (g := f) hg hf hpair
  lia

/-! ### Left-oriented degree bookkeeping -/

/-- The target length for a common left interleaver: the minimum degree
occurring in the family. -/
def leftCsDegree (fs : List ℝ[X]) : ℕ :=
  (fs.map Polynomial.natDegree).foldr Nat.min (csDegree fs)

private lemma foldr_min_le_of_mem {xs : List ℕ} {a seed : ℕ} (ha : a ∈ xs) :
    xs.foldr Nat.min seed ≤ a := by
  induction xs with
  | nil =>
      simp_all
  | cons x xs ih =>
      simp only [List.foldr_cons, List.mem_cons] at ha ⊢
      rcases ha with rfl | ha
      · exact Nat.min_le_left a (xs.foldr Nat.min seed)
      · exact le_trans (Nat.min_le_right x (xs.foldr Nat.min seed)) (ih ha)

lemma leftCsDegree_le_natDegree {fs : List ℝ[X]} {f : ℝ[X]} (hf : f ∈ fs) :
    leftCsDegree fs ≤ f.natDegree := by
  unfold leftCsDegree
  exact foldr_min_le_of_mem (List.mem_map_of_mem (f := Polynomial.natDegree) hf)

private lemma exists_mem_eq_foldr_min_of_forall_le
    {xs : List ℕ} {seed : ℕ} (hxs : xs ≠ []) (hseed : ∀ a ∈ xs, a ≤ seed) :
    ∃ a ∈ xs, a = xs.foldr Nat.min seed := by
  induction xs with
  | nil =>
      simp_all
  | cons x xs ih =>
      cases xs with
      | nil =>
        refine ⟨x, by simp, ?_⟩
        simp [List.foldr_cons, Nat.min_eq_left (hseed x (by simp))]
      | cons y ys =>
        have hseed_tail : ∀ a ∈ y :: ys, a ≤ seed := by
          intro a ha
          exact hseed a (by simp [ha])
        obtain ⟨a, ha, haeq⟩ := ih (by simp) hseed_tail
        by_cases hx : x ≤ (y :: ys).foldr Nat.min seed
        · refine ⟨x, by simp, ?_⟩
          exact (Nat.min_eq_left hx).symm
        · refine ⟨a, by simp [ha], ?_⟩
          have hle : (y :: ys).foldr Nat.min seed ≤ x := by lia
          exact haeq.trans (Nat.min_eq_right hle).symm

lemma exists_mem_leftCsDegree_of_ne_nil {fs : List ℝ[X]} (hfs : fs ≠ []) :
    ∃ f ∈ fs, f.natDegree = leftCsDegree fs := by
  have hmap_ne : fs.map Polynomial.natDegree ≠ [] := by
    simpa using hfs
  have hseed : ∀ a ∈ fs.map Polynomial.natDegree, a ≤ csDegree fs := by
    intro a ha
    rcases List.mem_map.mp ha with ⟨f, hf, rfl⟩
    exact natDegree_le_csDegree hf
  obtain ⟨d, hd, hd_eq⟩ := exists_mem_eq_foldr_min_of_forall_le hmap_ne hseed
  rcases List.mem_map.mp hd with ⟨f, hf, rfl⟩
  exact ⟨f, hf, hd_eq⟩

lemma natDegree_le_natDegree_succ_of_pairwiseHasCommonLeftInterleaver
    {fs : List ℝ[X]} {f g : ℝ[X]}
    (hf : f ∈ fs) (hg : g ∈ fs)
    (hpair : PairwiseHasCommonLeftInterleaver fs) :
    f.natDegree ≤ g.natDegree + 1 := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hf
  obtain ⟨j, hgj⟩ := List.mem_iff_get.1 hg
  rcases lt_trichotomy i j with hij | rfl | hji
  · obtain ⟨h, hhf, hhg⟩ := hpair i j hij
    rw [← hgj]
    exact le_trans (natDegree_bounds_of_prec hhf).2 <|
      Nat.succ_le_succ (natDegree_bounds_of_prec hhg).1
  · lia
  · obtain ⟨h, hhg, hhf⟩ := hpair j i hji
    rw [← hgj]
    exact le_trans (natDegree_bounds_of_prec hhf).2 <|
      Nat.succ_le_succ (natDegree_bounds_of_prec hhg).1

lemma natDegree_le_leftCsDegree_succ_of_pairwiseHasCommonLeftInterleaver
    {fs : List ℝ[X]} {f : ℝ[X]}
    (hfs : fs ≠ [])
    (hf : f ∈ fs)
    (hpair : PairwiseHasCommonLeftInterleaver fs) :
    f.natDegree ≤ leftCsDegree fs + 1 := by
  obtain ⟨g, hg, hgmin⟩ := exists_mem_leftCsDegree_of_ne_nil hfs
  have hbound :=
    natDegree_le_natDegree_succ_of_pairwiseHasCommonLeftInterleaver
      (f := f) (g := g) hf hg hpair
  lia

/-- Pairwise slot intersection for a pair of polynomials sharing a common
interleaver on the right. This is the local input needed for the finite-Helly
step in the Chudnovsky--Seymour proof. -/
theorem rootSlotInterval_inter_nonempty_of_commonInterleaver
    {f g h : ℝ[X]}
    (hfh : Prec f h) (hgh : Prec g h)
    (j : ℕ)
    (hjf : j < f.natDegree + 1)
    (hjg : j < g.natDegree + 1) :
    (rootSlotInterval (rootSeqDesc f)
        ⟨j, by simpa [hfh.1.2] using hjf⟩ ∩
      rootSlotInterval (rootSeqDesc g)
        ⟨j, by simpa [hgh.1.2] using hjg⟩).Nonempty := by
  let jf : Fin ((rootSeqDesc f).length + 1) := ⟨j, by simpa [hfh.1.2] using hjf⟩
  let jg : Fin ((rootSeqDesc g).length + 1) := ⟨j, by simpa [hgh.1.2] using hjg⟩
  change (rootSlotInterval (rootSeqDesc f) jf ∩
    rootSlotInterval (rootSeqDesc g) jg).Nonempty
  have hdeg_fh : f.natDegree ≤ h.natDegree ∧ h.natDegree ≤ f.natDegree + 1 :=
    natDegree_bounds_of_prec hfh
  have hdeg_gh : g.natDegree ≤ h.natDegree ∧ h.natDegree ≤ g.natDegree + 1 :=
    natDegree_bounds_of_prec hgh
  by_cases hjh : j < h.natDegree
  · let jh : Fin h.natDegree := ⟨j, hjh⟩
    let x : ℝ := (rootSeqDesc h).get ⟨j, by
      simpa [hfh.2.1.2] using hjh⟩
    have hmem_f : x ∈ rootSlotInterval (rootSeqDesc f) jf := by
      simpa [x, jf, jh] using (mem_rootSlotInterval_of_prec hfh jh)
    have hmem_g : x ∈ rootSlotInterval (rootSeqDesc g) jg := by
      simpa [x, jg, jh] using (mem_rootSlotInterval_of_prec hgh jh)
    exact ⟨x, ⟨hmem_f, hmem_g⟩⟩
  · have hj_eq_h : j = h.natDegree := by lia
    have hf_eq_h : f.natDegree = h.natDegree := by lia
    have hg_eq_h : g.natDegree = h.natDegree := by lia
    by_cases hdeg0 : h.natDegree = 0
    · have hj0 : j = 0 := by lia
      have hf0 : f.natDegree = 0 := by lia
      have hg0 : g.natDegree = 0 := by lia
      have hf_len0 : (rootSeqDesc f).length = 0 := by simp [hf0, hfh.1.2]
      have hg_len0 : (rootSeqDesc g).length = 0 := by simp [hg0, hgh.1.2]
      exact rootSlotInterval_inter_nonempty_of_lengths_eq_zero hf_len0 hg_len0 jf jg
    · have hf_pos : 0 < f.natDegree := by lia
      have hg_pos : 0 < g.natDegree := by lia
      have hrevf_ne : (rootSeqDesc f).reverse ≠ [] :=
        rootSeqDesc_reverse_ne_nil_of_natDegree_pos hfh.1.2 hf_pos
      have hrevg_ne : (rootSeqDesc g).reverse ≠ [] :=
        rootSeqDesc_reverse_ne_nil_of_natDegree_pos hgh.1.2 hg_pos
      let af : ℝ := ((rootSeqDesc f).reverse).get
        ⟨0, by grind⟩
      let ag : ℝ := ((rootSeqDesc g).reverse).get
        ⟨0, by grind⟩
      have hslot_f :
          rootSlotInterval (rootSeqDesc f) jf = Set.Iic af := by
        simpa [af, jf, hj_eq_h, hf_eq_h, hfh.1.2] using
          rootSlotInterval_last_eq_reverse_get_zero
            (rs := rootSeqDesc f) (List.reverse_ne_nil_iff.mp hrevf_ne)
      have hslot_g :
          rootSlotInterval (rootSeqDesc g) jg = Set.Iic ag := by
        simpa [ag, jg, hj_eq_h, hg_eq_h, hgh.1.2] using
          rootSlotInterval_last_eq_reverse_get_zero
            (rs := rootSeqDesc g) (List.reverse_ne_nil_iff.mp hrevg_ne)
      simp_all

/-- Root-sequence common interleaver used for the Chudnovsky--Seymour proof.
The sequence `ps` is written in descending order and its `j`th entry lies in the
`j`th admissible interval of every root sequence in the family. -/
def HasCommonInterleaverSeq (fs : List ℝ[X]) : Prop :=
  ∀ j : ℕ, ∃ x : ℝ, ∀ f ∈ fs, ∀ hjf : j < (rootSeqDesc f).length + 1,
    x ∈ rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩

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
    have hget_i : ss.get i = slotSetAt j fi := by
      simp [ss, i', fi, List.get_eq_getElem]
    have hget_k : ss.get k = slotSetAt j fk := by
      simp [ss, k', fk, List.get_eq_getElem]
    rw [hget_i, hget_k]
    have hfi_rr : fi.Splits := hrr fi (List.get_mem _ _)
    have hfk_rr : fk.Splits := hrr fk (List.get_mem _ _)
    by_cases hjfi : j < (rootSeqDesc fi).length + 1
    · by_cases hjfk : j < (rootSeqDesc fk).length + 1
      · have hjfi' : j < fi.natDegree + 1 := by simpa [hfi_rr] using hjfi
        have hjfk' : j < fk.natDegree + 1 := by
          simpa [rootSeqDesc_length hfk_rr] using hjfk
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

private lemma pairwise_ge_of_commonInterleaverSeq
    {fs : List ℝ[X]}
    (hseq : HasCommonInterleaverSeq fs)
    (hrr : ∀ f ∈ fs, f.Splits)
    (hfs_ne : fs ≠ []) :
    let d := csDegree fs
    let xs : Fin d → ℝ := fun j => Classical.choose (hseq j.1)
    (List.ofFn xs).Pairwise (· ≥ ·) := by
  classical
  let d := csDegree fs
  let xs : Fin d → ℝ := fun j => Classical.choose (hseq j.1)
  obtain ⟨fmax, hfmax_mem, hfmax_deg⟩ := exists_mem_csDegree_of_ne_nil (fs := fs) hfs_ne
  have hfmax_rr : fmax.Splits := hrr fmax hfmax_mem
  refine List.pairwise_ofFn.2 ?_
  intro i j hij
  have hd_pos : 0 < d := by lia
  have hroot_ne : rootSeqDesc fmax ≠ [] :=
    rootSeqDesc_ne_nil_of_natDegree_pos hfmax_rr (by lia)
  have hi_slot : i.1 < (rootSeqDesc fmax).length + 1 := by
    rw [rootSeqDesc_length hfmax_rr, hfmax_deg]
    lia
  have hj_slot : j.1 < (rootSeqDesc fmax).length + 1 := by
    rw [rootSeqDesc_length hfmax_rr, hfmax_deg]
    lia
  have hxi :
      xs i ∈ rootSlotInterval (rootSeqDesc fmax) ⟨i.1, hi_slot⟩ :=
    (Classical.choose_spec (hseq i.1)) fmax hfmax_mem hi_slot
  have hxj :
      xs j ∈ rootSlotInterval (rootSeqDesc fmax) ⟨j.1, hj_slot⟩ :=
    (Classical.choose_spec (hseq j.1)) fmax hfmax_mem hj_slot
  exact
    le_of_mem_rootSlots_of_lt
      (rs := rootSeqDesc fmax)
      hroot_ne
      rootSeqDesc_pairwise
      (i := i.1) (j := j.1)
      (by lia)
      (by lia)
      hxi hxj

private def polyOfDescRoots (xs : List ℝ) : ℝ[X] :=
  (xs.map fun r => X - C r).prod

private lemma polyOfDescRoots_ne_zero (xs : List ℝ) :
    polyOfDescRoots xs ≠ 0 := by
  unfold polyOfDescRoots
  refine List.prod_ne_zero ?_
  intro h0
  rcases List.mem_map.mp h0 with ⟨r, hr, hr0⟩
  exact (X_sub_C_ne_zero r) hr0

private lemma roots_polyOfDescRoots (xs : List ℝ) :
    (polyOfDescRoots xs).roots = (↑xs : Multiset ℝ) := by
  unfold polyOfDescRoots
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.map_cons, List.prod_cons,
        roots_mul (mul_ne_zero (X_sub_C_ne_zero x)
          (by simpa [polyOfDescRoots] using polyOfDescRoots_ne_zero xs)),
        roots_X_sub_C, ih]
      simp

private lemma isRealRooted_polyOfDescRoots (xs : List ℝ) :
    ((polyOfDescRoots xs) ≠ 0 ∧ (polyOfDescRoots xs).Splits) := by
  unfold polyOfDescRoots
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simpa [List.map_cons, List.prod_cons] using
        isRealRooted_mul (isRealRooted_X_sub_C x).1 (isRealRooted_X_sub_C x).2 ih.1 ih.2

private lemma rootSeqDesc_polyOfDescRoots_eq
    {xs : List ℝ} (hxs : xs.Pairwise (· ≥ ·)) :
    rootSeqDesc (polyOfDescRoots xs) = xs := by
  have hrr : ((polyOfDescRoots xs) ≠ 0 ∧
    (polyOfDescRoots xs).Splits) := isRealRooted_polyOfDescRoots xs
  have hroots : (↑xs.reverse : Multiset ℝ) = (polyOfDescRoots xs).roots := by
    rw [roots_polyOfDescRoots]
    simp
  have hdesc :=
    rootSeqDesc_eq_reverse_of_pairwise
      (f := polyOfDescRoots xs)
      (rs := xs.reverse)
      (by grind)
      hroots
  simp_all

private lemma prec_of_slots_polyOfDescRoots {f : ℝ[X]} {xs : List ℝ} (hf₀ : f ≠ 0) (hf : f.Splits)
    (hxs : xs.Pairwise (· ≥ ·))
    (hdeg_lo : f.natDegree ≤ xs.length)
    (hdeg_hi : xs.length ≤ f.natDegree + 1)
    (hslot : ∀ j (hj : j < xs.length),
      xs.get ⟨j, hj⟩ ∈ rootSlotInterval (rootSeqDesc f)
        ⟨j, by
          have : j < f.natDegree + 1 := lt_of_lt_of_le hj hdeg_hi
          simpa [hf] using this⟩) :
    Prec f (polyOfDescRoots xs) := by
  let ss : List ℝ := (rootSeqDesc f).reverse
  let rs : List ℝ := xs.reverse
  have hss_pair : ss.Pairwise (· ≤ ·) := by
    simpa [ss] using (rootSeqDesc_pairwise (f := f)).reverse
  have hrs_pair : rs.Pairwise (· ≤ ·) := by grind
  have hss_eq : (↑ss : Multiset ℝ) = f.roots := by
    simp [ss, rootSeqDesc, Multiset.sort_eq]
  have hrs_eq : (↑rs : Multiset ℝ) = (polyOfDescRoots xs).roots := by
    simp [rs, roots_polyOfDescRoots]
  have hpoly_rr : ((polyOfDescRoots xs) ≠ 0 ∧
    (polyOfDescRoots xs).Splits) := isRealRooted_polyOfDescRoots xs
  have hlen_cases : xs.length = f.natDegree ∨ xs.length = f.natDegree + 1 := by lia
  refine ⟨⟨hf₀, hf⟩, hpoly_rr, ss, rs, hss_pair, hrs_pair, hss_eq, hrs_eq, ?_⟩
  rcases hlen_cases with hlen | hlen
  · refine Or.inr ?_
    refine ⟨?_, ?_⟩
    · simp [ss, rs, hlen, hf]
    · refine listAlternates_of_index_bounds ?_ ?_ ?_
      · simp [ss, rs, hlen, hf]
      · intro k hk
        have hk_deg : k < f.natDegree := by
          simpa [ss, hf] using hk
        let j : ℕ := f.natDegree - 1 - k
        have hjx : j < xs.length := by lia
        have hjf : j < (rootSeqDesc f).length + 1 := by grind
        have hmem : xs.get ⟨j, hjx⟩ ∈ rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ := by
          grind
        have hroot_ne : rootSeqDesc f ≠ [] := by grind
        have hj_root : j < (rootSeqDesc f).length := by
          rw [rootSeqDesc_length hf]
          lia
        have hlow :
            (rootSeqDesc f).get ⟨j, hj_root⟩ ≤ xs.get ⟨j, hjx⟩ :=
          rootSlot_lower_bound (rs := rootSeqDesc f) hroot_ne hj_root hmem
        have hss_get :
            ss.get ⟨k, hk⟩ = (rootSeqDesc f).get ⟨j, hj_root⟩ := by
          have hk_root : k < (rootSeqDesc f).length := by
            grind
          have hget :=
            get_reverse_eq_get_sub (xs := rootSeqDesc f) (k := k) hk_root
          have hidx : (rootSeqDesc f).length - 1 - k = j := by
            rw [rootSeqDesc_length hf]
          lia
        grind
      · intro k hk
        have hk_deg : k + 1 < f.natDegree := by
          simpa [ss, rootSeqDesc_length hf] using hk
        let j : ℕ := f.natDegree - 1 - k
        have hj_pos : 0 < j := by
          lia
        have hjx : j < xs.length := by
          lia
        have hjf : j < (rootSeqDesc f).length + 1 := by
          grind
        have hmem : xs.get ⟨j, hjx⟩ ∈ rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ := by
          grind
        have hroot_ne : rootSeqDesc f ≠ [] := by
          grind
        have hj_le : j ≤ (rootSeqDesc f).length := by
          lia
        have hup :
            xs.get ⟨j, hjx⟩ ≤ (rootSeqDesc f).get ⟨j - 1, by lia⟩ :=
          rootSlot_upper_bound (rs := rootSeqDesc f) hroot_ne hj_pos hj_le hmem
        have hrs_get :
            rs.get ⟨k, by
              have : k < f.natDegree := by lia
              simpa [ss, rs, hlen, rootSeqDesc_length hf] using this⟩
              = xs.get ⟨j, hjx⟩ := by
          have hk_xs : k < xs.length := by lia
          have hget := get_reverse_eq_get_sub (xs := xs) (k := k) hk_xs
          have hidx : xs.length - 1 - k = j := by
            dsimp [j]
            lia
          calc
            rs.get ⟨k, by
                have : k < f.natDegree := by lia
                simpa [ss, rs, hlen, rootSeqDesc_length hf] using this⟩
                = xs.get ⟨xs.length - 1 - k, by lia⟩ := by
                    simp [rs]
            _ = xs.get ⟨j, hjx⟩ := by
                  apply congrArg (fun i => xs.get i)
                  apply Fin.ext
                  exact hidx
        have hss_get :
            ss.get ⟨k + 1, hk⟩ = (rootSeqDesc f).get ⟨j - 1, by lia⟩ := by
          have hk1_root : k + 1 < (rootSeqDesc f).length := by
            simpa [ss, rootSeqDesc_length hf] using hk
          have hget :=
            get_reverse_eq_get_sub (xs := rootSeqDesc f) (k := k + 1) hk1_root
          have hidx : (rootSeqDesc f).length - 1 - (k + 1) = j - 1 := by
            rw [rootSeqDesc_length hf]
            dsimp [j]
            lia
          calc
            ss.get ⟨k + 1, hk⟩
                = (rootSeqDesc f).get ⟨(rootSeqDesc f).length - 1 - (k + 1), by lia⟩ := by
                    simp [ss]
            _ = (rootSeqDesc f).get ⟨j - 1, by lia⟩ := by
                  apply congrArg (fun i => (rootSeqDesc f).get i)
                  apply Fin.ext
                  exact hidx
        rw [hrs_get, hss_get]
        exact hup
  · refine Or.inl ?_
    refine ⟨?_, ?_⟩
    · simp [ss, rs, hlen, rootSeqDesc_length hf]
    · refine listInterlaces_of_index_bounds ?_ ?_ ?_
      · simp [ss, rs, hlen, rootSeqDesc_length hf]
      · intro k hk
        have hk_deg : k < f.natDegree := by
          simpa [ss, rootSeqDesc_length hf] using hk
        let j : ℕ := f.natDegree - k
        have hj_pos : 0 < j := by
          lia
        have hjx : j < xs.length := by
          lia
        have hjf : j < (rootSeqDesc f).length + 1 := by
          grind
        have hmem : xs.get ⟨j, hjx⟩ ∈ rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ := by
          grind
        have hroot_ne : rootSeqDesc f ≠ [] := by
          grind
        have hj_le : j ≤ (rootSeqDesc f).length := by
          lia
        have hup :
            xs.get ⟨j, hjx⟩ ≤ (rootSeqDesc f).get ⟨j - 1, by lia⟩ :=
          rootSlot_upper_bound (rs := rootSeqDesc f) hroot_ne hj_pos hj_le hmem
        have hrs_get :
            rs.get ⟨k, by
              have : k < f.natDegree + 1 := Nat.lt_succ_of_lt hk_deg
              simpa [ss, rs, hlen, rootSeqDesc_length hf] using this⟩
              = xs.get ⟨j, hjx⟩ := by
          have hk_xs : k < xs.length := by lia
          have hget := get_reverse_eq_get_sub (xs := xs) (k := k) hk_xs
          have hidx : xs.length - 1 - k = j := by
            dsimp [j]
            lia
          calc
            rs.get ⟨k, by
                have : k < f.natDegree + 1 := Nat.lt_succ_of_lt hk_deg
                simpa [ss, rs, hlen, rootSeqDesc_length hf] using this⟩
                = xs.get ⟨xs.length - 1 - k, by lia⟩ := by
                    simp [rs]
            _ = xs.get ⟨j, hjx⟩ := by
                  apply congrArg (fun i => xs.get i)
                  apply Fin.ext
                  exact hidx
        have hss_get :
            ss.get ⟨k, hk⟩ = (rootSeqDesc f).get ⟨j - 1, by lia⟩ := by
          have hk_root : k < (rootSeqDesc f).length := by
            simpa [ss, rootSeqDesc_length hf] using hk
          have hget :=
            get_reverse_eq_get_sub (xs := rootSeqDesc f) (k := k) hk_root
          have hidx : (rootSeqDesc f).length - 1 - k = j - 1 := by
            rw [rootSeqDesc_length hf]
            dsimp [j]
            lia
          calc
            ss.get ⟨k, hk⟩
                = (rootSeqDesc f).get ⟨(rootSeqDesc f).length - 1 - k, by lia⟩ := by
                    simp [ss]
            _ = (rootSeqDesc f).get ⟨j - 1, by lia⟩ := by
                  apply congrArg (fun i => (rootSeqDesc f).get i)
                  apply Fin.ext
                  exact hidx
        rw [hrs_get, hss_get]
        exact hup
      · intro k hk
        have hk_deg : k < f.natDegree := by
          simpa [ss, rootSeqDesc_length hf] using hk
        let j : ℕ := f.natDegree - 1 - k
        have hjx : j < xs.length := by
          lia
        have hjf : j < (rootSeqDesc f).length + 1 := by
          grind
        have hmem : xs.get ⟨j, hjx⟩ ∈ rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ := by
          grind
        have hroot_ne : rootSeqDesc f ≠ [] := by
          grind
        have hj_root : j < (rootSeqDesc f).length := by
          grind
        have hlow :
            (rootSeqDesc f).get ⟨j, hj_root⟩ ≤ xs.get ⟨j, hjx⟩ :=
          rootSlot_lower_bound (rs := rootSeqDesc f) hroot_ne hj_root hmem
        have hss_get :
            ss.get ⟨k, hk⟩ = (rootSeqDesc f).get ⟨j, hj_root⟩ := by
          have hk_root : k < (rootSeqDesc f).length := by
            grind
          have hget :=
            get_reverse_eq_get_sub (xs := rootSeqDesc f) (k := k) hk_root
          have hidx : (rootSeqDesc f).length - 1 - k = j := by
            rw [rootSeqDesc_length hf]
          lia
        grind

/-- Chudnovsky--Seymour `2 ⇒ 3` in the polynomial language used elsewhere in
this file: pairwise common interleavers can be upgraded to a single common
right interleaver. The intended route is through
`hasCommonInterleaverSeq_of_pairwiseHasCommonInterleaver`. -/
private theorem hasCommonInterleaver_of_pairwiseHasCommonInterleaver_ge_two
    {f g : ℝ[X]} {fs : List ℝ[X]}
    (hrr : ∀ p ∈ f :: g :: fs, p.Splits)
    (hpos : ∀ p ∈ f :: g :: fs, HasPosLeadingCoeff p)
    (hpair : PairwiseHasCommonInterleaver (f :: g :: fs)) :
    HasCommonInterleaver (f :: g :: fs) := by
  /-
  This is the genuine Chudnovsky--Seymour core. The base cases `[]` and `[f]`
  are handled separately below, so the remaining argument may freely assume the
  family has length at least `2`.
  -/
  let ps : List ℝ[X] := f :: g :: fs
  have hrr_ps : ∀ p ∈ ps, p.Splits := by
    grind
  have hpos_ps : ∀ p ∈ ps, HasPosLeadingCoeff p := by
    grind
  have hpair_ps : PairwiseHasCommonInterleaver ps := by
    lia
  have hseq :
      HasCommonInterleaverSeq ps :=
    hasCommonInterleaverSeq_of_pairwiseHasCommonInterleaver
      (fs := ps) hrr_ps hpair_ps
  have hps_ne : ps ≠ [] := by
    lia
  let d : ℕ := csDegree ps
  let xs : Fin d → ℝ := fun j => Classical.choose (hseq j.1)
  let xlist : List ℝ := List.ofFn xs
  have hx_pair : xlist.Pairwise (· ≥ ·) := by
    simpa [d, xs, xlist] using
      (pairwise_ge_of_commonInterleaverSeq (fs := ps) hseq hrr_ps hps_ne)
  let h : ℝ[X] := polyOfDescRoots xlist
  refine ⟨h, ?_⟩
  intro p hp
  have hp_mem : p ∈ ps := by lia
  have hp_rr : p.Splits := hrr_ps p hp_mem
  have hp_deg_lo : p.natDegree ≤ xlist.length := by
    have : p.natDegree ≤ csDegree ps := natDegree_le_csDegree (fs := ps) hp_mem
    grind
  have hp_deg_hi : xlist.length ≤ p.natDegree + 1 := by
    have : csDegree ps ≤ p.natDegree + 1 :=
      csDegree_le_natDegree_succ_of_pairwiseHasCommonInterleaver
        (fs := ps) (f := p) hps_ne hp_mem hpair_ps
    grind
  have hslot :
      ∀ j (hj : j < xlist.length),
        xlist.get ⟨j, hj⟩ ∈ rootSlotInterval (rootSeqDesc p)
          ⟨j, by
            have : j < p.natDegree + 1 := lt_of_lt_of_le hj hp_deg_hi
            simpa [rootSeqDesc_length hp_rr] using this⟩ := by
    grind
  have hp_prec : Prec p (polyOfDescRoots xlist) :=
    prec_of_slots_polyOfDescRoots (hpos p hp_mem).ne_zero hp_rr hx_pair hp_deg_lo hp_deg_hi hslot
  lia

theorem hasCommonInterleaver_of_pairwiseHasCommonInterleaver
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, f.Splits)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseHasCommonInterleaver fs) :
    HasCommonInterleaver fs := by
  cases fs with
  | nil =>
      refine ⟨1, ?_⟩
      simp
  | cons f fs =>
    cases fs with
    | nil =>
      refine ⟨f, ?_⟩
      intro p hp
      rcases List.mem_singleton.mp hp with rfl
      simpa using prec_refl (hpos p (by simp)).ne_zero (hrr p (by simp))
    | cons g fs =>
      exact
        hasCommonInterleaver_of_pairwiseHasCommonInterleaver_ge_two
          (f := f) (g := g) (fs := fs) hrr hpos hpair

/-- A common interleaver immediately implies real-rootedness of the full sum,
by Wagner's finite-sum theorem on the right. -/
theorem isRealRooted_sum_of_commonInterleaver
    {fs : List ℝ[X]}
    (hcommon : HasCommonInterleaver fs)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hne : fs ≠ []) : (fs.sum ≠ 0 ∧ fs.sum.Splits) := by
  rcases hcommon with ⟨h, hprec⟩
  exact (prec_sum_right fs h hprec hpos hne).1

/-- Left-oriented sum real-rootedness package used by the Brändén 7.8.3
product family. This is the direct Chudnovsky--Seymour `3 ⇒ m` step for a
family with a common left interleaver. It should not be routed through
`WeightedCompatibleLeft`: that recursive Wagner structure imposes coprimeness
conditions which a common left interleaver does not provide in general. -/
theorem isRealRooted_sum_of_commonLeftInterleaver
    {fs : List ℝ[X]}
    (hcommon : HasCommonLeftInterleaver fs)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hne : fs ≠ []) : (fs.sum ≠ 0 ∧ fs.sum.Splits) := by
  rcases hcommon with ⟨h, hprec⟩
  exact (prec_sum_left_of_common_left_signed fs h hprec hpos hne).2.1

/-- Public wrapper around the descending-root polynomial constructor used in
slot-based closure arguments. -/
def polyOfDescRootsDesc (xs : List ℝ) : ℝ[X] :=
  polyOfDescRoots xs

@[simp] theorem roots_polyOfDescRootsDesc (xs : List ℝ) :
    (polyOfDescRootsDesc xs).roots = (↑xs : Multiset ℝ) := by
  simpa [polyOfDescRootsDesc] using roots_polyOfDescRoots xs

@[simp] theorem rootSeqDesc_polyOfDescRootsDesc_eq
    {xs : List ℝ} (hxs : xs.Pairwise (· ≥ ·)) :
    rootSeqDesc (polyOfDescRootsDesc xs) = xs := by
  simpa [polyOfDescRootsDesc] using rootSeqDesc_polyOfDescRoots_eq hxs

/-- Public lower-bound wrapper for a point lying in a root slot. -/
theorem rootSlot_lower_bound_of_mem
    {rs : List ℝ} (hrs : rs ≠ []) {j : ℕ} (hj : j < rs.length) {x : ℝ}
    (hx : x ∈ rootSlotInterval rs ⟨j, by lia⟩) :
    rs.get ⟨j, hj⟩ ≤ x :=
  rootSlot_lower_bound hrs hj hx

/-- Public upper-bound wrapper for a point lying in a root slot. -/
theorem rootSlot_upper_bound_of_mem
    {rs : List ℝ} (hrs : rs ≠ []) {j : ℕ} (hj0 : 0 < j) (hj : j ≤ rs.length)
    {x : ℝ}
    (hx : x ∈ rootSlotInterval rs ⟨j, by lia⟩) :
    x ≤ rs.get ⟨j - 1, by lia⟩ :=
  rootSlot_upper_bound hrs hj0 hj hx

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
  le_of_mem_rootSlots_of_lt hrs_ne hrs hij hj hx hy

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
    rootSeqDesc_ne_nil_of_natDegree_pos hf (by lia)
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

/-- In a `Prec` witness, the `j`th descending root of the right polynomial lies
in the `j`th admissible slot of the left polynomial. -/
theorem mem_rootSlotInterval_of_prec_desc
    {f g : ℝ[X]} (hfg : Prec f g) (j : Fin g.natDegree) :
    (rootSeqDesc g).get ⟨j.1, by
      rcases hfg with ⟨_, hg, _, _, _, _, _, _, _⟩
      simp [rootSeqDesc, card_roots_of_splits hg.2]⟩ ∈ rootSlotInterval (rootSeqDesc f)
      ⟨j.1, by
        rcases hfg with ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩
        have hdeg := (natDegree_bounds_of_prec
          ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩).2
        simpa [hf, hg] using lt_of_lt_of_le j.2 hdeg⟩ :=
  mem_rootSlotInterval_of_prec hfg j

/-- Slot data against `rootSeqDesc f` reconstructs a `Prec` witness with the
descending-root polynomial built from those slot choices. -/
theorem prec_of_slots_polyOfDescRootsDesc {f : ℝ[X]} {xs : List ℝ} (hf₀ : f ≠ 0) (hf : f.Splits)
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
    prec_of_slots_polyOfDescRoots hf₀ hf hxs hdeg_lo hdeg_hi hslot

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
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  classical
  let n : ℕ := f.natDegree + 1
  let x : Fin n → ℝ := fun j => Classical.choose (hslot j.1 (by simpa [n] using j.2))
  let xs : List ℝ := List.ofFn x
  have hxs_len : xs.length = f.natDegree + 1 := by
    simp [xs, n]
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
        (by simp [n, hdeg]) (by simp [n, hdeg])
        (fun j hj => by
          have hraw := (Classical.choose_spec (hslot j (by simpa [n] using hj))).2
          simpa [x] using hraw)

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
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  classical
  let n : ℕ := f.natDegree + 1
  let x : Fin n → ℝ :=
    fun j => Classical.choose (hslot j.1 (by simpa [n] using j.2))
  let xs : List ℝ := List.ofFn x
  have hxs_len : xs.length = f.natDegree + 1 := by
    simp [xs, n]
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
        (by simp [n, hdeg]) (by simp [n, hdeg])
        (fun j hj => by
          have hraw := (Classical.choose_spec (hslot j (by simpa [n] using hj))).2
          simpa [x] using hraw)

/-- Reversing a weak zero-aware interlacing sequence with nonnegative
coefficients preserves the same structure. -/
lemma IsInterlacingSeq0Nonneg.reverse {fs : List ℝ[X]}
    (hfs : IsInterlacingSeq0Nonneg fs) :
    fs.reverse.Pairwise (fun f g => Prec0 g f) ∧
    ∀ f ∈ fs.reverse, HasNonnegCoeffs f :=
  ⟨hfs.1.reverse, fun f hf => hfs.2 f (by simpa using hf)⟩

end
end RealRooted
