import RealRooted.InterlacingSequenceBasic
import RealRooted.WeightedSum
import RealRooted.PosCombo

/-!
# Common interleavers and Chudnovsky-Seymour theorem

Root-slot interval machinery, the finite Helly lemma (`listInter`), `csDegree`,
the Chudnovsky-Seymour pairwise-to-global common-interleaver upgrade, and the
`polyOfDescRoots` construction.
-/

set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.unnecessarySimpa false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

open Polynomial

noncomputable section

namespace RealRooted

set_option linter.flexible false in
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

lemma rootSeqDesc_length {f : ℝ[X]} (hf : IsRealRooted f) :
    (rootSeqDesc f).length = f.natDegree := by
  simp [rootSeqDesc, hf.2]

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
  · simpa using hrs.reverse
  · exact Multiset.coe_eq_coe.mp (by simpa [rootSeqDesc, hrs_eq, Multiset.sort_eq])

lemma natDegree_bounds_of_prec {f g : ℝ[X]} (hfg : Prec f g) :
    f.natDegree ≤ g.natDegree ∧ g.natDegree ≤ f.natDegree + 1 := by
  rcases hfg with ⟨hf, hg, ss, rs, _hss, _hrs, hss_eq, hrs_eq, hshape⟩
  have hss_len : ss.length = f.natDegree := by
    rw [← Multiset.coe_card, hss_eq, hf.2]
  have hrs_len : rs.length = g.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, hg.2]
  rcases hshape with ⟨hlen, _⟩ | ⟨hlen, _⟩ <;> omega

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
    Set.Icc (rs.get ⟨j.1, by omega⟩) (rs.get ⟨j.1 - 1, by omega⟩)

lemma rootSlotInterval_nonempty (rs : List ℝ) (hrs : rs.Pairwise (· ≥ ·))
    (j : Fin (rs.length + 1)) : (rootSlotInterval rs j).Nonempty := by
  unfold rootSlotInterval
  by_cases h0 : j.1 = 0
  · cases rs with
    | nil =>
        simp [h0]
    | cons r rs =>
        exact ⟨r, by simp [h0]⟩
  · by_cases hj : j.1 = rs.length
    · by_cases hrs_nil : rs = []
      · have : j.1 = 0 := by simpa [hrs_nil] using hj
        exact (h0 this).elim
      · obtain ⟨r, tl, hrev⟩ := List.exists_cons_of_ne_nil
          ((List.reverse_ne_nil_iff.mpr hrs_nil))
        refine ⟨r, ?_⟩
        simp [h0, hj, hrev, hrs_nil]
    · refine ⟨rs.get ⟨j.1, by omega⟩, ?_⟩
      simp [h0, hj]
      have hjlt : j.1 < rs.length := by
        omega
      let jm1 : Fin rs.length := ⟨j.1 - 1, by omega⟩
      let jj : Fin rs.length := ⟨j.1, hjlt⟩
      have hpair := List.pairwise_iff_get.mp hrs
      have hlt : jm1 < jj := by
        show j.1 - 1 < j.1
        omega
      simpa [jm1, jj] using hpair jm1 jj hlt

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
      · have : j.1 = 0 := by simpa [hrs_nil] using hj
        exact (h0 this).elim
      · obtain ⟨r, tl, hrev⟩ := List.exists_cons_of_ne_nil
          ((List.reverse_ne_nil_iff.mpr hrs_nil))
        simpa [h0, hj, hrev, hrs_nil] using (Set.ordConnected_Iic : Set.OrdConnected (Set.Iic r))
    · simpa [h0, hj] using
        (Set.ordConnected_Icc : Set.OrdConnected
          (Set.Icc (rs.get ⟨j.1, by omega⟩) (rs.get ⟨j.1 - 1, by omega⟩)))

lemma rootSlotInterval_congr
    {xs ys : List ℝ}
    {jx : Fin (xs.length + 1)}
    {jy : Fin (ys.length + 1)}
    (hxy : xs = ys)
    (hji : jx.1 = jy.1) :
    rootSlotInterval xs jx = rootSlotInterval ys jy := by
  subst hxy
  have : jx = jy := Fin.ext hji
  subst this
  rfl

lemma mem_rootSlotInterval_congr
    {xs ys : List ℝ} {x : ℝ}
    {jx : Fin (xs.length + 1)}
    {jy : Fin (ys.length + 1)}
    (hxy : xs = ys)
    (hji : jx.1 = jy.1) :
    x ∈ rootSlotInterval xs jx ↔ x ∈ rootSlotInterval ys jy := by
  rw [rootSlotInterval_congr hxy hji]

private lemma listInterlaces_left_le_of_right_le {ss rs : List ℝ} {c : ℝ}
    (hint : ListInterlaces ss rs)
    (hrs : ∀ r ∈ rs, r ≤ c) :
    ∀ s ∈ ss, s ≤ c := by
  induction ss generalizing rs with
  | nil =>
      intro s hs
      simpa using hs
  | cons s ss ih =>
      cases rs with
      | nil =>
          simp [ListInterlaces] at hint
      | cons r₁ rs' =>
          cases rs' with
          | nil =>
              simp [ListInterlaces] at hint
          | cons r₂ rs'' =>
              rcases hint with ⟨_, hs_r₂, htail⟩
              intro t ht
              simp at ht
              rcases ht with rfl | ht
              · exact le_trans hs_r₂ (hrs r₂ (by simp))
              · exact ih htail (fun r hr => hrs r (by simp [hr])) t ht

private lemma listAlternates_left_le_of_right_le {ss rs : List ℝ} {c : ℝ}
    (halt : ListAlternates ss rs)
    (hrs : ∀ r ∈ rs, r ≤ c) :
    ∀ s ∈ ss, s ≤ c := by
  induction ss generalizing rs with
  | nil =>
      intro s hs
      simpa using hs
  | cons s ss ih =>
      cases rs with
      | nil =>
          simp [ListAlternates] at halt
      | cons r rs' =>
          rcases halt with ⟨hsr, htail⟩
          intro t ht
          simp at ht
          rcases ht with rfl | ht
          · exact le_trans hsr (hrs r (by simp))
          · exact listInterlaces_left_le_of_right_le htail
              (fun x hx => hrs x (by simp [hx])) t ht

private lemma listInterlaces_all_le_getLast
    {ss rs : List ℝ}
    (hrs_ne : rs ≠ [])
    (hrs : rs.Pairwise (· ≤ ·))
    (hint : ListInterlaces ss rs) :
    ∀ s ∈ ss, s ≤ rs.getLast hrs_ne := by
  induction ss generalizing rs with
  | nil =>
      intro s hs
      simpa using hs
  | cons s ss ih =>
      cases rs with
      | nil =>
          cases (hrs_ne rfl)
      | cons r rs' =>
          cases rs' with
          | nil =>
              simp [ListInterlaces] at hint
          | cons r₂ rs'' =>
              rcases hint with ⟨_, hs_r₂, htail⟩
              intro t ht
              rcases List.mem_cons.mp ht with rfl | ht
              · exact le_trans hs_r₂ (List.Pairwise.rel_getLast hrs (by simp [List.mem_cons]))
              · exact ih (rs := r₂ :: rs'') (by simp) ((List.pairwise_cons.mp hrs).2) htail t ht

private lemma listAlternates_all_le_getLast
    {ss rs : List ℝ}
    (hrs_ne : rs ≠ [])
    (hrs : rs.Pairwise (· ≤ ·))
    (halt : ListAlternates ss rs) :
    ∀ s ∈ ss, s ≤ rs.getLast hrs_ne := by
  induction ss generalizing rs with
  | nil =>
      intro s hs
      simpa using hs
  | cons s ss ih =>
      cases rs with
      | nil =>
          cases (hrs_ne rfl)
      | cons r rs' =>
          rcases halt with ⟨hsr, htail⟩
          intro t ht
          rcases List.mem_cons.mp ht with rfl | ht
          · exact le_trans hsr (List.Pairwise.rel_getLast hrs (by simp [List.mem_cons]))
          · exact listInterlaces_all_le_getLast (rs := r :: rs') (by simp) hrs htail t ht

private lemma reverse_get_zero_eq_getLast {xs : List ℝ} (hxs : xs ≠ []) :
    xs.reverse.get ⟨0, by simpa [List.length_reverse] using List.length_pos_iff_ne_nil.mpr hxs⟩ =
      xs.getLast hxs := by
  have hrev :
      xs.reverse.get ⟨0, by simpa [List.length_reverse] using List.length_pos_iff_ne_nil.mpr hxs⟩ =
      xs.get ⟨xs.length - 1, by
        simpa using (Nat.sub_lt (List.length_pos_iff_ne_nil.mpr hxs) (by decide : 0 < 1))⟩ := by
    simpa using (List.get_reverse' xs 0 (by
      simpa using (Nat.sub_lt (List.length_pos_iff_ne_nil.mpr hxs) (by decide : 0 < 1))))
  rw [hrev]
  simpa using (List.get_length_sub_one (l := xs) (by
    simpa using (Nat.sub_lt (List.length_pos_iff_ne_nil.mpr hxs) (by decide : 0 < 1))))

private lemma reverse_get_last_eq_get_zero {xs : List ℝ} (hxs : xs ≠ []) :
    xs.reverse.get ⟨xs.length - 1, by
      simpa [List.length_reverse] using
        (Nat.sub_lt (List.length_pos_iff_ne_nil.mpr hxs) (by decide : 0 < 1))⟩ =
      xs.get ⟨0, List.length_pos_iff_ne_nil.mpr hxs⟩ := by
  have hrev :
      xs.reverse.get ⟨xs.length - 1, by
        simpa [List.length_reverse] using
          (Nat.sub_lt (List.length_pos_iff_ne_nil.mpr hxs) (by decide : 0 < 1))⟩ =
      xs.get ⟨xs.length - 1 - (xs.length - 1), by
        have hpos : 0 < xs.length := List.length_pos_iff_ne_nil.mpr hxs
        omega⟩ := by
    simpa using (List.get_reverse' xs (xs.length - 1) (by
      have hpos : 0 < xs.length := List.length_pos_iff_ne_nil.mpr hxs
      omega))
  rw [hrev]
  congr
  have hpos : 0 < xs.length := List.length_pos_iff_ne_nil.mpr hxs
  omega

private lemma get_reverse_eq_get_sub {xs : List ℝ} {k : ℕ} (hk : k < xs.length) :
    xs.reverse.get ⟨k, by simpa [List.length_reverse] using hk⟩ =
      xs.get ⟨xs.length - 1 - k, by omega⟩ := by
  simpa using (List.get_reverse' xs ⟨k, hk⟩)

private lemma rootSlotInterval_zero_of_ne_nil {rs : List ℝ} (hrs : rs ≠ []) :
    rootSlotInterval rs
      ⟨0, by simpa using List.length_pos_iff_ne_nil.mpr hrs⟩ =
      Set.Ici (rs.get ⟨0, List.length_pos_iff_ne_nil.mpr hrs⟩) := by
  cases rs with
  | nil =>
      cases hrs rfl
  | cons r rs =>
      simp [rootSlotInterval]

private lemma rootSlotInterval_reverse_zero {xs : List ℝ} (hxs : xs ≠ []) :
    rootSlotInterval xs.reverse
      ⟨0, by simpa [List.length_reverse] using List.length_pos_iff_ne_nil.mpr hxs⟩ =
      Set.Ici (xs.getLast hxs) := by
  rw [rootSlotInterval_zero_of_ne_nil (List.reverse_ne_nil_iff.mpr hxs)]
  simpa using congrArg Set.Ici (reverse_get_zero_eq_getLast hxs)

private lemma rootSlotInterval_reverse_last {xs : List ℝ} (hxs : xs ≠ []) :
    rootSlotInterval xs.reverse
      ⟨xs.length, by simpa [List.length_reverse] using Nat.lt_succ_self xs.length⟩ =
      Set.Iic (xs.get ⟨0, List.length_pos_iff_ne_nil.mpr hxs⟩) := by
  cases xs with
  | nil =>
      cases hxs rfl
  | cons x xs =>
      have hsimp :
          rootSlotInterval (x :: xs).reverse
            ⟨(x :: xs).length, by simp [List.length_reverse]⟩ =
            Set.Iic (((x :: xs).reverse.reverse).get ⟨0, by simp⟩) := by
        simp [rootSlotInterval]
      rw [hsimp]
      simp

private lemma rootSlotInterval_last_of_ne_nil {rs : List ℝ} (hrs : rs ≠ []) :
    rootSlotInterval rs
      ⟨rs.length, by simpa using Nat.lt_succ_self rs.length⟩ =
      Set.Iic (rs.get ⟨rs.length - 1, by
        simpa using (Nat.sub_lt (List.length_pos_iff_ne_nil.mpr hrs) (by decide : 0 < 1))⟩) := by
  have h := rootSlotInterval_reverse_last (xs := rs.reverse)
    (List.reverse_ne_nil_iff.mpr hrs)
  have hcongr :
      rootSlotInterval rs.reverse.reverse
        ⟨rs.length, by simpa [List.length_reverse] using Nat.lt_succ_self rs.length⟩
        =
      rootSlotInterval rs
        ⟨rs.length, by simpa using Nat.lt_succ_self rs.length⟩ := by
    apply rootSlotInterval_congr
    · simp
    · rfl
  calc
    rootSlotInterval rs
        ⟨rs.length, by simpa using Nat.lt_succ_self rs.length⟩
        =
      rootSlotInterval rs.reverse.reverse
        ⟨rs.length, by simpa [List.length_reverse] using Nat.lt_succ_self rs.length⟩ := by
          simpa using hcongr.symm
    _ = Set.Iic (rs.get ⟨rs.length - 1, by
          simpa using
            (Nat.sub_lt (List.length_pos_iff_ne_nil.mpr hrs) (by decide : 0 < 1))⟩) := by
          simpa [List.length_reverse] using h

private lemma mem_rootSlotInterval_zero_lower {rs : List ℝ} (hrs : rs ≠ []) {x : ℝ}
    (hx : x ∈ rootSlotInterval rs
      ⟨0, by simpa using List.length_pos_iff_ne_nil.mpr hrs⟩) :
    rs.get ⟨0, List.length_pos_iff_ne_nil.mpr hrs⟩ ≤ x := by
  rw [rootSlotInterval_zero_of_ne_nil hrs] at hx
  exact Set.mem_Ici.mp hx

private lemma mem_rootSlotInterval_last_upper {rs : List ℝ} (hrs : rs ≠ []) {x : ℝ}
    (hx : x ∈ rootSlotInterval rs
      ⟨rs.length, by simpa using Nat.lt_succ_self rs.length⟩) :
    x ≤ rs.getLast hrs := by
  have hlast :
      rs.get ⟨rs.length - 1, by
        simpa using (Nat.sub_lt (List.length_pos_iff_ne_nil.mpr hrs) (by decide : 0 < 1))⟩
        = rs.getLast hrs := by
    simpa using (List.get_length_sub_one (l := rs) (by
      simpa using (Nat.sub_lt (List.length_pos_iff_ne_nil.mpr hrs) (by decide : 0 < 1))))
  rw [rootSlotInterval_last_of_ne_nil hrs] at hx
  exact hlast ▸ Set.mem_Iic.mp hx

private lemma mem_rootSlotInterval_interior_bounds
    {rs : List ℝ} {j : ℕ} (hj0 : 0 < j) (hj : j < rs.length) {x : ℝ}
    (hx : x ∈ rootSlotInterval rs ⟨j, by omega⟩) :
    rs.get ⟨j, hj⟩ ≤ x ∧ x ≤ rs.get ⟨j - 1, by omega⟩ := by
  unfold rootSlotInterval at hx
  have h0 : ¬ j = 0 := by omega
  have hlast : ¬ j = rs.length := by omega
  simpa [h0, hlast] using hx

private lemma getLast_eq_get_lastIndex {rs : List ℝ} (hrs : rs ≠ []) :
    rs.getLast hrs =
      rs.get ⟨rs.length - 1, by
        simpa using (Nat.sub_lt (List.length_pos_iff_ne_nil.mpr hrs) (by decide : 0 < 1))⟩ := by
  simpa using (List.get_length_sub_one (l := rs) (by
    simpa using (Nat.sub_lt (List.length_pos_iff_ne_nil.mpr hrs) (by decide : 0 < 1)))).symm

private lemma rootSlot_lower_bound
    {rs : List ℝ} (hrs : rs ≠ []) {j : ℕ} (hj : j < rs.length) {x : ℝ}
    (hx : x ∈ rootSlotInterval rs ⟨j, by omega⟩) :
    rs.get ⟨j, hj⟩ ≤ x := by
  by_cases hj0 : j = 0
  · subst hj0
    simpa using mem_rootSlotInterval_zero_lower (rs := rs) hrs hx
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    exact (mem_rootSlotInterval_interior_bounds (rs := rs) hjpos hj hx).1

private lemma rootSlot_upper_bound
    {rs : List ℝ} (hrs : rs ≠ []) {j : ℕ} (hj0 : 0 < j) (hj : j ≤ rs.length) {x : ℝ}
    (hx : x ∈ rootSlotInterval rs ⟨j, by omega⟩) :
    x ≤ rs.get ⟨j - 1, by omega⟩ := by
  by_cases hlast : j = rs.length
  · have hx_last : x ∈ rootSlotInterval rs
        ⟨rs.length, by simpa [hlast] using (show j < rs.length + 1 by omega)⟩ := by
      simpa [hlast] using hx
    have hlast_up : x ≤ rs.getLast hrs := mem_rootSlotInterval_last_upper (rs := rs) hrs hx_last
    have hlast_idx :
        rs.getLast hrs = rs.get ⟨j - 1, by omega⟩ := by
      calc
        rs.getLast hrs = rs.get ⟨rs.length - 1, by
          simpa using (Nat.sub_lt (List.length_pos_iff_ne_nil.mpr hrs) (by decide : 0 < 1))⟩ :=
            getLast_eq_get_lastIndex (rs := rs) hrs
        _ = rs.get ⟨j - 1, by omega⟩ := by
            apply congrArg (fun i => rs.get i)
            apply Fin.ext
            simpa [hlast]
    exact hlast_idx ▸ hlast_up
  · have hj_lt : j < rs.length := lt_of_le_of_ne hj hlast
    exact (mem_rootSlotInterval_interior_bounds (rs := rs) (j := j) hj0 hj_lt hx).2

private lemma le_of_mem_adjacent_rootSlots
    {rs : List ℝ} (hrs : rs ≠ []) {j : ℕ} (hj : j + 1 < rs.length + 1)
    {x y : ℝ}
    (hx : x ∈ rootSlotInterval rs ⟨j, by omega⟩)
    (hy : y ∈ rootSlotInterval rs ⟨j + 1, hj⟩) :
    y ≤ x := by
  have hj_lt : j < rs.length := by omega
  have hx_lower : rs.get ⟨j, hj_lt⟩ ≤ x :=
    rootSlot_lower_bound (rs := rs) hrs hj_lt hx
  by_cases hlast : j + 1 = rs.length
  · have hy_last : y ≤ rs.getLast hrs := by
      have hy' : y ∈ rootSlotInterval rs
          ⟨rs.length, by simpa [hlast] using hj⟩ := by
        simpa [hlast] using hy
      exact mem_rootSlotInterval_last_upper (rs := rs) hrs hy'
    have hidx : rs.getLast hrs = rs.get ⟨j, hj_lt⟩ := by
      have hlastIdx : j = rs.length - 1 := by omega
      calc
        rs.getLast hrs = rs.get ⟨rs.length - 1, by
          simpa using (Nat.sub_lt (List.length_pos_iff_ne_nil.mpr hrs) (by decide : 0 < 1))⟩ :=
            getLast_eq_get_lastIndex (rs := rs) hrs
        _ = rs.get ⟨j, hj_lt⟩ := by
            apply congrArg (fun i => rs.get i)
            apply Fin.ext
            simpa [hlastIdx]
    exact le_trans (hidx ▸ hy_last) hx_lower
  · have hj1_lt : j + 1 < rs.length := by omega
    have hy_bounds :=
      mem_rootSlotInterval_interior_bounds (rs := rs) (j := j + 1) (by omega) hj1_lt hy
    have hy_upper : y ≤ rs.get ⟨j, hj_lt⟩ := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hy_bounds.2
    exact le_trans hy_upper hx_lower

private lemma get_le_get_of_pairwise_ge
    {rs : List ℝ} (hrs : rs.Pairwise (· ≥ ·))
    {i j : Fin rs.length} (hij : i ≤ j) :
    rs.get j ≤ rs.get i := by
  rcases lt_or_eq_of_le hij with hij' | rfl
  · simpa using (List.pairwise_iff_get.mp hrs i j hij')
  · rfl

private lemma le_of_mem_rootSlots_of_lt
    {rs : List ℝ} (hrs_ne : rs ≠ []) (hrs : rs.Pairwise (· ≥ ·))
    {i j : ℕ} (hij : i < j) (hj : j < rs.length + 1)
    {x y : ℝ}
    (hx : x ∈ rootSlotInterval rs ⟨i, by omega⟩)
    (hy : y ∈ rootSlotInterval rs ⟨j, hj⟩) :
    y ≤ x := by
  have hi_lt : i < rs.length := by omega
  have hx_lower : rs.get ⟨i, hi_lt⟩ ≤ x :=
    rootSlot_lower_bound (rs := rs) hrs_ne hi_lt hx
  by_cases hlast : j = rs.length
  · have hy_last : y ≤ rs.getLast hrs_ne := by
      have hy' : y ∈ rootSlotInterval rs
          ⟨rs.length, by simpa [hlast] using hj⟩ := by
        simpa [hlast] using hy
      exact mem_rootSlotInterval_last_upper (rs := rs) hrs_ne hy'
    have hlast_idx :
        rs.getLast hrs_ne =
          rs.get ⟨rs.length - 1, by
            simpa using (Nat.sub_lt (List.length_pos_iff_ne_nil.mpr hrs_ne)
              (by decide : 0 < 1))⟩ :=
      getLast_eq_get_lastIndex (rs := rs) hrs_ne
    have htail_le_hi :
        rs.get ⟨rs.length - 1, by
          simpa using (Nat.sub_lt (List.length_pos_iff_ne_nil.mpr hrs_ne)
            (by decide : 0 < 1))⟩ ≤
          rs.get ⟨i, hi_lt⟩ := by
      refine get_le_get_of_pairwise_ge (rs := rs) hrs ?_
      exact by
        change
          (⟨i, hi_lt⟩ : Fin rs.length) ≤
            ⟨rs.length - 1, by
              simpa using (Nat.sub_lt (List.length_pos_iff_ne_nil.mpr hrs_ne)
                (by decide : 0 < 1))⟩
        apply Fin.le_def.2
        exact Nat.le_pred_of_lt hi_lt
    exact le_trans (hlast_idx ▸ hy_last) (le_trans htail_le_hi hx_lower)
  · have hj_lt : j < rs.length := by omega
    have hj_pos : 0 < j := by omega
    have hy_bounds :=
      mem_rootSlotInterval_interior_bounds (rs := rs) (j := j) hj_pos hj_lt hy
    have hy_upper :
        y ≤ rs.get ⟨j - 1, by omega⟩ := hy_bounds.2
    have hmid :
        rs.get ⟨j - 1, by omega⟩ ≤ rs.get ⟨i, hi_lt⟩ := by
      refine get_le_get_of_pairwise_ge (rs := rs) hrs ?_
      exact by
        change
          (⟨i, hi_lt⟩ : Fin rs.length) ≤
            ⟨j - 1, by omega⟩
        apply Fin.le_def.2
        exact Nat.le_pred_of_lt hij
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
  | nil =>
      cases hks
  | cons s ss ih =>
      cases rs with
      | nil =>
          cases hint
      | cons r₁ rs' =>
          cases rs' with
          | nil =>
              cases hint
          | cons r₂ rs'' =>
              rcases hint with ⟨hr₁s, hsr₂, htail⟩
              cases k with
              | zero =>
                  simpa using And.intro hr₁s hsr₂
              | succ k =>
                  have hks' : k < ss.length := by
                    simpa using hks
                  have hkr' : k + 1 < (r₂ :: rs'').length := by
                    simpa using hkr
                  simpa using ih htail hks' hkr'

private lemma listInterlaces_of_index_bounds
    {ss rs : List ℝ}
    (hlen : ss.length + 1 = rs.length)
    (hlower : ∀ k (hk : k < ss.length),
      rs.get ⟨k, by
        have : k < ss.length + 1 := lt_trans hk (Nat.lt_succ_self ss.length)
        simpa [hlen] using this⟩ ≤ ss.get ⟨k, hk⟩)
    (hupper : ∀ k (hk : k < ss.length),
      ss.get ⟨k, hk⟩ ≤ rs.get ⟨k + 1, by
        have : k + 1 < ss.length + 1 := Nat.succ_lt_succ hk
        simpa [hlen] using this⟩) :
    ListInterlaces ss rs := by
  induction ss generalizing rs with
  | nil =>
      cases rs with
      | nil =>
          simp at hlen
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
              have hr₁s : r₁ ≤ s := by
                simpa using hlower 0 (by simp)
              have hs_r₂ : s ≤ r₂ := by
                simpa using hupper 0 (by simp)
              have hlower' : ∀ k (hk : k < ss.length),
                  (r₂ :: rs').get ⟨k, by
                    have : k < ss.length + 1 := lt_trans hk (Nat.lt_succ_self ss.length)
                    simpa [hlen'] using this⟩ ≤ ss.get ⟨k, hk⟩ := by
                intro k hk
                have hk' : k + 1 < (s :: ss).length := by
                  simpa using Nat.succ_lt_succ hk
                simpa using hlower (k + 1) hk'
              have hupper' : ∀ k (hk : k < ss.length),
                  ss.get ⟨k, hk⟩ ≤ (r₂ :: rs').get ⟨k + 1, by
                    have : k + 1 < ss.length + 1 := Nat.succ_lt_succ hk
                    simpa [hlen'] using this⟩ := by
                intro k hk
                have hk' : k + 1 < (s :: ss).length := by
                  simpa using Nat.succ_lt_succ hk
                simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                  hupper (k + 1) hk'
              exact ⟨hr₁s, hs_r₂, ih hlen' hlower' hupper'⟩

private lemma listAlternates_of_index_bounds
    {ss rs : List ℝ}
    (hlen : ss.length = rs.length)
    (hlower : ∀ k (hk : k < ss.length),
      ss.get ⟨k, hk⟩ ≤ rs.get ⟨k, by simpa [hlen] using hk⟩)
    (hupper : ∀ k (hk : k + 1 < ss.length),
      rs.get ⟨k, by
        have : k < ss.length := lt_trans (Nat.lt_succ_self k) hk
        simpa [hlen] using this⟩ ≤ ss.get ⟨k + 1, hk⟩) :
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
          have hlen' : ss.length = rs.length := by
            simpa using Nat.succ.inj hlen
          have hs_r : s ≤ r := by
            simpa using hlower 0 (by simp)
          have hinter : ListInterlaces ss (r :: rs) := by
            refine listInterlaces_of_index_bounds ?_ ?_ ?_
            · simpa using hlen
            · intro k hk
              have hk' : k + 1 < (s :: ss).length := by
                simpa using Nat.succ_lt_succ hk
              simpa using hupper k hk'
            · intro k hk
              have hk' : k + 1 < (s :: ss).length := by
                simpa using Nat.succ_lt_succ hk
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
      cases hks
  | cons s ss ih =>
      cases rs with
      | nil =>
          cases hkr
      | cons r rs' =>
          rcases halt with ⟨hsr, htail⟩
          cases k with
          | zero =>
              simpa using hsr
          | succ k =>
              have hks' : k < ss.length := by
                simpa using hks
              have hkr' : k < rs'.length := by
                simpa using hkr
              simpa using (listInterlaces_get_bounds htail hks'
                (by simpa using Nat.succ_lt_succ hkr')).2

private lemma listAlternates_get_upper
    {ss rs : List ℝ}
    (halt : ListAlternates ss rs)
    {k : ℕ}
    (hk : k + 1 < ss.length)
    (hkr : k < rs.length) :
    rs.get ⟨k, hkr⟩ ≤ ss.get ⟨k + 1, hk⟩ := by
  induction ss generalizing rs k with
  | nil =>
      cases hk
  | cons s ss ih =>
      cases rs with
      | nil =>
          cases hkr
      | cons r rs' =>
          rcases halt with ⟨hsr, htail⟩
          cases k with
          | zero =>
              cases ss with
              | nil =>
                  have : False := by
                    simpa using hk
                  exact this.elim
              | cons s₂ ss₂ =>
                  cases rs' with
                  | nil =>
                      cases htail
                  | cons r₂ rs₂ =>
                      rcases htail with ⟨hr_s₂, hs₂_r₂, htail'⟩
                      simpa using hr_s₂
          | succ k =>
              cases ss with
              | nil =>
                  have : False := by
                    simpa using hk
                  exact this.elim
              | cons s₂ ss₂ =>
                  cases rs' with
                  | nil =>
                      cases htail
                  | cons r₂ rs₂ =>
                      rcases htail with ⟨hr_s₂, hs₂_r₂, htail'⟩
                      have halt' : ListAlternates (s₂ :: ss₂) (r₂ :: rs₂) := by
                        exact ⟨hs₂_r₂, htail'⟩
                      have hk' : k + 1 < (s₂ :: ss₂).length := by
                        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hk
                      have hkr' : k < (r₂ :: rs₂).length := by
                        simpa using hkr
                      simpa using ih halt' hk' hkr'

private lemma mem_rootSlotInterval_reverse_of_listInterlaces_interior
    {ss rs : List ℝ}
    (hss : ss.Pairwise (· ≤ ·))
    (hrs : rs.Pairwise (· ≤ ·))
    (hlen : ss.length + 1 = rs.length)
    (hint : ListInterlaces ss rs)
    {j : Fin rs.length}
    (h0 : j.1 ≠ 0)
    (hlast : j.1 ≠ ss.length) :
    rs.reverse.get ⟨j.1, by simpa [List.length_reverse] using j.2⟩ ∈ rootSlotInterval ss.reverse
      ⟨j.1, by simpa [List.length_reverse, hlen] using j.2⟩ := by
  have hj_pos : 0 < j.1 := Nat.pos_of_ne_zero h0
  have hjss : j.1 < ss.length := by
    omega
  have hnot_last : ¬ j.1 = ss.length := hlast
  let k : Fin rs.length := ⟨rs.length - 1 - j.1, by omega⟩
  let klow : Fin ss.length := ⟨ss.length - 1 - j.1, by omega⟩
  let khigh : Fin ss.length := ⟨ss.length - j.1, by omega⟩
  have hrs_rev :
      rs.reverse.get ⟨j.1, by simpa [List.length_reverse] using j.2⟩ = rs.get k := by
    simpa [k] using (List.get_reverse' rs ⟨j.1, j.2⟩)
  have hss_rev_lo :
      ss.reverse.get ⟨j.1, by simpa [List.length_reverse] using hjss⟩ = ss.get klow := by
    simpa [klow] using (List.get_reverse' ss ⟨j.1, hjss⟩)
  have hpred' : j.1 - 1 < ss.length := by
    omega
  have hpred : j.1 - 1 < ss.reverse.length := by
    simpa [List.length_reverse] using hpred'
  let kupper : Fin ss.length := ⟨ss.length - 1 - (j.1 - 1), by omega⟩
  have hkupper_eq : kupper = khigh := by
    apply Fin.ext
    simp [kupper, khigh]
    omega
  have hss_rev_hi :
      ss.reverse.get ⟨j.1 - 1, hpred⟩ = ss.get khigh := by
    rw [show ss.get khigh = ss.get kupper by simpa [hkupper_eq]]
    simpa [kupper] using (List.get_reverse' ss ⟨j.1 - 1, hpred⟩)
  have hslot :
      rootSlotInterval ss.reverse
        ⟨j.1, by simpa [List.length_reverse, hlen] using j.2⟩ =
        Set.Icc (ss.reverse.get ⟨j.1, by simpa [List.length_reverse] using hjss⟩)
          (ss.reverse.get ⟨j.1 - 1, hpred⟩) := by
    simp [rootSlotInterval, h0, hnot_last, List.length_reverse]
  rw [hslot, hrs_rev, hss_rev_lo, hss_rev_hi]
  have hklow_succ_lt : klow.1 + 1 < rs.length := by
    simp [klow, hlen]
    omega
  have hb_low := listInterlaces_get_bounds hint klow.2 hklow_succ_lt
  have hidx_low :
      (⟨klow.1 + 1, hklow_succ_lt⟩ : Fin rs.length) = k := by
    apply Fin.ext
    simp [klow, k, hlen]
    omega
  have hlower : ss.get klow ≤ rs.get k := by
    simpa [hidx_low] using hb_low.2
  have hkhigh_succ_lt : khigh.1 + 1 < rs.length := by
    simp [khigh, hlen]
    omega
  have hb_high := listInterlaces_get_bounds hint khigh.2 hkhigh_succ_lt
  have hidx_high :
      (⟨khigh.1, lt_trans (Nat.lt_succ_self khigh.1) hkhigh_succ_lt⟩ : Fin rs.length) = k := by
    apply Fin.ext
    simp [khigh, k, hlen]
    omega
  have hupper : rs.get k ≤ ss.get khigh := by
    simpa [hidx_high] using hb_high.1
  exact ⟨hlower, hupper⟩

private lemma mem_rootSlotInterval_reverse_of_listInterlaces_zero
    {ss rs : List ℝ}
    (hss : ss.Pairwise (· ≤ ·))
    (hrs : rs.Pairwise (· ≤ ·))
    (hlen : ss.length + 1 = rs.length)
    (hint : ListInterlaces ss rs) :
    rs.reverse.get ⟨0, by
      have : 0 < rs.length := by omega
      simpa [List.length_reverse] using this⟩ ∈
      rootSlotInterval ss.reverse
        ⟨0, by
          have : 0 < ss.reverse.length + 1 := by simp
          simpa [List.length_reverse] using this⟩ := by
  cases ss with
  | nil =>
      simp [rootSlotInterval] at hlen ⊢
  | cons s ss =>
      have hss_ne : (s :: ss) ≠ [] := by simp
      have hrs_pos : 0 < rs.length := by omega
      have hrs_ne : rs ≠ [] := List.length_pos_iff_ne_nil.mp hrs_pos
      rw [rootSlotInterval_reverse_zero hss_ne]
      rw [reverse_get_zero_eq_getLast hrs_ne]
      exact Set.mem_Ici.mpr <|
        listInterlaces_all_le_getLast hrs_ne hrs hint _ (List.getLast_mem hss_ne)

private lemma mem_rootSlotInterval_reverse_of_listInterlaces_last
    {ss rs : List ℝ}
    (hss : ss.Pairwise (· ≤ ·))
    (hrs : rs.Pairwise (· ≤ ·))
    (hlen : ss.length + 1 = rs.length)
    (hint : ListInterlaces ss rs)
    (hss_ne : ss ≠ []) :
    rs.reverse.get ⟨ss.length, by
      have : ss.length < rs.length := by omega
      simpa [List.length_reverse] using this⟩ ∈
      rootSlotInterval ss.reverse
        ⟨ss.length, by
          have : ss.length < ss.reverse.length + 1 := by
            simpa [List.length_reverse] using Nat.lt_succ_self ss.length
          simpa [List.length_reverse] using this⟩ := by
  have hrs_pos : 0 < rs.length := by omega
  have hrs_ne : rs ≠ [] := List.length_pos_iff_ne_nil.mp hrs_pos
  rw [rootSlotInterval_reverse_last hss_ne]
  have hidx :
      (⟨ss.length, by
        have : ss.length < rs.length := by omega
        simpa [List.length_reverse] using this⟩ : Fin rs.reverse.length) =
      ⟨rs.length - 1, by
        simpa [List.length_reverse] using
          (Nat.sub_lt (List.length_pos_iff_ne_nil.mpr hrs_ne) (by decide : 0 < 1))⟩ := by
    have hsub : ss.length = rs.length - 1 := by
      omega
    apply Fin.ext
    simpa [hsub]
  rw [hidx]
  rw [reverse_get_last_eq_get_zero hrs_ne]
  apply Set.mem_Iic.mpr
  have hss_pos : 0 < ss.length := List.length_pos_iff_ne_nil.mpr hss_ne
  have hb :=
    listInterlaces_get_bounds hint (k := 0)
      (by simpa using hss_pos)
      (by simpa [hlen] using Nat.succ_lt_succ hss_pos)
  simpa using hb.1

private lemma mem_rootSlotInterval_reverse_of_listInterlaces
    {ss rs : List ℝ}
    (hss : ss.Pairwise (· ≤ ·))
    (hrs : rs.Pairwise (· ≤ ·))
    (hlen : ss.length + 1 = rs.length)
    (hint : ListInterlaces ss rs)
    (j : Fin rs.length) :
    rs.reverse.get ⟨j.1, by simpa [List.length_reverse] using j.2⟩ ∈ rootSlotInterval ss.reverse
      ⟨j.1, by simpa [List.length_reverse, hlen] using j.2⟩ := by
  by_cases h0 : j.1 = 0
  · have hj :
        j = ⟨0, by
          have : 0 < rs.length := by
            simpa [h0] using j.2
          simpa [h0] using this⟩ := by
      apply Fin.ext
      simpa [h0]
    simpa [hj] using mem_rootSlotInterval_reverse_of_listInterlaces_zero hss hrs hlen hint
  · by_cases hlast : j.1 = ss.length
    · have hss_ne : ss ≠ [] := by
        intro hnil
        have : j.1 = 0 := by simpa [hnil] using hlast
        exact h0 this
      have hj :
          j = ⟨ss.length, by
            have : ss.length < rs.length := by omega
            simpa [hlast] using this⟩ := by
        apply Fin.ext
        simpa [hlast]
      simpa [hj] using
        mem_rootSlotInterval_reverse_of_listInterlaces_last hss hrs hlen hint hss_ne
    · exact
        mem_rootSlotInterval_reverse_of_listInterlaces_interior hss hrs hlen hint h0 hlast

private lemma mem_rootSlotInterval_reverse_of_listAlternates_interior
    {ss rs : List ℝ}
    (hss : ss.Pairwise (· ≤ ·))
    (hrs : rs.Pairwise (· ≤ ·))
    (hlen : ss.length = rs.length)
    (halt : ListAlternates ss rs)
    {j : Fin rs.length}
    (h0 : j.1 ≠ 0) :
    rs.reverse.get ⟨j.1, by simpa [List.length_reverse] using j.2⟩ ∈ rootSlotInterval ss.reverse
      ⟨j.1, by simpa [List.length_reverse, hlen] using j.2⟩ := by
  have hjss : j.1 < ss.length := by simpa [hlen] using j.2
  have hnot_last : ¬ j.1 = ss.length := ne_of_lt hjss
  let k : Fin ss.length := ⟨ss.length - 1 - j.1, by omega⟩
  have hk_succ : k.1 + 1 < ss.length := by
    simp [k]
    omega
  let ks : Fin ss.length := ⟨k.1 + 1, hk_succ⟩
  let kr : Fin rs.length := ⟨rs.length - 1 - j.1, by omega⟩
  have hkr_eq : kr.1 = k.1 := by
    simp [kr, k, hlen]
  have hks_eq : ks.1 = ss.length - j.1 := by
    simp [ks, k]
    omega
  have hrs_rev :
      rs.reverse.get ⟨j.1, by simpa [List.length_reverse] using j.2⟩ = rs.get kr := by
    simpa [kr] using (List.get_reverse' rs ⟨j.1, j.2⟩)
  have hss_rev_lo :
      ss.reverse.get ⟨j.1, by simpa [List.length_reverse, hlen] using j.2⟩ = ss.get k := by
    simpa [k, hlen] using (List.get_reverse' ss ⟨j.1, hjss⟩)
  have hpred' : j.1 - 1 < ss.length := by
    omega
  have hpred : j.1 - 1 < ss.reverse.length := by
    simpa [List.length_reverse] using hpred'
  let kupper : Fin ss.length := ⟨ss.length - 1 - (j.1 - 1), by
    omega⟩
  have hkupper_eq : kupper = ks := by
    apply Fin.ext
    simp [kupper, ks, k]
    omega
  have hss_rev_hi :
      ss.reverse.get ⟨j.1 - 1, hpred⟩ = ss.get ks := by
    rw [show ss.get ks = ss.get kupper by simpa [hkupper_eq]]
    simpa [kupper, hlen] using (List.get_reverse' ss ⟨j.1 - 1, hpred⟩)
  have hslot :
      rootSlotInterval ss.reverse
        ⟨j.1, by simpa [List.length_reverse, hlen] using j.2⟩ =
        Set.Icc (ss.reverse.get ⟨j.1, by simpa [List.length_reverse, hlen] using j.2⟩)
          (ss.reverse.get ⟨j.1 - 1, hpred⟩) := by
    simp [rootSlotInterval, h0, hnot_last, List.length_reverse]
  rw [hslot, hrs_rev, hss_rev_lo, hss_rev_hi]
  rw [show kr = ⟨k.1, by simpa [hkr_eq] using kr.2⟩ by
    apply Fin.ext
    exact hkr_eq]
  have hk_lower : ss.get k ≤ rs.get ⟨k.1, by simpa [hkr_eq] using kr.2⟩ := by
    exact listAlternates_get_lower halt k.2 (by simpa [hkr_eq] using kr.2)
  have hk_upper : rs.get ⟨k.1, by simpa [hkr_eq] using kr.2⟩ ≤ ss.get ks := by
    have hk_rs : k.1 < rs.length := by simpa [hkr_eq] using kr.2
    simpa [ks] using listAlternates_get_upper halt hk_succ hk_rs
  exact ⟨hk_lower, hk_upper⟩

private lemma mem_rootSlotInterval_reverse_of_listAlternates_zero
    {ss rs : List ℝ}
    (hss : ss.Pairwise (· ≤ ·))
    (hrs : rs.Pairwise (· ≤ ·))
    (hlen : ss.length = rs.length)
    (halt : ListAlternates ss rs)
    (hrs_ne : rs ≠ []) :
    rs.reverse.get ⟨0, by
      have : 0 < rs.length := List.length_pos_iff_ne_nil.mpr hrs_ne
      simpa [List.length_reverse] using this⟩ ∈
      rootSlotInterval ss.reverse
        ⟨0, by
          have : 0 < ss.reverse.length + 1 := by simp
          simpa [List.length_reverse] using this⟩ := by
  cases ss with
  | nil =>
      simp at hlen
      cases rs with
      | nil =>
          simp [rootSlotInterval]
      | cons r rs' =>
          cases hlen
  | cons s ss =>
      have hss_ne : (s :: ss) ≠ [] := by simp
      have hrs_ne : rs ≠ [] := by
        apply List.length_pos_iff_ne_nil.mp
        have : 0 < (s :: ss).length := by simp
        simpa [hlen] using this
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
    rs.reverse.get ⟨j.1, by simpa [List.length_reverse] using j.2⟩ ∈ rootSlotInterval ss.reverse
      ⟨j.1, by simpa [List.length_reverse, hlen] using j.2⟩ := by
  by_cases h0 : j.1 = 0
  · have hj :
        j = ⟨0, by
          have : 0 < rs.length := by simpa [h0] using j.2
          simpa [h0] using this⟩ := by
      apply Fin.ext
      simpa [h0]
    have hrs_ne : rs ≠ [] := List.length_pos_iff_ne_nil.mp (by simpa [h0] using j.2)
    simpa [hj] using mem_rootSlotInterval_reverse_of_listAlternates_zero hss hrs hlen halt hrs_ne
  · exact mem_rootSlotInterval_reverse_of_listAlternates_interior hss hrs hlen halt h0

/-- Slot transport from an ascending `Prec` witness to the descending
Chudnovsky--Seymour interval language. This is the core bridge needed to turn
pairwise common interleavers into pairwise-intersecting slot intervals. -/
private lemma mem_rootSlotInterval_of_prec_witness
    {f g : ℝ[X]} {ss rs : List ℝ}
    (hf : IsRealRooted f) (hg : IsRealRooted g)
    (hss : ss.Pairwise (· ≤ ·)) (hrs : rs.Pairwise (· ≤ ·))
    (hss_eq : (↑ss : Multiset ℝ) = f.roots)
    (hrs_eq : (↑rs : Multiset ℝ) = g.roots)
    (hshape : (ss.length + 1 = rs.length ∧ ListInterlaces ss rs) ∨
      (ss.length = rs.length ∧ ListAlternates ss rs))
    (j : Fin rs.length) :
    rs.reverse.get ⟨j.1, by simpa [List.length_reverse] using j.2⟩ ∈
      rootSlotInterval ss.reverse
        ⟨j.1, by
          have hdeg : f.natDegree ≤ g.natDegree ∧ g.natDegree ≤ f.natDegree + 1 := by
            exact natDegree_bounds_of_prec ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩
          have hss_len : ss.length = f.natDegree := by
            rw [← Multiset.coe_card, hss_eq, hf.2]
          have hrs_len : rs.length = g.natDegree := by
            rw [← Multiset.coe_card, hrs_eq, hg.2]
          have hdeg' : rs.length ≤ ss.length + 1 := by
            simpa [hss_len, hrs_len] using hdeg.2
          have : j.1 < ss.reverse.length + 1 := by
            simpa [List.length_reverse] using lt_of_lt_of_le j.2 hdeg'
          exact this⟩ := by
  rcases hshape with ⟨hlen, hint⟩ | ⟨hlen, halt⟩
  · simpa using mem_rootSlotInterval_reverse_of_listInterlaces hss hrs hlen hint j
  · simpa using mem_rootSlotInterval_reverse_of_listAlternates hss hrs hlen halt j

private lemma mem_rootSlotInterval_of_prec
    {f g : ℝ[X]} (hfg : Prec f g) (j : Fin g.natDegree) :
    (rootSeqDesc g).get ⟨j.1, by
      rcases hfg with ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩
      simpa [rootSeqDesc, hg.2, hrs_eq] using j.2⟩ ∈ rootSlotInterval (rootSeqDesc f)
      ⟨j.1, by
        rcases hfg with ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩
        have hdeg := (natDegree_bounds_of_prec ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩).2
        simpa [rootSeqDesc_length hf, rootSeqDesc_length hg] using
          lt_of_lt_of_le j.2 hdeg⟩ := by
  rcases hfg with ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩
  have hss_desc : rootSeqDesc f = ss.reverse := rootSeqDesc_eq_reverse_of_pairwise hss hss_eq
  have hrs_desc : rootSeqDesc g = rs.reverse := rootSeqDesc_eq_reverse_of_pairwise hrs hrs_eq
  have hdeg := (natDegree_bounds_of_prec ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩).2
  have hss_len : ss.length = f.natDegree := by
    rw [← Multiset.coe_card, hss_eq, hf.2]
  have hrs_len : rs.length = g.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, hg.2]
  let jg_desc : Fin (rootSeqDesc g).length := ⟨j.1, by
    simpa [rootSeqDesc, hg.2, hrs_eq] using j.2⟩
  let jg_rev : Fin rs.reverse.length := ⟨j.1, by
    simpa [List.length_reverse, hrs_len] using j.2⟩
  let jf_desc : Fin ((rootSeqDesc f).length + 1) := ⟨j.1, by
    simpa [rootSeqDesc_length hf, rootSeqDesc_length hg] using lt_of_lt_of_le j.2 hdeg⟩
  let jf_rev : Fin (ss.reverse.length + 1) := ⟨j.1, by
    simpa [List.length_reverse, hss_len, hrs_len] using lt_of_lt_of_le j.2 hdeg⟩
  have hmem_rev : rs.reverse.get jg_rev ∈ rootSlotInterval ss.reverse jf_rev :=
    mem_rootSlotInterval_of_prec_witness hf hg hss hrs hss_eq hrs_eq hshape
      ⟨j.1, by simpa [hrs_len] using j.2⟩
  have hmem_desc : rs.reverse.get jg_rev ∈ rootSlotInterval (rootSeqDesc f) jf_desc := by
    exact (mem_rootSlotInterval_congr (x := rs.reverse.get jg_rev)
      (jx := jf_rev) (jy := jf_desc) hss_desc.symm rfl).mp hmem_rev
  have hget : (rootSeqDesc g).get jg_desc = rs.reverse.get jg_rev := by
    simpa [jg_desc, jg_rev, hrs_desc]
  have hgoal : (rootSeqDesc g).get jg_desc ∈ rootSlotInterval (rootSeqDesc f) jf_desc := by
    rw [hget]
    exact hmem_desc
  simpa [jg_desc, jf_desc] using hgoal

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
      simpa [listInter] using Set.univ_nonempty
  | cons s ss ih =>
      cases ss with
      | nil =>
          simpa [listInter] using hne s (by simp)
      | cons t ts =>
          have hhead : ∀ u ∈ t :: ts, (s ∩ u).Nonempty := (List.pairwise_cons.mp hpair).1
          have htail : (t :: ts).Pairwise fun s t => (s ∩ t).Nonempty :=
            (List.pairwise_cons.mp hpair).2
          have htail_ne : (listInter (t :: ts)).Nonempty := by
            apply ih
            · intro u hu
              exact hne u (by simp [hu])
            · intro u hu
              exact hconn u (by simp [hu])
            · exact htail
          rcases htail_ne with ⟨x, hx⟩
          by_cases hxs : x ∈ s
          · exact ⟨x, by simpa [listInter, hxs] using hx⟩
          · let ys : List ℝ := (List.attach (t :: ts)).map
              (fun u => Classical.choose (hhead u.1 u.2))
            have hys_pos : 0 < ys.length := by
              simp [ys]
            have hy_mem_s : ∀ y ∈ ys, y ∈ s := by
              intro y hy
              rcases List.mem_map.mp hy with ⟨u, hu, rfl⟩
              exact (Classical.choose_spec (hhead u.1 u.2)).1
            have hx_mem : ∀ u ∈ t :: ts, x ∈ u := by
              intro u hu
              exact (mem_listInter.mp hx) u hu
            let y0 : ℝ := Classical.choose (hhead t (by simp))
            have hy0s : y0 ∈ s := (Classical.choose_spec (hhead t (by simp))).1
            have hy0_side : y0 < x ∨ x < y0 := by
              have hy0_ne : y0 ≠ x := by
                intro hyx
                apply hxs
                simpa [y0, hyx] using hy0s
              exact lt_or_gt_of_ne hy0_ne
            rcases hy0_side with hy0lt | hxy0
            · let y : ℝ := ys.maximum_of_length_pos hys_pos
              have hy_mem : y ∈ ys := List.maximum_of_length_pos_mem hys_pos
              have hys : y ∈ s := hy_mem_s y hy_mem
              have hall_lt : ∀ z ∈ ys, z < x := by
                intro z hz
                have hzs : z ∈ s := hy_mem_s z hz
                by_cases hzx : z < x
                · exact hzx
                · have hxz : x < z := by
                    have hxle : x ≤ z := le_of_not_gt hzx
                    have hne_xz : x ≠ z := by
                      intro hxz_eq
                      apply hxs
                      simpa [hxz_eq] using hzs
                    exact lt_of_le_of_ne hxle hne_xz
                  have hx_in_s : x ∈ s := (hconn s (by simp)).out hy0s hzs ⟨hy0lt.le, hxz.le⟩
                  exact (hxs hx_in_s).elim
              refine ⟨y, ?_⟩
              rw [mem_listInter]
              intro u hu
              have hu' : u = s ∨ u ∈ t :: ts := by simpa using hu
              rcases hu' with rfl | hu
              · exact hys
              · let yu : ℝ := Classical.choose (hhead u hu)
                have hyu_mem : yu ∈ ys := by
                  have hmem_attach : (⟨u, hu⟩ : {v // v ∈ t :: ts}) ∈ (t :: ts).attach := by
                    exact List.mem_attach _ _
                  exact List.mem_map.mpr ⟨⟨u, hu⟩, hmem_attach, rfl⟩
                have hyu_le : yu ≤ y := List.le_maximum_of_length_pos_of_mem hyu_mem hys_pos
                have hy_lt : y < x := hall_lt y hy_mem
                have hyu_u : yu ∈ u := (Classical.choose_spec (hhead u hu)).2
                have hx_u : x ∈ u := hx_mem u hu
                exact (hconn u (by simp [hu])).out hyu_u hx_u ⟨hyu_le, hy_lt.le⟩
            · let y : ℝ := ys.minimum_of_length_pos hys_pos
              have hy_mem : y ∈ ys := List.minimum_of_length_pos_mem hys_pos
              have hys : y ∈ s := hy_mem_s y hy_mem
              have hall_gt : ∀ z ∈ ys, x < z := by
                intro z hz
                have hzs : z ∈ s := hy_mem_s z hz
                by_cases hxz : x < z
                · exact hxz
                · have hzx : z < x := by
                    have hzle : z ≤ x := le_of_not_gt hxz
                    have hne_zx : z ≠ x := by
                      intro hzx_eq
                      apply hxs
                      simpa [hzx_eq] using hzs
                    exact lt_of_le_of_ne hzle hne_zx
                  have hx_in_s : x ∈ s := (hconn s (by simp)).out hzs hy0s ⟨hzx.le, hxy0.le⟩
                  exact (hxs hx_in_s).elim
              refine ⟨y, ?_⟩
              rw [mem_listInter]
              intro u hu
              have hu' : u = s ∨ u ∈ t :: ts := by simpa using hu
              rcases hu' with rfl | hu
              · exact hys
              · let yu : ℝ := Classical.choose (hhead u hu)
                have hyu_mem : yu ∈ ys := by
                  have hmem_attach : (⟨u, hu⟩ : {v // v ∈ t :: ts}) ∈ (t :: ts).attach := by
                    exact List.mem_attach _ _
                  exact List.mem_map.mpr ⟨⟨u, hu⟩, hmem_attach, rfl⟩
                have hle_yu : y ≤ yu := List.minimum_of_length_pos_le_of_mem hyu_mem hys_pos
                have hx_lt : x < y := hall_gt y hy_mem
                have hyu_u : yu ∈ u := (Classical.choose_spec (hhead u hu)).2
                have hx_u : x ∈ u := hx_mem u hu
                exact (hconn u (by simp [hu])).out hx_u hyu_u ⟨hx_lt.le, hle_yu⟩

/-- The target length `d` in the Chudnovsky--Seymour construction: the maximum
degree occurring in the family. -/
def csDegree (fs : List ℝ[X]) : ℕ :=
  (fs.map Polynomial.natDegree).foldr max 0

lemma natDegree_le_csDegree {fs : List ℝ[X]} {f : ℝ[X]} (hf : f ∈ fs) :
    f.natDegree ≤ csDegree fs := by
  unfold csDegree
  exact List.le_max_of_le (by simpa using List.mem_map.mpr ⟨f, hf, rfl⟩) le_rfl

lemma csDegree_eq_zero_of_nil : csDegree ([] : List ℝ[X]) = 0 := by
  simp [csDegree]

lemma exists_mem_csDegree_of_ne_nil {fs : List ℝ[X]} (hfs : fs ≠ []) :
    ∃ f ∈ fs, f.natDegree = csDegree fs := by
  induction fs with
  | nil =>
      contradiction
  | cons f fs ih =>
      cases fs with
      | nil =>
          refine ⟨f, by simp, by simp [csDegree]⟩
      | cons g gs =>
          by_cases htail : csDegree (g :: gs) ≤ f.natDegree
          · refine ⟨f, by simp, ?_⟩
            simpa [csDegree] using htail
          · have hne_tail : g :: gs ≠ [] := by simp
            obtain ⟨p, hp, hpdeg⟩ := ih hne_tail
            refine ⟨p, by simp [hp], ?_⟩
            have hltail : f.natDegree ≤ csDegree (g :: gs) := by omega
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
  · rw [← hgj]
    exact Nat.le_succ (fs.get i).natDegree
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
  rw [hgmax] at hbound
  exact hbound

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
        ⟨j, by simpa [rootSeqDesc_length hfh.1] using hjf⟩ ∩
      rootSlotInterval (rootSeqDesc g)
        ⟨j, by simpa [rootSeqDesc_length hgh.1] using hjg⟩).Nonempty := by
  let jf : Fin ((rootSeqDesc f).length + 1) := ⟨j, by
    simpa [rootSeqDesc_length hfh.1] using hjf⟩
  let jg : Fin ((rootSeqDesc g).length + 1) := ⟨j, by
    simpa [rootSeqDesc_length hgh.1] using hjg⟩
  change (rootSlotInterval (rootSeqDesc f) jf ∩
    rootSlotInterval (rootSeqDesc g) jg).Nonempty
  have hdeg_fh : f.natDegree ≤ h.natDegree ∧ h.natDegree ≤ f.natDegree + 1 :=
    natDegree_bounds_of_prec hfh
  have hdeg_gh : g.natDegree ≤ h.natDegree ∧ h.natDegree ≤ g.natDegree + 1 :=
    natDegree_bounds_of_prec hgh
  have hh_rr : IsRealRooted h := hfh.2.1
  by_cases hjh : j < h.natDegree
  · let jh : Fin h.natDegree := ⟨j, hjh⟩
    let x : ℝ := (rootSeqDesc h).get ⟨j, by
      simpa [rootSeqDesc_length hh_rr] using hjh⟩
    have hmem_f : x ∈ rootSlotInterval (rootSeqDesc f) jf := by
      simpa [x, jf, jh] using (mem_rootSlotInterval_of_prec hfh jh)
    have hmem_g : x ∈ rootSlotInterval (rootSeqDesc g) jg := by
      simpa [x, jg, jh] using (mem_rootSlotInterval_of_prec hgh jh)
    exact ⟨x, ⟨hmem_f, hmem_g⟩⟩
  · have hj_eq_h : j = h.natDegree := by omega
    have hf_eq_h : f.natDegree = h.natDegree := by omega
    have hg_eq_h : g.natDegree = h.natDegree := by omega
    by_cases hdeg0 : h.natDegree = 0
    · have hj0 : j = 0 := by omega
      have hf0 : f.natDegree = 0 := by omega
      have hg0 : g.natDegree = 0 := by omega
      have hf_len0 : (rootSeqDesc f).length = 0 := by
        simpa [hf0] using rootSeqDesc_length hfh.1
      have hg_len0 : (rootSeqDesc g).length = 0 := by
        simpa [hg0] using rootSeqDesc_length hgh.1
      let j0nil : Fin (([] : List ℝ).length + 1) := ⟨0, by simp⟩
      have hslot_f :
          rootSlotInterval (rootSeqDesc f) jf = rootSlotInterval [] j0nil := by
        apply rootSlotInterval_congr
        · exact List.length_eq_zero_iff.mp hf_len0
        · simp [jf, j0nil, hj0]
      have hslot_g :
          rootSlotInterval (rootSeqDesc g) jg = rootSlotInterval [] j0nil := by
        apply rootSlotInterval_congr
        · exact List.length_eq_zero_iff.mp hg_len0
        · simp [jg, j0nil, hj0]
      refine ⟨0, ?_⟩
      refine ⟨?_, ?_⟩
      · rw [hslot_f]
        simp [rootSlotInterval, j0nil]
      · rw [hslot_g]
        simp [rootSlotInterval, j0nil]
    · have hf_pos : 0 < f.natDegree := by omega
      have hg_pos : 0 < g.natDegree := by omega
      have hrevf_ne : (rootSeqDesc f).reverse ≠ [] := by
        apply List.ne_nil_of_length_pos
        simpa [List.length_reverse, rootSeqDesc_length hfh.1] using hf_pos
      have hrevg_ne : (rootSeqDesc g).reverse ≠ [] := by
        apply List.ne_nil_of_length_pos
        simpa [List.length_reverse, rootSeqDesc_length hgh.1] using hg_pos
      let af : ℝ := ((rootSeqDesc f).reverse).get
        ⟨0, by simpa [List.length_reverse, rootSeqDesc_length hfh.1] using hf_pos⟩
      let ag : ℝ := ((rootSeqDesc g).reverse).get
        ⟨0, by simpa [List.length_reverse, rootSeqDesc_length hgh.1] using hg_pos⟩
      have hslot_f :
          rootSlotInterval (rootSeqDesc f) jf = Set.Iic af := by
        let jfr : Fin ((((rootSeqDesc f).reverse).reverse).length + 1) :=
          ⟨(rootSeqDesc f).reverse.length, by
            simpa [List.length_reverse] using
              Nat.lt_succ_self ((rootSeqDesc f).reverse.length)⟩
        have hbase :
            rootSlotInterval ((rootSeqDesc f).reverse).reverse jfr = Set.Iic af := by
          simpa [jfr, af] using
            rootSlotInterval_reverse_last (xs := (rootSeqDesc f).reverse) hrevf_ne
        have hcongr :
            rootSlotInterval ((rootSeqDesc f).reverse).reverse jfr =
            rootSlotInterval (rootSeqDesc f) jf := by
          apply rootSlotInterval_congr
          · simp
          · simp [jfr, jf, hj_eq_h, hf_eq_h, rootSeqDesc_length hfh.1, List.length_reverse]
        calc
          rootSlotInterval (rootSeqDesc f) jf
              = rootSlotInterval ((rootSeqDesc f).reverse).reverse jfr := by
                  simpa using hcongr.symm
          _ = Set.Iic af := hbase
      have hslot_g :
          rootSlotInterval (rootSeqDesc g) jg = Set.Iic ag := by
        let jgr : Fin ((((rootSeqDesc g).reverse).reverse).length + 1) :=
          ⟨(rootSeqDesc g).reverse.length, by
            simpa [List.length_reverse] using
              Nat.lt_succ_self ((rootSeqDesc g).reverse.length)⟩
        have hbase :
            rootSlotInterval ((rootSeqDesc g).reverse).reverse jgr = Set.Iic ag := by
          simpa [jgr, ag] using
            rootSlotInterval_reverse_last (xs := (rootSeqDesc g).reverse) hrevg_ne
        have hcongr :
            rootSlotInterval ((rootSeqDesc g).reverse).reverse jgr =
            rootSlotInterval (rootSeqDesc g) jg := by
          apply rootSlotInterval_congr
          · simp
          · simp [jgr, jg, hj_eq_h, hg_eq_h, rootSeqDesc_length hgh.1, List.length_reverse]
        calc
          rootSlotInterval (rootSeqDesc g) jg
              = rootSlotInterval ((rootSeqDesc g).reverse).reverse jgr := by
                  simpa using hcongr.symm
          _ = Set.Iic ag := hbase
      refine ⟨min af ag, ?_⟩
      refine ⟨?_, ?_⟩
      · rw [hslot_f]
        exact Set.mem_Iic.mpr (min_le_left _ _)
      · rw [hslot_g]
        exact Set.mem_Iic.mpr (min_le_right _ _)

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
  · simpa [hj] using Set.univ_nonempty

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
    (hrr : ∀ f ∈ fs, IsRealRooted f)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
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
    let i' : Fin fs.length := ⟨i.1, by simpa [hss_len] using i.2⟩
    let k' : Fin fs.length := ⟨k.1, by simpa [hss_len] using k.2⟩
    have hik' : i' < k' := by simpa [i', k'] using hik
    let fi : ℝ[X] := fs.get i'
    let fk : ℝ[X] := fs.get k'
    have hget_i : ss.get i = slotSetAt j fi := by
      simp [ss, i', fi, List.get_eq_getElem]
    have hget_k : ss.get k = slotSetAt j fk := by
      simp [ss, k', fk, List.get_eq_getElem]
    rw [hget_i, hget_k]
    have hfi_rr : IsRealRooted fi := hrr fi (List.get_mem _ _)
    have hfk_rr : IsRealRooted fk := hrr fk (List.get_mem _ _)
    by_cases hjfi : j < (rootSeqDesc fi).length + 1
    · by_cases hjfk : j < (rootSeqDesc fk).length + 1
      · have hjfi' : j < fi.natDegree + 1 := by
          simpa [rootSeqDesc_length hfi_rr] using hjfi
        have hjfk' : j < fk.natDegree + 1 := by
          simpa [rootSeqDesc_length hfk_rr] using hjfk
        rcases hpair i' k' hik' with ⟨hh, hfi_h, hfk_h⟩
        simpa [slotSetAt, hjfi, hjfk] using
          (rootSlotInterval_inter_nonempty_of_commonInterleaver hfi_h hfk_h j hjfi' hjfk')
      · simpa [slotSetAt, hjfi, hjfk] using
          (rootSlotInterval_nonempty (rs := rootSeqDesc fi) (rootSeqDesc_pairwise) ⟨j, hjfi⟩)
    · by_cases hjfk : j < (rootSeqDesc fk).length + 1
      · simpa [slotSetAt, hjfi, hjfk] using
          (rootSlotInterval_nonempty (rs := rootSeqDesc fk) (rootSeqDesc_pairwise) ⟨j, hjfk⟩)
      · simpa [slotSetAt, hjfi, hjfk] using Set.univ_nonempty
  rcases listInter_nonempty_of_pairwise_ordConnected ss hne hconn hpair_sets with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  intro f hf hjf
  have hx_all := (mem_listInter.mp hx)
  have hmem_slot : x ∈ slotSetAt j f := by
    exact hx_all (slotSetAt j f) (List.mem_map.mpr ⟨f, hf, rfl⟩)
  simpa [slotSetAt, hjf] using hmem_slot

private lemma pairwise_ge_of_commonInterleaverSeq
    {fs : List ℝ[X]}
    (hseq : HasCommonInterleaverSeq fs)
    (hrr : ∀ f ∈ fs, IsRealRooted f)
    (hfs_ne : fs ≠ []) :
    let d := csDegree fs
    let xs : Fin d → ℝ := fun j => Classical.choose (hseq j.1)
    (List.ofFn xs).Pairwise (· ≥ ·) := by
  classical
  let d := csDegree fs
  let xs : Fin d → ℝ := fun j => Classical.choose (hseq j.1)
  obtain ⟨fmax, hfmax_mem, hfmax_deg⟩ := exists_mem_csDegree_of_ne_nil (fs := fs) hfs_ne
  have hfmax_rr : IsRealRooted fmax := hrr fmax hfmax_mem
  refine List.pairwise_ofFn.2 ?_
  intro i j hij
  have hd_pos : 0 < d := by
    exact Nat.zero_lt_of_lt j.2
  have hroot_ne : rootSeqDesc fmax ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [rootSeqDesc_length hfmax_rr, hfmax_deg]
    exact hd_pos
  have hi_slot : i.1 < (rootSeqDesc fmax).length + 1 := by
    rw [rootSeqDesc_length hfmax_rr, hfmax_deg]
    exact Nat.lt_succ_of_lt i.2
  have hj_slot : j.1 < (rootSeqDesc fmax).length + 1 := by
    rw [rootSeqDesc_length hfmax_rr, hfmax_deg]
    exact Nat.lt_succ_of_lt j.2
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
      (by simpa using hij)
      (by simpa using hj_slot)
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
    IsRealRooted (polyOfDescRoots xs) := by
  unfold polyOfDescRoots
  induction xs with
  | nil =>
      exact ⟨one_ne_zero, by simp⟩
  | cons x xs ih =>
      simpa [List.map_cons, List.prod_cons] using
        isRealRooted_mul (isRealRooted_X_sub_C x) ih

private lemma rootSeqDesc_polyOfDescRoots_eq
    {xs : List ℝ} (hxs : xs.Pairwise (· ≥ ·)) :
    rootSeqDesc (polyOfDescRoots xs) = xs := by
  have hrr : IsRealRooted (polyOfDescRoots xs) := isRealRooted_polyOfDescRoots xs
  have hroots : (↑xs.reverse : Multiset ℝ) = (polyOfDescRoots xs).roots := by
    rw [roots_polyOfDescRoots]
    simp
  have hdesc :=
    rootSeqDesc_eq_reverse_of_pairwise
      (f := polyOfDescRoots xs)
      (rs := xs.reverse)
      (by simpa using hxs.reverse)
      hroots
  simpa using hdesc

private lemma prec_of_slots_polyOfDescRoots
    {f : ℝ[X]} {xs : List ℝ}
    (hf : IsRealRooted f)
    (hxs : xs.Pairwise (· ≥ ·))
    (hdeg_lo : f.natDegree ≤ xs.length)
    (hdeg_hi : xs.length ≤ f.natDegree + 1)
    (hslot : ∀ j (hj : j < xs.length),
      xs.get ⟨j, hj⟩ ∈ rootSlotInterval (rootSeqDesc f)
        ⟨j, by
          have : j < f.natDegree + 1 := lt_of_lt_of_le hj hdeg_hi
          simpa [rootSeqDesc_length hf] using this⟩) :
    Prec f (polyOfDescRoots xs) := by
  let ss : List ℝ := (rootSeqDesc f).reverse
  let rs : List ℝ := xs.reverse
  have hss_pair : ss.Pairwise (· ≤ ·) := by
    simpa [ss] using (rootSeqDesc_pairwise (f := f)).reverse
  have hrs_pair : rs.Pairwise (· ≤ ·) := by
    simpa [rs] using hxs.reverse
  have hss_eq : (↑ss : Multiset ℝ) = f.roots := by
    simpa [ss, rootSeqDesc, Multiset.sort_eq]
  have hrs_eq : (↑rs : Multiset ℝ) = (polyOfDescRoots xs).roots := by
    simpa [rs, roots_polyOfDescRoots]
  have hpoly_rr : IsRealRooted (polyOfDescRoots xs) := isRealRooted_polyOfDescRoots xs
  have hlen_cases : xs.length = f.natDegree ∨ xs.length = f.natDegree + 1 := by
    omega
  refine ⟨hf, hpoly_rr, ss, rs, hss_pair, hrs_pair, hss_eq, hrs_eq, ?_⟩
  rcases hlen_cases with hlen | hlen
  · refine Or.inr ?_
    refine ⟨?_, ?_⟩
    · simpa [ss, rs, hlen, rootSeqDesc_length hf]
    · refine listAlternates_of_index_bounds ?_ ?_ ?_
      · simpa [ss, rs, hlen, rootSeqDesc_length hf]
      · intro k hk
        have hk_deg : k < f.natDegree := by
          simpa [ss, rootSeqDesc_length hf] using hk
        let j : ℕ := f.natDegree - 1 - k
        have hjx : j < xs.length := by
          dsimp [j]
          omega
        have hjf : j < (rootSeqDesc f).length + 1 := by
          have : j < f.natDegree + 1 := by
            dsimp [j]
            omega
          simpa [rootSeqDesc_length hf] using this
        have hmem : xs.get ⟨j, hjx⟩ ∈ rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ := by
          simpa using hslot j hjx
        have hroot_ne : rootSeqDesc f ≠ [] := by
          apply List.ne_nil_of_length_pos
          rw [rootSeqDesc_length hf]
          omega
        have hj_root : j < (rootSeqDesc f).length := by
          rw [rootSeqDesc_length hf]
          dsimp [j]
          omega
        have hlow :
            (rootSeqDesc f).get ⟨j, hj_root⟩ ≤ xs.get ⟨j, hjx⟩ := by
          exact rootSlot_lower_bound (rs := rootSeqDesc f) hroot_ne hj_root hmem
        have hss_get :
            ss.get ⟨k, hk⟩ = (rootSeqDesc f).get ⟨j, hj_root⟩ := by
          have hk_root : k < (rootSeqDesc f).length := by
            simpa [ss, rootSeqDesc_length hf] using hk
          have hget :=
            get_reverse_eq_get_sub (xs := rootSeqDesc f) (k := k) hk_root
          have hidx : (rootSeqDesc f).length - 1 - k = j := by
            rw [rootSeqDesc_length hf]
          calc
            ss.get ⟨k, hk⟩
                = (rootSeqDesc f).get ⟨(rootSeqDesc f).length - 1 - k, by omega⟩ := by
                    simpa [ss] using hget
            _ = (rootSeqDesc f).get ⟨j, hj_root⟩ := by
                  apply congrArg (fun i => (rootSeqDesc f).get i)
                  apply Fin.ext
                  exact hidx
        have hrs_get :
            rs.get ⟨k, by simpa [ss, rs, hlen, rootSeqDesc_length hf] using hk⟩
              = xs.get ⟨j, hjx⟩ := by
          have hk_xs : k < xs.length := by
            omega
          have hget := get_reverse_eq_get_sub (xs := xs) (k := k) hk_xs
          have hidx : xs.length - 1 - k = j := by
            dsimp [j]
            omega
          calc
            rs.get ⟨k, by simpa [ss, rs, hlen, rootSeqDesc_length hf] using hk⟩
                = xs.get ⟨xs.length - 1 - k, by omega⟩ := by
                    simpa [rs] using hget
            _ = xs.get ⟨j, hjx⟩ := by
                  apply congrArg (fun i => xs.get i)
                  apply Fin.ext
                  exact hidx
        rw [hss_get, hrs_get]
        exact hlow
      · intro k hk
        have hk_deg : k + 1 < f.natDegree := by
          simpa [ss, rootSeqDesc_length hf] using hk
        let j : ℕ := f.natDegree - 1 - k
        have hj_pos : 0 < j := by
          dsimp [j]
          omega
        have hjx : j < xs.length := by
          dsimp [j]
          omega
        have hjf : j < (rootSeqDesc f).length + 1 := by
          have : j < f.natDegree + 1 := by
            dsimp [j]
            omega
          simpa [rootSeqDesc_length hf] using this
        have hmem : xs.get ⟨j, hjx⟩ ∈ rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ := by
          simpa using hslot j hjx
        have hroot_ne : rootSeqDesc f ≠ [] := by
          apply List.ne_nil_of_length_pos
          rw [rootSeqDesc_length hf]
          omega
        have hj_le : j ≤ (rootSeqDesc f).length := by
          rw [rootSeqDesc_length hf]
          dsimp [j]
          omega
        have hup :
            xs.get ⟨j, hjx⟩ ≤ (rootSeqDesc f).get ⟨j - 1, by omega⟩ := by
          exact rootSlot_upper_bound (rs := rootSeqDesc f) hroot_ne hj_pos hj_le hmem
        have hrs_get :
            rs.get ⟨k, by
              have : k < f.natDegree := by omega
              simpa [ss, rs, hlen, rootSeqDesc_length hf] using this⟩
              = xs.get ⟨j, hjx⟩ := by
          have hk_xs : k < xs.length := by
            dsimp [j]
            omega
          have hget := get_reverse_eq_get_sub (xs := xs) (k := k) hk_xs
          have hidx : xs.length - 1 - k = j := by
            dsimp [j]
            omega
          calc
            rs.get ⟨k, by
                have : k < f.natDegree := by omega
                simpa [ss, rs, hlen, rootSeqDesc_length hf] using this⟩
                = xs.get ⟨xs.length - 1 - k, by omega⟩ := by
                    simpa [rs] using hget
            _ = xs.get ⟨j, hjx⟩ := by
                  apply congrArg (fun i => xs.get i)
                  apply Fin.ext
                  exact hidx
        have hss_get :
            ss.get ⟨k + 1, hk⟩ = (rootSeqDesc f).get ⟨j - 1, by omega⟩ := by
          have hk1_root : k + 1 < (rootSeqDesc f).length := by
            simpa [ss, rootSeqDesc_length hf] using hk
          have hget :=
            get_reverse_eq_get_sub (xs := rootSeqDesc f) (k := k + 1) hk1_root
          have hidx : (rootSeqDesc f).length - 1 - (k + 1) = j - 1 := by
            rw [rootSeqDesc_length hf]
            dsimp [j]
            omega
          calc
            ss.get ⟨k + 1, hk⟩
                = (rootSeqDesc f).get ⟨(rootSeqDesc f).length - 1 - (k + 1), by omega⟩ := by
                    simpa [ss] using hget
            _ = (rootSeqDesc f).get ⟨j - 1, by omega⟩ := by
                  apply congrArg (fun i => (rootSeqDesc f).get i)
                  apply Fin.ext
                  exact hidx
        rw [hrs_get, hss_get]
        exact hup
  · refine Or.inl ?_
    refine ⟨?_, ?_⟩
    · simpa [ss, rs, hlen, rootSeqDesc_length hf]
    · refine listInterlaces_of_index_bounds ?_ ?_ ?_
      · simpa [ss, rs, hlen, rootSeqDesc_length hf]
      · intro k hk
        have hk_deg : k < f.natDegree := by
          simpa [ss, rootSeqDesc_length hf] using hk
        let j : ℕ := f.natDegree - k
        have hj_pos : 0 < j := by
          dsimp [j]
          omega
        have hjx : j < xs.length := by
          dsimp [j]
          omega
        have hjf : j < (rootSeqDesc f).length + 1 := by
          have : j < f.natDegree + 1 := by
            dsimp [j]
            omega
          simpa [rootSeqDesc_length hf] using this
        have hmem : xs.get ⟨j, hjx⟩ ∈ rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ := by
          simpa using hslot j hjx
        have hroot_ne : rootSeqDesc f ≠ [] := by
          apply List.ne_nil_of_length_pos
          rw [rootSeqDesc_length hf]
          omega
        have hj_le : j ≤ (rootSeqDesc f).length := by
          rw [rootSeqDesc_length hf]
          dsimp [j]
          omega
        have hup :
            xs.get ⟨j, hjx⟩ ≤ (rootSeqDesc f).get ⟨j - 1, by omega⟩ := by
          exact rootSlot_upper_bound (rs := rootSeqDesc f) hroot_ne hj_pos hj_le hmem
        have hrs_get :
            rs.get ⟨k, by
              have : k < f.natDegree + 1 := Nat.lt_succ_of_lt hk_deg
              simpa [ss, rs, hlen, rootSeqDesc_length hf] using this⟩
              = xs.get ⟨j, hjx⟩ := by
          have hk_xs : k < xs.length := by
            dsimp [j]
            omega
          have hget := get_reverse_eq_get_sub (xs := xs) (k := k) hk_xs
          have hidx : xs.length - 1 - k = j := by
            dsimp [j]
            omega
          calc
            rs.get ⟨k, by
                have : k < f.natDegree + 1 := Nat.lt_succ_of_lt hk_deg
                simpa [ss, rs, hlen, rootSeqDesc_length hf] using this⟩
                = xs.get ⟨xs.length - 1 - k, by omega⟩ := by
                    simpa [rs] using hget
            _ = xs.get ⟨j, hjx⟩ := by
                  apply congrArg (fun i => xs.get i)
                  apply Fin.ext
                  exact hidx
        have hss_get :
            ss.get ⟨k, hk⟩ = (rootSeqDesc f).get ⟨j - 1, by omega⟩ := by
          have hk_root : k < (rootSeqDesc f).length := by
            simpa [ss, rootSeqDesc_length hf] using hk
          have hget :=
            get_reverse_eq_get_sub (xs := rootSeqDesc f) (k := k) hk_root
          have hidx : (rootSeqDesc f).length - 1 - k = j - 1 := by
            rw [rootSeqDesc_length hf]
            dsimp [j]
            omega
          calc
            ss.get ⟨k, hk⟩
                = (rootSeqDesc f).get ⟨(rootSeqDesc f).length - 1 - k, by omega⟩ := by
                    simpa [ss] using hget
            _ = (rootSeqDesc f).get ⟨j - 1, by omega⟩ := by
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
          dsimp [j]
          omega
        have hjf : j < (rootSeqDesc f).length + 1 := by
          have : j < f.natDegree + 1 := by
            dsimp [j]
            omega
          simpa [rootSeqDesc_length hf] using this
        have hmem : xs.get ⟨j, hjx⟩ ∈ rootSlotInterval (rootSeqDesc f) ⟨j, hjf⟩ := by
          simpa using hslot j hjx
        have hroot_ne : rootSeqDesc f ≠ [] := by
          apply List.ne_nil_of_length_pos
          rw [rootSeqDesc_length hf]
          omega
        have hj_root : j < (rootSeqDesc f).length := by
          rw [rootSeqDesc_length hf]
          dsimp [j]
          omega
        have hlow :
            (rootSeqDesc f).get ⟨j, hj_root⟩ ≤ xs.get ⟨j, hjx⟩ := by
          exact rootSlot_lower_bound (rs := rootSeqDesc f) hroot_ne hj_root hmem
        have hss_get :
            ss.get ⟨k, hk⟩ = (rootSeqDesc f).get ⟨j, hj_root⟩ := by
          have hk_root : k < (rootSeqDesc f).length := by
            simpa [ss, rootSeqDesc_length hf] using hk
          have hget :=
            get_reverse_eq_get_sub (xs := rootSeqDesc f) (k := k) hk_root
          have hidx : (rootSeqDesc f).length - 1 - k = j := by
            rw [rootSeqDesc_length hf]
          calc
            ss.get ⟨k, hk⟩
                = (rootSeqDesc f).get ⟨(rootSeqDesc f).length - 1 - k, by omega⟩ := by
                    simpa [ss] using hget
            _ = (rootSeqDesc f).get ⟨j, hj_root⟩ := by
                  apply congrArg (fun i => (rootSeqDesc f).get i)
                  apply Fin.ext
                  exact hidx
        have hrs_get :
            rs.get ⟨k + 1, by
              have : k + 1 < f.natDegree + 1 := Nat.succ_lt_succ hk_deg
              simpa [ss, rs, hlen, rootSeqDesc_length hf] using this⟩
              = xs.get ⟨j, hjx⟩ := by
          have hk1_xs : k + 1 < xs.length := by
            dsimp [j]
            omega
          have hget := get_reverse_eq_get_sub (xs := xs) (k := k + 1) hk1_xs
          have hidx : xs.length - 1 - (k + 1) = j := by
            dsimp [j]
            omega
          calc
            rs.get ⟨k + 1, by
                have : k + 1 < f.natDegree + 1 := Nat.succ_lt_succ hk_deg
                simpa [ss, rs, hlen, rootSeqDesc_length hf] using this⟩
                = xs.get ⟨xs.length - 1 - (k + 1), by omega⟩ := by
                    simpa [rs] using hget
            _ = xs.get ⟨j, hjx⟩ := by
                  apply congrArg (fun i => xs.get i)
                  apply Fin.ext
                  exact hidx
        rw [hss_get, hrs_get]
        exact hlow

/-- Chudnovsky--Seymour `2 ⇒ 3` in the polynomial language used elsewhere in
this file: pairwise common interleavers can be upgraded to a single common
right interleaver. The intended route is through
`hasCommonInterleaverSeq_of_pairwiseHasCommonInterleaver`. -/
private theorem hasCommonInterleaver_of_pairwiseHasCommonInterleaver_ge_two
    {f g : ℝ[X]} {fs : List ℝ[X]}
    (hrr : ∀ p ∈ f :: g :: fs, IsRealRooted p)
    (hpos : ∀ p ∈ f :: g :: fs, HasPosLeadingCoeff p)
    (hpair : PairwiseHasCommonInterleaver (f :: g :: fs)) :
    HasCommonInterleaver (f :: g :: fs) := by
  /-
  This is the genuine Chudnovsky--Seymour core. The base cases `[]` and `[f]`
  are handled separately below, so the remaining argument may freely assume the
  family has length at least `2`.
  -/
  let ps : List ℝ[X] := f :: g :: fs
  have hrr_ps : ∀ p ∈ ps, IsRealRooted p := by
    intro p hp
    exact hrr p (by simpa [ps] using hp)
  have hpos_ps : ∀ p ∈ ps, HasPosLeadingCoeff p := by
    intro p hp
    exact hpos p (by simpa [ps] using hp)
  have hpair_ps : PairwiseHasCommonInterleaver ps := by
    simpa [ps] using hpair
  have hseq :
      HasCommonInterleaverSeq ps :=
    hasCommonInterleaverSeq_of_pairwiseHasCommonInterleaver
      (fs := ps) hrr_ps hpos_ps hpair_ps
  have hps_ne : ps ≠ [] := by
    simp [ps]
  let d : ℕ := csDegree ps
  let xs : Fin d → ℝ := fun j => Classical.choose (hseq j.1)
  let xlist : List ℝ := List.ofFn xs
  have hx_pair : xlist.Pairwise (· ≥ ·) := by
    simpa [d, xs, xlist] using
      (pairwise_ge_of_commonInterleaverSeq (fs := ps) hseq hrr_ps hps_ne)
  let h : ℝ[X] := polyOfDescRoots xlist
  refine ⟨h, ?_⟩
  intro p hp
  have hp_mem : p ∈ ps := by simpa [ps] using hp
  have hp_rr : IsRealRooted p := hrr_ps p hp_mem
  have hp_deg_lo : p.natDegree ≤ xlist.length := by
    have : p.natDegree ≤ csDegree ps := natDegree_le_csDegree (fs := ps) hp_mem
    simpa [xlist, d]
      using this
  have hp_deg_hi : xlist.length ≤ p.natDegree + 1 := by
    have : csDegree ps ≤ p.natDegree + 1 :=
      csDegree_le_natDegree_succ_of_pairwiseHasCommonInterleaver
        (fs := ps) (f := p) hps_ne hp_mem hpair_ps
    simpa [xlist, d]
      using this
  have hslot :
      ∀ j (hj : j < xlist.length),
        xlist.get ⟨j, hj⟩ ∈ rootSlotInterval (rootSeqDesc p)
          ⟨j, by
            have : j < p.natDegree + 1 := lt_of_lt_of_le hj hp_deg_hi
            simpa [rootSeqDesc_length hp_rr] using this⟩ := by
    intro j hj
    have hjp : j < p.natDegree + 1 := lt_of_lt_of_le hj hp_deg_hi
    have hjf : j < (rootSeqDesc p).length + 1 := by
      simpa [rootSeqDesc_length hp_rr] using hjp
    have hslot_raw :
        Classical.choose (hseq j) ∈ rootSlotInterval (rootSeqDesc p)
          ⟨j, hjf⟩ := by
      exact (Classical.choose_spec (hseq j)) p hp_mem hjf
    simpa [xlist, xs, d] using hslot_raw
  have hp_prec :
      Prec p (polyOfDescRoots xlist) :=
    prec_of_slots_polyOfDescRoots
      (f := p) (xs := xlist) hp_rr hx_pair hp_deg_lo hp_deg_hi hslot
  simpa [h] using hp_prec

theorem hasCommonInterleaver_of_pairwiseHasCommonInterleaver
    {fs : List ℝ[X]}
    (hrr : ∀ f ∈ fs, IsRealRooted f)
    (hpos : ∀ f ∈ fs, HasPosLeadingCoeff f)
    (hpair : PairwiseHasCommonInterleaver fs) :
    HasCommonInterleaver fs := by
  cases fs with
  | nil =>
      refine ⟨1, ?_⟩
      intro f hf
      simp at hf
  | cons f fs =>
      cases fs with
      | nil =>
          refine ⟨f, ?_⟩
          intro p hp
          rcases List.mem_singleton.mp hp with rfl
          simpa using prec_refl (hrr p (by simp))
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
    (hne : fs ≠ []) :
    IsRealRooted fs.sum := by
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
    (hne : fs ≠ []) :
    IsRealRooted fs.sum := by
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
    (hx : x ∈ rootSlotInterval rs ⟨j, by omega⟩) :
    rs.get ⟨j, hj⟩ ≤ x := by
  exact rootSlot_lower_bound hrs hj hx

/-- Public upper-bound wrapper for a point lying in a root slot. -/
theorem rootSlot_upper_bound_of_mem
    {rs : List ℝ} (hrs : rs ≠ []) {j : ℕ} (hj0 : 0 < j) (hj : j ≤ rs.length)
    {x : ℝ}
    (hx : x ∈ rootSlotInterval rs ⟨j, by omega⟩) :
    x ≤ rs.get ⟨j - 1, by omega⟩ := by
  exact rootSlot_upper_bound hrs hj0 hj hx

/-- Points in later root slots are weakly below points in earlier root slots.
This public wrapper exposes the monotonicity fact used in the slot-based
common-interleaver construction. -/
theorem le_of_mem_rootSlotInterval_of_lt
    {rs : List ℝ} (hrs_ne : rs ≠ []) (hrs : rs.Pairwise (· ≥ ·))
    {i j : ℕ} (hij : i < j) (hj : j < rs.length + 1)
    {x y : ℝ}
    (hx : x ∈ rootSlotInterval rs ⟨i, by omega⟩)
    (hy : y ∈ rootSlotInterval rs ⟨j, hj⟩) :
    y ≤ x := by
  exact le_of_mem_rootSlots_of_lt hrs_ne hrs hij hj hx hy

/-- In a `Prec` witness, the `j`th descending root of the right polynomial lies
in the `j`th admissible slot of the left polynomial. -/
theorem mem_rootSlotInterval_of_prec_desc
    {f g : ℝ[X]} (hfg : Prec f g) (j : Fin g.natDegree) :
    (rootSeqDesc g).get ⟨j.1, by
      rcases hfg with ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩
      simpa [rootSeqDesc, hg.2, hrs_eq] using j.2⟩ ∈ rootSlotInterval (rootSeqDesc f)
      ⟨j.1, by
        rcases hfg with ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩
        have hdeg := (natDegree_bounds_of_prec
          ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩).2
        simpa [rootSeqDesc_length hf, rootSeqDesc_length hg] using
          lt_of_lt_of_le j.2 hdeg⟩ := by
  exact mem_rootSlotInterval_of_prec hfg j

/-- Slot data against `rootSeqDesc f` reconstructs a `Prec` witness with the
descending-root polynomial built from those slot choices. -/
theorem prec_of_slots_polyOfDescRootsDesc
    {f : ℝ[X]} {xs : List ℝ}
    (hf : IsRealRooted f)
    (hxs : xs.Pairwise (· ≥ ·))
    (hdeg_lo : f.natDegree ≤ xs.length)
    (hdeg_hi : xs.length ≤ f.natDegree + 1)
    (hslot : ∀ j (hj : j < xs.length),
      xs.get ⟨j, hj⟩ ∈ rootSlotInterval (rootSeqDesc f)
        ⟨j, by
          have : j < f.natDegree + 1 := lt_of_lt_of_le hj hdeg_hi
          simpa [rootSeqDesc_length hf] using this⟩) :
    Prec f (polyOfDescRootsDesc xs) := by
  simpa [polyOfDescRootsDesc] using
    prec_of_slots_polyOfDescRoots
      (f := f) (xs := xs) hf hxs hdeg_lo hdeg_hi hslot

/-- Matching nonempty root-slot intersections for two same-degree real-rooted
polynomials produce a common right interleaver.  This isolates the constructive
part of the same-degree Chudnovsky--Seymour gap from the remaining
mathematical slot-intersection theorem. -/
theorem pairHasCommonInterleaver_of_sameDegree_slotIntersections
    {f g : ℝ[X]}
    (hf : IsRealRooted f)
    (hg : IsRealRooted g)
    (hdeg : g.natDegree = f.natDegree)
    (hslot :
      ∀ j (hj : j < f.natDegree + 1),
        (rootSlotInterval (rootSeqDesc f)
            ⟨j, by simpa [rootSeqDesc_length hf] using hj⟩ ∩
          rootSlotInterval (rootSeqDesc g)
            ⟨j, by
              have : j < g.natDegree + 1 := by omega
              simpa [rootSeqDesc_length hg] using this⟩).Nonempty) :
    ∃ h : ℝ[X], Prec f h ∧ Prec g h := by
  classical
  let n : ℕ := f.natDegree + 1
  let x : Fin n → ℝ := fun j => Classical.choose (hslot j.1 (by simpa [n] using j.2))
  let xs : List ℝ := List.ofFn x
  have hxs_len : xs.length = f.natDegree + 1 := by
    simp [xs, n]
  have hxs_pair : xs.Pairwise (· ≥ ·) := by
    refine List.pairwise_ofFn.2 ?_
    intro i j hij
    have hroot_ne : rootSeqDesc f ≠ [] := by
      apply List.ne_nil_of_length_pos
      rw [rootSeqDesc_length hf]
      omega
    have hi_slot : i.1 < (rootSeqDesc f).length + 1 := by
      have : i.1 < f.natDegree + 1 := by simpa [n] using i.2
      simpa [rootSeqDesc_length hf] using this
    have hj_slot : j.1 < (rootSeqDesc f).length + 1 := by
      have : j.1 < f.natDegree + 1 := by simpa [n] using j.2
      simpa [rootSeqDesc_length hf] using this
    have hxi :
        x i ∈ rootSlotInterval (rootSeqDesc f) ⟨i.1, hi_slot⟩ := by
      have hraw := (Classical.choose_spec (hslot i.1 (by simpa [n] using i.2))).1
      simpa [x] using hraw
    have hxj :
        x j ∈ rootSlotInterval (rootSeqDesc f) ⟨j.1, hj_slot⟩ := by
      have hraw := (Classical.choose_spec (hslot j.1 (by simpa [n] using j.2))).1
      simpa [x] using hraw
    exact
      le_of_mem_rootSlotInterval_of_lt
        (rs := rootSeqDesc f)
        hroot_ne
        rootSeqDesc_pairwise
        (i := i.1) (j := j.1)
        (by simpa using hij)
        (by simpa using hj_slot)
        hxi hxj
  let h : ℝ[X] := polyOfDescRootsDesc xs
  refine ⟨h, ?_, ?_⟩
  · have hdeg_lo : f.natDegree ≤ xs.length := by
      rw [hxs_len]
      omega
    have hdeg_hi : xs.length ≤ f.natDegree + 1 := by
      rw [hxs_len]
    have hslot_f :
        ∀ j (hj : j < xs.length),
          xs.get ⟨j, hj⟩ ∈ rootSlotInterval (rootSeqDesc f)
            ⟨j, by
              have : j < f.natDegree + 1 := lt_of_lt_of_le hj hdeg_hi
              simpa [rootSeqDesc_length hf] using this⟩ := by
      intro j hj
      have hjn : j < n := by
        simpa [n, hxs_len] using hj
      have hraw := (Classical.choose_spec (hslot j (by simpa [n] using hjn))).1
      convert hraw using 1
      · change (List.ofFn x)[j] = x ⟨j, hjn⟩
        convert (List.getElem_ofFn (f := x) (i := j) (by simpa [xs] using hj)) using 2
    simpa [h] using
      prec_of_slots_polyOfDescRootsDesc
        (f := f) (xs := xs) hf hxs_pair hdeg_lo hdeg_hi hslot_f
  · have hdeg_lo : g.natDegree ≤ xs.length := by
      rw [hxs_len, hdeg]
      omega
    have hdeg_hi : xs.length ≤ g.natDegree + 1 := by
      rw [hxs_len, hdeg]
    have hslot_g :
        ∀ j (hj : j < xs.length),
          xs.get ⟨j, hj⟩ ∈ rootSlotInterval (rootSeqDesc g)
            ⟨j, by
              have : j < g.natDegree + 1 := lt_of_lt_of_le hj hdeg_hi
              simpa [rootSeqDesc_length hg] using this⟩ := by
      intro j hj
      have hjn : j < n := by
        simpa [n, hxs_len] using hj
      have hraw := (Classical.choose_spec (hslot j (by simpa [n] using hjn))).2
      convert hraw using 1
      · change (List.ofFn x)[j] = x ⟨j, hjn⟩
        convert (List.getElem_ofFn (f := x) (i := j) (by simpa [xs] using hj)) using 2
    simpa [h] using
      prec_of_slots_polyOfDescRootsDesc
        (f := g) (xs := xs) hg hxs_pair hdeg_lo hdeg_hi hslot_g

/-- Reversing a weak zero-aware interlacing sequence with nonnegative
coefficients preserves the same structure. -/
lemma IsInterlacingSeq0Nonneg.reverse {fs : List ℝ[X]}
    (hfs : IsInterlacingSeq0Nonneg fs) :
    fs.reverse.Pairwise (fun f g => Prec0 g f) ∧
    ∀ f ∈ fs.reverse, HasNonnegCoeffs f := by
  rcases hfs with ⟨hint, hnonneg⟩
  refine ⟨hint.reverse, ?_⟩
  intro p hp
  exact hnonneg p (by simpa using List.mem_reverse.2 hp)


end
end RealRooted
