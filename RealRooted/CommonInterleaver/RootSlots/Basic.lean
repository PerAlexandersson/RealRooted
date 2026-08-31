import RealRooted.CommonInterleaver.RootDesc

/-!
# Common interleavers: root-slot basics

The root-slot intervals attached to descending root sequences, their endpoints,
and the order facts for points chosen from those intervals.
-/

open Polynomial

noncomputable section

namespace RealRooted

section

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

protected lemma CommonInterleaver.RootSlots.rootSlotInterval_eq_univ_of_length_eq_zero
    {rs : List ℝ} (hrs : rs.length = 0) (j : Fin (rs.length + 1)) :
    rootSlotInterval rs j = Set.univ := by
  have hrs_nil : rs = [] := List.length_eq_zero_iff.mp hrs
  subst rs
  rcases j with ⟨j, hj⟩
  simp at hj
  have hj0 : j = 0 := by lia
  subst j
  simp [rootSlotInterval]

protected lemma CommonInterleaver.RootSlots.rootSlotInterval_inter_nonempty_of_lengths_eq_zero
    {rs ss : List ℝ} (hrs : rs.length = 0) (hss : ss.length = 0)
    (jr : Fin (rs.length + 1)) (js : Fin (ss.length + 1)) :
    (rootSlotInterval rs jr ∩ rootSlotInterval ss js).Nonempty := by
  refine ⟨0, ?_, ?_⟩
  · rw [CommonInterleaver.RootSlots.rootSlotInterval_eq_univ_of_length_eq_zero hrs jr]
    simp
  · rw [CommonInterleaver.RootSlots.rootSlotInterval_eq_univ_of_length_eq_zero hss js]
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

protected lemma
    CommonInterleaver.RootSlots.reverse_get_zero_eq_getLast {xs : List ℝ} (hxs : xs ≠ []) :
    xs.reverse.get ⟨0, by grind⟩ =
      xs.getLast hxs := by
  grind

protected lemma
    CommonInterleaver.RootSlots.reverse_get_last_eq_get_zero {xs : List ℝ} (hxs : xs ≠ []) :
    xs.reverse.get ⟨xs.length - 1, by
      simpa [List.length_reverse] using
        (Nat.sub_lt (List.length_pos_iff_ne_nil.mpr hxs) (by lia : 0 < 1))⟩ =
      xs.get ⟨0, List.length_pos_iff_ne_nil.mpr hxs⟩ := by
  simp

protected lemma
    CommonInterleaver.RootSlots.get_reverse_eq_get_sub {xs : List ℝ} {k : ℕ}
    (hk : k < xs.length) :
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

protected lemma
    CommonInterleaver.RootSlots.rootSlotInterval_reverse_zero {xs : List ℝ} (hxs : xs ≠ []) :
    rootSlotInterval xs.reverse
      ⟨0, by lia⟩ =
      Set.Ici (xs.getLast hxs) := by
  rw [rootSlotInterval_zero_of_ne_nil (List.reverse_ne_nil_iff.mpr hxs)]
  grind

protected lemma
    CommonInterleaver.RootSlots.rootSlotInterval_reverse_last {xs : List ℝ} (hxs : xs ≠ []) :
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
  have h := CommonInterleaver.RootSlots.rootSlotInterval_reverse_last (xs := rs.reverse)
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
        ⟨rs.length, by simp⟩ := hcongr.symm
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

protected lemma
    CommonInterleaver.RootSlots.rootSlotInterval_last_eq_reverse_get_zero
    {rs : List ℝ} (hrs : rs ≠ []) :
    rootSlotInterval rs
      ⟨rs.length, by lia⟩ =
      Set.Iic (rs.reverse.get ⟨0, by grind⟩) := by
  rw [rootSlotInterval_last_of_ne_nil hrs]
  rw [CommonInterleaver.RootSlots.reverse_get_zero_eq_getLast hrs, getLast_eq_get_lastIndex hrs]

protected lemma CommonInterleaver.RootSlots.rootSlot_lower_bound
    {rs : List ℝ} (hrs : rs ≠ []) {j : ℕ} (hj : j < rs.length) {x : ℝ}
    (hx : x ∈ rootSlotInterval rs ⟨j, by lia⟩) :
    rs.get ⟨j, hj⟩ ≤ x := by
  by_cases hj0 : j = 0
  · subst hj0
    simpa using mem_rootSlotInterval_zero_lower (rs := rs) hrs hx
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    exact (mem_rootSlotInterval_interior_bounds (rs := rs) hjpos hj hx).1

protected lemma CommonInterleaver.RootSlots.rootSlot_upper_bound
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
        _ = rs.get ⟨j - 1, by lia⟩ := by simp_all
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
    CommonInterleaver.RootSlots.rootSlot_lower_bound (rs := rs) hrs hj_lt hx
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
        _ = rs.get ⟨j, hj_lt⟩ := by simp_all
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

protected lemma CommonInterleaver.RootSlots.le_of_mem_rootSlots_of_lt
    {rs : List ℝ} (hrs_ne : rs ≠ []) (hrs : rs.Pairwise (· ≥ ·))
    {i j : ℕ} (hij : i < j) (hj : j < rs.length + 1)
    {x y : ℝ}
    (hx : x ∈ rootSlotInterval rs ⟨i, by lia⟩)
    (hy : y ∈ rootSlotInterval rs ⟨j, hj⟩) :
    y ≤ x := by
  have hi_lt : i < rs.length := by lia
  have hx_lower : rs.get ⟨i, hi_lt⟩ ≤ x :=
    CommonInterleaver.RootSlots.rootSlot_lower_bound (rs := rs) hrs_ne hi_lt hx
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


end
end RealRooted
