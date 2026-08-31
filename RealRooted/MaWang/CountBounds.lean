import RealRooted.Basic
import RealRooted.Linear
import RealRooted.Derivative
import RealRooted.Wagner
import RealRooted.RootContinuity
import Mathlib.Analysis.Normed.Field.Approximation
import Mathlib.Analysis.Complex.Polynomial.Basic
-- import RealRooted.AffineDerivative  -- uncomment when AffineDerivative is built

open Polynomial Filter

noncomputable section

namespace RealRooted.MaWangInternal

theorem exists_signInterleaving {F : ℝ[X]} :
    ∀ (rs : List ℝ),
      rs.Pairwise (· ≤ ·) →
      (∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        F.eval r₁ * F.eval r₂ ≤ 0) →
      ∃ us : List ℝ, us.length = rs.length - 1 ∧
        ListInterlaces us rs ∧
        (∀ u ∈ us, F.IsRoot u)
  | [], _, _ => by
      refine ⟨[], by simp, ?_, ?_⟩
      · simp [ListInterlaces]
      · simp
  | [_], _, _ => by
      refine ⟨[], by simp, ?_, ?_⟩
      · simp [ListInterlaces]
      · simp
  | r₁ :: r₂ :: rest, hrs_sorted, hsign => by
      have hr₁r₂ : r₁ ≤ r₂ := List.rel_of_pairwise_cons hrs_sorted (by simp)
      have hprod : F.eval r₁ * F.eval r₂ ≤ 0 := by simpa using hsign [] rfl
      obtain ⟨u, hu₁, hu₂, hu_root⟩ :=
        exists_isRoot_between_of_eval_mul_nonpos hr₁r₂ hprod
      have htail_sorted : (r₂ :: rest).Pairwise (· ≤ ·) :=
        (List.pairwise_cons.mp hrs_sorted).2
      obtain ⟨us, hus_len, hus_int, hus_roots⟩ :=
        exists_signInterleaving (F := F) (r₂ :: rest) htail_sorted
          (fun pre {a b tail} hEq => by
            grind)
      refine ⟨u :: us, ?_, ?_, ?_⟩
      · simp [hus_len]
      · exact ⟨hu₁, hu₂, hus_int⟩
      · simp_all

/-- Public wrapper around `exists_signInterleaving`. This is the interval part of
Liu--Wang / Ma--Wang arguments: once we know the endpoint-sign condition on a
sorted root list, we can package the resulting real roots as an interleaving list. -/
theorem exists_roots_interlacing_of_consecutive_signs {F : ℝ[X]} {rs : List ℝ}
    (hrs_sorted : rs.Pairwise (· ≤ ·))
    (hsign :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        F.eval r₁ * F.eval r₂ ≤ 0) :
    ∃ us : List ℝ, us.length = rs.length - 1 ∧
      ListInterlaces us rs ∧
      (∀ u ∈ us, F.IsRoot u) :=
  exists_signInterleaving (F := F) rs hrs_sorted hsign

/-- Greedy ordered-matching lemma for the differ-by-1 case. The hypotheses say:
after consuming the first `pre.length` left-hand points, the remaining right-hand
points all lie to the right of the current left-hand point, and one of the
remaining points after the next consumed root already lies before the next
left-hand point. This is exactly the data needed to assemble an actual sorted
right-hand root list into a weak `ListInterlaces` layout. -/
theorem listInterlaces_of_drop_bounds :
    ∀ {ss ts : List ℝ},
      ss.Pairwise (· ≤ ·) →
      ts.Pairwise (· ≤ ·) →
      ss.length + 1 = ts.length →
      (∀ {s : ℝ} {rest : List ℝ},
        ss = s :: rest →
        ts.head! ≤ s) →
      (∀ (pre : List ℝ) {s : ℝ} {rest : List ℝ},
        ss = pre ++ s :: rest →
        ∀ u ∈ ts.drop (pre.length + 1), s ≤ u) →
      (∀ (pre : List ℝ) {s₁ s₂ : ℝ} {rest : List ℝ},
        ss = pre ++ s₁ :: s₂ :: rest →
        ∃ u, u ∈ ts.drop (pre.length + 1) ∧ u ≤ s₂) →
      ListInterlaces ss ts
  | [], ts, _, _, hlen, _, _, _ => by
      have hts_len : ts.length = 1 := by simp_all
      cases ts with
      | nil => lia
      | cons t ts' =>
          cases ts' with
          | nil => simp [ListInterlaces]
          | cons u us => simp at hts_len
  | s :: ss, ts, hss, hts, hlen, hleft, hge, hexists => by
      cases ts with
      | nil => simp at hlen
      | cons t ts' =>
          cases ts' with
          | nil => simp at hlen
          | cons u us =>
              have htu_sorted : (u :: us).Pairwise (· ≤ ·) :=
                (List.pairwise_cons.mp hts).2
              have ht_le_s : t ≤ s := by simp_all
              have hs_le_u : s ≤ u :=
                hge [] rfl u (by simp)
              cases ss with
              | nil =>
                  have hus_nil : us = [] := by simp_all
                  subst hus_nil
                  simp [ListInterlaces, ht_le_s, hs_le_u]
              | cons s₂ ss' =>
                  have hu_le_s₂ : u ≤ s₂ := by
                    obtain ⟨w, hw_drop, hw_le⟩ := hexists [] rfl
                    grind
                  have hleft' :
                      ∀ {s' : ℝ} {rest : List ℝ},
                        s₂ :: ss' = s' :: rest →
                        (u :: us).head! ≤ s' := by
                    simp_all
                  have hge' :
                      ∀ (pre : List ℝ) {s' : ℝ} {rest : List ℝ},
                        s₂ :: ss' = pre ++ s' :: rest →
                        ∀ v ∈ (u :: us).drop (pre.length + 1), s' ≤ v := by
                    intro pre s' rest hEq v hv
                    have hEq' : s :: s₂ :: ss' = (s :: pre) ++ s' :: rest := by
                      simp [List.cons_append, hEq]
                    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                      hge (s :: pre) hEq' v hv
                  have hexists' :
                      ∀ (pre : List ℝ) {s₁ s₂' : ℝ} {rest : List ℝ},
                        s₂ :: ss' = pre ++ s₁ :: s₂' :: rest →
                        ∃ v, v ∈ (u :: us).drop (pre.length + 1) ∧ v ≤ s₂' := by
                    grind
                  have hlen' : (s₂ :: ss').length + 1 = (u :: us).length := by simp_all
                  have hint_tail : ListInterlaces (s₂ :: ss') (u :: us) :=
                    listInterlaces_of_drop_bounds
                      (ss := s₂ :: ss') (ts := u :: us)
                      (List.pairwise_cons.mp hss).2 htu_sorted hlen' hleft' hge' hexists'
                  exact ⟨ht_le_s, hs_le_u, hint_tail⟩

/-- Greedy ordered-matching lemma for the same-degree case. The `drop` hypotheses
say that after consuming the first `pre.length` right-hand points, all remaining
points lie to the right of the current left-hand point, and one of them already
lies before the next left-hand point. This packages an actual sorted root list
into a weak `ListAlternates` layout. -/
theorem listAlternates_of_drop_bounds :
    ∀ {ss ts : List ℝ},
      ss.Pairwise (· ≤ ·) →
      ts.Pairwise (· ≤ ·) →
      ss.length = ts.length →
      (∀ (pre : List ℝ) {s : ℝ} {rest : List ℝ},
        ss = pre ++ s :: rest →
        ∀ u ∈ ts.drop pre.length, s ≤ u) →
      (∀ (pre : List ℝ) {s₁ s₂ : ℝ} {rest : List ℝ},
        ss = pre ++ s₁ :: s₂ :: rest →
        ∃ u, u ∈ ts.drop pre.length ∧ u ≤ s₂) →
      ListAlternates ss ts
  | [], [], _, _, _, _, _ => by simp [ListAlternates]
  | [], _ :: _, _, _, hlen, _, _ => by simp at hlen
  | _ :: _, [], _, _, hlen, _, _ => by simp at hlen
  | s :: ss, t :: ts, hss, hts, hlen, hge, hexists => by
      have hs_le_t : s ≤ t :=
        hge [] rfl t (by simp)
      cases ss with
      | nil =>
          cases ts with
          | nil =>
              simp [ListAlternates, hs_le_t, ListInterlaces]
          | cons u us =>
              simp at hlen
      | cons s₂ ss' =>
          have ht_le_s₂ : t ≤ s₂ := by
            obtain ⟨u, hu_mem, hu_le⟩ := hexists [] rfl
            have ht_le_u : t ≤ u := by simpa using hts.head!_le hu_mem
            grind
          have hge' :
              ∀ (pre : List ℝ) {s' : ℝ} {rest : List ℝ},
                s₂ :: ss' = pre ++ s' :: rest →
                ∀ u ∈ (t :: ts).drop (pre.length + 1), s' ≤ u := by
            grind
          have hexists' :
              ∀ (pre : List ℝ) {s₁ s₂' : ℝ} {rest : List ℝ},
                s₂ :: ss' = pre ++ s₁ :: s₂' :: rest →
                ∃ u, u ∈ (t :: ts).drop (pre.length + 1) ∧ u ≤ s₂' := by
            intro pre s₁ s₂' rest hEq
            have hEq' : s :: s₂ :: ss' = (s :: pre) ++ s₁ :: s₂' :: rest := by
              simp [List.cons_append, hEq]
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
              hexists (s :: pre) hEq'
          have hlen' : (s₂ :: ss').length + 1 = (t :: ts).length := by simp_all
          have hint_tail : ListInterlaces (s₂ :: ss') (t :: ts) :=
            listInterlaces_of_drop_bounds
              (ss := s₂ :: ss') (ts := t :: ts)
              (List.pairwise_cons.mp hss).2 hts hlen'
              (by
                simp_all)
              hge' hexists'
          exact ⟨hs_le_t, hint_tail⟩

/-- If a sorted list has at most `k` entries strictly below `s`, then every entry
in the `drop k` tail is `≥ s`. This is the count-to-tail bridge needed to feed
actual sorted root lists into the `drop`-based layout lemmas above. -/
lemma all_ge_of_countP_lt_drop
    {ts : List ℝ} (hts : ts.Pairwise (· ≤ ·)) {s : ℝ} {k : ℕ}
    (hcount : ts.countP (· < s) ≤ k) :
    ∀ u ∈ ts.drop k, s ≤ u := by
  intro u hu
  by_contra hus
  have hu_lt : u < s := lt_of_not_ge hus
  have htake_lt : ∀ x ∈ ts.take k, x < s := by
    intro x hx
    have hx_le_u : x ≤ u := hts.rel_of_mem_take_of_mem_drop hx hu
    grind
  have hk : k ≤ ts.length := by
    by_contra hk
    have hk' : ts.length < k := lt_of_not_ge hk
    have hnil : ts.drop k = [] := List.drop_eq_nil_of_le hk'.le
    simp [hnil] at hu
  have htake_count : (ts.take k).countP (· < s) = k := by
    rw [List.countP_eq_length_filter]
    have hfilter :
        List.filter (fun x => decide (x < s)) (ts.take k) = ts.take k := by
      simp_all
    grind
  have hdrop_pos : 0 < (ts.drop k).countP (· < s) := by grind
  have hsplit :
      ts.countP (· < s) =
        (ts.take k).countP (· < s) + (ts.drop k).countP (· < s) := by
    simpa [List.take_append_drop] using
      (List.countP_append (p := fun x => decide (x < s)) (l₁ := ts.take k) (l₂ := ts.drop k))
  lia

/-- If a list has more than `k` entries `≤ s`, then some entry of the `drop k`
tail is still `≤ s`. -/
lemma exists_mem_drop_le_of_lt_countP
    {ts : List ℝ} {s : ℝ} {k : ℕ}
    (hcount : k < ts.countP (· ≤ s)) :
    ∃ u, u ∈ ts.drop k ∧ u ≤ s := by
  by_contra hnot
  have hdrop_zero : (ts.drop k).countP (· ≤ s) = 0 := by simp_all
  have hsplit :
      ts.countP (· ≤ s) =
        (ts.take k).countP (· ≤ s) + (ts.drop k).countP (· ≤ s) := by
    simpa [List.take_append_drop] using
      (List.countP_append (p := fun x => decide (x ≤ s)) (l₁ := ts.take k) (l₂ := ts.drop k))
  rw [hsplit, hdrop_zero] at hcount
  have htake_le : (ts.take k).countP (· ≤ s) ≤ k :=
    (List.countP_le_length (p := fun x => decide (x ≤ s)) (l := ts.take k)).trans
      (by simp [List.length_take])
  lia

/-- Count-based ordered matching for the differ-by-1 case. If the sorted
right-hand list has:
- at least one element `≤` the first left-hand point,
- at most `pre.length + 1` elements strictly left of each later left-hand point,
- more than `pre.length + 1` elements `≤` the next left-hand point,

then the two lists satisfy the weak `ListInterlaces` layout. -/
theorem listInterlaces_of_count_bounds
    {ss ts : List ℝ}
    (hss : ss.Pairwise (· ≤ ·))
    (hts : ts.Pairwise (· ≤ ·))
    (hlen : ss.length + 1 = ts.length)
    (hhead :
      ∀ {s : ℝ} {rest : List ℝ},
        ss = s :: rest →
        0 < ts.countP (· ≤ s))
    (hlt :
      ∀ (pre : List ℝ) {s : ℝ} {rest : List ℝ},
        ss = pre ++ s :: rest →
        ts.countP (· < s) ≤ pre.length + 1)
    (hle :
      ∀ (pre : List ℝ) {s₁ s₂ : ℝ} {rest : List ℝ},
        ss = pre ++ s₁ :: s₂ :: rest →
        pre.length + 1 < ts.countP (· ≤ s₂)) :
    ListInterlaces ss ts := by
  apply listInterlaces_of_drop_bounds hss hts hlen
  · intro s rest hEq
    obtain ⟨u, hu_drop, hu_le⟩ :=
      exists_mem_drop_le_of_lt_countP (ts := ts) (s := s) (k := 0) (by simp_all)
    have hu_mem : u ∈ ts := by simp_all
    have hhead_le_u : ts.head! ≤ u := by simpa using hts.head!_le hu_mem
    grind
  · intro pre s rest hEq u hu
    exact all_ge_of_countP_lt_drop hts (hlt pre hEq) u hu
  · intro pre s₁ s₂ rest hEq
    exact exists_mem_drop_le_of_lt_countP
      (ts := ts) (s := s₂) (k := pre.length + 1) (hle pre hEq)

/-- Count-based ordered matching for the same-degree case. If the sorted
right-hand list has:
- at most `pre.length` elements strictly left of each left-hand point,
- more than `pre.length` elements `≤` the next left-hand point,

then the two lists satisfy the weak `ListAlternates` layout. -/
theorem listAlternates_of_count_bounds
    {ss ts : List ℝ}
    (hss : ss.Pairwise (· ≤ ·))
    (hts : ts.Pairwise (· ≤ ·))
    (hlen : ss.length = ts.length)
    (hlt :
      ∀ (pre : List ℝ) {s : ℝ} {rest : List ℝ},
        ss = pre ++ s :: rest →
        ts.countP (· < s) ≤ pre.length)
    (hle :
      ∀ (pre : List ℝ) {s₁ s₂ : ℝ} {rest : List ℝ},
        ss = pre ++ s₁ :: s₂ :: rest →
        pre.length < ts.countP (· ≤ s₂)) :
    ListAlternates ss ts := by
  apply listAlternates_of_drop_bounds hss hts hlen
  · intro pre s rest hEq u hu
    exact all_ge_of_countP_lt_drop hts (hlt pre hEq) u hu
  · intro pre s₁ s₂ rest hEq
    exact exists_mem_drop_le_of_lt_countP
      (ts := ts) (s := s₂) (k := pre.length) (hle pre hEq)

/-- Build a differ-by-1 `Prec` witness from real-rootedness and root-count
inequalities against explicit sorted root lists. -/
theorem prec_of_count_bounds_succ
    {f F : ℝ[X]} {rs ts : List ℝ}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits) (hF_ne : F ≠ 0) (hF_splits : F.Splits)
    (hrs_sorted : rs.Pairwise (· ≤ ·))
    (hts_sorted : ts.Pairwise (· ≤ ·))
    (hrs_eq : (↑rs : Multiset ℝ) = f.roots)
    (hts_eq : (↑ts : Multiset ℝ) = F.roots)
    (hdeg : F.natDegree = f.natDegree + 1)
    (hhead :
      ∀ {s : ℝ} {rest : List ℝ},
        rs = s :: rest →
        0 < ts.countP (· ≤ s))
    (hlt :
      ∀ (pre : List ℝ) {s : ℝ} {rest : List ℝ},
        rs = pre ++ s :: rest →
        ts.countP (· < s) ≤ pre.length + 1)
    (hle :
      ∀ (pre : List ℝ) {s₁ s₂ : ℝ} {rest : List ℝ},
        rs = pre ++ s₁ :: s₂ :: rest →
        pre.length + 1 < ts.countP (· ≤ s₂)) :
    Prec f F := by
  have hrs_len : rs.length = f.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hf_splits]
  have hts_len : ts.length = F.natDegree := by
    rw [← Multiset.coe_card, hts_eq, card_roots_of_splits hF_splits]
  have hlen : rs.length + 1 = ts.length := by lia
  exact
    ⟨⟨hf_ne, hf_splits⟩, ⟨hF_ne, hF_splits⟩, rs, ts, hrs_sorted, hts_sorted,
      hrs_eq, hts_eq,
      Or.inl ⟨hlen, listInterlaces_of_count_bounds hrs_sorted hts_sorted hlen hhead hlt hle⟩⟩

/-- Build a same-degree `Prec` witness from real-rootedness and root-count
inequalities against explicit sorted root lists. -/
theorem prec_of_count_bounds_same
    {f F : ℝ[X]} {rs ts : List ℝ}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits) (hF_ne : F ≠ 0) (hF_splits : F.Splits)
    (hrs_sorted : rs.Pairwise (· ≤ ·))
    (hts_sorted : ts.Pairwise (· ≤ ·))
    (hrs_eq : (↑rs : Multiset ℝ) = f.roots)
    (hts_eq : (↑ts : Multiset ℝ) = F.roots)
    (hdeg : F.natDegree = f.natDegree)
    (hlt :
      ∀ (pre : List ℝ) {s : ℝ} {rest : List ℝ},
        rs = pre ++ s :: rest →
        ts.countP (· < s) ≤ pre.length)
    (hle :
      ∀ (pre : List ℝ) {s₁ s₂ : ℝ} {rest : List ℝ},
        rs = pre ++ s₁ :: s₂ :: rest →
        pre.length < ts.countP (· ≤ s₂)) :
    Prec f F := by
  have hrs_len : rs.length = f.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hf_splits]
  have hts_len : ts.length = F.natDegree := by
    rw [← Multiset.coe_card, hts_eq, card_roots_of_splits hF_splits]
  have hlen : rs.length = ts.length := by lia
  exact
    ⟨⟨hf_ne, hf_splits⟩, ⟨hF_ne, hF_splits⟩, rs, ts, hrs_sorted, hts_sorted,
      hrs_eq, hts_eq,
      Or.inr ⟨hlen, listAlternates_of_count_bounds hrs_sorted hts_sorted hlen hlt hle⟩⟩
end RealRooted.MaWangInternal

namespace RealRooted

export MaWangInternal
  (exists_roots_interlacing_of_consecutive_signs
    listInterlaces_of_count_bounds
    listAlternates_of_count_bounds
    prec_of_count_bounds_succ
    prec_of_count_bounds_same)

end RealRooted
