/-
# Ma–Wang theorem (2008)

If `F(x) = u(x) f(x) + v(x) f'(x)` with `deg(f) ≤ deg(F) ≤ deg(f) + 1`,
`f` real-rooted, `v(r) ≠ 0` whenever `f(r) = 0`, and positive leading
coefficients, then `F` is real-rooted and `f ⊳ F`.

Reference: Shi-Mei Ma and Yi Wang, 2008.

## Proof sketch

At each root `r` of `f`: `F(r) = v(r) * f'(r)`.
Since `v(r) ≠ 0`, the sign of `F(r)` is `sign(v(r)) * sign(f'(r))`.

Between consecutive roots `rᵢ < rᵢ₊₁` of `f`:
- `f'(rᵢ)` and `f'(rᵢ₊₁)` have opposite signs (derivative_sign_at_consecutive_roots)
- If `v(rᵢ)` and `v(rᵢ₊₁)` have the same sign: `F` changes sign → IVT root
- If `v` changes sign: `v` has a root `t ∈ (rᵢ, rᵢ₊₁)`, and
  `F(t) = u(t) * f(t) ≠ 0` (since `f` has no roots there).
  Combined with the sign at the endpoints, this gives roots by IVT.

The degree conditions ensure `F` has the right number of roots for interlacing.

## Relation to other results

This generalizes:
- `prec_affine_derivative` (our key lemma): `u = C c`, `v = 1 - X`
- Derivative interlacing: `u = 0`, `v = 1` (i.e., `F = f'`)
- Many other classical real-rootedness results
-/
import RealRooted.Basic
import RealRooted.Linear
import RealRooted.Derivative
import RealRooted.Wagner
import Mathlib.Analysis.Normed.Field.Approximation
import Mathlib.Analysis.Complex.Polynomial.Basic
-- import RealRooted.AffineDerivative  -- uncomment when AffineDerivative is built

open Polynomial Filter

noncomputable section

namespace RealRooted

section

/-- Core interval-root construction: if a polynomial has opposite-or-zero signs at
each consecutive pair in a sorted real list `rs`, then it has a root in every
closed interval between consecutive entries of `rs`. -/
private theorem exists_signInterleaving {F : ℝ[X]} :
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
      have hprod : F.eval r₁ * F.eval r₂ ≤ 0 := by
        simpa using hsign [] rfl
      obtain ⟨u, hu₁, hu₂, hu_root⟩ :=
        exists_isRoot_between_of_eval_mul_nonpos hr₁r₂ hprod
      have htail_sorted : (r₂ :: rest).Pairwise (· ≤ ·) :=
        (List.pairwise_cons.mp hrs_sorted).2
      obtain ⟨us, hus_len, hus_int, hus_roots⟩ :=
        exists_signInterleaving (F := F) (r₂ :: rest) htail_sorted
          (fun pre {a b tail} hEq => by
            have hEq' : r₁ :: r₂ :: rest = (r₁ :: pre) ++ a :: b :: tail := by
              simp [List.cons_append, hEq]
            simpa using hsign (r₁ :: pre) hEq')
      refine ⟨u :: us, ?_, ?_, ?_⟩
      · simp [hus_len]
      · exact ⟨hu₁, hu₂, hus_int⟩
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv'
        · exact hu_root
        · exact hus_roots v hv'

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
private theorem listInterlaces_of_drop_bounds :
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
      have hts_len : ts.length = 1 := by simpa using hlen.symm
      cases ts with
      | nil => simp at hlen
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
              have ht_le_s : t ≤ s := by
                simpa using hleft rfl
              have hs_le_u : s ≤ u := by
                exact hge [] rfl u (by simp)
              cases ss with
              | nil =>
                  have hus_nil : us = [] := by
                    simp at hlen
                    lia
                  subst hus_nil
                  simp [ListInterlaces, ht_le_s, hs_le_u]
              | cons s₂ ss' =>
                  have hu_le_s₂ : u ≤ s₂ := by
                    obtain ⟨w, hw_drop, hw_le⟩ := hexists [] rfl
                    have hu_le_w : u ≤ w := by
                      simpa using htu_sorted.head!_le hw_drop
                    exact le_trans hu_le_w hw_le
                  have hleft' :
                      ∀ {s' : ℝ} {rest : List ℝ},
                        s₂ :: ss' = s' :: rest →
                        (u :: us).head! ≤ s' := by
                    intro s' rest hEq
                    cases hEq
                    simpa using hu_le_s₂
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
                    intro pre s₁ s₂' rest hEq
                    have hEq' : s :: s₂ :: ss' = (s :: pre) ++ s₁ :: s₂' :: rest := by
                      simp [List.cons_append, hEq]
                    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                      hexists (s :: pre) hEq'
                  have hlen' : (s₂ :: ss').length + 1 = (u :: us).length := by
                    simp at hlen ⊢
                    lia
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
private theorem listAlternates_of_drop_bounds :
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
      have hs_le_t : s ≤ t := by
        exact hge [] rfl t (by simp)
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
            have ht_le_u : t ≤ u := by
              simpa using hts.head!_le hu_mem
            exact le_trans ht_le_u hu_le
          have hge' :
              ∀ (pre : List ℝ) {s' : ℝ} {rest : List ℝ},
                s₂ :: ss' = pre ++ s' :: rest →
                ∀ u ∈ (t :: ts).drop (pre.length + 1), s' ≤ u := by
            intro pre s' rest hEq u hu
            have hEq' : s :: s₂ :: ss' = (s :: pre) ++ s' :: rest := by
              simp [List.cons_append, hEq]
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
              hge (s :: pre) hEq' u hu
          have hexists' :
              ∀ (pre : List ℝ) {s₁ s₂' : ℝ} {rest : List ℝ},
                s₂ :: ss' = pre ++ s₁ :: s₂' :: rest →
                ∃ u, u ∈ (t :: ts).drop (pre.length + 1) ∧ u ≤ s₂' := by
            intro pre s₁ s₂' rest hEq
            have hEq' : s :: s₂ :: ss' = (s :: pre) ++ s₁ :: s₂' :: rest := by
              simp [List.cons_append, hEq]
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
              hexists (s :: pre) hEq'
          have hlen' : (s₂ :: ss').length + 1 = (t :: ts).length := by
            simp at hlen ⊢
            lia
          have hint_tail : ListInterlaces (s₂ :: ss') (t :: ts) :=
            listInterlaces_of_drop_bounds
              (ss := s₂ :: ss') (ts := t :: ts)
              (List.pairwise_cons.mp hss).2 hts hlen'
              (by
                intro s' rest hEq
                cases hEq
                simpa using ht_le_s₂)
              hge' hexists'
          exact ⟨hs_le_t, hint_tail⟩

/-- If a sorted list has at most `k` entries strictly below `s`, then every entry
in the `drop k` tail is `≥ s`. This is the count-to-tail bridge needed to feed
actual sorted root lists into the `drop`-based layout lemmas above. -/
private lemma all_ge_of_countP_lt_drop
    {ts : List ℝ} (hts : ts.Pairwise (· ≤ ·)) {s : ℝ} {k : ℕ}
    (hcount : ts.countP (· < s) ≤ k) :
    ∀ u ∈ ts.drop k, s ≤ u := by
  intro u hu
  by_contra hus
  have hu_lt : u < s := lt_of_not_ge hus
  have htake_lt : ∀ x ∈ ts.take k, x < s := by
    intro x hx
    have hx_le_u : x ≤ u := hts.rel_of_mem_take_of_mem_drop hx hu
    exact lt_of_le_of_lt hx_le_u hu_lt
  have hk : k ≤ ts.length := by
    by_contra hk
    have hk' : ts.length < k := lt_of_not_ge hk
    have hnil : ts.drop k = [] := List.drop_eq_nil_of_le hk'.le
    simp [hnil] at hu
  have htake_count : (ts.take k).countP (· < s) = k := by
    rw [List.countP_eq_length_filter]
    have hfilter :
        List.filter (fun x => decide (x < s)) (ts.take k) = ts.take k := by
      apply List.filter_eq_self.mpr
      intro x hx
      simp [htake_lt x hx]
    rw [hfilter]
    simp [List.length_take, Nat.min_eq_left hk]
  have hdrop_pos : 0 < (ts.drop k).countP (· < s) := by
    rw [List.countP_eq_length_filter]
    exact List.length_pos_of_mem <| List.mem_filter.mpr ⟨hu, by simpa using hu_lt⟩
  have hsplit :
      ts.countP (· < s) =
        (ts.take k).countP (· < s) + (ts.drop k).countP (· < s) := by
    simpa [List.take_append_drop] using
      (List.countP_append (p := fun x => decide (x < s)) (l₁ := ts.take k) (l₂ := ts.drop k))
  rw [hsplit, htake_count] at hcount
  lia

/-- If a list has more than `k` entries `≤ s`, then some entry of the `drop k`
tail is still `≤ s`. -/
private lemma exists_mem_drop_le_of_lt_countP
    {ts : List ℝ} {s : ℝ} {k : ℕ}
    (hcount : k < ts.countP (· ≤ s)) :
    ∃ u, u ∈ ts.drop k ∧ u ≤ s := by
  by_contra hnot
  have hdrop_zero : (ts.drop k).countP (· ≤ s) = 0 := by
    rw [List.countP_eq_length_filter]
    have hfilter : List.filter (fun u => decide (u ≤ s)) (ts.drop k) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro u hu
      have hu_not : ¬ u ≤ s := by
        exact fun hus => hnot ⟨u, hu, hus⟩
      simp [hu_not]
    simp [hfilter]
  have hsplit :
      ts.countP (· ≤ s) =
        (ts.take k).countP (· ≤ s) + (ts.drop k).countP (· ≤ s) := by
    simpa [List.take_append_drop] using
      (List.countP_append (p := fun x => decide (x ≤ s)) (l₁ := ts.take k) (l₂ := ts.drop k))
  rw [hsplit, hdrop_zero] at hcount
  have htake_le : (ts.take k).countP (· ≤ s) ≤ k := by
    exact
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
      exists_mem_drop_le_of_lt_countP (ts := ts) (s := s) (k := 0) (by simpa using hhead hEq)
    have hu_mem : u ∈ ts := by simpa using hu_drop
    have hhead_le_u : ts.head! ≤ u := by
      simpa using hts.head!_le hu_mem
    exact le_trans hhead_le_u hu_le
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
    (hf : f ≠ 0 ∧ f.roots.card = f.natDegree) (hF : F ≠ 0 ∧ F.roots.card = F.natDegree)
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
    rw [← Multiset.coe_card, hrs_eq, hf.2]
  have hts_len : ts.length = F.natDegree := by
    rw [← Multiset.coe_card, hts_eq, hF.2]
  have hlen : rs.length + 1 = ts.length := by
    rw [hrs_len, hts_len, hdeg]
  exact ⟨hf, hF, rs, ts, hrs_sorted, hts_sorted, hrs_eq, hts_eq,
    Or.inl ⟨hlen, listInterlaces_of_count_bounds hrs_sorted hts_sorted hlen hhead hlt hle⟩⟩

/-- Build a same-degree `Prec` witness from real-rootedness and root-count
inequalities against explicit sorted root lists. -/
theorem prec_of_count_bounds_same
    {f F : ℝ[X]} {rs ts : List ℝ}
    (hf : f ≠ 0 ∧ f.roots.card = f.natDegree) (hF : F ≠ 0 ∧ F.roots.card = F.natDegree)
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
    rw [← Multiset.coe_card, hrs_eq, hf.2]
  have hts_len : ts.length = F.natDegree := by
    rw [← Multiset.coe_card, hts_eq, hF.2]
  have hlen : rs.length = ts.length := by
    rw [hrs_len, hts_len, hdeg]
  exact ⟨hf, hF, rs, ts, hrs_sorted, hts_sorted, hrs_eq, hts_eq,
    Or.inr ⟨hlen, listAlternates_of_count_bounds hrs_sorted hts_sorted hlen hlt hle⟩⟩

/-- Sign-normalization for a product of linear factors: multiplying by
`(-1) ^ countP (s < ·)` flips exactly the negative factors and makes the product
nonnegative. -/
private lemma nonneg_normalized_prod_sub_countP :
    ∀ (ts : List ℝ) (s : ℝ),
      0 ≤ (-1 : ℝ) ^ (ts.countP (s < ·)) * (ts.map (fun x => s - x)).prod
  | [], _ => by simp
  | x :: xs, s => by
      by_cases hx : s < x
      · have ih := nonneg_normalized_prod_sub_countP xs s
        rw [List.countP_cons_of_pos (by simpa using hx), List.map_cons, List.prod_cons]
        have hfactor :
            (-1 : ℝ) ^ (xs.countP (s < ·) + 1) * ((s - x) * (xs.map (fun y => s - y)).prod) =
              (x - s) * ((-1 : ℝ) ^ (xs.countP (s < ·)) * (xs.map (fun y => s - y)).prod) := by
          ring
        rw [hfactor]
        exact mul_nonneg (sub_nonneg.mpr (le_of_lt hx)) ih
      · have ih := nonneg_normalized_prod_sub_countP xs s
        rw [List.countP_cons_of_neg (by simpa using hx), List.map_cons, List.prod_cons]
        have hx_nonneg : 0 ≤ s - x := sub_nonneg.mpr (le_of_not_gt hx)
        have hfactor :
            (-1 : ℝ) ^ xs.countP (s < ·) * ((s - x) * (xs.map (fun y => s - y)).prod) =
              (s - x) * ((-1 : ℝ) ^ xs.countP (s < ·) * (xs.map (fun y => s - y)).prod) := by
          ring
        rw [hfactor]
        exact mul_nonneg hx_nonneg ih

/-- For a real-rooted polynomial with positive leading coefficient, the sign of
`F.eval s` is controlled by the parity of the number of roots strictly to the
right of `s`. -/
private lemma nonneg_normalized_eval_of_countP_gt
    {F : ℝ[X]} (hF : F ≠ 0 ∧ F.roots.card = F.natDegree) (hF_pos : HasPosLeadingCoeff F)
    {ts : List ℝ} (hts_eq : (↑ts : Multiset ℝ) = F.roots) (s : ℝ) :
    0 ≤ (-1 : ℝ) ^ (ts.countP (s < ·)) * F.eval s := by
  have hprod := nonneg_normalized_prod_sub_countP ts s
  have hlead_nonneg : 0 ≤ F.leadingCoeff := hF_pos.le
  have hfactor :
      (-1 : ℝ) ^ (ts.countP (s < ·)) *
          (F.leadingCoeff * (ts.map (fun x => s - x)).prod) =
        F.leadingCoeff *
          (((-1 : ℝ) ^ (ts.countP (s < ·))) * (ts.map (fun x => s - x)).prod) := by
    ring
  have hmain :
      0 ≤ (-1 : ℝ) ^ (ts.countP (s < ·)) *
        (F.leadingCoeff * (ts.map (fun x => s - x)).prod) := by
    rw [hfactor]
    exact mul_nonneg hlead_nonneg hprod
  rw [eval_eq_leadingCoeff_mul_prod_sub hF s, ← hts_eq]
  simpa using hmain

/-- If the parity predicted by the root count would force a positive sign, then
an assumed nonpositive value must actually be a root. -/
private lemma isRoot_of_eval_nonpos_of_even_countP_gt
    {F : ℝ[X]} (hF : F ≠ 0 ∧ F.roots.card = F.natDegree) (hF_pos : HasPosLeadingCoeff F)
    {ts : List ℝ} (hts_eq : (↑ts : Multiset ℝ) = F.roots) {s : ℝ}
    (hs : F.eval s ≤ 0) (heven : Even (ts.countP (s < ·))) :
    F.IsRoot s := by
  rcases heven with ⟨k, hk⟩
  have hnorm := nonneg_normalized_eval_of_countP_gt hF hF_pos hts_eq s
  rw [hk] at hnorm
  norm_num at hnorm
  rw [Polynomial.IsRoot.def]
  linarith

/-- If the parity predicted by the root count would force a negative sign, then
an assumed nonnegative value must actually be a root. -/
private lemma isRoot_of_eval_nonneg_of_odd_countP_gt
    {F : ℝ[X]} (hF : F ≠ 0 ∧ F.roots.card = F.natDegree) (hF_pos : HasPosLeadingCoeff F)
    {ts : List ℝ} (hts_eq : (↑ts : Multiset ℝ) = F.roots) {s : ℝ}
    (hs : 0 ≤ F.eval s) (hodd : Odd (ts.countP (s < ·))) :
    F.IsRoot s := by
  rcases hodd with ⟨k, hk⟩
  have hnorm := nonneg_normalized_eval_of_countP_gt hF hF_pos hts_eq s
  rw [hk] at hnorm
  have hnorm' : 0 ≤ -F.eval s := by
    simpa [pow_add, pow_mul] using hnorm
  rw [Polynomial.IsRoot.def]
  linarith [hs, hnorm']

/-- A strictly negative value occurs only when an odd number of roots lie
strictly to the right. -/
private lemma odd_countP_gt_of_eval_neg
    {F : ℝ[X]} (hF : F ≠ 0 ∧ F.roots.card = F.natDegree) (hF_pos : HasPosLeadingCoeff F)
    {ts : List ℝ} (hts_eq : (↑ts : Multiset ℝ) = F.roots) {s : ℝ}
    (hs : F.eval s < 0) :
    Odd (ts.countP (s < ·)) := by
  rcases Nat.even_or_odd (ts.countP (s < ·)) with heven | hodd
  · exfalso
    exact (show ¬ F.IsRoot s from by
      intro hroot
      rw [Polynomial.IsRoot.def] at hroot
      linarith) <|
      isRoot_of_eval_nonpos_of_even_countP_gt hF hF_pos hts_eq (le_of_lt hs) heven
  · exact hodd

/-- A strictly positive value occurs only when an even number of roots lie
strictly to the right. -/
private lemma even_countP_gt_of_eval_pos
    {F : ℝ[X]} (hF : F ≠ 0 ∧ F.roots.card = F.natDegree) (hF_pos : HasPosLeadingCoeff F)
    {ts : List ℝ} (hts_eq : (↑ts : Multiset ℝ) = F.roots) {s : ℝ}
    (hs : 0 < F.eval s) :
    Even (ts.countP (s < ·)) := by
  rcases Nat.even_or_odd (ts.countP (s < ·)) with heven | hodd
  · exact heven
  · exfalso
    exact (show ¬ F.IsRoot s from by
      intro hroot
      rw [Polynomial.IsRoot.def] at hroot
      linarith) <|
      isRoot_of_eval_nonneg_of_odd_countP_gt hF hF_pos hts_eq (le_of_lt hs) hodd

/-- In an interlacing layout, every consecutive pair on the right-hand list has
some left-hand element weakly between them. -/
private lemma exists_mem_between_of_listInterlaces_consecutive :
    ∀ {ss rs pre : List ℝ} {r₁ r₂ : ℝ} {rest : List ℝ},
      ListInterlaces ss rs →
      rs = pre ++ r₁ :: r₂ :: rest →
      ∃ s, s ∈ ss ∧ r₁ ≤ s ∧ s ≤ r₂
  := by
    intro ss rs pre r₁ r₂ rest hint hEq
    induction pre generalizing ss rs with
    | nil =>
        subst hEq
        cases ss with
        | nil =>
            simp [ListInterlaces] at hint
        | cons s ss' =>
            have hs : r₁ ≤ s ∧ s ≤ r₂ ∧ ListInterlaces ss' (r₂ :: rest) := by
              simpa [ListInterlaces] using hint
            exact ⟨s, by simp, hs.1, hs.2.1⟩
    | cons a pre ih =>
        cases ss with
        | nil =>
            cases rs with
            | nil => simp at hEq
            | cons b rs' =>
                cases rs' with
                | nil => simp at hEq
                | cons c rs'' =>
                    simp [ListInterlaces] at hint
        | cons s ss' =>
            cases rs with
            | nil => simp at hEq
            | cons b rs' =>
                have hbEq : b :: rs' = (a :: pre) ++ r₁ :: r₂ :: rest := hEq
                simp only [List.cons_append, List.cons.injEq] at hbEq
                rcases hbEq with ⟨rfl, htailEq⟩
                have htail : ListInterlaces ss' (pre ++ r₁ :: r₂ :: rest) := by
                  have hint' := hint
                  cases pre with
                  | nil =>
                      simp [htailEq, ListInterlaces] at hint'
                      simpa using hint'.2.2
                  | cons a' pre' =>
                      simp [htailEq, ListInterlaces] at hint'
                      simpa using hint'.2.2
                obtain ⟨t, ht_mem, hr₁t, ht_r₂⟩ :=
                  ih (ss := ss') (rs := pre ++ r₁ :: r₂ :: rest) htail rfl
                exact ⟨t, by simp [ht_mem], hr₁t, ht_r₂⟩

/-- If `g ⊳ f` and `f` and `g` share no roots, then consecutive roots of `f`
are strictly increasing. -/
private lemma lt_of_consecutive_of_interlaces_of_no_common
    {f g : ℝ[X]} {rs ss pre : List ℝ} {r₁ r₂ : ℝ} {rest : List ℝ}
    (hf : f ≠ 0 ∧ f.roots.card = f.natDegree) (hg : g ≠ 0 ∧ g.roots.card = g.natDegree)
    (hrs_eq : (↑rs : Multiset ℝ) = f.roots)
    (hss_eq : (↑ss : Multiset ℝ) = g.roots)
    (hint : ListInterlaces ss rs)
    (hEq : rs = pre ++ r₁ :: r₂ :: rest)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    r₁ < r₂ := by
  obtain ⟨s, hs_mem, hr₁s, hs_r₂⟩ :=
    exists_mem_between_of_listInterlaces_consecutive hint hEq
  have hr₁_root : f.IsRoot r₁ := by
    apply (mem_roots hf.1).mp
    rw [← hrs_eq]
    exact Multiset.mem_coe.mpr (by rw [hEq]; simp)
  have hs_root : g.IsRoot s := by
    apply (mem_roots hg.1).mp
    rw [← hss_eq]
    exact Multiset.mem_coe.mpr hs_mem
  by_contra hnot
  have hr₂_le_r₁ : r₂ ≤ r₁ := le_of_not_gt hnot
  have hs_eq : s = r₁ := le_antisymm (le_trans hs_r₂ hr₂_le_r₁) hr₁s
  exact hno r₁ hr₁_root (by simpa [hs_eq] using hs_root)

private lemma countP_le_add_countP_gt_eq_length (ts : List ℝ) (s : ℝ) :
    ts.countP (· ≤ s) + ts.countP (s < ·) = ts.length := by
  simpa [not_le, Nat.add_comm] using
    (ts.length_eq_countP_add_countP (fun x => decide (x ≤ s))).symm

private lemma countP_lt_countP_of_exists
    {ts : List ℝ} {p q : ℝ → Bool}
    (hpq : ∀ x, p x = true → q x = true)
    {a : ℝ} (ha : a ∈ ts) (hpa : p a = false) (hqa : q a = true) :
    ts.countP p < ts.countP q := by
  have hcount :
      (ts.filter q).countP p = ts.countP p := by
    rw [List.countP_eq_length_filter, List.countP_eq_length_filter]
    simp_rw [List.filter_filter]
    congr
    ext x
    by_cases hp : p x = true
    · simp [hp, hpq x hp]
    · simp [hp]
  have hlt :
      (ts.filter q).countP p < (ts.filter q).length := by
    rw [List.countP_lt_length_iff]
    refine ⟨a, List.mem_filter.mpr ⟨ha, hqa⟩, hpa⟩
  calc
    ts.countP p = (ts.filter q).countP p := by symm; exact hcount
    _ < (ts.filter q).length := hlt
    _ = ts.countP q := by rw [List.countP_eq_length_filter]

private lemma isRoot_of_mem_sorted_roots_eq
    {f : ℝ[X]} {rs pre : List ℝ} {r : ℝ} {rest : List ℝ}
    (hrs_eq : (↑rs : Multiset ℝ) = f.roots)
    (hEq : rs = pre ++ r :: rest) :
    f.IsRoot r := by
  have hf_ne : f ≠ 0 := by
    intro hf0
    have : r ∈ f.roots := by
      rw [← hrs_eq]
      exact Multiset.mem_coe.mpr (by rw [hEq]; simp)
    rw [hf0] at this
    simp at this
  exact (mem_roots hf_ne).mp <| by
    rw [← hrs_eq]
    exact Multiset.mem_coe.mpr (by rw [hEq]; simp)

private lemma listInterlaces_tail_pair_prod_nonneg :
    ∀ {ss : List ℝ} {r₁ r₂ : ℝ} {rest : List ℝ},
      r₁ ≤ r₂ →
      ListInterlaces ss (r₂ :: rest) →
      0 ≤ (ss.map (fun x => (r₁ - x) * (r₂ - x))).prod
  | ss, r₁, r₂, rest, hr₁r₂, h => by
      refine List.prod_nonneg ?_
      intro y hy
      rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
      have hr₂x : r₂ ≤ x := listInterlaces_all_ge ss rest r₂ h x hx
      have hr₁x : r₁ ≤ x := le_trans hr₁r₂ hr₂x
      nlinarith

private lemma prod_mul_prod_eq_prod_pairwise (l : List ℝ) (a b : ℝ) :
    (l.map (fun x => a - x)).prod * (l.map (fun x => b - x)).prod =
      (l.map fun x => (a - x) * (b - x)).prod := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      calc
        ((x :: xs).map (fun y => a - y)).prod * ((x :: xs).map (fun y => b - y)).prod
            = ((a - x) * (xs.map (fun y => a - y)).prod) *
                ((b - x) * (xs.map (fun y => b - y)).prod) := by
                  simp
        _ = ((a - x) * (b - x)) *
              ((xs.map (fun y => a - y)).prod * (xs.map (fun y => b - y)).prod) := by
                ring
        _ = ((a - x) * (b - x)) * ((xs.map fun y => (a - y) * (b - y)).prod) := by
              rw [ih]
        _ = ((x :: xs).map fun y => (a - y) * (b - y)).prod := by
              simp

/-- In a head-position interlacing layout, the product contribution from the
root list has opposite-or-zero signs at the first two right-hand points. -/
private lemma listInterlaces_prod_mul_prod_nonpos_at_heads
    {ss : List ℝ} {r₁ r₂ : ℝ} {rest : List ℝ}
    (hint : ListInterlaces ss (r₁ :: r₂ :: rest)) :
    (ss.map (fun x => r₁ - x)).prod * (ss.map (fun x => r₂ - x)).prod ≤ 0 := by
  obtain ⟨s, ss', rfl⟩ : ∃ s ss', ss = s :: ss' := by
    cases ss with
    | nil => simp [ListInterlaces] at hint
    | cons s ss => exact ⟨s, ss, rfl⟩
  obtain ⟨hr₁s, hsr₂, htail⟩ := hint
  have hr₁r₂ : r₁ ≤ r₂ := le_trans hr₁s hsr₂
  have hs_head_nonpos : (r₁ - s) * (r₂ - s) ≤ 0 := by
    nlinarith
  have htail_nonneg :
      0 ≤ ((ss'.map fun x => (r₁ - x) * (r₂ - x))).prod := by
    exact listInterlaces_tail_pair_prod_nonneg hr₁r₂ htail
  have htail_nonneg' :
      0 ≤ (ss'.map (fun x => r₁ - x)).prod * (ss'.map (fun x => r₂ - x)).prod := by
    rw [prod_mul_prod_eq_prod_pairwise ss' r₁ r₂]
    exact htail_nonneg
  calc
    ((s :: ss').map (fun x => r₁ - x)).prod * ((s :: ss').map (fun x => r₂ - x)).prod
        = ((r₁ - s) * (r₂ - s)) *
            ((ss'.map (fun x => r₁ - x)).prod * (ss'.map (fun x => r₂ - x)).prod) := by
              simp [mul_assoc, mul_left_comm]
    _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hs_head_nonpos htail_nonneg'

/-- In a sorted interlacing layout, the polynomial-factor product has
opposite-or-zero signs at any consecutive pair on the right-hand list. -/
private lemma listInterlaces_prod_mul_prod_nonpos_of_consecutive :
    ∀ {ss rs pre : List ℝ} {r₁ r₂ : ℝ} {rest : List ℝ},
      rs.Pairwise (· ≤ ·) →
      ListInterlaces ss rs →
      rs = pre ++ r₁ :: r₂ :: rest →
      (ss.map (fun x => r₁ - x)).prod * (ss.map (fun x => r₂ - x)).prod ≤ 0
  | ss, rs, [], r₁, r₂, rest, _, hint, hEq => by
      subst hEq
      exact listInterlaces_prod_mul_prod_nonpos_at_heads hint
  | ss, rs, a :: pre, r₁, r₂, rest, hrs_sorted, hint, hEq => by
      obtain ⟨s, ss', rfl⟩ : ∃ s ss', ss = s :: ss' := by
        cases ss with
        | nil =>
            cases rs with
            | nil => simp at hEq
            | cons b rs' =>
                cases rs' with
                | nil => simp at hEq
                | cons c rs'' => simp [ListInterlaces] at hint
        | cons s ss' => exact ⟨s, ss', rfl⟩
      cases rs with
      | nil => simp at hEq
      | cons b rs' =>
          have hbEq : b :: rs' = (a :: pre) ++ r₁ :: r₂ :: rest := hEq
          cases pre with
          | nil =>
              simp only [List.cons_append, List.nil_append, List.cons.injEq] at hbEq
              rcases hbEq with ⟨rfl, rfl⟩
              have hint' : b ≤ s ∧ s ≤ r₁ ∧
                ListInterlaces ss' (r₁ :: r₂ :: rest) := by
                simpa [ListInterlaces] using hint
              obtain ⟨har₁, hs_r₁, htail⟩ := hint'
              have hrs_tail : (r₁ :: r₂ :: rest).Pairwise (· ≤ ·) :=
                (List.pairwise_cons.mp hrs_sorted).2
              have hr₁r₂ : r₁ ≤ r₂ := List.rel_of_pairwise_cons hrs_tail (by simp)
              have hs_factor_nonneg : 0 ≤ (r₁ - s) * (r₂ - s) := by
                nlinarith
              have htail_nonpos :
                  (ss'.map (fun x => r₁ - x)).prod *
                    (ss'.map (fun x => r₂ - x)).prod ≤
                  0 := by
                exact listInterlaces_prod_mul_prod_nonpos_at_heads htail
              calc
                ((s :: ss').map (fun x => r₁ - x)).prod *
                    ((s :: ss').map (fun x => r₂ - x)).prod
                    = ((r₁ - s) * (r₂ - s)) *
                      ((ss'.map (fun x => r₁ - x)).prod *
                        (ss'.map (fun x => r₂ - x)).prod) := by
                          simp [mul_assoc, mul_left_comm]
                _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs_factor_nonneg htail_nonpos
          | cons a' pre' =>
              simp only [List.cons_append, List.cons.injEq] at hbEq
              rcases hbEq with ⟨rfl, htailEq⟩
              have hint_rs :
                  ListInterlaces (s :: ss') (b :: a' :: pre' ++ r₁ :: r₂ :: rest) := by
                simpa [htailEq] using hint
              have hint' : b ≤ s ∧ s ≤ a' ∧
                  ListInterlaces ss' (a' :: pre' ++ r₁ :: r₂ :: rest) := by
                simpa [ListInterlaces] using hint_rs
              obtain ⟨_, hs_le_a', hint_tail⟩ := hint'
              have hrs_tail : (a' :: pre' ++ r₁ :: r₂ :: rest).Pairwise (· ≤ ·) :=
                by simpa [htailEq] using (List.pairwise_cons.mp hrs_sorted).2
              have hr₁_mem : r₁ ∈ (a' :: pre' ++ r₁ :: r₂ :: rest) := by
                simp [List.mem_cons, List.mem_append]
              have ha'_le_r₁ : a' ≤ r₁ := by
                exact hrs_tail.head!_le hr₁_mem
              have hs_factor_nonneg : 0 ≤ (r₁ - s) * (r₂ - s) := by
                have hs_le_r₁ : s ≤ r₁ := le_trans hs_le_a' ha'_le_r₁
                have hr₁r₂ : r₁ ≤ r₂ := by
                  have hpre_tail : (pre' ++ r₁ :: r₂ :: rest).Pairwise (· ≤ ·) :=
                    (List.pairwise_cons.mp hrs_tail).2
                  have hrs_r₁r₂ : (r₁ :: r₂ :: rest).Pairwise (· ≤ ·) :=
                    (List.pairwise_append.mp hpre_tail).2.1
                  exact List.rel_of_pairwise_cons hrs_r₁r₂ (by simp)
                nlinarith
              have htail_nonpos :
                  (ss'.map (fun x => r₁ - x)).prod *
                    (ss'.map (fun x => r₂ - x)).prod ≤
                  0 :=
                listInterlaces_prod_mul_prod_nonpos_of_consecutive
                  (ss := ss') (rs := a' :: pre' ++ r₁ :: r₂ :: rest)
                  (pre := a' :: pre') (rest := rest) hrs_tail hint_tail (by simp)
              calc
                ((s :: ss').map (fun x => r₁ - x)).prod *
                    ((s :: ss').map (fun x => r₂ - x)).prod
                    = ((r₁ - s) * (r₂ - s)) *
                      ((ss'.map (fun x => r₁ - x)).prod *
                        (ss'.map (fun x => r₂ - x)).prod) := by
                          simp [mul_assoc, mul_left_comm]
                _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs_factor_nonneg htail_nonpos

/-- At consecutive roots of the right-hand polynomial in an interlacing layout,
the interlacing polynomial has opposite-or-zero signs. -/
private lemma eval_mul_eval_nonpos_of_interlacing_heads {g : ℝ[X]}
    (hg : g ≠ 0 ∧ g.roots.card = g.natDegree) (_hg_pos : HasPosLeadingCoeff g)
    {ss : List ℝ} {r₁ r₂ : ℝ} {rest : List ℝ}
    (hss_eq : (↑ss : Multiset ℝ) = g.roots)
    (hint : ListInterlaces ss (r₁ :: r₂ :: rest)) :
    g.eval r₁ * g.eval r₂ ≤ 0 := by
  rw [eval_eq_leadingCoeff_mul_prod_sub hg r₁,
      eval_eq_leadingCoeff_mul_prod_sub hg r₂, ← hss_eq]
  have hprod_nonpos :
      (ss.map (fun x => r₁ - x)).prod *
        (ss.map (fun x => r₂ - x)).prod ≤
      0 :=
    listInterlaces_prod_mul_prod_nonpos_at_heads hint
  have hlead_nonneg : 0 ≤ g.leadingCoeff * g.leadingCoeff := by
    simpa [pow_two] using sq_nonneg g.leadingCoeff
  have hprod_r₁ :
      ((↑ss : Multiset ℝ).map (fun x => r₁ - x)).prod =
        (ss.map (fun x => r₁ - x)).prod := rfl
  have hprod_r₂ :
      ((↑ss : Multiset ℝ).map (fun x => r₂ - x)).prod =
        (ss.map (fun x => r₂ - x)).prod := rfl
  have hfactor :
      (g.leadingCoeff * (ss.map (fun x => r₁ - x)).prod) *
          (g.leadingCoeff * (ss.map (fun x => r₂ - x)).prod) =
        (g.leadingCoeff * g.leadingCoeff) *
          (((ss.map (fun x => r₁ - x)).prod) *
            ((ss.map (fun x => r₂ - x)).prod)) := by
    ring
  rw [hprod_r₁, hprod_r₂]
  rw [hfactor]
  exact mul_nonpos_of_nonneg_of_nonpos hlead_nonneg hprod_nonpos

/-- At any consecutive pair in a sorted interlacing layout, the interlacing
polynomial has opposite-or-zero signs. -/
private lemma eval_mul_eval_nonpos_of_interlacing_consecutive {g : ℝ[X]}
    (hg : g ≠ 0 ∧ g.roots.card = g.natDegree)
    {ss rs pre : List ℝ} {r₁ r₂ : ℝ} {rest : List ℝ}
    (hrs_sorted : rs.Pairwise (· ≤ ·))
    (hss_eq : (↑ss : Multiset ℝ) = g.roots)
    (hint : ListInterlaces ss rs)
    (hEq : rs = pre ++ r₁ :: r₂ :: rest) :
    g.eval r₁ * g.eval r₂ ≤ 0 := by
  rw [eval_eq_leadingCoeff_mul_prod_sub hg r₁,
      eval_eq_leadingCoeff_mul_prod_sub hg r₂, ← hss_eq]
  have hprod_nonpos :
      (ss.map (fun x => r₁ - x)).prod *
        (ss.map (fun x => r₂ - x)).prod ≤
      0 :=
    listInterlaces_prod_mul_prod_nonpos_of_consecutive hrs_sorted hint hEq
  have hlead_nonneg : 0 ≤ g.leadingCoeff * g.leadingCoeff := by
    simpa [pow_two] using sq_nonneg g.leadingCoeff
  have hprod_r₁ :
      ((↑ss : Multiset ℝ).map (fun x => r₁ - x)).prod =
        (ss.map (fun x => r₁ - x)).prod := rfl
  have hprod_r₂ :
      ((↑ss : Multiset ℝ).map (fun x => r₂ - x)).prod =
        (ss.map (fun x => r₂ - x)).prod := rfl
  have hfactor :
      (g.leadingCoeff * (ss.map (fun x => r₁ - x)).prod) *
          (g.leadingCoeff * (ss.map (fun x => r₂ - x)).prod) =
        (g.leadingCoeff * g.leadingCoeff) *
          (((ss.map (fun x => r₁ - x)).prod) *
            ((ss.map (fun x => r₂ - x)).prod)) := by
    ring
  rw [hprod_r₁, hprod_r₂, hfactor]
  exact mul_nonpos_of_nonneg_of_nonpos hlead_nonneg hprod_nonpos

/-- Strict IVT bridge: strictly opposite endpoint signs give a real root in the
open interval. -/
lemma exists_isRoot_between_of_eval_mul_neg {p : ℝ[X]} {a b : ℝ}
    (hab : a < b) (hsign : p.eval a * p.eval b < 0) :
    ∃ c, a < c ∧ c < b ∧ p.IsRoot c := by
  obtain ⟨c, hac, hcb, hc_root⟩ :=
    exists_isRoot_between_of_eval_mul_nonpos (le_of_lt hab) (le_of_lt hsign)
  have hca : c ≠ a := by
    intro h
    subst h
    have : p.eval c = 0 := hc_root
    have hcontra : ¬ p.eval c * p.eval b < 0 := by simp [this]
    exact hcontra hsign
  have hcb' : c ≠ b := by
    intro h
    subst h
    have : p.eval c = 0 := hc_root
    have hcontra : ¬ p.eval a * p.eval c < 0 := by simp [this]
    exact hcontra hsign
  exact ⟨c, lt_of_le_of_ne hac (Ne.symm hca), lt_of_le_of_ne hcb hcb', hc_root⟩

/-- Strict interval-root construction: if a polynomial has strictly opposite
signs at each consecutive pair in a sorted real list `rs`, then it has a root
strictly between each consecutive pair. The constructed root list is strictly
sorted. -/
private theorem exists_strictSignInterleaving {F : ℝ[X]} :
    ∀ (rs : List ℝ),
      rs.Pairwise (· ≤ ·) →
      (∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        F.eval r₁ * F.eval r₂ < 0) →
      ∃ us : List ℝ, us.length = rs.length - 1 ∧
        ListInterlaces us rs ∧
        (∀ u ∈ us, F.IsRoot u) ∧
        us.Pairwise (· < ·)
  | [], _, _ => by
      refine ⟨[], by simp, ?_, ?_, ?_⟩
      · simp [ListInterlaces]
      · simp
      · exact List.Pairwise.nil
  | [_], _, _ => by
      refine ⟨[], by simp, ?_, ?_, ?_⟩
      · simp [ListInterlaces]
      · simp
      · exact List.Pairwise.nil
  | r₁ :: r₂ :: rest, hrs_sorted, hsign => by
      have hr₁r₂ : r₁ < r₂ := by
        have hprod : F.eval r₁ * F.eval r₂ < 0 := by
          simpa using hsign [] rfl
        have hr₁r₂_le : r₁ ≤ r₂ := List.rel_of_pairwise_cons hrs_sorted (by simp)
        by_contra hEq
        have : F.eval r₁ * F.eval r₂ = (F.eval r₁) ^ 2 := by
          have : r₁ = r₂ := le_antisymm hr₁r₂_le (not_lt.mp hEq)
          subst this
          ring
        nlinarith [sq_nonneg (F.eval r₁)]
      obtain ⟨u, hu₁, hu₂, hu_root⟩ :=
        exists_isRoot_between_of_eval_mul_neg hr₁r₂ (by simpa using hsign [] rfl)
      have htail_sorted : (r₂ :: rest).Pairwise (· ≤ ·) :=
        (List.pairwise_cons.mp hrs_sorted).2
      obtain ⟨us, hus_len, hus_int, hus_roots, hus_pw⟩ :=
        exists_strictSignInterleaving (F := F) (r₂ :: rest) htail_sorted
          (fun pre {a b tail} hEq => by
            have hEq' : r₁ :: r₂ :: rest = (r₁ :: pre) ++ a :: b :: tail := by
              simp [List.cons_append, hEq]
            simpa using hsign (r₁ :: pre) hEq')
      have hu_lt_all : ∀ w ∈ us, u < w := by
        intro w hw
        exact lt_of_lt_of_le hu₂ (listInterlaces_all_ge us rest r₂ hus_int w hw)
      refine ⟨u :: us, ?_, ?_, ?_, ?_⟩
      · simp [hus_len]
      · exact ⟨le_of_lt hu₁, le_of_lt hu₂, hus_int⟩
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv'
        · exact hu_root
        · exact hus_roots v hv'
      · exact List.pairwise_cons.mpr ⟨hu_lt_all, hus_pw⟩

/-- Public strict wrapper around `exists_strictSignInterleaving`. -/
theorem exists_roots_strictly_interlacing_of_consecutive_signs {F : ℝ[X]} {rs : List ℝ}
    (hrs_sorted : rs.Pairwise (· ≤ ·))
    (hsign :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        F.eval r₁ * F.eval r₂ < 0) :
    ∃ us : List ℝ, us.length = rs.length - 1 ∧
      ListInterlaces us rs ∧
      (∀ u ∈ us, F.IsRoot u) ∧
      us.Pairwise (· < ·) :=
  exists_strictSignInterleaving (F := F) rs hrs_sorted hsign

/-- If every element of the right-hand list is strictly above `a`, then so is
every element of the interlacing left-hand list. -/
private lemma listInterlaces_all_gt_of_lowerBound :
    ∀ {us rs : List ℝ},
      ListInterlaces us rs →
      ∀ {a : ℝ}, (∀ r ∈ rs, a < r) → ∀ u ∈ us, a < u
  | [], [], hint, a, hlt, u, hu => by
      simp at hu
  | [], [_], hint, a, hlt, u, hu => by
      simp at hu
  | s :: ss, r₁ :: r₂ :: rs, hint, a, hlt, u, hu => by
      obtain ⟨hr₁s, _, htail⟩ := hint
      rcases List.mem_cons.mp hu with rfl | hu'
      · exact lt_of_lt_of_le (hlt r₁ (by simp)) hr₁s
      · exact listInterlaces_all_gt_of_lowerBound htail
          (fun r hr => hlt r (by simp [hr])) u hu'
  | [], _ :: _ :: _, hint, _, _, _, _ => by simp [ListInterlaces] at hint
  | _ :: _, [], hint, _, _, _, _ => by simp [ListInterlaces] at hint
  | _ :: _, [_], hint, _, _, _, _ => by simp [ListInterlaces] at hint

/-- If every element of the right-hand list is strictly below `a`, then so is
every element of the interlacing left-hand list. -/
private lemma listInterlaces_all_lt_of_upperBound :
    ∀ {us rs : List ℝ},
      ListInterlaces us rs →
      ∀ {a : ℝ}, (∀ r ∈ rs, r < a) → ∀ u ∈ us, u < a
  | [], [], hint, a, hlt, u, hu => by
      simp at hu
  | [], [_], hint, a, hlt, u, hu => by
      simp at hu
  | s :: ss, r₁ :: r₂ :: rs, hint, a, hlt, u, hu => by
      obtain ⟨_, hsr₂, htail⟩ := hint
      rcases List.mem_cons.mp hu with rfl | hu'
      · exact lt_of_le_of_lt hsr₂ (hlt r₂ (by simp))
      · exact listInterlaces_all_lt_of_upperBound htail
          (fun r hr => hlt r (by simp [hr])) u hu'
  | [], _ :: _ :: _, hint, _, _, _, _ => by simp [ListInterlaces] at hint
  | _ :: _, [], hint, _, _, _, _ => by simp [ListInterlaces] at hint
  | _ :: _, [_], hint, _, _, _, _ => by simp [ListInterlaces] at hint

/-- Every element of the left-hand list is at most the last element of a
nonempty sorted right-hand list in a `ListInterlaces` layout. -/
private lemma listInterlaces_all_le_getLast :
    ∀ {us rs : List ℝ},
      (hrs_ne : rs ≠ []) →
      rs.Pairwise (· ≤ ·) →
      ListInterlaces us rs →
      ∀ u ∈ us, u ≤ rs.getLast hrs_ne
  | [], [], hrs_ne, _, hint, u, hu => by
      cases (hrs_ne rfl)
  | [], [_], _, _, hint, u, hu => by
      simp at hu
  | s :: ss, [r], _, _, hint, _, _ => by
      simp [ListInterlaces] at hint
  | s :: ss, r₁ :: r₂ :: rs, _, hrs_sorted, hint, u, hu => by
      obtain ⟨_, hs_r₂, htail⟩ := hint
      rcases List.mem_cons.mp hu with rfl | hu'
      · exact le_trans hs_r₂ (List.Pairwise.rel_getLast hrs_sorted (by simp [List.mem_cons]))
      · exact listInterlaces_all_le_getLast (rs := r₂ :: rs) (by simp)
          ((List.pairwise_cons.mp hrs_sorted).2) htail u hu'

private lemma eval_pos_of_all_roots_lt {p : ℝ[X]} {r : ℝ}
    (hp : p ≠ 0 ∧ p.roots.card = p.natDegree) (hp_pos : HasPosLeadingCoeff p)
    (hlt : ∀ t ∈ p.roots, t < r) :
    0 < p.eval r := by
  rw [eval_eq_leadingCoeff_mul_prod_sub hp r]
  have hprod : 0 < (p.roots.map (r - ·)).prod := by
    refine Multiset.prod_pos ?_
    intro y hy
    rcases Multiset.mem_map.mp hy with ⟨t, ht, rfl⟩
    exact sub_pos.mpr (hlt t ht)
  exact mul_pos hp_pos hprod

private lemma eval_pos_of_all_roots_gt_of_even {p : ℝ[X]} {r : ℝ}
    (hp : p ≠ 0 ∧ p.roots.card = p.natDegree) (hp_pos : HasPosLeadingCoeff p)
    (hpar : Even p.natDegree)
    (hgt : ∀ t ∈ p.roots, r < t) :
    0 < p.eval r := by
  by_cases hdeg0 : p.natDegree = 0
  · rw [eq_C_of_natDegree_eq_zero hdeg0] at hp_pos ⊢
    simpa [HasPosLeadingCoeff] using hp_pos
  · have hdeg : 0 < p.degree := natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hdeg0)
    have ht : Tendsto (fun x => p.eval x) atBot atTop :=
      tendsto_eval_atBot_atTop_of_posLeadingCoeff_even hp_pos hdeg hpar
    by_contra hnonpos
    rcases eq_or_lt_of_le (le_of_not_gt hnonpos) with hzero | hneg
    · have hr_root : p.IsRoot r := by simpa [Polynomial.IsRoot.def] using hzero
      exact lt_irrefl r (hgt r ((mem_roots hp.1).mpr hr_root))
    · obtain ⟨u, hu_le, hu_root⟩ := exists_isRoot_le_of_eval_neg_of_tendsto_atBot_atTop hneg ht
      exact not_lt_of_ge hu_le (hgt u ((mem_roots hp.1).mpr hu_root))

private lemma eval_neg_of_all_roots_gt_of_odd {p : ℝ[X]} {r : ℝ}
    (hp : p ≠ 0 ∧ p.roots.card = p.natDegree) (hp_pos : HasPosLeadingCoeff p)
    (hpar : Odd p.natDegree)
    (hgt : ∀ t ∈ p.roots, r < t) :
    p.eval r < 0 := by
  have hdeg : 0 < p.degree := by
    have hnatdeg : 0 < p.natDegree := by
      rcases hpar with ⟨k, hk⟩
      lia
    exact natDegree_pos_iff_degree_pos.mp hnatdeg
  have ht : Tendsto (fun x => p.eval x) atBot atBot :=
    tendsto_eval_atBot_atBot_of_posLeadingCoeff_odd hp_pos hdeg hpar
  by_contra hnonneg
  rcases eq_or_lt_of_le (le_of_not_gt hnonneg) with hzero | hpos
  · have hr_root : p.IsRoot r := by simpa [eq_comm, Polynomial.IsRoot.def] using hzero
    exact lt_irrefl r (hgt r ((mem_roots hp.1).mpr hr_root))
  · obtain ⟨u, hu_le, hu_root⟩ := exists_isRoot_le_of_eval_pos_of_tendsto_atBot_atBot hpos ht
    exact not_lt_of_ge hu_le (hgt u ((mem_roots hp.1).mpr hu_root))

private lemma eval_sign_of_interlaces_root
    {f g : ℝ[X]} {rs ss : List ℝ}
    (hg : g ≠ 0 ∧ g.roots.card = g.natDegree) (hg_pos : HasPosLeadingCoeff g)
    (hrs_sorted : rs.Pairwise (· ≤ ·))
    (hrs_eq : (↑rs : Multiset ℝ) = f.roots)
    (hss_eq : (↑ss : Multiset ℝ) = g.roots)
    (hint : ListInterlaces ss rs)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    ∀ (pre : List ℝ) {r : ℝ} {rest : List ℝ},
      rs = pre ++ r :: rest →
      (Even rest.length → 0 < g.eval r) ∧ (Odd rest.length → g.eval r < 0) := by
  intro pre r rest hEq
  induction rest generalizing pre r with
  | nil =>
      have hrs_ne : rs ≠ [] := by
        rw [hEq]
        simp
      have hr_root : f.IsRoot r := isRoot_of_mem_sorted_roots_eq hrs_eq hEq
      have hroots_g_lt_r : ∀ t ∈ g.roots, t < r := by
        intro t ht
        have ht_ss : t ∈ ss := by
          rw [← hss_eq] at ht
          exact Multiset.mem_coe.mp ht
        have ht_le_last : t ≤ rs.getLast hrs_ne :=
          listInterlaces_all_le_getLast hrs_ne hrs_sorted hint t ht_ss
        have ht_le_r : t ≤ r := by
          simpa [hEq] using ht_le_last
        have ht_root : g.IsRoot t := (mem_roots hg.1).mp ht
        by_contra hnot
        have hr_le_t : r ≤ t := not_lt.mp hnot
        have ht_eq : t = r := le_antisymm ht_le_r hr_le_t
        exact hno r hr_root (by simpa [ht_eq] using ht_root)
      constructor
      · intro _
        exact eval_pos_of_all_roots_lt hg hg_pos hroots_g_lt_r
      · intro hodd
        rcases hodd with ⟨k, hk⟩
        simp at hk
  | cons r₂ rest ih =>
      have hEq_next : rs = (pre ++ [r]) ++ r₂ :: rest := by
        simpa [List.append_assoc] using hEq
      have hnext := ih (pre := pre ++ [r]) (r := r₂) hEq_next
      have hr_root : f.IsRoot r := isRoot_of_mem_sorted_roots_eq hrs_eq hEq
      have hr₂_root : f.IsRoot r₂ := isRoot_of_mem_sorted_roots_eq hrs_eq hEq_next
      have hgg_nonpos : g.eval r * g.eval r₂ ≤ 0 :=
        eval_mul_eval_nonpos_of_interlacing_consecutive hg hrs_sorted hss_eq hint hEq
      have hg_r_ne : g.eval r ≠ 0 := by
        intro hg0
        exact hno r hr_root (by simpa [Polynomial.IsRoot.def] using hg0)
      have hg_r₂_ne : g.eval r₂ ≠ 0 := by
        intro hg0
        exact hno r₂ hr₂_root (by simpa [Polynomial.IsRoot.def] using hg0)
      have hgg_neg : g.eval r * g.eval r₂ < 0 := by
        exact lt_of_le_of_ne hgg_nonpos (mul_ne_zero hg_r_ne hg_r₂_ne)
      constructor
      · intro heven
        have hodd_rest : Odd rest.length := by
          apply Nat.not_even_iff_odd.mp
          simpa [Nat.succ_eq_add_one] using (Nat.even_add_one.mp heven)
        have hg₂_neg : g.eval r₂ < 0 := hnext.2 hodd_rest
        nlinarith
      · intro hodd
        have heven_rest : Even rest.length := by
          apply Nat.not_odd_iff_even.mp
          simpa [Nat.succ_eq_add_one] using (Nat.odd_add_one.mp hodd)
        have hg₂_pos : 0 < g.eval r₂ := hnext.1 heven_rest
        nlinarith

private lemma mul_nonpos_of_mul_nonpos_of_mul_neg {a b c d : ℝ}
    (hab : a * b ≤ 0) (hcd : c * d ≤ 0) (hbd : b * d < 0) :
    a * c ≤ 0 := by
  have hb_ne : b ≠ 0 := by
    intro hb0
    simp [hb0] at hbd
  rcases lt_or_gt_of_ne hb_ne with hb | hb
  · have hd : 0 < d := by
      nlinarith
    have ha : 0 ≤ a := by
      nlinarith
    have hc : c ≤ 0 := by
      nlinarith
    nlinarith
  · have hd : d < 0 := by
      nlinarith
    have ha : a ≤ 0 := by
      nlinarith
    have hc : 0 ≤ c := by
      nlinarith
    nlinarith

private lemma isRoot_of_eq_max_countP_le_of_sign
    {_f g F : ℝ[X]} {rs ts : List ℝ} {off : ℕ}
    {pre : List ℝ} {r : ℝ} {rest : List ℝ}
    (hF : F ≠ 0 ∧ F.roots.card = F.natDegree) (hF_pos : HasPosLeadingCoeff F)
    (_hrs_eq : (↑rs : Multiset ℝ) = _f.roots)
    (hts_eq : (↑ts : Multiset ℝ) = F.roots)
    (hoff : ts.length = rs.length + off)
    (hroot_nonpos : F.eval r * g.eval r ≤ 0)
    (hgsign : (Even rest.length → 0 < g.eval r) ∧ (Odd rest.length → g.eval r < 0))
    (hEq : rs = pre ++ r :: rest)
    (hcount : ts.countP (· ≤ r) = pre.length + off + 1) :
    F.IsRoot r := by
  have hrs_len : rs.length = pre.length + rest.length + 1 := by
    rw [hEq]
    simp [Nat.add_assoc]
  have hcount_gt : ts.countP (r < ·) = rest.length := by
    have hsplit := countP_le_add_countP_gt_eq_length ts r
    rw [hcount, hoff, hrs_len] at hsplit
    lia
  rcases Nat.even_or_odd rest.length with heven | hodd
  · have hF_nonpos : F.eval r ≤ 0 := by
      have hg_pos' : 0 < g.eval r := hgsign.1 heven
      nlinarith [hroot_nonpos, hg_pos']
    exact isRoot_of_eval_nonpos_of_even_countP_gt hF hF_pos hts_eq hF_nonpos
      (by simpa [hcount_gt] using heven)
  · have hF_nonneg : 0 ≤ F.eval r := by
      have hg_neg' : g.eval r < 0 := hgsign.2 hodd
      nlinarith [hroot_nonpos, hg_neg']
    exact isRoot_of_eval_nonneg_of_odd_countP_gt hF hF_pos hts_eq hF_nonneg
      (by simpa [hcount_gt] using hodd)

private lemma countP_le_of_eq_max_isRoot
    {_f F : ℝ[X]} {rs ts : List ℝ} {off : ℕ}
    (hF : F ≠ 0 ∧ F.roots.card = F.natDegree)
    (_hrs_sorted : rs.Pairwise (· ≤ ·))
    (hts_eq : (↑ts : Multiset ℝ) = F.roots)
    (hoff : ts.length = rs.length + off)
    (hstrict :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        r₁ < r₂)
    (hroot_on_max :
      ∀ (pre : List ℝ) {r : ℝ} {rest : List ℝ},
        rs = pre ++ r :: rest →
        ts.countP (· ≤ r) = pre.length + off + 1 →
        F.IsRoot r) :
    ∀ (pre : List ℝ) {r : ℝ} {rest : List ℝ},
      rs = pre ++ r :: rest →
      ts.countP (· ≤ r) ≤ pre.length + off + 1 := by
  intro pre r rest hEq
  induction rest generalizing pre r with
  | nil =>
      have hcount_le :
          ts.countP (· ≤ r) ≤ ts.length :=
        List.countP_le_length (p := fun x => decide (x ≤ r)) (l := ts)
      have hrs_len : rs.length = pre.length + 1 := by
        rw [hEq]
        simp
      rw [hoff, hrs_len] at hcount_le
      lia
  | cons r₂ rest ih =>
      have hEq_next : rs = (pre ++ [r]) ++ r₂ :: rest := by
        simpa [List.append_assoc] using hEq
      have hnext : ts.countP (· ≤ r₂) ≤ pre.length + off + 2 := by
        have hnext' := ih (pre := pre ++ [r]) (r := r₂) hEq_next
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hnext'
      have hr_lt_r₂ : r < r₂ := hstrict pre hEq
      by_cases hsmall : ts.countP (· ≤ r₂) ≤ pre.length + off + 1
      · have hmono : ts.countP (· ≤ r) ≤ ts.countP (· ≤ r₂) := by
          exact List.countP_mono_left <| by
            intro x _ hx
            simp only [decide_eq_true_eq] at hx ⊢
            exact le_trans hx (le_of_lt hr_lt_r₂)
        exact le_trans hmono hsmall
      · have heq : ts.countP (· ≤ r₂) = pre.length + off + 2 := by
          lia
        have hr₂_root : F.IsRoot r₂ := by
          apply hroot_on_max (pre := pre ++ [r]) hEq_next
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using heq
        have hr₂_mem : r₂ ∈ ts := by
          apply Multiset.mem_coe.mp
          rw [hts_eq]
          exact (mem_roots hF.1).mpr hr₂_root
        have hlt : ts.countP (· ≤ r) < ts.countP (· ≤ r₂) := by
          apply countP_lt_countP_of_exists
          · intro x hx
            simp only [decide_eq_true_eq] at hx ⊢
            exact le_trans hx (le_of_lt hr_lt_r₂)
          · exact hr₂_mem
          · simp [not_le_of_gt hr_lt_r₂]
          · simp
        lia

private lemma countP_lt_of_eq_max_isRoot
    {_f F : ℝ[X]} {rs ts : List ℝ} {off : ℕ}
    (hF : F ≠ 0 ∧ F.roots.card = F.natDegree)
    (hts_eq : (↑ts : Multiset ℝ) = F.roots)
    (hcount_le :
      ∀ (pre : List ℝ) {r : ℝ} {rest : List ℝ},
        rs = pre ++ r :: rest →
        ts.countP (· ≤ r) ≤ pre.length + off + 1)
    (hroot_on_max :
      ∀ (pre : List ℝ) {r : ℝ} {rest : List ℝ},
        rs = pre ++ r :: rest →
        ts.countP (· ≤ r) = pre.length + off + 1 →
        F.IsRoot r) :
    ∀ (pre : List ℝ) {r : ℝ} {rest : List ℝ},
      rs = pre ++ r :: rest →
      ts.countP (· < r) ≤ pre.length + off := by
  intro pre r rest hEq
  have hle := hcount_le pre hEq
  by_cases hsmall : ts.countP (· ≤ r) ≤ pre.length + off
  · have hmono : ts.countP (· < r) ≤ ts.countP (· ≤ r) := by
      exact List.countP_mono_left <| by
        intro x _ hx
        simp only [decide_eq_true_eq] at hx ⊢
        exact le_of_lt hx
    exact le_trans hmono hsmall
  · have heq : ts.countP (· ≤ r) = pre.length + off + 1 := by
      lia
    have hr_root : F.IsRoot r := hroot_on_max pre hEq heq
    have hr_mem : r ∈ ts := by
      apply Multiset.mem_coe.mp
      rw [hts_eq]
      exact (mem_roots hF.1).mpr hr_root
    have hlt : ts.countP (· < r) < ts.countP (· ≤ r) := by
      apply countP_lt_countP_of_exists
      · intro x hx
        simp only [decide_eq_true_eq] at hx ⊢
        exact le_of_lt hx
      · exact hr_mem
      · simp
      · simp
    lia

private lemma mul_neg_of_mul_neg_of_mul_neg {a b c d : ℝ}
    (hab : a * b < 0) (hcd : c * d < 0) (hbd : b * d < 0) :
    a * c < 0 := by
  have hb_ne : b ≠ 0 := by
    intro hb0
    simp [hb0] at hab
  rcases lt_or_gt_of_ne hb_ne with hb | hb
  · have hd : 0 < d := by nlinarith
    have ha : 0 < a := by nlinarith
    have hc : c < 0 := by nlinarith
    nlinarith
  · have hd : d < 0 := by nlinarith
    have ha : a < 0 := by nlinarith
    have hc : 0 < c := by nlinarith
    nlinarith

/-- If `ss` interlaces a nonempty sorted list `rs`, then adjoining one extra
point `uR` to the right turns the tail of `rs` into a `ListInterlaces` witness
against `ss ++ [uR]`. -/
private lemma listInterlaces_of_interlacing_append_right :
    ∀ {ss rs : List ℝ},
      rs ≠ [] →
      ListInterlaces ss rs →
      ∀ {s uR : ℝ},
        s ≤ rs.head! →
        (∀ r ∈ rs, r ≤ uR) →
        ListInterlaces rs (s :: ss ++ [uR])
  | [], [], hrs_ne, hint, s, uR, hs, hR => by
      cases (hrs_ne rfl)
  | [], [r], _, hint, s, uR, hs, hR => by
      have hs' : s ≤ r := by simpa using hs
      simp [ListInterlaces, hs', hR r (by simp)]
  | [], _ :: _ :: _, _, hint, _, _, _, _ => by
      simp [ListInterlaces] at hint
  | s₂ :: ss, [], hrs_ne, hint, s, uR, hs, hR => by
      cases (hrs_ne rfl)
  | s₂ :: ss, [r], _, hint, _, _, _, _ => by
      simp [ListInterlaces] at hint
  | s₂ :: ss, r₁ :: r₂ :: rs, _, hint, s, uR, hs, hR => by
      obtain ⟨hr₁s₂, hs₂r₂, htail⟩ := hint
      have htail_bound : ∀ r ∈ r₂ :: rs, r ≤ uR := by
        intro r hr
        exact hR r (by simp [hr])
      have htail_inter : ListInterlaces (r₂ :: rs) (s₂ :: ss ++ [uR]) := by
        exact listInterlaces_of_interlacing_append_right (rs := r₂ :: rs) (by simp)
          htail hs₂r₂ htail_bound
      exact ⟨hs, hr₁s₂, htail_inter⟩

/-- Same-degree assembly: strict sign changes on consecutive roots of `f`
produce inner roots of `F`; if one additional root of `F` lies strictly to the
right of all roots of `f`, then `f ≺ F` in the same-degree sense. -/
theorem prec_same_of_strict_signs_of_right_root
    {f F : ℝ[X]} {rs : List ℝ}
    (hf : f ≠ 0 ∧ f.roots.card = f.natDegree) (hF_ne : F ≠ 0)
    (hrs_sorted : rs.Pairwise (· ≤ ·))
    (hrs_eq : (↑rs : Multiset ℝ) = f.roots)
    (hdeg : F.natDegree = f.natDegree)
    (hn : 1 ≤ rs.length)
    (hsign :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        F.eval r₁ * F.eval r₂ < 0)
    (hright : ∃ uR, F.IsRoot uR ∧ ∀ r ∈ rs, r < uR) :
    Prec f F := by
  obtain ⟨uR, huR_root, huR_lt⟩ := hright
  obtain ⟨us, hus_len, hus_int, hus_roots, hus_pw⟩ :=
    exists_roots_strictly_interlacing_of_consecutive_signs (F := F) hrs_sorted hsign
  have hrs_len : rs.length = f.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, hf.2]
  have hrs_ne : rs ≠ [] := by
    intro h
    simp [h] at hn
  obtain ⟨r, rs', rfl⟩ : ∃ r rs', rs = r :: rs' := by
    cases rs with
    | nil => cases (hrs_ne rfl)
    | cons r rs' => exact ⟨r, rs', rfl⟩
  have hall_us_lt_uR : ∀ u ∈ us, u < uR :=
    listInterlaces_all_lt_of_upperBound hus_int huR_lt
  have hws_pw : (us ++ [uR]).Pairwise (· < ·) := by
    rw [List.pairwise_append]
    refine ⟨hus_pw, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    exact hall_us_lt_uR a ha
  have hws_sub : (↑(us ++ [uR]) : Multiset ℝ) ≤ F.roots := by
    rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr (hws_pw.imp ne_of_lt))]
    intro x hx
    rcases List.mem_append.mp (Multiset.mem_coe.mp hx) with hx_us | hx_uR
    · exact (mem_roots hF_ne).mpr (hus_roots x hx_us)
    · simp only [List.mem_singleton] at hx_uR
      subst hx_uR
      exact (mem_roots hF_ne).mpr huR_root
  have hws_len : (us ++ [uR]).length = F.natDegree := by
    calc
      (us ++ [uR]).length = us.length + 1 := by simp
      _ = (r :: rs').length := by rw [hus_len]; lia
      _ = f.natDegree := by rw [hrs_len]
      _ = F.natDegree := hdeg.symm
  have hws_eq : (↑(us ++ [uR]) : Multiset ℝ) = F.roots :=
    Multiset.eq_of_le_of_card_le hws_sub (by
      calc
        F.roots.card ≤ F.natDegree := card_roots' F
        _ = (us ++ [uR]).length := hws_len.symm
        _ = (↑(us ++ [uR]) : Multiset ℝ).card := (Multiset.coe_card _).symm)
  have hF : (F ≠ 0 ∧ F.roots.card = F.natDegree) := by
    refine ⟨hF_ne, ?_⟩
    rw [← hws_eq, Multiset.coe_card, hws_len]
  have hws_sorted : (us ++ [uR]).Pairwise (· ≤ ·) := hws_pw.imp le_of_lt
  have hshape : ListAlternates (r :: rs') (us ++ [uR]) := by
    cases us with
    | nil =>
        have hrs_single : rs' = [] := by
          cases rs' with
          | nil => rfl
          | cons a as =>
              simp at hus_len
        subst rs'
        simp [ListAlternates, ListInterlaces, le_of_lt (huR_lt r (by simp))]
    | cons s ss =>
        have hint' : ListInterlaces (s :: ss) (r :: rs') := by simpa using hus_int
        cases rs' with
        | nil =>
            simp [ListInterlaces] at hint'
        | cons r₂ rest =>
            obtain ⟨hrs, hs_r₂, htail⟩ := hint'
            have htail_bound : ∀ x ∈ r₂ :: rest, x ≤ uR := by
              intro x hx
              exact le_of_lt (huR_lt x (by simp [hx]))
            exact ⟨hrs, listInterlaces_of_interlacing_append_right (rs := r₂ :: rest) (by simp)
              htail hs_r₂ htail_bound⟩
  have hlen_shape : (r :: rs').length = (us ++ [uR]).length := by
    calc
      (r :: rs').length = f.natDegree := by rw [hrs_len]
      _ = F.natDegree := hdeg.symm
      _ = (us ++ [uR]).length := hws_len.symm
  exact ⟨hf, hF, r :: rs', us ++ [uR], hrs_sorted, hws_sorted, hrs_eq, hws_eq,
    Or.inr ⟨hlen_shape, hshape⟩⟩

/-- Add one outer point on each side of a sorted interlacing layout. -/
private lemma listInterlaces_with_outer :
    ∀ {us rs : List ℝ},
      rs ≠ [] →
      rs.Pairwise (· ≤ ·) →
      ListInterlaces us rs →
      ∀ {uL uR : ℝ},
        (∀ r ∈ rs, uL ≤ r) →
        (∀ r ∈ rs, r ≤ uR) →
        ListInterlaces rs (uL :: us ++ [uR])
  | [], [], hrs_ne, _, _, _, _, _, _ => by
      cases (hrs_ne rfl)
  | [], [r], _, _, _, _, _, hL, hR => by
      simp [ListInterlaces, hL r (by simp), hR r (by simp)]
  | [], _ :: _ :: _, _, _, hint, _, _, _, _ => by
      simp [ListInterlaces] at hint
  | _ :: _, [], hrs_ne, _, _, _, _, _, _ => by
      cases (hrs_ne rfl)
  | _ :: _, [_], _, _, hint, _, _, _, _ => by
      simp [ListInterlaces] at hint
  | s :: ss, r₁ :: r₂ :: rs, _, hrs, hint, uL, uR, hL, hR => by
      obtain ⟨hr₁s, hsr₂, htail⟩ := hint
      have hrs_tail : (r₂ :: rs).Pairwise (· ≤ ·) := (List.pairwise_cons.mp hrs).2
      have hrs_tail_ne : (r₂ :: rs) ≠ [] := by simp
      have hL_tail : ∀ r ∈ r₂ :: rs, s ≤ r := by
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hr'
        · exact hsr₂
        · exact le_trans hsr₂ (List.Pairwise.rel_head hrs_tail (List.mem_cons_of_mem _ hr'))
      have hR_tail : ∀ r ∈ r₂ :: rs, r ≤ uR := by
        intro r hr
        exact hR r (by simp [hr])
      simp only [List.cons_append, ListInterlaces, hL r₁ (by simp), hr₁s, true_and]
      exact listInterlaces_with_outer hrs_tail_ne hrs_tail htail hL_tail hR_tail

/-- Assemble a differ-by-1 `Prec` statement from strict sign changes on a sorted
root list together with one strict outer root on each side. -/
theorem prec_of_strict_signs_of_strict_outer_roots
    {f F : ℝ[X]} {rs : List ℝ}
    (hf : f ≠ 0 ∧ f.roots.card = f.natDegree) (hF_ne : F ≠ 0)
    (hrs_sorted : rs.Pairwise (· ≤ ·))
    (hrs_eq : (↑rs : Multiset ℝ) = f.roots)
    (hdeg : F.natDegree = f.natDegree + 1)
    (hn : 1 ≤ rs.length)
    (hsign :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        F.eval r₁ * F.eval r₂ < 0)
    (hleft : ∃ uL, F.IsRoot uL ∧ ∀ r ∈ rs, uL < r)
    (hright : ∃ uR, F.IsRoot uR ∧ ∀ r ∈ rs, r < uR) :
    Prec f F := by
  obtain ⟨uL, huL_root, huL_lt⟩ := hleft
  obtain ⟨uR, huR_root, huR_lt⟩ := hright
  obtain ⟨us, hus_len, hus_int, hus_roots, hus_pw⟩ :=
    exists_roots_strictly_interlacing_of_consecutive_signs (F := F) hrs_sorted hsign
  have hrs_len : rs.length = f.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, hf.2]
  have hrs_ne : rs ≠ [] := by
    intro h
    simp [h] at hn
  obtain ⟨r, rs', rfl⟩ : ∃ r rs', rs = r :: rs' := by
    cases rs with
    | nil => cases (hrs_ne rfl)
    | cons r rs' => exact ⟨r, rs', rfl⟩
  have hr_mem : r ∈ r :: rs' := by simp
  have huL_lt_uR : uL < uR := lt_trans (huL_lt r hr_mem) (huR_lt r hr_mem)
  have huL_lt_all_us : ∀ u ∈ us, uL < u :=
    listInterlaces_all_gt_of_lowerBound hus_int huL_lt
  have hall_us_lt_uR : ∀ u ∈ us, u < uR :=
    listInterlaces_all_lt_of_upperBound hus_int huR_lt
  have husuR_pw : (us ++ [uR]).Pairwise (· < ·) := by
    rw [List.pairwise_append]
    refine ⟨hus_pw, List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    exact hall_us_lt_uR a ha
  have hws_pw : (uL :: us ++ [uR]).Pairwise (· < ·) := by
    refine List.pairwise_cons.mpr ⟨?_, husuR_pw⟩
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact huL_lt_all_us x hx
    · simp only [List.mem_singleton] at hx
      subst hx
      exact huL_lt_uR
  have hws_sub : (↑(uL :: us ++ [uR]) : Multiset ℝ) ≤ F.roots := by
    rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr (hws_pw.imp ne_of_lt))]
    intro x hx
    rcases List.mem_cons.mp (Multiset.mem_coe.mp hx) with rfl | hx'
    · exact (mem_roots hF_ne).mpr huL_root
    rcases List.mem_append.mp hx' with hx_us | hx_uR
    · exact (mem_roots hF_ne).mpr (hus_roots x hx_us)
    · simp only [List.mem_singleton] at hx_uR
      subst hx_uR
      exact (mem_roots hF_ne).mpr huR_root
  have hws_len : (uL :: us ++ [uR]).length = F.natDegree := by
    calc
      (uL :: us ++ [uR]).length = us.length + 2 := by simp
      _ = (r :: rs').length + 1 := by rw [hus_len]; lia
      _ = f.natDegree + 1 := by rw [hrs_len]
      _ = F.natDegree := hdeg.symm
  have hws_eq : (↑(uL :: us ++ [uR]) : Multiset ℝ) = F.roots :=
    Multiset.eq_of_le_of_card_le hws_sub (by
      calc
        F.roots.card ≤ F.natDegree := card_roots' F
        _ = (uL :: us ++ [uR]).length := hws_len.symm
        _ = (↑(uL :: us ++ [uR]) : Multiset ℝ).card := (Multiset.coe_card _).symm)
  have hF : (F ≠ 0 ∧ F.roots.card = F.natDegree) := by
    refine ⟨hF_ne, ?_⟩
    rw [← hws_eq, Multiset.coe_card, hws_len]
  have hws_sorted : (uL :: us ++ [uR]).Pairwise (· ≤ ·) := hws_pw.imp le_of_lt
  have hshape : ListInterlaces (r :: rs') (uL :: us ++ [uR]) := by
    exact listInterlaces_with_outer hrs_ne hrs_sorted hus_int
      (fun r hr => le_of_lt (huL_lt r hr))
      (fun r hr => le_of_lt (huR_lt r hr))
  have hlen_shape : (r :: rs').length + 1 = (uL :: us ++ [uR]).length := by
    calc
      (r :: rs').length + 1 = f.natDegree + 1 := by rw [hrs_len]
      _ = F.natDegree := hdeg.symm
      _ = (uL :: us ++ [uR]).length := hws_len.symm
  exact ⟨hf, hF, r :: rs', uL :: us ++ [uR], hrs_sorted, hws_sorted, hrs_eq, hws_eq,
    Or.inl ⟨hlen_shape, hshape⟩⟩

/-- Right-hand IVT bridge: if a polynomial is nonpositive at `r` and tends to
`+∞` at `+∞`, then it has a real root to the right of `r`. -/
lemma exists_isRoot_ge_of_eval_nonpos_of_tendsto_atTop_atTop {p : ℝ[X]} {r : ℝ}
    (hr : p.eval r ≤ 0) (ht : Tendsto (fun x => p.eval x) atTop atTop) :
    ∃ u ≥ r, p.IsRoot u := by
  rcases eq_or_lt_of_le hr with hzero | hneg
  · exact ⟨r, le_rfl, by simpa [Polynomial.IsRoot.def] using hzero⟩
  · have hpos : ∀ᶠ x in atTop, 0 < p.eval x :=
      ht.eventually (Ioi_mem_atTop 0)
    have hgt : ∀ᶠ x : ℝ in atTop, r < x := eventually_gt_atTop r
    obtain ⟨x, hx_gt_r, hx_pos⟩ := (hgt.and hpos).exists
    have h0 : (0 : ℝ) ∈ Set.Icc (p.eval r) (p.eval x) := ⟨hr, le_of_lt hx_pos⟩
    obtain ⟨u, hu, hu_root⟩ :=
      intermediate_value_Icc (le_of_lt hx_gt_r) p.continuous.continuousOn h0
    exact ⟨u, hu.1, hu_root⟩

/-- Left-hand wrapper for the `atBot → +∞` case with a nonpositive value at the
basepoint. -/
lemma exists_isRoot_le_of_eval_nonpos_of_tendsto_atBot_atTop {p : ℝ[X]} {r : ℝ}
    (hr : p.eval r ≤ 0) (ht : Tendsto (fun x => p.eval x) atBot atTop) :
    ∃ u ≤ r, p.IsRoot u := by
  rcases eq_or_lt_of_le hr with hzero | hneg
  · exact ⟨r, le_rfl, by simpa [Polynomial.IsRoot.def] using hzero⟩
  · exact exists_isRoot_le_of_eval_neg_of_tendsto_atBot_atTop hneg ht

/-- Left-hand wrapper for the `atBot → -∞` case with a nonnegative value at the
basepoint. -/
lemma exists_isRoot_le_of_eval_nonneg_of_tendsto_atBot_atBot {p : ℝ[X]} {r : ℝ}
    (hr : 0 ≤ p.eval r) (ht : Tendsto (fun x => p.eval x) atBot atBot) :
    ∃ u ≤ r, p.IsRoot u := by
  rcases eq_or_lt_of_le hr with hzero | hpos
  · exact ⟨r, le_rfl, by simpa [eq_comm, Polynomial.IsRoot.def] using hzero⟩
  · exact exists_isRoot_le_of_eval_pos_of_tendsto_atBot_atBot hpos ht

/-- Even-left endpoint version of
`prec_of_strict_signs_of_strict_outer_roots`: if `f` has even degree, `F` has
positive leading coefficient and degree `deg(f)+1`, strictly alternates sign on
consecutive `f`-roots, is positive at the leftmost `f`-root, and negative at
the rightmost `f`-root, then `f ⊳ F`. -/
theorem prec_of_strict_signs_of_endSigns_even
    {f F : ℝ[X]} {rs : List ℝ}
    (hf : f ≠ 0 ∧ f.roots.card = f.natDegree)
    (hF_pos : HasPosLeadingCoeff F)
    (hrs_sorted : rs.Pairwise (· ≤ ·))
    (hrs_eq : (↑rs : Multiset ℝ) = f.roots)
    (hdeg : F.natDegree = f.natDegree + 1)
    (hn : 1 ≤ rs.length)
    (hpar : Even f.natDegree)
    (hsign :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        F.eval r₁ * F.eval r₂ < 0)
    (hleft_sign : 0 < F.eval rs.head!)
    (hright_sign : F.eval (rs.getLast (by
      intro hrs_nil
      simp [hrs_nil] at hn)) < 0) :
    Prec f F := by
  have hF_ne : F ≠ 0 := by
    intro h0
    simp [HasPosLeadingCoeff, h0] at hF_pos
  have hrs_ne : rs ≠ [] := by
    intro hrs_nil
    simp [hrs_nil] at hn
  have hF_natdeg_pos : 0 < F.natDegree := by
    rw [hdeg]
    lia
  have hF_deg_pos : 0 < F.degree := natDegree_pos_iff_degree_pos.mp hF_natdeg_pos
  have hF_odd : Odd F.natDegree := by
    rcases hpar with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [hdeg, hk]
    ring
  have hleft :
      ∃ uL, F.IsRoot uL ∧ ∀ r ∈ rs, uL < r := by
    have ht : Tendsto (fun x => F.eval x) atBot atBot :=
      tendsto_eval_atBot_atBot_of_posLeadingCoeff_odd hF_pos hF_deg_pos hF_odd
    obtain ⟨uL, huL_le, huL_root⟩ :=
      exists_isRoot_le_of_eval_pos_of_tendsto_atBot_atBot hleft_sign ht
    have huL_lt_head : uL < rs.head! := by
      refine lt_of_le_of_ne huL_le ?_
      intro hEq
      have : F.eval rs.head! = 0 := by simpa [Polynomial.IsRoot.def, hEq] using huL_root
      exact (ne_of_gt hleft_sign) this
    refine ⟨uL, huL_root, ?_⟩
    intro r hr
    exact lt_of_lt_of_le huL_lt_head (hrs_sorted.head!_le hr)
  have hright :
      ∃ uR, F.IsRoot uR ∧ ∀ r ∈ rs, r < uR := by
    have ht : Tendsto (fun x => F.eval x) atTop atTop :=
      F.tendsto_atTop_of_leadingCoeff_nonneg hF_deg_pos hF_pos.le
    obtain ⟨uR, huR_ge, huR_root⟩ :=
      exists_isRoot_ge_of_eval_nonpos_of_tendsto_atTop_atTop (le_of_lt hright_sign) ht
    have hlast_lt_uR : rs.getLast hrs_ne < uR := by
      refine lt_of_le_of_ne huR_ge ?_
      intro hEq
      have : F.eval (rs.getLast hrs_ne) = 0 := by simpa [Polynomial.IsRoot.def, hEq] using huR_root
      exact (ne_of_lt hright_sign) this
    refine ⟨uR, huR_root, ?_⟩
    intro r hr
    exact lt_of_le_of_lt (hrs_sorted.rel_getLast hr) hlast_lt_uR
  exact prec_of_strict_signs_of_strict_outer_roots hf hF_ne hrs_sorted hrs_eq hdeg hn
    hsign hleft hright

/-- Odd-left endpoint version of
`prec_of_strict_signs_of_strict_outer_roots`: if `f` has odd degree, `F` has
positive leading coefficient and degree `deg(f)+1`, strictly alternates sign on
consecutive `f`-roots, and is negative at both extreme `f`-roots, then
`f ⊳ F`. -/
theorem prec_of_strict_signs_of_endSigns_odd
    {f F : ℝ[X]} {rs : List ℝ}
    (hf : f ≠ 0 ∧ f.roots.card = f.natDegree)
    (hF_pos : HasPosLeadingCoeff F)
    (hrs_sorted : rs.Pairwise (· ≤ ·))
    (hrs_eq : (↑rs : Multiset ℝ) = f.roots)
    (hdeg : F.natDegree = f.natDegree + 1)
    (hn : 1 ≤ rs.length)
    (hpar : Odd f.natDegree)
    (hsign :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        F.eval r₁ * F.eval r₂ < 0)
    (hleft_sign : F.eval rs.head! < 0)
    (hright_sign : F.eval (rs.getLast (by
      intro hrs_nil
      simp [hrs_nil] at hn)) < 0) :
    Prec f F := by
  have hF_ne : F ≠ 0 := by
    intro h0
    simp [HasPosLeadingCoeff, h0] at hF_pos
  have hrs_ne : rs ≠ [] := by
    intro hrs_nil
    simp [hrs_nil] at hn
  have hF_natdeg_pos : 0 < F.natDegree := by
    rw [hdeg]
    lia
  have hF_deg_pos : 0 < F.degree := natDegree_pos_iff_degree_pos.mp hF_natdeg_pos
  have hF_even : Even F.natDegree := by
    rcases hpar with ⟨k, hk⟩
    refine ⟨k + 1, ?_⟩
    rw [hdeg, hk]
    ring
  have hleft :
      ∃ uL, F.IsRoot uL ∧ ∀ r ∈ rs, uL < r := by
    have ht : Tendsto (fun x => F.eval x) atBot atTop :=
      tendsto_eval_atBot_atTop_of_posLeadingCoeff_even hF_pos hF_deg_pos hF_even
    obtain ⟨uL, huL_le, huL_root⟩ :=
      exists_isRoot_le_of_eval_neg_of_tendsto_atBot_atTop hleft_sign ht
    have huL_lt_head : uL < rs.head! := by
      refine lt_of_le_of_ne huL_le ?_
      intro hEq
      have : F.eval rs.head! = 0 := by simpa [Polynomial.IsRoot.def, hEq] using huL_root
      exact (ne_of_lt hleft_sign) this
    refine ⟨uL, huL_root, ?_⟩
    intro r hr
    exact lt_of_lt_of_le huL_lt_head (hrs_sorted.head!_le hr)
  have hright :
      ∃ uR, F.IsRoot uR ∧ ∀ r ∈ rs, r < uR := by
    have ht : Tendsto (fun x => F.eval x) atTop atTop :=
      F.tendsto_atTop_of_leadingCoeff_nonneg hF_deg_pos hF_pos.le
    obtain ⟨uR, huR_ge, huR_root⟩ :=
      exists_isRoot_ge_of_eval_nonpos_of_tendsto_atTop_atTop (le_of_lt hright_sign) ht
    have hlast_lt_uR : rs.getLast hrs_ne < uR := by
      refine lt_of_le_of_ne huR_ge ?_
      intro hEq
      have : F.eval (rs.getLast hrs_ne) = 0 := by simpa [Polynomial.IsRoot.def, hEq] using huR_root
      exact (ne_of_lt hright_sign) this
    refine ⟨uR, huR_root, ?_⟩
    intro r hr
    exact lt_of_le_of_lt (hrs_sorted.rel_getLast hr) hlast_lt_uR
  exact prec_of_strict_signs_of_strict_outer_roots hf hF_ne hrs_sorted hrs_eq hdeg hn
    hsign hleft hright

/-- Liu--Wang differ-by-1 form: if `g ⊳ f`, `F` has degree `deg(f)+1`, positive
leading coefficient, and at every root `r` of `f` the value `F(r)` has the
opposite sign from `g(r)`, then `f ⊳ F`. -/
theorem prec_of_interlaces_eval_mul_neg_succ {f g F : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff F)
    (hdeg : F.natDegree = f.natDegree + 1)
    (hroot_sign : ∀ r, f.IsRoot r → F.eval r * g.eval r < 0) :
    Prec f F := by
  obtain ⟨hf, hg, hgdeg, rs, ss, hrs_sorted, hss_sorted, hrs_eq, hss_eq, hint⟩ := hgf
  have hrs_len : rs.length = f.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, hf.2]
  have hn : 1 ≤ rs.length := by
    rw [hrs_len]
    lia
  have hrs_ne : rs ≠ [] := by
    intro hrs_nil
    simp [hrs_nil] at hn
  obtain ⟨r₀, rs', rfl⟩ : ∃ r₀ rs', rs = r₀ :: rs' := by
    cases rs with
    | nil => cases (hrs_ne rfl)
    | cons r₀ rs' => exact ⟨r₀, rs', rfl⟩
  have hr₀_root : f.IsRoot r₀ := by
    apply (mem_roots hf.1).mp
    rw [← hrs_eq]
    exact Multiset.mem_coe.mpr (by simp)
  have hlast_root : f.IsRoot ((r₀ :: rs').getLast (by simp)) := by
    apply (mem_roots hf.1).mp
    rw [← hrs_eq]
    exact Multiset.mem_coe.mpr (List.getLast_mem (by simp))
  have hno_g_at_f : ∀ r, f.IsRoot r → ¬ g.IsRoot r := by
    intro r hr hgr
    have hprod := hroot_sign r hr
    have hg0 : g.eval r = 0 := by simpa [Polynomial.IsRoot.def] using hgr
    have : F.eval r * g.eval r = 0 := by simp [hg0]
    nlinarith [hprod, this]
  have hhead_lt_roots_g : ∀ t ∈ g.roots, r₀ < t := by
    intro t ht
    have ht_ss : t ∈ ss := by
      apply Multiset.mem_coe.mp
      rw [hss_eq]
      exact ht
    have hr₀_le_t : r₀ ≤ t := listInterlaces_all_ge ss rs' r₀ hint t ht_ss
    have ht_root : g.IsRoot t := (mem_roots hg.1).mp ht
    by_contra hnot
    have ht_le_r₀ : t ≤ r₀ := le_of_not_gt hnot
    have hEq : t = r₀ := le_antisymm ht_le_r₀ hr₀_le_t
    exact hno_g_at_f r₀ hr₀_root (by simpa [hEq] using ht_root)
  have hroots_g_lt_last : ∀ t ∈ g.roots, t < (r₀ :: rs').getLast (by simp) := by
    intro t ht
    have ht_ss : t ∈ ss := by
      apply Multiset.mem_coe.mp
      rw [hss_eq]
      exact ht
    have ht_le_last : t ≤ (r₀ :: rs').getLast (by simp) :=
      listInterlaces_all_le_getLast (rs := r₀ :: rs') (by simp) hrs_sorted hint t ht_ss
    have ht_root : g.IsRoot t := (mem_roots hg.1).mp ht
    by_contra hnot
    have hlast_le_t : (r₀ :: rs').getLast (by simp) ≤ t := not_lt.mp hnot
    have hEq : t = (r₀ :: rs').getLast (by simp) := le_antisymm ht_le_last hlast_le_t
    exact hno_g_at_f ((r₀ :: rs').getLast (by simp)) hlast_root (by simpa [hEq] using ht_root)
  have hsign :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        (r₀ :: rs') = pre ++ r₁ :: r₂ :: rest →
        F.eval r₁ * F.eval r₂ < 0 := by
    intro pre r₁ r₂ rest hEq
    have hr₁_root : f.IsRoot r₁ := by
      apply (mem_roots hf.1).mp
      rw [← hrs_eq]
      exact Multiset.mem_coe.mpr (by rw [hEq]; simp)
    have hr₂_root : f.IsRoot r₂ := by
      apply (mem_roots hf.1).mp
      rw [← hrs_eq]
      exact Multiset.mem_coe.mpr (by rw [hEq]; simp)
    have hFg₁ : F.eval r₁ * g.eval r₁ < 0 := hroot_sign r₁ hr₁_root
    have hFg₂ : F.eval r₂ * g.eval r₂ < 0 := hroot_sign r₂ hr₂_root
    have hgg_nonpos : g.eval r₁ * g.eval r₂ ≤ 0 :=
      eval_mul_eval_nonpos_of_interlacing_consecutive hg hrs_sorted hss_eq hint hEq
    have hg₁_ne : g.eval r₁ ≠ 0 := by
      intro hg₁
      have : F.eval r₁ * g.eval r₁ = 0 := by simp [hg₁]
      nlinarith [hFg₁, this]
    have hg₂_ne : g.eval r₂ ≠ 0 := by
      intro hg₂
      have : F.eval r₂ * g.eval r₂ = 0 := by simp [hg₂]
      nlinarith [hFg₂, this]
    have hgg_neg : g.eval r₁ * g.eval r₂ < 0 := by
      exact lt_of_le_of_ne hgg_nonpos (mul_ne_zero hg₁_ne hg₂_ne)
    exact mul_neg_of_mul_neg_of_mul_neg hFg₁ hFg₂ hgg_neg
  rcases Nat.even_or_odd f.natDegree with hf_even | hf_odd
  · have hg_odd : Odd g.natDegree := by
      rcases hf_even with ⟨k, hk⟩
      have hk_pos : 0 < k := by
        have : 0 < f.natDegree := by lia
        lia
      refine ⟨k - 1, ?_⟩
      lia
    have hg_left_neg : g.eval r₀ < 0 :=
      eval_neg_of_all_roots_gt_of_odd hg hg_pos hg_odd hhead_lt_roots_g
    have hF_left_pos : 0 < F.eval r₀ := by
      have hprod := hroot_sign r₀ hr₀_root
      nlinarith
    have hg_right_pos : 0 < g.eval ((r₀ :: rs').getLast (by simp)) :=
      eval_pos_of_all_roots_lt hg hg_pos hroots_g_lt_last
    have hF_right_neg : F.eval ((r₀ :: rs').getLast (by simp)) < 0 := by
      have hprod := hroot_sign ((r₀ :: rs').getLast (by simp)) hlast_root
      nlinarith
    exact prec_of_strict_signs_of_endSigns_even hf hF_pos hrs_sorted hrs_eq hdeg hn hf_even
      hsign hF_left_pos hF_right_neg
  · have hg_even : Even g.natDegree := by
      rcases hf_odd with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      lia
    have hg_left_pos : 0 < g.eval r₀ :=
      eval_pos_of_all_roots_gt_of_even hg hg_pos hg_even hhead_lt_roots_g
    have hF_left_neg : F.eval r₀ < 0 := by
      have hprod := hroot_sign r₀ hr₀_root
      nlinarith
    have hg_right_pos : 0 < g.eval ((r₀ :: rs').getLast (by simp)) :=
      eval_pos_of_all_roots_lt hg hg_pos hroots_g_lt_last
    have hF_right_neg : F.eval ((r₀ :: rs').getLast (by simp)) < 0 := by
      have hprod := hroot_sign ((r₀ :: rs').getLast (by simp)) hlast_root
      nlinarith
    exact prec_of_strict_signs_of_endSigns_odd hf hF_pos hrs_sorted hrs_eq hdeg hn hf_odd
      hsign hF_left_neg hF_right_neg

/-- Liu--Wang same-degree form: if `g ⊳ f`, `F` has the same degree as `f`,
positive leading coefficient, and at every root `r` of `f` the value `F(r)`
has the opposite sign from `g(r)`, then `f ≺ F` in the same-degree sense. -/
theorem prec_of_interlaces_eval_mul_neg_same {f g F : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff F)
    (hdeg : F.natDegree = f.natDegree)
    (hroot_sign : ∀ r, f.IsRoot r → F.eval r * g.eval r < 0) :
    Prec f F := by
  obtain ⟨hf, hg, hgdeg, rs, ss, hrs_sorted, hss_sorted, hrs_eq, hss_eq, hint⟩ := hgf
  have hrs_len : rs.length = f.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, hf.2]
  have hn : 1 ≤ rs.length := by
    rw [hrs_len]
    lia
  have hrs_ne : rs ≠ [] := by
    intro hrs_nil
    simp [hrs_nil] at hn
  obtain ⟨r₀, rs', rfl⟩ : ∃ r₀ rs', rs = r₀ :: rs' := by
    cases rs with
    | nil => cases (hrs_ne rfl)
    | cons r₀ rs' => exact ⟨r₀, rs', rfl⟩
  have hlast_root : f.IsRoot ((r₀ :: rs').getLast (by simp)) := by
    apply (mem_roots hf.1).mp
    rw [← hrs_eq]
    exact Multiset.mem_coe.mpr (List.getLast_mem (by simp))
  have hno_g_at_f : ∀ r, f.IsRoot r → ¬ g.IsRoot r := by
    intro r hr hgr
    have hprod := hroot_sign r hr
    have hg0 : g.eval r = 0 := by simpa [Polynomial.IsRoot.def] using hgr
    have : F.eval r * g.eval r = 0 := by simp [hg0]
    nlinarith [hprod, this]
  have hroots_g_lt_last : ∀ t ∈ g.roots, t < (r₀ :: rs').getLast (by simp) := by
    intro t ht
    have ht_ss : t ∈ ss := by
      apply Multiset.mem_coe.mp
      rw [hss_eq]
      exact ht
    have ht_le_last : t ≤ (r₀ :: rs').getLast (by simp) :=
      listInterlaces_all_le_getLast (rs := r₀ :: rs') (by simp) hrs_sorted hint t ht_ss
    have ht_root : g.IsRoot t := (mem_roots hg.1).mp ht
    by_contra hnot
    have hlast_le_t : (r₀ :: rs').getLast (by simp) ≤ t := not_lt.mp hnot
    have hEq : t = (r₀ :: rs').getLast (by simp) := le_antisymm ht_le_last hlast_le_t
    exact hno_g_at_f ((r₀ :: rs').getLast (by simp)) hlast_root (by simpa [hEq] using ht_root)
  have hsign :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        (r₀ :: rs') = pre ++ r₁ :: r₂ :: rest →
        F.eval r₁ * F.eval r₂ < 0 := by
    intro pre r₁ r₂ rest hEq
    have hr₁_root : f.IsRoot r₁ := by
      apply (mem_roots hf.1).mp
      rw [← hrs_eq]
      exact Multiset.mem_coe.mpr (by rw [hEq]; simp)
    have hr₂_root : f.IsRoot r₂ := by
      apply (mem_roots hf.1).mp
      rw [← hrs_eq]
      exact Multiset.mem_coe.mpr (by rw [hEq]; simp)
    have hFg₁ : F.eval r₁ * g.eval r₁ < 0 := hroot_sign r₁ hr₁_root
    have hFg₂ : F.eval r₂ * g.eval r₂ < 0 := hroot_sign r₂ hr₂_root
    have hgg_nonpos : g.eval r₁ * g.eval r₂ ≤ 0 :=
      eval_mul_eval_nonpos_of_interlacing_consecutive hg hrs_sorted hss_eq hint hEq
    have hg₁_ne : g.eval r₁ ≠ 0 := by
      intro hg₁
      have : F.eval r₁ * g.eval r₁ = 0 := by simp [hg₁]
      nlinarith [hFg₁, this]
    have hg₂_ne : g.eval r₂ ≠ 0 := by
      intro hg₂
      have : F.eval r₂ * g.eval r₂ = 0 := by simp [hg₂]
      nlinarith [hFg₂, this]
    have hgg_neg : g.eval r₁ * g.eval r₂ < 0 := by
      exact lt_of_le_of_ne hgg_nonpos (mul_ne_zero hg₁_ne hg₂_ne)
    exact mul_neg_of_mul_neg_of_mul_neg hFg₁ hFg₂ hgg_neg
  have hg_right_pos : 0 < g.eval ((r₀ :: rs').getLast (by simp)) :=
    eval_pos_of_all_roots_lt hg hg_pos hroots_g_lt_last
  have hF_right_neg : F.eval ((r₀ :: rs').getLast (by simp)) < 0 := by
    have hprod := hroot_sign ((r₀ :: rs').getLast (by simp)) hlast_root
    nlinarith
  have hF_ne : F ≠ 0 := by
    intro h0
    simp [HasPosLeadingCoeff, h0] at hF_pos
  have hF_natdeg_pos : 0 < F.natDegree := by
    rw [hdeg]
    lia
  have hF_deg_pos : 0 < F.degree := natDegree_pos_iff_degree_pos.mp hF_natdeg_pos
  have hright :
      ∃ uR, F.IsRoot uR ∧ ∀ r ∈ (r₀ :: rs'), r < uR := by
    have ht : Tendsto (fun x => F.eval x) atTop atTop :=
      F.tendsto_atTop_of_leadingCoeff_nonneg hF_deg_pos hF_pos.le
    obtain ⟨uR, huR_ge, huR_root⟩ :=
      exists_isRoot_ge_of_eval_nonpos_of_tendsto_atTop_atTop (le_of_lt hF_right_neg) ht
    have hlast_lt_uR : (r₀ :: rs').getLast hrs_ne < uR := by
      refine lt_of_le_of_ne huR_ge ?_
      intro hEq
      have : F.eval ((r₀ :: rs').getLast hrs_ne) = 0 := by
        simpa [Polynomial.IsRoot.def, hEq] using huR_root
      exact (ne_of_lt hF_right_neg) this
    refine ⟨uR, huR_root, ?_⟩
    intro r hr
    exact lt_of_le_of_lt (hrs_sorted.rel_getLast hr) hlast_lt_uR
  exact prec_same_of_strict_signs_of_right_root hf hF_ne hrs_sorted hrs_eq hdeg hn hsign hright

private lemma eval_mul_derivative_eq_of_isRoot {f u v : ℝ[X]} {r : ℝ}
    (hr : f.IsRoot r) :
    (u * f + v * f.derivative).eval r * f.derivative.eval r =
      v.eval r * (f.derivative.eval r) ^ 2 := by
  have hf0 : f.eval r = 0 := by
    simpa [Polynomial.IsRoot.def] using hr
  calc
    (u * f + v * f.derivative).eval r * f.derivative.eval r
      = ((u.eval r * f.eval r) + v.eval r * f.derivative.eval r) * f.derivative.eval r := by
          simp [eval_add, eval_mul]
    _ = (v.eval r * f.derivative.eval r) * f.derivative.eval r := by simp [hf0]
    _ = v.eval r * (f.derivative.eval r) ^ 2 := by ring

private lemma eval_mul_right_eq_of_isRoot {f g a b : ℝ[X]} {r : ℝ}
    (hr : f.IsRoot r) :
    (a * f + b * g).eval r * g.eval r =
      b.eval r * (g.eval r) ^ 2 := by
  have hf0 : f.eval r = 0 := by
    simpa [Polynomial.IsRoot.def] using hr
  calc
    (a * f + b * g).eval r * g.eval r
      = ((a.eval r * f.eval r) + b.eval r * g.eval r) * g.eval r := by
          simp [eval_add, eval_mul]
    _ = (b.eval r * g.eval r) * g.eval r := by simp [hf0]
    _ = b.eval r * (g.eval r) ^ 2 := by ring

private lemma eval_mul_right_nonpos_of_isRoot {f g a b : ℝ[X]} {r : ℝ}
    (hr : f.IsRoot r) (hb : b.eval r ≤ 0) :
    (a * f + b * g).eval r * g.eval r ≤ 0 := by
  rw [eval_mul_right_eq_of_isRoot hr]
  have hsq : 0 ≤ (g.eval r) ^ 2 := sq_nonneg (g.eval r)
  exact mul_nonpos_of_nonpos_of_nonneg hb hsq

private lemma eval_mul_right_neg_of_isRoot_of_eval_neg_of_not_isRoot
    {f g a b : ℝ[X]} {r : ℝ}
    (hr : f.IsRoot r) (hb : b.eval r < 0) (hg : ¬ g.IsRoot r) :
    (a * f + b * g).eval r * g.eval r < 0 := by
  rw [eval_mul_right_eq_of_isRoot hr]
  have hg_ne : g.eval r ≠ 0 := by
    intro hg0
    exact hg (by simpa [Polynomial.IsRoot.def] using hg0)
  have hsq : 0 < (g.eval r) ^ 2 := by
    exact sq_pos_iff.mpr hg_ne
  exact mul_neg_of_neg_of_pos hb hsq

/-- Structured Liu--Wang differ-by-1 theorem: if `g ⊳ f`, the combination
`a * f + b * g` has degree `deg(f)+1` and positive leading coefficient, `b` is
strictly negative at roots of `f`, and `f` and `g` have no common roots, then
`f ⊳ a * f + b * g`. -/
theorem prec_of_interlaces_evalCoeff_neg_succ
    {f g a b : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff (a * f + b * g))
    (hdeg : (a * f + b * g).natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_neg : ∀ r, f.IsRoot r → b.eval r < 0) :
    Prec f (a * f + b * g) := by
  refine prec_of_interlaces_eval_mul_neg_succ hgf hg_pos hF_pos hdeg ?_
  intro r hr
  exact eval_mul_right_neg_of_isRoot_of_eval_neg_of_not_isRoot hr (hb_neg r hr) (hno r hr)

/-- Structured Liu--Wang same-degree theorem: if `g ⊳ f`, the combination
`a * f + b * g` has the same degree as `f` and positive leading coefficient,
`b` is strictly negative at roots of `f`, and `f` and `g` have no common
roots, then `f ≺ a * f + b * g`. -/
theorem prec_of_interlaces_evalCoeff_neg_same
    {f g a b : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff (a * f + b * g))
    (hdeg : (a * f + b * g).natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_neg : ∀ r, f.IsRoot r → b.eval r < 0) :
    Prec f (a * f + b * g) := by
  refine prec_of_interlaces_eval_mul_neg_same hgf hg_pos hF_pos hdeg ?_
  intro r hr
  exact eval_mul_right_neg_of_isRoot_of_eval_neg_of_not_isRoot hr (hb_neg r hr) (hno r hr)

/-- Degree-bounded structured Liu--Wang theorem in the strict-sign/no-common
regime. -/
theorem prec_of_interlaces_evalCoeff_neg
    {f g a b : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff (a * f + b * g))
    (hdeg_lo : f.natDegree ≤ (a * f + b * g).natDegree)
    (hdeg_hi : (a * f + b * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_neg : ∀ r, f.IsRoot r → b.eval r < 0) :
    Prec f (a * f + b * g) := by
  have hcases :
      (a * f + b * g).natDegree = f.natDegree ∨
        (a * f + b * g).natDegree = f.natDegree + 1 := by
    lia
  rcases hcases with hsame | hsucc
  · exact prec_of_interlaces_evalCoeff_neg_same hgf hg_pos hF_pos hsame hno hb_neg
  · exact prec_of_interlaces_evalCoeff_neg_succ hgf hg_pos hF_pos hsucc hno hb_neg

private lemma hasPosLeadingCoeff_of_X_sub_C_mul {q : ℝ[X]} {r : ℝ}
    (h : HasPosLeadingCoeff ((X - C r) * q)) :
    HasPosLeadingCoeff q := by
  unfold HasPosLeadingCoeff at h ⊢
  simpa [Polynomial.leadingCoeff_mul, leadingCoeff_X_sub_C] using h

private lemma interlaces_of_interlaces_X_sub_C_mul {f g : ℝ[X]} {r : ℝ}
    (h : Interlaces ((X - C r) * g) ((X - C r) * f)) :
    Interlaces g f := by
  have hprec : Prec ((X - C r) * g) ((X - C r) * f) := h.toPrec
  have hprec' : Prec g f := prec_of_prec_mul_X_sub_C_both r hprec
  obtain ⟨hf_mul, hg_mul, hdeg_mul, _, _, _, _, _, _, _⟩ := h
  have hf0 : f ≠ 0 := right_ne_zero_of_mul hf_mul.1
  have hg0 : g ≠ 0 := right_ne_zero_of_mul hg_mul.1
  have hdeg : g.natDegree + 1 = f.natDegree := by
    rw [natDegree_mul (X_sub_C_ne_zero r) hg0, natDegree_X_sub_C,
      natDegree_mul (X_sub_C_ne_zero r) hf0, natDegree_X_sub_C] at hdeg_mul
    lia
  exact hprec'.toInterlaces hdeg

private lemma isRoot_add_mul_of_common_root {f g a b : ℝ[X]} {r : ℝ}
    (hrf : f.IsRoot r) (hrg : g.IsRoot r) :
    (a * f + b * g).IsRoot r := by
  rw [Polynomial.IsRoot.def]
  have hf0 : f.eval r = 0 := by
    simpa [Polynomial.IsRoot.def] using hrf
  have hg0 : g.eval r = 0 := by
    simpa [Polynomial.IsRoot.def] using hrg
  simp [eval_add, eval_mul, hf0, hg0]

private lemma add_mul_factor_X_sub_C {a b qf qg : ℝ[X]} {r : ℝ} :
    a * ((X - C r) * qf) + b * ((X - C r) * qg) =
      (X - C r) * (a * qf + b * qg) := by
  ring

/-- If a structured Liu--Wang quotient already satisfies the desired `Prec`
conclusion, multiplying everything by a common linear factor preserves it. This
is the multiplication-back step for common-root reductions. -/
private lemma prec_mul_X_sub_C_of_linearCombo_quotient
    {qf qg a b : ℝ[X]} {r : ℝ}
    (hprec : Prec qf (a * qf + b * qg)) :
    Prec ((X - C r) * qf) (a * ((X - C r) * qf) + b * ((X - C r) * qg)) := by
  have hmul :
      Prec ((X - C r) * qf) ((X - C r) * (a * qf + b * qg)) :=
    prec_mul_common_factor (isRealRooted_X_sub_C r) hprec
  simpa [add_mul_factor_X_sub_C, add_comm, add_left_comm, add_assoc] using hmul

private lemma common_root_reduction_data
    {f g a b : ℝ[X]} {r : ℝ}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff (a * f + b * g))
    (hdeg_lo : f.natDegree ≤ (a * f + b * g).natDegree)
    (hdeg_hi : (a * f + b * g).natDegree ≤ f.natDegree + 1)
    (hb_nonpos : ∀ s, f.IsRoot s → b.eval s ≤ 0)
    (hrf : f.IsRoot r) (hrg : g.IsRoot r) :
    ∃ qf qg,
      f = (X - C r) * qf ∧
      g = (X - C r) * qg ∧
      Interlaces qg qf ∧
      HasPosLeadingCoeff qg ∧
      HasPosLeadingCoeff (a * qf + b * qg) ∧
      qf.natDegree ≤ (a * qf + b * qg).natDegree ∧
      (a * qf + b * qg).natDegree ≤ qf.natDegree + 1 ∧
      (∀ s, qf.IsRoot s → b.eval s ≤ 0) := by
  have hgf' : Interlaces g f := hgf
  obtain ⟨hf, hg, _, _, _, _, _, _, _, _⟩ := hgf
  obtain ⟨qf, hqf⟩ := dvd_iff_isRoot.mpr hrf
  obtain ⟨qg, hqg⟩ := dvd_iff_isRoot.mpr hrg
  refine ⟨qf, qg, hqf, hqg, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hmul : Interlaces ((X - C r) * qg) ((X - C r) * qf) := by
      simpa [hqf, hqg] using hgf'
    exact interlaces_of_interlaces_X_sub_C_mul hmul
  · apply hasPosLeadingCoeff_of_X_sub_C_mul (r := r)
    simpa [hqg] using hg_pos
  · apply hasPosLeadingCoeff_of_X_sub_C_mul (r := r)
    simpa [hqf, hqg, add_mul_factor_X_sub_C, add_comm, add_left_comm, add_assoc] using hF_pos
  · have hf_ne : f ≠ 0 := hf.1
    have hF_ne : a * f + b * g ≠ 0 := by
      intro h0
      simp [HasPosLeadingCoeff, h0] at hF_pos
    have hqf_ne : qf ≠ 0 := by
      intro h0
      exact hf_ne (by simp [hqf, h0])
    have hFq_ne : a * qf + b * qg ≠ 0 := by
      intro h0
      exact hF_ne (by simp [hqf, hqg, add_mul_factor_X_sub_C, h0])
    rw [hqf, hqg, natDegree_mul (X_sub_C_ne_zero r) hqf_ne, natDegree_X_sub_C,
      add_mul_factor_X_sub_C,
      natDegree_mul (X_sub_C_ne_zero r) hFq_ne, natDegree_X_sub_C] at hdeg_lo
    lia
  · have hf_ne : f ≠ 0 := hf.1
    have hF_ne : a * f + b * g ≠ 0 := by
      intro h0
      simp [HasPosLeadingCoeff, h0] at hF_pos
    have hqf_ne : qf ≠ 0 := by
      intro h0
      exact hf_ne (by simp [hqf, h0])
    have hFq_ne : a * qf + b * qg ≠ 0 := by
      intro h0
      exact hF_ne (by simp [hqf, hqg, add_mul_factor_X_sub_C, h0])
    rw [hqf, hqg, natDegree_mul (X_sub_C_ne_zero r) hqf_ne, natDegree_X_sub_C,
      add_mul_factor_X_sub_C,
      natDegree_mul (X_sub_C_ne_zero r) hFq_ne, natDegree_X_sub_C] at hdeg_hi
    lia
  · intro s hs
    apply hb_nonpos s
    rw [hqf, Polynomial.IsRoot.def, eval_mul]
    have hs0 : qf.eval s = 0 := by
      simpa [Polynomial.IsRoot.def] using hs
    simp [hs0]

private lemma natDegree_lt_of_interlaces_degree_lower_bound {f g F : ℝ[X]}
    (hgf : Interlaces g f) (hdeg_lo : f.natDegree ≤ F.natDegree) :
    g.natDegree < F.natDegree := by
  obtain ⟨_, _, hdeg, _, _, _, _, _, _, _⟩ := hgf
  lia

lemma natDegree_sub_C_mul_eq_of_interlaces_degree_lower_bound
    {f g F : ℝ[X]} (hgf : Interlaces g f) (hdeg_lo : f.natDegree ≤ F.natDegree) (c : ℝ) :
    (F - C c * g).natDegree = F.natDegree := by
  have hlt : (C c * g).natDegree < F.natDegree := by
    exact (natDegree_C_mul_le c g).trans_lt
      (natDegree_lt_of_interlaces_degree_lower_bound hgf hdeg_lo)
  exact natDegree_sub_eq_left_of_natDegree_lt hlt

lemma hasPosLeadingCoeff_sub_C_mul_of_interlaces_degree_lower_bound
    {f g F : ℝ[X]} (hgf : Interlaces g f) (hdeg_lo : f.natDegree ≤ F.natDegree)
    (hF_pos : HasPosLeadingCoeff F) (c : ℝ) :
    HasPosLeadingCoeff (F - C c * g) := by
  unfold HasPosLeadingCoeff at hF_pos ⊢
  have hlt : degree (C c * g) < degree F := by
    exact degree_lt_degree <|
      (natDegree_C_mul_le c g).trans_lt
        (natDegree_lt_of_interlaces_degree_lower_bound hgf hdeg_lo)
  rw [leadingCoeff_sub_of_degree_lt hlt]
  exact hF_pos

/-- Weak-sign Liu--Wang perturbation step: subtracting a small positive constant from the
coefficient of `g` makes the root-sign condition strict, so the strict mixed theorem applies. -/
theorem prec_sub_C_mul_of_interlaces_evalCoeff_nonpos_of_no_common
    {f g a b : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff (a * f + b * g))
    (hdeg_lo : f.natDegree ≤ (a * f + b * g).natDegree)
    (hdeg_hi : (a * f + b * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_nonpos : ∀ r, f.IsRoot r → b.eval r ≤ 0)
    {δ : ℝ} (hδ : 0 < δ) :
    Prec f ((a * f + b * g) - C δ * g) := by
  let F : ℝ[X] := a * f + b * g
  have hdeg_lo' : f.natDegree ≤ F.natDegree := by
    simpa [F] using hdeg_lo
  have hdeg_hi' : F.natDegree ≤ f.natDegree + 1 := by
    simpa [F] using hdeg_hi
  have hcases : F.natDegree = f.natDegree ∨ F.natDegree = f.natDegree + 1 := by
    have := hdeg_lo'
    have := hdeg_hi'
    lia
  have hFδ_pos : HasPosLeadingCoeff (F - C δ * g) :=
    hasPosLeadingCoeff_sub_C_mul_of_interlaces_degree_lower_bound hgf hdeg_lo' hF_pos δ
  have hnat_Fδ : (F - C δ * g).natDegree = F.natDegree :=
    natDegree_sub_C_mul_eq_of_interlaces_degree_lower_bound hgf hdeg_lo' δ
  have hroot_sign : ∀ r, f.IsRoot r → (F - C δ * g).eval r * g.eval r < 0 := by
    intro r hr
    have hbδ : (b - C δ).eval r < 0 := by
      rw [Polynomial.eval_sub, Polynomial.eval_C]
      linarith [hb_nonpos r hr, hδ]
    have hEq : F - C δ * g = a * f + (b - C δ) * g := by
      simp [F, sub_eq_add_neg, add_assoc, right_distrib]
    rw [hEq]
    exact eval_mul_right_neg_of_isRoot_of_eval_neg_of_not_isRoot hr hbδ (hno r hr)
  rcases hcases with hsame | hsucc
  · have hdeg_same : (F - C δ * g).natDegree = f.natDegree := by
      rw [hnat_Fδ, hsame]
    exact prec_of_interlaces_eval_mul_neg_same hgf hg_pos hFδ_pos hdeg_same hroot_sign
  · have hdeg_succ : (F - C δ * g).natDegree = f.natDegree + 1 := by
      rw [hnat_Fδ, hsucc]
    exact prec_of_interlaces_eval_mul_neg_succ hgf hg_pos hFδ_pos hdeg_succ hroot_sign

/-- Real-rootedness for the perturbed weak-sign Liu--Wang combination. -/
theorem isRealRooted_sub_C_mul_of_interlaces_evalCoeff_nonpos_of_no_common
    {f g a b : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff (a * f + b * g))
    (hdeg_lo : f.natDegree ≤ (a * f + b * g).natDegree)
    (hdeg_hi : (a * f + b * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_nonpos : ∀ r, f.IsRoot r → b.eval r ≤ 0)
    {δ : ℝ} (hδ : 0 < δ) :
    (((a * f + b * g) - C δ * g) ≠ 0 ∧ ((a * f + b * g) - C δ * g).roots.card = ((a * f + b * g) - C δ * g).natDegree) :=
  (prec_sub_C_mul_of_interlaces_evalCoeff_nonpos_of_no_common
    hgf hg_pos hF_pos hdeg_lo hdeg_hi hno hb_nonpos hδ).2.1

private def coeffSumRange (p : ℝ[X]) : ℝ :=
  Finset.sum (Finset.range (p.natDegree + 1)) fun j => ‖p.coeff j‖

private lemma coeff_norm_le_coeffSumRange (p : ℝ[X]) (i : ℕ) :
    ‖p.coeff i‖ ≤ coeffSumRange p := by
  by_cases hi : i ∈ Finset.range (p.natDegree + 1)
  · unfold coeffSumRange
    exact Finset.single_le_sum (fun j _ => norm_nonneg _) hi
  · have hlt : p.natDegree < i := by
      exact Nat.lt_of_not_ge (by simpa [Finset.mem_range] using hi)
    rw [coeff_eq_zero_of_natDegree_lt hlt, norm_zero]
    have hnonneg : 0 ≤ coeffSumRange p := by
      unfold coeffSumRange
      exact Finset.sum_nonneg fun _ _ => norm_nonneg _
    simpa using hnonneg

private lemma mem_range_of_mem_aroots_of_isRealRooted {p : ℝ[X]} (hp : p ≠ 0 ∧ p.roots.card = p.natDegree)
    {z : ℂ} (hz : z ∈ p.aroots ℂ) :
    z ∈ (algebraMap ℝ ℂ).range := by
  have hmap :
      p.roots.map (algebraMap ℝ ℂ) = p.aroots ℂ := by
    simpa [Polynomial.aroots_def] using
      roots_map_of_injective_of_card_eq_natDegree
        (p := p) (f := algebraMap ℝ ℂ) (algebraMap ℝ ℂ).injective hp.2
  rw [← hmap] at hz
  rcases Multiset.mem_map.mp hz with ⟨x, _, rfl⟩
  exact ⟨x, rfl⟩

/-- Weak-sign Liu--Wang real-rootedness theorem in the no-common-roots regime. -/
theorem isRealRooted_of_interlaces_evalCoeff_nonpos_of_no_common
    {f g a b : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff (a * f + b * g))
    (hdeg_lo : f.natDegree ≤ (a * f + b * g).natDegree)
    (hdeg_hi : (a * f + b * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_nonpos : ∀ r, f.IsRoot r → b.eval r ≤ 0) :
    ((a * f + b * g) ≠ 0 ∧ (a * f + b * g).roots.card = (a * f + b * g).natDegree) := by
  let F : ℝ[X] := a * f + b * g
  have hF_ne : F ≠ 0 := by
    intro h0
    simp [HasPosLeadingCoeff, F, h0] at hF_pos
  have hlc_pos : 0 < F.leadingCoeff := by
    simpa [F] using hF_pos
  have hlc_ne : F.leadingCoeff ≠ 0 := ne_of_gt hlc_pos
  let q : ℝ[X] := C F.leadingCoeff⁻¹ * F
  have hq_monic : q.Monic := by
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    exact inv_mul_cancel₀ hlc_ne
  have hq_ne : q ≠ 0 := by
    exact mul_ne_zero (by simp [hlc_ne]) hF_ne
  have hf_deg_pos : 0 < f.natDegree := by
    obtain ⟨_, _, hdeg, _, _, _, _, _, _, _⟩ := hgf
    lia
  have hq_deg_pos : 0 < q.natDegree := by
    rw [show q = C F.leadingCoeff⁻¹ * F by rfl, natDegree_C_mul (inv_ne_zero hlc_ne)]
    have hF_deg_pos : 0 < F.natDegree := by
      have : f.natDegree ≤ F.natDegree := by
        simpa [F] using hdeg_lo
      lia
    exact hF_deg_pos
  have hroots_real :
      ∀ z ∈ (q.map (algebraMap ℝ ℂ)).roots, z ∈ (algebraMap ℝ ℂ).range := by
    intro z hz
    by_contra hz_not_real
    have hzim_ne : z.im ≠ 0 := by
      intro hzim
      apply hz_not_real
      refine ⟨z.re, ?_⟩
      apply Complex.ext <;> simp [hzim]
    have hz_aroot : z ∈ q.aroots ℂ := by
      simpa [Polynomial.aroots_def] using hz
    have hz_aeval : Polynomial.aeval z q = 0 := by
      exact (Polynomial.mem_aroots (p := q) (S := ℂ) (a := z)).mp hz_aroot |>.2
    let eps0 : ℝ := |z.im|
    have heps0_pos : 0 < eps0 := abs_pos.mpr hzim_ne
    let R : ℝ := max ‖z‖ 1
    let u : ℝ := eps0 / (2 * R)
    let η : ℝ := u ^ q.natDegree / (q.natDegree + 1)
    let M : ℝ := max 1 (coeffSumRange g)
    let A : ℝ := max 1 (‖F.leadingCoeff⁻¹‖ * M)
    let δ : ℝ := η / (2 * A)
    have hη_pos : 0 < η := by
      unfold η u R eps0
      positivity
    have hδ_pos : 0 < δ := by
      unfold δ A
      positivity
    let qδ : ℝ[X] := C F.leadingCoeff⁻¹ * (F - C δ * g)
    have hFδ_natdeg : (F - C δ * g).natDegree = F.natDegree :=
      natDegree_sub_C_mul_eq_of_interlaces_degree_lower_bound hgf
        (by simpa [F] using hdeg_lo) δ
    have hFδ_lc : (F - C δ * g).leadingCoeff = F.leadingCoeff := by
      have hlt : degree (C δ * g) < degree F := by
        exact degree_lt_degree <|
          (natDegree_C_mul_le δ g).trans_lt
            (natDegree_lt_of_interlaces_degree_lower_bound hgf (by simpa [F] using hdeg_lo))
      rw [leadingCoeff_sub_of_degree_lt hlt]
    have hqδ_monic : qδ.Monic := by
      apply monic_C_mul_of_mul_leadingCoeff_eq_one
      rw [hFδ_lc]
      exact inv_mul_cancel₀ hlc_ne
    have hqδ_deg : qδ.natDegree = q.natDegree := by
      rw [show qδ = C F.leadingCoeff⁻¹ * (F - C δ * g) by rfl,
        show q = C F.leadingCoeff⁻¹ * F by rfl,
        natDegree_C_mul (inv_ne_zero hlc_ne), natDegree_C_mul (inv_ne_zero hlc_ne),
        hFδ_natdeg]
    have hqδ_coeff :
        ∀ i : ℕ, ‖qδ.coeff i - q.coeff i‖ < η := by
      intro i
      have hgi_bound : ‖g.coeff i‖ ≤ M := by
        exact (coeff_norm_le_coeffSumRange g i).trans (le_max_right _ _)
      have hprod_bound : ‖F.leadingCoeff⁻¹‖ * ‖g.coeff i‖ ≤ A := by
        have hA : ‖F.leadingCoeff⁻¹‖ * M ≤ A := le_max_right _ _
        nlinarith [hgi_bound, norm_nonneg (F.leadingCoeff⁻¹), norm_nonneg (g.coeff i)]
      have hcoeff :
          qδ.coeff i - q.coeff i = -(F.leadingCoeff⁻¹ * (δ * g.coeff i)) := by
        simp [qδ, q, Polynomial.coeff_C_mul]
        ring
      calc
        ‖qδ.coeff i - q.coeff i‖
          = ‖-(F.leadingCoeff⁻¹ * (δ * g.coeff i))‖ := by rw [hcoeff]
        _ = ‖F.leadingCoeff⁻¹ * (δ * g.coeff i)‖ := by rw [norm_neg]
        _ = ‖F.leadingCoeff⁻¹‖ * ‖δ * g.coeff i‖ := by rw [norm_mul]
        _ = ‖F.leadingCoeff⁻¹‖ * (δ * ‖g.coeff i‖) := by
              rw [norm_mul, Real.norm_of_nonneg hδ_pos.le]
        _ = δ * (‖F.leadingCoeff⁻¹‖ * ‖g.coeff i‖) := by ring
        _ ≤ δ * A := by gcongr
        _ = η / 2 := by
              unfold δ
              field_simp [A]
        _ < η := by linarith
    obtain ⟨w, hw_mem, hw_close⟩ :=
      Polynomial.exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt
        (f := q) (g := qδ) hη_pos hz_aeval hq_monic hqδ_monic hqδ_deg hqδ_coeff
        (IsAlgClosed.splits _)
    have hFδ_rr : ((F - C δ * g) ≠ 0 ∧ (F - C δ * g).roots.card = (F - C δ * g).natDegree) :=
      isRealRooted_sub_C_mul_of_interlaces_evalCoeff_nonpos_of_no_common
        hgf hg_pos hF_pos hdeg_lo hdeg_hi hno hb_nonpos hδ_pos
    have hqδ_rr : (qδ ≠ 0 ∧ qδ.roots.card = qδ.natDegree) :=
      isRealRooted_C_mul hFδ_rr (inv_ne_zero hlc_ne)
    rcases mem_range_of_mem_aroots_of_isRealRooted hqδ_rr hw_mem with ⟨x, rfl⟩
    have him_le : eps0 ≤ ‖z - x‖ := by
      unfold eps0
      simpa using (Complex.abs_im_le_norm (z - x))
    have hR_pos : 0 < R := by
      unfold R
      positivity
    have hbound_eq :
        (((q.natDegree : ℝ) + 1) * η) ^ ((q.natDegree : ℝ)⁻¹) * R = eps0 / 2 := by
      have hdeg_ne : q.natDegree ≠ 0 := by lia
      have hu_nonneg : 0 ≤ u := by
        unfold u eps0 R
        positivity
      calc
        (((q.natDegree : ℝ) + 1) * η) ^ ((q.natDegree : ℝ)⁻¹) * R
            = (((q.natDegree : ℝ) + 1) * (u ^ q.natDegree / ((q.natDegree : ℝ) + 1)))
                ^ ((q.natDegree : ℝ)⁻¹) * R := by simp [η]
        _ = (u ^ q.natDegree) ^ ((q.natDegree : ℝ)⁻¹) * R := by
              congr 1
              field_simp
        _ = u * R := by rw [Real.pow_rpow_inv_natCast hu_nonneg hdeg_ne]
        _ = eps0 / 2 := by
              unfold u
              field_simp [R, hR_pos.ne']
    have hclose_eps : ‖z - x‖ < eps0 := by
      calc
        ‖z - x‖ < (((q.natDegree : ℝ) + 1) * η) ^ ((q.natDegree : ℝ)⁻¹) * R := hw_close
        _ = eps0 / 2 := hbound_eq
        _ < eps0 := by linarith
    exact (not_lt_of_ge him_le) hclose_eps
  have hq_split : q.Splits := by
    exact Polynomial.Splits.of_splits_map (i := algebraMap ℝ ℂ)
      (IsAlgClosed.splits _) hroots_real
  have hq_rr : (q ≠ 0 ∧ q.roots.card = q.natDegree) := by
    exact ⟨hq_ne, splits_iff_card_roots.mp hq_split⟩
  have hF_eq : C F.leadingCoeff * q = F := by
    unfold q
    calc
      C F.leadingCoeff * (C F.leadingCoeff⁻¹ * F)
          = (C F.leadingCoeff * C F.leadingCoeff⁻¹) * F := by rw [mul_assoc]
      _ = C (F.leadingCoeff * F.leadingCoeff⁻¹) * F := by rw [C_mul]
      _ = F := by simp [hlc_ne]
  have hF_rr : (F ≠ 0 ∧ F.roots.card = F.natDegree) := by
    rw [← hF_eq]
    exact isRealRooted_C_mul hq_rr hlc_ne
  simpa [F] using hF_rr

/-- If every positive perturbation `F - C δ * g` is real-rooted, then `F` is
real-rooted as well. The interlacing hypothesis is only used to keep the degree
and leading coefficient stable under the subtraction. -/
theorem isRealRooted_of_interlaces_sub_C_mul_of_forall_pos
    {f g F : ℝ[X]}
    (hgf : Interlaces g f)
    (hF_pos : HasPosLeadingCoeff F)
    (hdeg_lo : f.natDegree ≤ F.natDegree)
    (hsub_rr : ∀ {δ : ℝ}, 0 < δ → ((F - C δ * g) ≠ 0 ∧ (F - C δ * g).roots.card = (F - C δ * g).natDegree)) :
    (F ≠ 0 ∧ F.roots.card = F.natDegree) := by
  have hF_ne : F ≠ 0 := by
    intro h0
    simp [HasPosLeadingCoeff, h0] at hF_pos
  have hlc_pos : 0 < F.leadingCoeff := by
    simpa using hF_pos
  have hlc_ne : F.leadingCoeff ≠ 0 := ne_of_gt hlc_pos
  let q : ℝ[X] := C F.leadingCoeff⁻¹ * F
  have hq_monic : q.Monic := by
    apply monic_C_mul_of_mul_leadingCoeff_eq_one
    exact inv_mul_cancel₀ hlc_ne
  have hq_ne : q ≠ 0 := by
    exact mul_ne_zero (by simp [hlc_ne]) hF_ne
  have hq_deg_pos : 0 < q.natDegree := by
    rw [show q = C F.leadingCoeff⁻¹ * F by rfl, natDegree_C_mul (inv_ne_zero hlc_ne)]
    have hF_deg_pos : 0 < F.natDegree := by
      obtain ⟨_, _, hdeg, _, _, _, _, _, _, _⟩ := hgf
      lia
    exact hF_deg_pos
  have hroots_real :
      ∀ z ∈ (q.map (algebraMap ℝ ℂ)).roots, z ∈ (algebraMap ℝ ℂ).range := by
    intro z hz
    by_contra hz_not_real
    have hzim_ne : z.im ≠ 0 := by
      intro hzim
      apply hz_not_real
      refine ⟨z.re, ?_⟩
      apply Complex.ext <;> simp [hzim]
    have hz_aroot : z ∈ q.aroots ℂ := by
      simpa [Polynomial.aroots_def] using hz
    have hz_aeval : Polynomial.aeval z q = 0 := by
      exact (Polynomial.mem_aroots (p := q) (S := ℂ) (a := z)).mp hz_aroot |>.2
    let eps0 : ℝ := |z.im|
    have heps0_pos : 0 < eps0 := abs_pos.mpr hzim_ne
    let R : ℝ := max ‖z‖ 1
    let u : ℝ := eps0 / (2 * R)
    let η : ℝ := u ^ q.natDegree / (q.natDegree + 1)
    let M : ℝ := max 1 (coeffSumRange g)
    let A : ℝ := max 1 (‖F.leadingCoeff⁻¹‖ * M)
    let δ : ℝ := η / (2 * A)
    have hη_pos : 0 < η := by
      unfold η u R eps0
      positivity
    have hδ_pos : 0 < δ := by
      unfold δ A
      positivity
    let qδ : ℝ[X] := C F.leadingCoeff⁻¹ * (F - C δ * g)
    have hFδ_natdeg : (F - C δ * g).natDegree = F.natDegree :=
      natDegree_sub_C_mul_eq_of_interlaces_degree_lower_bound hgf hdeg_lo δ
    have hFδ_lc : (F - C δ * g).leadingCoeff = F.leadingCoeff := by
      have hlt : degree (C δ * g) < degree F := by
        exact degree_lt_degree <|
          (natDegree_C_mul_le δ g).trans_lt
            (natDegree_lt_of_interlaces_degree_lower_bound hgf hdeg_lo)
      rw [leadingCoeff_sub_of_degree_lt hlt]
    have hqδ_monic : qδ.Monic := by
      apply monic_C_mul_of_mul_leadingCoeff_eq_one
      rw [hFδ_lc]
      exact inv_mul_cancel₀ hlc_ne
    have hqδ_deg : qδ.natDegree = q.natDegree := by
      rw [show qδ = C F.leadingCoeff⁻¹ * (F - C δ * g) by rfl,
        show q = C F.leadingCoeff⁻¹ * F by rfl,
        natDegree_C_mul (inv_ne_zero hlc_ne), natDegree_C_mul (inv_ne_zero hlc_ne),
        hFδ_natdeg]
    have hqδ_coeff :
        ∀ i : ℕ, ‖qδ.coeff i - q.coeff i‖ < η := by
      intro i
      have hgi_bound : ‖g.coeff i‖ ≤ M := by
        exact (coeff_norm_le_coeffSumRange g i).trans (le_max_right _ _)
      have hprod_bound : ‖F.leadingCoeff⁻¹‖ * ‖g.coeff i‖ ≤ A := by
        have hA : ‖F.leadingCoeff⁻¹‖ * M ≤ A := le_max_right _ _
        nlinarith [hgi_bound, norm_nonneg (F.leadingCoeff⁻¹), norm_nonneg (g.coeff i)]
      have hcoeff :
          qδ.coeff i - q.coeff i = -(F.leadingCoeff⁻¹ * (δ * g.coeff i)) := by
        simp [qδ, q, Polynomial.coeff_C_mul]
        ring
      calc
        ‖qδ.coeff i - q.coeff i‖
          = ‖-(F.leadingCoeff⁻¹ * (δ * g.coeff i))‖ := by rw [hcoeff]
        _ = ‖F.leadingCoeff⁻¹ * (δ * g.coeff i)‖ := by rw [norm_neg]
        _ = ‖F.leadingCoeff⁻¹‖ * ‖δ * g.coeff i‖ := by rw [norm_mul]
        _ = ‖F.leadingCoeff⁻¹‖ * (δ * ‖g.coeff i‖) := by
              rw [norm_mul, Real.norm_of_nonneg hδ_pos.le]
        _ = δ * (‖F.leadingCoeff⁻¹‖ * ‖g.coeff i‖) := by ring
        _ ≤ δ * A := by gcongr
        _ = η / 2 := by
              unfold δ
              field_simp [A]
        _ < η := by linarith
    obtain ⟨w, hw_mem, hw_close⟩ :=
      Polynomial.exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt
        (f := q) (g := qδ) hη_pos hz_aeval hq_monic hqδ_monic hqδ_deg hqδ_coeff
        (IsAlgClosed.splits _)
    have hFδ_rr : ((F - C δ * g) ≠ 0 ∧ (F - C δ * g).roots.card = (F - C δ * g).natDegree) := hsub_rr hδ_pos
    have hqδ_rr : (qδ ≠ 0 ∧ qδ.roots.card = qδ.natDegree) :=
      isRealRooted_C_mul hFδ_rr (inv_ne_zero hlc_ne)
    rcases mem_range_of_mem_aroots_of_isRealRooted hqδ_rr hw_mem with ⟨x, rfl⟩
    have him_le : eps0 ≤ ‖z - x‖ := by
      unfold eps0
      simpa using (Complex.abs_im_le_norm (z - x))
    have hR_pos : 0 < R := by
      unfold R
      positivity
    have hbound_eq :
        (((q.natDegree : ℝ) + 1) * η) ^ ((q.natDegree : ℝ)⁻¹) * R = eps0 / 2 := by
      have hdeg_ne : q.natDegree ≠ 0 := by lia
      have hu_nonneg : 0 ≤ u := by
        unfold u eps0 R
        positivity
      calc
        (((q.natDegree : ℝ) + 1) * η) ^ ((q.natDegree : ℝ)⁻¹) * R
            = (((q.natDegree : ℝ) + 1) * (u ^ q.natDegree / ((q.natDegree : ℝ) + 1)))
                ^ ((q.natDegree : ℝ)⁻¹) * R := by simp [η]
        _ = (u ^ q.natDegree) ^ ((q.natDegree : ℝ)⁻¹) * R := by
              congr 1
              field_simp
        _ = u * R := by rw [Real.pow_rpow_inv_natCast hu_nonneg hdeg_ne]
        _ = eps0 / 2 := by
              unfold u
              field_simp [R, hR_pos.ne']
    have hclose_eps : ‖z - x‖ < eps0 := by
      calc
        ‖z - x‖ < (((q.natDegree : ℝ) + 1) * η) ^ ((q.natDegree : ℝ)⁻¹) * R := hw_close
        _ = eps0 / 2 := hbound_eq
        _ < eps0 := by linarith
    exact (not_lt_of_ge him_le) hclose_eps
  have hq_split : q.Splits := by
    exact Polynomial.Splits.of_splits_map (i := algebraMap ℝ ℂ)
      (IsAlgClosed.splits _) hroots_real
  have hq_rr : (q ≠ 0 ∧ q.roots.card = q.natDegree) := by
    exact ⟨hq_ne, splits_iff_card_roots.mp hq_split⟩
  have hF_eq : C F.leadingCoeff * q = F := by
    unfold q
    calc
      C F.leadingCoeff * (C F.leadingCoeff⁻¹ * F)
          = (C F.leadingCoeff * C F.leadingCoeff⁻¹) * F := by rw [mul_assoc]
      _ = C (F.leadingCoeff * F.leadingCoeff⁻¹) * F := by rw [C_mul]
      _ = F := by simp [hlc_ne]
  rw [← hF_eq]
  exact isRealRooted_C_mul hq_rr hlc_ne

/-- Weak-sign Liu--Wang same-degree theorem in the no-common-roots regime. -/
theorem prec_of_interlaces_evalCoeff_nonpos_same_of_no_common
    {f g a b : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff (a * f + b * g))
    (hdeg : (a * f + b * g).natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_nonpos : ∀ r, f.IsRoot r → b.eval r ≤ 0) :
    Prec f (a * f + b * g) := by
  let F : ℝ[X] := a * f + b * g
  have hgf' : Interlaces g f := hgf
  obtain ⟨hf, hg, _, rs, ss, hrs_sorted, _, hrs_eq, hss_eq, hint⟩ := hgf
  have hF : (F ≠ 0 ∧ F.roots.card = F.natDegree) := by
    apply isRealRooted_of_interlaces_evalCoeff_nonpos_of_no_common
      hgf' hg_pos hF_pos
    · simp [hdeg]
    · simp [hdeg]
    · exact hno
    · exact hb_nonpos
  set ts := F.roots.sort (· ≤ ·)
  have hts_eq : (↑ts : Multiset ℝ) = F.roots := Multiset.sort_eq ..
  have hts_sorted : ts.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hrs_len : rs.length = f.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, hf.2]
  have hts_len : ts.length = F.natDegree := by
    rw [show ts = F.roots.sort (· ≤ ·) by rfl, Multiset.length_sort, hF.2]
  have hoff : ts.length = rs.length + 0 := by
    rw [hts_len, hrs_len, hdeg]
    simp
  have hstrict :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        r₁ < r₂ := by
    intro pre r₁ r₂ rest hEq
    exact lt_of_consecutive_of_interlaces_of_no_common hf hg hrs_eq hss_eq hint hEq hno
  have hgsign :=
    eval_sign_of_interlaces_root hg hg_pos hrs_sorted hrs_eq hss_eq hint hno
  have hroot_on_max :
      ∀ (pre : List ℝ) {r : ℝ} {rest : List ℝ},
        rs = pre ++ r :: rest →
        ts.countP (· ≤ r) = pre.length + 1 →
        F.IsRoot r := by
    intro pre r rest hEq hcount
    have hr_root : f.IsRoot r := isRoot_of_mem_sorted_roots_eq hrs_eq hEq
    have hroot_nonpos : F.eval r * g.eval r ≤ 0 := by
      simpa [F] using
        eval_mul_right_nonpos_of_isRoot (f := f) (g := g) (a := a) (b := b)
          hr_root (hb_nonpos r hr_root)
    exact isRoot_of_eq_max_countP_le_of_sign hF hF_pos hrs_eq hts_eq hoff
      hroot_nonpos (hgsign pre hEq) hEq hcount
  have hcount_le :
      ∀ (pre : List ℝ) {r : ℝ} {rest : List ℝ},
        rs = pre ++ r :: rest →
        ts.countP (· ≤ r) ≤ pre.length + 1 :=
    countP_le_of_eq_max_isRoot (_f := f) hF hrs_sorted hts_eq hoff hstrict hroot_on_max
  have hlt :
      ∀ (pre : List ℝ) {r : ℝ} {rest : List ℝ},
        rs = pre ++ r :: rest →
        ts.countP (· < r) ≤ pre.length :=
    countP_lt_of_eq_max_isRoot (_f := f) (rs := rs) (off := 0)
      hF hts_eq hcount_le hroot_on_max
  have hle :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        pre.length < ts.countP (· ≤ r₂) := by
    intro pre r₁ r₂ rest hEq
    induction pre using List.reverseRecOn generalizing r₁ r₂ rest with
    | nil =>
        have hEq_next : rs = ([r₁] : List ℝ) ++ r₂ :: rest := by
          simpa using hEq
        have hr₂_root : f.IsRoot r₂ := isRoot_of_mem_sorted_roots_eq hrs_eq hEq_next
        have hFg₂_nonpos : F.eval r₂ * g.eval r₂ ≤ 0 := by
          simpa [F] using
            eval_mul_right_nonpos_of_isRoot (f := f) (g := g) (a := a) (b := b)
              hr₂_root (hb_nonpos r₂ hr₂_root)
        by_contra hnot
        have hcount_r₂ : ts.countP (· ≤ r₂) = 0 := by
          exact Nat.eq_zero_of_not_pos hnot
        have hrs_len : rs.length = rest.length + 2 := by
          rw [hEq]
          simp
        have hcount_gt : ts.countP (r₂ < ·) = rest.length + 2 := by
          have hsplit := countP_le_add_countP_gt_eq_length ts r₂
          rw [hcount_r₂, hoff, hrs_len] at hsplit
          simpa using hsplit
        have hr₂_Froot : F.IsRoot r₂ := by
          rcases Nat.even_or_odd rest.length with heven | hodd
          · have hF_nonpos : F.eval r₂ ≤ 0 := by
              have hg_pos' : 0 < g.eval r₂ := (hgsign [r₁] hEq_next).1 heven
              nlinarith [hFg₂_nonpos, hg_pos']
            have hcount_even : Even (ts.countP (r₂ < ·)) := by
              rw [hcount_gt]
              have hstep : Odd (rest.length + 1) := heven.add_odd odd_one
              have hfinal : Even ((rest.length + 1) + 1) := hstep.add_odd odd_one
              simpa [Nat.add_assoc] using hfinal
            exact isRoot_of_eval_nonpos_of_even_countP_gt hF hF_pos hts_eq hF_nonpos
              hcount_even
          · have hF_nonneg : 0 ≤ F.eval r₂ := by
              have hg_neg' : g.eval r₂ < 0 := (hgsign [r₁] hEq_next).2 hodd
              nlinarith [hFg₂_nonpos, hg_neg']
            have hcount_odd : Odd (ts.countP (r₂ < ·)) := by
              rw [hcount_gt]
              have hstep : Even (rest.length + 1) := hodd.add_odd odd_one
              have hfinal : Odd ((rest.length + 1) + 1) := hstep.add_odd odd_one
              simpa [Nat.add_assoc] using hfinal
            exact isRoot_of_eval_nonneg_of_odd_countP_gt hF hF_pos hts_eq hF_nonneg
              hcount_odd
        have hr₂_mem : r₂ ∈ ts := by
          apply Multiset.mem_coe.mp
          rw [hts_eq]
          exact (mem_roots hF.1).mpr hr₂_Froot
        have hcount_pos : 0 < ts.countP (· ≤ r₂) := by
          rw [List.countP_eq_length_filter]
          exact List.length_pos_of_mem <| List.mem_filter.mpr ⟨hr₂_mem, by simp⟩
        lia
    | append_singleton pre x ih =>
        have hEq_prev : rs = pre ++ x :: r₁ :: r₂ :: rest := by
          simpa [List.append_assoc] using hEq
        have hprev : pre.length < ts.countP (· ≤ r₁) := ih hEq_prev
        have hlen_pre : (pre ++ [x]).length = pre.length + 1 := by
          simp
        by_cases hgood : (pre ++ [x]).length < ts.countP (· ≤ r₂)
        · simpa using hgood
        · have hbad : ts.countP (· ≤ r₂) ≤ pre.length + 1 := by
            simpa [hlen_pre] using (Nat.not_lt.mp hgood)
          have hr₁_lt_r₂ : r₁ < r₂ := hstrict (pre ++ [x]) hEq
          have hmono : ts.countP (· ≤ r₁) ≤ ts.countP (· ≤ r₂) := by
            exact List.countP_mono_left <| by
              intro x _ hx
              simp only [decide_eq_true_eq] at hx ⊢
              exact le_trans hx (le_of_lt hr₁_lt_r₂)
          have hcount_r₁ : ts.countP (· ≤ r₁) = pre.length + 1 := by
            lia
          have hcount_r₂ : ts.countP (· ≤ r₂) = pre.length + 1 := by
            lia
          have hEq_next : rs = ((pre ++ [x]) ++ [r₁]) ++ r₂ :: rest := by
            simpa [List.append_assoc] using hEq
          have hr₂_root : f.IsRoot r₂ := isRoot_of_mem_sorted_roots_eq hrs_eq hEq_next
          have hFg₂_nonpos : F.eval r₂ * g.eval r₂ ≤ 0 := by
            simpa [F] using
              eval_mul_right_nonpos_of_isRoot (f := f) (g := g) (a := a) (b := b)
                hr₂_root (hb_nonpos r₂ hr₂_root)
          have hrs_len : rs.length = pre.length + rest.length + 3 := by
            rw [hEq]
            simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
          have hcount_gt : ts.countP (r₂ < ·) = rest.length + 2 := by
            have hsplit := countP_le_add_countP_gt_eq_length ts r₂
            rw [hcount_r₂, hoff, hrs_len] at hsplit
            lia
          have hr₂_Froot : F.IsRoot r₂ := by
            rcases Nat.even_or_odd rest.length with heven | hodd
            · have hF_nonpos : F.eval r₂ ≤ 0 := by
                have hg_pos' : 0 < g.eval r₂ := (hgsign ((pre ++ [x]) ++ [r₁]) hEq_next).1 heven
                nlinarith [hFg₂_nonpos, hg_pos']
              have hcount_even : Even (ts.countP (r₂ < ·)) := by
                rw [hcount_gt]
                have hstep : Odd (rest.length + 1) := heven.add_odd odd_one
                have hfinal : Even ((rest.length + 1) + 1) := hstep.add_odd odd_one
                simpa [Nat.add_assoc] using hfinal
              exact isRoot_of_eval_nonpos_of_even_countP_gt hF hF_pos hts_eq hF_nonpos
                hcount_even
            · have hF_nonneg : 0 ≤ F.eval r₂ := by
                have hg_neg' : g.eval r₂ < 0 := (hgsign ((pre ++ [x]) ++ [r₁]) hEq_next).2 hodd
                nlinarith [hFg₂_nonpos, hg_neg']
              have hcount_odd : Odd (ts.countP (r₂ < ·)) := by
                rw [hcount_gt]
                have hstep : Even (rest.length + 1) := hodd.add_odd odd_one
                have hfinal : Odd ((rest.length + 1) + 1) := hstep.add_odd odd_one
                simpa [Nat.add_assoc] using hfinal
              exact isRoot_of_eval_nonneg_of_odd_countP_gt hF hF_pos hts_eq hF_nonneg
                hcount_odd
          have hr₂_mem : r₂ ∈ ts := by
            apply Multiset.mem_coe.mp
            rw [hts_eq]
            exact (mem_roots hF.1).mpr hr₂_Froot
          have hcount_strict : ts.countP (· ≤ r₁) < ts.countP (· ≤ r₂) := by
            apply countP_lt_countP_of_exists
            · intro x hx
              simp only [decide_eq_true_eq] at hx ⊢
              exact le_trans hx (le_of_lt hr₁_lt_r₂)
            · exact hr₂_mem
            · simp [not_le_of_gt hr₁_lt_r₂]
            · simp
          lia
  simpa [F] using
    prec_of_count_bounds_same hf hF hrs_sorted hts_sorted hrs_eq hts_eq hdeg hlt hle

/-- Weak-sign Liu--Wang differ-by-1 theorem in the no-common-roots regime. -/
theorem prec_of_interlaces_evalCoeff_nonpos_succ_of_no_common
    {f g a b : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff (a * f + b * g))
    (hdeg : (a * f + b * g).natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hb_nonpos : ∀ r, f.IsRoot r → b.eval r ≤ 0) :
    Prec f (a * f + b * g) := by
  let F : ℝ[X] := a * f + b * g
  have hgf' : Interlaces g f := hgf
  obtain ⟨hf, hg, _, rs, ss, hrs_sorted, _, hrs_eq, hss_eq, hint⟩ := hgf
  have hF : (F ≠ 0 ∧ F.roots.card = F.natDegree) := by
    apply isRealRooted_of_interlaces_evalCoeff_nonpos_of_no_common
      hgf' hg_pos hF_pos
    · simp [hdeg]
    · simp [hdeg]
    · exact hno
    · exact hb_nonpos
  set ts := F.roots.sort (· ≤ ·)
  have hts_eq : (↑ts : Multiset ℝ) = F.roots := Multiset.sort_eq ..
  have hts_sorted : ts.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hrs_len : rs.length = f.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, hf.2]
  have hts_len : ts.length = F.natDegree := by
    rw [show ts = F.roots.sort (· ≤ ·) by rfl, Multiset.length_sort, hF.2]
  have hoff : ts.length = rs.length + 1 := by
    rw [hts_len, hrs_len, hdeg]
  have hstrict :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        r₁ < r₂ := by
    intro pre r₁ r₂ rest hEq
    exact lt_of_consecutive_of_interlaces_of_no_common hf hg hrs_eq hss_eq hint hEq hno
  have hgsign :=
    eval_sign_of_interlaces_root hg hg_pos hrs_sorted hrs_eq hss_eq hint hno
  have hroot_on_max :
      ∀ (pre : List ℝ) {r : ℝ} {rest : List ℝ},
        rs = pre ++ r :: rest →
        ts.countP (· ≤ r) = pre.length + 2 →
        F.IsRoot r := by
    intro pre r rest hEq hcount
    have hr_root : f.IsRoot r := isRoot_of_mem_sorted_roots_eq hrs_eq hEq
    have hroot_nonpos : F.eval r * g.eval r ≤ 0 := by
      simpa [F] using
        eval_mul_right_nonpos_of_isRoot (f := f) (g := g) (a := a) (b := b)
          hr_root (hb_nonpos r hr_root)
    exact isRoot_of_eq_max_countP_le_of_sign hF hF_pos hrs_eq hts_eq hoff
      hroot_nonpos (hgsign pre hEq) hEq hcount
  have hcount_le :
      ∀ (pre : List ℝ) {r : ℝ} {rest : List ℝ},
        rs = pre ++ r :: rest →
        ts.countP (· ≤ r) ≤ pre.length + 2 :=
    countP_le_of_eq_max_isRoot (_f := f) hF hrs_sorted hts_eq hoff hstrict hroot_on_max
  have hlt :
      ∀ (pre : List ℝ) {r : ℝ} {rest : List ℝ},
        rs = pre ++ r :: rest →
        ts.countP (· < r) ≤ pre.length + 1 :=
    countP_lt_of_eq_max_isRoot (_f := f) (rs := rs) (off := 1)
      hF hts_eq hcount_le hroot_on_max
  have hhead :
      ∀ {r : ℝ} {rest : List ℝ},
        rs = r :: rest →
        0 < ts.countP (· ≤ r) := by
    intro r rest hEq
    have hEq' : rs = ([] : List ℝ) ++ r :: rest := by
      simpa using hEq
    have hr_root : f.IsRoot r := isRoot_of_mem_sorted_roots_eq hrs_eq hEq'
    have hFg_nonpos : F.eval r * g.eval r ≤ 0 := by
      simpa [F] using
        eval_mul_right_nonpos_of_isRoot (f := f) (g := g) (a := a) (b := b)
          hr_root (hb_nonpos r hr_root)
    by_contra hnot
    have hcount_r : ts.countP (· ≤ r) = 0 := by
      exact Nat.eq_zero_of_not_pos hnot
    have hrs_len' : rs.length = rest.length + 1 := by
      rw [hEq]
      simp
    have hcount_gt : ts.countP (r < ·) = rest.length + 2 := by
      have hsplit := countP_le_add_countP_gt_eq_length ts r
      rw [hcount_r, hoff, hrs_len'] at hsplit
      simpa using hsplit
    have hr_Froot : F.IsRoot r := by
      rcases Nat.even_or_odd rest.length with heven | hodd
      · have hF_nonpos : F.eval r ≤ 0 := by
          have hg_pos' : 0 < g.eval r := (hgsign [] hEq).1 heven
          nlinarith [hFg_nonpos, hg_pos']
        have hcount_even : Even (ts.countP (r < ·)) := by
          rw [hcount_gt]
          have hstep : Odd (rest.length + 1) := heven.add_odd odd_one
          have hfinal : Even ((rest.length + 1) + 1) := hstep.add_odd odd_one
          simpa [Nat.add_assoc] using hfinal
        exact isRoot_of_eval_nonpos_of_even_countP_gt hF hF_pos hts_eq hF_nonpos
          hcount_even
      · have hF_nonneg : 0 ≤ F.eval r := by
          have hg_neg' : g.eval r < 0 := (hgsign [] hEq).2 hodd
          nlinarith [hFg_nonpos, hg_neg']
        have hcount_odd : Odd (ts.countP (r < ·)) := by
          rw [hcount_gt]
          have hstep : Even (rest.length + 1) := hodd.add_odd odd_one
          have hfinal : Odd ((rest.length + 1) + 1) := hstep.add_odd odd_one
          simpa [Nat.add_assoc] using hfinal
        exact isRoot_of_eval_nonneg_of_odd_countP_gt hF hF_pos hts_eq hF_nonneg
          hcount_odd
    have hr_mem : r ∈ ts := by
      apply Multiset.mem_coe.mp
      rw [hts_eq]
      exact (mem_roots hF.1).mpr hr_Froot
    have hcount_pos : 0 < ts.countP (· ≤ r) := by
      rw [List.countP_eq_length_filter]
      exact List.length_pos_of_mem <| List.mem_filter.mpr ⟨hr_mem, by simp⟩
    lia
  have hle :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        pre.length + 1 < ts.countP (· ≤ r₂) := by
    intro pre r₁ r₂ rest hEq
    induction pre using List.reverseRecOn generalizing r₁ r₂ rest with
    | nil =>
        have hEq_head : rs = r₁ :: r₂ :: rest := by
          simpa using hEq
        have hhead_r₁ : 0 < ts.countP (· ≤ r₁) := hhead hEq_head
        by_contra hnot
        have hbad : ts.countP (· ≤ r₂) ≤ 1 := by
          exact Nat.not_lt.mp hnot
        have hr₁_lt_r₂ : r₁ < r₂ := hstrict [] hEq
        have hmono : ts.countP (· ≤ r₁) ≤ ts.countP (· ≤ r₂) := by
          exact List.countP_mono_left <| by
            intro y _ hy
            simp only [decide_eq_true_eq] at hy ⊢
            exact le_trans hy (le_of_lt hr₁_lt_r₂)
        have hcount_r₁ : ts.countP (· ≤ r₁) = 1 := by
          lia
        have hcount_r₂ : ts.countP (· ≤ r₂) = 1 := by
          lia
        have hEq_next : rs = ([r₁] : List ℝ) ++ r₂ :: rest := by
          simpa using hEq
        have hr₂_root : f.IsRoot r₂ := isRoot_of_mem_sorted_roots_eq hrs_eq hEq_next
        have hFg₂_nonpos : F.eval r₂ * g.eval r₂ ≤ 0 := by
          simpa [F] using
            eval_mul_right_nonpos_of_isRoot (f := f) (g := g) (a := a) (b := b)
              hr₂_root (hb_nonpos r₂ hr₂_root)
        have hrs_len' : rs.length = rest.length + 2 := by
          rw [hEq]
          simp
        have hcount_gt : ts.countP (r₂ < ·) = rest.length + 2 := by
          have hsplit := countP_le_add_countP_gt_eq_length ts r₂
          rw [hcount_r₂, hoff, hrs_len'] at hsplit
          lia
        have hr₂_Froot : F.IsRoot r₂ := by
          rcases Nat.even_or_odd rest.length with heven | hodd
          · have hF_nonpos : F.eval r₂ ≤ 0 := by
              have hg_pos' : 0 < g.eval r₂ := (hgsign [r₁] hEq_next).1 heven
              nlinarith [hFg₂_nonpos, hg_pos']
            have hcount_even : Even (ts.countP (r₂ < ·)) := by
              rw [hcount_gt]
              have hstep : Odd (rest.length + 1) := heven.add_odd odd_one
              have hfinal : Even ((rest.length + 1) + 1) := hstep.add_odd odd_one
              simpa [Nat.add_assoc] using hfinal
            exact isRoot_of_eval_nonpos_of_even_countP_gt hF hF_pos hts_eq hF_nonpos
              hcount_even
          · have hF_nonneg : 0 ≤ F.eval r₂ := by
              have hg_neg' : g.eval r₂ < 0 := (hgsign [r₁] hEq_next).2 hodd
              nlinarith [hFg₂_nonpos, hg_neg']
            have hcount_odd : Odd (ts.countP (r₂ < ·)) := by
              rw [hcount_gt]
              have hstep : Even (rest.length + 1) := hodd.add_odd odd_one
              have hfinal : Odd ((rest.length + 1) + 1) := hstep.add_odd odd_one
              simpa [Nat.add_assoc] using hfinal
            exact isRoot_of_eval_nonneg_of_odd_countP_gt hF hF_pos hts_eq hF_nonneg
              hcount_odd
        have hr₂_mem : r₂ ∈ ts := by
          apply Multiset.mem_coe.mp
          rw [hts_eq]
          exact (mem_roots hF.1).mpr hr₂_Froot
        have hcount_strict : ts.countP (· ≤ r₁) < ts.countP (· ≤ r₂) := by
          apply countP_lt_countP_of_exists
          · intro y hy
            simp only [decide_eq_true_eq] at hy ⊢
            exact le_trans hy (le_of_lt hr₁_lt_r₂)
          · exact hr₂_mem
          · simp [not_le_of_gt hr₁_lt_r₂]
          · simp
        lia
    | append_singleton pre x ih =>
        have hEq_prev : rs = pre ++ x :: r₁ :: r₂ :: rest := by
          simpa [List.append_assoc] using hEq
        have hprev : pre.length + 1 < ts.countP (· ≤ r₁) := ih hEq_prev
        have hlen_pre : (pre ++ [x]).length + 1 = pre.length + 2 := by
          simp
        by_cases hgood : (pre ++ [x]).length + 1 < ts.countP (· ≤ r₂)
        · simpa [hlen_pre] using hgood
        have hr₁_lt_r₂ : r₁ < r₂ := hstrict (pre ++ [x]) hEq
        have hmono : ts.countP (· ≤ r₁) ≤ ts.countP (· ≤ r₂) := by
          exact List.countP_mono_left <| by
            intro y _ hy
            simp only [decide_eq_true_eq] at hy ⊢
            exact le_trans hy (le_of_lt hr₁_lt_r₂)
        have hbad : ts.countP (· ≤ r₂) ≤ pre.length + 2 := by
          simpa [hlen_pre] using (Nat.not_lt.mp hgood)
        have hcount_r₁ : ts.countP (· ≤ r₁) = pre.length + 2 := by
          lia
        have hcount_r₂ : ts.countP (· ≤ r₂) = pre.length + 2 := by
          lia
        have hEq_next : rs = ((pre ++ [x]) ++ [r₁]) ++ r₂ :: rest := by
          simpa [List.append_assoc] using hEq
        have hr₂_root : f.IsRoot r₂ := isRoot_of_mem_sorted_roots_eq hrs_eq hEq_next
        have hFg₂_nonpos : F.eval r₂ * g.eval r₂ ≤ 0 := by
          simpa [F] using
            eval_mul_right_nonpos_of_isRoot (f := f) (g := g) (a := a) (b := b)
              hr₂_root (hb_nonpos r₂ hr₂_root)
        have hrs_len' : rs.length = pre.length + rest.length + 3 := by
          rw [hEq]
          simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        have hcount_gt : ts.countP (r₂ < ·) = rest.length + 2 := by
          have hsplit := countP_le_add_countP_gt_eq_length ts r₂
          rw [hcount_r₂, hoff, hrs_len'] at hsplit
          lia
        have hr₂_Froot : F.IsRoot r₂ := by
          rcases Nat.even_or_odd rest.length with heven | hodd
          · have hF_nonpos : F.eval r₂ ≤ 0 := by
              have hg_pos' : 0 < g.eval r₂ := (hgsign ((pre ++ [x]) ++ [r₁]) hEq_next).1 heven
              nlinarith [hFg₂_nonpos, hg_pos']
            have hcount_even : Even (ts.countP (r₂ < ·)) := by
              rw [hcount_gt]
              have hstep : Odd (rest.length + 1) := heven.add_odd odd_one
              have hfinal : Even ((rest.length + 1) + 1) := hstep.add_odd odd_one
              simpa [Nat.add_assoc] using hfinal
            exact isRoot_of_eval_nonpos_of_even_countP_gt hF hF_pos hts_eq hF_nonpos
              hcount_even
          · have hF_nonneg : 0 ≤ F.eval r₂ := by
              have hg_neg' : g.eval r₂ < 0 := (hgsign ((pre ++ [x]) ++ [r₁]) hEq_next).2 hodd
              nlinarith [hFg₂_nonpos, hg_neg']
            have hcount_odd : Odd (ts.countP (r₂ < ·)) := by
              rw [hcount_gt]
              have hstep : Even (rest.length + 1) := hodd.add_odd odd_one
              have hfinal : Odd ((rest.length + 1) + 1) := hstep.add_odd odd_one
              simpa [Nat.add_assoc] using hfinal
            exact isRoot_of_eval_nonneg_of_odd_countP_gt hF hF_pos hts_eq hF_nonneg
              hcount_odd
        have hr₂_mem : r₂ ∈ ts := by
          apply Multiset.mem_coe.mp
          rw [hts_eq]
          exact (mem_roots hF.1).mpr hr₂_Froot
        have hcount_strict : ts.countP (· ≤ r₁) < ts.countP (· ≤ r₂) := by
          apply countP_lt_countP_of_exists
          · intro y hy
            simp only [decide_eq_true_eq] at hy ⊢
            exact le_trans hy (le_of_lt hr₁_lt_r₂)
          · exact hr₂_mem
          · simp [not_le_of_gt hr₁_lt_r₂]
          · simp
        lia
  simpa [F] using
    prec_of_count_bounds_succ hf hF hrs_sorted hts_sorted hrs_eq hts_eq hdeg hhead hlt hle

/-- Generic weak-sign same-degree theorem: if `g ⊳ f`, `F` is real-rooted with
the same degree as `f`, and at every root of `f` the value `F(r)` has
nonpositive sign relative to `g(r)`, then `f ≺ F`. -/
theorem prec_of_interlaces_eval_mul_nonpos_same_of_no_common
    {f g F : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF : F ≠ 0 ∧ F.roots.card = F.natDegree)
    (hF_pos : HasPosLeadingCoeff F)
    (hdeg : F.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hroot_nonpos : ∀ r, f.IsRoot r → F.eval r * g.eval r ≤ 0) :
    Prec f F := by
  obtain ⟨hf, hg, _, rs, ss, hrs_sorted, _, hrs_eq, hss_eq, hint⟩ := hgf
  set ts := F.roots.sort (· ≤ ·)
  have hts_eq : (↑ts : Multiset ℝ) = F.roots := Multiset.sort_eq ..
  have hts_sorted : ts.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hrs_len : rs.length = f.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, hf.2]
  have hts_len : ts.length = F.natDegree := by
    rw [show ts = F.roots.sort (· ≤ ·) by rfl, Multiset.length_sort, hF.2]
  have hoff : ts.length = rs.length + 0 := by
    rw [hts_len, hrs_len, hdeg]
    simp
  have hstrict :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        r₁ < r₂ := by
    intro pre r₁ r₂ rest hEq
    exact lt_of_consecutive_of_interlaces_of_no_common hf hg hrs_eq hss_eq hint hEq hno
  have hgsign :=
    eval_sign_of_interlaces_root hg hg_pos hrs_sorted hrs_eq hss_eq hint hno
  have hroot_on_max :
      ∀ (pre : List ℝ) {r : ℝ} {rest : List ℝ},
        rs = pre ++ r :: rest →
        ts.countP (· ≤ r) = pre.length + 1 →
        F.IsRoot r := by
    intro pre r rest hEq hcount
    have hr_root : f.IsRoot r := isRoot_of_mem_sorted_roots_eq hrs_eq hEq
    exact isRoot_of_eq_max_countP_le_of_sign hF hF_pos hrs_eq hts_eq hoff
      (hroot_nonpos r hr_root) (hgsign pre hEq) hEq hcount
  have hcount_le :
      ∀ (pre : List ℝ) {r : ℝ} {rest : List ℝ},
        rs = pre ++ r :: rest →
        ts.countP (· ≤ r) ≤ pre.length + 1 :=
    countP_le_of_eq_max_isRoot (_f := f) hF hrs_sorted hts_eq hoff hstrict hroot_on_max
  have hlt :
      ∀ (pre : List ℝ) {r : ℝ} {rest : List ℝ},
        rs = pre ++ r :: rest →
        ts.countP (· < r) ≤ pre.length :=
    countP_lt_of_eq_max_isRoot (_f := f) (rs := rs) (off := 0)
      hF hts_eq hcount_le hroot_on_max
  have hle :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        pre.length < ts.countP (· ≤ r₂) := by
    intro pre r₁ r₂ rest hEq
    induction pre using List.reverseRecOn generalizing r₁ r₂ rest with
    | nil =>
        have hEq_next : rs = ([r₁] : List ℝ) ++ r₂ :: rest := by
          simpa using hEq
        have hr₂_root : f.IsRoot r₂ := isRoot_of_mem_sorted_roots_eq hrs_eq hEq_next
        have hFg₂_nonpos : F.eval r₂ * g.eval r₂ ≤ 0 := hroot_nonpos r₂ hr₂_root
        by_contra hnot
        have hcount_r₂ : ts.countP (· ≤ r₂) = 0 := by
          exact Nat.eq_zero_of_not_pos hnot
        have hrs_len : rs.length = rest.length + 2 := by
          rw [hEq]
          simp
        have hcount_gt : ts.countP (r₂ < ·) = rest.length + 2 := by
          have hsplit := countP_le_add_countP_gt_eq_length ts r₂
          rw [hcount_r₂, hoff, hrs_len] at hsplit
          simpa using hsplit
        have hr₂_Froot : F.IsRoot r₂ := by
          rcases Nat.even_or_odd rest.length with heven | hodd
          · have hF_nonpos : F.eval r₂ ≤ 0 := by
              have hg_pos' : 0 < g.eval r₂ := (hgsign [r₁] hEq_next).1 heven
              nlinarith [hFg₂_nonpos, hg_pos']
            have hcount_even : Even (ts.countP (r₂ < ·)) := by
              rw [hcount_gt]
              have hstep : Odd (rest.length + 1) := heven.add_odd odd_one
              have hfinal : Even ((rest.length + 1) + 1) := hstep.add_odd odd_one
              simpa [Nat.add_assoc] using hfinal
            exact isRoot_of_eval_nonpos_of_even_countP_gt hF hF_pos hts_eq hF_nonpos
              hcount_even
          · have hF_nonneg : 0 ≤ F.eval r₂ := by
              have hg_neg' : g.eval r₂ < 0 := (hgsign [r₁] hEq_next).2 hodd
              nlinarith [hFg₂_nonpos, hg_neg']
            have hcount_odd : Odd (ts.countP (r₂ < ·)) := by
              rw [hcount_gt]
              have hstep : Even (rest.length + 1) := hodd.add_odd odd_one
              have hfinal : Odd ((rest.length + 1) + 1) := hstep.add_odd odd_one
              simpa [Nat.add_assoc] using hfinal
            exact isRoot_of_eval_nonneg_of_odd_countP_gt hF hF_pos hts_eq hF_nonneg
              hcount_odd
        have hr₂_mem : r₂ ∈ ts := by
          apply Multiset.mem_coe.mp
          rw [hts_eq]
          exact (mem_roots hF.1).mpr hr₂_Froot
        have hcount_pos : 0 < ts.countP (· ≤ r₂) := by
          rw [List.countP_eq_length_filter]
          exact List.length_pos_of_mem <| List.mem_filter.mpr ⟨hr₂_mem, by simp⟩
        lia
    | append_singleton pre x ih =>
        have hEq_prev : rs = pre ++ x :: r₁ :: r₂ :: rest := by
          simpa [List.append_assoc] using hEq
        have hprev : pre.length < ts.countP (· ≤ r₁) := ih hEq_prev
        have hlen_pre : (pre ++ [x]).length = pre.length + 1 := by
          simp
        by_cases hgood : (pre ++ [x]).length < ts.countP (· ≤ r₂)
        · simpa using hgood
        · have hbad : ts.countP (· ≤ r₂) ≤ pre.length + 1 := by
            simpa [hlen_pre] using (Nat.not_lt.mp hgood)
          have hr₁_lt_r₂ : r₁ < r₂ := hstrict (pre ++ [x]) hEq
          have hmono : ts.countP (· ≤ r₁) ≤ ts.countP (· ≤ r₂) := by
            exact List.countP_mono_left <| by
              intro x _ hx
              simp only [decide_eq_true_eq] at hx ⊢
              exact le_trans hx (le_of_lt hr₁_lt_r₂)
          have hcount_r₁ : ts.countP (· ≤ r₁) = pre.length + 1 := by
            lia
          have hcount_r₂ : ts.countP (· ≤ r₂) = pre.length + 1 := by
            lia
          have hEq_next : rs = ((pre ++ [x]) ++ [r₁]) ++ r₂ :: rest := by
            simpa [List.append_assoc] using hEq
          have hr₂_root : f.IsRoot r₂ := isRoot_of_mem_sorted_roots_eq hrs_eq hEq_next
          have hFg₂_nonpos : F.eval r₂ * g.eval r₂ ≤ 0 := hroot_nonpos r₂ hr₂_root
          have hrs_len : rs.length = pre.length + rest.length + 3 := by
            rw [hEq]
            simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
          have hcount_gt : ts.countP (r₂ < ·) = rest.length + 2 := by
            have hsplit := countP_le_add_countP_gt_eq_length ts r₂
            rw [hcount_r₂, hoff, hrs_len] at hsplit
            lia
          have hr₂_Froot : F.IsRoot r₂ := by
            rcases Nat.even_or_odd rest.length with heven | hodd
            · have hF_nonpos : F.eval r₂ ≤ 0 := by
                have hg_pos' : 0 < g.eval r₂ := (hgsign ((pre ++ [x]) ++ [r₁]) hEq_next).1 heven
                nlinarith [hFg₂_nonpos, hg_pos']
              have hcount_even : Even (ts.countP (r₂ < ·)) := by
                rw [hcount_gt]
                have hstep : Odd (rest.length + 1) := heven.add_odd odd_one
                have hfinal : Even ((rest.length + 1) + 1) := hstep.add_odd odd_one
                simpa [Nat.add_assoc] using hfinal
              exact isRoot_of_eval_nonpos_of_even_countP_gt hF hF_pos hts_eq hF_nonpos
                hcount_even
            · have hF_nonneg : 0 ≤ F.eval r₂ := by
                have hg_neg' : g.eval r₂ < 0 := (hgsign ((pre ++ [x]) ++ [r₁]) hEq_next).2 hodd
                nlinarith [hFg₂_nonpos, hg_neg']
              have hcount_odd : Odd (ts.countP (r₂ < ·)) := by
                rw [hcount_gt]
                have hstep : Even (rest.length + 1) := hodd.add_odd odd_one
                have hfinal : Odd ((rest.length + 1) + 1) := hstep.add_odd odd_one
                simpa [Nat.add_assoc] using hfinal
              exact isRoot_of_eval_nonneg_of_odd_countP_gt hF hF_pos hts_eq hF_nonneg
                hcount_odd
          have hr₂_mem : r₂ ∈ ts := by
            apply Multiset.mem_coe.mp
            rw [hts_eq]
            exact (mem_roots hF.1).mpr hr₂_Froot
          have hcount_strict : ts.countP (· ≤ r₁) < ts.countP (· ≤ r₂) := by
            apply countP_lt_countP_of_exists
            · intro x hx
              simp only [decide_eq_true_eq] at hx ⊢
              exact le_trans hx (le_of_lt hr₁_lt_r₂)
            · exact hr₂_mem
            · simp [not_le_of_gt hr₁_lt_r₂]
            · simp
          lia
  exact
    prec_of_count_bounds_same hf hF hrs_sorted hts_sorted hrs_eq hts_eq hdeg hlt hle

/-- Generic weak-sign differ-by-1 theorem: if `g ⊳ f`, `F` is real-rooted with
degree `deg(f)+1`, and at every root of `f` the value `F(r)` has nonpositive
sign relative to `g(r)`, then `f ⊳ F`. -/
theorem prec_of_interlaces_eval_mul_nonpos_succ_of_no_common
    {f g F : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF : F ≠ 0 ∧ F.roots.card = F.natDegree)
    (hF_pos : HasPosLeadingCoeff F)
    (hdeg : F.natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hroot_nonpos : ∀ r, f.IsRoot r → F.eval r * g.eval r ≤ 0) :
    Prec f F := by
  obtain ⟨hf, hg, _, rs, ss, hrs_sorted, _, hrs_eq, hss_eq, hint⟩ := hgf
  set ts := F.roots.sort (· ≤ ·)
  have hts_eq : (↑ts : Multiset ℝ) = F.roots := Multiset.sort_eq ..
  have hts_sorted : ts.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hrs_len : rs.length = f.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, hf.2]
  have hts_len : ts.length = F.natDegree := by
    rw [show ts = F.roots.sort (· ≤ ·) by rfl, Multiset.length_sort, hF.2]
  have hoff : ts.length = rs.length + 1 := by
    rw [hts_len, hrs_len, hdeg]
  have hstrict :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        r₁ < r₂ := by
    intro pre r₁ r₂ rest hEq
    exact lt_of_consecutive_of_interlaces_of_no_common hf hg hrs_eq hss_eq hint hEq hno
  have hgsign :=
    eval_sign_of_interlaces_root hg hg_pos hrs_sorted hrs_eq hss_eq hint hno
  have hroot_on_max :
      ∀ (pre : List ℝ) {r : ℝ} {rest : List ℝ},
        rs = pre ++ r :: rest →
        ts.countP (· ≤ r) = pre.length + 2 →
        F.IsRoot r := by
    intro pre r rest hEq hcount
    have hr_root : f.IsRoot r := isRoot_of_mem_sorted_roots_eq hrs_eq hEq
    exact isRoot_of_eq_max_countP_le_of_sign hF hF_pos hrs_eq hts_eq hoff
      (hroot_nonpos r hr_root) (hgsign pre hEq) hEq hcount
  have hcount_le :
      ∀ (pre : List ℝ) {r : ℝ} {rest : List ℝ},
        rs = pre ++ r :: rest →
        ts.countP (· ≤ r) ≤ pre.length + 2 :=
    countP_le_of_eq_max_isRoot (_f := f) hF hrs_sorted hts_eq hoff hstrict hroot_on_max
  have hlt :
      ∀ (pre : List ℝ) {r : ℝ} {rest : List ℝ},
        rs = pre ++ r :: rest →
        ts.countP (· < r) ≤ pre.length + 1 :=
    countP_lt_of_eq_max_isRoot (_f := f) (rs := rs) (off := 1)
      hF hts_eq hcount_le hroot_on_max
  have hhead :
      ∀ {r : ℝ} {rest : List ℝ},
        rs = r :: rest →
        0 < ts.countP (· ≤ r) := by
    intro r rest hEq
    have hEq' : rs = ([] : List ℝ) ++ r :: rest := by
      simpa using hEq
    have hr_root : f.IsRoot r := isRoot_of_mem_sorted_roots_eq hrs_eq hEq'
    have hFg_nonpos : F.eval r * g.eval r ≤ 0 := hroot_nonpos r hr_root
    by_contra hnot
    have hcount_r : ts.countP (· ≤ r) = 0 := by
      exact Nat.eq_zero_of_not_pos hnot
    have hrs_len' : rs.length = rest.length + 1 := by
      rw [hEq]
      simp
    have hcount_gt : ts.countP (r < ·) = rest.length + 2 := by
      have hsplit := countP_le_add_countP_gt_eq_length ts r
      rw [hcount_r, hoff, hrs_len'] at hsplit
      simpa using hsplit
    have hr_Froot : F.IsRoot r := by
      rcases Nat.even_or_odd rest.length with heven | hodd
      · have hF_nonpos : F.eval r ≤ 0 := by
          have hg_pos' : 0 < g.eval r := (hgsign [] hEq).1 heven
          nlinarith [hFg_nonpos, hg_pos']
        have hcount_even : Even (ts.countP (r < ·)) := by
          rw [hcount_gt]
          have hstep : Odd (rest.length + 1) := heven.add_odd odd_one
          have hfinal : Even ((rest.length + 1) + 1) := hstep.add_odd odd_one
          simpa [Nat.add_assoc] using hfinal
        exact isRoot_of_eval_nonpos_of_even_countP_gt hF hF_pos hts_eq hF_nonpos
          hcount_even
      · have hF_nonneg : 0 ≤ F.eval r := by
          have hg_neg' : g.eval r < 0 := (hgsign [] hEq).2 hodd
          nlinarith [hFg_nonpos, hg_neg']
        have hcount_odd : Odd (ts.countP (r < ·)) := by
          rw [hcount_gt]
          have hstep : Even (rest.length + 1) := hodd.add_odd odd_one
          have hfinal : Odd ((rest.length + 1) + 1) := hstep.add_odd odd_one
          simpa [Nat.add_assoc] using hfinal
        exact isRoot_of_eval_nonneg_of_odd_countP_gt hF hF_pos hts_eq hF_nonneg
          hcount_odd
    have hr_mem : r ∈ ts := by
      apply Multiset.mem_coe.mp
      rw [hts_eq]
      exact (mem_roots hF.1).mpr hr_Froot
    have hcount_pos : 0 < ts.countP (· ≤ r) := by
      rw [List.countP_eq_length_filter]
      exact List.length_pos_of_mem <| List.mem_filter.mpr ⟨hr_mem, by simp⟩
    lia
  have hle :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        pre.length + 1 < ts.countP (· ≤ r₂) := by
    intro pre r₁ r₂ rest hEq
    induction pre using List.reverseRecOn generalizing r₁ r₂ rest with
    | nil =>
        have hEq_head : rs = r₁ :: r₂ :: rest := by
          simpa using hEq
        have hhead_r₁ : 0 < ts.countP (· ≤ r₁) := hhead hEq_head
        by_contra hnot
        have hbad : ts.countP (· ≤ r₂) ≤ 1 := by
          exact Nat.not_lt.mp hnot
        have hr₁_lt_r₂ : r₁ < r₂ := hstrict [] hEq
        have hmono : ts.countP (· ≤ r₁) ≤ ts.countP (· ≤ r₂) := by
          exact List.countP_mono_left <| by
            intro y _ hy
            simp only [decide_eq_true_eq] at hy ⊢
            exact le_trans hy (le_of_lt hr₁_lt_r₂)
        have hcount_r₁ : ts.countP (· ≤ r₁) = 1 := by
          lia
        have hcount_r₂ : ts.countP (· ≤ r₂) = 1 := by
          lia
        have hEq_next : rs = ([r₁] : List ℝ) ++ r₂ :: rest := by
          simpa using hEq
        have hr₂_root : f.IsRoot r₂ := isRoot_of_mem_sorted_roots_eq hrs_eq hEq_next
        have hFg₂_nonpos : F.eval r₂ * g.eval r₂ ≤ 0 := hroot_nonpos r₂ hr₂_root
        have hrs_len' : rs.length = rest.length + 2 := by
          rw [hEq]
          simp
        have hcount_gt : ts.countP (r₂ < ·) = rest.length + 2 := by
          have hsplit := countP_le_add_countP_gt_eq_length ts r₂
          rw [hcount_r₂, hoff, hrs_len'] at hsplit
          lia
        have hr₂_Froot : F.IsRoot r₂ := by
          rcases Nat.even_or_odd rest.length with heven | hodd
          · have hF_nonpos : F.eval r₂ ≤ 0 := by
              have hg_pos' : 0 < g.eval r₂ := (hgsign [r₁] hEq_next).1 heven
              nlinarith [hFg₂_nonpos, hg_pos']
            have hcount_even : Even (ts.countP (r₂ < ·)) := by
              rw [hcount_gt]
              have hstep : Odd (rest.length + 1) := heven.add_odd odd_one
              have hfinal : Even ((rest.length + 1) + 1) := hstep.add_odd odd_one
              simpa [Nat.add_assoc] using hfinal
            exact isRoot_of_eval_nonpos_of_even_countP_gt hF hF_pos hts_eq hF_nonpos
              hcount_even
          · have hF_nonneg : 0 ≤ F.eval r₂ := by
              have hg_neg' : g.eval r₂ < 0 := (hgsign [r₁] hEq_next).2 hodd
              nlinarith [hFg₂_nonpos, hg_neg']
            have hcount_odd : Odd (ts.countP (r₂ < ·)) := by
              rw [hcount_gt]
              have hstep : Even (rest.length + 1) := hodd.add_odd odd_one
              have hfinal : Odd ((rest.length + 1) + 1) := hstep.add_odd odd_one
              simpa [Nat.add_assoc] using hfinal
            exact isRoot_of_eval_nonneg_of_odd_countP_gt hF hF_pos hts_eq hF_nonneg
              hcount_odd
        have hr₂_mem : r₂ ∈ ts := by
          apply Multiset.mem_coe.mp
          rw [hts_eq]
          exact (mem_roots hF.1).mpr hr₂_Froot
        have hcount_strict : ts.countP (· ≤ r₁) < ts.countP (· ≤ r₂) := by
          apply countP_lt_countP_of_exists
          · intro y hy
            simp only [decide_eq_true_eq] at hy ⊢
            exact le_trans hy (le_of_lt hr₁_lt_r₂)
          · exact hr₂_mem
          · simp [not_le_of_gt hr₁_lt_r₂]
          · simp
        lia
    | append_singleton pre x ih =>
        have hEq_prev : rs = pre ++ x :: r₁ :: r₂ :: rest := by
          simpa [List.append_assoc] using hEq
        have hprev : pre.length + 1 < ts.countP (· ≤ r₁) := ih hEq_prev
        have hlen_pre : (pre ++ [x]).length + 1 = pre.length + 2 := by
          simp
        by_cases hgood : (pre ++ [x]).length + 1 < ts.countP (· ≤ r₂)
        · simpa [hlen_pre] using hgood
        have hr₁_lt_r₂ : r₁ < r₂ := hstrict (pre ++ [x]) hEq
        have hmono : ts.countP (· ≤ r₁) ≤ ts.countP (· ≤ r₂) := by
          exact List.countP_mono_left <| by
            intro y _ hy
            simp only [decide_eq_true_eq] at hy ⊢
            exact le_trans hy (le_of_lt hr₁_lt_r₂)
        have hbad : ts.countP (· ≤ r₂) ≤ pre.length + 2 := by
          simpa [hlen_pre] using (Nat.not_lt.mp hgood)
        have hcount_r₁ : ts.countP (· ≤ r₁) = pre.length + 2 := by
          lia
        have hcount_r₂ : ts.countP (· ≤ r₂) = pre.length + 2 := by
          lia
        have hEq_next : rs = ((pre ++ [x]) ++ [r₁]) ++ r₂ :: rest := by
          simpa [List.append_assoc] using hEq
        have hr₂_root : f.IsRoot r₂ := isRoot_of_mem_sorted_roots_eq hrs_eq hEq_next
        have hFg₂_nonpos : F.eval r₂ * g.eval r₂ ≤ 0 := hroot_nonpos r₂ hr₂_root
        have hrs_len' : rs.length = pre.length + rest.length + 3 := by
          rw [hEq]
          simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        have hcount_gt : ts.countP (r₂ < ·) = rest.length + 2 := by
          have hsplit := countP_le_add_countP_gt_eq_length ts r₂
          rw [hcount_r₂, hoff, hrs_len'] at hsplit
          lia
        have hr₂_Froot : F.IsRoot r₂ := by
          rcases Nat.even_or_odd rest.length with heven | hodd
          · have hF_nonpos : F.eval r₂ ≤ 0 := by
              have hg_pos' : 0 < g.eval r₂ := (hgsign ((pre ++ [x]) ++ [r₁]) hEq_next).1 heven
              nlinarith [hFg₂_nonpos, hg_pos']
            have hcount_even : Even (ts.countP (r₂ < ·)) := by
              rw [hcount_gt]
              have hstep : Odd (rest.length + 1) := heven.add_odd odd_one
              have hfinal : Even ((rest.length + 1) + 1) := hstep.add_odd odd_one
              simpa [Nat.add_assoc] using hfinal
            exact isRoot_of_eval_nonpos_of_even_countP_gt hF hF_pos hts_eq hF_nonpos
              hcount_even
          · have hF_nonneg : 0 ≤ F.eval r₂ := by
              have hg_neg' : g.eval r₂ < 0 := (hgsign ((pre ++ [x]) ++ [r₁]) hEq_next).2 hodd
              nlinarith [hFg₂_nonpos, hg_neg']
            have hcount_odd : Odd (ts.countP (r₂ < ·)) := by
              rw [hcount_gt]
              have hstep : Even (rest.length + 1) := hodd.add_odd odd_one
              have hfinal : Odd ((rest.length + 1) + 1) := hstep.add_odd odd_one
              simpa [Nat.add_assoc] using hfinal
            exact isRoot_of_eval_nonneg_of_odd_countP_gt hF hF_pos hts_eq hF_nonneg
              hcount_odd
        have hr₂_mem : r₂ ∈ ts := by
          apply Multiset.mem_coe.mp
          rw [hts_eq]
          exact (mem_roots hF.1).mpr hr₂_Froot
        have hcount_strict : ts.countP (· ≤ r₁) < ts.countP (· ≤ r₂) := by
          apply countP_lt_countP_of_exists
          · intro y hy
            simp only [decide_eq_true_eq] at hy ⊢
            exact le_trans hy (le_of_lt hr₁_lt_r₂)
          · exact hr₂_mem
          · simp [not_le_of_gt hr₁_lt_r₂]
          · simp
        lia
  exact
    prec_of_count_bounds_succ hf hF hrs_sorted hts_sorted hrs_eq hts_eq hdeg hhead hlt hle

/-- Degree-bounded generic weak-sign theorem in the no-common-roots regime. -/
theorem prec_of_interlaces_eval_mul_nonpos_of_no_common
    {f g F : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF : F ≠ 0 ∧ F.roots.card = F.natDegree)
    (hF_pos : HasPosLeadingCoeff F)
    (hdeg_lo : f.natDegree ≤ F.natDegree)
    (hdeg_hi : F.natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hroot_nonpos : ∀ r, f.IsRoot r → F.eval r * g.eval r ≤ 0) :
    Prec f F := by
  have hcases : F.natDegree = f.natDegree ∨ F.natDegree = f.natDegree + 1 := by
    lia
  rcases hcases with hsame | hsucc
  · exact
      prec_of_interlaces_eval_mul_nonpos_same_of_no_common
        hgf hg_pos hF hF_pos hsame hno hroot_nonpos
  · exact
      prec_of_interlaces_eval_mul_nonpos_succ_of_no_common
        hgf hg_pos hF hF_pos hsucc hno hroot_nonpos

/-- Degree-bounded structured Liu--Wang theorem in the weak-sign regime. -/
theorem prec_of_interlaces_evalCoeff_nonpos
    {f g a b : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hF_pos : HasPosLeadingCoeff (a * f + b * g))
    (hdeg_lo : f.natDegree ≤ (a * f + b * g).natDegree)
    (hdeg_hi : (a * f + b * g).natDegree ≤ f.natDegree + 1)
    (hb_nonpos : ∀ r, f.IsRoot r → b.eval r ≤ 0) :
    Prec f (a * f + b * g) := by
  classical
  refine
    Nat.strong_induction_on
      (p := fun n =>
        ∀ {f g a b : ℝ[X]},
          f.natDegree = n →
          Interlaces g f →
          HasPosLeadingCoeff g →
          HasPosLeadingCoeff (a * f + b * g) →
          f.natDegree ≤ (a * f + b * g).natDegree →
          (a * f + b * g).natDegree ≤ f.natDegree + 1 →
          (∀ r, f.IsRoot r → b.eval r ≤ 0) →
          Prec f (a * f + b * g))
      f.natDegree ?_ rfl hgf hg_pos hF_pos hdeg_lo hdeg_hi hb_nonpos
  intro n ih f g a b hfdeg hgf hg_pos hF_pos hdeg_lo hdeg_hi hb_nonpos
  by_cases hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r
  · have hcases :
        (a * f + b * g).natDegree = f.natDegree ∨
          (a * f + b * g).natDegree = f.natDegree + 1 := by
      lia
    rcases hcases with hsame | hsucc
    · exact
        prec_of_interlaces_evalCoeff_nonpos_same_of_no_common
          hgf hg_pos hF_pos hsame hno hb_nonpos
    · exact
        prec_of_interlaces_evalCoeff_nonpos_succ_of_no_common
          hgf hg_pos hF_pos hsucc hno hb_nonpos
  · push Not at hno
    rcases hno with ⟨r, hrf, hrg⟩
    obtain ⟨qf, qg, hqf, hqg, hqinter, hqg_pos, hqF_pos, hqdeg_lo, hqdeg_hi, hq_nonpos⟩ :=
      common_root_reduction_data hgf hg_pos hF_pos hdeg_lo hdeg_hi hb_nonpos hrf hrg
    obtain ⟨hf, _, _, _, _, _, _, _, _, _⟩ := hgf
    have hqf_ne : qf ≠ 0 := by
      exact right_ne_zero_of_mul (by simpa [hqf] using hf.1)
    have hqf_deg_lt : qf.natDegree < n := by
      rw [← hfdeg, hqf, natDegree_mul (X_sub_C_ne_zero r) hqf_ne, natDegree_X_sub_C]
      lia
    have hprec_q : Prec qf (a * qf + b * qg) := by
      exact ih qf.natDegree hqf_deg_lt rfl hqinter hqg_pos hqF_pos hqdeg_lo hqdeg_hi hq_nonpos
    have hprec_mul :
        Prec ((X - C r) * qf) (a * ((X - C r) * qf) + b * ((X - C r) * qg)) :=
      prec_mul_X_sub_C_of_linearCombo_quotient (a := a) (b := b) (r := r) hprec_q
    simpa [hqf, hqg] using hprec_mul

/-- Derivative specialization of the Liu--Wang mixed theorem in the degree `+1`
case. The hypothesis is the strict root-sign condition naturally obtained from
`F(r) = v(r) f'(r)`. -/
theorem prec_ma_wang_succ {f u v : ℝ[X]}
    (hf : f ≠ 0 ∧ f.roots.card = f.natDegree)
    (hdegf : 2 ≤ f.natDegree)
    (hdeg : (u * f + v * f.derivative).natDegree = f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + v * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hroot_sign : ∀ r, f.IsRoot r → v.eval r * (f.derivative.eval r) ^ 2 < 0) :
    Prec f (u * f + v * f.derivative) := by
  have hder : Interlaces f.derivative f := derivative_interlaces hf hdegf
  have hf'_pos : HasPosLeadingCoeff f.derivative :=
    hasPosLeadingCoeff_derivative hf_pos (by lia)
  refine prec_of_interlaces_eval_mul_neg_succ hder hf'_pos hF_pos hdeg ?_
  intro r hr
  rw [eval_mul_derivative_eq_of_isRoot hr]
  exact hroot_sign r hr

/-- Derivative specialization of the Liu--Wang mixed theorem in the same-degree
case. The hypothesis is the strict root-sign condition naturally obtained from
`F(r) = v(r) f'(r)`. -/
theorem prec_ma_wang_same {f u v : ℝ[X]}
    (hf : f ≠ 0 ∧ f.roots.card = f.natDegree)
    (hdegf : 2 ≤ f.natDegree)
    (hdeg : (u * f + v * f.derivative).natDegree = f.natDegree)
    (hF_pos : HasPosLeadingCoeff (u * f + v * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hroot_sign : ∀ r, f.IsRoot r → v.eval r * (f.derivative.eval r) ^ 2 < 0) :
    Prec f (u * f + v * f.derivative) := by
  have hder : Interlaces f.derivative f := derivative_interlaces hf hdegf
  have hf'_pos : HasPosLeadingCoeff f.derivative :=
    hasPosLeadingCoeff_derivative hf_pos (by lia)
  refine prec_of_interlaces_eval_mul_neg_same hder hf'_pos hF_pos hdeg ?_
  intro r hr
  rw [eval_mul_derivative_eq_of_isRoot hr]
  exact hroot_sign r hr

/-- Derivative specialization of the Liu--Wang mixed theorem allowing either the
same-degree or degree `+1` outcome. -/
theorem prec_ma_wang {f u v : ℝ[X]}
    (hf : f ≠ 0 ∧ f.roots.card = f.natDegree)
    (hdegf : 2 ≤ f.natDegree)
    (hdeg_lo : f.natDegree ≤ (u * f + v * f.derivative).natDegree)
    (hdeg_hi : (u * f + v * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + v * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hroot_sign : ∀ r, f.IsRoot r → v.eval r * (f.derivative.eval r) ^ 2 < 0) :
    Prec f (u * f + v * f.derivative) := by
  have hcases :
      (u * f + v * f.derivative).natDegree = f.natDegree ∨
        (u * f + v * f.derivative).natDegree = f.natDegree + 1 := by
    lia
  cases hcases with
  | inl hsame =>
      exact prec_ma_wang_same hf hdegf hsame hF_pos hf_pos hroot_sign
  | inr hsucc =>
      exact prec_ma_wang_succ hf hdegf hsucc hF_pos hf_pos hroot_sign

end
end RealRooted
