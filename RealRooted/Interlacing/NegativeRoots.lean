import RealRooted.WagnerRightSum

/-!
# Negative-root consequences of interlacing

This module centralizes list and polynomial lemmas for transporting strict
negative-root bounds through `Interlaces` and same-degree `Prec` relations.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- A list product is positive when all of its factors are positive. -/
lemma list_prod_pos_of_forall_pos :
    ∀ {l : List ℝ}, (∀ x ∈ l, 0 < x) → 0 < l.prod
  | [], _ => by simp
  | x :: xs, h => by
      have hx : 0 < x := h x (by simp)
      have hxs : 0 < xs.prod :=
        list_prod_pos_of_forall_pos (fun y hy => h y (by simp [hy]))
      simp_all

/-- All but the rightmost entry of the longer row in an interlacing are
strictly negative when every entry of the shorter row is strictly negative. -/
lemma listInterlaces_dropLast_lt_zero_of_forall_lt_zero :
    ∀ {ss rs : List ℝ},
      ListInterlaces ss rs →
      (∀ s ∈ ss, s < 0) →
      ∀ r ∈ rs.dropLast, r < 0
  | [], [], _, _, _, hr => by simp at hr
  | [], [_], _, _, _, hr => by simp at hr
  | s :: ss, r₁ :: r₂ :: rs, hint, hss, r, hr => by
      obtain ⟨hr₁s, _, htail⟩ := hint
      rw [List.dropLast_cons_cons] at hr
      rcases List.mem_cons.mp hr with rfl | hr'
      · exact lt_of_le_of_lt hr₁s (hss s (by simp))
      · exact listInterlaces_dropLast_lt_zero_of_forall_lt_zero htail
          (fun x hx => hss x (by simp [hx])) r hr'
  | [], _ :: _ :: _, hint, _, _, _ => by simp [ListInterlaces] at hint
  | _ :: _, [], hint, _, _, _ => by simp [ListInterlaces] at hint
  | _ :: _, [_], hint, _, _, _ => by simp [ListInterlaces] at hint

/-- A positive value at zero forces the rightmost root of the longer member
of a strict negative-root interlacing to remain strictly negative. -/
theorem roots_neg_of_interlaces_of_eval_zero_pos {g f : ℝ[X]}
    (hgf : Interlaces g f)
    (hf_pos : HasPosLeadingCoeff f)
    (hf_zero : 0 < f.eval 0)
    (hg_neg : ∀ r, g.IsRoot r → r < 0) :
    ∀ r, f.IsRoot r → r < 0 := by
  obtain ⟨hf, hg, _, rs, ss, _, _, hrs_eq, hss_eq, hint⟩ := hgf
  have hrs_len : rs.length = f.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hf.2]
  have hrs_ne : rs ≠ [] := by grind
  have hss_neg : ∀ s ∈ ss, s < 0 := by
    intro s hs
    have hs_root : g.IsRoot s := (mem_roots hg.1).mp <| by
      simpa [hss_eq] using Multiset.mem_coe.mpr hs
    exact hg_neg s hs_root
  have hrs_drop_neg : ∀ r ∈ rs.dropLast, r < 0 :=
    listInterlaces_dropLast_lt_zero_of_forall_lt_zero hint hss_neg
  have h_eval :
      f.eval 0 = f.leadingCoeff * (rs.map (0 - ·)).prod := by
    rw [eval_eq_leadingCoeff_mul_prod_sub hf.2 0, ← hrs_eq]
    simp
  have hrs_drop_prod_pos : 0 < (rs.dropLast.map (0 - ·)).prod :=
    list_prod_pos_of_forall_pos (by grind)
  have hlast_neg : rs.getLast hrs_ne < 0 := by
    have hf_zero' := hf_zero
    rw [h_eval, ← List.dropLast_append_getLast hrs_ne, List.map_append,
      List.prod_append] at hf_zero'
    simp only [List.map, List.prod_singleton] at hf_zero'
    have hmid :
        0 < (rs.dropLast.map (0 - ·)).prod * (0 - rs.getLast hrs_ne) :=
      (mul_pos_iff_of_pos_left hf_pos).mp hf_zero'
    have hfactor : 0 < 0 - rs.getLast hrs_ne :=
      (mul_pos_iff_of_pos_left hrs_drop_prod_pos).mp hmid
    linarith
  intro r hr
  have hr_mem : r ∈ rs := Multiset.mem_coe.mp (by simp_all)
  by_cases hr_last : r = rs.getLast hrs_ne
  · lia
  · have hr_drop : r ∈ rs.dropLast :=
      List.mem_dropLast_of_mem_of_ne_getLast hr_mem hr_last
    exact hrs_drop_neg r hr_drop

/-- If the shorter row has strictly negative roots and the longer row has a
zero root, every root of the longer row is nonpositive. -/
theorem roots_nonpos_of_interlaces_of_zero_root_of_roots_neg {g f : ℝ[X]}
    (hgf : Interlaces g f)
    (hzero : f.IsRoot 0)
    (hg_neg : ∀ r, g.IsRoot r → r < 0) :
    ∀ r, f.IsRoot r → r ≤ 0 := by
  obtain ⟨hf, hg, _, rs, ss, _, _, hrs_eq, hss_eq, hint⟩ := hgf
  have hzero_mem : 0 ∈ rs := Multiset.mem_coe.mp (by simp_all)
  have hrs_ne : rs ≠ [] := by grind
  have hss_neg : ∀ s ∈ ss, s < 0 := by
    intro s hs
    have hs_root : g.IsRoot s := (mem_roots hg.1).mp <| by
      simpa [hss_eq] using Multiset.mem_coe.mpr hs
    exact hg_neg s hs_root
  have hrs_drop_neg : ∀ r ∈ rs.dropLast, r < 0 :=
    listInterlaces_dropLast_lt_zero_of_forall_lt_zero hint hss_neg
  have hlast_zero : rs.getLast hrs_ne = 0 := by
    by_contra hlast_ne
    have hzero_drop : 0 ∈ rs.dropLast :=
      List.mem_dropLast_of_mem_of_ne_getLast hzero_mem (by lia)
    exact (ne_of_lt (hrs_drop_neg 0 hzero_drop)) rfl
  intro r hr
  have hr_mem : r ∈ rs := Multiset.mem_coe.mp (by simp_all)
  by_cases hr_last : r = rs.getLast hrs_ne
  · simp [hr_last, hlast_zero]
  · exact (hrs_drop_neg r
      (List.mem_dropLast_of_mem_of_ne_getLast hr_mem hr_last)).le

/-- A negative bound on the right row of an interlacing transfers to the left
row. -/
lemma listInterlaces_left_lt_of_right_lt :
    ∀ {ss rs : List ℝ},
      ListInterlaces ss rs →
      (∀ r ∈ rs, r < 0) →
      ∀ s ∈ ss, s < 0
  | [], [], _, _, _, hs => by simp at hs
  | [], [_], _, _, _, hs => by simp at hs
  | s :: ss, r₁ :: r₂ :: rs, hint, hrs_neg, t, ht => by
      obtain ⟨_, hs_r₂, htail⟩ := hint
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact lt_of_le_of_lt hs_r₂ (hrs_neg r₂ (by simp))
      · exact listInterlaces_left_lt_of_right_lt htail
          (fun u hu => hrs_neg u (by simp [hu])) t ht'
  | [], _ :: _ :: _, hint, _, _, _ => by simp [ListInterlaces] at hint
  | _ :: _, [], hint, _, _, _ => by cases hint
  | _ :: _, [_], hint, _, _, _ => by cases hint

/-- Strict negativity of every root of the longer member of an interlacing
forces strict negativity of every root of the shorter member. -/
theorem roots_neg_of_interlaces_of_right_roots_neg {g f : ℝ[X]}
    (hgf : Interlaces g f)
    (hf_neg : ∀ r, f.IsRoot r → r < 0) :
    ∀ r, g.IsRoot r → r < 0 := by
  obtain ⟨hf, hg, _, rs, ss, _, _, hrs_eq, hss_eq, hint⟩ := hgf
  have hrs_neg : ∀ r ∈ rs, r < 0 := by
    intro r hr
    apply hf_neg r
    apply (Polynomial.mem_roots hf.1).mp
    simpa [hrs_eq] using Multiset.mem_coe.mpr hr
  have hss_neg : ∀ s ∈ ss, s < 0 :=
    listInterlaces_left_lt_of_right_lt hint hrs_neg
  intro r hr
  apply hss_neg r
  apply Multiset.mem_coe.mp
  simp_all

/-- A negative bound on the right row of a same-length alternation transfers
to the left row. -/
lemma listAlternates_left_lt_of_right_lt :
    ∀ {ss rs : List ℝ},
      ListAlternates ss rs →
      (∀ r ∈ rs, r < 0) →
      ∀ s ∈ ss, s < 0
  | [], [], _, _, _, hs => by simp at hs
  | s :: ss, r :: rs, halt, hrs_neg, t, ht => by
      obtain ⟨hsr, hint⟩ := halt
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact lt_of_le_of_lt hsr (hrs_neg r (by simp))
      · exact listInterlaces_left_lt_of_right_lt hint
          (fun u hu => hrs_neg u (by lia)) t ht'
  | [], _ :: _, halt, _, _, _ => by simp_all
  | _ :: _, [], halt, _, _, _ => by cases halt

/-- In an equal-length alternation, every right-row entry except the last is
strictly negative when every left-row entry is strictly negative. -/
lemma listAlternates_dropLast_right_lt_zero_of_left_lt_zero :
    ∀ {ss rs : List ℝ},
      ListAlternates ss rs →
      (∀ s ∈ ss, s < 0) →
      ∀ r ∈ rs.dropLast, r < 0
  | [], [], _, _, _, hr => by simp at hr
  | s :: ss, r :: rs, halt, hss_neg, t, ht => by
      obtain ⟨_, hint⟩ := halt
      cases rs with
      | nil => simp at ht
      | cons r₂ rs' =>
          cases ss with
          | nil => simp [ListInterlaces] at hint
          | cons s₂ ss' =>
              obtain ⟨hr_s₂, hs₂_r₂, htail⟩ := hint
              rw [List.dropLast_cons_cons] at ht
              rcases List.mem_cons.mp ht with rfl | ht'
              · exact lt_of_le_of_lt hr_s₂ (hss_neg s₂ (by simp))
              · have haltTail : ListAlternates (s₂ :: ss') (r₂ :: rs') := by
                  change s₂ ≤ r₂ ∧ ListInterlaces ss' (r₂ :: rs')
                  exact ⟨hs₂_r₂, htail⟩
                exact listAlternates_dropLast_right_lt_zero_of_left_lt_zero
                  haltTail (fun u hu => hss_neg u (by simp [hu])) t ht'
  | [], _ :: _, halt, _, _, _ => by simp [ListAlternates] at halt
  | _ :: _, [], halt, _, _, _ => by simp [ListAlternates] at halt

/-- In a same-degree proper-position pair, a zero root of the right
polynomial must be its rightmost root when every root of the left polynomial
is strictly negative; hence all right roots are nonpositive. -/
theorem roots_nonpos_of_prec_sameDegree_of_zero_root_of_left_roots_neg
    {f g : ℝ[X]}
    (hfg : Prec f g)
    (hdeg : f.natDegree = g.natDegree)
    (hzero : g.IsRoot 0)
    (hf_neg : ∀ r, f.IsRoot r → r < 0) :
    ∀ r, g.IsRoot r → r ≤ 0 := by
  obtain ⟨hf, hg, ss, rs, _, _, hss_eq, hrs_eq, hshape⟩ := hfg
  have hss_len : ss.length = f.natDegree := by
    rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hf.2]
  have hrs_len : rs.length = g.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hg.2]
  have halt : ListAlternates ss rs := by
    rcases hshape with ⟨_, hint⟩ | ⟨_, halt⟩
    · lia
    · exact halt
  have hzero_mem : 0 ∈ rs := Multiset.mem_coe.mp (by simp_all)
  have hrs_ne : rs ≠ [] := by grind
  have hss_neg : ∀ s ∈ ss, s < 0 := by
    intro s hs
    apply hf_neg s
    apply (Polynomial.mem_roots hf.1).mp
    simpa [hss_eq] using Multiset.mem_coe.mpr hs
  have hrs_drop_neg : ∀ r ∈ rs.dropLast, r < 0 :=
    listAlternates_dropLast_right_lt_zero_of_left_lt_zero halt hss_neg
  have hlast_zero : rs.getLast hrs_ne = 0 := by
    by_contra hlast_ne
    have hzero_drop : 0 ∈ rs.dropLast :=
      List.mem_dropLast_of_mem_of_ne_getLast hzero_mem (by lia)
    exact (ne_of_lt (hrs_drop_neg 0 hzero_drop)) rfl
  intro r hr
  have hr_mem : r ∈ rs := Multiset.mem_coe.mp (by simp_all)
  by_cases hr_last : r = rs.getLast hrs_ne
  · simp [hr_last, hlast_zero]
  · exact (hrs_drop_neg r
      (List.mem_dropLast_of_mem_of_ne_getLast hr_mem hr_last)).le

/-- In a same-degree proper-position pair, strict negativity of every root of
the right polynomial implies strict negativity of every root of the left. -/
theorem roots_neg_of_prec_sameDegree_of_roots_neg {g f : ℝ[X]}
    (hgf : Prec g f)
    (hdeg : g.natDegree = f.natDegree)
    (hf_neg : ∀ r, f.IsRoot r → r < 0) :
    ∀ r, g.IsRoot r → r < 0 := by
  obtain ⟨hg, hf, ss, rs, _, _, hss_eq, hrs_eq, hshape⟩ := hgf
  have hss_len : ss.length = g.natDegree := by
    rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hg.2]
  have hrs_len : rs.length = f.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hf.2]
  rcases hshape with ⟨_, hint⟩ | ⟨_, halt⟩
  · lia
  · have hrs_neg : ∀ s ∈ rs, s < 0 := by
      intro s hs
      apply hf_neg s
      apply (mem_roots hf.1).mp
      simpa [hrs_eq] using Multiset.mem_coe.mpr hs
    have hss_neg : ∀ s ∈ ss, s < 0 :=
      listAlternates_left_lt_of_right_lt halt hrs_neg
    intro r hr
    apply hss_neg r
    apply Multiset.mem_coe.mp
    simp_all

end RealRooted
