import RealRooted.MaWang.StrictSigns.Assembly

/-!
# Strict interlacing from root-count signs

If `p` has simple real roots and `F` has the sign `-(-1)^(number of roots of p to the right)` at
every root of `p`, and `F` has positive leading coefficient and one more degree than `p`, then
`p ≪ F` strictly.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Number of larger entries in a strictly sorted list. -/
theorem countP_lt_getElem_of_pairwise_lt {l : List ℝ} (hl : l.Pairwise (· < ·))
    (i : ℕ) (hi : i < l.length) :
    l.countP (fun r => decide (l[i] < r)) = l.length - 1 - i := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a t ih =>
      cases i with
      | zero =>
          have hall : t.countP (fun r => decide (a < r)) = t.length :=
            List.countP_eq_length.mpr (fun x hx => by
              simpa using List.rel_of_pairwise_cons hl hx)
          simp [hall]
      | succ i' =>
          have hi' : i' < t.length := by simpa using hi
          have hlt : a < t[i'] := List.rel_of_pairwise_cons hl (List.getElem_mem hi')
          have hih := ih (List.Pairwise.of_cons hl) i' hi'
          have hn : ¬ t[i'] < a := not_lt.mpr hlt.le
          simp only [List.getElem_cons_succ, List.countP_cons, hih, List.length_cons,
            decide_eq_true_eq, hn, ite_false]
          lia

private lemma countP_lt_adjacent {pre rest : List ℝ} {r₁ r₂ : ℝ}
    (h : (pre ++ r₁ :: r₂ :: rest).Pairwise (· < ·)) :
    (pre ++ r₁ :: r₂ :: rest).countP (fun r => decide (r₁ < r)) =
      (pre ++ r₁ :: r₂ :: rest).countP (fun r => decide (r₂ < r)) + 1 := by
  obtain ⟨hpre, hmid, hcross⟩ := List.pairwise_append.mp h
  obtain ⟨hr₁, hmid'⟩ := List.pairwise_cons.mp hmid
  obtain ⟨hr₂, _⟩ := List.pairwise_cons.mp hmid'
  have h12 : r₁ < r₂ := hr₁ r₂ (by simp)
  have hpre₁ : pre.countP (fun r => decide (r₁ < r)) = 0 :=
    List.countP_eq_zero.mpr (fun x hx => by
      have := hcross x hx r₁ (by simp)
      simpa using this.le)
  have hpre₂ : pre.countP (fun r => decide (r₂ < r)) = 0 :=
    List.countP_eq_zero.mpr (fun x hx => by
      have := (hcross x hx r₁ (by simp)).trans h12
      simpa using this.le)
  have hrest₁ : rest.countP (fun r => decide (r₁ < r)) = rest.length :=
    List.countP_eq_length.mpr (fun x hx => by simpa using h12.trans (hr₂ x hx))
  have hrest₂ : rest.countP (fun r => decide (r₂ < r)) = rest.length :=
    List.countP_eq_length.mpr (fun x hx => by simpa using hr₂ x hx)
  simp only [List.countP_append, List.countP_cons, hpre₁, hpre₂, hrest₁, hrest₂, h12,
    lt_self_iff_false, decide_true, decide_false, ite_true, not_lt.mpr h12.le]
  lia

/-- `p ≪ F` strictly, from the signs of `F` at the roots of `p`, measured by the number of roots
of `p` to the right. -/
theorem strictInterl_of_eval_mul_neg_one_pow_countP_neg {p F : ℝ[X]}
    (hp : p ≠ 0) (hps : p.Splits) (hpnd : p.roots.Nodup) (hpos : 1 ≤ p.natDegree)
    (hF : 0 < F.leadingCoeff) (hdeg : F.natDegree = p.natDegree + 1)
    (hsign : ∀ x ∈ p.roots, F.eval x * (-1 : ℝ) ^ (p.roots.countP (fun r => x < r)) < 0) :
    StrictInterl p F ∧ ∀ x, p.IsRoot x → ¬ F.IsRoot x := by
  refine ⟨?_, ?_⟩
  · set rs : List ℝ := p.roots.sort (· ≤ ·) with hrs_def
    have hrs_le : rs.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
    have hrs_eq : (↑rs : Multiset ℝ) = p.roots := Multiset.sort_eq ..
    have hrs_nodup : rs.Nodup := Multiset.coe_nodup.mp (by rw [hrs_eq]; exact hpnd)
    have hrs_lt : rs.Pairwise (· < ·) :=
      (hrs_le.and hrs_nodup).imp (fun h => lt_of_le_of_ne h.1 h.2)
    have hrs_len : rs.length = p.natDegree := by
      rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hps]
    have hrs_ne : rs ≠ [] := by
      intro h
      rw [h] at hrs_len
      simp only [List.length_nil] at hrs_len
      lia
    have hcnt : ∀ x, p.roots.countP (fun r => x < r) = rs.countP (fun r => decide (x < r)) := by
      intro x
      rw [← hrs_eq, Multiset.coe_countP]
    have hmem : ∀ x ∈ rs, x ∈ p.roots := fun x hx => by
      rw [← hrs_eq]
      exact Multiset.mem_coe.mpr hx
    have hconsec : ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest → F.eval r₁ * F.eval r₂ < 0 := by
      intro pre r₁ r₂ rest hdecomp
      have h1 := hsign r₁ (hmem r₁ (by simp [hdecomp]))
      have h2 := hsign r₂ (hmem r₂ (by simp [hdecomp]))
      rw [hcnt, hdecomp] at h1 h2
      have hrel := countP_lt_adjacent (hdecomp ▸ hrs_lt)
      rw [hrel, pow_succ] at h1
      generalize hE : (-1 : ℝ) ^ List.countP (fun r => decide (r₂ < r))
        (pre ++ r₁ :: r₂ :: rest) = e at h1 h2
      have hsq : e * e = 1 := by
        rw [← hE, ← pow_add]
        exact Even.neg_one_pow ⟨_, rfl⟩
      have hprod := mul_pos_of_neg_of_neg h1 h2
      have : F.eval r₁ * (e * -1) * (F.eval r₂ * e) =
          -(F.eval r₁ * F.eval r₂) * (e * e) := by ring
      rw [this, hsq] at hprod
      linarith
    have hright : F.eval (rs.getLast hrs_ne) < 0 := by
      have h := hsign _ (hmem _ (List.getLast_mem hrs_ne))
      rw [hcnt] at h
      have h0 : rs.countP (fun r => decide (rs.getLast hrs_ne < r)) = 0 :=
        List.countP_eq_zero.mpr (fun x hx => by
          simpa using List.Pairwise.rel_getLast hrs_le hx)
      rw [h0, pow_zero, mul_one] at h
      exact h
    have hhead : rs.head! = rs[0]'(by lia) := by
      have key : ∀ l : List ℝ, ∀ h : l ≠ [], l.head! = l[0]'(List.length_pos_iff.mpr h) := by
        intro l h
        cases l with
        | nil => exact absurd rfl h
        | cons r0 tl => rfl
      exact key rs hrs_ne
    have hleft : F.eval rs.head! * (-1 : ℝ) ^ (p.natDegree - 1) < 0 := by
      have h := hsign rs.head! (hmem _ (by
        rw [hhead]
        exact List.getElem_mem _))
      rw [hcnt, hhead, countP_lt_getElem_of_pairwise_lt hrs_lt 0 (by lia)] at h
      rw [hhead, ← hrs_len]
      simpa using h
    rcases Nat.even_or_odd p.natDegree with hev | hodd
    · have hodd' : Odd (p.natDegree - 1) := by
        rw [Nat.odd_iff]
        obtain ⟨k, hk⟩ := hev
        lia
      rw [hodd'.neg_one_pow] at hleft
      exact strictInterl_of_strict_signs_of_endSigns_even hp hps hF hrs_le hrs_eq hdeg
        (by lia) hev hconsec (by linarith) hright
    · have hev' : Even (p.natDegree - 1) := by
        rw [Nat.even_iff]
        obtain ⟨k, hk⟩ := hodd
        lia
      rw [hev'.neg_one_pow] at hleft
      exact strictInterl_of_strict_signs_of_endSigns_odd hp hps hF hrs_le hrs_eq hdeg
        (by lia) hodd hconsec (by linarith) hright
  · intro x hx hFx
    have h := hsign x ((mem_roots hp).mpr hx)
    rw [hFx.eq_zero, zero_mul] at h
    exact lt_irrefl _ h


/-- Every element of the shorter list is at least the head of the longer one. -/
theorem listInterlaces_ge_head {ss rs' : List ℝ} {r : ℝ}
    (hint : ListInterlaces ss (r :: rs')) (hs : (r :: rs').Pairwise (· ≤ ·)) :
    ∀ x ∈ ss, r ≤ x := by
  induction ss generalizing r rs' with
  | nil => simp
  | cons s ss ih =>
      cases rs' with
      | nil => simp [ListInterlaces] at hint
      | cons r₂ rs'' =>
          rcases hint with ⟨h1, _, htail⟩
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact h1
          · have hr₂ := ih htail (List.Pairwise.of_cons hs) x hx
            exact (List.rel_of_pairwise_cons hs (by simp)).trans hr₂

/-- Number of entries of a strictly interlacing larger list above the `i`-th entry. -/
theorem countP_lt_getElem_of_listInterlaces_strict {ss rs : List ℝ}
    (hint : ListInterlaces ss rs) (hrs : rs.Pairwise (· < ·))
    (hdisj : ∀ s ∈ ss, s ∉ rs) (hlen : ss.length + 1 = rs.length)
    (i : ℕ) (hi : i < ss.length) :
    rs.countP (fun r => decide (ss[i] < r)) = ss.length - i := by
  induction ss generalizing rs i with
  | nil => simp at hi
  | cons s ss ih =>
      rcases rs with _ | ⟨r₁, _ | ⟨r₂, rs₂⟩⟩
      · simp at hlen
      · simp at hlen
      · obtain ⟨h1, h2, htail⟩ := hint
        have hr₂ : s ≠ r₂ := fun h => hdisj s (by simp) (by simp [h])
        have hr₁ : s ≠ r₁ := fun h => hdisj s (by simp) (by simp [h])
        have hlt₂ : s < r₂ := lt_of_le_of_ne h2 hr₂
        have hlen₂ : rs₂.length = ss.length := by
          simp only [List.length_cons] at hlen
          lia
        cases i with
        | zero =>
            have hall : rs₂.countP (fun r => decide (s < r)) = rs₂.length := by
              apply List.countP_eq_length.mpr
              intro x hx
              have := List.rel_of_pairwise_cons (List.Pairwise.of_cons hrs) hx
              simpa using hlt₂.trans this
            simp only [List.getElem_cons_zero, List.countP_cons, hall, hlen₂]
            have : ¬ s < r₁ := not_lt.mpr h1
            simp [this, hlt₂]
        | succ i' =>
            have hi' : i' < ss.length := by simpa using hi
            have hih := ih htail (List.Pairwise.of_cons hrs)
              (fun x hx => by
                intro hmem
                exact hdisj x (by simp [hx]) (by simp [hmem])) (by
                simp only [List.length_cons] at hlen ⊢
                lia) i' hi'
            have hx₂ := listInterlaces_ge_head htail
              (List.Pairwise.imp (fun h => h.le) (List.Pairwise.of_cons hrs))
              ss[i'] (List.getElem_mem hi')
            have hr₁lt : r₁ < r₂ := List.rel_of_pairwise_cons hrs (by simp)
            have hn : ¬ ss[i'] < r₁ := not_lt.mpr (hr₁lt.le.trans hx₂)
            simp only [List.getElem_cons_succ, List.countP_cons, hih, List.length_cons]
            simp [hn]

end RealRooted
