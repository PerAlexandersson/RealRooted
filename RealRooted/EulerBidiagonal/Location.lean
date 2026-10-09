import RealRooted.EulerBidiagonal.ComparisonData

/-!
# Root location for the general Euler step

The roots `π_0 < … < π_m` of `generalStep κ a b u v q` interlace the comparison zeros, and the
comparison polynomial alternates in sign at them:
`generalComparison_sign_at_generalStep_root` (the sign `(−1)^(number of roots of generalStep q
to the right)`).
-/

open Polynomial

noncomputable section

namespace RealRooted.EulerBidiagonal

/-- Consecutive strict sign changes from alternating signs along a list. -/
theorem eval_mul_neg_of_alternating {F : ℝ[X]} {Pts : List ℝ}
    (h : ∀ (j : ℕ) (hj : j < Pts.length),
      0 < (-1 : ℝ) ^ (Pts.length - 1 - j) * F.eval Pts[j]) :
    ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
      Pts = pre ++ r₁ :: r₂ :: rest → F.eval r₁ * F.eval r₂ < 0 := by
  intro pre r₁ r₂ rest heq
  subst heq
  have h1 := h pre.length (by simp)
  have h2 := h (pre.length + 1) (by simp)
  have e1 : (pre ++ r₁ :: r₂ :: rest)[pre.length]'(by simp) = r₁ := by simp
  have e2 : (pre ++ r₁ :: r₂ :: rest)[pre.length + 1]'(by simp) = r₂ := by simp
  rw [e1] at h1
  rw [e2] at h2
  have hl1 : (pre ++ r₁ :: r₂ :: rest).length - 1 - pre.length = rest.length + 1 := by
    simp
  have hl2 : (pre ++ r₁ :: r₂ :: rest).length - 1 - (pre.length + 1) = rest.length := by
    simp only [List.length_append, List.length_cons]
    lia
  rw [hl1, pow_succ] at h1
  rw [hl2] at h2
  have hsq : (-1 : ℝ) ^ rest.length * (-1 : ℝ) ^ rest.length = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨rest.length, rfl⟩
  have hprod := mul_pos h1 h2
  have : (-1 : ℝ) ^ rest.length * -1 * F.eval r₁ * ((-1 : ℝ) ^ rest.length * F.eval r₂) =
      -(F.eval r₁ * F.eval r₂) * ((-1 : ℝ) ^ rest.length * (-1 : ℝ) ^ rest.length) := by ring
  rw [this, hsq] at hprod
  linarith

/-- `0 < q(0)` for a negative-simple polynomial. -/
theorem eval_zero_pos_of_isNegativeSimple {q : ℝ[X]} (hq : IsNegativeSimple q) :
    0 < q.eval 0 := by
  have hq0mem : (0 : ℝ) ∉ q.roots := fun hmem => lt_irrefl _ (hq.2.2.2.2 0 hmem)
  have hcount : q.roots.countP (fun x => 0 < x) = 0 := by
    apply Multiset.countP_eq_zero.mpr
    intro x hx hpos
    exact (not_lt_of_ge (hq.2.2.2.2 x hx).le) hpos
  simpa [hcount] using eval_sign hq.2.1 hq.2.2.2.1 0 hq0mem

/-- `(T q)(0) > 0` for a negative-simple `q`. -/
theorem generalStep_eval_zero_pos (κ a b u v : ℝ) (q : ℝ[X]) (hκ : 0 < κ) (ha : 0 < a)
    (hb : 0 < b) (hq : IsNegativeSimple q) :
    0 < (generalStep κ a b u v q).eval 0 := by
  have hq0c : 0 < q.coeff 0 := by
    simpa [coeff_zero_eq_eval_zero] using eval_zero_pos_of_isNegativeSimple hq
  calc
    0 < κ * a * b * q.coeff 0 := mul_pos (mul_pos (mul_pos hκ ha) hb) hq0c
    _ = (generalStep κ a b u v q).coeff 0 := by rw [coeff_zero_generalStep]
    _ = (generalStep κ a b u v q).eval 0 := by simp [coeff_zero_eq_eval_zero]

/-- Sign data of `T q` along the sample points `L, A₀, …, A_{m-1}, 0`. -/
theorem generalStep_alternating_signs (κ a b u v : ℝ) (q : ℝ[X]) (m : ℕ) (L : ℝ)
    (A : List ℝ) (hAlen : A.length = m)
    (hLT : 0 < (-1 : ℝ) ^ (m + 1) * (generalStep κ a b u v q).eval L)
    (hAsign : ∀ (i : ℕ) (hi : i < A.length),
      0 < (-1 : ℝ) ^ (m - i) * (generalStep κ a b u v q).eval A[i])
    (hT0 : 0 < (generalStep κ a b u v q).eval 0) :
    ∀ (j : ℕ) (hj : j < (L :: (A ++ [0])).length),
      0 < (-1 : ℝ) ^ ((L :: (A ++ [0])).length - 1 - j) *
        (generalStep κ a b u v q).eval (L :: (A ++ [0]))[j] := by
  intro j hj
  have hlen : (L :: (A ++ [0])).length = m + 2 := by simp [hAlen]
  cases j with
  | zero =>
      simp only [hlen, List.getElem_cons_zero]
      simpa using hLT
  | succ j =>
      simp only [List.getElem_cons_succ]
      by_cases hjm : j < m
      · have hjA : j < A.length := by lia
        rw [List.getElem_append_left hjA]
        have h := hAsign j hjA
        have : (L :: (A ++ [0])).length - 1 - (j + 1) = m - j := by lia
        rw [this]
        exact h
      · have hjm' : j = m := by
          have : j < A.length + 1 := by simpa [hAlen] using hj
          lia
        subst hjm'
        rw [List.getElem_append_right (by lia)]
        have : (L :: (A ++ [0])).length - 1 - (j + 1) = 0 := by lia
        rw [this]
        simpa [hAlen] using hT0


/-- The sample points `L, A₀, …, A_{m-1}, 0` are strictly increasing. -/
theorem pairwise_lt_cons_append_zero {A : List ℝ} {L : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hAlen : A.length = m) (hApair : A.Pairwise (· < ·)) (hAneg : ∀ x ∈ A, x < 0)
    (hLA : ∀ x ∈ A, L < x) : (L :: (A ++ [0])).Pairwise (· < ·) := by
  refine List.Pairwise.cons ?_ (List.pairwise_append.mpr ⟨hApair, by simp, ?_⟩)
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hLA x hx
    · simp only [List.mem_singleton] at hx
      subst hx
      have hy : A[0]'(by lia) ∈ A := List.getElem_mem _
      exact (hLA _ hy).trans (hAneg _ hy)
  · intro x hx y hy
    simp only [List.mem_singleton] at hy
    rw [hy]
    exact hAneg x hx

/-- Roots of `T q` interlacing the sample points, with their exact count. -/
theorem exists_generalStep_roots_interlacing
    (κ a b u v : ℝ) (q : ℝ[X]) (m : ℕ) (hq : IsNegativeSimple q) (hqdeg : q.natDegree = m)
    (hm : 1 ≤ m) (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) (hell : ∀ k ≤ m, 0 < u + v * k)
    (A : List ℝ) (hAlen : A.length = m) (hApair : A.Pairwise (· < ·))
    (hAneg : ∀ x ∈ A, x < 0) (L : ℝ) (hLA : ∀ x ∈ A, L < x)
    (hLT : 0 < (-1 : ℝ) ^ (m + 1) * (generalStep κ a b u v q).eval L)
    (hAsign : ∀ (i : ℕ) (hi : i < A.length),
      0 < (-1 : ℝ) ^ (m - i) * (generalStep κ a b u v q).eval A[i]) :
    ∃ us : List ℝ, us.length = m + 1 ∧ ListInterlaces us (L :: (A ++ [0])) ∧
      us.Pairwise (· < ·) ∧ (↑us : Multiset ℝ) = (generalStep κ a b u v q).roots := by
  have hT := generalStep_natDegree_and_leadingCoeff κ a b u v q m hqdeg hq.2.2.2.1 hell
  have hT0 := generalStep_eval_zero_pos κ a b u v q hκ ha hb hq
  have hTne : generalStep κ a b u v q ≠ 0 := by
    intro h
    have := hT.2
    rw [h] at this
    simp at this
  have hsigns := generalStep_alternating_signs κ a b u v q m L A hAlen hLT hAsign hT0
  have hsorted : (L :: (A ++ [0])).Pairwise (· ≤ ·) :=
    (pairwise_lt_cons_append_zero hm hAlen hApair hAneg hLA).imp le_of_lt
  obtain ⟨us, hus_len, hint, hus_roots, hus_pair⟩ :=
    MaWangInternal.exists_roots_strictly_interlacing_of_consecutive_signs
      (F := generalStep κ a b u v q) hsorted (eval_mul_neg_of_alternating hsigns)
  have hlen : us.length = m + 1 := by
    simp only [List.length_cons, List.length_append, hAlen, List.length_nil] at hus_len
    lia
  have hnd : (↑us : Multiset ℝ).Nodup :=
    Multiset.coe_nodup.mpr (List.Pairwise.imp (fun h => ne_of_lt h) hus_pair)
  obtain ⟨hroots, _⟩ := roots_eq_of_nodup_of_natDegree_le hTne hnd
    (fun x hx => hus_roots x (Multiset.mem_coe.mp hx)) (by
      rw [Multiset.coe_card, hlen, hT.1])
  exact ⟨us, hlen, hint, hus_pair, hroots.symm⟩



/-- Sign of the comparison polynomial at the roots of `T q`, given its root structure. -/
theorem generalComparison_sign_of_comparison_roots
    (κ a b u v : ℝ) (q : ℝ[X]) (m : ℕ) (hq : IsNegativeSimple q) (hqdeg : q.natDegree = m)
    (hm : 1 ≤ m) (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) (hell : ∀ k ≤ m, 0 < u + v * k)
    (A : List ℝ) (hAlen : A.length = m) (hApair : A.Pairwise (· < ·))
    (hAneg : ∀ x ∈ A, x < 0) (L : ℝ) (hLA : ∀ x ∈ A, L < x)
    (hLT : 0 < (-1 : ℝ) ^ (m + 1) * (generalStep κ a b u v q).eval L)
    (hAsign : ∀ (i : ℕ) (hi : i < A.length),
      0 < (-1 : ℝ) ^ (m - i) * (generalStep κ a b u v q).eval A[i])
    (E : Multiset ℝ) (hGroots : (generalComparison κ a b v q).roots = ↑A + E)
    (hGsp : (generalComparison κ a b v q).Splits)
    (hE : (E = 0 ∧ 0 < (generalComparison κ a b v q).leadingCoeff) ∨
      (E = {L} ∧ 0 < (generalComparison κ a b v q).leadingCoeff) ∨
      (∃ e, E = {e} ∧ 0 < e ∧ (generalComparison κ a b v q).leadingCoeff < 0)) :
    ∀ x ∈ (generalStep κ a b u v q).roots,
      0 < (generalComparison κ a b v q).eval x *
        (-1 : ℝ) ^ ((generalStep κ a b u v q).roots.countP (fun r => x < r)) := by
  obtain ⟨us, hlen, hint, hpair, hus_eq⟩ := exists_generalStep_roots_interlacing κ a b u v q m
    hq hqdeg hm hκ ha hb hell A hAlen hApair hAneg L hLA hLT hAsign
  have hT0 := generalStep_eval_zero_pos κ a b u v q hκ ha hb hq
  have hsigns := generalStep_alternating_signs κ a b u v q m L A hAlen hLT hAsign hT0
  have hPts_lt := pairwise_lt_cons_append_zero hm hAlen hApair hAneg hLA
  have hPts_ne : ∀ y ∈ L :: (A ++ [0]), (generalStep κ a b u v q).eval y ≠ 0 := by
    intro y hy h
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hy
    have := hsigns j hj
    rw [h] at this
    simp at this
  have hdisj : ∀ s ∈ us, s ∉ L :: (A ++ [0]) := by
    intro s hs hmem
    have hs' : s ∈ (generalStep κ a b u v q).roots := by
      rw [← hus_eq]
      exact Multiset.mem_coe.mpr hs
    exact hPts_ne s hmem (isRoot_of_mem_roots hs')
  intro x hx
  have hxroot : (generalStep κ a b u v q).eval x = 0 := isRoot_of_mem_roots hx
  rw [← hus_eq] at hx
  have hxus : x ∈ us := Multiset.mem_coe.mp hx
  obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hxus
  have hxPts : x ∉ L :: (A ++ [0]) := hdisj x hxus
  have hxA : x ∉ A := fun h => hxPts (by simp [h])
  have hxL : x ≠ L := fun h => hxPts (by simp [h])
  have hLx : L ≤ x := listInterlaces_ge_head hint (hPts_lt.imp le_of_lt) x hxus
  have hxle : x ≤ 0 := by
    refine listInterlaces_left_le_of_right_le hint (c := 0) ?_ x hxus
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact ((hLA _ (List.getElem_mem (show 0 < A.length by lia))).trans
        (hAneg _ (List.getElem_mem (show 0 < A.length by lia)))).le
    · rcases List.mem_append.mp hr with hr | hr
      · exact (hAneg r hr).le
      · simp only [List.mem_singleton] at hr
        exact hr.le
  have hx0 : x < 0 := by
    refine lt_of_le_of_ne hxle ?_
    intro h
    rw [h] at hxroot
    linarith
  have hcntT : (generalStep κ a b u v q).roots.countP (fun r => x < r) = m - i := by
    rw [← hus_eq, Multiset.coe_countP, ← hix]
    have := countP_lt_getElem_of_pairwise_lt hpair i hi
    simpa [hlen] using this
  have hcntPts := countP_lt_getElem_of_listInterlaces_strict hint hPts_lt hdisj
    (by simp [hlen, hAlen]) i hi
  have hcntA : A.countP (fun r => decide (x < r)) = m - i := by
    rw [hix] at hcntPts
    simp only [List.countP_cons, List.countP_append, not_lt.mpr hLx, hx0, hlen] at hcntPts
    simp only [List.countP_nil, decide_true, ite_true, decide_false, Bool.false_eq_true,
      ite_false] at hcntPts
    lia
  rw [hcntT]
  have hsing : ∀ c : ℝ, Multiset.countP (fun r => x < r) ({c} : Multiset ℝ) =
      if x < c then 1 else 0 := by
    intro c
    rw [← Multiset.cons_zero, Multiset.countP_cons]
    simp
  rcases hE with ⟨hE0, hlc⟩ | ⟨hEL, hlc⟩ | ⟨e, hEe, he, hlc⟩
  · have hxG : x ∉ (generalComparison κ a b v q).roots := by
      rw [hGroots, hE0]
      simpa using hxA
    have h := eval_sign hGsp hlc x hxG
    simp only [hGroots, hE0, Multiset.coe_countP, hcntA, add_zero] at h
    exact h
  · have hxG : x ∉ (generalComparison κ a b v q).roots := by
      rw [hGroots, hEL]
      simp [hxA, hxL]
    have h := eval_sign hGsp hlc x hxG
    simp only [hGroots, hEL, Multiset.countP_add, Multiset.coe_countP, hcntA,
      hsing, not_lt.mpr hLx, ite_false,
      add_zero] at h
    exact h
  · have hxG : x ∉ (generalComparison κ a b v q).roots := by
      rw [hGroots, hEe]
      simp only [Multiset.mem_add, Multiset.mem_coe, Multiset.mem_singleton, not_or]
      exact ⟨hxA, (hx0.trans he).ne⟩
    have hNsp : (-(generalComparison κ a b v q)).Splits := by
      apply splits_of_card_roots
      rw [roots_neg, natDegree_neg]
      exact card_roots_of_splits hGsp
    have hNlc : 0 < (-(generalComparison κ a b v q)).leadingCoeff := by
      rw [leadingCoeff_neg]
      exact neg_pos.mpr hlc
    have hxN : x ∉ (-(generalComparison κ a b v q)).roots := by
      rw [roots_neg]
      exact hxG
    have h := eval_sign hNsp hNlc x hxN
    simp only [roots_neg, hGroots, hEe, Multiset.countP_add, Multiset.coe_countP, hcntA,
      hsing, hx0.trans he, ite_true, eval_neg] at h
    rw [pow_succ] at h
    nlinarith


/-- (A1) for `m ≥ 1`: at every root of `T q`, the comparison polynomial has the sign
`(-1)^(number of roots of T q to the right)`. -/
theorem generalComparison_sign_at_generalStep_root_of_one_le
    (κ a b u v : ℝ) (q : ℝ[X]) (m : ℕ) (hm : 1 ≤ m) (hq : IsNegativeSimple q)
    (hqdeg : q.natDegree = m) (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b)
    (hell : ∀ k ≤ m, 0 < u + v * k)
    (hQ : ∀ t ≤ 0, comparisonDefect κ a b u v t < 0) :
    ∀ x ∈ (generalStep κ a b u v q).roots,
      0 < (generalComparison κ a b v q).eval x *
        (-1 : ℝ) ^ ((generalStep κ a b u v q).roots.countP (fun r => x < r)) := by
  obtain ⟨rs, A, hrs, hrs_eq, hrs_len, hAlen, hApair, hAneg, hAroot, hint, hlow, hAsign⟩ :=
    exists_comparison_data κ a b u v q m hm hq hqdeg hκ ha hb hQ
  have hqlc : 0 < q.leadingCoeff := hq.2.2.2.1
  have hT := generalStep_natDegree_and_leadingCoeff κ a b u v q m hqdeg hqlc hell
  have hAnd : (↑A : Multiset ℝ).Nodup :=
    Multiset.coe_nodup.mpr (hApair.imp (fun h => ne_of_lt h))
  have hAne : A ≠ [] := by
    intro h
    rw [h] at hAlen
    simp only [List.length_nil] at hAlen
    lia
  -- a left sample point for the case `v ≤ 0`
  have hleft : ∃ L, (∀ x ∈ A, L < x) ∧
      0 < (-1 : ℝ) ^ (m + 1) * (generalStep κ a b u v q).eval L := by
    obtain ⟨R, hR, hRs⟩ := exists_left_endpoint_sign hT.1 hT.2 A.head!
    exact ⟨R, fun x hx => hR.trans_le ((hApair.imp le_of_lt).head!_le hx), hRs⟩
  rcases lt_trichotomy v 0 with hv | hv | hv
  · -- `v < 0`
    obtain ⟨e, heroot, he⟩ := exists_comparison_root_pos_of_neg κ a b v q m hv hκ ha hb hq hqdeg
    obtain ⟨hGdeg, hGlc⟩ := generalComparison_natDegree_of_v_ne_zero κ a b v q m hv.ne hqdeg hqlc
    have hlc : (generalComparison κ a b v q).leadingCoeff < 0 := by
      rw [hGlc]
      exact mul_neg_of_neg_of_pos hv hqlc
    have hGne : generalComparison κ a b v q ≠ 0 := by
      intro h
      rw [h] at hlc
      simp at hlc
    have heA : e ∉ A := fun h => (lt_asymm he (hAneg e h)).elim
    obtain ⟨hroots, hsp⟩ := roots_eq_of_nodup_of_natDegree_le hGne
      (M := ↑(e :: A)) (Multiset.coe_nodup.mpr (List.nodup_cons.mpr ⟨heA, hAnd⟩)) (by
        intro x hx
        rcases List.mem_cons.mp (Multiset.mem_coe.mp hx) with rfl | hx
        · exact heroot
        · exact hAroot x hx) (by
        rw [Multiset.coe_card, hGdeg]
        simp [hAlen])
    obtain ⟨L, hLA, hLT⟩ := hleft
    refine generalComparison_sign_of_comparison_roots κ a b u v q m hq hqdeg hm hκ ha hb hell
      A hAlen hApair hAneg L hLA hLT hAsign {e} ?_ hsp (Or.inr (Or.inr ⟨e, rfl, he, hlc⟩))
    rw [hroots, ← Multiset.cons_coe, ← Multiset.singleton_add, add_comm]
  · -- `v = 0`
    subst hv
    obtain ⟨hGdeg, hGlc⟩ := generalComparison_natDegree_of_v_eq_zero κ a b q m hκ ha hb hqdeg hqlc
    have hGne : generalComparison κ a b 0 q ≠ 0 := by
      intro h
      rw [h] at hGlc
      simp at hGlc
    obtain ⟨hroots, hsp⟩ := roots_eq_of_nodup_of_natDegree_le hGne (M := ↑A) hAnd
      (fun x hx => hAroot x (Multiset.mem_coe.mp hx)) (by
        rw [Multiset.coe_card, hGdeg, hAlen])
    obtain ⟨L, hLA, hLT⟩ := hleft
    refine generalComparison_sign_of_comparison_roots κ a b u 0 q m hq hqdeg hm hκ ha hb hell
      A hAlen hApair hAneg L hLA hLT hAsign 0 ?_ hsp (Or.inl ⟨rfl, hGlc⟩)
    rw [hroots, add_zero]
  · -- `v > 0`
    obtain ⟨e, heroot, he⟩ := exists_comparison_root_lt_roots_of_pos κ a b v q m hv hκ hq hqdeg
      rs hrs hrs_eq hrs_len hm
    obtain ⟨hGdeg, hGlc⟩ := generalComparison_natDegree_of_v_ne_zero κ a b v q m hv.ne' hqdeg hqlc
    have hlc : 0 < (generalComparison κ a b v q).leadingCoeff := by
      rw [hGlc]
      exact mul_pos hv hqlc
    have hGne : generalComparison κ a b v q ≠ 0 := by
      intro h
      rw [h] at hlc
      simp at hlc
    have heA' : ∀ x ∈ A, e < x := by
      intro x hx
      obtain ⟨r, hr, hrx⟩ := hlow x hx
      have : r ∈ q.roots := by
        rw [← hrs_eq]
        exact Multiset.mem_coe.mpr hr
      exact (he r this).trans_le hrx
    have heA : e ∉ A := fun h => lt_irrefl _ (heA' e h)
    have heneg : e < 0 := by
      have hy : A[0]'(by lia) ∈ A := List.getElem_mem _
      exact (heA' _ hy).trans (hAneg _ hy)
    obtain ⟨hroots, hsp⟩ := roots_eq_of_nodup_of_natDegree_le hGne
      (M := ↑(e :: A)) (Multiset.coe_nodup.mpr (List.nodup_cons.mpr ⟨heA, hAnd⟩)) (by
        intro x hx
        rcases List.mem_cons.mp (Multiset.mem_coe.mp hx) with rfl | hx
        · exact heroot
        · exact hAroot x hx) (by
        rw [Multiset.coe_card, hGdeg]
        simp [hAlen])
    have hprod := generalStep_eval_mul_neg_of_generalComparison_root κ a b u v q e hκ hq hQ
      heroot heneg
    have hqe : 0 < (-1 : ℝ) ^ m * q.eval e := by
      have hnot : e ∉ q.roots := by
        intro h
        exact lt_irrefl _ (he e h)
      have h := eval_sign hq.2.1 hqlc e hnot
      have hcnt : q.roots.countP (fun r => e < r) = m := by
        have : q.roots.countP (fun r => e < r) = Multiset.card q.roots :=
          Multiset.countP_eq_card.mpr (fun r hr => he r hr)
        rw [this, card_roots_of_splits hq.2.1, hqdeg]
      rw [hcnt] at h
      linarith
    have hLT := generalStep_sign_of_input_sign κ a b u v q e m hprod hqe
    refine generalComparison_sign_of_comparison_roots κ a b u v q m hq hqdeg hm hκ ha hb hell
      A hAlen hApair hAneg e heA' hLT hAsign {e} ?_ hsp (Or.inr (Or.inl ⟨rfl, hlc⟩))
    rw [hroots, ← Multiset.cons_coe, ← Multiset.singleton_add, add_comm]


/-- (A1) for constant `q`. -/
theorem generalComparison_sign_at_generalStep_root_of_natDegree_eq_zero
    (κ a b u v : ℝ) (q : ℝ[X]) (hq : IsNegativeSimple q) (hqdeg : q.natDegree = 0)
    (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) (hu : 0 < u)
    (hQ : ∀ t ≤ 0, comparisonDefect κ a b u v t < 0) :
    ∀ x ∈ (generalStep κ a b u v q).roots,
      0 < (generalComparison κ a b v q).eval x *
        (-1 : ℝ) ^ ((generalStep κ a b u v q).roots.countP (fun r => x < r)) := by
  have hqC : q = C (q.coeff 0) := eq_C_of_natDegree_eq_zero hqdeg
  have hc0 : 0 < q.coeff 0 := by
    simpa [coeff_zero_eq_eval_zero] using eval_zero_pos_of_isNegativeSimple hq
  have hTeval : ∀ x : ℝ, (generalStep κ a b u v q).eval x =
      q.coeff 0 * (κ * a * b + u * x) := by
    intro x
    rw [hqC]
    simp only [generalStep, theta, derivative_C, mul_zero, map_zero, zero_add, eval_add, eval_mul,
      eval_C, eval_X, eval_zero, coeff_C_zero]
    ring
  have hGeval : ∀ x : ℝ, (generalComparison κ a b v q).eval x =
      q.coeff 0 * (κ * (a + b + 1) + v * x) := by
    intro x
    rw [hqC]
    simp only [generalComparison, theta, derivative_C, mul_zero, eval_add, eval_mul, eval_C,
      eval_X, eval_zero, coeff_C_zero]
    ring
  intro x hx
  have hxroot : κ * a * b + u * x = 0 := by
    have h := (isRoot_of_mem_roots hx).eq_zero
    rw [hTeval] at h
    exact (mul_eq_zero.mp h).resolve_left hc0.ne'
  have hx0 : x < 0 := by
    have : u * x = -(κ * a * b) := by linarith
    have hpos : 0 < κ * a * b := by positivity
    by_contra hcon
    push Not at hcon
    nlinarith [mul_nonneg hu.le hcon]
  have hcnt : (generalStep κ a b u v q).roots.countP (fun r => x < r) = 0 := by
    apply Multiset.countP_eq_zero.mpr
    intro y hy hxy
    have hyroot : κ * a * b + u * y = 0 := by
      have h := (isRoot_of_mem_roots hy).eq_zero
      rw [hTeval] at h
      exact (mul_eq_zero.mp h).resolve_left hc0.ne'
    have : u * (y - x) = 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_left hu.ne'
    linarith
  rw [hcnt, pow_zero, mul_one, hGeval]
  have hc : 0 < κ * (a + b + 1) := by positivity
  apply mul_pos hc0
  rcases le_or_gt v 0 with hv | hv
  · nlinarith [mul_nonneg (neg_nonneg.mpr hv) (neg_nonneg.mpr hx0.le)]
  · set σ : ℝ := -(κ * (a + b + 1)) / v with hσ
    have hσneg : σ < 0 := by
      rw [hσ]
      exact div_neg_of_neg_of_pos (by linarith) hv
    have hσroot : (generalComparison κ a b v q).IsRoot σ := by
      rw [IsRoot.def, hGeval]
      have : κ * (a + b + 1) + v * σ = 0 := by
        rw [hσ]
        field_simp
        ring
      rw [this, mul_zero]
    have hprod := generalStep_eval_mul_neg_of_generalComparison_root κ a b u v q σ hκ hq hQ
      hσroot hσneg
    rw [hTeval] at hprod
    have hqσ : q.eval σ = q.coeff 0 := by
      rw [hqC]
      simp
    rw [hqσ] at hprod
    have hneg : κ * a * b + u * σ < 0 := by
      by_contra hcon
      push Not at hcon
      nlinarith [mul_nonneg hc0.le hcon]
    have hσx : σ < x := by
      have : u * (σ - x) < 0 := by linarith
      by_contra hcon
      push Not at hcon
      nlinarith [mul_nonneg hu.le (sub_nonneg.mpr hcon)]
    have hvx : 0 < v * (x - σ) := mul_pos hv (by linarith)
    have : κ * (a + b + 1) + v * x = v * (x - σ) := by
      rw [hσ]
      field_simp
      ring
    rw [this]
    exact hvx


/-- **(A1)**: for a negative-simple `q` of degree `m`, at every root `x` of `T q` the comparison
polynomial has the sign `(-1)^(number of roots of T q to the right of x)`. -/
theorem generalComparison_sign_at_generalStep_root
    (κ a b u v : ℝ) (q : ℝ[X]) (m : ℕ) (hq : IsNegativeSimple q) (hqdeg : q.natDegree = m)
    (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) (hell : ∀ k ≤ m, 0 < u + v * k)
    (hQ : ∀ t ≤ 0, comparisonDefect κ a b u v t < 0) :
    ∀ x ∈ (generalStep κ a b u v q).roots,
      0 < (generalComparison κ a b v q).eval x *
        (-1 : ℝ) ^ ((generalStep κ a b u v q).roots.countP (fun r => x < r)) := by
  cases m with
  | zero =>
      exact generalComparison_sign_at_generalStep_root_of_natDegree_eq_zero κ a b u v q hq hqdeg
        hκ ha hb (by simpa using hell 0 le_rfl) hQ
  | succ m =>
      exact generalComparison_sign_at_generalStep_root_of_one_le κ a b u v q (m + 1) (by lia) hq
        hqdeg hκ ha hb hell hQ

end RealRooted.EulerBidiagonal
