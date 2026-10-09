import RealRooted.EulerBidiagonal.General
import RealRooted.Interlacing.RootCountSigns

/-!
# Comparison roots of the general Euler step

For `q` with simple negative roots, the zeros of `generalComparison κ a b v q` interlace the roots
of `q` (with one extra zero to the left when `v > 0` and one positive zero when `v < 0`), and
`generalStep q` has the sign opposite to `q` at each nonpositive comparison zero.  These are the
inputs for locating the roots of `generalStep q` (`EulerBidiagonal.Location`).
-/

open Polynomial

noncomputable section

namespace RealRooted.EulerBidiagonal

private lemma generalComparison_eq (κ a b v : ℝ) (p : ℝ[X]) :
    generalComparison κ a b v p =
      C (2 * κ) * theta p + C (κ * (a + b + 1)) * p + C v * (X * p) := by
  simp only [generalComparison, C_mul, C_add, C_1, C_ofNat]
  ring

/-- Coefficients of the comparison polynomial. -/
theorem coeff_generalComparison_succ (κ a b v : ℝ) (p : ℝ[X]) (k : ℕ) :
    (generalComparison κ a b v p).coeff (k + 1) =
      κ * (2 * ((k + 1 : ℕ) : ℝ) + (a + b + 1)) * p.coeff (k + 1) + v * p.coeff k := by
  rw [generalComparison_eq]
  simp only [coeff_add, coeff_C_mul, coeff_X_mul, coeff_theta]
  ring

/-- The constant coefficient of the comparison polynomial. -/
theorem coeff_zero_generalComparison (κ a b v : ℝ) (p : ℝ[X]) :
    (generalComparison κ a b v p).coeff 0 = κ * (a + b + 1) * p.coeff 0 := by
  rw [generalComparison_eq]
  simp only [coeff_add, coeff_C_mul, coeff_X_mul_zero, coeff_theta, Nat.cast_zero, zero_mul]
  ring

/-- Degree and leading coefficient of the comparison polynomial when `v = 0`. -/
theorem generalComparison_natDegree_of_v_eq_zero (κ a b : ℝ) (q : ℝ[X]) (m : ℕ)
    (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b)
    (hqdeg : q.natDegree = m) (hqpos : 0 < q.leadingCoeff) :
    (generalComparison κ a b 0 q).natDegree = m ∧
      0 < (generalComparison κ a b 0 q).leadingCoeff := by
  have htop : (generalComparison κ a b 0 q).coeff m =
      κ * (2 * (m : ℝ) + (a + b + 1)) * q.leadingCoeff := by
    cases m with
    | zero => 
      rw [coeff_zero_generalComparison]
      simp [leadingCoeff, hqdeg]
    | succ k =>
      rw [coeff_generalComparison_succ]
      simp [leadingCoeff, hqdeg]
  have hpos : 0 < κ * (2 * (m : ℝ) + (a + b + 1)) * q.leadingCoeff := by positivity
  have hle : (generalComparison κ a b 0 q).natDegree ≤ m := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    cases k with
    | zero => lia
    | succ k =>
      rw [coeff_generalComparison_succ]
      have h1 : q.coeff (k + 1) = 0 := coeff_eq_zero_of_natDegree_lt (by lia)
      rw [h1]
      simp
  have hdeg : (generalComparison κ a b 0 q).natDegree = m :=
    natDegree_eq_of_le_of_coeff_ne_zero hle (by rw [htop]; exact hpos.ne')
  refine ⟨hdeg, ?_⟩
  rw [leadingCoeff, hdeg, htop]
  exact hpos

/-- Degree and leading coefficient of the comparison polynomial when `v ≠ 0`. -/
theorem generalComparison_natDegree_of_v_ne_zero (κ a b v : ℝ) (q : ℝ[X]) (m : ℕ)
    (hv : v ≠ 0) (hqdeg : q.natDegree = m) (hqpos : 0 < q.leadingCoeff) :
    (generalComparison κ a b v q).natDegree = m + 1 ∧
      (generalComparison κ a b v q).leadingCoeff = v * q.leadingCoeff := by
  have htop : (generalComparison κ a b v q).coeff (m + 1) = v * q.leadingCoeff := by
    rw [coeff_generalComparison_succ]
    have h1 : q.coeff (m + 1) = 0 := coeff_eq_zero_of_natDegree_lt (by lia)
    rw [h1]
    simp [leadingCoeff, hqdeg]
  have hle : (generalComparison κ a b v q).natDegree ≤ m + 1 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    cases k with
    | zero => lia
    | succ k =>
      rw [coeff_generalComparison_succ]
      have h1 : q.coeff (k + 1) = 0 := coeff_eq_zero_of_natDegree_lt (by lia)
      have h2 : q.coeff k = 0 := coeff_eq_zero_of_natDegree_lt (by lia)
      rw [h1, h2]
      simp
  have hdeg : (generalComparison κ a b v q).natDegree = m + 1 :=
    natDegree_eq_of_le_of_coeff_ne_zero hle (by
      rw [htop]
      exact mul_ne_zero hv hqpos.ne')
  refine ⟨hdeg, ?_⟩
  rw [leadingCoeff, hdeg, htop]


/-! ## Comparison roots and the sign of `T q` there -/

/-- The sorted roots of a negative-simple polynomial, together with the roots of its comparison
polynomial interlacing them and zero, and the alternating signs of `T q` at those roots. -/
theorem exists_comparison_data
    (κ a b u v : ℝ) (q : ℝ[X]) (m : ℕ) (hm : 1 ≤ m)
    (hq : IsNegativeSimple q) (hqdeg : q.natDegree = m)
    (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b)
    (hQ : ∀ t ≤ 0, comparisonDefect κ a b u v t < 0) :
    ∃ rs A : List ℝ, rs.Pairwise (· < ·) ∧ (↑rs : Multiset ℝ) = q.roots ∧ rs.length = m ∧
      A.length = m ∧ A.Pairwise (· < ·) ∧ (∀ x ∈ A, x < 0) ∧
      (∀ x ∈ A, (generalComparison κ a b v q).IsRoot x) ∧
      ListInterlaces A (rs ++ [0]) ∧ (∀ x ∈ A, ∃ r ∈ rs, r ≤ x) ∧
      ∀ (i : ℕ) (hi : i < A.length),
        0 < (-1 : ℝ) ^ (m - i) * (generalStep κ a b u v q).eval A[i] := by
  have hqsplits : q.Splits := hq.2.1
  have hqlc : 0 < q.leadingCoeff := hq.2.2.2.1
  set rs : List ℝ := q.roots.sort (· ≤ ·) with hrs_def
  have hrs_le : rs.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hrs_eq : (↑rs : Multiset ℝ) = q.roots := Multiset.sort_eq ..
  have hrs_nodup : rs.Nodup := Multiset.coe_nodup.mp (by rw [hrs_eq]; exact hq.2.2.1.roots_nodup)
  have hrs_lt : rs.Pairwise (· < ·) :=
    (hrs_le.and hrs_nodup).imp (fun h => lt_of_le_of_ne h.1 h.2)
  have hrs_len : rs.length = m := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hqsplits, hqdeg]
  have hrs_ne : rs ≠ [] := by
    intro h
    rw [h] at hrs_len
    simp only [List.length_nil] at hrs_len
    lia
  have hrs_mem : ∀ x, x ∈ rs ↔ x ∈ q.roots := fun x => by
    rw [← hrs_eq]
    exact Multiset.mem_coe.symm
  have hrs_neg : ∀ x ∈ rs, x < 0 := fun x hx => hq.2.2.2.2 x ((hrs_mem x).mp hx)
  obtain ⟨ss, σ, hss_len, hint, hroots, hpair⟩ :=
    exists_comparison_roots_with_last κ a b v q rs (rs.getLast hrs_ne) hκ ha hb hq
      hrs_lt hrs_eq (List.getLast_mem hrs_ne)
      (fun x hx => List.Pairwise.rel_getLast hrs_le hx)
      (hrs_neg _ (List.getLast_mem hrs_ne))
  set A : List ℝ := ss ++ [σ] with hA
  have hA_len : A.length = m := by
    simp only [hA, List.length_append, List.length_singleton]
    lia
  have hA_le : ∀ x ∈ A, x ≤ 0 := by
    have := listInterlaces_left_le_of_right_le hint (c := 0) (by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact (hrs_neg x hx).le
      · simp only [List.mem_singleton] at hx
        exact hx.le)
    exact this
  have hA_root : ∀ x ∈ A, (generalComparison κ a b v q).IsRoot x := hroots
  have hA_neg : ∀ x ∈ A, x < 0 := by
    intro x hx
    refine lt_of_le_of_ne (hA_le x hx) ?_
    intro h
    have hz := (hA_root x hx).eq_zero
    have hzero := generalComparison_eval_zero_pos κ a b v q hκ ha hb hq
    rw [h] at hz
    linarith
  have hA_prod : ∀ x ∈ A, q.eval x * (generalStep κ a b u v q).eval x < 0 :=
    fun x hx => generalStep_eval_mul_neg_of_generalComparison_root κ a b u v q x hκ hq hQ
        (hA_root x hx) (hA_neg x hx)
  have hA_not : ∀ x ∈ A, x ∉ rs ++ [0] := by
    intro x hx hmem
    rcases List.mem_append.mp hmem with h | h
    · have hroot : q.eval x = 0 := isRoot_of_mem_roots ((hrs_mem x).mp h)
      have := hA_prod x hx
      rw [hroot] at this
      simp at this
    · simp only [List.mem_singleton] at h
      exact lt_irrefl _ (h ▸ hA_neg x hx)
  have hrs0_lt : (rs ++ [0]).Pairwise (· < ·) := by
    apply List.pairwise_append.mpr
    refine ⟨hrs_lt, by simp, ?_⟩
    intro x hx y hy
    simp only [List.mem_singleton] at hy
    rw [hy]
    exact hrs_neg x hx
  have hcount : ∀ (i : ℕ) (hi : i < m),
      q.roots.countP (fun r => A[i]'(by lia) < r) = m - i - 1 := by
    intro i hi
    have hc := countP_lt_getElem_of_listInterlaces_strict hint hrs0_lt hA_not (by
      simp only [List.length_append, List.length_singleton, hA_len, hrs_len])
      i (by lia)
    rw [List.countP_append] at hc
    have h0 : [(0 : ℝ)].countP (fun r => decide (A[i]'(by lia) < r)) = 1 := by
      simp [hA_neg _ (List.getElem_mem _)]
    rw [h0, hA_len] at hc
    rw [← hrs_eq, Multiset.coe_countP]
    lia
  have hqsign : ∀ (i : ℕ) (hi : i < m),
      0 < (-1 : ℝ) ^ (m - i - 1) * q.eval (A[i]'(by lia)) := by
    intro i hi
    have hnot : A[i]'(by lia) ∉ q.roots := by
      rw [← hrs_eq]
      intro h
      exact hA_not _ (List.getElem_mem _) (List.mem_append_left _ (Multiset.mem_coe.mp h))
    have := eval_sign hqsplits hqlc _ hnot
    rw [hcount i hi] at this
    linarith
  have hlow : ∀ x ∈ A, ∃ r ∈ rs, r ≤ x := by
    obtain ⟨r0, tl, hrsc⟩ : ∃ r0 tl, rs = r0 :: tl := by
      cases hh : rs with
      | nil => exact absurd hh hrs_ne
      | cons r0 tl => exact ⟨r0, tl, rfl⟩
    intro x hx
    refine ⟨r0, by rw [hrsc]; simp, ?_⟩
    rw [hrsc] at hint hrs0_lt
    exact listInterlaces_ge_head hint (hrs0_lt.imp le_of_lt) x hx
  refine ⟨rs, A, hrs_lt, hrs_eq, hrs_len, hA_len, hpair, hA_neg, hA_root, hint, hlow, ?_⟩
  · intro i hi'
    have hi : i < m := by lia
    have := generalStep_sign_of_input_sign κ a b u v q (A[i]'(by lia)) (m - i - 1)
      (hA_prod _ (List.getElem_mem _)) (hqsign i hi)
    have hmi : m - i - 1 + 1 = m - i := by lia
    rw [hmi] at this
    exact this


/-! ## The extra root of the comparison polynomial -/

/-- For `v > 0` the comparison polynomial has a root to the left of all roots of `q`. -/
theorem exists_comparison_root_lt_roots_of_pos
    (κ a b v : ℝ) (q : ℝ[X]) (m : ℕ) (hv : 0 < v) (hκ : 0 < κ)
    (hq : IsNegativeSimple q) (hqdeg : q.natDegree = m) (rs : List ℝ)
    (hrs : rs.Pairwise (· < ·)) (hrs_eq : (↑rs : Multiset ℝ) = q.roots)
    (hrs_len : rs.length = m) (hm : 1 ≤ m) :
    ∃ e, (generalComparison κ a b v q).IsRoot e ∧ ∀ r ∈ q.roots, e < r := by
  obtain ⟨r0, tl, rfl⟩ : ∃ r0 tl, rs = r0 :: tl := by
    cases rs with
    | nil =>
        simp only [List.length_nil] at hrs_len
        lia
    | cons r0 tl => exact ⟨r0, tl, rfl⟩
  have hr0_roots : r0 ∈ q.roots := by
    rw [← hrs_eq]
    simp
  have hr0root : q.IsRoot r0 := isRoot_of_mem_roots hr0_roots
  have hr0neg : r0 < 0 := hq.2.2.2.2 r0 hr0_roots
  have hall : ∀ r ∈ tl, r0 < r := fun r hr => List.rel_of_pairwise_cons hrs hr
  have hcnt : q.roots.countP (fun r => r0 < r) = m - 1 := by
    rw [← hrs_eq, Multiset.coe_countP, List.countP_cons]
    have hall' : tl.countP (fun r => decide (r0 < r)) = tl.length :=
      List.countP_eq_length.mpr (fun x hx => by simpa using hall x hx)
    simp only [hall', lt_self_iff_false, decide_false, Bool.false_eq_true, ite_false]
    simp only [List.length_cons] at hrs_len
    lia
  have hder := deriv_at_root_sign hq.2.1 hq.2.2.2.1 r0 hr0_roots
    (hq.2.2.1.roots_count_eq_one hr0root)
  rw [hcnt] at hder
  obtain ⟨hGdeg, hGlc⟩ := generalComparison_natDegree_of_v_ne_zero κ a b v q m hv.ne' hqdeg
    hq.2.2.2.1
  have hGpos : 0 < (generalComparison κ a b v q).leadingCoeff := by
    rw [hGlc]
    exact mul_pos hv hq.2.2.2.1
  obtain ⟨R, hR, hRsign⟩ := exists_left_endpoint_sign hGdeg hGpos r0
  have hG0 : (generalComparison κ a b v q).eval r0 = 2 * κ * r0 * q.derivative.eval r0 := by
    rw [generalComparison]
    simp only [eval_add, eval_mul, eval_C, eval_X, theta, hr0root.eq_zero]
    ring
  have hsq : (-1 : ℝ) ^ (m - 1) * (-1 : ℝ) ^ (m - 1) = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨m - 1, rfl⟩
  have hpow : (-1 : ℝ) ^ (m + 1) = (-1 : ℝ) ^ (m - 1) := by
    have : m + 1 = (m - 1) + 2 := by lia
    rw [this, pow_add]
    norm_num
  rw [hpow] at hRsign
  have hprod : 0 < (generalComparison κ a b v q).eval R * q.derivative.eval r0 := by
    have h := mul_pos hRsign hder
    have : (-1 : ℝ) ^ (m - 1) * (generalComparison κ a b v q).eval R *
        (q.derivative.eval r0 * (-1 : ℝ) ^ (m - 1)) =
        (generalComparison κ a b v q).eval R * q.derivative.eval r0 *
          ((-1 : ℝ) ^ (m - 1) * (-1 : ℝ) ^ (m - 1)) := by ring
    rw [this, hsq, mul_one] at h
    exact h
  have hmul : (generalComparison κ a b v q).eval R *
      (generalComparison κ a b v q).eval r0 < 0 := by
    rw [hG0]
    have h2κ : 2 * κ * r0 < 0 := mul_neg_of_pos_of_neg (by linarith) hr0neg
    calc
      _ = (2 * κ * r0) * ((generalComparison κ a b v q).eval R * q.derivative.eval r0) := by
        ring
      _ < 0 := mul_neg_of_neg_of_pos h2κ hprod
  obtain ⟨e, he1, he2, heroot⟩ :=
    MaWangInternal.exists_isRoot_between_of_eval_mul_neg (p := generalComparison κ a b v q)
      hR hmul
  refine ⟨e, heroot, ?_⟩
  intro r hr
  rw [← hrs_eq] at hr
  rcases List.mem_cons.mp (Multiset.mem_coe.mp hr) with rfl | hr
  · exact he2
  · exact he2.trans (hall r hr)

/-- For `v < 0` the comparison polynomial has a positive root. -/
theorem exists_comparison_root_pos_of_neg
    (κ a b v : ℝ) (q : ℝ[X]) (m : ℕ) (hv : v < 0) (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b)
    (hq : IsNegativeSimple q) (hqdeg : q.natDegree = m) :
    ∃ e, (generalComparison κ a b v q).IsRoot e ∧ 0 < e := by
  obtain ⟨hGdeg, hGlc⟩ := generalComparison_natDegree_of_v_ne_zero κ a b v q m hv.ne hqdeg
    hq.2.2.2.1
  have hGneg : (generalComparison κ a b v q).leadingCoeff ≤ 0 := by
    rw [hGlc]
    exact (mul_neg_of_neg_of_pos hv hq.2.2.2.1).le
  have hdegpos : 0 < (generalComparison κ a b v q).degree := by
    apply natDegree_pos_iff_degree_pos.mp
    lia
  have ht := (generalComparison κ a b v q).tendsto_atBot_of_leadingCoeff_nonpos hdegpos hGneg
  have hzero := generalComparison_eval_zero_pos κ a b v q hκ ha hb hq
  obtain ⟨e, he0, heroot⟩ :=
    exists_isRoot_ge_of_eval_nonneg_of_tendsto_atTop_atBot hzero.le ht
  refine ⟨e, heroot, lt_of_le_of_ne he0 ?_⟩
  intro h
  have := heroot.eq_zero
  rw [← h] at this
  linarith

/-- A nonzero polynomial with a nodup list of roots of full length splits with exactly these
roots. -/
theorem roots_eq_of_nodup_of_natDegree_le {G : ℝ[X]} {M : Multiset ℝ} (hG : G ≠ 0)
    (hnd : M.Nodup) (hsub : ∀ x ∈ M, G.IsRoot x) (hcard : G.natDegree ≤ M.card) :
    G.roots = M ∧ G.Splits := by
  have hle : M ≤ G.roots := by
    rw [Multiset.le_iff_subset hnd]
    intro x hx
    exact (mem_roots hG).mpr (hsub x hx)
  have hcard' : G.roots.card ≤ M.card := (card_roots' G).trans hcard
  have heq : M = G.roots := Multiset.eq_of_le_of_card_le hle hcard'
  refine ⟨heq.symm, ?_⟩
  apply splits_of_card_roots
  apply le_antisymm (card_roots' G)
  rw [← heq]
  exact hcard

end RealRooted.EulerBidiagonal
