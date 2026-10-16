module

public import RealRooted.MaWang.CountBounds

public noncomputable section

open Polynomial Filter

namespace RealRooted.MaWangInternal

/-- Sign-normalization for a product of linear factors: multiplying by
`(-1) ^ countP (s < ·)` flips exactly the negative factors and makes the product
nonnegative. -/
private lemma nonneg_normalized_prod_sub_countP :
    ∀ (ts : List ℝ) (s : ℝ),
      0 ≤ (-1 : ℝ) ^ (ts.countP (s < ·)) * (ts.map (fun x => s - x)).prod
  | [], _ => by simp
  | x :: xs, s => by
      by_cases hx : s < x
      · rw [List.countP_cons_of_pos (by lia), List.map_cons, List.prod_cons]
        convert mul_nonneg (sub_nonneg.mpr hx.le)
          (nonneg_normalized_prod_sub_countP xs s) using 1
        ring
      · rw [List.countP_cons_of_neg (by lia), List.map_cons, List.prod_cons]
        convert mul_nonneg (sub_nonneg.mpr (le_of_not_gt hx))
          (nonneg_normalized_prod_sub_countP xs s) using 1
        ring

/-- For a real-rooted polynomial with positive leading coefficient, the sign of
`F.eval s` is controlled by the parity of the number of roots strictly to the
right of `s`. -/
private lemma nonneg_normalized_eval_of_countP_gt
    {F : ℝ[X]} (hF_splits : F.Splits) (hF_pos : HasPosLeadingCoeff F)
    {ts : List ℝ} (hts_eq : (↑ts : Multiset ℝ) = F.roots) (s : ℝ) :
    0 ≤ (-1 : ℝ) ^ (ts.countP (s < ·)) * F.eval s := by
  rw [Polynomial.Splits.eval_eq_prod_roots hF_splits s, ← hts_eq]
  change 0 ≤ (-1 : ℝ) ^ ts.countP (s < ·) *
    (F.leadingCoeff * (ts.map (fun x => s - x)).prod)
  convert mul_nonneg hF_pos.le (nonneg_normalized_prod_sub_countP ts s) using 1
  ring

/-- If the parity predicted by the root count would force a positive sign, then
an assumed nonpositive value must actually be a root. -/
lemma isRoot_of_eval_nonpos_of_even_countP_gt
    {F : ℝ[X]} (hF_splits : F.Splits) (hF_pos : HasPosLeadingCoeff F)
    {ts : List ℝ} (hts_eq : (↑ts : Multiset ℝ) = F.roots) {s : ℝ}
    (hs : F.eval s ≤ 0) (heven : Even (ts.countP (s < ·))) :
    F.IsRoot s := by
  rcases heven with ⟨k, hk⟩
  have hnorm := nonneg_normalized_eval_of_countP_gt hF_splits hF_pos hts_eq s
  simp [hk] at hnorm
  rw [Polynomial.IsRoot.def]
  linarith

/-- If the parity predicted by the root count would force a negative sign, then
an assumed nonnegative value must actually be a root. -/
lemma isRoot_of_eval_nonneg_of_odd_countP_gt
    {F : ℝ[X]} (hF_splits : F.Splits) (hF_pos : HasPosLeadingCoeff F)
    {ts : List ℝ} (hts_eq : (↑ts : Multiset ℝ) = F.roots) {s : ℝ}
    (hs : 0 ≤ F.eval s) (hodd : Odd (ts.countP (s < ·))) :
    F.IsRoot s := by
  rcases hodd with ⟨k, hk⟩
  have hnorm := nonneg_normalized_eval_of_countP_gt hF_splits hF_pos hts_eq s
  have hnorm' : 0 ≤ -F.eval s := by simpa [hk, pow_add, pow_mul] using hnorm
  rw [Polynomial.IsRoot.def]
  grind

/-- In an interlacing layout, every consecutive pair on the right-hand list has
some left-hand element weakly between them. -/
private lemma exists_mem_between_of_listInterlaces_consecutive :
    ∀ {ss rs pre : List ℝ} {r₁ r₂ : ℝ} {rest : List ℝ},
      ListInterlaces ss rs →
      rs = pre ++ r₁ :: r₂ :: rest →
      ∃ s, s ∈ ss ∧ r₁ ≤ s ∧ s ≤ r₂ := by
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
            simp_all
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
                      simp_all
                  | cons a' pre' =>
                      simp [htailEq, ListInterlaces] at hint'
                      simp_all
                grind

/-- If `g ⊳ f` and `f` and `g` share no roots, then consecutive roots of `f`
are strictly increasing. -/
lemma lt_of_consecutive_of_interlaces_of_no_common
    {f g : ℝ[X]} {rs ss pre : List ℝ} {r₁ r₂ : ℝ} {rest : List ℝ}
    (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hrs_eq : (↑rs : Multiset ℝ) = f.roots)
    (hss_eq : (↑ss : Multiset ℝ) = g.roots)
    (hint : ListInterlaces ss rs)
    (hEq : rs = pre ++ r₁ :: r₂ :: rest)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    r₁ < r₂ := by
  obtain ⟨s, hs_mem, hr₁s, hs_r₂⟩ :=
    exists_mem_between_of_listInterlaces_consecutive hint hEq
  have hr₁_root : f.IsRoot r₁ := by
    apply (mem_roots hf_ne).mp
    simpa [hrs_eq] using Multiset.mem_coe.mpr (by simp_all : r₁ ∈ rs)
  have hs_root : g.IsRoot s := by
    apply (mem_roots hg_ne).mp
    simpa [hss_eq] using Multiset.mem_coe.mpr hs_mem
  grind

lemma countP_le_add_countP_gt_eq_length (ts : List ℝ) (s : ℝ) :
    ts.countP (· ≤ s) + ts.countP (s < ·) = ts.length := by
  simpa [not_le, Nat.add_comm] using
    (ts.length_eq_countP_add_countP (fun x => decide (x ≤ s))).symm

lemma countP_lt_countP_of_exists
    {ts : List ℝ} {p q : ℝ → Bool}
    (hpq : ∀ x, p x = true → q x = true)
    {a : ℝ} (ha : a ∈ ts) (hpa : p a = false) (hqa : q a = true) :
    ts.countP p < ts.countP q := by
  have hcount : (ts.filter q).countP p = ts.countP p := by
    rw [List.countP_eq_length_filter, List.countP_eq_length_filter]
    simp_rw [List.filter_filter]
    congr
    ext x
    simp_all
  have hlt : (ts.filter q).countP p < (ts.filter q).length := by
    rw [List.countP_lt_length_iff]
    grind
  grind

lemma isRoot_of_mem_sorted_roots_eq
    {f : ℝ[X]} {rs pre : List ℝ} {r : ℝ} {rest : List ℝ}
    (hrs_eq : (↑rs : Multiset ℝ) = f.roots)
    (hEq : rs = pre ++ r :: rest) :
    f.IsRoot r := by
  have hf_ne : f ≠ 0 := fun hf0 => by simp_all
  exact (mem_roots hf_ne).mp <| by
    simpa [hrs_eq] using Multiset.mem_coe.mpr (by simp_all : r ∈ rs)

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
        | cons s ss' => lia
      cases rs with
      | nil => simp at hEq
      | cons b rs' =>
          have hbEq : b :: rs' = (a :: pre) ++ r₁ :: r₂ :: rest := hEq
          cases pre with
          | nil =>
              simp only [List.cons_append, List.nil_append, List.cons.injEq] at hbEq
              rcases hbEq with ⟨rfl, rfl⟩
              have hint' : b ≤ s ∧ s ≤ r₁ ∧
                ListInterlaces ss' (r₁ :: r₂ :: rest) := by simpa [ListInterlaces] using hint
              obtain ⟨har₁, hs_r₁, htail⟩ := hint'
              have hrs_tail : (r₁ :: r₂ :: rest).Pairwise (· ≤ ·) :=
                (List.pairwise_cons.mp hrs_sorted).2
              have hr₁r₂ : r₁ ≤ r₂ := List.rel_of_pairwise_cons hrs_tail (by simp)
              have hs_factor_nonneg : 0 ≤ (r₁ - s) * (r₂ - s) := by nlinarith
              have htail_nonpos :
                  (ss'.map (fun x => r₁ - x)).prod *
                    (ss'.map (fun x => r₂ - x)).prod ≤
                  0 :=
                listInterlaces_prod_mul_prod_nonpos_at_heads htail
              simpa [mul_assoc, mul_left_comm, mul_comm] using
                mul_nonpos_of_nonneg_of_nonpos hs_factor_nonneg htail_nonpos
          | cons a' pre' =>
              simp only [List.cons_append, List.cons.injEq] at hbEq
              rcases hbEq with ⟨rfl, htailEq⟩
              have hint_rs :
                  ListInterlaces (s :: ss') (b :: a' :: pre' ++ r₁ :: r₂ :: rest) := by
                lia
              have hint' : b ≤ s ∧ s ≤ a' ∧
                  ListInterlaces ss' (a' :: pre' ++ r₁ :: r₂ :: rest) := by
                simpa [ListInterlaces] using hint_rs
              obtain ⟨_, hs_le_a', hint_tail⟩ := hint'
              have hrs_tail : (a' :: pre' ++ r₁ :: r₂ :: rest).Pairwise (· ≤ ·) :=
                by simp_all
              have ha'_le_r₁ : a' ≤ r₁ := List.Pairwise.rel_head hrs_tail (by simp)
              have hs_factor_nonneg : 0 ≤ (r₁ - s) * (r₂ - s) := by
                have hs_le_r₁ : s ≤ r₁ := le_trans hs_le_a' ha'_le_r₁
                have hr₁r₂ : r₁ ≤ r₂ := by grind
                nlinarith
              have htail_nonpos :
                  (ss'.map (fun x => r₁ - x)).prod *
                    (ss'.map (fun x => r₂ - x)).prod ≤
                  0 :=
                listInterlaces_prod_mul_prod_nonpos_of_consecutive
                  (ss := ss') (rs := a' :: pre' ++ r₁ :: r₂ :: rest)
                  (pre := a' :: pre') (rest := rest) hrs_tail hint_tail (by lia)
              simpa [mul_assoc, mul_left_comm, mul_comm] using
                mul_nonpos_of_nonneg_of_nonpos hs_factor_nonneg htail_nonpos

/-- At any consecutive pair in a sorted interlacing layout, the interlacing
polynomial has opposite-or-zero signs. -/
lemma eval_mul_eval_nonpos_of_interlacing_consecutive {g : ℝ[X]}
    (hg_splits : g.Splits)
    {ss rs pre : List ℝ} {r₁ r₂ : ℝ} {rest : List ℝ}
    (hrs_sorted : rs.Pairwise (· ≤ ·))
    (hss_eq : (↑ss : Multiset ℝ) = g.roots)
    (hint : ListInterlaces ss rs)
    (hEq : rs = pre ++ r₁ :: r₂ :: rest) :
    g.eval r₁ * g.eval r₂ ≤ 0 := by
  rw [Polynomial.Splits.eval_eq_prod_roots hg_splits r₁,
      Polynomial.Splits.eval_eq_prod_roots hg_splits r₂, ← hss_eq]
  have hprod_nonpos :
      (ss.map (fun x => r₁ - x)).prod * (ss.map (fun x => r₂ - x)).prod ≤ 0 :=
    listInterlaces_prod_mul_prod_nonpos_of_consecutive hrs_sorted hint hEq
  change (g.leadingCoeff * (ss.map (fun x => r₁ - x)).prod) *
    (g.leadingCoeff * (ss.map (fun x => r₂ - x)).prod) ≤ 0
  convert mul_nonpos_of_nonneg_of_nonpos (sq_nonneg g.leadingCoeff) hprod_nonpos using 1
  ring

/-- Strict IVT bridge: strictly opposite endpoint signs give a real root in the
open interval. -/
lemma exists_isRoot_between_of_eval_mul_neg {p : ℝ[X]} {a b : ℝ}
    (hab : a < b) (hsign : p.eval a * p.eval b < 0) :
    ∃ c, a < c ∧ c < b ∧ p.IsRoot c := by
  obtain ⟨c, hac, hcb, hc_root⟩ :=
    exists_isRoot_between_of_eval_mul_nonpos (le_of_lt hab) (le_of_lt hsign)
  have hca : c ≠ a := fun h => by simp_all
  have hcb' : c ≠ b := fun h => by simp_all
  grind

end RealRooted.MaWangInternal

namespace RealRooted

export MaWangInternal
  (listInterlaces_prod_mul_prod_nonpos_of_consecutive
    eval_mul_eval_nonpos_of_interlacing_consecutive
    exists_isRoot_between_of_eval_mul_neg)

end RealRooted
