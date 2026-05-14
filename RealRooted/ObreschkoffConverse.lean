import RealRooted.AllCombo
import RealRooted.AffineDerivative

/-!
# Obreschkoff converse: AllComboRealRooted → Prec

Wronskian orientation lemmas, the same-degree and succ-degree cases,
and the main converse `prec_of_allComboRealRooted`.
-/

set_option linter.unnecessarySimpa false

open Polynomial

noncomputable section

namespace RealRooted

set_option linter.flexible false in
section

private def wronskian (f g : ℝ[X]) : ℝ[X] :=
  g * f.derivative - f * g.derivative

private lemma wronskian_eval {f g : ℝ[X]} {x : ℝ} :
    (wronskian f g).eval x =
      g.eval x * f.derivative.eval x - f.eval x * g.derivative.eval x := by
  simp [wronskian, sub_eq_add_neg]

private lemma eval_derivative_iterateTDeriv
    (eps : ℝ) (n : ℕ) (p : ℝ[X]) (x : ℝ) :
    (iterateTDeriv eps n p).derivative.eval x =
      (iterateTDeriv eps n p.derivative).eval x := by
  have hcomm :
      (iterateTDeriv eps n p).derivative =
        iterateTDeriv eps n p.derivative := by
    simpa using iterate_derivative_iterateTDeriv eps n 1 p
  rw [hcomm]

private lemma wronskian_iterateTDeriv_eval
    (eps : ℝ) (n : ℕ) (f g : ℝ[X]) (x : ℝ) :
    (wronskian (iterateTDeriv eps n f) (iterateTDeriv eps n g)).eval x =
      (iterateTDeriv eps n g).eval x * (iterateTDeriv eps n f.derivative).eval x -
        (iterateTDeriv eps n f).eval x * (iterateTDeriv eps n g.derivative).eval x := by
  rw [wronskian_eval]
  rw [eval_derivative_iterateTDeriv, eval_derivative_iterateTDeriv]

private lemma continuous_wronskian_iterateTDeriv_eval_joint
    (n : ℕ) (f g : ℝ[X]) :
    Continuous fun z : ℝ × ℝ =>
      (wronskian (iterateTDeriv z.1 n f) (iterateTDeriv z.1 n g)).eval z.2 := by
  have hf : Continuous fun z : ℝ × ℝ => (iterateTDeriv z.1 n f).eval z.2 :=
    continuous_eval_iterateTDeriv_joint n f
  have hg : Continuous fun z : ℝ × ℝ => (iterateTDeriv z.1 n g).eval z.2 :=
    continuous_eval_iterateTDeriv_joint n g
  have hf' : Continuous fun z : ℝ × ℝ => (iterateTDeriv z.1 n f.derivative).eval z.2 :=
    continuous_eval_iterateTDeriv_joint n f.derivative
  have hg' : Continuous fun z : ℝ × ℝ => (iterateTDeriv z.1 n g.derivative).eval z.2 :=
    continuous_eval_iterateTDeriv_joint n g.derivative
  have hEq :
      (fun z : ℝ × ℝ =>
        (wronskian (iterateTDeriv z.1 n f) (iterateTDeriv z.1 n g)).eval z.2) =
      fun z : ℝ × ℝ =>
        (iterateTDeriv z.1 n g).eval z.2 * (iterateTDeriv z.1 n f.derivative).eval z.2 -
          (iterateTDeriv z.1 n f).eval z.2 * (iterateTDeriv z.1 n g.derivative).eval z.2 := by
    funext z
    exact wronskian_iterateTDeriv_eval z.1 n f g z.2
  rw [hEq]
  exact hg.mul hf' |>.sub (hf.mul hg')

private lemma continuousAt_wronskian_iterateTDeriv_eval_joint_zero
    (n : ℕ) (f g : ℝ[X]) (x : ℝ) :
    ContinuousAt
      (fun z : ℝ × ℝ =>
        (wronskian (iterateTDeriv z.1 n f) (iterateTDeriv z.1 n g)).eval z.2)
      (0, x) := by
  have hcont :
      ContinuousAt
        (fun z : ℝ × ℝ =>
          (wronskian (iterateTDeriv z.1 n f) (iterateTDeriv z.1 n g)).eval z.2)
        (0, x) :=
    (continuous_wronskian_iterateTDeriv_eval_joint n f g).continuousAt
  simpa [iterateTDeriv_zero_eps] using hcont

private lemma pos_of_norm_sub_lt_half_of_pos_local {a b : ℝ}
    (ha : 0 < a) (hab : ‖b - a‖ < a / 2) :
    0 < b := by
  have hab' : -(a / 2) < b - a ∧ b - a < a / 2 := by
    simpa [Real.norm_eq_abs] using (abs_lt.mp hab)
  linarith

private lemma exists_delta_wronskian_iterateTDeriv_eval_mul_pos_joint_at_zero
    (n : ℕ) {f g : ℝ[X]} {x : ℝ}
    (hx_eval : (wronskian f g).eval x ≠ 0) :
    ∃ δ > 0, ∀ {z : ℝ × ℝ}, ‖z - (0, x)‖ < δ →
      0 <
        (wronskian (iterateTDeriv z.1 n f) (iterateTDeriv z.1 n g)).eval z.2 *
          (wronskian f g).eval x := by
  obtain ⟨δ, hδ, hclose⟩ :=
    Metric.continuousAt_iff.mp
      (continuousAt_wronskian_iterateTDeriv_eval_joint_zero n f g x)
      (‖(wronskian f g).eval x‖ / 2) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro z hz
  have hclose' :
      ‖(wronskian (iterateTDeriv z.1 n f) (iterateTDeriv z.1 n g)).eval z.2 -
          (wronskian f g).eval x‖ <
        ‖(wronskian f g).eval x‖ / 2 := by
    simpa [dist_eq_norm, iterateTDeriv_zero_eps] using hclose hz
  rcases lt_or_gt_of_ne hx_eval with hx_neg | hx_pos
  · have hneg_iter :
        (wronskian (iterateTDeriv z.1 n f) (iterateTDeriv z.1 n g)).eval z.2 < 0 := by
      have hneg_norm :
          ‖-(wronskian (iterateTDeriv z.1 n f) (iterateTDeriv z.1 n g)).eval z.2 -
              (-(wronskian f g).eval x)‖ =
            ‖(wronskian (iterateTDeriv z.1 n f) (iterateTDeriv z.1 n g)).eval z.2 -
                (wronskian f g).eval x‖ := by
        rw [sub_eq_add_neg, neg_neg]
        have hEq :
            -(wronskian (iterateTDeriv z.1 n f) (iterateTDeriv z.1 n g)).eval z.2 +
                (wronskian f g).eval x =
              -((wronskian (iterateTDeriv z.1 n f) (iterateTDeriv z.1 n g)).eval z.2 -
                (wronskian f g).eval x) := by
          ring
        rw [hEq, norm_neg]
      have hclose_neg0 :
          ‖-(wronskian (iterateTDeriv z.1 n f) (iterateTDeriv z.1 n g)).eval z.2 -
              (-(wronskian f g).eval x)‖ <
            ‖(wronskian f g).eval x‖ / 2 := by
        rw [hneg_norm]
        exact hclose'
      have hclose_neg :
          ‖-(wronskian (iterateTDeriv z.1 n f) (iterateTDeriv z.1 n g)).eval z.2 -
              (-(wronskian f g).eval x)‖ <
            (-(wronskian f g).eval x) / 2 := by
        simpa [Real.norm_eq_abs, abs_of_neg hx_neg] using hclose_neg0
      have hpos_neg_iter :
          0 < -(wronskian (iterateTDeriv z.1 n f) (iterateTDeriv z.1 n g)).eval z.2 :=
        pos_of_norm_sub_lt_half_of_pos_local (by linarith) hclose_neg
      linarith
    exact mul_pos_of_neg_of_neg hneg_iter hx_neg
  · have hpos_iter :
        0 < (wronskian (iterateTDeriv z.1 n f) (iterateTDeriv z.1 n g)).eval z.2 :=
      pos_of_norm_sub_lt_half_of_pos_local hx_pos
        (by simpa [Real.norm_eq_abs, abs_of_pos hx_pos] using hclose')
    exact mul_pos hpos_iter hx_pos

private lemma natDegree_bounds_of_prec_local {f g : ℝ[X]} (hfg : Prec f g) :
    f.natDegree ≤ g.natDegree ∧ g.natDegree ≤ f.natDegree + 1 := by
  rcases hfg with ⟨hf, hg, ss, rs, _hss, _hrs, hss_eq, hrs_eq, hshape⟩
  have hss_len : ss.length = f.natDegree := by
    rw [← Multiset.coe_card, hss_eq, hf.2]
  have hrs_len : rs.length = g.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, hg.2]
  rcases hshape with ⟨hlen, _⟩ | ⟨hlen, _⟩ <;> omega

/-- Translation-invariant form of
`listInterlaces_of_listAlternates_append_zero`: if a same-degree alternating
layout ends with one extra rightmost point `uR`, then deleting that endpoint
produces a genuine `ListInterlaces` layout. -/
private lemma listInterlaces_of_listAlternates_append_right
    {ss qs : List ℝ} {uR : ℝ}
    (hlen : qs.length + 1 = ss.length)
    (halt : ListAlternates ss (qs ++ [uR])) :
    ListInterlaces qs ss := by
  have halt0 :
      ListAlternates (ss.map (· - uR)) ((qs.map (· - uR)) ++ [0]) := by
    simpa [List.map_append] using listAlternates_map_sub_const halt uR
  have hlen0 : (qs.map (· - uR)).length + 1 = (ss.map (· - uR)).length := by
    simpa using hlen
  have hint0 :
      ListInterlaces (qs.map (· - uR)) (ss.map (· - uR)) :=
    listInterlaces_of_listAlternates_append_zero
      (qs.map (· - uR)) (ss.map (· - uR)) hlen0 halt0
  have hfun :
      ((fun x : ℝ => x + uR) ∘ fun x => x - uR) = fun x => x := by
    funext x
    change (x - uR) + uR = x
    ring_nf
  simpa [List.map_map, Function.comp, hfun] using
    listInterlaces_map_sub_const hint0 (-uR)

private lemma listInterlaces_left_le_of_right_le_local {ss rs : List ℝ} {c : ℝ}
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
              rcases hint with ⟨hr₁s, hs_r₂, htail⟩
              intro t ht
              simp at ht
              rcases ht with rfl | ht
              · exact le_trans hs_r₂ (hrs r₂ (by simp))
              · exact ih htail (fun r hr => hrs r (by simp [hr])) t ht

private lemma listAlternates_left_le_of_right_le_local {ss rs : List ℝ} {c : ℝ}
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
          · exact listInterlaces_left_le_of_right_le_local htail
              (fun x hx => hrs x (by simp [hx])) t ht

private lemma roots_le_of_prec_right_local {f g : ℝ[X]} {c : ℝ}
    (h : Prec f g)
    (hg_le : ∀ r ∈ g.roots, r ≤ c) :
    ∀ r ∈ f.roots, r ≤ c := by
  rcases h with ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩
  have hrs_le : ∀ r ∈ rs, r ≤ c := by
    intro r hr
    exact hg_le r (by rw [← hrs_eq]; exact Multiset.mem_coe.mpr hr)
  intro r hr
  have hr' : r ∈ ss := by
    have : r ∈ (↑ss : Multiset ℝ) := by simpa [hss_eq] using hr
    exact Multiset.mem_coe.mp this
  rcases hshape with ⟨_, hint⟩ | ⟨_, halt⟩
  · exact listInterlaces_left_le_of_right_le_local hint hrs_le r hr'
  · exact listAlternates_left_le_of_right_le_local halt hrs_le r hr'

private lemma listInterlaces_tail_pair_prod_nonneg_local :
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

private lemma prod_mul_prod_eq_prod_pairwise_local (l : List ℝ) (a b : ℝ) :
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

/-- Local public-in-file replacement for the private Ma--Wang product lemma:
at consecutive points on the right-hand list of a `ListInterlaces` layout, the
interlacing-product contribution is nonpositive. This is the exact list-level
sign input needed later for the same-degree cancellation branch. -/
private lemma listInterlaces_prod_mul_prod_nonpos_at_heads_local
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
    exact listInterlaces_tail_pair_prod_nonneg_local hr₁r₂ htail
  have htail_nonneg' :
      0 ≤ (ss'.map (fun x => r₁ - x)).prod * (ss'.map (fun x => r₂ - x)).prod := by
    rw [prod_mul_prod_eq_prod_pairwise_local ss' r₁ r₂]
    exact htail_nonneg
  calc
    ((s :: ss').map (fun x => r₁ - x)).prod * ((s :: ss').map (fun x => r₂ - x)).prod
        = ((r₁ - s) * (r₂ - s)) *
            ((ss'.map (fun x => r₁ - x)).prod * (ss'.map (fun x => r₂ - x)).prod) := by
              simp [mul_assoc, mul_left_comm]
    _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hs_head_nonpos htail_nonneg'

private lemma listInterlaces_prod_mul_prod_nonpos_of_consecutive_local :
    ∀ {ss rs pre : List ℝ} {r₁ r₂ : ℝ} {rest : List ℝ},
      rs.Pairwise (· ≤ ·) →
      ListInterlaces ss rs →
      rs = pre ++ r₁ :: r₂ :: rest →
      (ss.map (fun x => r₁ - x)).prod * (ss.map (fun x => r₂ - x)).prod ≤ 0
  | ss, rs, [], r₁, r₂, rest, _, hint, hEq => by
      subst hEq
      exact listInterlaces_prod_mul_prod_nonpos_at_heads_local hint
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
              simp at hbEq
              rcases hbEq with ⟨rfl, rfl⟩
              have hint' :
                  b ≤ s ∧ s ≤ r₁ ∧
                    ListInterlaces ss' (r₁ :: r₂ :: rest) := by
                simpa [ListInterlaces] using hint
              obtain ⟨hb_r₁, hs_r₁, htail⟩ := hint'
              have hrs_tail : (r₁ :: r₂ :: rest).Pairwise (· ≤ ·) :=
                (List.pairwise_cons.mp hrs_sorted).2
              have hr₁r₂ : r₁ ≤ r₂ := List.rel_of_pairwise_cons hrs_tail (by simp)
              have hs_factor_nonneg : 0 ≤ (r₁ - s) * (r₂ - s) := by
                nlinarith
              have htail_nonpos :
                  (ss'.map (fun x => r₁ - x)).prod *
                    (ss'.map (fun x => r₂ - x)).prod ≤ 0 := by
                exact listInterlaces_prod_mul_prod_nonpos_at_heads_local htail
              calc
                ((s :: ss').map (fun x => r₁ - x)).prod *
                    ((s :: ss').map (fun x => r₂ - x)).prod
                    = ((r₁ - s) * (r₂ - s)) *
                        ((ss'.map (fun x => r₁ - x)).prod *
                          (ss'.map (fun x => r₂ - x)).prod) := by
                          simp [mul_assoc, mul_left_comm]
                _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs_factor_nonneg htail_nonpos
          | cons a' pre' =>
              simp at hbEq
              rcases hbEq with ⟨rfl, htailEq⟩
              have hint_rs :
                  ListInterlaces (s :: ss') (b :: a' :: pre' ++ r₁ :: r₂ :: rest) := by
                simpa [htailEq] using hint
              have hint' :
                  b ≤ s ∧ s ≤ a' ∧
                    ListInterlaces ss' (a' :: pre' ++ r₁ :: r₂ :: rest) := by
                simpa [ListInterlaces] using hint_rs
              obtain ⟨_, hs_le_a', hint_tail⟩ := hint'
              have hrs_tail : (a' :: pre' ++ r₁ :: r₂ :: rest).Pairwise (· ≤ ·) := by
                simpa [htailEq] using (List.pairwise_cons.mp hrs_sorted).2
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
                  (ss'.map (fun x => r₁ - x)).prod * (ss'.map (fun x => r₂ - x)).prod ≤ 0 :=
                listInterlaces_prod_mul_prod_nonpos_of_consecutive_local
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

/-- Local consecutive-root sign lemma for an interlacer. This is the exact
public-in-file replacement for the private Ma--Wang helper needed in the
same-degree forward branch. -/
private lemma eval_mul_eval_nonpos_of_interlacing_consecutive_local {g : ℝ[X]}
    (hg : IsRealRooted g)
    {ss rs pre : List ℝ} {r₁ r₂ : ℝ} {rest : List ℝ}
    (hrs_sorted : rs.Pairwise (· ≤ ·))
    (hss_eq : (↑ss : Multiset ℝ) = g.roots)
    (hint : ListInterlaces ss rs)
    (hEq : rs = pre ++ r₁ :: r₂ :: rest) :
    g.eval r₁ * g.eval r₂ ≤ 0 := by
  rw [eval_eq_leadingCoeff_mul_prod_sub hg r₁,
    eval_eq_leadingCoeff_mul_prod_sub hg r₂, ← hss_eq]
  have hprod_nonpos :
      (ss.map (fun x => r₁ - x)).prod * (ss.map (fun x => r₂ - x)).prod ≤ 0 :=
    listInterlaces_prod_mul_prod_nonpos_of_consecutive_local hrs_sorted hint hEq
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

private lemma eval_mul_eval_neg_of_interlaces_consecutive_of_no_common
    {f g : ℝ[X]}
    (hgf : Interlaces g f)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
      f.roots.sort (· ≤ ·) = pre ++ r₁ :: r₂ :: rest →
      g.eval r₁ * g.eval r₂ < 0 := by
  obtain ⟨hf, hg, _hdeg, rs, ss, hrs_sorted, hss_sorted, hrs_eq, hss_eq, hint⟩ := hgf
  intro pre r₁ r₂ rest hEq
  have hrs_sort : rs = f.roots.sort (· ≤ ·) := by
    apply List.Perm.eq_of_pairwise' hrs_sorted (Multiset.pairwise_sort ..)
    exact Multiset.coe_eq_coe.mp (hrs_eq.trans (Multiset.sort_eq ..).symm)
  have hEq_rs : rs = pre ++ r₁ :: r₂ :: rest := by
    calc
      rs = f.roots.sort (· ≤ ·) := hrs_sort
      _ = pre ++ r₁ :: r₂ :: rest := hEq
  have hnonpos :
      g.eval r₁ * g.eval r₂ ≤ 0 :=
    eval_mul_eval_nonpos_of_interlacing_consecutive_local hg hrs_sorted hss_eq hint hEq_rs
  have hr₁_root : f.IsRoot r₁ := by
    apply (mem_roots hf.1).mp
    rw [← hrs_eq]
    exact Multiset.mem_coe.mpr (by rw [hEq_rs]; simp)
  have hr₂_root : f.IsRoot r₂ := by
    apply (mem_roots hf.1).mp
    rw [← hrs_eq]
    exact Multiset.mem_coe.mpr (by rw [hEq_rs]; simp)
  have hg₁_ne : g.eval r₁ ≠ 0 := by
    intro hg₁
    exact hno r₁ hr₁_root (by simpa [Polynomial.IsRoot.def] using hg₁)
  have hg₂_ne : g.eval r₂ ≠ 0 := by
    intro hg₂
    exact hno r₂ hr₂_root (by simpa [Polynomial.IsRoot.def] using hg₂)
  exact lt_of_le_of_ne hnonpos (by simpa using mul_ne_zero hg₁_ne hg₂_ne)

private lemma mul_neg_of_mul_neg_of_mul_neg_local {a b c d : ℝ}
    (hab : a * b < 0) (hcd : c * d < 0) (hbd : b * d < 0) :
    a * c < 0 := by
  have hb_ne : b ≠ 0 := by
    intro hb0
    simp [hb0] at hab
  rcases lt_or_gt_of_ne hb_ne with hb | hb
  · have hd : 0 < d := by
      nlinarith
    have ha : 0 < a := by
      nlinarith
    have hc : c < 0 := by
      nlinarith
    nlinarith
  · have hd : d < 0 := by
      nlinarith
    have ha : a < 0 := by
      nlinarith
    have hc : 0 < c := by
      nlinarith
    nlinarith

/-- Degree-drop converse to the usual Ma--Wang assembly step: if a nonzero
polynomial `F` has strictly alternating signs on consecutive roots of a
real-rooted polynomial `f`, and `F` has strictly smaller degree than `f`, then
the degree gap is forced to be exactly one and `F` is the left interlacer of
`f`.

This is the shape needed for the same-degree Obreschkoff forward direction when
the top coefficient cancels in `α f + β g`: the canceled combination should not
sit on the right of `f`, but rather become the common interlacer on the left. -/
private theorem interlaces_of_consecutive_signs_of_natDegree_lt
    {f F : ℝ[X]}
    (hf : IsRealRooted f) (hF_ne : F ≠ 0)
    (hdeg_lt : F.natDegree < f.natDegree)
    (hsign :
      let rs := f.roots.sort (· ≤ ·)
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        F.eval r₁ * F.eval r₂ < 0) :
    Interlaces F f := by
  let rs := f.roots.sort (· ≤ ·)
  have hrs_eq : (↑rs : Multiset ℝ) = f.roots := Multiset.sort_eq ..
  have hrs_sorted : rs.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  obtain ⟨us, hus_len, hus_int, hus_roots, hus_pw⟩ :=
    exists_roots_strictly_interlacing_of_consecutive_signs
      (F := F) hrs_sorted (by simpa [rs] using hsign)
  have hrs_len : rs.length = f.natDegree := by
    rw [show rs = f.roots.sort (· ≤ ·) by rfl, Multiset.length_sort, hf.2]
  have hus_sub : (↑us : Multiset ℝ) ≤ F.roots := by
    rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr (hus_pw.imp ne_of_lt))]
    intro x hx
    exact (mem_roots hF_ne).mpr (hus_roots x (Multiset.mem_coe.mp hx))
  have hus_card_le : us.length ≤ F.natDegree := by
    calc
      us.length = (↑us : Multiset ℝ).card := (Multiset.coe_card _).symm
      _ ≤ F.roots.card := Multiset.card_le_card hus_sub
      _ ≤ F.natDegree := card_roots' F
  have hus_len_f : us.length = f.natDegree - 1 := by
    rwa [hrs_len] at hus_len
  have hdeg : F.natDegree + 1 = f.natDegree := by
    omega
  have hus_len_deg : us.length = F.natDegree := by
    omega
  have hus_eq : (↑us : Multiset ℝ) = F.roots :=
    Multiset.eq_of_le_of_card_le hus_sub (by
      calc
        F.roots.card ≤ F.natDegree := card_roots' F
        _ = us.length := hus_len_deg.symm
        _ = (↑us : Multiset ℝ).card := (Multiset.coe_card _).symm)
  have hF : IsRealRooted F := by
    refine ⟨hF_ne, ?_⟩
    rw [← hus_eq, Multiset.coe_card, hus_len_deg]
  exact
    ⟨hf, hF, hdeg, rs, us, hrs_sorted, hus_pw.imp le_of_lt, hrs_eq, hus_eq, hus_int⟩

/-- The right-family pair `(f + g, f + 2g)` stays in the same Obreschkoff plane.

This is a convenient basis change for later converse work: every linear
combination of these two polynomials is still a linear combination of `(f, g)`,
so `AllComboRealRooted` is inherited for free. -/
private lemma allComboRealRooted_right_family_one_two
    {f g : ℝ[X]} (hall : AllComboRealRooted f g) :
    AllComboRealRooted (f + g) (f + C (2 : ℝ) * g) := by
  intro α β
  have hrewrite :
      C α * (f + g) + C β * (f + C (2 : ℝ) * g) =
        C (α + β) * f + C (α + 2 * β) * g := by
    calc
      C α * (f + g) + C β * (f + C (2 : ℝ) * g)
          = (C α * f + C β * f) + (C α * g + C (β * 2) * g) := by
              rw [mul_add, mul_add, C_mul]
              ring
      _ = (C α + C β) * f + (C α + C (β * 2)) * g := by
            rw [← add_mul, ← add_mul]
      _ = C (α + β) * f + C (α + β * 2) * g := by
            rw [← C_add, ← C_add]
      _ = C (α + β) * f + C (α + 2 * β) * g := by
            congr 2
            ring_nf
  simpa [hrewrite] using hall (α + β) (α + 2 * β)

/-- A common root of `(f + g, f + 2g)` is already a common root of `(f, g)`.

This packages the elementary subtraction argument needed if the converse is
rerouted through the `f + g`, `f + 2g` family. -/
private lemma no_common_root_right_family_one_two_of_no_common
    {f g : ℝ[X]}
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    ∀ r, (f + g).IsRoot r → ¬ (f + C (2 : ℝ) * g).IsRoot r := by
  intro r hfg_root hfg2_root
  have hfg_eval : (f + g).eval r = 0 := by
    simpa [Polynomial.IsRoot.def] using hfg_root
  have hfg2_eval : (f + C (2 : ℝ) * g).eval r = 0 := by
    simpa [Polynomial.IsRoot.def] using hfg2_root
  rw [Polynomial.eval_add] at hfg_eval
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] at hfg2_eval
  have hg_eval : g.eval r = 0 := by
    linarith
  have hf_eval : f.eval r = 0 := by
    linarith
  exact hno r
    (by simpa [Polynomial.IsRoot.def] using hf_eval)
    (by simpa [Polynomial.IsRoot.def] using hg_eval)

/-- Safe degree/leading-coefficient packaging for the right-family reroute.

The heuristic "`(f + g, f + 2g)` regularizes to the top degree" is only
reliably true after sign-normalizing so both original leading coefficients are
positive; otherwise the same-degree case can still cancel at the top. This
helper records the version that is actually stable in Lean. -/
private lemma right_family_degree_data_of_posLeadingCoeff
    {f g : ℝ[X]}
    (hdeg : f.natDegree ≤ g.natDegree)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g) :
    HasPosLeadingCoeff (f + g) ∧
      HasPosLeadingCoeff (f + C (2 : ℝ) * g) ∧
      (f + g).natDegree = g.natDegree ∧
      (f + C (2 : ℝ) * g).natDegree = g.natDegree := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using
      PosComboRealRooted.family_hasPosLeadingCoeff_right
        (f := f) (g := g) hdeg hf_pos hg_pos (μ := 1) zero_lt_one
  · simpa using
      PosComboRealRooted.family_hasPosLeadingCoeff_right
        (f := f) (g := g) hdeg hf_pos hg_pos (μ := 2) (by norm_num)
  · simpa using
      PosComboRealRooted.family_natDegree_right
        (f := f) (g := g) hdeg hf_pos hg_pos (μ := 1) zero_lt_one
  · simpa using
      PosComboRealRooted.family_natDegree_right
        (f := f) (g := g) hdeg hf_pos hg_pos (μ := 2) (by norm_num)

/-- Under the positive-leading and degree-order hypotheses, the stronger
`AllComboRealRooted` assumption implies the positive-combination hypothesis
used by the same-degree converse infrastructure. -/
private lemma posComboRealRooted_of_allComboRealRooted_of_natDegree_le
    {f g : ℝ[X]}
    (hall : AllComboRealRooted f g)
    (hdeg : f.natDegree ≤ g.natDegree)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g) :
    PosComboRealRooted f g := by
  intro lam μ hlam hμ
  rcases hall lam μ with hzero | hrr
  · have hcomb_pos : HasPosLeadingCoeff (C lam * f + C μ * g) := by
      exact
        hasPosLeadingCoeff_pos_combo_of_natDegree_le_right
          hdeg hf_pos hg_pos hlam hμ
    exfalso
    have : 0 < (0 : ℝ) := by
      simpa [HasPosLeadingCoeff, hzero] using hcomb_pos
    exact lt_irrefl 0 this
  · exact hrr

/-- At a root of `f + 2g`, the companion family member `f + g` has the
opposite sign of `g`. Under the no-common-root hypothesis this sign is strict,
because `g` cannot vanish there. This is one of the Ma--Wang style transport
inputs for pushing an orientation of the right family back toward `g`. -/
private lemma eval_mul_right_family_one_neg_at_root_two_of_no_common
    {f g : ℝ[X]}
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    ∀ r, (f + C (2 : ℝ) * g).IsRoot r → (f + g).eval r * g.eval r < 0 := by
  intro r hroot
  have hq_eval : (f + C (2 : ℝ) * g).eval r = 0 := by
    simpa [Polynomial.IsRoot.def] using hroot
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] at hq_eval
  have hp_eval : (f + g).eval r = -g.eval r := by
    rw [Polynomial.eval_add]
    linarith
  have hg_ne : g.eval r ≠ 0 := by
    intro hg0
    have hf0 : f.eval r = 0 := by
      linarith
    exact hno r
      (by simpa [Polynomial.IsRoot.def] using hf0)
      (by simpa [Polynomial.IsRoot.def] using hg0)
  calc
    (f + g).eval r * g.eval r = -(g.eval r) ^ 2 := by
      rw [hp_eval]
      ring
    _ < 0 := by
      have hsq : 0 < (g.eval r) ^ 2 := sq_pos_iff.mpr hg_ne
      nlinarith

/-- At a root of `f + g`, the other family member `f + 2g` has the opposite
sign of `f`. As above, the no-common-root hypothesis makes the sign strict.
This is the symmetric Ma--Wang input when one wants to transport an orientation
of the right family back toward `f`. -/
private lemma eval_mul_right_family_two_neg_at_root_one_of_no_common
    {f g : ℝ[X]}
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    ∀ r, (f + g).IsRoot r → (f + C (2 : ℝ) * g).eval r * f.eval r < 0 := by
  intro r hroot
  have hp_eval0 : (f + g).eval r = 0 := by
    simpa [Polynomial.IsRoot.def] using hroot
  rw [Polynomial.eval_add] at hp_eval0
  have hq_eval : (f + C (2 : ℝ) * g).eval r = -f.eval r := by
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    linarith
  have hf_ne : f.eval r ≠ 0 := by
    intro hf0
    have hg0 : g.eval r = 0 := by
      linarith
    exact hno r
      (by simpa [Polynomial.IsRoot.def] using hf0)
      (by simpa [Polynomial.IsRoot.def] using hg0)
  calc
    (f + C (2 : ℝ) * g).eval r * f.eval r = -(f.eval r) ^ 2 := by
      rw [hq_eval]
      ring
    _ < 0 := by
      have hsq : 0 < (f.eval r) ^ 2 := sq_pos_iff.mpr hf_ne
      nlinarith

/-- `AllComboRealRooted` is preserved by any linear change of basis in the
`(f, g)`-plane. No invertibility is needed for the forward direction: every
linear combination of the new pair is visibly a linear combination of the old
pair. -/
private lemma allComboRealRooted_linear_change
    {f g p q : ℝ[X]} {a b c d : ℝ}
    (hp : p = C a * f + C b * g)
    (hq : q = C c * f + C d * g)
    (hall : AllComboRealRooted f g) :
    AllComboRealRooted p q := by
  intro α β
  have hrewrite :
      C α * p + C β * q =
        C (α * a + β * c) * f + C (α * b + β * d) * g := by
    rw [hp, hq]
    calc
      C α * (C a * f + C b * g) + C β * (C c * f + C d * g)
          = (C α * (C a * f) + C α * (C b * g)) +
              (C β * (C c * f) + C β * (C d * g)) := by
                rw [mul_add, mul_add]
      _ = (C (α * a) * f + C (α * b) * g) +
            (C (β * c) * f + C (β * d) * g) := by
              simp [C_mul, mul_assoc]
      _ = (C (α * a) * f + C (β * c) * f) +
            (C (α * b) * g + C (β * d) * g) := by
              ring
      _ = C (α * a + β * c) * f + C (α * b + β * d) * g := by
            rw [← add_mul, ← add_mul, ← C_add, ← C_add]
  rw [hrewrite]
  exact hall (α * a + β * c) (α * b + β * d)

/-- No-common-roots is preserved by an invertible linear change of basis in the
`(f, g)`-plane. This is the algebraic bridge needed for the "pick a special
combination and a complementary combination" strategy. -/
private lemma no_common_root_linear_change
    {f g p q : ℝ[X]} {a b c d : ℝ}
    (hp : p = C a * f + C b * g)
    (hq : q = C c * f + C d * g)
    (hdet : a * d - b * c ≠ 0)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    ∀ r, p.IsRoot r → ¬ q.IsRoot r := by
  intro r hpr hqr
  have hp_eval : p.eval r = 0 := by
    simpa [Polynomial.IsRoot.def] using hpr
  have hq_eval : q.eval r = 0 := by
    simpa [Polynomial.IsRoot.def] using hqr
  rw [hp, eval_add, eval_mul, eval_mul, eval_C, eval_C] at hp_eval
  rw [hq, eval_add, eval_mul, eval_mul, eval_C, eval_C] at hq_eval
  have hdet_eval :
      (a * d - b * c) * f.eval r = 0 := by
    have h1 := congrArg (fun x : ℝ => d * x) hp_eval
    have h2 := congrArg (fun x : ℝ => b * x) hq_eval
    nlinarith
  have hf_eval : f.eval r = 0 := by
    exact (mul_eq_zero.mp hdet_eval).resolve_left hdet
  have hdet_eval' :
      (a * d - b * c) * g.eval r = 0 := by
    have h1 := congrArg (fun x : ℝ => a * x) hq_eval
    have h2 := congrArg (fun x : ℝ => c * x) hp_eval
    nlinarith
  have hg_eval : g.eval r = 0 := by
    exact (mul_eq_zero.mp hdet_eval').resolve_left hdet
  exact hno r
    (by simpa [Polynomial.IsRoot.def] using hf_eval)
    (by simpa [Polynomial.IsRoot.def] using hg_eval)

private lemma wronskian_eval_ne_zero_of_eq_zero_or_simple_combo
    {f g : ℝ[X]}
    (hf : IsRealRooted f) (hg : IsRealRooted g)
    (hcombo :
      ∀ α β : ℝ,
        C α * f + C β * g = 0 ∨
          (IsRealRooted (C α * f + C β * g) ∧
            HasSimpleRoots (C α * f + C β * g)))
    (hdeg_pos : 0 < max f.natDegree g.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {x : ℝ} :
    (wronskian f g).eval x ≠ 0 := by
  let p : ℝ[X] := C (g.eval x) * f + C (-f.eval x) * g
  have hp_root : p.IsRoot x := by
    simp [p, Polynomial.IsRoot.def]
    ring
  intro hw
  have hp_der_eval_eq : p.derivative.eval x = (wronskian f g).eval x := by
    simp [p, wronskian_eval]
    ring
  have hp_der_eval : p.derivative.eval x = 0 := by
    rw [hp_der_eval_eq, hw]
  have hp_der_root : p.derivative.IsRoot x := by
    simpa [Polynomial.IsRoot.def] using hp_der_eval
  rcases hcombo (g.eval x) (-f.eval x) with hp0 | ⟨hp_rr, hp_simple⟩
  · by_cases hgx0 : g.eval x = 0
    · have hmul : C (-f.eval x) * g = 0 := by
        simpa [p, hgx0] using hp0
      rcases mul_eq_zero.mp hmul with hC | hg0
      · have hfx0 : f.eval x = 0 := by
          have : -f.eval x = 0 := by simpa using C_eq_zero.mp hC
          linarith
        exact hno x
          (by simpa [Polynomial.IsRoot.def] using hfx0)
          (by simpa [Polynomial.IsRoot.def] using hgx0)
      · exact hg.1 hg0 |> False.elim
    · have hEq1 : C (g.eval x) * f = C (f.eval x) * g := by
        have hEq := congrArg (fun q : ℝ[X] => q + C (f.eval x) * g) hp0
        simpa [p, add_assoc, add_comm, add_left_comm, sub_eq_add_neg] using hEq
      have hscalar : f = C (f.eval x / g.eval x) * g := by
        ext n
        have hcoeff := congrArg (fun q : ℝ[X] => q.coeff n) hEq1
        simp [coeff_C_mul]
        apply (mul_left_cancel₀ hgx0)
        calc
          g.eval x * f.coeff n = f.eval x * g.coeff n := by
            simpa [coeff_C_mul] using hcoeff
          _ = g.eval x * ((f.eval x / g.eval x) * g.coeff n) := by
            field_simp [hgx0]
      have hfx0 : f.eval x ≠ 0 := by
        intro hfx0
        have hf0 : f = 0 := by
          rw [hscalar, hfx0]
          simp
        exact hf.1 hf0
      have hscale_ne : f.eval x / g.eval x ≠ 0 := div_ne_zero hfx0 hgx0
      have hdeg_eq : f.natDegree = g.natDegree := by
        rw [hscalar, natDegree_C_mul hscale_ne]
      have hg_deg_pos : 0 < g.natDegree := by
        have hmax_eq : max f.natDegree g.natDegree = g.natDegree := by
          rw [hdeg_eq]
          simp
        rw [← hmax_eq]
        exact hdeg_pos
      obtain ⟨r, hr⟩ :=
        exists_isRoot_of_isRealRooted_of_not_isUnit hg
          (not_isUnit_of_natDegree_pos g hg_deg_pos)
      have hfr : f.IsRoot r := by
        have hgr_eval : g.eval r = 0 := by
          simpa [Polynomial.IsRoot.def] using hr
        have hfr_eval : f.eval r = 0 := by
          rw [hscalar, eval_mul, eval_C]
          simp [hgr_eval]
        simpa [Polynomial.IsRoot.def] using hfr_eval
      exact hno r hfr hr
  · have hp_ne : p ≠ 0 := hp_rr.1
    have hmult : 1 < p.rootMultiplicity x := by
      exact (one_lt_rootMultiplicity_iff_isRoot hp_ne).2 ⟨hp_root, hp_der_root⟩
    have hsimple := hp_simple x hp_root
    rw [hsimple] at hmult
    omega

private lemma hasSimpleRoots_combo_of_wronskian_eval_ne_zero
    {f g : ℝ[X]} {α β : ℝ}
    (hp : IsRealRooted (C α * f + C β * g))
    (hW_ne : ∀ x : ℝ, (wronskian f g).eval x ≠ 0) :
    HasSimpleRoots (C α * f + C β * g) := by
  let p : ℝ[X] := C α * f + C β * g
  intro r hr
  have hp_ne : p ≠ 0 := hp.1
  by_contra hmult_ne
  have hmult_pos : 0 < p.rootMultiplicity r := by
    exact (rootMultiplicity_pos hp_ne).mpr hr
  have hmult_ge2 : 2 ≤ p.rootMultiplicity r := by
    have hmult_ge1 : 1 ≤ p.rootMultiplicity r := Nat.succ_le_of_lt hmult_pos
    have hmult_not1 : p.rootMultiplicity r ≠ 1 := by
      simpa using hmult_ne
    omega
  have hder_root : p.derivative.IsRoot r :=
    isRoot_derivative_of_rootMultiplicity_ge_two hmult_ge2
  have hp_eval : p.eval r = 0 := by
    simpa [p, Polynomial.IsRoot.def] using hr
  have hp_der_eval : p.derivative.eval r = 0 := by
    simpa [p, Polynomial.IsRoot.def] using hder_root
  have hp_eval' : α * f.eval r + β * g.eval r = 0 := by
    simpa [p, eval_add, eval_mul, eval_C] using hp_eval
  have hp_der_eval' : α * f.derivative.eval r + β * g.derivative.eval r = 0 := by
    simpa [p, derivative_add, derivative_C_mul, eval_add, eval_mul, eval_C] using hp_der_eval
  have hαβ_ne : α ≠ 0 ∨ β ≠ 0 := by
    by_contra h
    push_neg at h
    rcases h with ⟨hα0, hβ0⟩
    have : p = 0 := by
      simp [p, hα0, hβ0]
    exact hp_ne this
  have hW_zero : (wronskian f g).eval r = 0 := by
    rcases hαβ_ne with hα | hβ
    · have hmul : α * (wronskian f g).eval r = 0 := by
        calc
          α * (wronskian f g).eval r
              = g.eval r * (α * f.derivative.eval r + β * g.derivative.eval r) -
                  g.derivative.eval r * (α * f.eval r + β * g.eval r) := by
                    rw [wronskian_eval]
                    ring
          _ = 0 := by rw [hp_der_eval', hp_eval']; ring
      exact (mul_eq_zero.mp hmul).resolve_left hα
    · have hmul : β * (wronskian f g).eval r = 0 := by
        calc
          β * (wronskian f g).eval r
              = f.derivative.eval r * (α * f.eval r + β * g.eval r) -
                  f.eval r * (α * f.derivative.eval r + β * g.derivative.eval r) := by
                    rw [wronskian_eval]
                    ring
          _ = 0 := by rw [hp_eval', hp_der_eval']; ring
      exact (mul_eq_zero.mp hmul).resolve_left hβ
  exact hW_ne r hW_zero

private lemma combo_eq_zero_or_realRooted_simple_of_wronskian_eval_ne_zero
    {f g : ℝ[X]}
    (hall : AllComboRealRooted f g)
    (hW_ne : ∀ x : ℝ, (wronskian f g).eval x ≠ 0) :
    ∀ α β : ℝ,
      C α * f + C β * g = 0 ∨
        (IsRealRooted (C α * f + C β * g) ∧
          HasSimpleRoots (C α * f + C β * g)) := by
  intro α β
  rcases hall α β with hzero | hrr
  · exact Or.inl hzero
  · exact Or.inr ⟨hrr, hasSimpleRoots_combo_of_wronskian_eval_ne_zero hrr hW_ne⟩

/-- If the Wronskian vanishes at `x`, then inside the same `AllComboRealRooted`
plane we can choose a special basis `(p, q)` such that:
- `p` has a multiple root at `x`,
- `q` does not vanish at `x`,
- the new pair still has no common roots.

This packages the standard "differentiate the special combination at the
Wronskian-zero point" reduction. It is the clean algebraic entry point for the
remaining converse contradiction. -/
private lemma exists_special_pair_of_wronskian_zero
    {f g : ℝ[X]}
    (hall : AllComboRealRooted f g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {x : ℝ}
    (hw : (wronskian f g).eval x = 0) :
    ∃ p q : ℝ[X],
      p = C (g.eval x) * f + C (-f.eval x) * g ∧
        ((g.eval x = 0 ∧ q = f) ∨ (g.eval x ≠ 0 ∧ q = g)) ∧
        AllComboRealRooted p q ∧
        (∀ r, p.IsRoot r → ¬ q.IsRoot r) ∧
        p.IsRoot x ∧
        p.derivative.IsRoot x ∧
        q.eval x ≠ 0 := by
  let p : ℝ[X] := C (g.eval x) * f + C (-f.eval x) * g
  have hp_root : p.IsRoot x := by
    simp [p, Polynomial.IsRoot.def]
    ring
  have hp_der_eval_eq : p.derivative.eval x = (wronskian f g).eval x := by
    simp [p, wronskian_eval]
    ring
  have hp_der_root : p.derivative.IsRoot x := by
    rw [Polynomial.IsRoot.def, hp_der_eval_eq, hw]
  by_cases hgx0 : g.eval x = 0
  · have hfx_ne : f.eval x ≠ 0 := by
      intro hfx0
      exact hno x
        (by simpa [Polynomial.IsRoot.def] using hfx0)
        (by simpa [Polynomial.IsRoot.def] using hgx0)
    refine ⟨p, f, rfl, Or.inl ⟨hgx0, rfl⟩, ?_, ?_, hp_root, hp_der_root, hfx_ne⟩
    · exact
        allComboRealRooted_linear_change
          (p := p) (q := f)
          (a := g.eval x) (b := -f.eval x) (c := 1) (d := 0)
          (by rfl) (by simp)
          hall
    · exact
        no_common_root_linear_change
          (p := p) (q := f)
          (a := g.eval x) (b := -f.eval x) (c := 1) (d := 0)
          (by rfl) (by simp)
          (by simpa [hgx0] using hfx_ne)
          hno
  · refine ⟨p, g, rfl, Or.inr ⟨hgx0, rfl⟩, ?_, ?_, hp_root, hp_der_root, hgx0⟩
    · exact
        allComboRealRooted_linear_change
          (p := p) (q := g)
          (a := g.eval x) (b := -f.eval x) (c := 0) (d := 1)
          (by rfl) (by simp)
          hall
    · exact
        no_common_root_linear_change
          (p := p) (q := g)
          (a := g.eval x) (b := -f.eval x) (c := 0) (d := 1)
          (by rfl) (by simp)
          (by simpa using hgx0)
          hno

private lemma eval_derivative_ne_zero_of_hasSimpleRoots
    {p : ℝ[X]} (hp0 : p ≠ 0) (hsimple : HasSimpleRoots p)
    {r : ℝ} (hr : p.IsRoot r) :
    p.derivative.eval r ≠ 0 := by
  intro hder0
  have hder_root : p.derivative.IsRoot r := by
    simpa [Polynomial.IsRoot.def] using hder0
  have hmult : 1 < p.rootMultiplicity r := by
    exact (one_lt_rootMultiplicity_iff_isRoot hp0).2 ⟨hr, hder_root⟩
  rw [hsimple r hr] at hmult
  omega

/-- An exact double root has nonvanishing second derivative. This is the local
algebraic fact used to turn the final converse obstruction into a quantified
second-derivative inequality, rather than another global interlacing argument. -/
private lemma eval_derivative_derivative_ne_zero_of_rootMultiplicity_eq_two
    {p : ℝ[X]} {x : ℝ}
    (hp0 : p ≠ 0)
    (hmult : p.rootMultiplicity x = 2) :
    p.derivative.derivative.eval x ≠ 0 := by
  have hp_root : p.IsRoot x := by
    exact (rootMultiplicity_pos hp0).mp (by simpa [hmult])
  have hp_deg_ge2 : 2 ≤ p.natDegree := by
    calc
      2 = p.rootMultiplicity x := by simpa [hmult]
      _ = p.roots.count x := (count_roots p).symm
      _ ≤ p.roots.card := p.roots.count_le_card x
      _ ≤ p.natDegree := card_roots' p
  have hpd_ne : p.derivative ≠ 0 := derivative_ne_zero hp_deg_ge2
  have hpd_rootmult : p.derivative.rootMultiplicity x = 1 := by
    rw [derivative_rootMultiplicity_of_root hp_root, hmult]
  intro hder2
  have hpd_root : p.derivative.IsRoot x := by
    exact (rootMultiplicity_pos hpd_ne).mp (by simpa [hpd_rootmult])
  have hpd_der_root : p.derivative.derivative.IsRoot x := by
    simpa [Polynomial.IsRoot.def] using hder2
  have hmult_gt : 1 < p.derivative.rootMultiplicity x := by
    exact (one_lt_rootMultiplicity_iff_isRoot hpd_ne).2 ⟨hpd_root, hpd_der_root⟩
  rw [hpd_rootmult] at hmult_gt
  omega

/-- Local double-root obstruction in the positive-sign case.

If every linear combination of `p` and `q` is real-rooted, `p` has an exact
double root at `x`, and the second-derivative/product sign at `x` is positive,
then a sufficiently small perturbation `p + β q` violates the standard
non-root second-derivative inequality. This is the clean local contradiction
used in the last step of the Obreschkoff converse. -/
private lemma false_of_allComboRealRooted_of_double_root_and_eval_ne_of_pos
    {p q : ℝ[X]} {x : ℝ}
    (hall : AllComboRealRooted p q)
    (hp_mult : p.rootMultiplicity x = 2)
    (hq_eval_ne : q.eval x ≠ 0)
    (hprod_pos : 0 < p.derivative.derivative.eval x * q.eval x) :
    False := by
  have hp0 : p ≠ 0 := by
    intro hp0
    simp [hp0] at hp_mult
  have hp_root : p.IsRoot x := by
    exact (rootMultiplicity_pos hp0).mp (by simpa [hp_mult])
  have hp_der_root : p.derivative.IsRoot x := by
    exact isRoot_derivative_of_rootMultiplicity_ge_two (by simpa [hp_mult])
  have hp_eval0 : p.eval x = 0 := by
    simpa [Polynomial.IsRoot.def] using hp_root
  have hp_der_eval0 : p.derivative.eval x = 0 := by
    simpa [Polynomial.IsRoot.def] using hp_der_root
  have hp_rr : IsRealRooted p := by
    rcases hall 1 0 with hzero | hrr
    · exact False.elim (hp0 (by simpa using hzero))
    · simpa using hrr
  let pp : ℝ := p.derivative.derivative.eval x
  let qx : ℝ := q.eval x
  let qp : ℝ := q.derivative.eval x
  let qq : ℝ := q.derivative.derivative.eval x
  have hpp_ne : pp ≠ 0 := by
    have hprod_ne : p.derivative.derivative.eval x * q.eval x ≠ 0 := ne_of_gt hprod_pos
    dsimp [pp]
    exact (mul_ne_zero_iff.mp hprod_ne).1
  have hqx_ne : qx ≠ 0 := by
    simpa [qx] using hq_eval_ne
  let A : ℝ := pp * qx
  let B : ℝ := qp ^ 2 - qq * qx
  let δ₁ : ℝ := A / (2 * (|B| + 1))
  let δ₂ : ℝ := |pp| / (2 * (|qq| + 1))
  let β : ℝ := min δ₁ δ₂
  have hA_pos : 0 < A := by
    simpa [A, pp, qx] using hprod_pos
  have hβ_pos : 0 < β := by
    dsimp [β, δ₁, δ₂, A, B]
    positivity
  have hβ_ne : β ≠ 0 := hβ_pos.ne'
  have hβ_le_δ₁ : β ≤ δ₁ := min_le_left _ _
  have hβ_le_δ₂ : β ≤ δ₂ := min_le_right _ _
  have hsecond_small : |β * qq| ≤ |pp| / 2 := by
    calc
      |β * qq| = β * |qq| := by
        rw [abs_mul, abs_of_nonneg (le_of_lt hβ_pos)]
      _ ≤ β * (|qq| + 1) := by nlinarith [hβ_pos, abs_nonneg qq]
      _ ≤ δ₂ * (|qq| + 1) := by
        gcongr
      _ = |pp| / 2 := by
        dsimp [δ₂]
        field_simp
  have hcombo_der2_ne :
      (p.derivative.derivative.eval x + β * q.derivative.derivative.eval x) ≠ 0 := by
    intro hsum
    have hEq : pp = -(β * qq) := by
      linarith [hsum]
    have habs_eq : |pp| = |β * qq| := by
      rw [hEq, abs_neg]
    have hpp_abs_pos : 0 < |pp| := abs_pos.mpr hpp_ne
    rw [habs_eq] at hpp_abs_pos
    linarith
  have hcombo_nonzero :
      C 1 * p + C β * q ≠ 0 := by
    intro hzero
    have heval := congrArg (fun r : ℝ[X] => r.eval x) hzero
    have heval0 : p.eval x + β * q.eval x = 0 := by
      simpa using heval
    have : β * q.eval x = 0 := by
      simpa [hp_eval0] using heval0
    exact hq_eval_ne ((mul_eq_zero.mp this).resolve_left hβ_ne)
  have hcombo_rr :
      IsRealRooted (C 1 * p + C β * q) := by
    rcases hall 1 β with hzero | hrr
    · exact False.elim (hcombo_nonzero (by simpa using hzero))
    · simpa using hrr
  have hcombo_eval_ne :
      (C 1 * p + C β * q).eval x ≠ 0 := by
    have heval :
        (C 1 * p + C β * q).eval x = β * q.eval x := by
      simp [hp_eval0]
    rw [heval]
    exact mul_ne_zero hβ_ne hq_eval_ne
  have hcombo_deg_ge2 : 2 ≤ (C 1 * p + C β * q).natDegree := by
    by_contra hlt
    have hdeg_lt2 : (C 1 * p + C β * q).natDegree < 2 := by omega
    have hder2_zero : (derivative^[2]) (C 1 * p + C β * q) = 0 :=
      iterate_derivative_eq_zero hdeg_lt2
    have hder2_eval_zero :
        (C 1 * p + C β * q).derivative.derivative.eval x = 0 := by
      simpa [Function.iterate_succ_apply'] using congrArg (fun r : ℝ[X] => r.eval x) hder2_zero
    have : p.derivative.derivative.eval x + β * q.derivative.derivative.eval x = 0 := by
      simpa using hder2_eval_zero
    exact hcombo_der2_ne this
  have hineq_raw :=
    deriv2_mul_lt_deriv_sq_at_non_root hcombo_rr (by omega) hcombo_eval_ne
  have hineq : A < β * B := by
    dsimp [A, B, pp, qx, qp, qq]
    have hineq' := hineq_raw
    simp [hp_eval0, hp_der_eval0] at hineq'
    nlinarith [hβ_pos]
  have hβB_lt : β * |B| < A := by
    calc
      β * |B| ≤ β * (|B| + 1) := by
        nlinarith [hβ_pos, abs_nonneg B]
      _ ≤ δ₁ * (|B| + 1) := by
        gcongr
      _ = A / 2 := by
        dsimp [δ₁]
        field_simp
      _ < A := by linarith
  have hineq_le : β * B ≤ β * |B| := by
    have hB_le : B ≤ |B| := le_abs_self B
    nlinarith [hβ_pos, hB_le]
  exact (lt_irrefl A) (lt_of_lt_of_le hineq (le_trans hineq_le (le_of_lt hβB_lt)))

/-- Local double-root obstruction without a sign assumption. We flip the
companion polynomial if necessary so the positive-branch lemma applies. -/
private lemma false_of_allComboRealRooted_of_double_root_and_eval_ne
    {p q : ℝ[X]} {x : ℝ}
    (hall : AllComboRealRooted p q)
    (hp_mult : p.rootMultiplicity x = 2)
    (hq_eval_ne : q.eval x ≠ 0) :
    False := by
  by_cases hprod_pos : 0 < p.derivative.derivative.eval x * q.eval x
  · exact
      false_of_allComboRealRooted_of_double_root_and_eval_ne_of_pos
        hall hp_mult hq_eval_ne hprod_pos
  · have hpp_ne :
        p.derivative.derivative.eval x ≠ 0 := by
      exact
        eval_derivative_derivative_ne_zero_of_rootMultiplicity_eq_two
          (by
            intro hp0
            simp [hp0] at hp_mult)
          hp_mult
    have hprod_ne : p.derivative.derivative.eval x * q.eval x ≠ 0 :=
      mul_ne_zero hpp_ne hq_eval_ne
    have hprod_neg : p.derivative.derivative.eval x * q.eval x < 0 := by
      exact lt_of_le_of_ne (le_of_not_gt hprod_pos) hprod_ne
    have hneg_pos : 0 < p.derivative.derivative.eval x * (-q).eval x := by
      simpa [Polynomial.eval_neg] using neg_pos.mpr hprod_neg
    have hall_neg : AllComboRealRooted p (-q) := by
      simpa using (allComboRealRooted_C_mul_right (f := p) (g := q) (c := (-1 : ℝ)) hall)
    have hq_neg_eval_ne : (-q).eval x ≠ 0 := by
      simpa [Polynomial.eval_neg] using neg_ne_zero.mpr hq_eval_ne
    exact
      false_of_allComboRealRooted_of_double_root_and_eval_ne_of_pos
        hall_neg hp_mult hq_neg_eval_ne hneg_pos

private lemma no_nontrivial_linear_relation_of_no_common_root
    {f g : ℝ[X]}
    (hf : IsRealRooted f)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hf_deg_pos : 0 < f.natDegree)
    {α β : ℝ}
    (hα : α ≠ 0) (hβ : β ≠ 0)
    (hlin : C α * f + C β * g = 0) :
    False := by
  have hEq : C α * f = C (-β) * g := by
    have htmp : C α * f = -(C β * g) := eq_neg_of_add_eq_zero_left hlin
    simpa [neg_mul, C_mul] using htmp
  have hscalar : f = C ((-β) / α) * g := by
    ext n
    have hcoeff := congrArg (fun q : ℝ[X] => q.coeff n) hEq
    simp [coeff_C_mul] at hcoeff ⊢
    apply (mul_left_cancel₀ hα)
    calc
      α * f.coeff n = (-β) * g.coeff n := by simpa using hcoeff
      _ = α * (((-β) / α) * g.coeff n) := by
            field_simp [hα]
  have hscale_ne : (-β) / α ≠ 0 := div_ne_zero (neg_ne_zero.mpr hβ) hα
  obtain ⟨r, hr⟩ :=
    exists_isRoot_of_isRealRooted_of_not_isUnit hf
      (not_isUnit_of_natDegree_pos f hf_deg_pos)
  have hgr : g.IsRoot r := by
    have hfr_eval : f.eval r = 0 := by
      simpa [Polynomial.IsRoot.def] using hr
    have hgr_eval : g.eval r = 0 := by
      rw [hscalar, eval_mul, eval_C] at hfr_eval
      exact (mul_eq_zero.mp hfr_eval).resolve_left hscale_ne
    simpa [Polynomial.IsRoot.def] using hgr_eval
  exact hno r hr hgr

private lemma no_common_root_iterateTDeriv_of_allComboRealRooted
    {f g : ℝ[X]}
    (hf : IsRealRooted f) (hg : IsRealRooted g)
    (hall : AllComboRealRooted f g)
    (hdeg : f.natDegree + 1 = g.natDegree ∨ f.natDegree = g.natDegree)
    {eps : ℝ} (heps : 0 < eps)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    let n := max f.natDegree g.natDegree
    ∀ r, (iterateTDeriv eps n f).IsRoot r → ¬ (iterateTDeriv eps n g).IsRoot r := by
  dsimp
  intro r hfr hgr
  obtain ⟨_, hf', hg', hf_simple, hg_simple, _⟩ :=
    simple_pair_of_allComboRealRooted_iterateTDeriv hf hg hall hdeg heps
  have hcombo :=
    allComboRealRooted_eq_zero_or_isRealRooted_and_hasSimpleRoots_iterateTDeriv
      hall heps
  let α : ℝ := (iterateTDeriv eps (max f.natDegree g.natDegree) g).derivative.eval r
  let β : ℝ := -((iterateTDeriv eps (max f.natDegree g.natDegree) f).derivative.eval r)
  have hα_ne : α ≠ 0 :=
    eval_derivative_ne_zero_of_hasSimpleRoots hg'.1 hg_simple hgr
  have hβ_ne : β ≠ 0 := by
    exact neg_ne_zero.mpr <|
      eval_derivative_ne_zero_of_hasSimpleRoots hf'.1 hf_simple hfr
  have hp_root :
      (C α * iterateTDeriv eps (max f.natDegree g.natDegree) f +
        C β * iterateTDeriv eps (max f.natDegree g.natDegree) g).IsRoot r := by
    rw [Polynomial.IsRoot.def] at hfr hgr ⊢
    dsimp [α, β]
    simp [hfr, hgr]
  have hp_der_root :
      (C α * iterateTDeriv eps (max f.natDegree g.natDegree) f +
        C β * iterateTDeriv eps (max f.natDegree g.natDegree) g).derivative.IsRoot r := by
    simp [Polynomial.IsRoot.def, α, β]
    ring
  rcases hcombo α β with hp0 | ⟨hp_rr, hp_simple⟩
  · have hlin :
        C α * f + C β * g = 0 := by
        have hiter_eq :
            iterateTDeriv eps (max f.natDegree g.natDegree) (C α * f + C β * g) =
              iterateTDeriv eps (max f.natDegree g.natDegree) 0 := by
          simpa [iterateTDeriv_linear_combo, iterateTDeriv_zero_poly] using hp0
        exact (iterateTDeriv_injective eps (max f.natDegree g.natDegree)) (by simpa using hiter_eq)
    have hdeg_iter_pos : 0 < (iterateTDeriv eps (max f.natDegree g.natDegree) f).natDegree := by
      have hr_mem :
          r ∈ (iterateTDeriv eps (max f.natDegree g.natDegree) f).roots :=
        (mem_roots hf'.1).2 hfr
      have hcard :
          0 < (iterateTDeriv eps (max f.natDegree g.natDegree) f).roots.card :=
        Multiset.card_pos_iff_exists_mem.mpr ⟨r, hr_mem⟩
      simpa [hf'.2] using hcard
    have hf_deg_pos : 0 < f.natDegree := by
      simpa [natDegree_iterateTDeriv_of_isRealRooted
        (eps := eps) (n := max f.natDegree g.natDegree) hf] using hdeg_iter_pos
    exact no_nontrivial_linear_relation_of_no_common_root
      hf hno hf_deg_pos hα_ne hβ_ne hlin
  · have hp_ne :
        C α * iterateTDeriv eps (max f.natDegree g.natDegree) f +
          C β * iterateTDeriv eps (max f.natDegree g.natDegree) g ≠ 0 :=
      hp_rr.1
    have hmult :
        1 <
          (C α * iterateTDeriv eps (max f.natDegree g.natDegree) f +
            C β * iterateTDeriv eps (max f.natDegree g.natDegree) g).rootMultiplicity r := by
      exact (one_lt_rootMultiplicity_iff_isRoot hp_ne).2 ⟨hp_root, hp_der_root⟩
    rw [hp_simple r hp_root] at hmult
    omega

private lemma derivative_sign_at_consecutive_simple_roots
    {f : ℝ[X]} (hf : IsRealRooted f) (hsimple : HasSimpleRoots f)
    {r₁ r₂ : ℝ} (hr₁ : f.IsRoot r₁) (hr₂ : f.IsRoot r₂)
    (hlt : r₁ < r₂)
    (hno_between : ∀ r ∈ f.roots, ¬ (r₁ < r ∧ r < r₂)) :
    f.derivative.eval r₁ * f.derivative.eval r₂ < 0 := by
  have hnonpos :=
    derivative_sign_at_consecutive_roots hr₁ hr₂ hlt hno_between hf.1
  have hder₁_ne : f.derivative.eval r₁ ≠ 0 :=
    eval_derivative_ne_zero_of_hasSimpleRoots hf.1 hsimple hr₁
  have hder₂_ne : f.derivative.eval r₂ ≠ 0 :=
    eval_derivative_ne_zero_of_hasSimpleRoots hf.1 hsimple hr₂
  exact lt_of_le_of_ne hnonpos (mul_ne_zero hder₁_ne hder₂_ne)

private lemma wronskian_eval_mul_pos_of_le_of_eq_zero_or_simple_combo
    {f g : ℝ[X]}
    (hf : IsRealRooted f) (hg : IsRealRooted g)
    (hcombo :
      ∀ α β : ℝ,
        C α * f + C β * g = 0 ∨
          (IsRealRooted (C α * f + C β * g) ∧
            HasSimpleRoots (C α * f + C β * g)))
    (hdeg_pos : 0 < max f.natDegree g.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    {x y : ℝ} (hxy : x ≤ y) :
    0 < (wronskian f g).eval x * (wronskian f g).eval y := by
  by_contra hnonpos
  obtain ⟨z, _, _, hz_root⟩ :=
    exists_isRoot_between_of_eval_mul_nonpos hxy (not_lt.mp hnonpos)
  have hz_eval0 : (wronskian f g).eval z = 0 := by
    simpa [Polynomial.IsRoot.def] using hz_root
  exact
    (wronskian_eval_ne_zero_of_eq_zero_or_simple_combo
      hf hg hcombo hdeg_pos hno (x := z)) hz_eval0

private lemma hasPosLeadingCoeff_derivative_of_pos
    {f : ℝ[X]} (hf_pos : HasPosLeadingCoeff f) (hdeg : 1 ≤ f.natDegree) :
    HasPosLeadingCoeff f.derivative := by
  unfold HasPosLeadingCoeff at hf_pos ⊢
  rw [leadingCoeff, natDegree_derivative_eq hdeg, coeff_derivative]
  rw [Nat.sub_add_cancel hdeg, coeff_natDegree] at *
  have hdeg_pos : 0 < (f.natDegree : ℝ) := by
    exact_mod_cast hdeg
  nlinarith

private lemma hasSimpleRoots_of_eq_zero_or_isRealRooted_and_hasSimpleRoots_left
    {f g : ℝ[X]}
    (hf : IsRealRooted f)
    (hcombo :
      ∀ α β : ℝ,
        C α * f + C β * g = 0 ∨
          (IsRealRooted (C α * f + C β * g) ∧
            HasSimpleRoots (C α * f + C β * g))) :
    HasSimpleRoots f := by
  rcases hcombo 1 0 with hzero | ⟨_, hsimple⟩
  · have : f = 0 := by simpa using hzero
    exact (hf.1 this).elim
  · simpa using hsimple

private lemma hasSimpleRoots_of_eq_zero_or_isRealRooted_and_hasSimpleRoots_right
    {f g : ℝ[X]}
    (hg : IsRealRooted g)
    (hcombo :
      ∀ α β : ℝ,
        C α * f + C β * g = 0 ∨
          (IsRealRooted (C α * f + C β * g) ∧
            HasSimpleRoots (C α * f + C β * g))) :
    HasSimpleRoots g := by
  rcases hcombo 0 1 with hzero | ⟨_, hsimple⟩
  · have : g = 0 := by simpa [add_comm] using hzero
    exact (hg.1 this).elim
  · simpa [add_comm] using hsimple

private theorem prec_or_revPrec_of_eq_zero_or_simple_combo_sameDegree
    {f g : ℝ[X]}
    (hf : IsRealRooted f) (hg : IsRealRooted g)
    (hcombo :
      ∀ α β : ℝ,
        C α * f + C β * g = 0 ∨
          (IsRealRooted (C α * f + C β * g) ∧
            HasSimpleRoots (C α * f + C β * g)))
    (hdeg : g.natDegree = f.natDegree)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f g ∨ Prec g f := by
  have hf_simple :
      HasSimpleRoots f :=
    hasSimpleRoots_of_eq_zero_or_isRealRooted_and_hasSimpleRoots_left hf hcombo
  have hg_simple :
      HasSimpleRoots g :=
    hasSimpleRoots_of_eq_zero_or_isRealRooted_and_hasSimpleRoots_right hg hcombo
  by_cases hdeg0 : f.natDegree = 0
  · have hgdeg0 : g.natDegree = 0 := by simpa [hdeg] using hdeg0
    have hroots_f : f.roots = 0 := by
      apply Multiset.card_eq_zero.mp
      rw [hf.2, hdeg0]
    have hroots_g : g.roots = 0 := by
      apply Multiset.card_eq_zero.mp
      rw [hg.2, hgdeg0]
    left
    refine ⟨hf, hg, [], [], by simp, by simp, ?_, ?_, ?_⟩
    · simpa [hroots_f]
    · simpa [hroots_g]
    · exact Or.inr ⟨by simp, by simp [ListAlternates]⟩
  by_cases hdeg1 : f.natDegree = 1
  · exact PosComboRealRooted.prec_or_revPrec_of_same_degree_one hdeg hdeg1
  have hdeg_ge2 : 2 ≤ f.natDegree := by omega
  have hgdeg_ge2 : 2 ≤ g.natDegree := by rw [hdeg]; exact hdeg_ge2
  have hW_ne : ∀ x : ℝ, (wronskian f g).eval x ≠ 0 := by
    intro x
    have hdeg_pos : 0 < max f.natDegree g.natDegree := by
      rw [hdeg]
      omega
    exact
      wronskian_eval_ne_zero_of_eq_zero_or_simple_combo
        hf hg hcombo hdeg_pos hno (x := x)
  have hW_prod :
      ∀ {x y : ℝ}, x ≤ y → 0 < (wronskian f g).eval x * (wronskian f g).eval y := by
    intro x y hxy
    have hdeg_pos : 0 < max f.natDegree g.natDegree := by
      rw [hdeg]
      omega
    exact
      wronskian_eval_mul_pos_of_le_of_eq_zero_or_simple_combo
        hf hg hcombo hdeg_pos hno hxy
  have hf'_pos :
      HasPosLeadingCoeff f.derivative :=
    hasPosLeadingCoeff_derivative_of_pos hf_pos (by omega)
  have hg'_pos :
      HasPosLeadingCoeff g.derivative :=
    hasPosLeadingCoeff_derivative_of_pos hg_pos (by omega)
  by_cases hWneg0 : (wronskian f g).eval 0 < 0
  · have hWneg : ∀ x : ℝ, (wronskian f g).eval x < 0 := by
      intro x
      by_cases hx : x ≤ 0
      · have hprod := hW_prod hx
        nlinarith
      · have hx' : 0 ≤ x := le_of_not_ge hx
        have hprod := hW_prod hx'
        nlinarith
    have hder : Interlaces f.derivative f := derivative_interlaces hf hdeg_ge2
    have hroot_sign :
        ∀ r, f.IsRoot r → g.eval r * f.derivative.eval r < 0 := by
      intro r hr
      have hf_eval : f.eval r = 0 := by
        simpa [Polynomial.IsRoot.def] using hr
      simpa [wronskian_eval, hf_eval] using hWneg r
    left
    exact prec_of_interlaces_eval_mul_neg_same hder hf'_pos hg_pos hdeg hroot_sign
  · have hWpos0 : 0 < (wronskian f g).eval 0 := by
      have hW0_nonneg : 0 ≤ (wronskian f g).eval 0 := le_of_not_gt hWneg0
      exact lt_of_le_of_ne hW0_nonneg (Ne.symm (hW_ne 0))
    have hWpos : ∀ x : ℝ, 0 < (wronskian f g).eval x := by
      intro x
      by_cases hx : x ≤ 0
      · have hprod := hW_prod hx
        nlinarith
      · have hx' : 0 ≤ x := le_of_not_ge hx
        have hprod := hW_prod hx'
        nlinarith
    have hder : Interlaces g.derivative g := derivative_interlaces hg hgdeg_ge2
    have hroot_sign :
        ∀ r, g.IsRoot r → f.eval r * g.derivative.eval r < 0 := by
      intro r hr
      have hg_eval : g.eval r = 0 := by
        simpa [Polynomial.IsRoot.def] using hr
      have hw : 0 < -(f.eval r * g.derivative.eval r) := by
        simpa [wronskian_eval, hg_eval] using hWpos r
      nlinarith
    right
    exact prec_of_interlaces_eval_mul_neg_same hder hg'_pos hf_pos hdeg.symm hroot_sign

private lemma prec_degree_zero_right_of_degree_one
    {f g : ℝ[X]}
    (hf : IsRealRooted f) (hg : IsRealRooted g)
    (hf_deg0 : f.natDegree = 0) (hg_deg1 : g.natDegree = 1) :
    Prec f g := by
  obtain ⟨r, hr_eq⟩ : ∃ r, g.roots = {r} := by
    apply Multiset.card_eq_one.mp
    simpa [hg_deg1] using hg.2
  have hroots_f : f.roots = 0 := by
    apply Multiset.card_eq_zero.mp
    rw [hf.2, hf_deg0]
  refine ⟨hf, hg, [], [r], by simp, List.pairwise_singleton _ _, ?_, ?_, ?_⟩
  · simpa [hroots_f]
  · simpa [hr_eq]
  · exact Or.inl ⟨by simp, by simp [ListInterlaces]⟩

private lemma interlaces_derivative_of_degree_pos
    {f : ℝ[X]}
    (hf : IsRealRooted f) (hf_pos : HasPosLeadingCoeff f)
    (hdeg : 1 ≤ f.natDegree) :
    Interlaces f.derivative f := by
  by_cases hdeg1 : f.natDegree = 1
  · have hf'_pos : HasPosLeadingCoeff f.derivative :=
      hasPosLeadingCoeff_derivative_of_pos hf_pos hdeg
    have hf'_ne : f.derivative ≠ 0 := by
      intro h0
      simpa [HasPosLeadingCoeff, h0] using hf'_pos
    have hf'_deg0 : f.derivative.natDegree = 0 := by
      simpa [hdeg1] using natDegree_derivative_eq hdeg
    have hf'_rr : IsRealRooted f.derivative :=
      isRealRooted_of_deg_zero hf'_ne hf'_deg0
    exact
      (prec_degree_zero_right_of_degree_one hf'_rr hf hf'_deg0 hdeg1).toInterlaces
        (by rw [hf'_deg0, hdeg1])
  · have hdeg_ge2 : 2 ≤ f.natDegree := by omega
    exact derivative_interlaces hf hdeg_ge2

private lemma wronskian_coeff_top_succ
    {f g : ℝ[X]}
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_deg_pos : 1 ≤ f.natDegree) :
    (wronskian f g).coeff (2 * f.natDegree) = -(f.leadingCoeff * g.leadingCoeff) := by
  have hf'_deg : f.derivative.natDegree = f.natDegree - 1 :=
    natDegree_derivative_eq hf_deg_pos
  have hg'_deg : g.derivative.natDegree = g.natDegree - 1 :=
    natDegree_derivative_eq (by omega)
  have hf'_lc : f.derivative.leadingCoeff = (f.natDegree : ℝ) * f.leadingCoeff := by
    unfold Polynomial.leadingCoeff
    rw [hf'_deg, coeff_derivative, Nat.sub_add_cancel hf_deg_pos, coeff_natDegree]
    have hnat : (↑(f.natDegree - 1) : ℝ) + 1 = f.natDegree := by
      simpa [add_comm] using
        (show (((f.natDegree - 1 : ℕ) : ℝ) + 1 = f.natDegree) by
          exact_mod_cast Nat.sub_add_cancel hf_deg_pos)
    calc
      f.leadingCoeff * (↑(f.natDegree - 1) + 1)
          = f.leadingCoeff * f.natDegree := by rw [hnat]
      _ = (f.natDegree : ℝ) * f.leadingCoeff := by ring
  have hg'_lc : g.derivative.leadingCoeff = (g.natDegree : ℝ) * g.leadingCoeff := by
    unfold Polynomial.leadingCoeff
    rw [hg'_deg, coeff_derivative, Nat.sub_add_cancel (by omega), coeff_natDegree]
    have hnat : (↑(g.natDegree - 1) : ℝ) + 1 = g.natDegree := by
      simpa [add_comm] using
        (show (((g.natDegree - 1 : ℕ) : ℝ) + 1 = g.natDegree) by
          exact_mod_cast Nat.sub_add_cancel (show 1 ≤ g.natDegree by omega))
    calc
      g.leadingCoeff * (↑(g.natDegree - 1) + 1)
          = g.leadingCoeff * g.natDegree := by rw [hnat]
      _ = (g.natDegree : ℝ) * g.leadingCoeff := by ring
  have hcoeff_gf' :
      (g * f.derivative).coeff (2 * f.natDegree) = g.leadingCoeff * f.derivative.leadingCoeff := by
    have htop : g.natDegree + f.derivative.natDegree = 2 * f.natDegree := by
      rw [hf'_deg, hdeg]
      omega
    simpa [htop] using coeff_mul_degree_add_degree g f.derivative
  have hcoeff_fg' :
      (f * g.derivative).coeff (2 * f.natDegree) = f.leadingCoeff * g.derivative.leadingCoeff := by
    have htop : f.natDegree + g.derivative.natDegree = 2 * f.natDegree := by
      rw [hg'_deg, hdeg]
      omega
    simpa [htop] using coeff_mul_degree_add_degree f g.derivative
  have hdegR : (g.natDegree : ℝ) = f.natDegree + 1 := by
    exact_mod_cast hdeg
  unfold wronskian
  rw [coeff_sub, hcoeff_gf', hcoeff_fg', hf'_lc, hg'_lc, hdegR]
  ring_nf

private lemma wronskian_natDegree_succ
    {f g : ℝ[X]}
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hf_deg_pos : 1 ≤ f.natDegree) :
    (wronskian f g).natDegree = 2 * f.natDegree := by
  have hcoeff_top := wronskian_coeff_top_succ (f := f) (g := g) hdeg hf_deg_pos
  have hcoeff_top_ne : (wronskian f g).coeff (2 * f.natDegree) ≠ 0 := by
    rw [hcoeff_top, neg_ne_zero]
    exact mul_ne_zero (ne_of_gt hf_pos) (ne_of_gt hg_pos)
  have hgf'_le : (g * f.derivative).natDegree ≤ 2 * f.natDegree := by
    calc
      (g * f.derivative).natDegree ≤ g.natDegree + f.derivative.natDegree := natDegree_mul_le
      _ = 2 * f.natDegree := by
        rw [natDegree_derivative_eq hf_deg_pos, hdeg]
        omega
  have hfg'_le : (f * g.derivative).natDegree ≤ 2 * f.natDegree := by
    calc
      (f * g.derivative).natDegree ≤ f.natDegree + g.derivative.natDegree := natDegree_mul_le
      _ = 2 * f.natDegree := by
        rw [natDegree_derivative_eq (by omega), hdeg]
        omega
  have hW_le : (wronskian f g).natDegree ≤ 2 * f.natDegree := by
    unfold wronskian
    calc
      (g * f.derivative - f * g.derivative).natDegree
          ≤ max (g * f.derivative).natDegree (f * g.derivative).natDegree := natDegree_sub_le _ _
      _ ≤ 2 * f.natDegree := max_le hgf'_le hfg'_le
  exact natDegree_eq_of_le_of_coeff_ne_zero hW_le hcoeff_top_ne

private lemma leadingCoeff_wronskian_succ
    {f g : ℝ[X]}
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hf_deg_pos : 1 ≤ f.natDegree) :
    (wronskian f g).leadingCoeff = -(f.leadingCoeff * g.leadingCoeff) := by
  unfold Polynomial.leadingCoeff
  rw [wronskian_natDegree_succ hdeg hf_pos hg_pos hf_deg_pos,
    wronskian_coeff_top_succ hdeg hf_deg_pos]
  rw [coeff_natDegree, coeff_natDegree]

private theorem prec_of_eq_zero_or_simple_combo_succDegree
    {f g : ℝ[X]}
    (hf : IsRealRooted f) (hg : IsRealRooted g)
    (hcombo :
      ∀ α β : ℝ,
        C α * f + C β * g = 0 ∨
          (IsRealRooted (C α * f + C β * g) ∧
            HasSimpleRoots (C α * f + C β * g)))
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f g := by
  by_cases hdeg0 : f.natDegree = 0
  · have hgdeg1 : g.natDegree = 1 := by simpa [hdeg0] using hdeg
    exact prec_degree_zero_right_of_degree_one hf hg hdeg0 hgdeg1
  have hf_deg_pos : 1 ≤ f.natDegree := by omega
  have hW_ne : ∀ x : ℝ, (wronskian f g).eval x ≠ 0 := by
    intro x
    have hdeg_pos : 0 < max f.natDegree g.natDegree := by
      rw [hdeg]
      omega
    exact
      wronskian_eval_ne_zero_of_eq_zero_or_simple_combo
        hf hg hcombo hdeg_pos hno (x := x)
  have hW_prod :
      ∀ {x y : ℝ}, x ≤ y → 0 < (wronskian f g).eval x * (wronskian f g).eval y := by
    intro x y hxy
    have hdeg_pos : 0 < max f.natDegree g.natDegree := by
      rw [hdeg]
      omega
    exact
      wronskian_eval_mul_pos_of_le_of_eq_zero_or_simple_combo
        hf hg hcombo hdeg_pos hno hxy
  have hq_pos : HasPosLeadingCoeff (-wronskian f g) := by
    unfold HasPosLeadingCoeff
    rw [leadingCoeff_neg, leadingCoeff_wronskian_succ hdeg hf_pos hg_pos hf_deg_pos]
    simpa using mul_pos hf_pos hg_pos
  have hq_deg_pos : 0 < (-wronskian f g).degree := by
    have hnat : 0 < (-wronskian f g).natDegree := by
      rw [natDegree_neg, wronskian_natDegree_succ hdeg hf_pos hg_pos hf_deg_pos]
      omega
    exact natDegree_pos_iff_degree_pos.mp hnat
  have hq_even : Even (-wronskian f g).natDegree := by
    rw [natDegree_neg, wronskian_natDegree_succ hdeg hf_pos hg_pos hf_deg_pos]
    exact even_two_mul _
  have ht : Filter.Tendsto (fun x => (-wronskian f g).eval x) Filter.atBot Filter.atTop :=
    tendsto_eval_atBot_atTop_of_posLeadingCoeff_even hq_pos hq_deg_pos hq_even
  have hq_event : ∀ᶠ x : ℝ in Filter.atBot, 0 < (-wronskian f g).eval x := by
    exact ht.eventually (Filter.Ioi_mem_atTop 0)
  obtain ⟨x₀, hx₀⟩ := hq_event.exists
  have hWneg₀ : (wronskian f g).eval x₀ < 0 := by
    simpa using hx₀
  have hWneg : ∀ x : ℝ, (wronskian f g).eval x < 0 := by
    intro x
    by_cases hxx₀ : x ≤ x₀
    · have hprod := hW_prod hxx₀
      nlinarith
    · have hx₀x : x₀ ≤ x := le_of_not_ge hxx₀
      have hprod := hW_prod hx₀x
      nlinarith
  have hf'_pos : HasPosLeadingCoeff f.derivative :=
    hasPosLeadingCoeff_derivative_of_pos hf_pos hf_deg_pos
  have hder : Interlaces f.derivative f :=
    interlaces_derivative_of_degree_pos hf hf_pos hf_deg_pos
  have hroot_sign :
      ∀ r, f.IsRoot r → g.eval r * f.derivative.eval r < 0 := by
    intro r hr
    have hf_eval : f.eval r = 0 := by
      simpa [Polynomial.IsRoot.def] using hr
    simpa [wronskian_eval, hf_eval] using hWneg r
  exact prec_of_interlaces_eval_mul_neg_succ hder hf'_pos hg_pos hdeg hroot_sign

/-- Handoff helper for the Obreschkoff converse.

Once we know that every nonzero linear combination of `f` and `g` is
real-rooted with simple roots, the remaining proof is only bookkeeping:

1. normalize leading-coefficient signs so that the Wronskian lemmas can use the
   existing positive-leading-coefficient API;
2. dispatch to the same-degree / succ-degree simple-pair theorem above; and
3. scale back to the original pair.

This isolates the still-missing bridge in `prec_of_allComboRealRooted`:
producing the `hcombo` hypothesis for the *original* pair from
`AllComboRealRooted` plus the no-common-roots assumption. -/
private theorem prec_of_eq_zero_or_simple_combo_of_no_common
    {f g : ℝ[X]}
    (hf : IsRealRooted f) (hg : IsRealRooted g)
    (hcombo :
      ∀ α β : ℝ,
        C α * f + C β * g = 0 ∨
          (IsRealRooted (C α * f + C β * g) ∧
            HasSimpleRoots (C α * f + C β * g)))
    (hdeg : f.natDegree + 1 = g.natDegree ∨ f.natDegree = g.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f g ∨ Prec g f := by
  have hf_lc_ne : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf.1
  have hg_lc_ne : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hg.1
  let sf : ℝ := if 0 < f.leadingCoeff then 1 else -1
  let sg : ℝ := if 0 < g.leadingCoeff then 1 else -1
  have hsf_ne : sf ≠ 0 := by
    dsimp [sf]
    split_ifs <;> norm_num
  have hsg_ne : sg ≠ 0 := by
    dsimp [sg]
    split_ifs <;> norm_num
  have hsf_pos : 0 < sf * f.leadingCoeff := by
    dsimp [sf]
    split_ifs with hpos
    · nlinarith
    · have hneg : f.leadingCoeff < 0 := by
        exact lt_of_le_of_ne (le_of_not_gt hpos) hf_lc_ne
      nlinarith
  have hsg_pos : 0 < sg * g.leadingCoeff := by
    dsimp [sg]
    split_ifs with hpos
    · nlinarith
    · have hneg : g.leadingCoeff < 0 := by
        exact lt_of_le_of_ne (le_of_not_gt hpos) hg_lc_ne
      nlinarith
  let f₀ : ℝ[X] := C sf * f
  let g₀ : ℝ[X] := C sg * g
  have hf₀ : IsRealRooted f₀ := isRealRooted_C_mul hf hsf_ne
  have hg₀ : IsRealRooted g₀ := isRealRooted_C_mul hg hsg_ne
  have hf₀_pos : HasPosLeadingCoeff f₀ := by
    unfold HasPosLeadingCoeff f₀
    rw [leadingCoeff_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr hsf_ne) f]
    simpa [sf] using hsf_pos
  have hg₀_pos : HasPosLeadingCoeff g₀ := by
    unfold HasPosLeadingCoeff g₀
    rw [leadingCoeff_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr hsg_ne) g]
    simpa [sg] using hsg_pos
  have hcombo₀ :
      ∀ α β : ℝ,
        C α * f₀ + C β * g₀ = 0 ∨
          (IsRealRooted (C α * f₀ + C β * g₀) ∧
            HasSimpleRoots (C α * f₀ + C β * g₀)) := by
    intro α β
    simpa [f₀, g₀, C_mul, mul_assoc, mul_left_comm, mul_comm] using
      hcombo (α * sf) (β * sg)
  have hdeg₀ :
      f₀.natDegree + 1 = g₀.natDegree ∨ f₀.natDegree = g₀.natDegree := by
    simpa [f₀, g₀, natDegree_C_mul hsf_ne, natDegree_C_mul hsg_ne] using hdeg
  have hno₀ : ∀ r, f₀.IsRoot r → ¬ g₀.IsRoot r := by
    intro r hrf₀ hrg₀
    have hrf : f.IsRoot r := by
      have hrf₀_eval : (C sf * f).eval r = 0 := by
        simpa [f₀, Polynomial.IsRoot.def] using hrf₀
      rw [eval_mul, eval_C] at hrf₀_eval
      have : f.eval r = 0 := (mul_eq_zero.mp hrf₀_eval).resolve_left hsf_ne
      simpa [Polynomial.IsRoot.def] using this
    have hrg : g.IsRoot r := by
      have hrg₀_eval : (C sg * g).eval r = 0 := by
        simpa [g₀, Polynomial.IsRoot.def] using hrg₀
      rw [eval_mul, eval_C] at hrg₀_eval
      have : g.eval r = 0 := (mul_eq_zero.mp hrg₀_eval).resolve_left hsg_ne
      simpa [Polynomial.IsRoot.def] using this
    exact hno r hrf hrg
  have hprec₀ : Prec f₀ g₀ ∨ Prec g₀ f₀ := by
    rcases hdeg₀ with hsucc | hsame
    · left
      exact
        prec_of_eq_zero_or_simple_combo_succDegree
          hf₀ hg₀ hcombo₀ hsucc.symm hf₀_pos hg₀_pos hno₀
    · exact
        prec_or_revPrec_of_eq_zero_or_simple_combo_sameDegree
          hf₀ hg₀ hcombo₀ hsame.symm hf₀_pos hg₀_pos hno₀
  have hsf_inv_ne : sf⁻¹ ≠ 0 := inv_ne_zero hsf_ne
  have hsg_inv_ne : sg⁻¹ ≠ 0 := inv_ne_zero hsg_ne
  have hf_scale : C sf⁻¹ * f₀ = f := by
    calc
      C sf⁻¹ * f₀ = (C sf⁻¹ * C sf) * f := by simp [f₀, mul_assoc]
      _ = C (sf⁻¹ * sf) * f := by rw [C_mul]
      _ = C 1 * f := by
            congr 1
            field_simp [hsf_ne]
      _ = f := by simp
  have hg_scale : C sg⁻¹ * g₀ = g := by
    calc
      C sg⁻¹ * g₀ = (C sg⁻¹ * C sg) * g := by simp [g₀, mul_assoc]
      _ = C (sg⁻¹ * sg) * g := by rw [C_mul]
      _ = C 1 * g := by
            congr 1
            field_simp [hsg_ne]
      _ = g := by simp
  rcases hprec₀ with hfg₀ | hgf₀
  · left
    have hscaled : Prec (C sf⁻¹ * f₀) (C sg⁻¹ * g₀) :=
      prec_C_mul_right (prec_C_mul_left hfg₀ hsf_inv_ne) hsg_inv_ne
    simpa [hf_scale, hg_scale] using hscaled
  · right
    have hscaled : Prec (C sg⁻¹ * g₀) (C sf⁻¹ * f₀) :=
      prec_C_mul_right (prec_C_mul_left hgf₀ hsg_inv_ne) hsf_inv_ne
    simpa [hf_scale, hg_scale] using hscaled

/-- Regularized no-common-root converse step for the `iterateTDeriv` pair.

This packages the exact simple-pair/Wronskian endgame that the main converse
uses after regularization, leaving the remaining `ε → 0` transport as the only
unfinished step. -/
private theorem prec_or_revPrec_iterateTDeriv_of_allComboRealRooted_of_no_common
    {f g : ℝ[X]}
    (hf : IsRealRooted f) (hg : IsRealRooted g)
    (hall : AllComboRealRooted f g)
    (hdeg : f.natDegree + 1 = g.natDegree ∨ f.natDegree = g.natDegree)
    {eps : ℝ} (heps : 0 < eps)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    let n := max f.natDegree g.natDegree
    Prec (iterateTDeriv eps n f) (iterateTDeriv eps n g) ∨
      Prec (iterateTDeriv eps n g) (iterateTDeriv eps n f) := by
  dsimp
  have hsimple_data :
      AllComboRealRooted (iterateTDeriv eps (max f.natDegree g.natDegree) f)
          (iterateTDeriv eps (max f.natDegree g.natDegree) g) ∧
        IsRealRooted (iterateTDeriv eps (max f.natDegree g.natDegree) f) ∧
        IsRealRooted (iterateTDeriv eps (max f.natDegree g.natDegree) g) ∧
        HasSimpleRoots (iterateTDeriv eps (max f.natDegree g.natDegree) f) ∧
        HasSimpleRoots (iterateTDeriv eps (max f.natDegree g.natDegree) g) ∧
        ((iterateTDeriv eps (max f.natDegree g.natDegree) f).natDegree + 1 =
            (iterateTDeriv eps (max f.natDegree g.natDegree) g).natDegree ∨
          (iterateTDeriv eps (max f.natDegree g.natDegree) f).natDegree =
            (iterateTDeriv eps (max f.natDegree g.natDegree) g).natDegree) := by
    simpa using
      simple_pair_of_allComboRealRooted_iterateTDeriv hf hg hall hdeg heps
  have hcombo_simple :
      ∀ α β : ℝ,
        C α * iterateTDeriv eps (max f.natDegree g.natDegree) f +
            C β * iterateTDeriv eps (max f.natDegree g.natDegree) g = 0 ∨
          (IsRealRooted
              (C α * iterateTDeriv eps (max f.natDegree g.natDegree) f +
                C β * iterateTDeriv eps (max f.natDegree g.natDegree) g) ∧
            HasSimpleRoots
              (C α * iterateTDeriv eps (max f.natDegree g.natDegree) f +
                C β * iterateTDeriv eps (max f.natDegree g.natDegree) g)) := by
    simpa using
      allComboRealRooted_eq_zero_or_isRealRooted_and_hasSimpleRoots_iterateTDeriv
        hall heps
  have hno_simple :
      ∀ r,
        (iterateTDeriv eps (max f.natDegree g.natDegree) f).IsRoot r →
          ¬ (iterateTDeriv eps (max f.natDegree g.natDegree) g).IsRoot r := by
    simpa using
      no_common_root_iterateTDeriv_of_allComboRealRooted
        hf hg hall hdeg heps hno
  rcases hsimple_data with ⟨_, hf_iter, hg_iter, _, _, hdeg_iter⟩
  exact
    prec_of_eq_zero_or_simple_combo_of_no_common
      hf_iter hg_iter hcombo_simple hdeg_iter hno_simple

/-- In the succ-degree branch, the regularized pair has forced orientation by
degree, so the converse endgame returns the left orientation outright. -/
private theorem prec_iterateTDeriv_of_allComboRealRooted_succ_of_no_common
    {f g : ℝ[X]}
    (hf : IsRealRooted f) (hg : IsRealRooted g)
    (hall : AllComboRealRooted f g)
    (hsucc : f.natDegree + 1 = g.natDegree)
    {eps : ℝ} (heps : 0 < eps)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    let n := max f.natDegree g.natDegree
    Prec (iterateTDeriv eps n f) (iterateTDeriv eps n g) := by
  have hprec_iter :
      Prec (iterateTDeriv eps (max f.natDegree g.natDegree) f)
          (iterateTDeriv eps (max f.natDegree g.natDegree) g) ∨
        Prec (iterateTDeriv eps (max f.natDegree g.natDegree) g)
          (iterateTDeriv eps (max f.natDegree g.natDegree) f) :=
    prec_or_revPrec_iterateTDeriv_of_allComboRealRooted_of_no_common
      hf hg hall (Or.inl hsucc) heps hno
  have hdeg_iter_succ :
      (iterateTDeriv eps (max f.natDegree g.natDegree) f).natDegree + 1 =
        (iterateTDeriv eps (max f.natDegree g.natDegree) g).natDegree := by
    simpa [natDegree_iterateTDeriv_of_isRealRooted
        (eps := eps) (n := max f.natDegree g.natDegree) hf,
      natDegree_iterateTDeriv_of_isRealRooted
        (eps := eps) (n := max f.natDegree g.natDegree) hg] using hsucc
  dsimp
  rcases hprec_iter with hfg | hgf
  · exact hfg
  · have hbounds := natDegree_bounds_of_prec_local hgf
    omega

/-- Every element of the left-hand list is bounded by the rightmost element of
the right-hand list in a nonempty `ListInterlaces` layout.

This tiny list lemma is the bookkeeping bridge behind the degree-gap reduction
below: once we know a point is a root of `p'`, interlacing lets us push it to a
root of `p` on its right. -/
private lemma listInterlaces_all_le_getLast_local :
    ∀ {ss rs : List ℝ},
      (hrs_ne : rs ≠ []) →
      rs.Pairwise (· ≤ ·) →
      ListInterlaces ss rs →
      ∀ s ∈ ss, s ≤ rs.getLast hrs_ne
  | [], [], hrs_ne, _, hint, s, hs => by
      cases (hrs_ne rfl)
  | [], [_], _, _, hint, s, hs => by
      simpa using hs
  | s :: ss, [r], _, _, hint, _, _ => by
      simp [ListInterlaces] at hint
  | s :: ss, r₁ :: r₂ :: rs, _, hrs_sorted, hint, t, ht => by
      obtain ⟨_, hs_r₂, htail⟩ := hint
      rcases List.mem_cons.mp ht with rfl | ht
      · exact
          le_trans hs_r₂
            (List.Pairwise.rel_getLast hrs_sorted (by simp [List.mem_cons]))
      · exact
          listInterlaces_all_le_getLast_local (rs := r₂ :: rs) (by simp)
            ((List.pairwise_cons.mp hrs_sorted).2) htail t ht

/-- Same-degree companion to
`interlaces_of_consecutive_signs_of_natDegree_lt`: if a nonzero polynomial `F`
has strict sign changes on consecutive roots of a real-rooted polynomial `f`,
has the same degree as `f`, and has one extra outer root on either side, then
`F` is real-rooted. This is the exact assembly step needed for the non-cancel
opposite-sign branch in the forward same-degree Obreschkoff theorem. -/
private theorem isRealRooted_of_consecutive_signs_of_natDegree_eq_of_outer_root
    {f F : ℝ[X]}
    (hf : IsRealRooted f) (hF_ne : F ≠ 0)
    (hdeg : F.natDegree = f.natDegree)
    (hdeg_pos : 1 ≤ f.natDegree)
    (hsign :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        f.roots.sort (· ≤ ·) = pre ++ r₁ :: r₂ :: rest →
        F.eval r₁ * F.eval r₂ < 0)
    (houter :
      (∃ uL, F.IsRoot uL ∧ ∀ r, f.IsRoot r → uL < r) ∨
      (∃ uR, F.IsRoot uR ∧ ∀ r, f.IsRoot r → r < uR)) :
    IsRealRooted F := by
  let rs := f.roots.sort (· ≤ ·)
  have hrs_eq : (↑rs : Multiset ℝ) = f.roots := Multiset.sort_eq ..
  have hrs_sorted : rs.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  obtain ⟨us, hus_len, hus_int, hus_roots, hus_pw⟩ :=
    exists_roots_strictly_interlacing_of_consecutive_signs
      (F := F) hrs_sorted (by simpa [rs] using hsign)
  have hrs_len : rs.length = f.natDegree := by
    rw [show rs = f.roots.sort (· ≤ ·) by rfl, Multiset.length_sort, hf.2]
  have hrs_ne : rs ≠ [] := by
    intro hrs_nil
    simp [hrs_nil] at hrs_len
    omega
  have hus_sub : (↑us : Multiset ℝ) ≤ F.roots := by
    rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr (hus_pw.imp ne_of_lt))]
    intro x hx
    exact (mem_roots hF_ne).mpr (hus_roots x (Multiset.mem_coe.mp hx))
  have hus_len_deg : us.length = F.natDegree - 1 := by
    omega
  rcases houter with ⟨uL, huL_root, huL_lt⟩ | ⟨uR, huR_root, huR_lt⟩
  · obtain ⟨r₀, rs', hrs_cons⟩ : ∃ r₀ rs', rs = r₀ :: rs' := by
      cases h : rs with
      | nil => cases (hrs_ne h)
      | cons r₀ rs' =>
          refine ⟨r₀, rs', ?_⟩
          simpa using h.symm
    have hr₀_root : f.IsRoot r₀ := by
      apply (mem_roots hf.1).mp
      rw [← hrs_eq, hrs_cons]
      exact Multiset.mem_coe.mpr (by simp)
    have hus_int' : ListInterlaces us (r₀ :: rs') := by
      simpa [hrs_cons] using hus_int
    have huL_lt_all_us : ∀ u ∈ us, uL < u := by
      intro u hu
      exact lt_of_lt_of_le (huL_lt r₀ hr₀_root)
        (listInterlaces_all_ge us rs' r₀ hus_int' u hu)
    have hws_pw : (uL :: us).Pairwise (· < ·) := by
      refine List.pairwise_cons.mpr ⟨?_, hus_pw⟩
      intro u hu
      exact huL_lt_all_us u hu
    have hws_sub : (↑(uL :: us) : Multiset ℝ) ≤ F.roots := by
      rw [Multiset.le_iff_subset (Multiset.coe_nodup.mpr (hws_pw.imp ne_of_lt))]
      intro x hx
      rcases List.mem_cons.mp (Multiset.mem_coe.mp hx) with rfl | hx'
      · exact (mem_roots hF_ne).mpr huL_root
      · exact (mem_roots hF_ne).mpr (hus_roots x hx')
    have hws_len : (uL :: us).length = F.natDegree := by
      calc
        (uL :: us).length = us.length + 1 := by simp
        _ = F.natDegree := by omega
    have hws_eq : (↑(uL :: us) : Multiset ℝ) = F.roots :=
      Multiset.eq_of_le_of_card_le hws_sub (by
        calc
          F.roots.card ≤ F.natDegree := card_roots' F
          _ = (uL :: us).length := hws_len.symm
          _ = (↑(uL :: us) : Multiset ℝ).card := (Multiset.coe_card _).symm)
    refine ⟨hF_ne, ?_⟩
    rw [← hws_eq, Multiset.coe_card, hws_len]
  · have hu_mem : rs.getLast hrs_ne ∈ rs := List.getLast_mem hrs_ne
    have hu_root : f.IsRoot (rs.getLast hrs_ne) := by
      apply (mem_roots hf.1).mp
      rw [← hrs_eq]
      exact Multiset.mem_coe.mpr hu_mem
    have hus_lt_all_uR : ∀ u ∈ us, u < uR := by
      intro u hu
      exact lt_of_le_of_lt
        (listInterlaces_all_le_getLast_local hrs_ne hrs_sorted hus_int u hu)
        (huR_lt _ hu_root)
    have hws_pw : (us ++ [uR]).Pairwise (· < ·) := by
      rw [List.pairwise_append]
      refine ⟨hus_pw, List.pairwise_singleton _ _, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst hb
      exact hus_lt_all_uR a ha
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
        _ = F.natDegree := by omega
    have hws_eq : (↑(us ++ [uR]) : Multiset ℝ) = F.roots :=
      Multiset.eq_of_le_of_card_le hws_sub (by
        calc
          F.roots.card ≤ F.natDegree := card_roots' F
          _ = (us ++ [uR]).length := hws_len.symm
          _ = (↑(us ++ [uR]) : Multiset ℝ).card := (Multiset.coe_card _).symm)
    refine ⟨hF_ne, ?_⟩
    rw [← hws_eq, Multiset.coe_card, hws_len]

/-- A nonconstant real-rooted polynomial has a rightmost root. -/
private lemma exists_rightmost_root_of_isRealRooted
    {p : ℝ[X]} (hp : IsRealRooted p) (hdeg : 1 ≤ p.natDegree) :
    ∃ r, p.IsRoot r ∧ ∀ s ∈ p.roots, s ≤ r := by
  let rs := p.roots.sort (· ≤ ·)
  have hrs_eq : (↑rs : Multiset ℝ) = p.roots := Multiset.sort_eq ..
  have hrs_sorted : rs.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hrs_len : rs.length = p.natDegree := by
    rw [show rs = p.roots.sort (· ≤ ·) by rfl, Multiset.length_sort, hp.2]
  have hrs_ne : rs ≠ [] := by
    intro hrs_nil
    simp [hrs_nil] at hrs_len
    omega
  refine ⟨rs.getLast hrs_ne, ?_, ?_⟩
  · have hr_mem : rs.getLast hrs_ne ∈ rs := List.getLast_mem hrs_ne
    have : rs.getLast hrs_ne ∈ p.roots := by
      rw [← hrs_eq]
      exact Multiset.mem_coe.mpr hr_mem
    exact (mem_roots hp.1).mp this
  · intro s hs
    have hs_mem : s ∈ rs := by
      apply Multiset.mem_coe.mp
      rwa [hrs_eq]
    exact hrs_sorted.rel_getLast hs_mem

/-- If every root of `p` lies strictly to the left of `r`, then `p(r) > 0`
for positive leading coefficient. This local copy is exactly the sign input
needed to make the rightmost-critical-point argument compile in this file,
without depending on Ma-Wang's private helper namespace. -/
private lemma eval_pos_of_all_roots_lt_local {p : ℝ[X]} {r : ℝ}
    (hp : IsRealRooted p) (hp_pos : HasPosLeadingCoeff p)
    (hlt : ∀ t ∈ p.roots, t < r) :
    0 < p.eval r := by
  rw [eval_eq_leadingCoeff_mul_prod_sub hp r]
  have hprod : 0 < (p.roots.map (r - ·)).prod := by
    refine Multiset.prod_pos ?_
    intro y hy
    rcases Multiset.mem_map.mp hy with ⟨t, ht, rfl⟩
    exact sub_pos.mpr (hlt t ht)
  exact mul_pos hp_pos hprod

private lemma eval_pos_of_all_roots_gt_of_even_local {p : ℝ[X]} {r : ℝ}
    (hp : IsRealRooted p) (hp_pos : HasPosLeadingCoeff p)
    (hdeg : 0 < p.degree) (hpar : Even p.natDegree)
    (hgt : ∀ t ∈ p.roots, r < t) :
    0 < p.eval r := by
  have ht : Filter.Tendsto (fun x => p.eval x) Filter.atBot Filter.atTop :=
    tendsto_eval_atBot_atTop_of_posLeadingCoeff_even hp_pos hdeg hpar
  by_contra hnonpos
  rcases eq_or_lt_of_le (le_of_not_gt hnonpos) with hzero | hneg
  · have hr_root : p.IsRoot r := by
      simpa [Polynomial.IsRoot.def] using hzero
    exact lt_irrefl r (hgt r ((mem_roots hp.1).mpr hr_root))
  · obtain ⟨u, hu_le, hu_root⟩ := exists_isRoot_le_of_eval_neg_of_tendsto_atBot_atTop hneg ht
    exact not_lt_of_ge hu_le (hgt u ((mem_roots hp.1).mpr hu_root))

private lemma eval_neg_of_all_roots_gt_of_odd_local {p : ℝ[X]} {r : ℝ}
    (hp : IsRealRooted p) (hp_pos : HasPosLeadingCoeff p)
    (hdeg : 0 < p.degree) (hpar : Odd p.natDegree)
    (hgt : ∀ t ∈ p.roots, r < t) :
    p.eval r < 0 := by
  have ht : Filter.Tendsto (fun x => p.eval x) Filter.atBot Filter.atBot :=
    tendsto_eval_atBot_atBot_of_posLeadingCoeff_odd hp_pos hdeg hpar
  by_contra hnonneg
  rcases eq_or_lt_of_le (le_of_not_gt hnonneg) with hzero | hpos
  · have hr_root : p.IsRoot r := by
      simpa [eq_comm, Polynomial.IsRoot.def] using hzero
    exact lt_irrefl r (hgt r ((mem_roots hp.1).mpr hr_root))
  · obtain ⟨u, hu_le, hu_root⟩ := exists_isRoot_le_of_eval_pos_of_tendsto_atBot_atBot hpos ht
    exact not_lt_of_ge hu_le (hgt u ((mem_roots hp.1).mpr hu_root))

/-- Same-degree `hroot_sign` real-rootedness without assuming the target has
positive leading coefficient.

The positive-leading branch is already Ma--Wang:
`prec_of_interlaces_eval_mul_neg_same`. The genuinely new content here is the
negative-leading branch: strict sign changes still force real-rootedness, but
the extra root now comes from the left endpoint rather than the right. This is
exactly the helper needed for the opposite-sign, non-cancel branch in the
forward same-degree Obreschkoff theorem. -/
private theorem isRealRooted_of_interlaces_eval_mul_neg_same_any_lc
    {f g F : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : F.natDegree = f.natDegree)
    (hdeg_pos : 2 ≤ f.natDegree)
    (hroot_sign : ∀ r, f.IsRoot r → F.eval r * g.eval r < 0) :
    IsRealRooted F := by
  by_cases hF_pos : HasPosLeadingCoeff F
  · exact (prec_of_interlaces_eval_mul_neg_same hgf hg_pos hF_pos hdeg hroot_sign).2.1
  obtain ⟨hf, hg, hgdeg, rs0, ss, hrs0_sorted, hss_sorted, hrs0_eq, hss_eq, hint0⟩ := hgf
  let rs := f.roots.sort (· ≤ ·)
  have hrs_eq : (↑rs : Multiset ℝ) = f.roots := Multiset.sort_eq ..
  have hrs_sorted : rs.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hrs0_eq_rs : rs0 = rs := by
    apply List.Perm.eq_of_pairwise' hrs0_sorted hrs_sorted
    exact Multiset.coe_eq_coe.mp (hrs0_eq.trans hrs_eq.symm)
  subst hrs0_eq_rs
  have hint : ListInterlaces ss rs := by
    simpa using hint0
  have hgf' : Interlaces g f :=
    ⟨hf, hg, hgdeg, rs, ss, hrs_sorted, hss_sorted, hrs_eq,
      hss_eq, hint⟩
  have hF_natdeg_pos : 0 < F.natDegree := by
    rw [hdeg]
    omega
  have hF_ne : F ≠ 0 := by
    intro h0
    simp [h0] at hF_natdeg_pos
  have hF_lc_ne : F.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hF_ne
  have hF_lc_neg : F.leadingCoeff < 0 := by
    unfold HasPosLeadingCoeff at hF_pos
    exact lt_of_le_of_ne (le_of_not_gt hF_pos) hF_lc_ne
  have hrs_len : rs.length = f.natDegree := by
    rw [show rs = f.roots.sort (· ≤ ·) by rfl, Multiset.length_sort, hf.2]
  have hrs_ne : rs ≠ [] := by
    intro hrs_nil
    simp [hrs_nil] at hrs_len
    omega
  obtain ⟨r₀, rs', hrs_cons⟩ : ∃ r₀ rs', rs = r₀ :: rs' := by
    cases h : rs with
    | nil => cases (hrs_ne h)
    | cons r₀ rs' =>
        exact ⟨r₀, rs', by simpa using h.symm⟩
  have hint_cons : ListInterlaces ss (r₀ :: rs') := by
    simpa [hrs_cons] using hint
  have hhead_eq : rs.head! = r₀ := by
    simp [hrs_cons]
  have hr₀_root : f.IsRoot r₀ := by
    apply (mem_roots hf.1).mp
    rw [← hrs_eq, hrs_cons]
    exact Multiset.mem_coe.mpr (by simp)
  have hno_g_at_f : ∀ r, f.IsRoot r → ¬ g.IsRoot r := by
    intro r hr hgr
    have hprod := hroot_sign r hr
    have hg0 : g.eval r = 0 := by
      simpa [Polynomial.IsRoot.def] using hgr
    have : F.eval r * g.eval r = 0 := by
      simp [hg0]
    nlinarith [hprod, this]
  have hhead_lt_roots_g : ∀ t ∈ g.roots, r₀ < t := by
    intro t ht
    have ht_ss : t ∈ ss := by
      apply Multiset.mem_coe.mp
      rw [hss_eq]
      exact ht
    have hr₀_le_t : r₀ ≤ t := listInterlaces_all_ge ss rs' r₀ hint_cons t ht_ss
    have ht_root : g.IsRoot t := (mem_roots hg.1).mp ht
    by_contra hnot
    have ht_le_r₀ : t ≤ r₀ := le_of_not_gt hnot
    have hEq : t = r₀ := le_antisymm ht_le_r₀ hr₀_le_t
    exact hno_g_at_f r₀ hr₀_root (by simpa [hEq] using ht_root)
  have hsign :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        f.roots.sort (· ≤ ·) = pre ++ r₁ :: r₂ :: rest →
        F.eval r₁ * F.eval r₂ < 0 := by
    intro pre r₁ r₂ rest hEq
    have hEq_rs : rs = pre ++ r₁ :: r₂ :: rest := by
      simpa [rs] using hEq
    have hr₁_root : f.IsRoot r₁ := by
      apply (mem_roots hf.1).mp
      rw [← hrs_eq]
      exact Multiset.mem_coe.mpr (by rw [hEq_rs]; simp)
    have hr₂_root : f.IsRoot r₂ := by
      apply (mem_roots hf.1).mp
      rw [← hrs_eq]
      exact Multiset.mem_coe.mpr (by rw [hEq_rs]; simp)
    have hFg₁ : F.eval r₁ * g.eval r₁ < 0 := hroot_sign r₁ hr₁_root
    have hFg₂ : F.eval r₂ * g.eval r₂ < 0 := hroot_sign r₂ hr₂_root
    have hgg : g.eval r₁ * g.eval r₂ < 0 :=
      eval_mul_eval_neg_of_interlaces_consecutive_of_no_common hgf' hno_g_at_f pre hEq
    exact mul_neg_of_mul_neg_of_mul_neg_local hFg₁ hFg₂ hgg
  have hnegF_pos : HasPosLeadingCoeff (C (-1 : ℝ) * F) := by
    unfold HasPosLeadingCoeff
    rw [leadingCoeff_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr (by norm_num : (-1 : ℝ) ≠ 0)) F]
    nlinarith
  have hnegF_deg : (C (-1 : ℝ) * F).natDegree = f.natDegree := by
    rw [natDegree_C_mul (by norm_num : (-1 : ℝ) ≠ 0), hdeg]
  have hnegF_natdeg_pos : 0 < (C (-1 : ℝ) * F).natDegree := by
    rw [hnegF_deg]
    omega
  have hnegF_deg_pos : 0 < (C (-1 : ℝ) * F).degree :=
    natDegree_pos_iff_degree_pos.mp hnegF_natdeg_pos
  have hg_natdeg_pos : 1 ≤ g.natDegree := by
    omega
  have hg_deg_pos : 0 < g.degree := natDegree_pos_iff_degree_pos.mp hg_natdeg_pos
  have hleft :
      ∃ uL, F.IsRoot uL ∧ ∀ r, f.IsRoot r → uL < r := by
    rcases Nat.even_or_odd f.natDegree with hf_even | hf_odd
    · have hg_odd : Odd g.natDegree := by
        rcases hf_even with ⟨k, hk⟩
        have hk_pos : 0 < k := by
          omega
        refine ⟨k - 1, ?_⟩
        omega
      have hg_left_neg : g.eval r₀ < 0 :=
        eval_neg_of_all_roots_gt_of_odd_local hg hg_pos hg_deg_pos hg_odd hhead_lt_roots_g
      have hF_left_pos : 0 < F.eval r₀ := by
        have hprod := hroot_sign r₀ hr₀_root
        nlinarith
      have hnegF_left_neg : (C (-1 : ℝ) * F).eval r₀ < 0 := by
        rw [Polynomial.eval_mul, Polynomial.eval_C]
        nlinarith
      have hnegF_even : Even (C (-1 : ℝ) * F).natDegree := by
        rw [hnegF_deg]
        exact hf_even
      have ht :
          Filter.Tendsto (fun x => (C (-1 : ℝ) * F).eval x) Filter.atBot Filter.atTop :=
        tendsto_eval_atBot_atTop_of_posLeadingCoeff_even hnegF_pos hnegF_deg_pos hnegF_even
      obtain ⟨uL, huL_le, huL_root_neg⟩ :=
        exists_isRoot_le_of_eval_neg_of_tendsto_atBot_atTop hnegF_left_neg ht
      have huL_root : F.IsRoot uL := by
        have huL_eval_neg : (C (-1 : ℝ) * F).eval uL = 0 := by
          simpa [Polynomial.IsRoot.def] using huL_root_neg
        rw [Polynomial.eval_mul, Polynomial.eval_C] at huL_eval_neg
        have huL_eval : F.eval uL = 0 := by
          exact (mul_eq_zero.mp huL_eval_neg).resolve_left (by norm_num)
        simpa [Polynomial.IsRoot.def] using huL_eval
      have huL_lt_r₀ : uL < r₀ := by
        refine lt_of_le_of_ne huL_le ?_
        intro hEq
        have : F.eval r₀ = 0 := by
          simpa [Polynomial.IsRoot.def, hEq] using huL_root
        exact (ne_of_gt hF_left_pos) this
      refine ⟨uL, huL_root, ?_⟩
      intro r hr
      have hr_mem : r ∈ rs := by
        apply Multiset.mem_coe.mp
        rw [hrs_eq]
        exact (mem_roots hf.1).mpr hr
      have hr₀_le_r : r₀ ≤ r := by
        rw [← hhead_eq]
        exact hrs_sorted.head!_le hr_mem
      exact lt_of_lt_of_le huL_lt_r₀ hr₀_le_r
    · have hg_even : Even g.natDegree := by
        rcases hf_odd with ⟨k, hk⟩
        refine ⟨k, ?_⟩
        omega
      have hg_left_pos : 0 < g.eval r₀ :=
        eval_pos_of_all_roots_gt_of_even_local hg hg_pos hg_deg_pos hg_even hhead_lt_roots_g
      have hF_left_neg : F.eval r₀ < 0 := by
        have hprod := hroot_sign r₀ hr₀_root
        nlinarith
      have hnegF_left_pos : 0 < (C (-1 : ℝ) * F).eval r₀ := by
        rw [Polynomial.eval_mul, Polynomial.eval_C]
        nlinarith
      have hnegF_odd : Odd (C (-1 : ℝ) * F).natDegree := by
        rw [hnegF_deg]
        exact hf_odd
      have ht :
          Filter.Tendsto (fun x => (C (-1 : ℝ) * F).eval x) Filter.atBot Filter.atBot :=
        tendsto_eval_atBot_atBot_of_posLeadingCoeff_odd hnegF_pos hnegF_deg_pos hnegF_odd
      obtain ⟨uL, huL_le, huL_root_neg⟩ :=
        exists_isRoot_le_of_eval_pos_of_tendsto_atBot_atBot hnegF_left_pos ht
      have huL_root : F.IsRoot uL := by
        have huL_eval_neg : (C (-1 : ℝ) * F).eval uL = 0 := by
          simpa [Polynomial.IsRoot.def] using huL_root_neg
        rw [Polynomial.eval_mul, Polynomial.eval_C] at huL_eval_neg
        have huL_eval : F.eval uL = 0 := by
          exact (mul_eq_zero.mp huL_eval_neg).resolve_left (by norm_num)
        simpa [Polynomial.IsRoot.def] using huL_eval
      have huL_lt_r₀ : uL < r₀ := by
        refine lt_of_le_of_ne huL_le ?_
        intro hEq
        have : F.eval r₀ = 0 := by
          simpa [Polynomial.IsRoot.def, hEq] using huL_root
        exact (ne_of_lt hF_left_neg) this
      refine ⟨uL, huL_root, ?_⟩
      intro r hr
      have hr_mem : r ∈ rs := by
        apply Multiset.mem_coe.mp
        rw [hrs_eq]
        exact (mem_roots hf.1).mpr hr
      have hr₀_le_r : r₀ ≤ r := by
        rw [← hhead_eq]
        exact hrs_sorted.head!_le hr_mem
      exact lt_of_lt_of_le huL_lt_r₀ hr₀_le_r
  exact
    isRealRooted_of_consecutive_signs_of_natDegree_eq_of_outer_root
      hf hF_ne hdeg (by omega) hsign (Or.inl hleft)

/-- If all roots of `p'` are at most `c`, then `p.eval` is strictly increasing
on `[c, +∞)`. This is the analytic core of the degree-gap argument: once the
last critical point is known, any larger real root would force a contradiction. -/
private lemma strictMonoOn_eval_Ici_of_derivative_roots_le
    {p : ℝ[X]} {c : ℝ}
    (hp' : IsRealRooted p.derivative)
    (hp'_pos : HasPosLeadingCoeff p.derivative)
    (hroots_le : ∀ s ∈ p.derivative.roots, s ≤ c) :
    StrictMonoOn (fun x => p.eval x) (Set.Ici c) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici c) p.continuous.continuousOn ?_
  intro x hx
  have hx' : c < x := by simpa using hx
  have hlt : ∀ t ∈ p.derivative.roots, t < x := by
    intro t ht
    exact lt_of_le_of_lt (hroots_le t ht) hx'
  have hpos_eval : 0 < p.derivative.eval x :=
    eval_pos_of_all_roots_lt_local hp' hp'_pos hlt
  simpa using hpos_eval

/-- A root of `p'` always has a root of `p` weakly to its right. We package the
rightmost-root extraction here because it is reused twice in the degree-gap
reduction: first to show a real-rooted polynomial must be nonpositive at its
last critical point, and then again to contradict real-rootedness after a
constant shift. -/
private lemma exists_root_ge_of_derivative_root
    {p : ℝ[X]} (hp : IsRealRooted p) (hdeg : 2 ≤ p.natDegree)
    {c : ℝ} (hc : p.derivative.IsRoot c) :
    ∃ r, p.IsRoot r ∧ c ≤ r := by
  obtain ⟨hp_rr, hp'_rr, _hdeg, rs, ss, hrs_sorted, hss_sorted, hrs_eq, hss_eq, hint⟩ :=
    derivative_interlaces hp hdeg
  have hrs_len : rs.length = p.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, hp_rr.2]
  have hrs_ne : rs ≠ [] := by
    intro hrs_nil
    simp [hrs_nil] at hrs_len
    omega
  have hc_mem : c ∈ ss := by
    apply Multiset.mem_coe.mp
    rw [hss_eq]
    exact (mem_roots hp'_rr.1).mpr hc
  refine ⟨rs.getLast hrs_ne, ?_, ?_⟩
  · have hr_mem : rs.getLast hrs_ne ∈ rs := List.getLast_mem hrs_ne
    have : rs.getLast hrs_ne ∈ p.roots := by
      rw [← hrs_eq]
      exact Multiset.mem_coe.mpr hr_mem
    exact (mem_roots hp_rr.1).mp this
  · exact listInterlaces_all_le_getLast_local hrs_ne hrs_sorted hint c hc_mem

/-- Exact degree bookkeeping for iterated derivatives. We use this in the
degree-gap reduction to show that differentiating the smaller polynomial down to
degree `0` still leaves the larger one with degree at least `2`. -/
private lemma natDegree_iterate_derivative_eq_sub
    {p : ℝ[X]} {k : ℕ} (hp0 : p ≠ 0) (hk : k ≤ p.natDegree) :
    (derivative^[k] p).natDegree = p.natDegree - k := by
  apply le_antisymm (natDegree_iterate_derivative p k)
  apply le_natDegree_of_ne_zero
  have hcoeff :
      (derivative^[k] p).coeff (p.natDegree - k) ≠ 0 := by
    rw [coeff_iterate_derivative, Nat.sub_add_cancel hk, nsmul_eq_mul, coeff_natDegree]
    exact mul_ne_zero
      (Nat.cast_ne_zero.mpr (Nat.descFactorial_pos.mpr hk).ne')
      (leadingCoeff_ne_zero.mpr hp0)
  exact hcoeff

/-- Iterated derivatives stay nonzero as long as we do not differentiate past
the degree. -/
private lemma iterate_derivative_ne_zero_of_le_natDegree
    {p : ℝ[X]} {k : ℕ} (hp0 : p ≠ 0) (hk : k ≤ p.natDegree) :
    (derivative^[k] p) ≠ 0 := by
  intro hk0
  have hcoeff :
      (derivative^[k] p).coeff (p.natDegree - k) ≠ 0 := by
    rw [coeff_iterate_derivative, Nat.sub_add_cancel hk, nsmul_eq_mul, coeff_natDegree]
    exact mul_ne_zero
      (Nat.cast_ne_zero.mpr (Nat.descFactorial_pos.mpr hk).ne')
      (leadingCoeff_ne_zero.mpr hp0)
  simpa [hk0] using hcoeff

/-- A positive-leading real-rooted polynomial of degree at least `2` is
nonpositive at its rightmost critical point. The point is chosen as the
rightmost root of `p'`; to the right of it the derivative is strictly
positive, so a positive value there would prevent the real-rooted polynomial
itself from having any root on its right, contradicting interlacing of `p'`
with `p`. -/
private lemma exists_rightmost_derivative_root_with_eval_nonpos
    {p : ℝ[X]} (hp : IsRealRooted p) (hp_pos : HasPosLeadingCoeff p)
    (hdeg : 2 ≤ p.natDegree) :
    ∃ c, p.derivative.IsRoot c ∧
      (∀ s ∈ p.derivative.roots, s ≤ c) ∧
      p.eval c ≤ 0 := by
  have hp' : IsRealRooted p.derivative := (derivative_interlaces hp hdeg).2.1
  have hp'_pos : HasPosLeadingCoeff p.derivative :=
    hasPosLeadingCoeff_derivative_of_pos hp_pos (by omega)
  have hp'_deg : p.derivative.natDegree = p.natDegree - 1 :=
    natDegree_derivative_eq (by omega)
  obtain ⟨c, hc_root, hc_top⟩ :=
    exists_rightmost_root_of_isRealRooted hp' (by rw [hp'_deg]; omega)
  have hnonpos : p.eval c ≤ 0 := by
    by_contra hpc
    have hmono :
        StrictMonoOn (fun x => p.eval x) (Set.Ici c) :=
      strictMonoOn_eval_Ici_of_derivative_roots_le hp' hp'_pos hc_top
    obtain ⟨r, hr_root, hcr_le⟩ := exists_root_ge_of_derivative_root hp hdeg hc_root
    by_cases hcr : c = r
    · have : p.eval c = 0 := by
        simpa [Polynomial.IsRoot.def, hcr] using hr_root
      linarith
    · have hcr_lt : c < r := lt_of_le_of_ne hcr_le hcr
      have hlt_eval : p.eval c < p.eval r := hmono (by simp) (by exact hcr_le) hcr_lt
      have : p.eval r = 0 := by
        simpa [Polynomial.IsRoot.def] using hr_root
      linarith
  exact ⟨c, hc_root, hc_top, hnonpos⟩

/-- Constant shifts eventually destroy real-rootedness once the polynomial has
degree at least `2`. This is the key obstruction used in the degree-closeness
theorem below. The proof shifts the polynomial upward past its value at the
rightmost critical point; the derivative is unchanged, so the shifted
polynomial would still need a real root on the right by interlacing, but it is
already strictly increasing there. -/
private lemma exists_shift_not_isRealRooted_of_isRealRooted_of_natDegree_ge_two
    {p : ℝ[X]} (hp : IsRealRooted p) (hp_pos : HasPosLeadingCoeff p)
    (hdeg : 2 ≤ p.natDegree) :
    ∃ t : ℝ, ¬ IsRealRooted (C t + p) := by
  obtain ⟨c, hc_root, hc_top, hpc_nonpos⟩ :=
    exists_rightmost_derivative_root_with_eval_nonpos hp hp_pos hdeg
  let t : ℝ := 1 - p.eval c
  refine ⟨t, ?_⟩
  intro hq
  have hqdeg : 2 ≤ (C t + p).natDegree := by
    rw [natDegree_add_eq_right_of_natDegree_lt (by
      rw [natDegree_C]
      omega)]
    exact hdeg
  have hq'_rr : IsRealRooted (C t + p).derivative := (derivative_interlaces hq hqdeg).2.1
  have hmono :
      StrictMonoOn (fun x => (C t + p).eval x) (Set.Ici c) := by
    have hder_eq : (C t + p).derivative = p.derivative := by
      simp
    refine strictMonoOn_eval_Ici_of_derivative_roots_le ?_ ?_ ?_
    · simpa [hder_eq] using hq'_rr
    · simpa [hder_eq] using hasPosLeadingCoeff_derivative_of_pos hp_pos (by omega)
    · intro s hs
      have hs' : s ∈ p.derivative.roots := by
        simpa [hder_eq] using hs
      exact hc_top s hs'
  have hqc_pos : 0 < (C t + p).eval c := by
    have : (C t + p).eval c = 1 := by
      simp [t]
    linarith
  obtain ⟨r, hr_root, hcr_le⟩ := exists_root_ge_of_derivative_root hq hqdeg (by
    simpa using hc_root)
  by_cases hcr : c = r
  · have : (C t + p).eval c = 0 := by
      simpa [Polynomial.IsRoot.def, hcr] using hr_root
    linarith
  · have hcr_lt : c < r := lt_of_le_of_ne hcr_le hcr
    have hlt_eval :
        (C t + p).eval c < (C t + p).eval r := hmono (by simp) (by exact hcr_le) hcr_lt
    have : (C t + p).eval r = 0 := by
      simpa [Polynomial.IsRoot.def] using hr_root
    linarith

/-- A nonzero constant cannot form an `AllComboRealRooted` pair with a
positive-leading degree-`≥ 2` polynomial: a suitable constant shift of the
second polynomial fails to be real-rooted. -/
private theorem not_allComboRealRooted_const_left_of_natDegree_ge_two_of_pos
    {c : ℝ} {p : ℝ[X]}
    (hc : c ≠ 0)
    (hp : IsRealRooted p) (hp_pos : HasPosLeadingCoeff p)
    (hdeg : 2 ≤ p.natDegree) :
    ¬ AllComboRealRooted (C c) p := by
  intro hall
  obtain ⟨t, ht⟩ :=
    exists_shift_not_isRealRooted_of_isRealRooted_of_natDegree_ge_two hp hp_pos hdeg
  have hcombo_t : C t + p = 0 ∨ IsRealRooted (C t + p) := by
    have hrewrite : C (t / c) * C c + p = C t + p := by
      calc
        C (t / c) * C c + p = C ((t / c) * c) + p := by
          simp [C_mul]
        _ = C t + p := by
          congr 1
          field_simp [hc]
    simpa [hrewrite] using (hall (t / c) 1)
  rcases hcombo_t with hzero | hrr
  · have hp_const : p = -C t := by
      calc
        p = -C t + (C t + p) := by ring
        _ = -C t := by simp [hzero]
    rw [hp_const, natDegree_neg, natDegree_C] at hdeg
    omega
  · exact ht hrr

/-- Sign-normalized version of the constant-vs-degree-`≥ 2` obstruction.

This is the exact lemma used in the degree-closeness theorem: after enough
ordinary derivatives, one polynomial becomes a nonzero constant while the other
still has degree at least `2`, so `AllComboRealRooted` is impossible. -/
private theorem not_allComboRealRooted_const_left_of_natDegree_ge_two
    {c : ℝ} {p : ℝ[X]}
    (hc : c ≠ 0)
    (hp : IsRealRooted p)
    (hdeg : 2 ≤ p.natDegree) :
    ¬ AllComboRealRooted (C c) p := by
  by_cases hp_pos : 0 < p.leadingCoeff
  · exact
      not_allComboRealRooted_const_left_of_natDegree_ge_two_of_pos
        hc hp hp_pos hdeg
  · intro hall
    have hneg_rr : IsRealRooted (-p) := by
      simpa using isRealRooted_C_mul (p := p) hp (a := (-1 : ℝ)) (by norm_num)
    have hneg_pos : HasPosLeadingCoeff (-p) := by
      unfold HasPosLeadingCoeff
      rw [leadingCoeff_neg]
      have hne0 : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp.1
      have hlt : p.leadingCoeff < 0 := by
        exact lt_of_le_of_ne (le_of_not_gt hp_pos) (by simpa using hne0)
      linarith
    have hall_neg : AllComboRealRooted (C c) (-p) := by
      simpa using
        (allComboRealRooted_C_mul_right (f := C c) (g := p) (c := (-1 : ℝ)) hall)
    exact
      not_allComboRealRooted_const_left_of_natDegree_ge_two_of_pos
        hc hneg_rr hneg_pos (by simpa [natDegree_neg] using hdeg) hall_neg

/-- A degree gap of at least `2` is incompatible with `AllComboRealRooted`.

This is the degree-only part of the Obreschkoff converse. It is intentionally
recorded separately because it is a useful first reduction for future agents:
before arguing about root order or orientation, we can already rule out large
degree gaps by differentiating down to the constant-vs-degree-`≥ 2` case. -/
private theorem not_degree_gap_ge_two_of_allComboRealRooted
    {f g : ℝ[X]}
    (hall : AllComboRealRooted f g)
    (hf0 : f ≠ 0) (hg0 : g ≠ 0)
    (hgap : f.natDegree + 2 ≤ g.natDegree) :
    False := by
  let n : ℕ := f.natDegree
  let fN : ℝ[X] := (derivative^[n]) f
  let gN : ℝ[X] := (derivative^[n]) g
  have hallN : AllComboRealRooted fN gN := by
    simpa [n, fN, gN] using allComboRealRooted_iterate_derivative hall n
  have hfN_deg : fN.natDegree = 0 := by
    dsimp [fN, n]
    simpa using natDegree_iterate_derivative_eq_sub hf0 (le_rfl : f.natDegree ≤ f.natDegree)
  have hfN_ne : fN ≠ 0 := by
    dsimp [fN, n]
    exact iterate_derivative_ne_zero_of_le_natDegree hf0 (le_rfl : f.natDegree ≤ f.natDegree)
  have hfN_C : fN = C (fN.coeff 0) := eq_C_of_natDegree_eq_zero hfN_deg
  have hfN_coeff_ne : fN.coeff 0 ≠ 0 := by
    intro h0
    have : fN = 0 := by simpa [h0] using hfN_C
    exact hfN_ne this
  set cf : ℝ := fN.coeff 0
  have hfN_C' : fN = C cf := by
    change fN = C (fN.coeff 0)
    exact hfN_C
  have hgN_deg : gN.natDegree = g.natDegree - n := by
    dsimp [gN, n]
    exact natDegree_iterate_derivative_eq_sub hg0 (by omega)
  have hgN_deg_ge2 : 2 ≤ gN.natDegree := by
    rw [hgN_deg]
    dsimp [n]
    omega
  have hgN_ne : gN ≠ 0 := by
    dsimp [gN, n]
    exact iterate_derivative_ne_zero_of_le_natDegree hg0 (by omega)
  have hgN_rr : IsRealRooted gN := by
    rcases hallN 0 1 with hzero | hrr
    · exact False.elim (hgN_ne (by simpa [fN, gN, add_comm] using hzero))
    · simpa [fN, gN, add_comm] using hrr
  exact
    not_allComboRealRooted_const_left_of_natDegree_ge_two
      (c := cf) (p := gN) (by simpa [cf] using hfN_coeff_ne) hgN_rr hgN_deg_ge2
      (by simpa [hfN_C'] using hallN)

/-- Degree control for the Obreschkoff converse.

The zero-polynomial caveat is essential: `AllComboRealRooted f 0` holds for any
real-rooted `f`, so no degree bound is possible without `f ≠ 0` and `g ≠ 0`.
With that caveat, every all-real-rooted 2-plane is already forced into the
same-degree / differ-by-1 regime before any root-order arguments begin. -/
theorem natDegree_close_of_allComboRealRooted
    {f g : ℝ[X]}
    (hall : AllComboRealRooted f g)
    (hf0 : f ≠ 0) (hg0 : g ≠ 0) :
    f.natDegree ≤ g.natDegree + 1 ∧
      g.natDegree ≤ f.natDegree + 1 := by
  constructor
  · by_contra hfg
    exact
      not_degree_gap_ge_two_of_allComboRealRooted
        (f := g) (g := f) (allComboRealRooted_comm hall) hg0 hf0 (by omega)
  · by_contra hgf
    exact not_degree_gap_ge_two_of_allComboRealRooted hall hf0 hg0 (by omega)

/-- Equivalent trichotomy form of `natDegree_close_of_allComboRealRooted`. -/
theorem natDegree_eq_or_succ_or_revSucc_of_allComboRealRooted
    {f g : ℝ[X]}
    (hall : AllComboRealRooted f g)
    (hf0 : f ≠ 0) (hg0 : g ≠ 0) :
    f.natDegree = g.natDegree ∨
      f.natDegree + 1 = g.natDegree ∨
      g.natDegree + 1 = f.natDegree := by
  rcases natDegree_close_of_allComboRealRooted hall hf0 hg0 with ⟨hfg, hgf⟩
  omega

private theorem prec_of_allComboRealRooted_of_no_common
    (hstep :
      ∀ {f g : ℝ[X]},
        IsRealRooted f →
        IsRealRooted g →
        AllComboRealRooted f g →
        (f.natDegree + 1 = g.natDegree ∨ f.natDegree = g.natDegree) →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        Prec f g ∨ Prec g f)
    {f g : ℝ[X]}
    (hf : IsRealRooted f) (hg : IsRealRooted g)
    (hall : AllComboRealRooted f g)
    (hdeg : f.natDegree + 1 = g.natDegree ∨ f.natDegree = g.natDegree) :
    Prec f g ∨ Prec g f := by
  refine
    Nat.strong_induction_on
      (p := fun n =>
        ∀ {f g : ℝ[X]},
          f.natDegree = n →
          IsRealRooted f →
          IsRealRooted g →
          AllComboRealRooted f g →
          (f.natDegree + 1 = g.natDegree ∨ f.natDegree = g.natDegree) →
          Prec f g ∨ Prec g f)
      f.natDegree ?_ rfl hf hg hall hdeg
  intro n ih f g hfdeg hf hg hall hdeg
  by_cases hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r
  · exact hstep hf hg hall hdeg hno
  · push_neg at hno
    rcases hno with ⟨r, hrf, hrg⟩
    obtain ⟨qf, hqf⟩ := dvd_iff_isRoot.mpr hrf
    obtain ⟨qg, hqg⟩ := dvd_iff_isRoot.mpr hrg
    have hqf_ne : qf ≠ 0 := by
      exact right_ne_zero_of_mul (by simpa [hqf] using hf.1)
    have hqg_ne : qg ≠ 0 := by
      exact right_ne_zero_of_mul (by simpa [hqg] using hg.1)
    have hqf_rr : IsRealRooted qf := by
      exact isRealRooted_of_dvd hf hqf_ne ⟨X - C r, by simpa [mul_comm] using hqf⟩
    have hqg_rr : IsRealRooted qg := by
      exact isRealRooted_of_dvd hg hqg_ne ⟨X - C r, by simpa [mul_comm] using hqg⟩
    have hqhall : AllComboRealRooted qf qg :=
      allComboRealRooted_common_root_reduction hqf hqg hall
    have hqdeg : qf.natDegree + 1 = qg.natDegree ∨ qf.natDegree = qg.natDegree := by
      rcases hdeg with hsucc | hsame
      · left
        rw [hqf, natDegree_mul (X_sub_C_ne_zero r) hqf_ne, natDegree_X_sub_C,
          hqg, natDegree_mul (X_sub_C_ne_zero r) hqg_ne, natDegree_X_sub_C] at hsucc
        omega
      · right
        rw [hqf, natDegree_mul (X_sub_C_ne_zero r) hqf_ne, natDegree_X_sub_C,
          hqg, natDegree_mul (X_sub_C_ne_zero r) hqg_ne, natDegree_X_sub_C] at hsame
        omega
    have hqf_deg_lt : qf.natDegree < n := by
      rw [← hfdeg, hqf, natDegree_mul (X_sub_C_ne_zero r) hqf_ne, natDegree_X_sub_C]
      omega
    have hprec_q : Prec qf qg ∨ Prec qg qf :=
      ih qf.natDegree hqf_deg_lt rfl hqf_rr hqg_rr hqhall hqdeg
    rcases hprec_q with hprec_q | hprec_q
    · left
      have hprec_mul : Prec ((X - C r) * qf) ((X - C r) * qg) :=
        prec_mul_common_factor (isRealRooted_X_sub_C r) hprec_q
      simpa [hqf, hqg] using hprec_mul
    · right
      have hprec_mul : Prec ((X - C r) * qg) ((X - C r) * qf) :=
        prec_mul_common_factor (isRealRooted_X_sub_C r) hprec_q
      simpa [hqf, hqg] using hprec_mul

/-- **Obreschkoff's theorem** (Brändén, Theorem 7.7.3): `f` and `g` interlace
if and only if every polynomial in the real linear span `{αf + βg : α, β ∈ ℝ}`
is real-rooted (or zero).

Forward direction: interlacing → all combinations real-rooted.
This follows from Wagner addition (already proved). -/
theorem prec_of_allComboRealRooted {f g : ℝ[X]}
    (hf : IsRealRooted f) (hg : IsRealRooted g)
    (hall : AllComboRealRooted f g)
    (hdeg : f.natDegree + 1 = g.natDegree ∨ f.natDegree = g.natDegree) :
    Prec f g ∨ Prec g f := by
  refine prec_of_allComboRealRooted_of_no_common ?_ hf hg hall hdeg
  intro f g hf hg hall hdeg hno
  let eps : ℝ := 1
  have heps : 0 < eps := by
    dsimp [eps]
    norm_num
  let n : ℕ := max f.natDegree g.natDegree
  have hsimple_data :
      AllComboRealRooted (iterateTDeriv eps n f) (iterateTDeriv eps n g) ∧
        IsRealRooted (iterateTDeriv eps n f) ∧
        IsRealRooted (iterateTDeriv eps n g) ∧
        HasSimpleRoots (iterateTDeriv eps n f) ∧
        HasSimpleRoots (iterateTDeriv eps n g) ∧
        ((iterateTDeriv eps n f).natDegree + 1 = (iterateTDeriv eps n g).natDegree ∨
          (iterateTDeriv eps n f).natDegree = (iterateTDeriv eps n g).natDegree) := by
    simpa [n] using simple_pair_of_allComboRealRooted_iterateTDeriv hf hg hall hdeg heps
  rcases hsimple_data with ⟨hall_iter, _, _, hf_simple, hg_simple, _⟩
  have hprec_iter :
      Prec (iterateTDeriv eps n f) (iterateTDeriv eps n g) ∨
        Prec (iterateTDeriv eps n g) (iterateTDeriv eps n f) := by
    simpa [n] using
      prec_or_revPrec_iterateTDeriv_of_allComboRealRooted_of_no_common
        hf hg hall hdeg heps hno
  have hlead_f_iter :
      (iterateTDeriv eps n f).leadingCoeff = f.leadingCoeff := by
    simpa [n] using
      leadingCoeff_iterateTDeriv_of_isRealRooted
        (eps := eps) (k := max f.natDegree g.natDegree) hf
  have hlead_g_iter :
      (iterateTDeriv eps n g).leadingCoeff = g.leadingCoeff := by
    simpa [n] using
      leadingCoeff_iterateTDeriv_of_isRealRooted
        (eps := eps) (k := max f.natDegree g.natDegree) hg
  have hpos_f_iter :
      HasPosLeadingCoeff (iterateTDeriv eps n f) ↔ HasPosLeadingCoeff f := by
    simpa [n] using
      hasPosLeadingCoeff_iterateTDeriv_of_isRealRooted
        (eps := eps) (k := max f.natDegree g.natDegree) hf
  have hpos_g_iter :
      HasPosLeadingCoeff (iterateTDeriv eps n g) ↔ HasPosLeadingCoeff g := by
    simpa [n] using
      hasPosLeadingCoeff_iterateTDeriv_of_isRealRooted
        (eps := eps) (k := max f.natDegree g.natDegree) hg
  have hsucc_iter_forced :
      f.natDegree + 1 = g.natDegree →
        Prec (iterateTDeriv eps n f) (iterateTDeriv eps n g) := by
    intro hsucc
    simpa [n] using
      prec_iterateTDeriv_of_allComboRealRooted_succ_of_no_common
        hf hg hall hsucc heps hno
  -- Handoff note:
  -- With `natDegree_close_of_allComboRealRooted` now available earlier in this
  -- file, the remaining converse has a clean two-case split (for nonzero
  -- inputs): up to swapping, either `f.natDegree + 1 = g.natDegree` or
  -- `f.natDegree = g.natDegree`.
  --
  -- The `+1` case is the right next target because the orientation is forced:
  -- one only has to prove `Prec f g`, not an Obreschkoff alternative. In that
  -- branch, `hprec_iter` should also collapse to the left orientation by degree
  -- alone after rewriting `hdeg_iter` with `natDegree_iterateTDeriv_of_isRealRooted`.
  -- So the remaining `+1`-case gap is strictly narrower than the same-degree
  -- gap: transport
  --   `Prec (iterateTDeriv eps n f) (iterateTDeriv eps n g)`
  -- back to
  --   `Prec f g`.
  --
  -- `hprec_iter` is now the fully regularized Obreschkoff conclusion for the
  -- simple `iterateTDeriv` pair. The remaining gap is *only* a transport step
  -- back to `(f, g)`. Two routes still look viable:
  -- 1. prove directly that `hall + hno` already forces every nonzero original
  --    combination `C α * f + C β * g` to have simple roots, then apply the
  --    helper theorem above to `(f, g)` itself and bypass `iterateTDeriv`;
  --    concretely, the target lemma is
  --    `∀ α β : ℝ,
  --        C α * f + C β * g = 0 ∨
  --          (IsRealRooted (C α * f + C β * g) ∧
  --            HasSimpleRoots (C α * f + C β * g))`.
  --    Once this is available, the endgame is exactly
  --    `prec_of_eq_zero_or_simple_combo_of_no_common hf hg hcombo_original hdeg hno`.
  -- 2. prove a closure / limit theorem saying that the orientation encoded by
  --    `hprec_iter` survives the `iterateTDeriv` regularization.
  --    In the succ-degree branch, the orientation issue is now resolved:
  --    `hsucc_iter_forced` packages the degree argument showing that the
  --    regularized pair cannot land in the reverse orientation. So the only
  --    missing succ-degree step is the transport
  --      `Prec (iterateTDeriv eps n f) (iterateTDeriv eps n g) -> Prec f g`.
  --    The new continuity primitives now live in `IteratedDerivativeShift`:
  --      * `iterateTDeriv_zero_eps`
  --      * `coeff_TDeriv`
  --      * `continuous_coeff_iterateTDeriv`
  --      * `continuousAt_coeff_iterateTDeriv_zero`
  --      * `continuous_eval_iterateTDeriv_joint`
  --      * `continuousAt_eval_iterateTDeriv_joint_zero`
  --      * `exists_delta_for_eval_iterateTDeriv_joint_at_zero`
  --      * `exists_delta_eval_mul_pos_iterateTDeriv_joint_at_zero`
  --      * `exists_delta_not_isRoot_iterateTDeriv_near_point`
  --      * `exists_delta_and_real_root_near_iterateTDeriv`
  --      * `exists_delta_and_real_root_near_iterateTDeriv_of_isRealRooted`
  --    So the clean next refactor is to stop fixing `eps := 1` here, keep
  --    `eps` symbolic, and combine those coefficientwise `ε → 0` facts with
  --    `RootContinuity`. The new non-monic nearby-root wrapper means the
  --    closure route can work after a one-time leading-coefficient/sign
  --    normalization, without rebuilding monic scaling inside the converse.
  --    For the slot-based variant of that closure route, the minimal public
  --    `CommonInterleaverSeq` API is now available as:
  --      * `polyOfDescRootsDesc`
  --      * `rootSeqDesc_polyOfDescRootsDesc_eq`
  --      * `mem_rootSlotInterval_of_prec_desc`
  --      * `rootSlot_lower_bound_of_mem`
  --      * `rootSlot_upper_bound_of_mem`
  --      * `prec_of_slots_polyOfDescRootsDesc`
  -- 3. reroute through the formalized right-family pair
  --    `(f + g, f + 2g)`: `allComboRealRooted_right_family_one_two` keeps us
  --    in the same Obreschkoff plane, and
  --    `no_common_root_right_family_one_two_of_no_common` keeps the no-common
  --    root hypothesis available for that basis change. The safe version of
  --    this route should first sign-normalize to positive leading coefficients;
  --    only then does the family reliably keep the top degree via
  --    `right_family_degree_data_of_posLeadingCoeff`. The key strict root-sign
  --    inputs are now also packaged:
  --    `eval_mul_right_family_one_neg_at_root_two_of_no_common` and
  --    `eval_mul_right_family_two_neg_at_root_one_of_no_common`.
  --    Concretely, the next Ma--Wang-style continuation to test is:
  --      a. scale `(f, g)` to positive-leading `(f₀, g₀)`;
  --      b. set `F := f₀ + g₀`, `G := f₀ + C (2 : ℝ) * g₀`;
  --      c. use `right_family_degree_data_of_posLeadingCoeff` to get the
  --         same-degree family bookkeeping;
  --      d. prove `Prec F G ∨ Prec G F`, then combine the two strict root-sign
  --         lemmas above with `prec_same_of_root_sign_data` / Ma--Wang to
  --         transport that orientation back to `Prec f₀ g₀ ∨ Prec g₀ f₀`;
  --      e. scale back to `(f, g)`.
  --    Important caveat: the tempting "pure subtraction" lemmas
  --      `Prec p q ↔ Prec p (q - p)` and `Prec p q ↔ Prec (p - q) q`
  --    are false for the current `Prec` API as stated; `prec_refl` already
  --    gives a counterexample by taking `p = q ≠ 0`, since then `q - p = 0`
  --    and `Prec p 0` does not hold. So this route still needs extra
  --    hypotheses/sign data, not just linear algebra on polynomials.
  --
  -- The new helper facts above also settle one normalization annoyance for the
  -- closure route: `iterateTDeriv` preserves leading coefficients exactly
  -- (`hlead_f_iter`, `hlead_g_iter`), hence preserves `HasPosLeadingCoeff`
  -- exactly (`hpos_f_iter`, `hpos_g_iter`). So if we sign-normalize `(f, g)`
  -- once, the entire regularized family keeps that normalization without any
  -- ε-dependent rescaling.
  --    The first two derived facts to keep in scope for that route are
  --    `have hall_family :
  --        AllComboRealRooted (f + g) (f + C (2 : ℝ) * g) :=
  --          allComboRealRooted_right_family_one_two hall`
  --    and
  --    `have hno_family :
  --        ∀ r, (f + g).IsRoot r → ¬ (f + C (2 : ℝ) * g).IsRoot r :=
  --          no_common_root_right_family_one_two_of_no_common hno`.
  --
  -- Either route should finish this theorem without changing the Wronskian
  -- infrastructure above. Keeping `hprec_iter` explicit here should make it
  -- easier for another agent to pick up from the exact reduced goal.
  have _hall_iter_keepalive : AllComboRealRooted (iterateTDeriv eps n f) (iterateTDeriv eps n g) :=
    hall_iter
  have _hf_simple_keepalive : HasSimpleRoots (iterateTDeriv eps n f) := hf_simple
  have _hg_simple_keepalive : HasSimpleRoots (iterateTDeriv eps n g) := hg_simple
  have _hlead_f_iter_keepalive :
      (iterateTDeriv eps n f).leadingCoeff = f.leadingCoeff := hlead_f_iter
  have _hlead_g_iter_keepalive :
      (iterateTDeriv eps n g).leadingCoeff = g.leadingCoeff := hlead_g_iter
  have _hpos_f_iter_keepalive :
      HasPosLeadingCoeff (iterateTDeriv eps n f) ↔ HasPosLeadingCoeff f := hpos_f_iter
  have _hpos_g_iter_keepalive :
      HasPosLeadingCoeff (iterateTDeriv eps n g) ↔ HasPosLeadingCoeff g := hpos_g_iter
  have _hsucc_iter_forced_keepalive :
      f.natDegree + 1 = g.natDegree →
        Prec (iterateTDeriv eps n f) (iterateTDeriv eps n g) := hsucc_iter_forced
  have hcombo_original :
      ∀ α β : ℝ,
        C α * f + C β * g = 0 ∨
          (IsRealRooted (C α * f + C β * g) ∧
            HasSimpleRoots (C α * f + C β * g)) := by
    by_cases hmax0 : max f.natDegree g.natDegree = 0
    · have hfdeg0 : f.natDegree = 0 := by omega
      have hgdeg0 : g.natDegree = 0 := by omega
      have hfC : f = C (f.coeff 0) := eq_C_of_natDegree_eq_zero hfdeg0
      have hgC : g = C (g.coeff 0) := eq_C_of_natDegree_eq_zero hgdeg0
      intro α β
      by_cases hcomb : C α * f + C β * g = 0
      · exact Or.inl hcomb
      · rw [hfC, hgC] at hcomb ⊢
        let c : ℝ := α * f.coeff 0 + β * g.coeff 0
        have hsum_eq :
            C α * C (f.coeff 0) + C β * C (g.coeff 0) =
              C c := by
          calc
            C α * C (f.coeff 0) + C β * C (g.coeff 0)
                = C (α * f.coeff 0) + C (β * g.coeff 0) := by simp [C_mul]
            _ = C (α * f.coeff 0 + β * g.coeff 0) := by rw [← C_add]
            _ = C c := by simp [c]
        have hconst_ne : C c ≠ 0 := by
          simpa [hsum_eq] using hcomb
        have hcoeff_ne : c ≠ 0 := by
          intro hzero
          exact hconst_ne (by simp [hzero])
        have hnat0 :
            (C α * C (f.coeff 0) + C β * C (g.coeff 0)).natDegree = 0 := by
          rw [hsum_eq]
          simp
        right
        refine ⟨?_, ?_⟩
        · exact isRealRooted_of_deg_zero hcomb hnat0
        · rw [hsum_eq]
          intro r hr
          have : c = 0 := by
            simpa [Polynomial.IsRoot.def, c] using hr
          exact (hcoeff_ne this).elim
    · have hmax_pos : 0 < max f.natDegree g.natDegree := Nat.pos_of_ne_zero hmax0
      have hW_ne : ∀ x : ℝ, (wronskian f g).eval x ≠ 0 := by
        /-
        Reduced live frontier.

        The remaining converse contradiction now starts from the special-pair
        reduction above: if the Wronskian vanished at `x`, we could replace
        `(f, g)` inside the same `AllComboRealRooted` plane by a pair `(p, q)`
        with no common roots such that
        * `p` has a multiple root at `x`,
        * `q.eval x ≠ 0`.

        So the last missing theorem is now the explicit contradiction:
        such a pair cannot exist in the positive-degree/no-common-root regime.
        The keepalive facts above (`hprec_iter`, `hall_iter`, `hf_simple`,
        `hg_simple`, `hlead_*_iter`, `hpos_*_iter`, `hsucc_iter_forced`) are
        the intended ingredients for that final local argument.
        -/
        intro x hw
        obtain ⟨p, q, hp_def, hq_case, hpq_all, hpq_no, hp_root, hp_der_root, hq_eval_ne⟩ :=
          exists_special_pair_of_wronskian_zero hall hno hw
        have hq0 : q ≠ 0 := by
          intro hq0
          exact hq_eval_ne (by simp [hq0])
        have hq_rr : IsRealRooted q := by
          rcases hq_case with ⟨_, rfl⟩ | ⟨_, rfl⟩
          · simpa using hf
          · simpa using hg
        have hp0 : p ≠ 0 := by
          rcases hq_case with ⟨hgx0, hqf⟩ | ⟨hgx_ne, hqg⟩
          · have hfx_ne : f.eval x ≠ 0 := by simpa [hqf] using hq_eval_ne
            rw [hp_def, hgx0]
            simp [hfx_ne, hg.1]
          · intro hp0
            have hlin : C (g.eval x) * f + C (-f.eval x) * g = 0 := by
              simpa [hp_def] using hp0
            by_cases hfx0 : f.eval x = 0
            · have hEq : C (g.eval x) * f = 0 := by
                simpa [hfx0] using hlin
              rcases mul_eq_zero.mp hEq with hC | hf0
              · exact hgx_ne (by simpa using C_eq_zero.mp hC)
              · exact hf.1 hf0
            · by_cases hf_deg_pos : 0 < f.natDegree
              · exact
                  no_nontrivial_linear_relation_of_no_common_root
                    hf hno hf_deg_pos hgx_ne (neg_ne_zero.mpr hfx0) hlin
              · have hfdeg0 : f.natDegree = 0 := Nat.eq_zero_of_not_pos hf_deg_pos
                rcases hdeg with hsucc | hsame
                · have hEq : C (g.eval x) * f = C (f.eval x) * g := by
                    have htmp : C (g.eval x) * f = -(C (-f.eval x) * g) :=
                      eq_neg_of_add_eq_zero_left hlin
                    simpa [neg_mul, C_mul] using htmp
                  have hscalar : f = C (f.eval x / g.eval x) * g := by
                    ext n
                    have hcoeff := congrArg (fun q : ℝ[X] => q.coeff n) hEq
                    simp [coeff_C_mul] at hcoeff ⊢
                    apply (mul_left_cancel₀ hgx_ne)
                    calc
                      g.eval x * f.coeff n = f.eval x * g.coeff n := by
                        simpa [coeff_C_mul] using hcoeff
                      _ = g.eval x * ((f.eval x / g.eval x) * g.coeff n) := by
                            field_simp [hgx_ne]
                  have hdeg_eq : f.natDegree = g.natDegree := by
                    rw [hscalar, natDegree_C_mul (div_ne_zero hfx0 hgx_ne)]
                  omega
                · have hgdeg0 : g.natDegree = 0 := by omega
                  have hmax0' : max f.natDegree g.natDegree = 0 := by
                    simp [hfdeg0, hgdeg0]
                  exact (Nat.ne_of_gt hmax_pos) hmax0'
        have hp_rr : IsRealRooted p := by
          rcases hpq_all 1 0 with hp_zero | hp_rr
          · exact False.elim (hp0 (by simpa using hp_zero))
          · simpa using hp_rr
        have hq_not_root : ¬ q.IsRoot x := by
          simpa [Polynomial.IsRoot.def] using hq_eval_ne
        have hp_mult_gt : 1 < p.rootMultiplicity x := by
          exact (one_lt_rootMultiplicity_iff_isRoot hp0).2 ⟨hp_root, hp_der_root⟩
        have hp_mult_ge2 : 2 ≤ p.rootMultiplicity x := by omega
        /-
        Final local contradiction.

        Instead of regularizing all the way to a simple pair and then passing
        slot data back to the limit, we now only iterate `T_ε` long enough to
        reduce the multiple root of `p` at `x` to an exact double root. For a
        sufficiently small shift parameter `η`, the companion polynomial
        `iterateTDeriv η (m - 2) q` still does not vanish at `x`, while
        `iterateTDeriv η (m - 2) p` has root multiplicity exactly `2` there.

        That exact double-root pair is impossible in an `AllComboRealRooted`
        plane: a small perturbation by the companion violates the standard
        second-derivative inequality for non-roots
        (`deriv2_mul_lt_deriv_sq_at_non_root`). So the original Wronskian-zero
        assumption was impossible.
        -/
        let m : ℕ := p.rootMultiplicity x
        let k : ℕ := m - 2
        obtain ⟨δ, hδ, hqk_not_root⟩ :=
          exists_delta_not_isRoot_iterateTDeriv_at_point k hq_not_root
        let η : ℝ := δ / 2
        have hη_pos : 0 < η := by
          dsimp [η]
          linarith
        have hη_small : ‖η‖ < δ := by
          have hη_norm : ‖η‖ = δ / 2 := by
            rw [Real.norm_eq_abs, show η = δ / 2 by rfl, abs_of_pos hη_pos]
          rw [hη_norm]
          linarith
        have hqk_not_root_x : ¬ (iterateTDeriv η k q).IsRoot x := hqk_not_root hη_small
        have hqk_eval_ne : (iterateTDeriv η k q).eval x ≠ 0 := by
          simpa [Polynomial.IsRoot.def] using hqk_not_root_x
        have hk_le : k ≤ p.rootMultiplicity x := by
          dsimp [k, m]
          omega
        have hpk_mult :
            (iterateTDeriv η k p).rootMultiplicity x = 2 := by
          calc
            (iterateTDeriv η k p).rootMultiplicity x = p.rootMultiplicity x - k := by
              exact rootMultiplicity_iterateTDeriv_eq_tsub hη_pos hp_rr hk_le
            _ = 2 := by
              dsimp [k, m]
              omega
        have hpq_all_k :
            AllComboRealRooted (iterateTDeriv η k p) (iterateTDeriv η k q) :=
          allComboRealRooted_iterateTDeriv hpq_all hη_pos k
        exact
          false_of_allComboRealRooted_of_double_root_and_eval_ne
            hpq_all_k hpk_mult hqk_eval_ne
      exact
        combo_eq_zero_or_realRooted_simple_of_wronskian_eval_ne_zero
          hall hW_ne
  have htransport :
      (f.natDegree + 1 = g.natDegree → Prec f g) ∧
        (f.natDegree = g.natDegree → Prec f g ∨ Prec g f) := by
    constructor
    · intro hsucc
      have hprec_or :
          Prec f g ∨ Prec g f :=
        prec_of_eq_zero_or_simple_combo_of_no_common
          hf hg hcombo_original (Or.inl hsucc) hno
      rcases hprec_or with hfg | hgf
      · exact hfg
      · have hbounds := natDegree_bounds_of_prec_local hgf
        omega
    · intro hsame
      exact
        prec_of_eq_zero_or_simple_combo_of_no_common
          hf hg hcombo_original (Or.inr hsame) hno
  rcases htransport with ⟨hsucc_transport, hsame_transport⟩
  rcases hdeg with hsucc | hsame
  · exact Or.inl (hsucc_transport hsucc)
  · exact hsame_transport hsame

private theorem allComboRealRooted_of_prec_succDegree_pos
    {f g : ℝ[X]}
    (hfg : Prec f g)
    (hdeg : f.natDegree + 1 = g.natDegree)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g) :
    AllComboRealRooted f g := by
  let hfg_inter : Interlaces f g := hfg.toInterlaces hdeg
  intro α β
  by_cases hβ0 : β = 0
  · by_cases hα0 : α = 0
    · left
      simp [hα0, hβ0]
    · right
      have hrr : IsRealRooted (C α * f) := isRealRooted_C_mul hfg.1 hα0
      simpa [hβ0] using hrr
  · rcases lt_or_gt_of_ne hβ0 with hβneg | hβpos
    · by_cases hα_nonpos : α ≤ 0
      · right
        have hrr_neg :
            IsRealRooted (C (-α) * f + C (-β) * g) :=
          isRealRooted_nonneg_combo_of_prec
            hfg hf_pos hg_pos
            (by linarith) (by linarith) (Or.inr (by linarith))
        have hrr :
            IsRealRooted
              (C (-1 : ℝ) * (C (-α) * f + C (-β) * g)) :=
          isRealRooted_C_mul hrr_neg (by norm_num : (-1 : ℝ) ≠ 0)
        have hEq :
            C (-1 : ℝ) * (C (-α) * f + C (-β) * g) =
              C α * f + C β * g := by
          ext i
          simp [Polynomial.coeff_add, Polynomial.coeff_C_mul]
          ring_nf
        simpa [hEq, add_comm, add_left_comm, add_assoc] using hrr
      · have hαpos : 0 < α := lt_of_not_ge hα_nonpos
        right
        have hmix_pos : HasPosLeadingCoeff (C (-β) * g + C (-α) * f) := by
          have hdeg_scaled :
              (C (-α) * f).natDegree < (C (-β) * g).natDegree := by
            rw [natDegree_C_mul (show -α ≠ 0 by linarith),
              natDegree_C_mul (show -β ≠ 0 by linarith)]
            omega
          exact
            hasPosLeadingCoeff_add_of_natDegree_lt_left
              hdeg_scaled
              (hasPosLeadingCoeff_C_mul (by linarith) hg_pos)
        have hmix_deg :
            (C (-β) * g + C (-α) * f).natDegree = g.natDegree := by
          have hdeg_scaled :
              (C (-α) * f).natDegree < (C (-β) * g).natDegree := by
            rw [natDegree_C_mul (show -α ≠ 0 by linarith),
              natDegree_C_mul (show -β ≠ 0 by linarith)]
            omega
          calc
            (C (-β) * g + C (-α) * f).natDegree = (C (-β) * g).natDegree := by
              exact natDegree_add_eq_left_of_natDegree_lt_of_posLeadingCoeff hdeg_scaled
                (hasPosLeadingCoeff_C_mul (by linarith) hg_pos)
            _ = g.natDegree := by rw [natDegree_C_mul (by linarith : (-β) ≠ 0)]
        have hrr_neg :
            IsRealRooted (C (-β) * g + C (-α) * f) := by
          have hmix_lo : g.natDegree ≤ (C (-β) * g + C (-α) * f).natDegree := by
            rw [hmix_deg]
          have hmix_hi : (C (-β) * g + C (-α) * f).natDegree ≤ g.natDegree + 1 := by
            rw [hmix_deg]
            omega
          have hprec_mix :
              Prec g (C (-β) * g + C (-α) * f) :=
            prec_of_interlaces_evalCoeff_nonpos
              (f := g) (g := f) (a := C (-β)) (b := C (-α))
              hfg_inter hf_pos hmix_pos
              hmix_lo hmix_hi
              (by
                intro r _
                simp
                linarith)
          exact hprec_mix.2.1
        have hrr :
            IsRealRooted
              (C (-1 : ℝ) * (C (-β) * g + C (-α) * f)) :=
          isRealRooted_C_mul hrr_neg (by norm_num : (-1 : ℝ) ≠ 0)
        have hEq :
            C (-1 : ℝ) * (C (-β) * g + C (-α) * f) =
              C α * f + C β * g := by
          ext i
          simp [Polynomial.coeff_add, Polynomial.coeff_C_mul]
        simpa [hEq, add_comm] using hrr
    · by_cases hα_nonneg : 0 ≤ α
      · right
        by_cases hα0 : α = 0
        · have hrr : IsRealRooted (C β * g) := isRealRooted_C_mul hfg.2.1 hβ0
          simpa [hα0, add_comm] using hrr
        · exact
            isRealRooted_nonneg_combo_of_prec
              hfg hf_pos hg_pos hα_nonneg (le_of_lt hβpos)
              (Or.inr hβpos)
      · have hαneg : α < 0 := lt_of_not_ge hα_nonneg
        right
        have hmix_pos : HasPosLeadingCoeff (C β * g + C α * f) := by
          have hdeg_scaled :
              (C α * f).natDegree < (C β * g).natDegree := by
            rw [natDegree_C_mul (show α ≠ 0 by linarith), natDegree_C_mul hβ0]
            omega
          exact
            hasPosLeadingCoeff_add_of_natDegree_lt_left
              hdeg_scaled
              (hasPosLeadingCoeff_C_mul hβpos hg_pos)
        have hmix_deg :
            (C β * g + C α * f).natDegree = g.natDegree := by
          have hdeg_scaled :
              (C α * f).natDegree < (C β * g).natDegree := by
            rw [natDegree_C_mul (show α ≠ 0 by linarith), natDegree_C_mul hβ0]
            omega
          calc
            (C β * g + C α * f).natDegree = (C β * g).natDegree := by
              exact natDegree_add_eq_left_of_natDegree_lt_of_posLeadingCoeff hdeg_scaled
                (hasPosLeadingCoeff_C_mul hβpos hg_pos)
            _ = g.natDegree := by rw [natDegree_C_mul hβ0]
        have hmix_lo : g.natDegree ≤ (C β * g + C α * f).natDegree := by
          rw [hmix_deg]
        have hmix_hi : (C β * g + C α * f).natDegree ≤ g.natDegree + 1 := by
          rw [hmix_deg]
          omega
        have hprec_mix :
            Prec g (C β * g + C α * f) :=
          prec_of_interlaces_evalCoeff_nonpos
            (f := g) (g := f) (a := C β) (b := C α)
            hfg_inter hf_pos hmix_pos
            hmix_lo hmix_hi
            (by
              intro r _
              simp
              linarith)
        simpa [add_comm, add_left_comm, add_assoc] using hprec_mix.2.1

private theorem allComboRealRooted_of_prec_succDegree
    {f g : ℝ[X]}
    (hfg : Prec f g)
    (hdeg : f.natDegree + 1 = g.natDegree) :
    AllComboRealRooted f g := by
  have hf : IsRealRooted f := hfg.1
  have hg : IsRealRooted g := hfg.2.1
  have hf_lc_ne : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf.1
  have hg_lc_ne : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hg.1
  let sf : ℝ := if 0 < f.leadingCoeff then 1 else -1
  let sg : ℝ := if 0 < g.leadingCoeff then 1 else -1
  have hsf_ne : sf ≠ 0 := by
    dsimp [sf]
    split_ifs <;> norm_num
  have hsg_ne : sg ≠ 0 := by
    dsimp [sg]
    split_ifs <;> norm_num
  have hsf_sq : sf * sf = 1 := by
    dsimp [sf]
    split_ifs <;> norm_num
  have hsg_sq : sg * sg = 1 := by
    dsimp [sg]
    split_ifs <;> norm_num
  have hsf_pos : 0 < sf * f.leadingCoeff := by
    dsimp [sf]
    split_ifs with hpos
    · nlinarith
    · have hneg : f.leadingCoeff < 0 := by
        exact lt_of_le_of_ne (le_of_not_gt hpos) hf_lc_ne
      nlinarith
  have hsg_pos : 0 < sg * g.leadingCoeff := by
    dsimp [sg]
    split_ifs with hpos
    · nlinarith
    · have hneg : g.leadingCoeff < 0 := by
        exact lt_of_le_of_ne (le_of_not_gt hpos) hg_lc_ne
      nlinarith
  let f₀ : ℝ[X] := C sf * f
  let g₀ : ℝ[X] := C sg * g
  have hfg₀ : Prec f₀ g₀ := prec_C_mul_right (prec_C_mul_left hfg hsf_ne) hsg_ne
  have hdeg₀ : f₀.natDegree + 1 = g₀.natDegree := by
    simpa [f₀, g₀, natDegree_C_mul hsf_ne, natDegree_C_mul hsg_ne] using hdeg
  have hf₀_pos : HasPosLeadingCoeff f₀ := by
    unfold HasPosLeadingCoeff f₀
    rw [leadingCoeff_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr hsf_ne) f]
    simpa [sf] using hsf_pos
  have hg₀_pos : HasPosLeadingCoeff g₀ := by
    unfold HasPosLeadingCoeff g₀
    rw [leadingCoeff_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr hsg_ne) g]
    simpa [sg] using hsg_pos
  have hall₀ : AllComboRealRooted f₀ g₀ :=
    allComboRealRooted_of_prec_succDegree_pos hfg₀ hdeg₀ hf₀_pos hg₀_pos
  intro α β
  have hEq_f : C α * C sf * (C sf * f) = C α * f := by
    calc
      C α * C sf * (C sf * f) = C α * ((C sf * C sf) * f) := by
        simp [mul_assoc]
      _ = C α * (C (sf * sf) * f) := by rw [C_mul]
      _ = C α * (C 1 * f) := by rw [hsf_sq]
      _ = C α * f := by simp
  have hEq_g : C β * C sg * (C sg * g) = C β * g := by
    calc
      C β * C sg * (C sg * g) = C β * ((C sg * C sg) * g) := by
        simp [mul_assoc]
      _ = C β * (C (sg * sg) * g) := by rw [C_mul]
      _ = C β * (C 1 * g) := by rw [hsg_sq]
      _ = C β * g := by simp
  simpa [f₀, g₀, mul_assoc, hEq_f, hEq_g] using hall₀ (α * sf) (β * sg)

/-- To prove the same-degree forward direction of Obreschkoff, it is enough to
handle the no-common-roots case. Shared roots can be factored out recursively,
and `AllComboRealRooted` is rebuilt using
`allComboRealRooted_mul_common_factor`. This mirrors the converse reduction but
keeps the orientation fixed. -/
private theorem allComboRealRooted_of_prec_sameDegree_of_no_common
    (hstep :
      ∀ {f g : ℝ[X]},
        Prec f g →
        f.natDegree = g.natDegree →
        (∀ r, f.IsRoot r → ¬ g.IsRoot r) →
        AllComboRealRooted f g)
    {f g : ℝ[X]}
    (hfg : Prec f g)
    (hdeg : f.natDegree = g.natDegree) :
    AllComboRealRooted f g := by
  refine
    Nat.strong_induction_on
      (p := fun n =>
        ∀ {f g : ℝ[X]},
          f.natDegree = n →
          Prec f g →
          f.natDegree = g.natDegree →
          AllComboRealRooted f g)
      f.natDegree ?_ rfl hfg hdeg
  intro n ih f g hfdeg hfg hdeg
  by_cases hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r
  · exact hstep hfg hdeg hno
  · push_neg at hno
    rcases hno with ⟨r, hrf, hrg⟩
    obtain ⟨qf, hqf⟩ := dvd_iff_isRoot.mpr hrf
    obtain ⟨qg, hqg⟩ := dvd_iff_isRoot.mpr hrg
    have hqf_ne : qf ≠ 0 := by
      exact right_ne_zero_of_mul (by simpa [hqf] using hfg.1.1)
    have hqg_ne : qg ≠ 0 := by
      exact right_ne_zero_of_mul (by simpa [hqg] using hfg.2.1.1)
    have hqdeg : qf.natDegree = qg.natDegree := by
      rw [hqf, natDegree_mul (X_sub_C_ne_zero r) hqf_ne, natDegree_X_sub_C,
        hqg, natDegree_mul (X_sub_C_ne_zero r) hqg_ne, natDegree_X_sub_C] at hdeg
      omega
    have hqf_deg_lt : qf.natDegree < n := by
      rw [← hfdeg, hqf, natDegree_mul (X_sub_C_ne_zero r) hqf_ne, natDegree_X_sub_C]
      omega
    have hprec_q : Prec qf qg := by
      apply prec_of_prec_mul_X_sub_C_both r
      simpa [hqf, hqg] using hfg
    have hqhall : AllComboRealRooted qf qg :=
      ih qf.natDegree hqf_deg_lt rfl hprec_q hqdeg
    have hmul :
        AllComboRealRooted ((X - C r) * qf) ((X - C r) * qg) :=
      allComboRealRooted_mul_common_factor (isRealRooted_X_sub_C r) hqhall
    simpa [hqf, hqg] using hmul

/-- In the same-degree `Prec` case, removing a rightmost root of `g` turns the
quotient into an honest differ-by-1 interlacer for `f`.

This packages the root-list combinatorics behind the hard equal-degree forward
branch: after peeling off the outer `g`-root, one can work with a genuine
`Interlaces` hypothesis rather than a raw same-degree `Prec` witness. -/
private lemma interlaces_of_prec_sameDegree_rightmost_factor
    {f g q : ℝ[X]} {uR : ℝ}
    (hfg : Prec f g)
    (hdeg : f.natDegree = g.natDegree)
    (hright : ∀ r ∈ g.roots, r ≤ uR)
    (hgq : g = (X - C uR) * q) :
    Interlaces q f := by
  obtain ⟨hf, hg, ss, rs, hss_sorted, hrs_sorted, hss_eq, hrs_eq, hshape⟩ := hfg
  have hss_len : ss.length = f.natDegree := by
    rw [← Multiset.coe_card, hss_eq, hf.2]
  have hrs_len : rs.length = g.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, hg.2]
  have hq_ne : q ≠ 0 := by
    exact right_ne_zero_of_mul (by simpa [hgq] using hg.1)
  have hq : IsRealRooted q := by
    apply isRealRooted_of_dvd hg hq_ne
    exact ⟨X - C uR, by simpa [hgq, mul_comm]⟩
  have hq_deg_g : q.natDegree + 1 = g.natDegree := by
    rw [hgq, natDegree_mul (X_sub_C_ne_zero uR) hq_ne, natDegree_X_sub_C]
    omega
  have hq_deg : q.natDegree + 1 = f.natDegree := by
    omega
  rcases hshape with ⟨hlen, _hint⟩ | ⟨_hlen, halt⟩
  · exfalso
    omega
  · let qs := q.roots.sort (· ≤ ·)
    have hqs_eq : (↑qs : Multiset ℝ) = q.roots := Multiset.sort_eq ..
    have hqs_sorted : qs.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
    have hqs_len : qs.length = q.natDegree := by
      rw [show qs = q.roots.sort (· ≤ ·) by rfl, Multiset.length_sort, hq.2]
    have hqs_le_uR : ∀ r ∈ qs, r ≤ uR := by
      intro r hr
      exact hright r (by
        rw [hgq, roots_mul (mul_ne_zero (X_sub_C_ne_zero uR) hq_ne), roots_X_sub_C]
        apply Multiset.mem_add.mpr
        right
        rw [← hqs_eq]
        exact Multiset.mem_coe.mpr hr)
    have hqs_sorted_right : (qs ++ [uR]).Pairwise (· ≤ ·) := by
      rw [List.pairwise_append]
      refine ⟨hqs_sorted, List.pairwise_singleton _ _, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst hb
      exact hqs_le_uR a ha
    have hrs_eq_right : rs = qs ++ [uR] := by
      apply List.Perm.eq_of_pairwise' hrs_sorted hqs_sorted_right
      apply Multiset.coe_eq_coe.mp
      calc
        (↑rs : Multiset ℝ) = g.roots := hrs_eq
        _ = ({uR} : Multiset ℝ) + q.roots := by
              rw [hgq, roots_mul (mul_ne_zero (X_sub_C_ne_zero uR) hq_ne), roots_X_sub_C]
        _ = q.roots + ({uR} : Multiset ℝ) := by rw [add_comm]
        _ = q.roots + ↑[uR] := by simp
        _ = (↑qs : Multiset ℝ) + ↑[uR] := by rw [hqs_eq]
        _ = (↑(qs ++ [uR]) : Multiset ℝ) := by rw [Multiset.coe_add]
    have hlen_qs : qs.length + 1 = ss.length := by
      rw [hqs_len, hss_len]
      omega
    have hint_qs : ListInterlaces qs ss := by
      have halt_right : ListAlternates ss (qs ++ [uR]) := by
        simpa [hrs_eq_right] using halt
      exact listInterlaces_of_listAlternates_append_right hlen_qs halt_right
    exact ⟨hf, hq, hq_deg, ss, qs, hss_sorted, hqs_sorted, hss_eq, hqs_eq, hint_qs⟩

private lemma no_common_with_right_factor_quotient
    {f q : ℝ[X]} {uR : ℝ}
    (hno : ∀ r, f.IsRoot r → ¬ ((X - C uR) * q).IsRoot r) :
    ∀ r, f.IsRoot r → ¬ q.IsRoot r := by
  intro r hr hq
  apply hno r hr
  rw [Polynomial.IsRoot.def, eval_mul]
  have hq_eval : q.eval r = 0 := by
    simpa [Polynomial.IsRoot.def] using hq
  rw [hq_eval]
  simp

private lemma root_lt_rightmost_of_prec_sameDegree_no_common
    {f g : ℝ[X]} {uR : ℝ}
    (hfg : Prec f g)
    (huR_root : g.IsRoot uR)
    (huR_max : ∀ r ∈ g.roots, r ≤ uR)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    ∀ r, f.IsRoot r → r < uR := by
  intro r hr
  have hr_le : r ≤ uR := roots_le_of_prec_right_local hfg huR_max r <| by
    exact (mem_roots hfg.1.1).mpr hr
  have hr_ne : r ≠ uR := by
    intro hEq
    exact hno r hr (hEq ▸ huR_root)
  exact lt_of_le_of_ne hr_le hr_ne

private lemma hasPosLeadingCoeff_of_right_factor
    {q : ℝ[X]} {uR : ℝ}
    (h : HasPosLeadingCoeff ((X - C uR) * q)) :
    HasPosLeadingCoeff q := by
  unfold HasPosLeadingCoeff at h ⊢
  simpa [Polynomial.leadingCoeff_mul, leadingCoeff_X_sub_C] using h

private lemma prec_of_right_factor_combo_of_natDegree_ge
    {f q : ℝ[X]} {uR α β : ℝ}
    (hqf : Interlaces q f)
    (hq_pos : HasPosLeadingCoeff q)
    (hF_pos : HasPosLeadingCoeff (C α * f + C β * ((X - C uR) * q)))
    (hdeg_lo : f.natDegree ≤ (C α * f + C β * ((X - C uR) * q)).natDegree)
    (hq_no : ∀ r, f.IsRoot r → ¬ q.IsRoot r)
    (hroot_lt : ∀ r, f.IsRoot r → r < uR)
    (hβ : 0 < β) :
    Prec f (C α * f + C β * ((X - C uR) * q)) := by
  have hq_ne : q ≠ 0 := hqf.2.1.1
  have hbeta_term_eq :
      C β * ((X - C uR) * q) = (C β * (X - C uR)) * q := by
    rw [mul_assoc]
  have hdeg_hi :
      (C α * f + C β * ((X - C uR) * q)).natDegree ≤ f.natDegree + 1 := by
    have hsum_le :
        (C α * f + (C β * (X - C uR)) * q).natDegree ≤
          max (C α * f).natDegree (((C β * (X - C uR)) * q).natDegree) :=
      natDegree_add_le _ _
    have hscaled_le : (C α * f).natDegree ≤ f.natDegree := natDegree_C_mul_le α f
    have hbeta_term_deg : ((C β * (X - C uR)) * q).natDegree = f.natDegree := by
      rw [natDegree_mul
          (show C β * (X - C uR) ≠ 0 by
            exact mul_ne_zero (C_ne_zero.mpr hβ.ne') (X_sub_C_ne_zero uR))
          hq_ne]
      rw [natDegree_mul (C_ne_zero.mpr hβ.ne') (X_sub_C_ne_zero uR),
        natDegree_C, natDegree_X_sub_C]
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hqf.2.2.1
    rw [hbeta_term_eq]
    exact (le_trans hsum_le (max_le hscaled_le (le_of_eq hbeta_term_deg))).trans <| by omega
  have hb_neg : ∀ r, f.IsRoot r → (C β * (X - C uR)).eval r < 0 := by
    intro r hr
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
    have hru : r - uR < 0 := sub_neg.mpr (hroot_lt r hr)
    nlinarith
  have hF_pos' : HasPosLeadingCoeff (C α * f + (C β * (X - C uR)) * q) := by
    simpa [hbeta_term_eq] using hF_pos
  have hdeg_lo' : f.natDegree ≤ (C α * f + (C β * (X - C uR)) * q).natDegree := by
    simpa [hbeta_term_eq] using hdeg_lo
  have hprec :
      Prec f (C α * f + (C β * (X - C uR)) * q) :=
    prec_of_interlaces_evalCoeff_neg
      (f := f) (g := q) (a := C α) (b := C β * (X - C uR))
      hqf hq_pos hF_pos' hdeg_lo' (by simpa [hbeta_term_eq] using hdeg_hi) hq_no hb_neg
  simpa [hbeta_term_eq] using hprec

/-- A nonzero combination `α f + β (X - uR) q` with `β > 0` is real-rooted in
the same-degree/no-common-roots regime. This is the core right-factor reduction
used in the forward equal-degree Obreschkoff proof: depending on whether the
top coefficient cancels, the combination either becomes the left interlacer of
`f` or stays same-degree and is forced to be real-rooted by strict sign changes
plus one outer root. -/
private theorem isRealRooted_of_right_factor_combo_posβ
    {f q : ℝ[X]} {uR α β : ℝ}
    (hqf : Interlaces q f)
    (hq_pos : HasPosLeadingCoeff q)
    (hq_no : ∀ r, f.IsRoot r → ¬ q.IsRoot r)
    (hroot_lt : ∀ r, f.IsRoot r → r < uR)
    (hβ : 0 < β)
    (hF_ne : C α * f + C β * ((X - C uR) * q) ≠ 0)
    (hdeg_pos : 1 ≤ f.natDegree) :
    IsRealRooted (C α * f + C β * ((X - C uR) * q)) := by
  let F : ℝ[X] := C α * f + C β * ((X - C uR) * q)
  have hf : IsRealRooted f := hqf.1
  have hq : IsRealRooted q := hqf.2.1
  have hF_ne' : F ≠ 0 := by simpa [F] using hF_ne
  have hdeg_le : F.natDegree ≤ f.natDegree := by
    have hsum_le :
        F.natDegree ≤ max (C α * f).natDegree (C β * ((X - C uR) * q)).natDegree := by
      simpa [F] using natDegree_add_le (C α * f) (C β * ((X - C uR) * q))
    have hleft_le : (C α * f).natDegree ≤ f.natDegree := natDegree_C_mul_le α f
    have hright_eq : (C β * ((X - C uR) * q)).natDegree = f.natDegree := by
      rw [natDegree_C_mul hβ.ne', natDegree_mul (X_sub_C_ne_zero uR) hq.1, natDegree_X_sub_C]
      simpa [Nat.add_comm] using hqf.2.2.1
    exact (le_trans hsum_le (max_le hleft_le (le_of_eq hright_eq)))
  have hroot_sign :
      ∀ r, f.IsRoot r → F.eval r * q.eval r < 0 := by
    intro r hr
    have hf_eval : f.eval r = 0 := by
      simpa [Polynomial.IsRoot.def] using hr
    have hq_eval_ne : q.eval r ≠ 0 := by
      intro hq_eval
      exact hq_no r hr (by simpa [Polynomial.IsRoot.def] using hq_eval)
    have hru : r - uR < 0 := sub_neg.mpr (hroot_lt r hr)
    have hsq : 0 < (q.eval r) ^ 2 := sq_pos_iff.mpr hq_eval_ne
    have hcalc : F.eval r * q.eval r = β * (r - uR) * (q.eval r) ^ 2 := by
      dsimp [F]
      rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, hf_eval,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C]
      ring
    have hprod_neg : β * (r - uR) * (q.eval r) ^ 2 < 0 := by
      exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hβ hru) hsq
    exact hcalc ▸ hprod_neg
  have hsign_core :
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        f.roots.sort (· ≤ ·) = pre ++ r₁ :: r₂ :: rest →
        F.eval r₁ * F.eval r₂ < 0 := by
    intro pre r₁ r₂ rest hEq
    have hrs_eq : (↑(f.roots.sort (· ≤ ·)) : Multiset ℝ) = f.roots := Multiset.sort_eq ..
    have hr₁_root : f.IsRoot r₁ := by
      apply (mem_roots hf.1).mp
      rw [← hrs_eq]
      exact Multiset.mem_coe.mpr (by rw [hEq]; simp)
    have hr₂_root : f.IsRoot r₂ := by
      apply (mem_roots hf.1).mp
      rw [← hrs_eq]
      exact Multiset.mem_coe.mpr (by rw [hEq]; simp)
    have hFq₁ : F.eval r₁ * q.eval r₁ < 0 := hroot_sign r₁ hr₁_root
    have hFq₂ : F.eval r₂ * q.eval r₂ < 0 := hroot_sign r₂ hr₂_root
    have hqq : q.eval r₁ * q.eval r₂ < 0 :=
      eval_mul_eval_neg_of_interlaces_consecutive_of_no_common hqf hq_no pre hEq
    exact mul_neg_of_mul_neg_of_mul_neg_local hFq₁ hFq₂ hqq
  have hsign :
      let rs := f.roots.sort (· ≤ ·)
      ∀ (pre : List ℝ) {r₁ r₂ : ℝ} {rest : List ℝ},
        rs = pre ++ r₁ :: r₂ :: rest →
        F.eval r₁ * F.eval r₂ < 0 := by
    simpa using hsign_core
  by_cases hdeg_lt : F.natDegree < f.natDegree
  · exact (interlaces_of_consecutive_signs_of_natDegree_lt hf hF_ne' hdeg_lt hsign).2.1
  · have hdeg_eq : F.natDegree = f.natDegree := by omega
    by_cases hdeg_one : f.natDegree = 1
    · have hF_deg_one : F.natDegree = 1 := by omega
      exact isRealRooted_of_degree_one hF_deg_one
    · have hdeg_two : 2 ≤ f.natDegree := by omega
      exact
        isRealRooted_of_interlaces_eval_mul_neg_same_any_lc
          hqf hq_pos hdeg_eq hdeg_two hroot_sign

/-- Positive-leading, no-common-roots equal-degree forward Obreschkoff. This is
the honest same-degree core: same-sign combinations are covered by Wagner
addition, while opposite-sign combinations are routed through the rightmost
root factorization `g = (X - C uR) * qg` and the helper
`isRealRooted_of_right_factor_combo_posβ`. -/
private theorem allComboRealRooted_of_prec_sameDegree_pos_of_no_common
    {f g : ℝ[X]}
    (hfg : Prec f g)
    (hdeg : f.natDegree = g.natDegree)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    AllComboRealRooted f g := by
  have hf : IsRealRooted f := hfg.1
  have hg : IsRealRooted g := hfg.2.1
  by_cases hdeg0 : f.natDegree = 0
  · intro α β
    by_cases hcomb : C α * f + C β * g = 0
    · exact Or.inl hcomb
    · have hgdeg0 : g.natDegree = 0 := by omega
      have hfC : f = C (f.coeff 0) := eq_C_of_natDegree_eq_zero hdeg0
      have hgC : g = C (g.coeff 0) := eq_C_of_natDegree_eq_zero hgdeg0
      rw [hfC, hgC] at hcomb ⊢
      have hsum_eq :
          C α * C (f.coeff 0) + C β * C (g.coeff 0) =
            C (α * f.coeff 0 + β * g.coeff 0) := by
        calc
          C α * C (f.coeff 0) + C β * C (g.coeff 0)
              = C (α * f.coeff 0) + C (β * g.coeff 0) := by simp [C_mul]
          _ = C (α * f.coeff 0 + β * g.coeff 0) := by rw [← C_add]
      right
      refine ⟨hcomb, ?_⟩
      have hroots_eq :
          (C α * C (f.coeff 0) + C β * C (g.coeff 0)).roots =
            (C (α * f.coeff 0 + β * g.coeff 0)).roots := by
        exact congrArg roots hsum_eq
      have hnat_eq :
          (C α * C (f.coeff 0) + C β * C (g.coeff 0)).natDegree =
            (C (α * f.coeff 0 + β * g.coeff 0)).natDegree := by
        exact congrArg natDegree hsum_eq
      rw [hroots_eq, hnat_eq, roots_C, natDegree_C]
      simp
  have hdeg_pos : 1 ≤ f.natDegree := by omega
  obtain ⟨uR, huR_root, huR_max⟩ :=
    exists_rightmost_root_of_isRealRooted hg (by rw [← hdeg]; exact hdeg_pos)
  obtain ⟨qg, hqg⟩ := dvd_iff_isRoot.mpr huR_root
  have hqg_inter : Interlaces qg f :=
    interlaces_of_prec_sameDegree_rightmost_factor hfg hdeg huR_max hqg
  have hqg_no : ∀ r, f.IsRoot r → ¬ qg.IsRoot r := by
    apply no_common_with_right_factor_quotient
    simpa [hqg] using hno
  have hroot_lt : ∀ r, f.IsRoot r → r < uR := by
    exact root_lt_rightmost_of_prec_sameDegree_no_common hfg huR_root huR_max hno
  have hqg_pos : HasPosLeadingCoeff qg := by
    apply hasPosLeadingCoeff_of_right_factor
    simpa [hqg] using hg_pos
  intro α β
  by_cases hcomb : C α * f + C β * g = 0
  · exact Or.inl hcomb
  · right
    by_cases hβ0 : β = 0
    · have hα0 : α ≠ 0 := by
        intro hα0
        apply hcomb
        simp [hα0, hβ0]
      have hrr : IsRealRooted (C α * f) := isRealRooted_C_mul hf hα0
      simpa [hβ0] using hrr
    · rcases lt_or_gt_of_ne hβ0 with hβneg | hβpos
      · by_cases hα_nonpos : α ≤ 0
        · have hrr_neg :
            IsRealRooted (C (-α) * f + C (-β) * g) :=
          isRealRooted_nonneg_combo_of_prec
            hfg hf_pos hg_pos (by linarith) (by linarith) (Or.inr (by linarith))
          have hrr :
              IsRealRooted
                (C (-1 : ℝ) * (C (-α) * f + C (-β) * g)) :=
            isRealRooted_C_mul hrr_neg (by norm_num : (-1 : ℝ) ≠ 0)
          have hEq :
              C (-1 : ℝ) * (C (-α) * f + C (-β) * g) =
                C α * f + C β * g := by
            ext i
            simp [Polynomial.coeff_add, Polynomial.coeff_C_mul]
            ring_nf
          simpa [hEq, add_comm, add_left_comm, add_assoc] using hrr
        · have hαpos : 0 < α := lt_of_not_ge hα_nonpos
          have hcomb_neg : C (-α) * f + C (-β) * g ≠ 0 := by
            intro h0
            apply hcomb
            have hEq :
                C (-1 : ℝ) * (C (-α) * f + C (-β) * g) =
                  C α * f + C β * g := by
              ext i
              simp [Polynomial.coeff_add, Polynomial.coeff_C_mul]
              ring_nf
            rw [← hEq, h0]
            simp
          have hrr_neg :
              IsRealRooted (C (-α) * f + C (-β) * g) := by
            simpa [hqg] using
              isRealRooted_of_right_factor_combo_posβ
                (f := f) (q := qg) (uR := uR) (α := -α) (β := -β)
                hqg_inter hqg_pos hqg_no hroot_lt (by linarith) (by simpa [hqg] using hcomb_neg)
                hdeg_pos
          have hrr :
              IsRealRooted
                (C (-1 : ℝ) * (C (-α) * f + C (-β) * g)) :=
            isRealRooted_C_mul hrr_neg (by norm_num : (-1 : ℝ) ≠ 0)
          have hEq :
              C (-1 : ℝ) * (C (-α) * f + C (-β) * g) =
                C α * f + C β * g := by
            ext i
            simp [Polynomial.coeff_add, Polynomial.coeff_C_mul]
            ring_nf
          simpa [hEq, add_comm, add_left_comm, add_assoc] using hrr
      · by_cases hα_nonneg : 0 ≤ α
        · exact
            isRealRooted_nonneg_combo_of_prec
              hfg hf_pos hg_pos hα_nonneg (le_of_lt hβpos)
              (Or.inr hβpos)
        · have hαneg : α < 0 := lt_of_not_ge hα_nonneg
          simpa [hqg] using
            isRealRooted_of_right_factor_combo_posβ
              (f := f) (q := qg) (uR := uR) (α := α) (β := β)
              hqg_inter hqg_pos hqg_no hroot_lt hβpos (by simpa [hqg] using hcomb) hdeg_pos

/-- Opposite-sign right-factor combinations are real-rooted even when the top
coefficient does not have the sign needed to orient a `Prec` witness directly.
The proof splits into the genuine degree-drop case, where the combination
becomes a left interlacer of `f`, and the same-degree case, where strict sign
changes plus one outer root are enough to force real-rootedness. -/
private theorem allComboRealRooted_of_prec_sameDegree
    {f g : ℝ[X]}
    (hfg : Prec f g)
    (hdeg : f.natDegree = g.natDegree) :
    AllComboRealRooted f g := by
  refine allComboRealRooted_of_prec_sameDegree_of_no_common ?_ hfg hdeg
  intro f g hfg hdeg hno
  have hf : IsRealRooted f := hfg.1
  have hg : IsRealRooted g := hfg.2.1
  have hf_lc_ne : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf.1
  have hg_lc_ne : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hg.1
  let sf : ℝ := if 0 < f.leadingCoeff then 1 else -1
  let sg : ℝ := if 0 < g.leadingCoeff then 1 else -1
  have hsf_ne : sf ≠ 0 := by
    dsimp [sf]
    split_ifs <;> norm_num
  have hsg_ne : sg ≠ 0 := by
    dsimp [sg]
    split_ifs <;> norm_num
  have hsf_sq : sf * sf = 1 := by
    dsimp [sf]
    split_ifs <;> norm_num
  have hsg_sq : sg * sg = 1 := by
    dsimp [sg]
    split_ifs <;> norm_num
  have hsf_pos : 0 < sf * f.leadingCoeff := by
    dsimp [sf]
    split_ifs with hpos
    · nlinarith
    · have hneg : f.leadingCoeff < 0 := by
        exact lt_of_le_of_ne (le_of_not_gt hpos) hf_lc_ne
      nlinarith
  have hsg_pos : 0 < sg * g.leadingCoeff := by
    dsimp [sg]
    split_ifs with hpos
    · nlinarith
    · have hneg : g.leadingCoeff < 0 := by
        exact lt_of_le_of_ne (le_of_not_gt hpos) hg_lc_ne
      nlinarith
  let f₀ : ℝ[X] := C sf * f
  let g₀ : ℝ[X] := C sg * g
  have hfg₀ : Prec f₀ g₀ := prec_C_mul_right (prec_C_mul_left hfg hsf_ne) hsg_ne
  have hdeg₀ : f₀.natDegree = g₀.natDegree := by
    simpa [f₀, g₀, natDegree_C_mul hsf_ne, natDegree_C_mul hsg_ne] using hdeg
  have hf₀_pos : HasPosLeadingCoeff f₀ := by
    unfold HasPosLeadingCoeff f₀
    rw [leadingCoeff_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr hsf_ne) f]
    simpa [sf] using hsf_pos
  have hg₀_pos : HasPosLeadingCoeff g₀ := by
    unfold HasPosLeadingCoeff g₀
    rw [leadingCoeff_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr hsg_ne) g]
    simpa [sg] using hsg_pos
  have hno₀ : ∀ r, f₀.IsRoot r → ¬ g₀.IsRoot r := by
    intro r hrf₀ hrg₀
    have hrf : f.IsRoot r := by
      have hrf₀_eval : (C sf * f).eval r = 0 := by
        simpa [f₀, Polynomial.IsRoot.def] using hrf₀
      rw [eval_mul, eval_C] at hrf₀_eval
      have : f.eval r = 0 := (mul_eq_zero.mp hrf₀_eval).resolve_left hsf_ne
      simpa [Polynomial.IsRoot.def] using this
    have hrg : g.IsRoot r := by
      have hrg₀_eval : (C sg * g).eval r = 0 := by
        simpa [g₀, Polynomial.IsRoot.def] using hrg₀
      rw [eval_mul, eval_C] at hrg₀_eval
      have : g.eval r = 0 := (mul_eq_zero.mp hrg₀_eval).resolve_left hsg_ne
      simpa [Polynomial.IsRoot.def] using this
    exact hno r hrf hrg
  have hall₀ : AllComboRealRooted f₀ g₀ :=
    allComboRealRooted_of_prec_sameDegree_pos_of_no_common hfg₀ hdeg₀ hf₀_pos hg₀_pos hno₀
  intro α β
  have hEq_f : C α * C sf * (C sf * f) = C α * f := by
    calc
      C α * C sf * (C sf * f) = C α * ((C sf * C sf) * f) := by
        simp [mul_assoc]
      _ = C α * (C (sf * sf) * f) := by rw [C_mul]
      _ = C α * (C 1 * f) := by rw [hsf_sq]
      _ = C α * f := by simp
  have hEq_g : C β * C sg * (C sg * g) = C β * g := by
    calc
      C β * C sg * (C sg * g) = C β * ((C sg * C sg) * g) := by
        simp [mul_assoc]
      _ = C β * (C (sg * sg) * g) := by rw [C_mul]
      _ = C β * (C 1 * g) := by rw [hsg_sq]
      _ = C β * g := by simp
  simpa [f₀, g₀, mul_assoc, hEq_f, hEq_g] using hall₀ (α * sf) (β * sg)

/-- Forward direction of Obreschkoff: if `f ≪ g` then all real combinations
`αf + βg` are real-rooted (or zero). Follows from Wagner addition. -/
theorem allComboRealRooted_of_prec {f g : ℝ[X]}
    (hfg : Prec f g) :
    AllComboRealRooted f g := by
  have hdeg_bounds := natDegree_bounds_of_prec_local hfg
  have hdeg :
      f.natDegree + 1 = g.natDegree ∨ f.natDegree = g.natDegree := by
    omega
  rcases hdeg with hsucc | hsame
  · exact allComboRealRooted_of_prec_succDegree hfg hsucc
  · exact allComboRealRooted_of_prec_sameDegree hfg hsame


end
end RealRooted
