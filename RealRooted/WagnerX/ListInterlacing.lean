import RealRooted.Basic
import RealRooted.Linear
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Algebra.Polynomial

/-!
# Wagner-X list interlacing

Legacy root-list interlacing algebra used by Wagner's polynomial transports.
-/

open Polynomial Filter

noncomputable section

namespace RealRooted

/-! ## List-level lemmas for interlacing -/

/-- Every element of `ss` is `≥` the first element of `rs` in a ListInterlaces. -/
lemma listInterlaces_all_ge :
    ∀ (ss rs : List ℝ) (r : ℝ),
    ListInterlaces ss (r :: rs) →
    ∀ s ∈ ss, r ≤ s
  | [], _, _, _ => by simp
  | [s], [], r, hint => by simp [ListInterlaces] at hint
  | s :: ss', r₁ :: rs', r, hint => by
    obtain ⟨hr, hsr₁, htail⟩ := hint
    intro s' hs'
    rcases List.mem_cons.mp hs' with rfl | hs''
    · lia
    · exact le_trans (le_trans hr hsr₁) (listInterlaces_all_ge ss' rs' r₁ htail s' hs'')
  | _ :: _ :: _, [], _, hint => by simp [ListInterlaces] at hint

/-- All elements of `rs` in a `ListInterlaces ss (r :: rs)` are `≥ r`. -/
lemma listInterlaces_rs_all_ge :
    ∀ (ss rs : List ℝ) (r : ℝ),
    ListInterlaces ss (r :: rs) →
    ∀ r' ∈ rs, r ≤ r'
  | [], [], _, _ => by simp
  | [], _ :: _, _, hint => by simp [ListInterlaces] at hint
  | s :: ss', r₂ :: rs', r, hint => by
    obtain ⟨hr, hsr₂, htail⟩ := hint
    intro r' hr'
    rcases List.mem_cons.mp hr' with rfl | hr''
    · grind
    · exact le_trans (le_trans hr hsr₂) (listInterlaces_rs_all_ge ss' rs' r₂ htail r' hr'')
  | _ :: _, [], _, hint => by simp

/-- The tail factors in a differ-by-one interlacing layout are all
nonnegative when paired against two ordered right-hand points. -/
lemma listInterlaces_tail_pair_prod_nonneg :
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

/-- In a head-position interlacing layout, evaluating at the first two
right-hand points gives opposite-or-zero product signs. -/
lemma listInterlaces_prod_mul_prod_nonpos_at_heads
    {ss : List ℝ} {r₁ r₂ : ℝ} {rest : List ℝ}
    (hint : ListInterlaces ss (r₁ :: r₂ :: rest)) :
    (ss.map (fun x => r₁ - x)).prod * (ss.map (fun x => r₂ - x)).prod ≤ 0 := by
  obtain ⟨s, ss', rfl⟩ : ∃ s ss', ss = s :: ss' := by
    cases ss with
    | nil => simp [ListInterlaces] at hint
    | cons s ss => simp
  obtain ⟨hr₁s, hsr₂, htail⟩ := hint
  have hr₁r₂ : r₁ ≤ r₂ := le_trans hr₁s hsr₂
  have hs_head_nonpos : (r₁ - s) * (r₂ - s) ≤ 0 := by nlinarith
  have htail_nonneg :
      0 ≤ ((ss'.map fun x => (r₁ - x) * (r₂ - x))).prod :=
    listInterlaces_tail_pair_prod_nonneg hr₁r₂ htail
  have htail_nonneg' :
      0 ≤ (ss'.map (fun x => r₁ - x)).prod * (ss'.map (fun x => r₂ - x)).prod := by
    simp_all
  calc
    ((s :: ss').map (fun x => r₁ - x)).prod * ((s :: ss').map (fun x => r₂ - x)).prod
        = ((r₁ - s) * (r₂ - s)) *
            ((ss'.map (fun x => r₁ - x)).prod * (ss'.map (fun x => r₂ - x)).prod) := by
              simp [mul_assoc, mul_left_comm]
    _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hs_head_nonpos htail_nonneg'

/-- Every element of the tail of `ss` is `≥ b` in a ListInterlaces ss (a :: b :: rest). -/
lemma listInterlaces_tail_ge :
    ∀ (ss : List ℝ) (a b : ℝ) (rest : List ℝ),
    ListInterlaces ss (a :: b :: rest) →
    ∀ s ∈ ss.tail, b ≤ s
  | [], _, _, _, _ => by simp
  | [_], _, _, _, _ => by simp
  | _ :: ss', a, b, rest, hint => by
    obtain ⟨_, _, htail⟩ := hint
    exact fun s hs => listInterlaces_all_ge ss' rest b htail s hs

/-- A list satisfying `ListInterlaces ss rs` is sorted (pairwise ≤). -/
lemma pairwise_le_of_listInterlaces :
    ∀ (ss rs : List ℝ), ListInterlaces ss rs → ss.Pairwise (· ≤ ·)
  | [], _, _ => List.Pairwise.nil
  | [_], _, _ => List.pairwise_singleton _ _
  | s₁ :: s₂ :: ss', r₁ :: r₂ :: rs', h => by
      obtain ⟨_, hs₁r₂, htail⟩ := h
      have hs₁s₂ : s₁ ≤ s₂ :=
        le_trans hs₁r₂
          (listInterlaces_all_ge (s₂ :: ss') rs' r₂ htail s₂ (by simp))
      have ih : (s₂ :: ss').Pairwise (· ≤ ·) :=
        pairwise_le_of_listInterlaces (s₂ :: ss') (r₂ :: rs') htail
      grind
  | _ :: _ :: _, [], h => by simp [ListInterlaces] at h
  | _ :: _ :: _, [_], h => by simp [ListInterlaces] at h

lemma orderedInsert_eq_cons_of_forall_le {a : ℝ} :
    ∀ {l : List ℝ}, (∀ b ∈ l, a ≤ b) → l.orderedInsert (· ≤ ·) a = a :: l
  | [], _ => by simp
  | b :: l, h => by
      simp_all

lemma listInterlaces_orderedInsert :
    ∀ {ss rs : List ℝ},
      ss.length + 1 = rs.length →
      ListInterlaces ss rs →
      ∀ a : ℝ, ListInterlaces (ss.orderedInsert (· ≤ ·) a) (rs.orderedInsert (· ≤ ·) a)
  | [], [r], hlen, hint, a => by
      by_cases har : a ≤ r
      · simp [ListInterlaces, har]
      · have hra : r ≤ a := le_of_not_ge har
        simp [ListInterlaces, har, hra]
  | s :: ss, r₁ :: r₂ :: rs, hlen, hint, a => by
      obtain ⟨hr₁s, hsr₂, htail⟩ := hint
      by_cases har₁ : a ≤ r₁
      · have has : a ≤ s := le_trans har₁ hr₁s
        rw [List.orderedInsert_cons_of_le (r := (· ≤ ·)) (l := r₂ :: rs) har₁,
          List.orderedInsert_cons_of_le (r := (· ≤ ·)) (l := ss) has]
        exact ⟨le_rfl, har₁, ⟨hr₁s, hsr₂, htail⟩⟩
      · by_cases has : a ≤ s
        · have har₂ : a ≤ r₂ := le_trans has hsr₂
          rw [List.orderedInsert_of_not_le (r := (· ≤ ·)) (l := r₂ :: rs) har₁,
            List.orderedInsert_cons_of_le (r := (· ≤ ·)) (l := ss) has,
            List.orderedInsert_cons_of_le (r := (· ≤ ·)) (l := rs) har₂]
          exact ⟨le_of_not_ge har₁, le_rfl, has, hsr₂, htail⟩
        · by_cases har₂ : a ≤ r₂
          · have htail_ge : ∀ b ∈ ss, a ≤ b :=
              fun b hb => le_trans har₂ (listInterlaces_all_ge ss rs r₂ htail b hb)
            rw [List.orderedInsert_of_not_le (r := (· ≤ ·)) (l := r₂ :: rs) har₁,
              List.orderedInsert_of_not_le (r := (· ≤ ·)) (l := ss) has,
              List.orderedInsert_cons_of_le (r := (· ≤ ·)) (l := rs) har₂,
              orderedInsert_eq_cons_of_forall_le htail_ge]
            exact ⟨hr₁s, le_of_not_ge has, le_rfl, har₂, htail⟩
          · rw [List.orderedInsert_of_not_le (r := (· ≤ ·)) (l := r₂ :: rs) har₁,
              List.orderedInsert_of_not_le (r := (· ≤ ·)) (l := ss) has,
              List.orderedInsert_of_not_le (r := (· ≤ ·)) (l := rs) har₂]
            have hlen' : ss.length + 1 = (r₂ :: rs).length := by simp_all
            exact ⟨hr₁s, hsr₂, by
              simpa [List.orderedInsert_of_not_le (r := (· ≤ ·)) (l := rs) har₂] using
                listInterlaces_orderedInsert hlen' htail a⟩
  | [], _ :: _ :: _, hlen, _, _ => by simp at hlen
  | _ :: _, [], hlen, _, _ => by simp at hlen
  | _ :: _, [_], hlen, _, _ => by simp at hlen

lemma listAlternates_orderedInsert :
    ∀ {ss rs : List ℝ},
      ss.length = rs.length →
      ListAlternates ss rs →
      ∀ a : ℝ, ListAlternates (ss.orderedInsert (· ≤ ·) a) (rs.orderedInsert (· ≤ ·) a)
  | [], [], _, _, a => by
      simp [ListAlternates, ListInterlaces]
  | s :: ss, r :: rs, hlen, halt, a => by
      obtain ⟨hsr, hint⟩ := halt
      by_cases has : a ≤ s
      · have har : a ≤ r := le_trans has hsr
        rw [List.orderedInsert_cons_of_le (r := (· ≤ ·)) (l := rs) har,
          List.orderedInsert_cons_of_le (r := (· ≤ ·)) (l := ss) has]
        exact ⟨le_rfl, ⟨has, hsr, hint⟩⟩
      · by_cases har : a ≤ r
        · rw [List.orderedInsert_of_not_le (r := (· ≤ ·)) (l := ss) has,
            List.orderedInsert_cons_of_le (r := (· ≤ ·)) (l := rs) har]
          have htail_ge : ∀ b ∈ ss, a ≤ b :=
            fun b hb => le_trans har (listInterlaces_all_ge ss rs r hint b hb)
          rw [orderedInsert_eq_cons_of_forall_le htail_ge]
          constructor
          · grind
          · exact ⟨le_rfl, har, hint⟩
        · rw [List.orderedInsert_of_not_le (r := (· ≤ ·)) (l := ss) has,
            List.orderedInsert_of_not_le (r := (· ≤ ·)) (l := rs) har]
          have hlen' : ss.length + 1 = (r :: rs).length := by simp_all
          exact ⟨hsr, by
            simpa [List.orderedInsert_of_not_le (r := (· ≤ ·)) (l := rs) har] using
              listInterlaces_orderedInsert hlen' hint a⟩
  | [], _ :: _, hlen, _, _ => by simp at hlen
  | _ :: _, [], hlen, _, _ => by simp at hlen

lemma listInterlaces_of_orderedInsert (a : ℝ) :
    ∀ {ss rs : List ℝ},
      ss.length + 1 = rs.length →
      ss.Pairwise (· ≤ ·) →
      rs.Pairwise (· ≤ ·) →
      ListInterlaces (ss.orderedInsert (· ≤ ·) a) (rs.orderedInsert (· ≤ ·) a) →
      ListInterlaces ss rs
  | [], [r], _, _, _, _ => by simp [ListInterlaces]
  | s :: ss, r₁ :: r₂ :: rs, hlen, hss, hrs, hint => by
      by_cases har₁ : a ≤ r₁
      · by_cases has : a ≤ s
        · rw [List.orderedInsert_cons_of_le (r := (· ≤ ·)) (l := ss) has,
            List.orderedInsert_cons_of_le (r := (· ≤ ·)) (l := r₂ :: rs) har₁] at hint
          simp only [ListInterlaces, Std.le_refl, true_and] at hint
          exact ⟨hint.2.1, hint.2.2.1, hint.2.2.2⟩
        · rw [List.orderedInsert_of_not_le (r := (· ≤ ·)) (l := ss) has,
            List.orderedInsert_cons_of_le (r := (· ≤ ·)) (l := r₂ :: rs) har₁] at hint
          simp [ListInterlaces, has] at hint
      · by_cases has : a ≤ s
        · by_cases har₂ : a ≤ r₂
          · rw [List.orderedInsert_cons_of_le (r := (· ≤ ·)) (l := ss) has,
              List.orderedInsert_of_not_le (r := (· ≤ ·)) (l := r₂ :: rs) har₁,
              List.orderedInsert_cons_of_le (r := (· ≤ ·)) (l := rs) har₂] at hint
            simp only [ListInterlaces, Std.le_refl, true_and] at hint
            exact ⟨le_trans hint.1 hint.2.1, hint.2.2.1, hint.2.2.2⟩
          · rw [List.orderedInsert_cons_of_le (r := (· ≤ ·)) (l := ss) has,
              List.orderedInsert_of_not_le (r := (· ≤ ·)) (l := r₂ :: rs) har₁,
              List.orderedInsert_of_not_le (r := (· ≤ ·)) (l := rs) har₂] at hint
            simp [ListInterlaces, har₂] at hint
        · by_cases har₂ : a ≤ r₂
          · rw [List.orderedInsert_of_not_le (r := (· ≤ ·)) (l := ss) has,
              List.orderedInsert_of_not_le (r := (· ≤ ·)) (l := r₂ :: rs) har₁,
              List.orderedInsert_cons_of_le (r := (· ≤ ·)) (l := rs) har₂] at hint
            simp only [ListInterlaces, reduceCtorEq, imp_self, implies_true, List.cons.injEq,
              and_false] at hint
            have hlen' : ss.length + 1 = (r₂ :: rs).length := by simp_all
            have htail :
                ListInterlaces (ss.orderedInsert (· ≤ ·) a)
                  ((r₂ :: rs).orderedInsert (· ≤ ·) a) := by
              simp_all
            exact ⟨hint.1, le_trans hint.2.1 har₂,
              listInterlaces_of_orderedInsert a hlen' hss.of_cons hrs.of_cons htail⟩
          · rw [List.orderedInsert_of_not_le (r := (· ≤ ·)) (l := ss) has,
              List.orderedInsert_of_not_le (r := (· ≤ ·)) (l := r₂ :: rs) har₁,
              List.orderedInsert_of_not_le (r := (· ≤ ·)) (l := rs) har₂] at hint
            have hlen' : ss.length + 1 = (r₂ :: rs).length := by simp_all
            simp only [ListInterlaces, reduceCtorEq, imp_self, implies_true] at hint
            have htail :
                ListInterlaces (ss.orderedInsert (· ≤ ·) a)
                  ((r₂ :: rs).orderedInsert (· ≤ ·) a) := by
              grind
            exact ⟨hint.1, hint.2.1,
              listInterlaces_of_orderedInsert a hlen' hss.of_cons hrs.of_cons htail⟩
  | [], _ :: _ :: _, hlen, _, _, _ => by simp at hlen
  | _ :: _, [], hlen, _, _, _ => by simp at hlen
  | _ :: _, [_], hlen, _, _, _ => by simp at hlen

lemma listAlternates_of_orderedInsert (a : ℝ) :
    ∀ {ss rs : List ℝ},
      ss.length = rs.length →
      ss.Pairwise (· ≤ ·) →
      rs.Pairwise (· ≤ ·) →
      ListAlternates (ss.orderedInsert (· ≤ ·) a) (rs.orderedInsert (· ≤ ·) a) →
      ListAlternates ss rs
  | [], [], _, _, _, _ => by simp [ListAlternates]
  | s :: ss, r :: rs, hlen, hss, hrs, hint => by
      by_cases has : a ≤ s
      · by_cases har : a ≤ r
        · rw [List.orderedInsert_cons_of_le (r := (· ≤ ·)) (l := ss) has,
            List.orderedInsert_cons_of_le (r := (· ≤ ·)) (l := rs) har] at hint
          have htail : a ≤ s ∧ s ≤ r ∧ ListInterlaces ss (r :: rs) := by
            simpa [ListAlternates, ListInterlaces] using hint
          exact ⟨htail.2.1, htail.2.2⟩
        · rw [List.orderedInsert_cons_of_le (r := (· ≤ ·)) (l := ss) has,
            List.orderedInsert_of_not_le (r := (· ≤ ·)) (l := rs) har] at hint
          simp [ListAlternates, har] at hint
      · by_cases har : a ≤ r
        · rw [List.orderedInsert_of_not_le (r := (· ≤ ·)) (l := ss) has,
            List.orderedInsert_cons_of_le (r := (· ≤ ·)) (l := rs) har] at hint
          simp only [ListAlternates] at hint
          have hlen' : ss.length + 1 = (r :: rs).length := by simp_all
          have htail :
              ListInterlaces (ss.orderedInsert (· ≤ ·) a)
                ((r :: rs).orderedInsert (· ≤ ·) a) := by
            simp_all
          exact ⟨le_trans hint.1 har,
            listInterlaces_of_orderedInsert a hlen' hss.of_cons hrs htail⟩
        · rw [List.orderedInsert_of_not_le (r := (· ≤ ·)) (l := ss) has,
            List.orderedInsert_of_not_le (r := (· ≤ ·)) (l := rs) har] at hint
          simp only [ListAlternates] at hint
          have hlen' : ss.length + 1 = (r :: rs).length := by simp_all
          have htail :
              ListInterlaces (ss.orderedInsert (· ≤ ·) a)
                ((r :: rs).orderedInsert (· ≤ ·) a) := by
            grind
          exact ⟨hint.1,
            listInterlaces_of_orderedInsert a hlen' hss.of_cons hrs htail⟩
  | [], _ :: _, hlen, _, _, _ => by simp at hlen
  | _ :: _, [], hlen, _, _, _ => by simp at hlen

/-! ## List-level lemmas for Wagner (3) -/

lemma listAlternates_append_zero :
    ∀ (ss rs : List ℝ),
    ss.length + 1 = rs.length →
    ListInterlaces ss rs →
    (∀ r ∈ rs, r ≤ 0) →
    ListAlternates rs (ss ++ [0])
  | [], [r₁], _, _, hrs => by
    simp only [ListAlternates, List.nil_append, ListInterlaces]
    simp_all
  | s :: _, _ :: [], hlen, _, _ => by simp at hlen
  | s :: ss', r₁ :: r₂ :: rs', hlen, hint, hrs => by
    obtain ⟨hr₁s, hsr₂, htail⟩ := hint
    simp only [ListAlternates, List.cons_append]
    refine ⟨hr₁s, ?_⟩
    have hrs_tail : ∀ r ∈ r₂ :: rs', r ≤ 0 :=
      List.forall_mem_of_forall_mem_cons hrs
    have hlen_tail : ss'.length + 1 = (r₂ :: rs').length := by simp_all
    have ih := listAlternates_append_zero ss' (r₂ :: rs') hlen_tail htail hrs_tail
    match ss', rs' with
    | [], [] =>
      simp only [ListInterlaces, List.nil_append]
      simp_all
    | s' :: ss'', _ =>
      simp only [ListInterlaces, List.cons_append]
      simp only [ListAlternates, List.cons_append] at ih
      lia

lemma listInterlaces_of_listAlternates_append_zero :
    ∀ (ss rs : List ℝ),
    ss.length + 1 = rs.length →
    ListAlternates rs (ss ++ [0]) →
    ListInterlaces ss rs
  | [], [_], _, halt => by
    simp only [ListAlternates, List.nil_append, ListInterlaces] at halt ⊢
  | s :: _, _ :: [], hlen, _ => by simp at hlen
  | s :: ss', r₁ :: r₂ :: rs', hlen, halt => by
    simp only [ListAlternates, List.cons_append] at halt
    obtain ⟨hr₁s, htail_inter⟩ := halt
    match ss', rs' with
    | [], [] =>
      simp only [ListInterlaces, List.nil_append] at htail_inter ⊢
      lia
    | s' :: ss'', rs'' =>
      simp only [ListInterlaces, List.cons_append] at htail_inter
      obtain ⟨hsr₂, hr₂s', htail'⟩ := htail_inter
      refine ⟨hr₁s, hsr₂, ?_⟩
      have halt' : ListAlternates (r₂ :: rs'') ((s' :: ss'') ++ [0]) := by
        simp only [ListAlternates, List.cons_append]; lia
      have hlen' : (s' :: ss'').length + 1 = (r₂ :: rs'').length := by simp_all
      exact listInterlaces_of_listAlternates_append_zero (s' :: ss'') (r₂ :: rs'') hlen' halt'

lemma listInterlaces_of_listAlternates_append_right
    {ss qs : List ℝ} {uR : ℝ}
    (hlen : qs.length + 1 = ss.length)
    (halt : ListAlternates ss (qs ++ [uR])) :
    ListInterlaces qs ss := by
  have halt0 :
      ListAlternates (ss.map (· - uR)) ((qs.map (· - uR)) ++ [0]) := by
    simpa [List.map_append] using listAlternates_map_sub_const halt uR
  have hlen0 : (qs.map (· - uR)).length + 1 = (ss.map (· - uR)).length := by simp_all
  have hint0 :
      ListInterlaces (qs.map (· - uR)) (ss.map (· - uR)) :=
    listInterlaces_of_listAlternates_append_zero
      (qs.map (· - uR)) (ss.map (· - uR)) hlen0 halt0
  have hfun :
      ((fun x : ℝ => x + uR) ∘ fun x => x - uR) = fun x => x := by
    grind
  simpa [List.map_map, Function.comp, hfun] using
    listInterlaces_map_sub_const hint0 (-uR)

/-- In the same-degree `Prec` case, removing a rightmost root of the right-hand
polynomial turns the quotient into an honest differ-by-1 interlacer for the
left-hand polynomial. -/
lemma interlaces_of_prec_sameDegree_rightmost_factor
    {f g q : ℝ[X]} {uR : ℝ}
    (hfg : Prec f g)
    (hdeg : f.natDegree = g.natDegree)
    (hright : ∀ r ∈ g.roots, r ≤ uR)
    (hgq : g = (X - C uR) * q) :
    Interlaces q f := by
  obtain ⟨hf, hg, ss, rs, hss_sorted, hrs_sorted, hss_eq, hrs_eq, hshape⟩ := hfg
  have hss_len : ss.length = f.natDegree := by
    rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hf.2]
  have hrs_len : rs.length = g.natDegree := by
    rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hg.2]
  have hq_ne : q ≠ 0 := by simp_all
  have hq : q ≠ 0 ∧ q.Splits := by
    apply isRealRooted_of_dvd hg.1 hg.2 hq_ne
    simp_all
  have hq_deg_g : q.natDegree + 1 = g.natDegree := by
    rw [hgq, natDegree_mul (X_sub_C_ne_zero uR) hq_ne, natDegree_X_sub_C]
    lia
  have hq_deg : q.natDegree + 1 = f.natDegree := by lia
  rcases hshape with ⟨_, _⟩ | ⟨_, halt⟩
  · lia
  · let qs := q.roots.sort (· ≤ ·)
    have hqs_eq : (↑qs : Multiset ℝ) = q.roots := Multiset.sort_eq ..
    have hqs_sorted : qs.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
    have hqs_len : qs.length = q.natDegree := by
      rw [show qs = q.roots.sort (· ≤ ·) by lia, Multiset.length_sort,
        card_roots_of_splits hq.2]
    have hqs_le_uR : ∀ r ∈ qs, r ≤ uR :=
      fun r hr => hright r (by
        rw [hgq, roots_mul (mul_ne_zero (X_sub_C_ne_zero uR) hq_ne), roots_X_sub_C]
        apply Multiset.mem_add.mpr
        right
        simpa [hqs_eq] using Multiset.mem_coe.mpr hr)
    have hqs_sorted_right : (qs ++ [uR]).Pairwise (· ≤ ·) := by grind
    have hrs_eq_right : rs = qs ++ [uR] := by
      apply List.Perm.eq_of_pairwise' hrs_sorted hqs_sorted_right
      apply Multiset.coe_eq_coe.mp
      calc
        (↑rs : Multiset ℝ) = g.roots := hrs_eq
        _ = ({uR} : Multiset ℝ) + q.roots := by
          rw [hgq, roots_mul (mul_ne_zero (X_sub_C_ne_zero uR) hq_ne), roots_X_sub_C]
        _ = q.roots + ({uR} : Multiset ℝ) := by grind
        _ = q.roots + ↑[uR] := by simp
        _ = (↑qs : Multiset ℝ) + ↑[uR] := by lia
        _ = (↑(qs ++ [uR]) : Multiset ℝ) := by rw [Multiset.coe_add]
    have hlen_qs : qs.length + 1 = ss.length := by lia
    have halt_right : ListAlternates ss (qs ++ [uR]) := by lia
    have hshape_qs_rs : ListInterlaces qs ss :=
      listInterlaces_of_listAlternates_append_right hlen_qs halt_right
    exact ⟨hf, hq, hq_deg, ss, qs, hss_sorted, hqs_sorted, hss_eq, hqs_eq, hshape_qs_rs⟩

lemma listInterlaces_append_zero_both :
    ∀ (ss rs : List ℝ),
    ss.length + 1 = rs.length →
    ListInterlaces ss rs →
    (∀ r ∈ rs, r ≤ 0) →
    ListInterlaces (ss ++ [0]) (rs ++ [0])
  | [], [r], _, _, hrs => by
      simp [ListInterlaces, hrs r (by simp)]
  | _ :: _, [_], hlen, _, _ => by simp at hlen
  | s :: ss', r₁ :: r₂ :: rs', hlen, hint, hrs => by
      obtain ⟨hr₁s, hsr₂, htail⟩ := hint
      simp only [List.cons_append, ListInterlaces, hr₁s, hsr₂, true_and]
      have hrs_tail : ∀ r ∈ r₂ :: rs', r ≤ 0 :=
        List.forall_mem_of_forall_mem_cons hrs
      have hlen_tail : ss'.length + 1 = (r₂ :: rs').length := by simp_all
      exact listInterlaces_append_zero_both ss' (r₂ :: rs') hlen_tail htail hrs_tail
  | [], _ :: _ :: _, hlen, _, _ => by simp at hlen
  | _ :: _, [], hlen, _, _ => by simp at hlen

lemma listAlternates_append_zero_both :
    ∀ (ss rs : List ℝ),
    ss.length = rs.length →
    ListAlternates ss rs →
    (∀ r ∈ rs, r ≤ 0) →
    ListAlternates (ss ++ [0]) (rs ++ [0])
  | [], [], _, _, _ => by simp [ListAlternates, ListInterlaces]
  | s :: ss', r :: rs', hlen, halt, hrs => by
      obtain ⟨hsr, htail⟩ := halt
      simp only [ListAlternates, List.cons_append, hsr, true_and]
      have hlen_tail : ss'.length + 1 = (r :: rs').length := by simp_all
      exact listInterlaces_append_zero_both ss' (r :: rs') hlen_tail htail hrs
  | [], _ :: _, hlen, _, _ => by simp at hlen
  | _ :: _, [], hlen, _, _ => by simp at hlen

lemma listInterlaces_of_append_zero_both :
    ∀ (ss rs : List ℝ),
    ss.length + 1 = rs.length →
    ListInterlaces (ss ++ [0]) (rs ++ [0]) →
    ListInterlaces ss rs
  | [], [r], _, _ => by simp [ListInterlaces]
  | _ :: _, [_], hlen, _ => by simp at hlen
  | s :: ss', r₁ :: r₂ :: rs', hlen, hint => by
      simp only [List.cons_append, ListInterlaces] at hint ⊢
      refine ⟨hint.1, hint.2.1, ?_⟩
      have hlen_tail : ss'.length + 1 = (r₂ :: rs').length := by simp_all
      exact listInterlaces_of_append_zero_both ss' (r₂ :: rs') hlen_tail hint.2.2
  | [], _ :: _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen

lemma listInterlaces_right_of_listAlternates_append_zero :
    ∀ (ss rs : List ℝ),
    ss.length = rs.length →
    ListAlternates ss rs →
    (∀ r ∈ rs, r ≤ 0) →
    ListInterlaces rs (ss ++ [0])
  | ss, rs, hlen, halt, hrs => by
      have halt0 : ListAlternates (ss ++ [0]) (rs ++ [0]) :=
        listAlternates_append_zero_both ss rs hlen halt hrs
      have hlen0 : rs.length + 1 = (ss ++ [0]).length := by simp [hlen]
      exact listInterlaces_of_listAlternates_append_zero rs (ss ++ [0]) hlen0 halt0

lemma listAlternates_of_append_zero_both :
    ∀ (ss rs : List ℝ),
    ss.length = rs.length →
    ListAlternates (ss ++ [0]) (rs ++ [0]) →
    ListAlternates ss rs
  | [], [], _, _ => by simp [ListAlternates]
  | s :: ss', r :: rs', hlen, halt => by
      simp only [List.cons_append, ListAlternates] at halt ⊢
      refine ⟨halt.1, ?_⟩
      have hlen_tail : ss'.length + 1 = (r :: rs').length := by simp_all
      exact listInterlaces_of_append_zero_both ss' (r :: rs') hlen_tail halt.2
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen

end RealRooted
