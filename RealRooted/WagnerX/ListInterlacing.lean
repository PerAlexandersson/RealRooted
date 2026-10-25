module

public import RealRooted.Basic
public import RealRooted.Linear
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Wagner-X list interlacing

Legacy root-list interlacing algebra used by Wagner's polynomial transports.
-/

@[expose] public section

open Polynomial Filter

noncomputable section

namespace RealRooted

/-! ## List-level lemmas for interlacing -/

/-- Every element of `ss` is `≥` the first element of `rs` in a ListInterlaces. -/
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
private lemma listInterlaces_tail_pair_prod_nonneg :
    ∀ {ss : List ℝ} {r₁ r₂ : ℝ} {rest : List ℝ},
      r₁ ≤ r₂ →
      ListInterlaces ss (r₂ :: rest) →
      0 ≤ (ss.map (fun x => (r₁ - x) * (r₂ - x))).prod
  | ss, r₁, r₂, rest, hr₁r₂, h => by
      refine List.prod_nonneg fun y hy => ?_
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
      nlinarith [listInterlaces_all_ge ss rest r₂ h x hx]

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
  have htail_nonneg' :
      0 ≤ (ss'.map (fun x => r₁ - x)).prod * (ss'.map (fun x => r₂ - x)).prod := by
    simpa using listInterlaces_tail_pair_prod_nonneg hr₁r₂ htail
  calc
    ((s :: ss').map (fun x => r₁ - x)).prod * ((s :: ss').map (fun x => r₂ - x)).prod
        = ((r₁ - s) * (r₂ - s)) *
            ((ss'.map (fun x => r₁ - x)).prod * (ss'.map (fun x => r₂ - x)).prod) := by
              simp [mul_assoc, mul_left_comm]
    _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hs_head_nonpos htail_nonneg'

/-- A list satisfying `ListInterlaces ss rs` is sorted (pairwise ≤). -/
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
            exact ⟨hr₁s, hsr₂, by
              simpa [List.orderedInsert_of_not_le (r := (· ≤ ·)) (l := rs) har₂] using
                listInterlaces_orderedInsert (by simp_all) htail a⟩
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
          exact ⟨hsr, by
            simpa [List.orderedInsert_of_not_le (r := (· ≤ ·)) (l := rs) har] using
              listInterlaces_orderedInsert (by simp_all) hint a⟩
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
            exact ⟨hint.1, le_trans hint.2.1 har₂,
              listInterlaces_of_orderedInsert a (by simp_all) hss.of_cons hrs.of_cons
                (by simp_all)⟩
          · rw [List.orderedInsert_of_not_le (r := (· ≤ ·)) (l := ss) has,
              List.orderedInsert_of_not_le (r := (· ≤ ·)) (l := r₂ :: rs) har₁,
              List.orderedInsert_of_not_le (r := (· ≤ ·)) (l := rs) har₂] at hint
            simp only [ListInterlaces, reduceCtorEq, imp_self, implies_true] at hint
            exact ⟨hint.1, hint.2.1,
              listInterlaces_of_orderedInsert a (by simp_all) hss.of_cons hrs.of_cons
                (by grind)⟩
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
          exact ⟨le_trans hint.1 har,
            listInterlaces_of_orderedInsert a (by simp_all) hss.of_cons hrs (by simp_all)⟩
        · rw [List.orderedInsert_of_not_le (r := (· ≤ ·)) (l := ss) has,
            List.orderedInsert_of_not_le (r := (· ≤ ·)) (l := rs) har] at hint
          simp only [ListAlternates] at hint
          exact ⟨hint.1,
            listInterlaces_of_orderedInsert a (by simp_all) hss.of_cons hrs (by grind)⟩
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
    have ih := listAlternates_append_zero ss' (r₂ :: rs') (by simp_all) htail
      (List.forall_mem_of_forall_mem_cons hrs)
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
      exact listInterlaces_of_listAlternates_append_zero (s' :: ss'') (r₂ :: rs'')
        (by simp_all) (by simp only [ListAlternates, List.cons_append]; lia)

private lemma listInterlaces_of_listAlternates_append_right
    {ss qs : List ℝ} {uR : ℝ}
    (hlen : qs.length + 1 = ss.length)
    (halt : ListAlternates ss (qs ++ [uR])) :
    ListInterlaces qs ss := by
  have hint0 :
      ListInterlaces (qs.map (· - uR)) (ss.map (· - uR)) :=
    listInterlaces_of_listAlternates_append_zero
      (qs.map (· - uR)) (ss.map (· - uR)) (by simpa using hlen)
      (by simpa [List.map_append] using listAlternates_map_sub_const halt uR)
  have hfun : ((fun x : ℝ => x + uR) ∘ fun x => x - uR) = fun x => x := by grind
  simpa [List.map_map, Function.comp, hfun] using
    listInterlaces_map_sub_const hint0 (-uR)

/-- In the same-degree `StrictInterl` case, removing a rightmost root of the right-hand
polynomial turns the quotient into an honest differ-by-1 interlacer for the
left-hand polynomial. -/
lemma interlaces_of_strictInterl_sameDegree_rightmost_factor
    {f g q : ℝ[X]} {uR : ℝ}
    (hfg : StrictInterl f g)
    (hdeg : f.natDegree = g.natDegree)
    (hright : ∀ r ∈ g.roots, r ≤ uR)
    (hgq : g = (X - C uR) * q) :
    Interlaces q f := by
  obtain ⟨ss, rs, hss_sorted, hrs_sorted, hss_eq, hrs_eq, halt⟩ :=
    hfg.exists_listAlternates_of_natDegree_eq hdeg
  have hss_len : ss.length = f.natDegree := by
    rw [← Multiset.coe_card, hss_eq, Polynomial.splits_iff_card_roots.mp hfg.1.2]
  have hq_ne : q ≠ 0 := right_ne_zero_of_mul (by rw [← hgq]; exact hfg.2.1.1)
  have hq : q ≠ 0 ∧ q.Splits := by
    apply isRealRooted_of_dvd hfg.2.1.1 hfg.2.1.2 hq_ne
    simp_all
  have hq_deg_g : q.natDegree + 1 = g.natDegree := by
    rw [hgq, natDegree_mul (X_sub_C_ne_zero uR) hq_ne, natDegree_X_sub_C]
    lia
  have hq_deg : q.natDegree + 1 = f.natDegree := by lia
  let qs := q.roots.sort (· ≤ ·)
  have hqs_eq : (↑qs : Multiset ℝ) = q.roots := Multiset.sort_eq ..
  have hqs_sorted : qs.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hqs_len : qs.length = q.natDegree := by
    simp [qs, Polynomial.splits_iff_card_roots.mp hq.2]
  have hqs_le_uR : ∀ r ∈ qs, r ≤ uR :=
    fun r hr => hright r (by
      rw [hgq, roots_mul (mul_ne_zero (X_sub_C_ne_zero uR) hq_ne), roots_X_sub_C]
      exact Multiset.mem_add.mpr <| Or.inr <| by simpa [hqs_eq] using Multiset.mem_coe.mpr hr)
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
  rw [hrs_eq_right] at halt
  exact ⟨hfg.1, hq, hq_deg, ss, qs, hss_sorted, hqs_sorted, hss_eq, hqs_eq,
    listInterlaces_of_listAlternates_append_right hlen_qs halt⟩

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
      exact listInterlaces_append_zero_both ss' (r₂ :: rs') (by simp_all) htail
        (List.forall_mem_of_forall_mem_cons hrs)
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
      exact listInterlaces_append_zero_both ss' (r :: rs') (by simp_all) htail hrs
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
      exact listInterlaces_of_append_zero_both ss' (r₂ :: rs') (by simp_all) hint.2.2
  | [], _ :: _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen

lemma listInterlaces_right_of_listAlternates_append_zero :
    ∀ (ss rs : List ℝ),
    ss.length = rs.length →
    ListAlternates ss rs →
    (∀ r ∈ rs, r ≤ 0) →
    ListInterlaces rs (ss ++ [0])
  | ss, rs, hlen, halt, hrs => by
      exact listInterlaces_of_listAlternates_append_zero rs (ss ++ [0]) (by simp [hlen])
        (listAlternates_append_zero_both ss rs hlen halt hrs)

lemma listAlternates_of_append_zero_both :
    ∀ (ss rs : List ℝ),
    ss.length = rs.length →
    ListAlternates (ss ++ [0]) (rs ++ [0]) →
    ListAlternates ss rs
  | [], [], _, _ => by simp [ListAlternates]
  | s :: ss', r :: rs', hlen, halt => by
      simp only [List.cons_append, ListAlternates] at halt ⊢
      refine ⟨halt.1, ?_⟩
      exact listInterlaces_of_append_zero_both ss' (r :: rs') (by simp_all) halt.2
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen

private lemma coe_orderedInsert_eq_roots_mul_X_sub_C {p : ℝ[X]} (hp : p ≠ 0)
    {ss : List ℝ} (hss : (↑ss : Multiset ℝ) = p.roots) (r : ℝ) :
    (↑(ss.orderedInsert (· ≤ ·) r) : Multiset ℝ) = ((X - C r) * p).roots := by
  have hinsert :
      (↑(ss.orderedInsert (· ≤ ·) r) : Multiset ℝ) = ({r} : Multiset ℝ) + ↑ss := by
    calc
      (↑(ss.orderedInsert (· ≤ ·) r) : Multiset ℝ) = ↑(r :: ss) :=
        Multiset.coe_eq_coe.mpr (List.perm_orderedInsert (r := (· ≤ ·)) r ss)
      _ = ({r} : Multiset ℝ) + ↑ss := by simp
  have hroots : ({r} : Multiset ℝ) + ↑ss = ((X - C r) * p).roots := by
    rw [hss]
    simpa [roots_X_sub_C] using
      (roots_mul (mul_ne_zero (X_sub_C_ne_zero r) hp)).symm
  exact hinsert.trans hroots

/-- Multiplying both polynomials by the same affine factor preserves strict
interlacing. -/
theorem StrictInterl.mul_X_sub_C_both {f g : ℝ[X]} (h : StrictInterl f g) (r : ℝ) :
    StrictInterl ((X - C r) * f) ((X - C r) * g) := by
  rcases h with ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hcase⟩
  refine ⟨isRealRooted_mul (isRealRooted_X_sub_C r).1 (isRealRooted_X_sub_C r).2 hf.1 hf.2,
    isRealRooted_mul (isRealRooted_X_sub_C r).1 (isRealRooted_X_sub_C r).2 hg.1 hg.2,
    ss.orderedInsert (· ≤ ·) r, rs.orderedInsert (· ≤ ·) r,
    hss.orderedInsert _ _, hrs.orderedInsert _ _, ?_, ?_, ?_⟩
  · exact coe_orderedInsert_eq_roots_mul_X_sub_C hf.1 hss_eq r
  · exact coe_orderedInsert_eq_roots_mul_X_sub_C hg.1 hrs_eq r
  · rcases hcase with ⟨hlen, hint⟩ | ⟨hlen, halt⟩
    · refine Or.inl ⟨?_, listInterlaces_orderedInsert hlen hint r⟩
      rw [List.orderedInsert_length (r := (· ≤ ·)) ss r,
        List.orderedInsert_length (r := (· ≤ ·)) rs r]
      lia
    · exact Or.inr ⟨by
        rw [List.orderedInsert_length (r := (· ≤ ·)) ss r,
          List.orderedInsert_length (r := (· ≤ ·)) rs r]
        lia,
        listAlternates_orderedInsert hlen halt r⟩

/-- Cancelling a common affine factor preserves strict interlacing. -/
theorem StrictInterl.of_mul_X_sub_C_both {f g : ℝ[X]} {r : ℝ}
    (h : StrictInterl ((X - C r) * f) ((X - C r) * g)) :
    StrictInterl f g := by
  rcases h with
    ⟨hXf, hXg, ss_mul, rs_mul, hss_mul, hrs_mul, hss_mul_eq, hrs_mul_eq, hcase⟩
  have hf0 : f ≠ 0 := right_ne_zero_of_mul hXf.1
  have hg0 : g ≠ 0 := right_ne_zero_of_mul hXg.1
  have hf : f ≠ 0 ∧ f.Splits :=
    ⟨hf0, hXf.2.of_dvd hXf.1 (dvd_mul_left f _)⟩
  have hg : g ≠ 0 ∧ g.Splits :=
    ⟨hg0, hXg.2.of_dvd hXg.1 (dvd_mul_left g _)⟩
  set ss := f.roots.sort (· ≤ ·)
  set rs := g.roots.sort (· ≤ ·)
  have hss_eq : (↑ss : Multiset ℝ) = f.roots := Multiset.sort_eq ..
  have hrs_eq : (↑rs : Multiset ℝ) = g.roots := Multiset.sort_eq ..
  have hss_sorted : ss.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hrs_sorted : rs.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hss_insert_eq :
      (↑(ss.orderedInsert (· ≤ ·) r) : Multiset ℝ) = ((X - C r) * f).roots :=
    coe_orderedInsert_eq_roots_mul_X_sub_C hf.1 hss_eq r
  have hrs_insert_eq :
      (↑(rs.orderedInsert (· ≤ ·) r) : Multiset ℝ) = ((X - C r) * g).roots :=
    coe_orderedInsert_eq_roots_mul_X_sub_C hg.1 hrs_eq r
  have hss_mul_is : ss_mul = ss.orderedInsert (· ≤ ·) r :=
    List.Perm.eq_of_pairwise' hss_mul (hss_sorted.orderedInsert _ _)
      (Multiset.coe_eq_coe.mp (hss_mul_eq.trans hss_insert_eq.symm))
  have hrs_mul_is : rs_mul = rs.orderedInsert (· ≤ ·) r :=
    List.Perm.eq_of_pairwise' hrs_mul (hrs_sorted.orderedInsert _ _)
      (Multiset.coe_eq_coe.mp (hrs_mul_eq.trans hrs_insert_eq.symm))
  refine ⟨hf, hg, ss, rs, hss_sorted, hrs_sorted, hss_eq, hrs_eq, ?_⟩
  rcases hcase with ⟨hlen, hint⟩ | ⟨hlen, halt⟩
  · rw [hss_mul_is, hrs_mul_is] at hint hlen
    have hlen' : ss.length + 1 = rs.length := by
      simp only [List.orderedInsert_length] at hlen
      lia
    exact Or.inl ⟨hlen', listInterlaces_of_orderedInsert r hlen' hss_sorted hrs_sorted hint⟩
  · rw [hss_mul_is, hrs_mul_is] at halt hlen
    have hlen' : ss.length = rs.length := by
      simp only [List.orderedInsert_length] at hlen
      lia
    exact Or.inr ⟨hlen', listAlternates_of_orderedInsert r hlen' hss_sorted hrs_sorted halt⟩

/-- Multiplication by the same affine factor on both sides is an equivalence
on strict interlacing. -/
theorem StrictInterl.mul_X_sub_C_both_iff {f g : ℝ[X]} (r : ℝ) :
    StrictInterl f g ↔ StrictInterl ((X - C r) * f) ((X - C r) * g) :=
  ⟨fun h => h.mul_X_sub_C_both r, StrictInterl.of_mul_X_sub_C_both⟩

/-- Multiplying both polynomials by the same affine factor preserves
zero-aware interlacing. -/
theorem Interl.mul_X_sub_C_both {f g : ℝ[X]} (h : Interl f g) (r : ℝ) :
    Interl ((X - C r) * f) ((X - C r) * g) := by
  rcases h with rfl | rfl | hfg
  · simpa using interl_zero_left ((X - C r) * g)
  · simpa using interl_zero_right ((X - C r) * f)
  · exact (hfg.mul_X_sub_C_both r).toInterl

/-- Cancelling a common affine factor preserves zero-aware interlacing. -/
theorem Interl.of_mul_X_sub_C_both {f g : ℝ[X]} {r : ℝ}
    (h : Interl ((X - C r) * f) ((X - C r) * g)) :
    Interl f g := by
  by_cases hf0 : f = 0
  · simpa [hf0] using interl_zero_left g
  by_cases hg0 : g = 0
  · simpa [hg0] using interl_zero_right f
  have hstrict : StrictInterl ((X - C r) * f) ((X - C r) * g) :=
    h.toStrictInterl_of_ne
      (mul_ne_zero (X_sub_C_ne_zero r) hf0) (mul_ne_zero (X_sub_C_ne_zero r) hg0)
  exact hstrict.of_mul_X_sub_C_both.toInterl

/-- Multiplying both polynomials by `X` preserves zero-aware interlacing. -/
theorem Interl.mul_X_both {f g : ℝ[X]} (h : Interl f g) :
    Interl (X * f) (X * g) := by
  simpa using h.mul_X_sub_C_both 0

/-- Cancelling a common factor `X` preserves zero-aware interlacing. -/
theorem Interl.of_mul_X_both {f g : ℝ[X]} (h : Interl (X * f) (X * g)) :
    Interl f g := by
  apply Interl.of_mul_X_sub_C_both (r := 0)
  simpa using h

end RealRooted
