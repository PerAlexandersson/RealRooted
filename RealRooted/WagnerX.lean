import RealRooted.Basic
import RealRooted.Linear
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Algebra.Polynomial

/-!
# Wagner's lemma

Three forms of Wagner's lemma for polynomials:
1. f ≪ h ∧ g ≪ h → (f + g) ≪ h  (positive leading coefficients)
2. h ≪ f ∧ h ≪ g → h ≪ (f + g)  (positive leading coefficients)
3. f ≪ g ↔ g ≪ X·f               (non-negative coefficients / roots ≤ 0)

(1) and (2) generalize to n summands: if f₁,...,fₙ all interlace h
with positive leading coefficients, then (Σ fᵢ) interlaces h.
-/

open Polynomial Filter

noncomputable section

namespace RealRooted

section

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
  have hs_head_nonpos : (r₁ - s) * (r₂ - s) ≤ 0 := by
    nlinarith
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

private lemma listInterlaces_of_orderedInsert (a : ℝ) :
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

private lemma listAlternates_of_orderedInsert (a : ℝ) :
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
  have hq_ne : q ≠ 0 := by
    simp_all
  have hq : q ≠ 0 ∧ q.Splits := by
    apply isRealRooted_of_dvd hg.1 hg.2 hq_ne
    simp_all
  have hq_deg_g : q.natDegree + 1 = g.natDegree := by
    rw [hgq, natDegree_mul (X_sub_C_ne_zero uR) hq_ne, natDegree_X_sub_C]
    lia
  have hq_deg : q.natDegree + 1 = f.natDegree := by
    lia
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
    have hqs_sorted_right : (qs ++ [uR]).Pairwise (· ≤ ·) := by
      grind
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
    have hlen_qs : qs.length + 1 = ss.length := by
      lia
    have halt_right : ListAlternates ss (qs ++ [uR]) := by
      lia
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

/-! ## Roots of nonneg-coefficient polynomials are ≤ 0 -/

lemma hasNonnegCoeffs_zero : HasNonnegCoeffs (0 : ℝ[X]) := by
  simp [HasNonnegCoeffs]

lemma hasNonnegCoeffs_one : HasNonnegCoeffs (1 : ℝ[X]) := by
  rintro (_ | n)
  · simp
  · rw [coeff_one]
    simp

lemma hasNonnegCoeffs_C {a : ℝ} (ha : 0 ≤ a) : HasNonnegCoeffs (C a) := by
  rintro (_ | n) <;> simp [ha]

lemma nonnegCoeffs_C_mul {a : ℝ} (ha : 0 ≤ a) {p : ℝ[X]}
    (hp : HasNonnegCoeffs p) :
    HasNonnegCoeffs (C a * p) := by
  intro n
  simpa [coeff_C_mul] using mul_nonneg ha (hp n)

lemma HasNonnegCoeffs.add {p q : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q) :
    HasNonnegCoeffs (p + q) := fun n => by
  simpa [coeff_add] using add_nonneg (hp n) (hq n)

lemma hasNonnegCoeffs_finsetSum {ι : Type}
    (s : Finset ι) (f : ι → ℝ[X]) (hf : ∀ i ∈ s, HasNonnegCoeffs (f i)) :
    HasNonnegCoeffs (s.sum f) := by
  classical
  intro n
  simpa [finsetSum_coeff] using Finset.sum_nonneg fun i hi => hf i hi n

lemma hasNonnegCoeffs_sum :
    ∀ ps : List ℝ[X], (∀ p ∈ ps, HasNonnegCoeffs p) → HasNonnegCoeffs ps.sum
  | [], _ => by simpa using hasNonnegCoeffs_zero
  | p :: ps, hps => by
      have hp : HasNonnegCoeffs p := hps p (by simp)
      have htail : HasNonnegCoeffs ps.sum :=
        hasNonnegCoeffs_sum ps (fun q hq => hps q (by simp [hq]))
      simpa using hp.add htail

lemma HasNonnegCoeffs.mul {p q : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q) :
    HasNonnegCoeffs (p * q) := by
  intro n
  simpa [coeff_mul] using Finset.sum_nonneg fun ij _ => mul_nonneg (hp ij.1) (hq ij.2)

protected lemma HasNonnegCoeffs.pow {p : ℝ[X]} (hp : HasNonnegCoeffs p) :
    ∀ n : ℕ, HasNonnegCoeffs (p ^ n)
  | 0 => hasNonnegCoeffs_one
  | n + 1 => by
      simpa [pow_succ] using (hp.pow n).mul hp

lemma hasNonnegCoeffs_X_sub_C {r : ℝ} (hr : r ≤ 0) : HasNonnegCoeffs (X - C r) := by
  rintro (_ | _ | n)
  · simp [coeff_sub, hr]
  · simp [coeff_sub]
  · rw [coeff_sub, coeff_X_of_ne_one (by lia), coeff_C_succ]
    simp

lemma hasNonnegCoeffs_X : HasNonnegCoeffs (X : ℝ[X]) := by
  simpa using hasNonnegCoeffs_X_sub_C (r := 0) le_rfl

protected lemma HasNonnegCoeffs.X_mul {p : ℝ[X]} (hp : HasNonnegCoeffs p) :
    HasNonnegCoeffs (X * p) :=
  hasNonnegCoeffs_X.mul hp

lemma hasNonnegCoeffs_X_add_C {a : ℝ} (ha : 0 ≤ a) :
    HasNonnegCoeffs (X + C a : ℝ[X]) := by
  simpa [sub_eq_add_neg] using hasNonnegCoeffs_X_sub_C (r := -a) (by linarith)

lemma hasNonnegCoeffs_X_add_one : HasNonnegCoeffs (X + 1 : ℝ[X]) := by
  simpa using hasNonnegCoeffs_X_add_C (a := 1) (zero_le_one : (0 : ℝ) ≤ 1)

lemma hasNonnegCoeffs_multiset_prod_X_sub_C :
    ∀ s : Multiset ℝ, (∀ r ∈ s, r ≤ 0) → HasNonnegCoeffs ((s.map (X - C ·)).prod) := by
  intro s hs
  induction s using Multiset.induction_on with
  | empty =>
      simpa using hasNonnegCoeffs_one
  | @cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons]
      exact (hasNonnegCoeffs_X_sub_C (hs a (by simp))).mul
        (ih (fun r hr => hs r (by simp [hr])))

lemma roots_nonpos_of_nonneg_coeffs {p : ℝ[X]} (hp : p.Splits)
    (hnn : HasNonnegCoeffs p) : ∀ r ∈ p.roots, r ≤ 0 := by
  have _ := hp
  exact roots_nonpos_of_hasNonnegCoeffs hnn

lemma hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos {p : ℝ[X]} (hp : p.Splits) :
    HasNonnegCoeffs p ∧ p ≠ 0 ↔ HasPosLeadingCoeff p ∧ ∀ r ∈ p.roots, r ≤ 0 := by
  constructor
  · intro ⟨hnn, hp₀⟩
    exact ⟨hnn.pos_leadingCoeff hp₀, roots_nonpos_of_nonneg_coeffs hp hnn⟩
  · rintro ⟨hp₀, hroots_nonpos⟩
    refine ⟨?_, hp₀.ne_zero⟩
    rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C (card_roots_of_splits hp)]
    exact (hasNonnegCoeffs_C hp₀.le).mul
      (hasNonnegCoeffs_multiset_prod_X_sub_C p.roots hroots_nonpos)

/-- If all roots of a real-rooted positive-leading polynomial are at most `r`,
then translating by `X + r` gives a polynomial with nonnegative
coefficients. -/
lemma hasNonnegCoeffs_comp_X_add_C_of_roots_le
    {p : ℝ[X]} (hp_pos : HasPosLeadingCoeff p) (hp_splits : p.Splits)
    {r : ℝ} (hbound : ∀ s ∈ p.roots, s ≤ r) :
    HasNonnegCoeffs (p.comp (X + C r)) := by
  have hp' : ((p.comp (X + C r)) ≠ 0 ∧ (p.comp (X + C r)).Splits) :=
    isRealRooted_comp_X_add_C hp_pos.ne_zero hp_splits r
  refine ((hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos hp'.2).2 ?_).1
  refine ⟨hp_pos.comp_X_add_C r, ?_⟩
  intro s hs
  simp only [roots_comp_X_add_C r] at hs
  rcases Multiset.mem_map.mp hs with ⟨t, ht, rfl⟩
  simp_all

lemma hasNonnegCoeffs_of_dvd_of_isRealRooted_of_hasPosLeadingCoeff
    {p q : ℝ[X]}
    (hp_ne : p ≠ 0) (hp_splits : p.Splits) (hpnn : HasNonnegCoeffs p)
    (hq_ne : q ≠ 0) (hq_splits : q.Splits) (hq_pos : HasPosLeadingCoeff q)
    (hqp : q ∣ p) :
    HasNonnegCoeffs q := by
  refine ((hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos hq_splits).mpr ?_).1
  refine ⟨hq_pos, ?_⟩
  intro r hr
  have hrq : q.IsRoot r := (mem_roots hq_ne).mp hr
  have hrp : p.IsRoot r := IsRoot.of_dvd hqp hrq
  exact roots_nonpos_of_nonneg_coeffs hp_splits hpnn r ((mem_roots hp_ne).mpr hrp)

theorem prec_of_prec_mul_X_of_sameDegree_of_roots_nonpos {f g : ℝ[X]}
    (h : Prec g (X * f))
    (hdeg : f.natDegree = g.natDegree)
    (hf_nonpos : ∀ r ∈ f.roots, r ≤ 0) :
    Prec f g := by
  rcases h with ⟨hg, hXf, ss_g, rs_Xf, hss_g, hrs_Xf, hss_g_eq, hrs_Xf_eq, hshape⟩
  have hf : f ≠ 0 ∧ f.Splits := by simp_all
  set rs_f := f.roots.sort (· ≤ ·)
  have hrs_f_eq : (↑rs_f : Multiset ℝ) = f.roots := Multiset.sort_eq ..
  have hrs_f : rs_f.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hrs_f_nonpos : ∀ r ∈ rs_f, r ≤ 0 :=
    fun r hr => hf_nonpos r (by rw [← hrs_f_eq]; exact Multiset.mem_coe.mpr hr)
  have hrs_f0 : (rs_f ++ [(0 : ℝ)]).Pairwise (· ≤ ·) := by grind
  have hXf_roots : (X * f).roots = {0} + f.roots := by
    rw [roots_mul (mul_ne_zero X_ne_zero hf.1), roots_X]
  have hrs_Xf_is : rs_Xf = rs_f ++ [(0 : ℝ)] := by
    have hmultiset_eq : (↑rs_Xf : Multiset ℝ) = ↑(rs_f ++ [(0 : ℝ)]) := by
      rw [hrs_Xf_eq, hXf_roots, ← hrs_f_eq, ← Multiset.coe_add]
      simp [add_comm]
    exact List.Perm.eq_of_pairwise' hrs_Xf hrs_f0 (Multiset.coe_eq_coe.mp hmultiset_eq)
  have hlen_fg : rs_f.length = ss_g.length := by
    rw [← Multiset.coe_card, hrs_f_eq, card_roots_of_splits hf.2,
      ← Multiset.coe_card, hss_g_eq, card_roots_of_splits hg.2, hdeg]
  rcases hshape with ⟨hlen, hint⟩ | ⟨hlen, _⟩
  · rw [hrs_Xf_is] at hint hlen
    have hlen' : ss_g.length + 1 = (rs_f ++ [(0 : ℝ)]).length := by lia
    have hrs_f0_nonpos : ∀ r ∈ rs_f ++ [(0 : ℝ)], r ≤ 0 := by grind
    have halt0 :
        ListAlternates (rs_f ++ [(0 : ℝ)]) (ss_g ++ [(0 : ℝ)]) :=
      listAlternates_append_zero ss_g (rs_f ++ [(0 : ℝ)]) hlen' hint hrs_f0_nonpos
    have halt : ListAlternates rs_f ss_g :=
      listAlternates_of_append_zero_both rs_f ss_g hlen_fg halt0
    exact ⟨hf, hg, rs_f, ss_g, hrs_f, hss_g, hrs_f_eq, hss_g_eq, Or.inr ⟨hlen_fg, halt⟩⟩
  · simp_all

/-! ## Wagner (3): f ≪ g ↔ g ≪ X·f -/

theorem prec_iff_prec_mul_X {f g : ℝ[X]}
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g)
    (hf₀ : f ≠ 0) (hf : f.Splits) (hg₀ : g ≠ 0) (hg : g.Splits)
    (hdeg : f.natDegree + 1 = g.natDegree) :
    Prec f g ↔ Prec g (X * f) := by
  have hXf_roots : (X * f).roots = {0} + f.roots := by
    rw [roots_mul (mul_ne_zero X_ne_zero hf₀), roots_X]
  have hXf_deg : (X * f).natDegree = g.natDegree := by simp_all
  have hf_nonpos : ∀ r ∈ f.roots, r ≤ 0 := roots_nonpos_of_nonneg_coeffs hf hfnn
  have hg_nonpos : ∀ r ∈ g.roots, r ≤ 0 := roots_nonpos_of_nonneg_coeffs hg hgnn
  constructor
  · -- Forward: Prec f g → Prec g (X * f)
    intro ⟨_, _, ss, rs, hss, hrs, hss_eq, hrs_eq, hcase⟩
    rcases hcase with ⟨hlen, hint⟩ | ⟨hlen, _⟩
    · have hrs_nonpos : ∀ r ∈ rs, r ≤ 0 := fun r hr =>
        hg_nonpos r (by rw [← hrs_eq]; exact Multiset.mem_coe.mpr hr)
      have hss0_eq : (↑(ss ++ [(0 : ℝ)]) : Multiset ℝ) = (X * f).roots := by
        have : (↑(ss ++ [(0 : ℝ)]) : Multiset ℝ) = ↑ss + {(0 : ℝ)} := by
          rw [← Multiset.coe_add]; simp
        grind
      have hss_nonpos : ∀ s ∈ ss, s ≤ 0 := fun s hs =>
        hf_nonpos s (by rw [← hss_eq]; exact Multiset.mem_coe.mpr hs)
      have hss0_sorted : (ss ++ [(0 : ℝ)]).Pairwise (· ≤ ·) := by grind
      exact
        ⟨⟨hg₀, hg⟩, by simp_all, rs, ss ++ [(0 : ℝ)], hrs, hss0_sorted,
          hrs_eq, hss0_eq,
          Or.inr ⟨by simp_all, listAlternates_append_zero ss rs hlen hint hrs_nonpos⟩⟩
    · have : ss.length = f.natDegree := by
        rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hf]
      have : rs.length = g.natDegree := by
        rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hg]
      lia
  · -- Backward: Prec g (X * f) → Prec f g
    intro ⟨_, _, ss_g, rs_xf, hss_g, hrs_xf, hss_g_eq, hrs_xf_eq, hcase⟩
    rcases hcase with ⟨hlen, _⟩ | ⟨hlen, halt⟩
    · have : ss_g.length = g.natDegree := by
        rw [← Multiset.coe_card, hss_g_eq, card_roots_of_splits hg]
      have : rs_xf.length = (X * f).natDegree := by
        rw [← Multiset.coe_card, hrs_xf_eq, card_roots_of_splits (by simp_all)]
      lia
    · set ss_f := f.roots.sort (· ≤ ·)
      have hss_f_eq : (↑ss_f : Multiset ℝ) = f.roots := Multiset.sort_eq ..
      have hss_f_sorted : ss_f.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
      have hrs_xf_is : rs_xf = ss_f ++ [(0 : ℝ)] := by
        have hmultiset_eq : (↑rs_xf : Multiset ℝ) = ↑(ss_f ++ [(0 : ℝ)]) := by
          rw [hrs_xf_eq, hXf_roots, ← hss_f_eq, ← Multiset.coe_add]; simp [add_comm]
        have hsorted_concat : (ss_f ++ [(0 : ℝ)]).Pairwise (· ≤ ·) := by
          rw [List.pairwise_append]
          exact ⟨hss_f_sorted, List.pairwise_singleton _ _, fun a ha _ hb => by
            simp only [List.mem_singleton] at hb; rw [hb]
            exact hf_nonpos a (by rw [← hss_f_eq]; exact Multiset.mem_coe.mpr ha)⟩
        exact List.Perm.eq_of_pairwise' hrs_xf hsorted_concat
          (Multiset.coe_eq_coe.mp hmultiset_eq)
      rw [hrs_xf_is] at halt
      have hlen' : ss_f.length + 1 = ss_g.length := by simp_all
      exact
        ⟨⟨hf₀, hf⟩, ⟨hg₀, hg⟩, ss_f, ss_g, hss_f_sorted, hss_g, hss_f_eq,
          hss_g_eq,
          Or.inl ⟨by lia, listInterlaces_of_listAlternates_append_zero ss_f ss_g hlen' halt⟩⟩

theorem prec_sameDegree_to_prec_mul_X_of_roots_nonpos {f g : ℝ[X]}
    (h : Prec f g)
    (hdeg : f.natDegree = g.natDegree)
    (hf_nonpos : ∀ r ∈ f.roots, r ≤ 0)
    (hg_nonpos : ∀ r ∈ g.roots, r ≤ 0) :
    Prec g (X * f) := by
  rcases h with ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hcase⟩
  have hXf_rr : (X * f) ≠ 0 ∧ (X * f).Splits := by simp_all
  have hXf_roots : (X * f).roots = {0} + f.roots := by
    rw [roots_mul (mul_ne_zero X_ne_zero hf.1), roots_X]
  have hss_nonpos : ∀ s ∈ ss, s ≤ 0 := fun s hs =>
    hf_nonpos s (by rw [← hss_eq]; exact Multiset.mem_coe.mpr hs)
  have hss0_sorted : (ss ++ [(0 : ℝ)]).Pairwise (· ≤ ·) := by grind
  have hss0_eq : (↑(ss ++ [(0 : ℝ)]) : Multiset ℝ) = (X * f).roots := by
    have : (↑(ss ++ [(0 : ℝ)]) : Multiset ℝ) = (↑ss : Multiset ℝ) + {(0 : ℝ)} := by
      rw [← Multiset.coe_add]
      simp
    grind
  rcases hcase with ⟨hlen, hint⟩ | ⟨hlen, halt⟩
  · have hss_len : ss.length = f.natDegree := by
      rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hf.2]
    have hrs_len : rs.length = g.natDegree := by
      rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hg.2]
    lia
  · refine ⟨hg, hXf_rr, rs, ss ++ [0], hrs, hss0_sorted, hrs_eq, hss0_eq, Or.inl ?_⟩
    refine ⟨?_, listInterlaces_right_of_listAlternates_append_zero ss rs ?_ halt ?_⟩
    · simp_all
    · lia
    · intro r hr
      exact hg_nonpos r (by rw [← hrs_eq]; exact Multiset.mem_coe.mpr hr)

theorem prec_of_prec_mul_X_sameDegree_of_roots_nonpos {f g : ℝ[X]}
    (h : Prec g (X * f))
    (hdeg : f.natDegree = g.natDegree)
    (hf_nonpos : ∀ r ∈ f.roots, r ≤ 0) :
    Prec f g := by
  rcases h with
    ⟨hg, hXf, ss_g, rs_Xf, hss_g, hrs_Xf, hss_g_eq, hrs_Xf_eq, hshape⟩
  have hf : f ≠ 0 ∧ f.Splits := by simp_all
  set rs_f := f.roots.sort (· ≤ ·)
  have hrs_f_eq : (↑rs_f : Multiset ℝ) = f.roots := Multiset.sort_eq ..
  have hrs_f : rs_f.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hrs_f_nonpos : ∀ r ∈ rs_f, r ≤ 0 :=
    fun r hr => hf_nonpos r (by rw [← hrs_f_eq]; exact Multiset.mem_coe.mpr hr)
  have hrs_f0 : (rs_f ++ [(0 : ℝ)]).Pairwise (· ≤ ·) := by grind
  have hXf_roots : (X * f).roots = {0} + f.roots := by
    rw [roots_mul (mul_ne_zero X_ne_zero hf.1), roots_X]
  have hrs_Xf_is : rs_Xf = rs_f ++ [(0 : ℝ)] := by
    have hmultiset_eq : (↑rs_Xf : Multiset ℝ) = ↑(rs_f ++ [(0 : ℝ)]) := by
      rw [hrs_Xf_eq, hXf_roots, ← hrs_f_eq, ← Multiset.coe_add]
      simp [add_comm]
    exact List.Perm.eq_of_pairwise' hrs_Xf hrs_f0 (Multiset.coe_eq_coe.mp hmultiset_eq)
  have hlen_fg : rs_f.length = ss_g.length := by
    rw [← Multiset.coe_card, hrs_f_eq, card_roots_of_splits hf.2,
      ← Multiset.coe_card, hss_g_eq, card_roots_of_splits hg.2, hdeg]
  rcases hshape with ⟨hlen, hint⟩ | ⟨hlen, _⟩
  · rw [hrs_Xf_is] at hint hlen
    have hlen' : ss_g.length + 1 = (rs_f ++ [(0 : ℝ)]).length := by lia
    have hrs_f0_nonpos : ∀ r ∈ rs_f ++ [(0 : ℝ)], r ≤ 0 := by grind
    have halt0 :
        ListAlternates (rs_f ++ [(0 : ℝ)]) (ss_g ++ [(0 : ℝ)]) :=
      listAlternates_append_zero ss_g (rs_f ++ [(0 : ℝ)]) hlen' hint hrs_f0_nonpos
    have halt : ListAlternates rs_f ss_g :=
      listAlternates_of_append_zero_both rs_f ss_g hlen_fg halt0
    exact ⟨hf, hg, rs_f, ss_g, hrs_f, hss_g, hrs_f_eq, hss_g_eq,
      Or.inr ⟨hlen_fg, halt⟩⟩
  · simp_all

theorem prec_iff_prec_mul_X_of_roots_nonpos {f g : ℝ[X]} (hf : f.Splits) (hg : g.Splits)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hf_nonpos : ∀ r ∈ f.roots, r ≤ 0)
    (hg_nonpos : ∀ r ∈ g.roots, r ≤ 0)
    (hdeg : f.natDegree + 1 = g.natDegree) :
    Prec f g ↔ Prec g (X * f) := by
  have ⟨hfnn, hf₀⟩ := (hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos hf).mpr
    ⟨hf_pos, hf_nonpos⟩
  have ⟨hgnn, hg₀⟩ := (hasNonnegCoeffs_iff_pos_leadingCoeff_and_roots_nonpos hg).mpr
    ⟨hg_pos, hg_nonpos⟩
  exact prec_iff_prec_mul_X hfnn hgnn hf₀ hf hg₀ hg hdeg

/-- Nonnegative-coefficients form of Wagner (3): if `f ≪ g` and both
polynomials have nonnegative coefficients, then `g ≪ X * f`. This packages
the differ-by-1 and same-degree cases under one theorem. -/
theorem prec_mul_X_of_prec_of_nonneg {f g : ℝ[X]}
    (h : Prec f g) (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g) :
    Prec g (X * f) := by
  rcases h with ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hshape⟩
  have hf_nonpos : ∀ r ∈ f.roots, r ≤ 0 := roots_nonpos_of_nonneg_coeffs hf.2 hfnn
  have hg_nonpos : ∀ r ∈ g.roots, r ≤ 0 := roots_nonpos_of_nonneg_coeffs hg.2 hgnn
  rcases hshape with ⟨hlen, hint⟩ | ⟨hlen, halt⟩
  · have hdeg : f.natDegree + 1 = g.natDegree := by
      have hss_len : ss.length = f.natDegree := by
        rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hf.2]
      have hrs_len : rs.length = g.natDegree := by
        rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hg.2]
      lia
    exact (prec_iff_prec_mul_X_of_roots_nonpos hf.2 hg.2 (hfnn.pos_leadingCoeff hf.1)
      (hgnn.pos_leadingCoeff hg.1) hf_nonpos hg_nonpos hdeg).mp
        ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, Or.inl ⟨hlen, hint⟩⟩
  · have hdeg : f.natDegree = g.natDegree := by
      have hss_len : ss.length = f.natDegree := by
        rw [← Multiset.coe_card, hss_eq, card_roots_of_splits hf.2]
      have hrs_len : rs.length = g.natDegree := by
        rw [← Multiset.coe_card, hrs_eq, card_roots_of_splits hg.2]
      lia
    exact
      prec_sameDegree_to_prec_mul_X_of_roots_nonpos
        ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, Or.inr ⟨hlen, halt⟩⟩
        hdeg hf_nonpos hg_nonpos

/-- Zero-aware Wagner (3): if `f ≪₀ g` and both polynomials have nonnegative
coefficients, then `g ≪₀ X * f`. -/
theorem prec0_mul_X_of_prec0 {f g : ℝ[X]}
    (h : Prec0 f g) (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g) :
    Prec0 g (X * f) := by
  rcases h with rfl | rfl | hfg
  · simpa using prec0_zero_right g
  · exact prec0_zero_left (X * f)
  · exact (prec_mul_X_of_prec_of_nonneg hfg hfnn hgnn).toPrec0

theorem prec_mul_X_both_of_roots_nonpos {f g : ℝ[X]} (h : Prec f g)
    (hf_nonpos : ∀ r ∈ f.roots, r ≤ 0)
    (hg_nonpos : ∀ r ∈ g.roots, r ≤ 0) :
    Prec (X * f) (X * g) := by
  rcases h with ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hcase⟩
  have hXf : (X * f) ≠ 0 ∧ (X * f).Splits := by simp_all
  have hXg : (X * g) ≠ 0 ∧ (X * g).Splits := by simp_all
  have hXf_roots : (X * f).roots = {0} + f.roots := by
    rw [roots_mul (mul_ne_zero X_ne_zero hf.1), roots_X]
  have hXg_roots : (X * g).roots = {0} + g.roots := by
    rw [roots_mul (mul_ne_zero X_ne_zero hg.1), roots_X]
  have hss_nonpos : ∀ s ∈ ss, s ≤ 0 := fun s hs =>
    hf_nonpos s (by rw [← hss_eq]; exact Multiset.mem_coe.mpr hs)
  have hrs_nonpos : ∀ r ∈ rs, r ≤ 0 := fun r hr =>
    hg_nonpos r (by rw [← hrs_eq]; exact Multiset.mem_coe.mpr hr)
  have hss0_sorted : (ss ++ [(0 : ℝ)]).Pairwise (· ≤ ·) := by grind
  have hrs0_sorted : (rs ++ [(0 : ℝ)]).Pairwise (· ≤ ·) := by grind
  refine ⟨hXf, hXg, ss ++ [0], rs ++ [0], hss0_sorted, hrs0_sorted, ?_, ?_, ?_⟩
  · have : (↑(ss ++ [(0 : ℝ)]) : Multiset ℝ) = (↑ss : Multiset ℝ) + {(0 : ℝ)} := by
      rw [← Multiset.coe_add]
      simp
    grind
  · have : (↑(rs ++ [(0 : ℝ)]) : Multiset ℝ) = (↑rs : Multiset ℝ) + {(0 : ℝ)} := by
      rw [← Multiset.coe_add]
      simp
    grind
  · rcases hcase with ⟨hlen, hint⟩ | ⟨hlen, halt⟩
    · exact Or.inl
        ⟨by simp_all, listInterlaces_append_zero_both ss rs hlen hint hrs_nonpos⟩
    · exact Or.inr
        ⟨by simp_all, listAlternates_append_zero_both ss rs hlen halt hrs_nonpos⟩

theorem prec_of_prec_mul_X_both_of_roots_nonpos {f g : ℝ[X]}
    (h : Prec (X * f) (X * g))
    (hf_nonpos : ∀ r ∈ f.roots, r ≤ 0)
    (hg_nonpos : ∀ r ∈ g.roots, r ≤ 0) :
    Prec f g := by
  rcases h with ⟨hXf, hXg, ss_xf, rs_xg, hss_xf, hrs_xg, hss_xf_eq, hrs_xg_eq, hcase⟩
  have hf : f ≠ 0 ∧ f.Splits := by simp_all
  have hg : g ≠ 0 ∧ g.Splits := by simp_all
  have hXf_roots : (X * f).roots = {0} + f.roots := by
    rw [roots_mul (mul_ne_zero X_ne_zero hf.1), roots_X]
  have hXg_roots : (X * g).roots = {0} + g.roots := by
    rw [roots_mul (mul_ne_zero X_ne_zero hg.1), roots_X]
  set ss_f := f.roots.sort (· ≤ ·)
  set rs_g := g.roots.sort (· ≤ ·)
  have hss_f_eq : (↑ss_f : Multiset ℝ) = f.roots := Multiset.sort_eq ..
  have hrs_g_eq : (↑rs_g : Multiset ℝ) = g.roots := Multiset.sort_eq ..
  have hss_f_sorted : ss_f.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hrs_g_sorted : rs_g.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hss_f_nonpos : ∀ s ∈ ss_f, s ≤ 0 := fun s hs =>
    hf_nonpos s (by rw [← hss_f_eq]; exact Multiset.mem_coe.mpr hs)
  have hrs_g_nonpos : ∀ r ∈ rs_g, r ≤ 0 := fun r hr =>
    hg_nonpos r (by rw [← hrs_g_eq]; exact Multiset.mem_coe.mpr hr)
  have hss_f0_sorted : (ss_f ++ [(0 : ℝ)]).Pairwise (· ≤ ·) := by grind
  have hrs_g0_sorted : (rs_g ++ [(0 : ℝ)]).Pairwise (· ≤ ·) := by grind
  have hss_xf_is : ss_xf = ss_f ++ [(0 : ℝ)] := by
    have hmultiset_eq : (↑ss_xf : Multiset ℝ) = ↑(ss_f ++ [(0 : ℝ)]) := by
      rw [hss_xf_eq, hXf_roots, ← hss_f_eq, ← Multiset.coe_add]
      simp [add_comm]
    exact List.Perm.eq_of_pairwise' hss_xf hss_f0_sorted (Multiset.coe_eq_coe.mp hmultiset_eq)
  have hrs_xg_is : rs_xg = rs_g ++ [(0 : ℝ)] := by
    have hmultiset_eq : (↑rs_xg : Multiset ℝ) = ↑(rs_g ++ [(0 : ℝ)]) := by
      rw [hrs_xg_eq, hXg_roots, ← hrs_g_eq, ← Multiset.coe_add]
      simp [add_comm]
    exact List.Perm.eq_of_pairwise' hrs_xg hrs_g0_sorted (Multiset.coe_eq_coe.mp hmultiset_eq)
  rcases hcase with ⟨hlen, hint⟩ | ⟨hlen, halt⟩
  · rw [hss_xf_is, hrs_xg_is] at hint hlen
    have hlen' : ss_f.length + 1 = rs_g.length := by simp_all
    exact ⟨hf, hg, ss_f, rs_g, hss_f_sorted, hrs_g_sorted, hss_f_eq, hrs_g_eq,
      Or.inl ⟨hlen', listInterlaces_of_append_zero_both ss_f rs_g hlen' hint⟩⟩
  · rw [hss_xf_is, hrs_xg_is] at halt hlen
    have hlen' : ss_f.length = rs_g.length := by simp_all
    exact ⟨hf, hg, ss_f, rs_g, hss_f_sorted, hrs_g_sorted, hss_f_eq, hrs_g_eq,
      Or.inr ⟨hlen', listAlternates_of_append_zero_both ss_f rs_g hlen' halt⟩⟩

theorem prec_iff_prec_mul_X_both_of_roots_nonpos {f g : ℝ[X]}
    (hf_nonpos : ∀ r ∈ f.roots, r ≤ 0)
    (hg_nonpos : ∀ r ∈ g.roots, r ≤ 0) :
    Prec f g ↔ Prec (X * f) (X * g) :=
  ⟨fun h => prec_mul_X_both_of_roots_nonpos h hf_nonpos hg_nonpos,
    fun h => prec_of_prec_mul_X_both_of_roots_nonpos h hf_nonpos hg_nonpos⟩

theorem prec0_mul_X_both_of_nonneg {f g : ℝ[X]}
    (h : Prec0 f g) (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g) :
    Prec0 (X * f) (X * g) := by
  rcases h with rfl | rfl | hfg
  · simpa using prec0_zero_left (X * g)
  · simpa using prec0_zero_right (X * f)
  · exact
      (prec_mul_X_both_of_roots_nonpos hfg
        (roots_nonpos_of_nonneg_coeffs hfg.1.2 hfnn)
        (roots_nonpos_of_nonneg_coeffs hfg.2.1.2 hgnn)).toPrec0

theorem prec0_of_prec0_mul_X_both_of_nonneg {f g : ℝ[X]}
    (h : Prec0 (X * f) (X * g)) (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g) :
    Prec0 f g := by
  by_cases hf0 : f = 0
  · simpa [hf0] using prec0_zero_left g
  by_cases hg0 : g = 0
  · simpa [hg0] using prec0_zero_right f
  have hXf0 : X * f ≠ 0 := mul_ne_zero X_ne_zero hf0
  have hXg0 : X * g ≠ 0 := mul_ne_zero X_ne_zero hg0
  have hstrict : Prec (X * f) (X * g) := h.toPrec_of_ne hXf0 hXg0
  have hf : f ≠ 0 ∧ f.Splits := isRealRooted_of_X_mul hstrict.1.1 hstrict.1.2
  have hg : g ≠ 0 ∧ g.Splits := isRealRooted_of_X_mul hstrict.2.1.1 hstrict.2.1.2
  exact
    (prec_of_prec_mul_X_both_of_roots_nonpos hstrict
      (roots_nonpos_of_nonneg_coeffs hf.2 hfnn)
      (roots_nonpos_of_nonneg_coeffs hg.2 hgnn)).toPrec0

theorem prec0_iff_prec0_mul_X_both_of_nonneg {f g : ℝ[X]}
    (hfnn : HasNonnegCoeffs f) (hgnn : HasNonnegCoeffs g) :
    Prec0 f g ↔ Prec0 (X * f) (X * g) :=
  ⟨fun h => prec0_mul_X_both_of_nonneg h hfnn hgnn,
    fun h => prec0_of_prec0_mul_X_both_of_nonneg h hfnn hgnn⟩

theorem prec_mul_X_sub_C_both_of_roots_le {f g : ℝ[X]} (r : ℝ) (h : Prec f g)
    (hf_le : ∀ s ∈ f.roots, s ≤ r)
    (hg_le : ∀ s ∈ g.roots, s ≤ r) :
    Prec ((X - C r) * f) ((X - C r) * g) := by
  set f' := f.comp (X + C r)
  set g' := g.comp (X + C r)
  have hfg' : Prec f' g' := by
    simpa [f', g'] using (prec_comp_X_add_C_iff (f := f) (g := g) r).2 h
  have hf'_nonpos : ∀ s ∈ f'.roots, s ≤ 0 := by
    intro s hs
    simp only [f', roots_comp_X_add_C r] at hs
    rcases Multiset.mem_map.mp hs with ⟨t, ht, rfl⟩
    simp_all
  have hg'_nonpos : ∀ s ∈ g'.roots, s ≤ 0 := by
    intro s hs
    simp only [g', roots_comp_X_add_C r] at hs
    rcases Multiset.mem_map.mp hs with ⟨t, ht, rfl⟩
    simp_all
  have hX' : Prec (X * f') (X * g') :=
    prec_mul_X_both_of_roots_nonpos hfg' hf'_nonpos hg'_nonpos
  have htranslated :
      Prec (((X - C r) * f).comp (X + C r)) (((X - C r) * g).comp (X + C r)) := by
    simpa [f', g', mul_comp, sub_comp, X_comp, C_comp, sub_eq_add_neg,
      comp_assoc, add_assoc, add_left_comm, add_comm] using hX'
  exact (prec_comp_X_add_C_iff (f := (X - C r) * f) (g := (X - C r) * g) r).1 htranslated

theorem prec_of_prec_mul_X_sub_C_both_of_roots_le {f g : ℝ[X]} (r : ℝ)
    (h : Prec ((X - C r) * f) ((X - C r) * g))
    (hf_le : ∀ s ∈ f.roots, s ≤ r)
    (hg_le : ∀ s ∈ g.roots, s ≤ r) :
    Prec f g := by
  set f' := f.comp (X + C r)
  set g' := g.comp (X + C r)
  have htranslated :
      Prec (((X - C r) * f).comp (X + C r)) (((X - C r) * g).comp (X + C r)) := by
    simpa using (prec_comp_X_add_C_iff (f := (X - C r) * f) (g := (X - C r) * g) r).2 h
  have hf'_nonpos : ∀ s ∈ f'.roots, s ≤ 0 := by
    intro s hs
    simp only [f', roots_comp_X_add_C r] at hs
    rcases Multiset.mem_map.mp hs with ⟨t, ht, rfl⟩
    simp_all
  have hg'_nonpos : ∀ s ∈ g'.roots, s ≤ 0 := by
    intro s hs
    simp only [g', roots_comp_X_add_C r] at hs
    rcases Multiset.mem_map.mp hs with ⟨t, ht, rfl⟩
    simp_all
  have hfg' : Prec f' g' := by
    have hX' : Prec (X * f') (X * g') := by
      simpa [f', g', mul_comp, sub_comp, X_comp, C_comp, sub_eq_add_neg,
        comp_assoc, add_assoc, add_left_comm, add_comm] using htranslated
    exact prec_of_prec_mul_X_both_of_roots_nonpos hX' hf'_nonpos hg'_nonpos
  exact (prec_comp_X_add_C_iff (f := f) (g := g) r).1 (by lia)

theorem prec_iff_prec_mul_X_sub_C_both_of_roots_le {f g : ℝ[X]} (r : ℝ)
    (hf_le : ∀ s ∈ f.roots, s ≤ r)
    (hg_le : ∀ s ∈ g.roots, s ≤ r) :
    Prec f g ↔ Prec ((X - C r) * f) ((X - C r) * g) :=
  ⟨fun h => prec_mul_X_sub_C_both_of_roots_le r h hf_le hg_le,
    fun h => prec_of_prec_mul_X_sub_C_both_of_roots_le r h hf_le hg_le⟩

theorem prec_mul_X_sub_C_both {f g : ℝ[X]} (r : ℝ) (h : Prec f g) :
    Prec ((X - C r) * f) ((X - C r) * g) := by
  rcases h with ⟨hf, hg, ss, rs, hss, hrs, hss_eq, hrs_eq, hcase⟩
  refine ⟨isRealRooted_mul (isRealRooted_X_sub_C r).1 (isRealRooted_X_sub_C r).2 hf.1 hf.2,
    isRealRooted_mul (isRealRooted_X_sub_C r).1 (isRealRooted_X_sub_C r).2 hg.1 hg.2,
    ss.orderedInsert (· ≤ ·) r, rs.orderedInsert (· ≤ ·) r,
    hss.orderedInsert _ _, hrs.orderedInsert _ _, ?_, ?_, ?_⟩
  · have hinsert :
        (↑(ss.orderedInsert (· ≤ ·) r) : Multiset ℝ) =
          ({r} : Multiset ℝ) + (↑ss : Multiset ℝ) := by
        calc
          (↑(ss.orderedInsert (· ≤ ·) r) : Multiset ℝ) = ↑(r :: ss) :=
            Multiset.coe_eq_coe.mpr (List.perm_orderedInsert (r := (· ≤ ·)) r ss)
          _ = ({r} : Multiset ℝ) + (↑ss : Multiset ℝ) := by
            simp
    have hroots :
        ({r} : Multiset ℝ) + (↑ss : Multiset ℝ) = ((X - C r) * f).roots := by
      rw [hss_eq]
      simpa [roots_X_sub_C] using (roots_mul (mul_ne_zero (X_sub_C_ne_zero r) hf.1)).symm
    lia
  · have hinsert :
        (↑(rs.orderedInsert (· ≤ ·) r) : Multiset ℝ) =
          ({r} : Multiset ℝ) + (↑rs : Multiset ℝ) := by
        calc
          (↑(rs.orderedInsert (· ≤ ·) r) : Multiset ℝ) = ↑(r :: rs) :=
            Multiset.coe_eq_coe.mpr (List.perm_orderedInsert (r := (· ≤ ·)) r rs)
          _ = ({r} : Multiset ℝ) + (↑rs : Multiset ℝ) := by
            simp
    have hroots :
        ({r} : Multiset ℝ) + (↑rs : Multiset ℝ) = ((X - C r) * g).roots := by
      rw [hrs_eq]
      simpa [roots_X_sub_C] using (roots_mul (mul_ne_zero (X_sub_C_ne_zero r) hg.1)).symm
    lia
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

theorem prec_of_prec_mul_X_sub_C_both {f g : ℝ[X]} (r : ℝ)
    (h : Prec ((X - C r) * f) ((X - C r) * g)) :
    Prec f g := by
  rcases h with ⟨hXf, hXg, ss_mul, rs_mul, hss_mul, hrs_mul, hss_mul_eq, hrs_mul_eq, hcase⟩
  have hf0 : f ≠ 0 := right_ne_zero_of_mul hXf.1
  have hg0 : g ≠ 0 := right_ne_zero_of_mul hXg.1
  have hf : (f ≠ 0 ∧ f.Splits) := isRealRooted_of_dvd hXf.1 hXf.2 hf0 (dvd_mul_left f _)
  have hg : (g ≠ 0 ∧ g.Splits) := isRealRooted_of_dvd hXg.1 hXg.2 hg0 (dvd_mul_left g _)
  set ss := f.roots.sort (· ≤ ·)
  set rs := g.roots.sort (· ≤ ·)
  have hss_eq : (↑ss : Multiset ℝ) = f.roots := Multiset.sort_eq ..
  have hrs_eq : (↑rs : Multiset ℝ) = g.roots := Multiset.sort_eq ..
  have hss_sorted : ss.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hrs_sorted : rs.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hss_insert_eq :
      (↑(ss.orderedInsert (· ≤ ·) r) : Multiset ℝ) = ((X - C r) * f).roots := by
    rw [show (↑(ss.orderedInsert (· ≤ ·) r) : Multiset ℝ) =
        ({r} : Multiset ℝ) + (↑ss : Multiset ℝ) by
          calc
            (↑(ss.orderedInsert (· ≤ ·) r) : Multiset ℝ) = ↑(r :: ss) :=
              Multiset.coe_eq_coe.mpr (List.perm_orderedInsert (r := (· ≤ ·)) r ss)
            _ = ({r} : Multiset ℝ) + (↑ss : Multiset ℝ) := by
              simp]
    rw [hss_eq]
    symm
    rw [roots_mul (mul_ne_zero (X_sub_C_ne_zero r) hf.1), roots_X_sub_C]
  have hrs_insert_eq :
      (↑(rs.orderedInsert (· ≤ ·) r) : Multiset ℝ) = ((X - C r) * g).roots := by
    rw [show (↑(rs.orderedInsert (· ≤ ·) r) : Multiset ℝ) =
        ({r} : Multiset ℝ) + (↑rs : Multiset ℝ) by
          calc
            (↑(rs.orderedInsert (· ≤ ·) r) : Multiset ℝ) = ↑(r :: rs) :=
              Multiset.coe_eq_coe.mpr (List.perm_orderedInsert (r := (· ≤ ·)) r rs)
            _ = ({r} : Multiset ℝ) + (↑rs : Multiset ℝ) := by
              simp]
    rw [hrs_eq]
    symm
    rw [roots_mul (mul_ne_zero (X_sub_C_ne_zero r) hg.1), roots_X_sub_C]
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

theorem prec_mul_common_factor {d f g : ℝ[X]} (hd_ne : d ≠ 0) (hd_splits : d.Splits)
    (h : Prec f g) :
    Prec (d * f) (d * g) := by
  have hprod : Prec (((d.roots.map fun a => X - C a).prod) * f)
      (((d.roots.map fun a => X - C a).prod) * g) := by
    induction d.roots using Multiset.induction_on with
    | empty =>
        simp_all
    | @cons a s ih =>
        simpa [Multiset.map_cons, Multiset.prod_cons, mul_assoc, mul_left_comm, mul_comm] using
          prec_mul_X_sub_C_both a ih
  have hlc0 : d.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hd_ne
  have hscaled :
      Prec ((C d.leadingCoeff * (d.roots.map fun a => X - C a).prod) * f)
        ((C d.leadingCoeff * (d.roots.map fun a => X - C a).prod) * g) := by
    have hleft := prec_C_mul_left hprod hlc0
    have hboth := prec_C_mul_right hleft hlc0
    simpa [mul_assoc, mul_left_comm, mul_comm] using hboth
  simpa [C_leadingCoeff_mul_prod_multiset_X_sub_C (card_roots_of_splits hd_splits), mul_assoc]
    using hscaled

theorem prec_iff_prec_mul_X_sub_C_of_roots_le {f g : ℝ[X]} (r : ℝ)
    (hf : f.Splits) (hg : g.Splits)
    (hf_pos : HasPosLeadingCoeff f) (hg_pos : HasPosLeadingCoeff g)
    (hf_le : ∀ s ∈ f.roots, s ≤ r)
    (hg_le : ∀ s ∈ g.roots, s ≤ r)
    (hdeg : f.natDegree + 1 = g.natDegree) :
    Prec f g ↔ Prec g ((X - C r) * f) := by
  set f' := f.comp (X + C r)
  set g' := g.comp (X + C r)
  have hf' : f' ≠ 0 ∧ f'.Splits := by
    simpa [f'] using isRealRooted_comp_X_add_C hf_pos.ne_zero hf r
  have hg' : g' ≠ 0 ∧ g'.Splits := by
    simpa [g'] using isRealRooted_comp_X_add_C hg_pos.ne_zero hg r
  have hf'_pos : HasPosLeadingCoeff f' := by
    simpa [f'] using hf_pos.comp_X_add_C r
  have hg'_pos : HasPosLeadingCoeff g' := by
    simpa [g'] using hg_pos.comp_X_add_C r
  have hf'_nonpos : ∀ s ∈ f'.roots, s ≤ 0 := by
    intro s hs
    simp only [f', roots_comp_X_add_C r] at hs
    rcases Multiset.mem_map.mp hs with ⟨t, ht, rfl⟩
    simp_all
  have hg'_nonpos : ∀ s ∈ g'.roots, s ≤ 0 := by
    intro s hs
    simp only [g', roots_comp_X_add_C r] at hs
    rcases Multiset.mem_map.mp hs with ⟨t, ht, rfl⟩
    simp_all
  have hdeg' : f'.natDegree + 1 = g'.natDegree := by
    simpa [f', g', natDegree_comp] using hdeg
  have hshift :
      Prec f' g' ↔ Prec g' (X * f') :=
    prec_iff_prec_mul_X_of_roots_nonpos hf'.2 hg'.2 hf'_pos hg'_pos hf'_nonpos hg'_nonpos hdeg'
  constructor
  · intro hfg
    have hfg' : Prec f' g' := by
      simpa [f', g'] using (prec_comp_X_add_C_iff (f := f) (g := g) r).2 hfg
    have hgxf' : Prec g' (X * f') := hshift.mp hfg'
    have htranslated : Prec g' (((X - C r) * f).comp (X + C r)) := by
      simpa [f', g', mul_comp, sub_comp, X_comp, C_comp, sub_eq_add_neg,
        comp_assoc, add_assoc, add_left_comm, add_comm] using hgxf'
    exact (prec_comp_X_add_C_iff (f := g) (g := (X - C r) * f) r).1 htranslated
  · intro hgf
    have hgf' : Prec g' (((X - C r) * f).comp (X + C r)) := by
      simpa [g'] using (prec_comp_X_add_C_iff (f := g) (g := (X - C r) * f) r).2 hgf
    have hgxf' : Prec g' (X * f') := by
      simpa [f', g', mul_comp, sub_comp, X_comp, C_comp, sub_eq_add_neg,
        comp_assoc, add_assoc, add_left_comm, add_comm] using hgf'
    have hfg' : Prec f' g' := hshift.mpr hgxf'
    exact (prec_comp_X_add_C_iff (f := f) (g := g) r).1 (by lia)

end
end RealRooted
