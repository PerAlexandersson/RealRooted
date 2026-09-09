import RealRooted.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Multiset.Sort
import RealRooted.Derivative.RootCounting

open Polynomial Set

noncomputable section

namespace RealRooted

/-! ## Interleaving construction -/

/-- Recursively produce a root of `f'` between each consecutive pair in `rs`. -/
noncomputable def mkInterleaving (f : ℝ[X]) :
    (rs : List ℝ) → (hrs : ∀ r ∈ rs, f.IsRoot r) → List ℝ
  | [], _ | [_], _ => []
  | r₁ :: r₂ :: rest, hrs =>
    have hr₁ : f.IsRoot r₁ := hrs r₁ (.head _)
    have hr₂ : f.IsRoot r₂ := hrs r₂ (.tail _ (.head _))
    have hrest : ∀ r ∈ r₂ :: rest, f.IsRoot r :=
      List.forall_mem_of_forall_mem_cons hrs
    let s := if hlt : r₁ < r₂ then
      (exists_root_derivative_between hlt hr₁ hr₂).choose
    else r₁
    s :: mkInterleaving f (r₂ :: rest) hrest

lemma mkInterleaving_length (f : ℝ[X]) :
    ∀ (rs : List ℝ) (hrs : ∀ r ∈ rs, f.IsRoot r),
    (mkInterleaving f rs hrs).length = rs.length - 1
  | [], _ | [_], _ => by simp [mkInterleaving]
  | _ :: r₂ :: rest, hrs => by
    simp only [mkInterleaving, List.length_cons]
    rw [mkInterleaving_length f (r₂ :: rest)]
    simp

/-! ## Properties of the construction

Key change: we generalize the multiset condition to `≤` (sub-multiset)
so that the induction goes through when we drop the first element. -/

/-- Each constructed element is a root of f' in [r₁, r₂].
    Uses sub-multiset condition `≤` to handle repeated roots. -/
lemma mkInterleaving_spec (f : ℝ[X]) :
    ∀ (rs : List ℝ) (hrs : ∀ r ∈ rs, f.IsRoot r)
      (_ : rs.Pairwise (· ≤ ·))
      (_ : (↑rs : Multiset ℝ) ≤ f.roots),
    (∀ s ∈ mkInterleaving f rs hrs, f.derivative.IsRoot s) ∧
    ListInterlaces (mkInterleaving f rs hrs) rs
  | [], _, _, _ | [_], _, _, _ => by
    refine ⟨?_, ?_⟩ <;> simp [mkInterleaving, ListInterlaces]
  | r₁ :: r₂ :: rest, hrs, hsorted, hsub => by
    have hr₁r₂ : r₁ ≤ r₂ := List.rel_of_pairwise_cons hsorted (.head _)
    have hrest : ∀ r ∈ r₂ :: rest, f.IsRoot r :=
      List.forall_mem_of_forall_mem_cons hrs
    have hsorted_tail := (List.pairwise_cons.mp hsorted).2
    -- The tail is also a sub-multiset of f.roots
    have hsub_tail : (↑(r₂ :: rest) : Multiset ℝ) ≤ f.roots := by
      apply le_trans _ hsub
      simp [Multiset.le_iff_count, Multiset.coe_count, List.count_cons]
    -- Recursive result
    have ih := mkInterleaving_spec f (r₂ :: rest) hrest hsorted_tail hsub_tail
    simp only [mkInterleaving]
    constructor
    · -- All elements are roots of f'
      intro s hs
      simp only [List.mem_cons] at hs
      rcases hs with rfl | hs
      · -- First element: Rolle or multiplicity
        split_ifs with hlt
        · grind
        · -- r₁ = r₂, repeated root
          have heq : r₁ = r₂ := le_antisymm hr₁r₂ (not_lt.mp hlt)
          have hcount_list
              : 2 ≤ Multiset.count r₁ (↑(r₁ :: r₂ :: rest) : Multiset ℝ) := by
            simp [heq]
          have hcount : 2 ≤ Multiset.count r₁ f.roots :=
            le_trans hcount_list ((Multiset.le_iff_count.mp hsub) r₁)
          rw [count_roots] at hcount
          exact isRoot_derivative_of_rootMultiplicity_ge_two hcount
      · simp_all
    · -- ListInterlaces
      refine ⟨?_, ?_, ih.2⟩
      · -- r₁ ≤ s
        grind
      · -- s ≤ r₂
        grind

/-! ## Sortedness from interleaving -/

/-- If `ss` interleaves with sorted `rs`, then `ss` is sorted. -/
lemma sorted_of_listInterlaces :
    ∀ (ss rs : List ℝ),
    rs.Pairwise (· ≤ ·) →
    ListInterlaces ss rs →
    ss.Pairwise (· ≤ ·)
  | [], _, _, _ => List.Pairwise.nil
  | [_], _, _, _ => List.pairwise_singleton _ _
  | s₁ :: s₂ :: ss', r₁ :: r₂ :: r₃ :: rs', hrs, hint => by
    -- hint : r₁ ≤ s₁ ∧ s₁ ≤ r₂ ∧ ListInterlaces (s₂ :: ss') (r₂ :: r₃ :: rs')
    obtain ⟨_, hs₁r₂, hint_tail⟩ := hint
    -- From hint_tail: r₂ ≤ s₂ ∧ ...
    have hr₂s₂ : r₂ ≤ s₂ := hint_tail.1
    have hs₁s₂ : s₁ ≤ s₂ := le_trans hs₁r₂ hr₂s₂
    have hrs_tail : (r₂ :: r₃ :: rs').Pairwise (· ≤ ·) :=
      (List.pairwise_cons.mp hrs).2
    have ih := sorted_of_listInterlaces (s₂ :: ss') (r₂ :: r₃ :: rs') hrs_tail hint_tail
    grind
  | _ :: _ :: _, _ :: _ :: [], _, hint => by
    -- rs has exactly 2 elements, ss has ≥ 2 — impossible by ListInterlaces structure
    simp [ListInterlaces] at hint
  | _ :: _ :: _, _ :: [], _, hint => by simp [ListInterlaces] at hint
  | _ :: _ :: _, [], _, hint => by simp [ListInterlaces] at hint

/-! ## Sub-multiset relation -/

/-- All elements of the interleaving of `r₁ :: rest` are ≥ r₁. -/
private lemma mkInterleaving_ge (f : ℝ[X]) :
    ∀ (r₁ : ℝ) (rest : List ℝ) (hrs : ∀ r ∈ r₁ :: rest, f.IsRoot r)
      (_ : (r₁ :: rest).Pairwise (· ≤ ·))
      (_ : (↑(r₁ :: rest) : Multiset ℝ) ≤ f.roots),
    ∀ x ∈ mkInterleaving f (r₁ :: rest) hrs, r₁ ≤ x
  | _, [], _, _, _ => by simp [mkInterleaving]
  | r₁, r₂ :: rest', hrs, hsorted, hsub => by
    intro x hx
    simp only [mkInterleaving, List.mem_cons] at hx
    have hr₁r₂ : r₁ ≤ r₂ := List.rel_of_pairwise_cons hsorted (.head _)
    rcases hx with rfl | hx
    · -- x is the head element
      grind
    · -- x is in the recursive tail
      have hrest : ∀ r ∈ r₂ :: rest', f.IsRoot r :=
        List.forall_mem_of_forall_mem_cons hrs
      have hsorted_tail := (List.pairwise_cons.mp hsorted).2
      have hsub_tail : (↑(r₂ :: rest') : Multiset ℝ) ≤ f.roots := by
        apply le_trans _ hsub
        simp [Multiset.le_iff_count, Multiset.coe_count, List.count_cons]
      exact le_trans hr₁r₂ (mkInterleaving_ge f r₂ rest' hrest hsorted_tail hsub_tail x hx)

/-- The sub-multiset relation: `↑ss ≤ f'.roots`. -/
lemma mkInterleaving_sub_multiset (f : ℝ[X])
    (hdeg : 2 ≤ f.natDegree) :
    ∀ (rs : List ℝ) (hrs : ∀ r ∈ rs, f.IsRoot r)
      (_ : rs.Pairwise (· ≤ ·))
      (_ : (↑rs : Multiset ℝ) ≤ f.roots),
    -- (A) sub-multiset of f'.roots
    (↑(mkInterleaving f rs hrs) : Multiset ℝ) ≤ f.derivative.roots ∧
    -- (B) count bound for elements in rs
    (∀ a, a ∈ (↑rs : Multiset ℝ) →
      (↑(mkInterleaving f rs hrs) : Multiset ℝ).count a + 1 ≤ (↑rs : Multiset ℝ).count a)
  | [], _, _, _ | [_], _, _, _ => ⟨Multiset.zero_le _, by simp [mkInterleaving]⟩
  | r₁ :: r₂ :: rest, hrs, hsorted, hsub => by
    have hr₁r₂ : r₁ ≤ r₂ := List.rel_of_pairwise_cons hsorted (.head _)
    have hrest : ∀ r ∈ r₂ :: rest, f.IsRoot r :=
      List.forall_mem_of_forall_mem_cons hrs
    have hsorted_tail := (List.pairwise_cons.mp hsorted).2
    have hsub_tail : (↑(r₂ :: rest) : Multiset ℝ) ≤ f.roots := by
      apply le_trans _ hsub
      simp [Multiset.le_iff_count, Multiset.coe_count, List.count_cons]
    have ih := mkInterleaving_sub_multiset f hdeg (r₂ :: rest) hrest hsorted_tail hsub_tail
    have hf'_ne : f.derivative ≠ 0 :=
      Polynomial.derivative_ne_zero.mpr (by lia)
    have hge_tail : ∀ x ∈ mkInterleaving f (r₂ :: rest) hrest, r₂ ≤ x :=
      mkInterleaving_ge f r₂ rest hrest hsorted_tail hsub_tail
    -- Definitionally unfold mkInterleaving via let + rfl
    let s : ℝ := if hlt : r₁ < r₂ then
      (exists_root_derivative_between hlt (hrs r₁ (.head _))
        (hrs r₂ (.tail _ (.head _)))).choose
    else r₁
    have hunfold : mkInterleaving f (r₁ :: r₂ :: rest) hrs =
      s :: mkInterleaving f (r₂ :: rest) hrest := rfl
    rw [hunfold]
    -- Now goal is about ↑(s :: mkInterleaving f (r₂ :: rest) hrest)
    -- Helper: count of s in the tail
    have htail_count_s_rolle (hlt : r₁ < r₂) :
        (↑(mkInterleaving f (r₂ :: rest) hrest) : Multiset ℝ).count
          (exists_root_derivative_between hlt (hrs r₁ (.head _))
            (hrs r₂ (.tail _ (.head _)))).choose = 0 :=
      Multiset.count_eq_zero.mpr (by
        rw [Multiset.mem_coe]; grind)
    constructor
    · -- (A): s ::ₘ ↑ss' ≤ f'.roots
      change s ::ₘ ↑(mkInterleaving f (r₂ :: rest) hrest) ≤ f.derivative.roots
      -- s is a root of f' (proved in mkInterleaving_spec)
      have hs_root : f.derivative.IsRoot s :=
        (mkInterleaving_spec f (r₁ :: r₂ :: rest) hrs hsorted
          (le_of_eq rfl |>.trans hsub)).1 s (by simp_all)
      have hs_mem : s ∈ f.derivative.roots := (mem_roots hf'_ne).mpr hs_root
      by_cases hlt : r₁ < r₂
      · -- Rolle: s ∉ ↑ss' (all tail ≥ r₂ > s), use cons_le_of_notMem
        have hspec := (exists_root_derivative_between hlt
          (hrs r₁ (.head _)) (hrs r₂ (.tail _ (.head _)))).choose_spec
        have hs_notin : s ∉ (↑(mkInterleaving f (r₂ :: rest) hrest) : Multiset ℝ) := by
          rw [Multiset.mem_coe]; grind
        rw [Multiset.cons_le_of_notMem hs_notin]
        lia
      · -- Multiplicity: s = r₁ = r₂, use count argument via IH(B)
        have hr_eq : r₁ = r₂ := le_antisymm hr₁r₂ (not_lt.mp hlt)
        have hs : s = r₁ := dif_neg hlt
        rw [Multiset.le_iff_count]; intro a
        rw [Multiset.count_cons]
        split_ifs with heq
        · -- s = a: use IH(B) + multiplicity chain
          -- heq : s = a (or a = s depending on count_cons)
          have ih_B := ih.2 a (by
            simp_all)
          -- count a (r₁ :: r₂ :: rest) ≤ rootMultiplicity a f
          have hcount_full : (↑(r₁ :: r₂ :: rest) : Multiset ℝ).count a ≤
            f.rootMultiplicity a := by rw [← count_roots]; exact Multiset.count_le_of_le a hsub
          -- (r₁ :: r₂ :: rest).count a = 1 + (r₂ :: rest).count a since r₁ = s = a
          have : (↑(r₁ :: r₂ :: rest) : Multiset ℝ).count a =
            (↑(r₂ :: rest) : Multiset ℝ).count a + 1 := by simp_all
          rw [this] at hcount_full
          have hmult := rootMultiplicity_sub_one_le_derivative_rootMultiplicity_of_ne_zero
            f a hf'_ne
          -- Goal involves Multiset.count and rootMultiplicity — close with lia
          simp only [count_roots] at *; lia
        · -- s ≠ a: use IH directly
          simp only [add_zero]; exact Multiset.count_le_of_le a ih.1
    · -- (B): count bound: ∀ a ∈ ↑rs, count a ss + 1 ≤ count a rs
      intro a ha
      change a ∈ (r₁ ::ₘ ↑(r₂ :: rest) : Multiset ℝ) at ha
      rw [Multiset.mem_cons] at ha
      change (s ::ₘ ↑(mkInterleaving f (r₂ :: rest) hrest)).count a + 1 ≤
        (r₁ ::ₘ ↑(r₂ :: rest) : Multiset ℝ).count a
      rw [Multiset.count_cons, Multiset.count_cons]
      by_cases heq : a = s <;> by_cases hr₁a : a = r₁
      · -- a = s, a = r₁
        rw [if_pos heq, if_pos hr₁a]
        have hr_eq : r₁ = r₂ := by grind
        simp_all
      · -- a = s, a ≠ r₁: vacuous
        rw [if_pos heq, if_neg hr₁a]; exfalso
        rcases ha with rfl | ha_tail
        · lia
        · by_cases hlt : r₁ < r₂
          · -- Rolle: s < r₂ ≤ all tail elements, so s ∉ tail
            have hspec := (exists_root_derivative_between hlt
              (hrs r₁ (.head _)) (hrs r₂ (.tail _ (.head _)))).choose_spec
            have : a < r₂ := by lia
            have : r₂ ≤ a := by
              have hmem := Multiset.mem_coe.mp ha_tail
              rcases List.mem_cons.mp hmem with h | h <;> simp_all
            linarith
          · lia
      · -- a ≠ s, a = r₁
        rw [if_neg heq, if_pos hr₁a]
        by_cases ha2 : a ∈ (↑(r₂ :: rest) : Multiset ℝ)
        · grind
        · have hlt : r₁ < r₂ := by lia
          have : (↑(mkInterleaving f (r₂ :: rest) hrest) : Multiset ℝ).count a = 0 :=
            Multiset.count_eq_zero.mpr (by
              rw [Multiset.mem_coe]; grind)
          lia
      · -- a ≠ s, a ≠ r₁
        grind

/-- The recursively selected witness is the penultimate entry of `ss`.
The product statement permits repeated entries and endpoint equality. -/
private lemma exists_penultimate_listInterlaces_prod_nonneg :
    ∀ {ss rs : List ℝ},
      ss.Pairwise (· ≤ ·) →
      ListInterlaces ss rs →
      2 ≤ ss.length →
      ∃ c ∈ ss, 0 ≤ (rs.map (c - ·)).prod := by
  intro ss
  induction ss with
  | nil =>
      intro rs _ _ hlen
      simp at hlen
  | cons s ss ih =>
      cases ss with
      | nil =>
          intro rs _ _ hlen
          simp at hlen
      | cons t ts =>
          intro rs hss hint _
          cases rs with
          | nil =>
              simp [ListInterlaces] at hint
          | cons r₁ rs =>
              cases rs with
              | nil =>
                  simp [ListInterlaces] at hint
              | cons r₂ rest =>
                  obtain ⟨hr₁s, hsr₂, htail⟩ := hint
                  by_cases hts : ts = []
                  · subst ts
                    have hrest_len : rest.length = 1 := by
                      simpa using
                        (listInterlaces_cons_length_eq htail).symm
                    obtain ⟨r₃, rfl⟩ :=
                      List.length_eq_one_iff.mp hrest_len
                    change r₂ ≤ t ∧ t ≤ r₃ ∧ True at htail
                    obtain ⟨hr₂t, htr₃, _⟩ := htail
                    refine ⟨s, by simp, ?_⟩
                    have h₁ : 0 ≤ s - r₁ :=
                      sub_nonneg.mpr hr₁s
                    have h₂ : s - r₂ ≤ 0 :=
                      sub_nonpos.mpr hsr₂
                    have h₃ : s - r₃ ≤ 0 :=
                      sub_nonpos.mpr
                        (hsr₂.trans (hr₂t.trans htr₃))
                    simpa [mul_assoc] using
                      mul_nonneg h₁
                        (mul_nonneg_of_nonpos_of_nonpos h₂ h₃)
                  · have htail_len : 2 ≤ (t :: ts).length := by grind
                    have hss_cons := List.pairwise_cons.mp hss
                    obtain ⟨c, hc, hcprod⟩ :=
                      ih hss_cons.2 htail htail_len
                    have hsc : s ≤ c :=
                      hss_cons.1 c hc
                    have hr₁c : r₁ ≤ c :=
                      hr₁s.trans hsc
                    refine
                      ⟨c, List.mem_cons_of_mem s hc, ?_⟩
                    simpa [List.map, List.prod_cons] using
                      mul_nonneg (sub_nonneg.mpr hr₁c) hcprod

/-! ## Main theorem -/

/-- **Derivative interlacing**: if `f` is real-rooted of degree ≥ 2,
    then `f.derivative` interlaces `f`. -/
theorem derivative_interlaces {f : ℝ[X]} (hf : f.Splits) (hdeg : 2 ≤ f.natDegree) :
    Interlaces f.derivative f := by
  -- Sort the roots of f
  set rs := f.roots.sort (· ≤ ·) with hrs_def
  have hrs_sorted : rs.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hrs_multiset : (↑rs : Multiset ℝ) = f.roots := Multiset.sort_eq ..
  have hrs_length : rs.length = f.natDegree := by
    rw [hrs_def, Multiset.length_sort, card_roots_of_splits hf]
  have hrs_root : ∀ r ∈ rs, f.IsRoot r := by simp_all
  -- Construct interleaving
  set ss := mkInterleaving f rs hrs_root
  have hss_length : ss.length = f.natDegree - 1 := by rw [mkInterleaving_length]; lia
  -- Properties from the construction
  have hsub_rs : (↑rs : Multiset ℝ) ≤ f.roots := le_of_eq hrs_multiset
  have hspec := mkInterleaving_spec f rs hrs_root hrs_sorted hsub_rs
  have hss_roots : ∀ s ∈ ss, f.derivative.IsRoot s := hspec.1
  have hss_interlaces : ListInterlaces ss rs := hspec.2
  -- Sub-multiset relation
  have hsub : (↑ss : Multiset ℝ) ≤ f.derivative.roots :=
    (mkInterleaving_sub_multiset f hdeg rs hrs_root hrs_sorted hsub_rs).1
  -- Degree and cardinality → f' is real-rooted
  have hf'_ne : f.derivative ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr (by lia)
  have hf'_card : f.derivative.roots.card = f.derivative.natDegree := by
    apply le_antisymm (card_roots' _)
    calc f.derivative.natDegree
      _ = f.natDegree - 1 := f.natDegree_derivative
      _ = ss.length := hss_length.symm
      _ = (↑ss : Multiset ℝ).card := (Multiset.coe_card ss).symm
      _ ≤ f.derivative.roots.card := Multiset.card_le_card hsub
  have hf'_rr : (f.derivative ≠ 0 ∧ f.derivative.Splits) :=
    ⟨hf'_ne, splits_of_card_roots hf'_card⟩
  -- Multiset equality (sub-multiset + same cardinality)
  have hss_eq : (↑ss : Multiset ℝ) = f.derivative.roots :=
    Multiset.eq_of_le_of_card_le hsub
      (le_of_eq (by rw [hf'_card, f.natDegree_derivative, ← hss_length,
        ← Multiset.coe_card]))
  -- Sortedness from interleaving
  have hss_sorted : ss.Pairwise (· ≤ ·) :=
    sorted_of_listInterlaces ss rs hrs_sorted hss_interlaces
  -- Assemble
  exact ⟨⟨by rintro rfl; simp at hf'_ne, hf⟩, hf'_rr, by rw [f.natDegree_derivative]; lia,
    rs, ss, hrs_sorted, hss_sorted, hrs_multiset, hss_eq, hss_interlaces⟩

/-- A positive-leading splitting polynomial of degree at least four is
nonnegative at the penultimate derivative-root occurrence.

Repeated roots are retained: if the selected derivative root is also a root
of `p`, the conclusion is equality. -/
theorem exists_derivative_root_eval_nonneg_of_four_le_natDegree
    {p : ℝ[X]} (hp : p.Splits) (hp_pos : HasPosLeadingCoeff p)
    (hdeg : 4 ≤ p.natDegree) :
    ∃ c ∈ p.derivative.roots, 0 ≤ p.eval c := by
  obtain
      ⟨_, hpd, _, rs, ss, _, hss_sorted, hrs_eq, hss_eq, hint⟩ :=
    derivative_interlaces hp (by lia)
  have hss_length : ss.length = p.derivative.natDegree := by
    calc
      ss.length = (↑ss : Multiset ℝ).card := by simp
      _ = p.derivative.roots.card := congrArg Multiset.card hss_eq
      _ = p.derivative.natDegree := card_roots_of_splits hpd.2
  have hss_two : 2 ≤ ss.length := by
    rw [hss_length, p.natDegree_derivative]
    lia
  obtain ⟨c, hc, hcprod⟩ :=
    exists_penultimate_listInterlaces_prod_nonneg
      hss_sorted hint hss_two
  have hc_roots : c ∈ p.derivative.roots := by
    rw [← hss_eq]
    exact Multiset.mem_coe.mpr hc
  refine ⟨c, hc_roots, ?_⟩
  have heval :
      p.eval c = p.leadingCoeff * (rs.map (c - ·)).prod := by
    rw [hp.eval_eq_prod_roots c, ← hrs_eq]
    rfl
  rw [heval]
  exact mul_nonneg hp_pos.le hcprod

/-- A nonzero degree-zero real-rooted polynomial precedes a nonzero
degree-one real-rooted polynomial. -/
lemma prec_degree_zero_right_of_degree_one
    {f g : ℝ[X]}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits) (hg_ne : g ≠ 0) (hg_splits : g.Splits)
    (hf_deg0 : f.natDegree = 0) (hg_deg1 : g.natDegree = 1) :
    Prec f g := by
  obtain ⟨r, hr_eq⟩ : ∃ r, g.roots = {r} := by
    apply Multiset.card_eq_one.mp
    simpa [hg_deg1] using card_roots_of_splits hg_splits
  have hroots_f : f.roots = 0 := by
    apply Multiset.card_eq_zero.mp
    rw [card_roots_of_splits hf_splits, hf_deg0]
  refine ⟨⟨hf_ne, hf_splits⟩, ⟨hg_ne, hg_splits⟩, [], [r], by simp,
    List.pairwise_singleton _ _, ?_, ?_, ?_⟩
  · simp [hroots_f]
  · simp [hr_eq]
  · exact Or.inl ⟨by simp, by simp [ListInterlaces]⟩

/-- The derivative of any nonconstant positive-leading real-rooted polynomial
interlaces the original polynomial, including the degree-one boundary case. -/
lemma interlaces_derivative_of_pos_natDegree
    {f : ℝ[X]}
    (hf_ne : f ≠ 0) (hf_splits : f.Splits) (hf_pos : HasPosLeadingCoeff f)
    (hdeg : 1 ≤ f.natDegree) :
    Interlaces f.derivative f := by
  by_cases hdeg1 : f.natDegree = 1
  · have hf'_pos : HasPosLeadingCoeff f.derivative := hf_pos.derivative (by lia)
    have hf'_ne : f.derivative ≠ 0 := by simp_all
    have hf'_deg0 : f.derivative.natDegree = 0 := by simp [hdeg1, f.natDegree_derivative]
    have hf'_rr : f.derivative ≠ 0 ∧ f.derivative.Splits :=
      ⟨hf'_ne, Polynomial.Splits.of_natDegree_eq_zero hf'_deg0⟩
    exact
      (prec_degree_zero_right_of_degree_one hf'_rr.1 hf'_rr.2 hf_ne hf_splits
        hf'_deg0 hdeg1).toInterlaces (by lia)
  · exact derivative_interlaces hf_splits (by lia)

end RealRooted
