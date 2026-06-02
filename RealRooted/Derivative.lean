import RealRooted.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Multiset.Sort

/-!
# Derivative interlacing

The main result is that if `f` is a real-rooted polynomial of degree at least
two, then `f.derivative` is real-rooted and interlaces `f`.
-/

open Polynomial Set

noncomputable section

namespace RealRooted

/-! ## Exact degree of derivative -/

lemma natDegree_derivative_eq {p : ℝ[X]} (hp : 1 ≤ p.natDegree) :
    p.derivative.natDegree = p.natDegree - 1 := by
  apply le_antisymm (natDegree_derivative_le p)
  apply Polynomial.le_natDegree_of_ne_zero
  have h1 : p.natDegree - 1 + 1 = p.natDegree := Nat.sub_add_cancel hp
  rw [coeff_derivative, h1]
  have hcast : (↑(p.natDegree - 1) : ℝ) + 1 = ↑p.natDegree := by
    rw [Nat.cast_sub hp]; ring
  rw [hcast]
  exact mul_ne_zero
    (leadingCoeff_ne_zero.mpr (by intro h; simp [h] at hp))
    (Nat.cast_ne_zero.mpr (by lia))

lemma derivative_ne_zero {f : ℝ[X]} (hdeg : 2 ≤ f.natDegree) :
    f.derivative ≠ 0 := by
  intro h
  have := natDegree_derivative_eq (show 1 ≤ f.natDegree by lia)
  rw [h, natDegree_zero] at this; lia

lemma HasNonnegCoeffs.derivative {p : ℝ[X]} (hp : HasNonnegCoeffs p) :
    HasNonnegCoeffs p.derivative := by
  intro n
  rw [coeff_derivative]
  exact mul_nonneg (hp (n + 1)) (by positivity)

lemma nonnegCoeffs_derivative {p : ℝ[X]} (hp : HasNonnegCoeffs p) :
    HasNonnegCoeffs p.derivative :=
  hp.derivative

lemma hasPosLeadingCoeff_derivative {f : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f) (hdeg : 1 ≤ f.natDegree) :
    HasPosLeadingCoeff f.derivative := by
  unfold HasPosLeadingCoeff at hf_pos ⊢
  rw [leadingCoeff, natDegree_derivative_eq hdeg, coeff_derivative]
  rw [Nat.sub_add_cancel hdeg, coeff_natDegree] at *
  have hdeg_pos : 0 < (f.natDegree : ℝ) := by
    exact_mod_cast hdeg
  nlinarith

lemma coeff_one_sub_X_mul_derivative (p : ℝ[X]) (m : Nat) :
    ((1 - X) * p.derivative).coeff m =
      ((m + 1 : ℝ) * p.coeff (m + 1)) - ((m : ℝ) * p.coeff m) := by
  cases m with
  | zero =>
      simp [coeff_derivative]
  | succ m =>
      rw [sub_mul, one_mul, coeff_sub, coeff_X_mul, coeff_derivative, coeff_derivative]
      norm_num
      ring

/-! ## Rolle's theorem for polynomials -/

theorem exists_root_derivative_between {p : ℝ[X]} {a b : ℝ} (hab : a < b)
    (ha : p.IsRoot a) (hb : p.IsRoot b) :
    ∃ c, a < c ∧ c < b ∧ p.derivative.IsRoot c := by
  have hcont : ContinuousOn (fun x => p.eval x) (Icc a b) :=
    p.continuous.continuousOn
  have hfab : p.eval a = p.eval b := by
    simp only [IsRoot.def] at ha hb; rw [ha, hb]
  have hderiv : ∀ x ∈ Ioo a b, HasDerivAt (fun x => p.eval x) (p.derivative.eval x) x :=
    fun x _ => p.hasDerivAt x
  obtain ⟨c, hc_mem, hc_eq⟩ := exists_hasDerivAt_eq_zero hab hcont hfab hderiv
  exact ⟨c, hc_mem.1, hc_mem.2, hc_eq⟩

theorem isRoot_derivative_of_rootMultiplicity_ge_two {p : ℝ[X]} {r : ℝ}
    (hm : 2 ≤ p.rootMultiplicity r) :
    p.derivative.IsRoot r := by
  have hp0 : p ≠ 0 := by intro h; simp [h] at hm
  have hdvd : (X - C r) ^ 2 ∣ p := (le_rootMultiplicity_iff hp0).mp hm
  have hdvd' : (X - C r) ^ (2 - 1) ∣ p.derivative :=
    pow_sub_one_dvd_derivative_of_pow_dvd hdvd
  simp only [Nat.reduceSubDiff, pow_one] at hdvd'
  exact dvd_iff_isRoot.mp hdvd'

/-! ## Interleaving construction -/

/-- Recursively produce a root of `f'` between each consecutive pair in `rs`. -/
noncomputable def mkInterleaving (f : ℝ[X]) :
    (rs : List ℝ) → (hrs : ∀ r ∈ rs, f.IsRoot r) → List ℝ
  | [], _ | [_], _ => []
  | r₁ :: r₂ :: rest, hrs =>
    have hr₁ : f.IsRoot r₁ := hrs r₁ (.head _)
    have hr₂ : f.IsRoot r₂ := hrs r₂ (.tail _ (.head _))
    have hrest : ∀ r ∈ r₂ :: rest, f.IsRoot r := fun r hr => hrs r (.tail _ hr)
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
    simp only [List.length_cons]; lia

/-! ## Properties of the construction

Key change: we generalize the multiset condition to `≤` (sub-multiset)
so that the induction goes through when we drop the first element. -/

/-- Each constructed element is a root of f' in [r₁, r₂].
    Uses sub-multiset condition `≤` to handle repeated roots. -/
lemma mkInterleaving_spec (f : ℝ[X]) :
    ∀ (rs : List ℝ) (hrs : ∀ r ∈ rs, f.IsRoot r)
      (_hsorted : rs.Pairwise (· ≤ ·))
      (_hsub : (↑rs : Multiset ℝ) ≤ f.roots),
    (∀ s ∈ mkInterleaving f rs hrs, f.derivative.IsRoot s) ∧
    ListInterlaces (mkInterleaving f rs hrs) rs
  | [], _, _, _ | [_], _, _, _ => by
    refine ⟨?_, ?_⟩ <;> simp [mkInterleaving, ListInterlaces]
  | r₁ :: r₂ :: rest, hrs, hsorted, hsub => by
    have hr₁r₂ : r₁ ≤ r₂ := List.rel_of_pairwise_cons hsorted (.head _)
    have hrest : ∀ r ∈ r₂ :: rest, f.IsRoot r := fun r hr => hrs r (.tail _ hr)
    have hsorted_tail := (List.pairwise_cons.mp hsorted).2
    -- The tail is also a sub-multiset of f.roots
    have hsub_tail : (↑(r₂ :: rest) : Multiset ℝ) ≤ f.roots := by
      apply le_trans _ hsub
      change (↑(r₂ :: rest) : Multiset ℝ) ≤ (↑(r₁ :: r₂ :: rest) : Multiset ℝ)
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
        · exact (exists_root_derivative_between hlt
            (hrs r₁ (.head _)) (hrs r₂ (.tail _ (.head _)))).choose_spec.2.2
        · -- r₁ = r₂, repeated root
          have heq : r₁ = r₂ := le_antisymm hr₁r₂ (not_lt.mp hlt)
          have hcount_list
              : 2 ≤ Multiset.count r₁ (↑(r₁ :: r₂ :: rest) : Multiset ℝ) := by
            simp [heq]
          have hcount : 2 ≤ Multiset.count r₁ f.roots :=
            le_trans hcount_list ((Multiset.le_iff_count.mp hsub) r₁)
          rw [count_roots] at hcount
          exact isRoot_derivative_of_rootMultiplicity_ge_two hcount
      · exact ih.1 s hs
    · -- ListInterlaces
      refine ⟨?_, ?_, ih.2⟩
      · -- r₁ ≤ s
        split_ifs with hlt
        · exact le_of_lt (exists_root_derivative_between hlt
            (hrs r₁ (.head _)) (hrs r₂ (.tail _ (.head _)))).choose_spec.1
        · exact le_refl _
      · -- s ≤ r₂
        split_ifs with hlt
        · exact le_of_lt (exists_root_derivative_between hlt
            (hrs r₁ (.head _)) (hrs r₂ (.tail _ (.head _)))).choose_spec.2.1
        · exact hr₁r₂

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
    exact List.pairwise_cons.mpr ⟨fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hs₁s₂
      · exact le_trans hs₁s₂ (List.rel_of_pairwise_cons ih hx'), ih⟩
  | _ :: _ :: _, _ :: _ :: [], _, hint => by
    -- rs has exactly 2 elements, ss has ≥ 2 — impossible by ListInterlaces structure
    simp [ListInterlaces] at hint
  | _ :: _ :: _, _ :: [], _, hint => by simp [ListInterlaces] at hint
  | _ :: _ :: _, [], _, hint => by simp [ListInterlaces] at hint

/-! ## Sub-multiset relation -/

/-- All elements of the interleaving of `r₁ :: rest` are ≥ r₁. -/
private lemma mkInterleaving_ge (f : ℝ[X]) :
    ∀ (r₁ : ℝ) (rest : List ℝ) (hrs : ∀ r ∈ r₁ :: rest, f.IsRoot r)
      (_hsorted : (r₁ :: rest).Pairwise (· ≤ ·))
      (_hsub : (↑(r₁ :: rest) : Multiset ℝ) ≤ f.roots),
    ∀ x ∈ mkInterleaving f (r₁ :: rest) hrs, r₁ ≤ x
  | _, [], _, _, _ => by simp [mkInterleaving]
  | r₁, r₂ :: rest', hrs, hsorted, hsub => by
    intro x hx
    simp only [mkInterleaving, List.mem_cons] at hx
    have hr₁r₂ : r₁ ≤ r₂ := List.rel_of_pairwise_cons hsorted (.head _)
    rcases hx with rfl | hx
    · -- x is the head element
      split_ifs with hlt
      · exact le_of_lt (exists_root_derivative_between hlt
          (hrs r₁ (.head _)) (hrs r₂ (.tail _ (.head _)))).choose_spec.1
      · exact le_refl _
    · -- x is in the recursive tail
      have hrest := fun r hr => hrs r (.tail _ hr)
      have hsorted_tail := (List.pairwise_cons.mp hsorted).2
      have hsub_tail : (↑(r₂ :: rest') : Multiset ℝ) ≤ f.roots := by
        apply le_trans _ hsub
        change (↑(r₂ :: rest') : Multiset ℝ) ≤ (↑(r₁ :: r₂ :: rest') : Multiset ℝ)
        simp [Multiset.le_iff_count, Multiset.coe_count, List.count_cons]
      exact le_trans hr₁r₂ (mkInterleaving_ge f r₂ rest' hrest hsorted_tail hsub_tail x hx)

/-- The sub-multiset relation: `↑ss ≤ f'.roots`. -/
lemma mkInterleaving_sub_multiset (f : ℝ[X])
    (hdeg : 2 ≤ f.natDegree) :
    ∀ (rs : List ℝ) (hrs : ∀ r ∈ rs, f.IsRoot r)
      (_hsorted : rs.Pairwise (· ≤ ·))
      (_hsub : (↑rs : Multiset ℝ) ≤ f.roots),
    -- (A) sub-multiset of f'.roots
    (↑(mkInterleaving f rs hrs) : Multiset ℝ) ≤ f.derivative.roots ∧
    -- (B) count bound for elements in rs
    (∀ a, a ∈ (↑rs : Multiset ℝ) →
      (↑(mkInterleaving f rs hrs) : Multiset ℝ).count a + 1 ≤ (↑rs : Multiset ℝ).count a)
  | [], _, _, _ | [_], _, _, _ => ⟨Multiset.zero_le _, by simp [mkInterleaving]⟩
  | r₁ :: r₂ :: rest, hrs, hsorted, hsub => by
    have hr₁r₂ : r₁ ≤ r₂ := List.rel_of_pairwise_cons hsorted (.head _)
    have hrest : ∀ r ∈ r₂ :: rest, f.IsRoot r := fun r hr => hrs r (.tail _ hr)
    have hsorted_tail := (List.pairwise_cons.mp hsorted).2
    have hsub_tail : (↑(r₂ :: rest) : Multiset ℝ) ≤ f.roots := by
      apply le_trans _ hsub
      change (↑(r₂ :: rest) : Multiset ℝ) ≤ (↑(r₁ :: r₂ :: rest) : Multiset ℝ)
      simp [Multiset.le_iff_count, Multiset.coe_count, List.count_cons]
    have ih := mkInterleaving_sub_multiset f hdeg (r₂ :: rest) hrest hsorted_tail hsub_tail
    have hf'_ne : f.derivative ≠ 0 := derivative_ne_zero hdeg
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
        rw [Multiset.mem_coe]; intro hmem
        linarith [(exists_root_derivative_between hlt (hrs r₁ (.head _))
          (hrs r₂ (.tail _ (.head _)))).choose_spec.2.1, hge_tail _ hmem])
    constructor
    · -- (A): s ::ₘ ↑ss' ≤ f'.roots
      change s ::ₘ ↑(mkInterleaving f (r₂ :: rest) hrest) ≤ f.derivative.roots
      -- s is a root of f' (proved in mkInterleaving_spec)
      have hs_root : f.derivative.IsRoot s :=
        (mkInterleaving_spec f (r₁ :: r₂ :: rest) hrs hsorted
          (le_of_eq rfl |>.trans hsub)).1 s (by rw [hunfold]; exact .head _)
      have hs_mem : s ∈ f.derivative.roots := (mem_roots hf'_ne).mpr hs_root
      by_cases hlt : r₁ < r₂
      · -- Rolle: s ∉ ↑ss' (all tail ≥ r₂ > s), use cons_le_of_notMem
        have hspec := (exists_root_derivative_between hlt
          (hrs r₁ (.head _)) (hrs r₂ (.tail _ (.head _)))).choose_spec
        have hs_notin : s ∉ (↑(mkInterleaving f (r₂ :: rest) hrest) : Multiset ℝ) := by
          rw [Multiset.mem_coe]; intro hmem
          have : s = _ := dif_pos hlt
          linarith [hge_tail _ hmem, (this ▸ hspec).2.1]
        rw [Multiset.cons_le_of_notMem hs_notin]
        exact ⟨hs_mem, ih.1⟩
      · -- Multiplicity: s = r₁ = r₂, use count argument via IH(B)
        have hr_eq : r₁ = r₂ := le_antisymm hr₁r₂ (not_lt.mp hlt)
        have hs : s = r₁ := dif_neg hlt
        rw [Multiset.le_iff_count]; intro a
        rw [Multiset.count_cons]
        split_ifs with heq
        · -- s = a: use IH(B) + multiplicity chain
          -- heq : s = a (or a = s depending on count_cons)
          have ih_B := ih.2 a (by
            have : a = r₂ := by rw [heq, hs, hr_eq]
            rw [this]; exact Multiset.mem_coe.mpr (.head _))
          -- count a (r₁ :: r₂ :: rest) ≤ rootMultiplicity a f
          have hcount_full : (↑(r₁ :: r₂ :: rest) : Multiset ℝ).count a ≤
            f.rootMultiplicity a := by
            rw [← count_roots]; exact Multiset.count_le_of_le a hsub
          -- (r₁ :: r₂ :: rest).count a = 1 + (r₂ :: rest).count a since r₁ = s = a
          have : (↑(r₁ :: r₂ :: rest) : Multiset ℝ).count a =
            (↑(r₂ :: rest) : Multiset ℝ).count a + 1 := by
            change (r₁ ::ₘ ↑(r₂ :: rest)).count a = _
            rw [Multiset.count_cons]
            split_ifs with h
            · ring
            · exfalso; exact h (show a = r₁ by rw [heq, hs])
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
        have hr_eq : r₁ = r₂ := by
          rcases lt_or_eq_of_le hr₁r₂ with hlt | h; swap
          · exact h
          -- Rolle: r₁ < s, but s = a = r₁, contradiction
          have hspec := (exists_root_derivative_between hlt
            (hrs r₁ (.head _)) (hrs r₂ (.tail _ (.head _)))).choose_spec
          have : r₁ < s := by rw [show s = _ from dif_pos hlt]; exact hspec.1
          linarith [show s = r₁ from by rw [← heq, hr₁a]]
        have ih_B := ih.2 a (by
          rw [heq, show s = r₁ from dif_neg (not_lt.mpr (ge_of_eq hr_eq)), hr_eq]
          exact Multiset.mem_coe.mpr (.head _))
        lia
      · -- a = s, a ≠ r₁: vacuous
        rw [if_pos heq, if_neg hr₁a]; exfalso
        rcases ha with rfl | ha_tail
        · exact hr₁a rfl
        · by_cases hlt : r₁ < r₂
          · -- Rolle: s < r₂ ≤ all tail elements, so s ∉ tail
            have hspec := (exists_root_derivative_between hlt
              (hrs r₁ (.head _)) (hrs r₂ (.tail _ (.head _)))).choose_spec
            have : a < r₂ := by
              have : s = _ := dif_pos hlt; rw [heq, this]; exact hspec.2.1
            have : r₂ ≤ a := by
              have hmem := Multiset.mem_coe.mp ha_tail
              rcases List.mem_cons.mp hmem with h | h
              · exact h ▸ le_refl _
              · exact List.rel_of_pairwise_cons hsorted_tail h
            linarith
          · exact hr₁a (show a = r₁ by rw [heq]; exact dif_neg hlt)
      · -- a ≠ s, a = r₁
        rw [if_neg heq, if_pos hr₁a]
        by_cases ha2 : a ∈ (↑(r₂ :: rest) : Multiset ℝ)
        · have ih_B := ih.2 a ha2; lia
        · have hlt : r₁ < r₂ := by
            rcases lt_or_eq_of_le hr₁r₂ with h | h; · exact h
            · exfalso; rw [hr₁a, h] at ha2; exact ha2 (Multiset.mem_coe.mpr (.head _))
          have : (↑(mkInterleaving f (r₂ :: rest) hrest) : Multiset ℝ).count a = 0 :=
            Multiset.count_eq_zero.mpr (by
              rw [Multiset.mem_coe]; intro hmem; linarith [hge_tail _ hmem])
          rw [this]; lia
      · -- a ≠ s, a ≠ r₁
        rw [if_neg heq, if_neg hr₁a]
        rcases ha with rfl | ha_tail
        · exact absurd rfl hr₁a
        · have ih_B := ih.2 a ha_tail; lia

/-! ## Main theorem -/

/-- **Derivative interlacing**: if `f` is real-rooted of degree ≥ 2,
    then `f.derivative` interlaces `f`. -/
theorem derivative_interlaces {f : ℝ[X]} (hf : f ≠ 0 ∧ f.roots.card = f.natDegree)
    (hdeg : 2 ≤ f.natDegree) :
    Interlaces f.derivative f := by
  -- Sort the roots of f
  set rs := f.roots.sort (· ≤ ·) with hrs_def
  have hrs_sorted : rs.Pairwise (· ≤ ·) := Multiset.pairwise_sort ..
  have hrs_multiset : (↑rs : Multiset ℝ) = f.roots := Multiset.sort_eq ..
  have hrs_length : rs.length = f.natDegree := by
    rw [hrs_def, Multiset.length_sort, hf.2]
  have hrs_root : ∀ r ∈ rs, f.IsRoot r := by
    intro r hr; rw [Multiset.mem_sort] at hr; rwa [mem_roots hf.1] at hr
  -- Construct interleaving
  set ss := mkInterleaving f rs hrs_root
  have hss_length : ss.length = f.natDegree - 1 := by
    rw [mkInterleaving_length]; lia
  -- Properties from the construction
  have hsub_rs : (↑rs : Multiset ℝ) ≤ f.roots := le_of_eq hrs_multiset
  have hspec := mkInterleaving_spec f rs hrs_root hrs_sorted hsub_rs
  have hss_roots : ∀ s ∈ ss, f.derivative.IsRoot s := hspec.1
  have hss_interlaces : ListInterlaces ss rs := hspec.2
  -- Sub-multiset relation
  have hsub : (↑ss : Multiset ℝ) ≤ f.derivative.roots :=
    (mkInterleaving_sub_multiset f hdeg rs hrs_root hrs_sorted hsub_rs).1
  -- Degree and cardinality → f' is real-rooted
  have hf'_ne : f.derivative ≠ 0 := derivative_ne_zero hdeg
  have hf'_deg : f.derivative.natDegree = f.natDegree - 1 :=
    natDegree_derivative_eq (by lia)
  have hf'_card : f.derivative.roots.card = f.derivative.natDegree := by
    apply le_antisymm (card_roots' _)
    calc f.derivative.natDegree
      _ = f.natDegree - 1 := hf'_deg
      _ = ss.length := hss_length.symm
      _ = (↑ss : Multiset ℝ).card := (Multiset.coe_card ss).symm
      _ ≤ f.derivative.roots.card := Multiset.card_le_card hsub
  have hf'_rr : (f.derivative ≠ 0 ∧
    f.derivative.roots.card = f.derivative.natDegree) := ⟨hf'_ne, hf'_card⟩
  -- Multiset equality (sub-multiset + same cardinality)
  have hss_eq : (↑ss : Multiset ℝ) = f.derivative.roots :=
    Multiset.eq_of_le_of_card_le hsub (by rw [Multiset.coe_card, hss_length, hf'_card, hf'_deg])
  -- Sortedness from interleaving
  have hss_sorted : ss.Pairwise (· ≤ ·) :=
    sorted_of_listInterlaces ss rs hrs_sorted hss_interlaces
  -- Assemble
  exact ⟨hf, hf'_rr, by lia,
    rs, ss, hrs_sorted, hss_sorted, hrs_multiset, hss_eq, hss_interlaces⟩

end RealRooted
