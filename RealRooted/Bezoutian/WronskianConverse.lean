import Mathlib.Analysis.Polynomial.Basic
import RealRooted.Bezoutian.ComplexRoots

/-!
# Wronskian positivity and strict interlacing

Root-sign and gap arguments converting global Wronskian positivity to strict
same-degree proper position, together with the higher-degree converse from a
positive Bezout matrix.
-/

open Polynomial Matrix

noncomputable section

namespace RealRooted

lemma Polynomial.no_repeated_root_of_wronskian_pos {p q : ℝ[X]}
    (hW : ∀ t : ℝ, 0 < q.derivative.eval t * p.eval t - q.eval t * p.derivative.eval t)
    (r : ℝ) (hp_root : p.IsRoot r) : ¬ p.derivative.IsRoot r := by
  intro hd
  have := hW r
  simp_all

lemma Polynomial.roots_nodup_of_splits_and_simple {p : ℝ[X]}
    (h_simple : ∀ r : ℝ, p.IsRoot r → ¬ p.derivative.IsRoot r) :
    p.roots.Nodup := by
  rw [Multiset.nodup_iff_count_le_one]
  intro r
  rw [count_roots]
  by_cases hr : p.IsRoot r
  · exact Nat.le_of_not_lt fun h ↦ h_simple r hr <| by
      simpa [hr] using Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity h
  · rw [rootMultiplicity_eq_zero hr]
    simp

lemma StrictMono.fin_interlacing_of_root_between {n : ℕ}
    (s r : Fin (n + 1) → ℝ) (hs : StrictMono s)
    (h_root_below : s 0 < r 0)
    (h_between : ∀ k : Fin n,
    ∃ j : Fin (n + 1), r k.castSucc < s j ∧ s j < r k.succ) :
    (∀ k : Fin (n + 1), s k < r k) ∧
    (∀ (i j : Fin (n + 1)), i < j → r i < s j) := by
  have h_second_part : ∀ i j : Fin (n + 1), i < j → r i < s j := by
    intro i
    refine Fin.reverseInduction ?_ ?_ i
    · grind
    · intro i IH j hj
      obtain ⟨k, hk₁, hk₂⟩ := h_between i
      by_cases h_cases : j ≤ k
      · grind
      · exact lt_of_lt_of_le hk₁ (hs.monotone (not_le.mp h_cases).le)
  refine ⟨fun k ↦ ?_, h_second_part⟩
  refine Fin.inductionOn k ?_ ?_
  · simp_all
  · intro k ih
    obtain ⟨j, hj₁, hj₂⟩ := h_between k
    refine lt_of_le_of_lt (hs.monotone (Nat.succ_le_of_lt ?_)) hj₂
    by_contra hnot
    have h_le : j ≤ k.castSucc := not_lt.mp hnot
    have : s j ≤ s k.castSucc := hs.monotone h_le
    grind

lemma Polynomial.roots_sort_eq_ofFn {n : ℕ} {p : ℝ[X]}
    (hp_ne : p ≠ 0) (hp_splits : p.Splits) (hp_deg : p.natDegree = n)
    (hp_nodup : p.roots.Nodup)
    (s : Fin n → ℝ) (hs : StrictMono s)
    (hs_surj : ∀ x ∈ p.roots, ∃ k, s k = x) :
    p.roots.sort (· ≤ ·) = List.ofFn s := by
  have h_eq_multiset : p.roots = Multiset.ofList (List.ofFn s) := by
    refine Multiset.eq_of_le_of_card_le (Multiset.le_iff_count.mpr ?_) ?_
    · intro x
      by_cases hx : x ∈ p.roots <;> simp_all
    · rw [Polynomial.splits_iff_card_roots] at hp_splits
      simp_all
  rw [h_eq_multiset, List.ofFn_eq_map]
  refine List.mergeSort_eq_self (· ≤ ·) ?_
  simp only [List.pairwise_iff_get, List.get_eq_getElem, List.getElem_map,
    List.getElem_finRange, Fin.cast_mk]
  exact fun i j hij ↦ hs.monotone hij.le

lemma StrictPrecSameDegree.of_fin_interlacing {n : ℕ}
    (s r : Fin n → ℝ) (hs : StrictMono s) (hr : StrictMono r)
    (hint : ∀ k : Fin n, s k < r k)
    (hint' : ∀ (i j : Fin n), i < j → r i < s j)
    (p q : ℝ[X])
    (hp_ne : p ≠ 0) (hq_ne : q ≠ 0)
    (hp_splits : p.Splits) (hq_splits : q.Splits)
    (hp_deg : p.natDegree = n) (hq_deg : q.natDegree = n)
    (hp_roots_nodup : p.roots.Nodup) (hq_roots_nodup : q.roots.Nodup)
    (hs_surj : ∀ x ∈ p.roots, ∃ k, s k = x)
    (hr_surj : ∀ x ∈ q.roots, ∃ k, r k = x) :
    StrictPrecSameDegree p q :=
  ⟨⟨hp_ne, hp_splits⟩, ⟨hq_ne, hq_splits⟩, hp_deg ▸ hq_deg ▸ rfl,
    Polynomial.roots_sort_eq_ofFn hp_ne hp_splits hp_deg hp_roots_nodup s hs hs_surj ▸
    Polynomial.roots_sort_eq_ofFn hq_ne hq_splits hq_deg hq_roots_nodup r hr hr_surj ▸
    List.Interleaves.ofFn s r hint hint'⟩

lemma tendsto_eval_mul_neg_one_pow_atBot {n : ℕ} {p : ℝ[X]}
    (hp_pos : HasPosLeadingCoeff p) (hp_deg : p.natDegree = n + 1) :
    Filter.Tendsto (fun x ↦ p.eval x * (-1) ^ (n + 1)) Filter.atBot Filter.atTop := by
  have h_leading :
      0 < Polynomial.leadingCoeff (p.comp (-Polynomial.X)) * (-1) ^ (n + 1) := by
    rw [Polynomial.comp_neg_X_leadingCoeff_eq, hp_deg]
    rcases Nat.even_or_odd (n + 1) with h | h <;>
      rw [h.neg_one_pow] <;> norm_num <;> exact hp_pos
  have h_tendsto_comp :
      Filter.Tendsto
        (fun x ↦ Polynomial.eval x
          (p.comp (-Polynomial.X) * Polynomial.C ((-1) ^ (n + 1))))
        Filter.atTop Filter.atTop := by
    rw [Polynomial.tendsto_atTop_iff_leadingCoeff_nonneg]
    rw [Polynomial.degree_mul, Polynomial.degree_C] <;> norm_num [h_leading]
    refine ⟨Polynomial.natDegree_pos_iff_degree_pos.mp ?_, ?_⟩
    · simp [*]
    · simpa [hp_deg] using h_leading.le
  have h_tendsto_neg :
      Filter.Tendsto (fun x ↦ p.eval (-x) * (-1) ^ (n + 1)) Filter.atTop Filter.atTop := by
    simp_all
  convert h_tendsto_neg.comp Filter.tendsto_neg_atBot_atTop using 2
  simp

lemma mul_neg_of_pos_mul_neg_one_pow_succ {n : ℕ} {a b : ℝ}
    (ha : 0 < a * (-1) ^ n) (hb : 0 < b * (-1) ^ (n + 1)) :
    b * a < 0 := by
  have h_pow : (-1 : ℝ) ^ (n + 1) = -((-1) ^ n) := by
    rw [pow_succ]
    ring
  have h_sq : ((-1 : ℝ) ^ n) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    simp
  rw [h_pow] at hb
  nlinarith [hb, ha, h_sq]

lemma exists_index_eq_of_mem_roots {n : ℕ} {p : ℝ[X]} (s : Fin n → ℝ) (hs : StrictMono s)
    (hs_root : ∀ k, p.IsRoot (s k)) (hp_ne : p ≠ 0) (hp_deg : p.natDegree ≤ n)
    (x : ℝ) (hx : x ∈ p.roots) : ∃ i, s i = x := by
  have h_subset : Finset.image s Finset.univ ⊆ p.roots.toFinset := by
    rw [Finset.image_subset_iff]
    intro k _
    exact Multiset.mem_toFinset.mpr (mem_roots'.mpr ⟨hp_ne, hs_root k⟩)
  have h_card : p.roots.toFinset.card ≤ (Finset.image s Finset.univ).card := by
    rw [Finset.card_image_of_injective _ hs.injective, Finset.card_univ, Fintype.card_fin]
    exact le_trans (Multiset.toFinset_card_le _) (Polynomial.card_roots' p |>.trans hp_deg)
  have h_eq := Finset.eq_of_subset_of_card_le h_subset h_card
  have hx_in : x ∈ Finset.image s Finset.univ := by rwa [h_eq, Multiset.mem_toFinset]
  rcases Finset.mem_image.mp hx_in with ⟨i, _, hi⟩
  exact ⟨i, hi⟩

lemma prod_sub_eq_neg_one_pow_mul_prod_abs {m : ℕ}
    (r : Fin m → ℝ) (hr : StrictMono r) (k : Fin m) :
    ∏ j ∈ Finset.univ.erase k, (r k - r j) = (-1) ^ (m - 1 - k.val) *
      ∏ j ∈ Finset.univ.erase k, |r k - r j| := by
  have h_prod_sign_abs : ∏ j ∈ Finset.univ.erase k, (r k - r j) =
      ∏ j ∈ Finset.univ.erase k,
        (-1) ^ (if k < j then 1 else 0) * |r k - r j| := by
    refine Finset.prod_congr rfl fun j hj ↦ ?_
    split_ifs with hjk
    · simp only [pow_one, neg_mul, one_mul]
      rw [abs_of_neg (sub_neg.mpr (hr hjk))]
      ring
    · simp only [pow_zero, one_mul]
      rw [abs_of_nonneg (sub_nonneg.mpr (hr.monotone (not_lt.mp hjk)))]
  rw [h_prod_sign_abs, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  congr 2
  have : (Finset.univ.erase k).filter (fun x ↦ k < x) = Finset.Ioi k := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, Finset.mem_Ioi, and_true]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨ne_of_gt h, h⟩⟩
  rw [Finset.sum_boole, this, Fin.card_Ioi]
  rfl

lemma sign_p_at_root_of_wronskian_pos {n : ℕ}
    {p q : ℝ[X]} (hq_pos : HasPosLeadingCoeff q) (hq_deg : q.natDegree = n + 1)
    (hW : ∀ t : ℝ, 0 < q.derivative.eval t * p.eval t - q.eval t * p.derivative.eval t)
    (r : Fin (n + 1) → ℝ) (hr_mono : StrictMono r) (hr_roots : ∀ k, q.IsRoot (r k))
    (k : Fin (n + 1)) : 0 < p.eval (r k) * (-1) ^ (n - k.val) := by
  have hq_eq : q = C q.leadingCoeff * ∏ j : Fin (n + 1),
    (X - C (r j)) := by
    convert Polynomial.splits_eq_C_mul_prod _ _ _ _ _
    · exact leadingCoeff_ne_zero.mp hq_pos.ne'
    · simp_all
    · simp_all
    · exact hr_mono.injective
  have h_eval_deriv :
      q.derivative.eval (r k) =
        q.leadingCoeff * ∏ j ∈ Finset.erase Finset.univ k, (r k - r j) := by
    conv_lhs => rw [hq_eq]
    exact Polynomial.eval_derivative_C_mul_prod_X_sub_C_univ_at_root
      q.leadingCoeff r k
  have h_sign_change_prod :
      0 < p.eval (r k) * ∏ j ∈ Finset.erase Finset.univ k, (r k - r j) := by
    have := hW (r k)
    have hq_eval : q.eval (r k) = 0 := hr_roots k
    rw [hq_eval, zero_mul, sub_zero, h_eval_deriv, mul_assoc] at this
    have h_prod := pos_of_mul_pos_right this hq_pos.le
    rwa [mul_comm] at h_prod
  have h_prod_sign := prod_sub_eq_neg_one_pow_mul_prod_abs r hr_mono k
  have : n + 1 - 1 - k.val = n - k.val := rfl
  rw [this] at h_prod_sign
  rw [h_prod_sign] at h_sign_change_prod
  nlinarith [show 0 < ∏ j ∈ Finset.univ.erase k, |r k - r j| from
    Finset.prod_pos fun j hj ↦ abs_pos.mpr <| sub_ne_zero.mpr <|
      hr_mono.injective.ne (Finset.ne_of_mem_erase hj).symm]

lemma sign_change_p_of_wronskian_pos {n : ℕ}
    {p q : ℝ[X]} (hq_pos : HasPosLeadingCoeff q) (hq_deg : q.natDegree = n + 1)
    (hW : ∀ t : ℝ, 0 < q.derivative.eval t * p.eval t - q.eval t * p.derivative.eval t)
    (r : Fin (n + 1) → ℝ) (hr_mono : StrictMono r) (hr_roots : ∀ k, q.IsRoot (r k))
    (k : Fin n) : p.eval (r (Fin.castSucc k)) * p.eval (r (Fin.succ k)) < 0 := by
  have h_sign_change_k := sign_p_at_root_of_wronskian_pos hq_pos hq_deg hW
    r hr_mono hr_roots (Fin.castSucc k)
  have h_sign_change_succ := sign_p_at_root_of_wronskian_pos hq_pos hq_deg hW
    r hr_mono hr_roots (Fin.succ k)
  have h_eq : n - (Fin.castSucc k : ℕ) = n - (Fin.succ k : ℕ) + 1 := by
    have : (Fin.castSucc k : ℕ) = k.val := rfl
    have : (Fin.succ k : ℕ) = k.val + 1 := rfl
    lia
  rw [h_eq] at h_sign_change_k
  exact mul_neg_of_pos_mul_neg_one_pow_succ h_sign_change_succ h_sign_change_k

lemma Polynomial.exists_root_between_roots_of_wronskian_pos {n : ℕ}
    {p q : ℝ[X]} (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = n + 1) (hq_deg : q.natDegree = n + 1)
    (hW : ∀ t : ℝ, 0 < q.derivative.eval t * p.eval t -
    q.eval t * p.derivative.eval t)
    (r : Fin (n + 1) → ℝ) (hr_mono : StrictMono r) (hr_roots : ∀ k, q.IsRoot (r k)) :
    (∃ x, p.IsRoot x ∧ x < r 0) ∧
    (∀ k : Fin n, ∃ x, p.IsRoot x ∧ r k.castSucc < x ∧ x < r k.succ) := by
  constructor
  · have h_sign_change_zero : 0 < p.eval (r 0) * (-1) ^ n :=
      sign_p_at_root_of_wronskian_pos hq_pos hq_deg hW r hr_mono hr_roots 0
    have h_tendsto_bot :
        Filter.Tendsto (fun x ↦ p.eval x * (-1) ^ (n + 1)) Filter.atBot Filter.atTop :=
      tendsto_eval_mul_neg_one_pow_atBot hp_pos hp_deg
    have h_sign_change_bot : ∃ x : ℝ, x < r 0 ∧ 0 < p.eval x * (-1) ^ (n + 1) :=
      (Filter.Eventually.and (Filter.eventually_lt_atBot (r 0))
        (h_tendsto_bot.eventually_gt_atTop 0)).exists
    obtain ⟨x, hx₁, hx₂⟩ := h_sign_change_bot
    have h_ivt : ∃ c ∈ Set.Ioo x (r 0), p.eval c = 0 := by
      have h_cont : ContinuousOn (fun t ↦ p.eval t) (Set.Icc x (r 0)) :=
        p.continuous.continuousOn
      have h_sign_change_ends : p.eval x * p.eval (r 0) < 0 :=
        mul_neg_of_pos_mul_neg_one_pow_succ h_sign_change_zero hx₂
      rw [mul_neg_iff] at h_sign_change_ends
      rcases h_sign_change_ends with h | h
      · exact intermediate_value_Ioo' hx₁.le h_cont (Set.mem_Ioo.mpr ⟨h.2, h.1⟩)
      · exact intermediate_value_Ioo hx₁.le h_cont (Set.mem_Ioo.mpr ⟨h.1, h.2⟩)
    rcases h_ivt with ⟨c, hc_in, hc_root⟩
    exact ⟨c, hc_root, hc_in.2⟩
  · intro k
    have h_ivt : ∃ x ∈ Set.Ioo (r (Fin.castSucc k)) (r (Fin.succ k)), p.eval x = 0 := by
      have h_cont :
          ContinuousOn (fun x ↦ p.eval x)
            (Set.Icc (r (Fin.castSucc k)) (r (Fin.succ k))) :=
        p.continuous.continuousOn
      have := sign_change_p_of_wronskian_pos hq_pos hq_deg hW r hr_mono hr_roots k
      rw [mul_neg_iff] at this
      have hle : r (Fin.castSucc k) ≤ r (Fin.succ k) :=
        hr_mono.monotone (Nat.le_succ _)
      rcases this with h | h
      · exact intermediate_value_Ioo' hle h_cont (Set.mem_Ioo.mpr ⟨h.2, h.1⟩)
      · exact intermediate_value_Ioo hle h_cont (Set.mem_Ioo.mpr ⟨h.1, h.2⟩)
    rcases h_ivt with ⟨c, hc_in, hc_root⟩
    exact ⟨c, hc_root, hc_in⟩

lemma sign_p_at_root_of_wronskian_pos' {n : ℕ}
    {p q : ℝ[X]} (hq_pos : HasPosLeadingCoeff q)
    (hq_deg : q.natDegree = n)
    (hW : ∀ t : ℝ, 0 < p.derivative.eval t * q.eval t - p.eval t * q.derivative.eval t)
    (r : Fin n → ℝ) (hr_mono : StrictMono r) (hr_roots : ∀ k, q.IsRoot (r k))
    (k : Fin n) : 0 < p.eval (r k) * (-1) ^ (n - k.val) := by
  have hq_eq : q = C q.leadingCoeff * ∏ j : Fin n, (X - C (r j)) :=
    Polynomial.splits_eq_C_mul_prod (leadingCoeff_ne_zero.mp hq_pos.ne')
      hq_deg r hr_roots hr_mono.injective
  have h_eval_deriv :
      q.derivative.eval (r k) =
        q.leadingCoeff * ∏ j ∈ Finset.erase Finset.univ k, (r k - r j) := by
    conv_lhs => rw [hq_eq]
    exact Polynomial.eval_derivative_C_mul_prod_X_sub_C_univ_at_root q.leadingCoeff r k
  have h_W_val :
      0 < p.derivative.eval (r k) * q.eval (r k) - p.eval (r k) * q.derivative.eval (r k) :=
    hW (r k)
  rw [hr_roots k, mul_zero, zero_sub, h_eval_deriv] at h_W_val
  have h_prod_neg : p.eval (r k) *
      (∏ j ∈ Finset.erase Finset.univ k, (r k - r j)) < 0 := by
    have : 0 < q.leadingCoeff := hq_pos
    nlinarith [h_W_val, this]
  have h_prod_sign :
      ∏ j ∈ Finset.univ.erase k, (r k - r j) =
        (-1) ^ (n - 1 - k.val) * ∏ j ∈ Finset.univ.erase k, |r k - r j| :=
    prod_sub_eq_neg_one_pow_mul_prod_abs r hr_mono k
  have h_abs_pos : 0 < ∏ j ∈ Finset.univ.erase k, |r k - r j| :=
    Finset.prod_pos fun j hj ↦ abs_pos.mpr <| sub_ne_zero.mpr <|
      hr_mono.injective.ne (Finset.ne_of_mem_erase hj).symm
  rw [h_prod_sign] at h_prod_neg
  have : n - k.val = (n - 1 - k.val) + 1 := by lia
  rw [this, pow_succ]
  nlinarith [h_abs_pos, h_prod_neg]

lemma sign_change_p_of_wronskian_pos' {n : ℕ}
    {p q : ℝ[X]} (hq_pos : HasPosLeadingCoeff q)
    (hq_deg : q.natDegree = n)
    (hW : ∀ t : ℝ, 0 < p.derivative.eval t * q.eval t - p.eval t * q.derivative.eval t)
    (r : Fin n → ℝ) (hr_mono : StrictMono r) (hr_roots : ∀ k, q.IsRoot (r k))
    (k : Fin n) (hk : k.val + 1 < n) :
    p.eval (r k) * p.eval (r ⟨k.val + 1, hk⟩) < 0 := by
  have hk₀ : 0 < p.eval (r k) * (-1) ^ (n - k.val) :=
    sign_p_at_root_of_wronskian_pos' hq_pos hq_deg hW r hr_mono hr_roots k
  have hk₁ : 0 < p.eval (r ⟨k.val + 1, hk⟩) * (-1) ^ (n - (k.val + 1)) :=
    sign_p_at_root_of_wronskian_pos' hq_pos hq_deg hW r hr_mono hr_roots ⟨k.val + 1, hk⟩
  have : n - k.val = (n - (k.val + 1)) + 1 := by lia
  rw [this] at hk₀
  exact mul_neg_of_pos_mul_neg_one_pow_succ hk₁ hk₀

lemma exists_root_between_consecutive_of_wronskian_pos {n : ℕ}
    {p q : ℝ[X]} (hq_pos : HasPosLeadingCoeff q)
    (hq_deg : q.natDegree = n)
    (hW : ∀ t : ℝ, 0 < p.derivative.eval t * q.eval t - p.eval t * q.derivative.eval t)
    (r : Fin n → ℝ) (hr_mono : StrictMono r) (hr_roots : ∀ k, q.IsRoot (r k))
    (k : Fin n) (hk : k.val + 1 < n) :
    ∃ x, p.IsRoot x ∧ r k < x ∧ x < r ⟨k.val + 1, hk⟩ := by
  have : p.eval (r k) * p.eval (r ⟨k.val + 1, hk⟩) < 0 :=
    sign_change_p_of_wronskian_pos' hq_pos hq_deg hW r hr_mono hr_roots k hk
  have h_lt : r k < r ⟨k.val + 1, hk⟩ := hr_mono (Nat.lt_succ_self k.val)
  have h_cont : ContinuousOn (fun t ↦ p.eval t) (Set.Icc (r k) (r ⟨k.val + 1, hk⟩)) :=
    p.continuous.continuousOn
  rw [mul_neg_iff] at this
  rcases this with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · obtain ⟨c, hc_in, hc_root⟩ :=
      intermediate_value_Ioo' h_lt.le h_cont (Set.mem_Ioo.mpr ⟨h₂, h₁⟩)
    exact ⟨c, hc_root, hc_in.1, hc_in.2⟩
  · obtain ⟨c, hc_in, hc_root⟩ :=
      intermediate_value_Ioo h_lt.le h_cont (Set.mem_Ioo.mpr ⟨h₁, h₂⟩)
    exact ⟨c, hc_root, hc_in.1, hc_in.2⟩

lemma exists_root_below_min_of_wronskian_pos {n : ℕ} (hn : n ≠ 0)
    {p q : ℝ[X]} (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = n + 1) (hq_deg : q.natDegree = n)
    (hW : ∀ t : ℝ, 0 < p.derivative.eval t * q.eval t - p.eval t * q.derivative.eval t)
    (r : Fin n → ℝ) (hr_mono : StrictMono r) (hr_roots : ∀ k, q.IsRoot (r k)) :
    ∃ x, p.IsRoot x ∧ x < r ⟨0, Nat.pos_of_ne_zero hn⟩ := by
  set k : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
  have h_sign₀ : 0 < p.eval (r k) * (-1) ^ (n - k.val) :=
    sign_p_at_root_of_wronskian_pos' hq_pos hq_deg hW r hr_mono hr_roots k
  simp only [k, Nat.sub_zero] at h_sign₀
  have h_tendsto_bot :
      Filter.Tendsto (fun x ↦ p.eval x * (-1) ^ (n + 1)) Filter.atBot Filter.atTop :=
    tendsto_eval_mul_neg_one_pow_atBot hp_pos hp_deg
  obtain ⟨x, hx₁, hx₂⟩ := (Filter.Eventually.and (Filter.eventually_lt_atBot (r k))
    (h_tendsto_bot.eventually_gt_atTop 0)).exists
  have h_cont : ContinuousOn (fun t ↦ p.eval t) (Set.Icc x (r k)) :=
    p.continuous.continuousOn
  have : p.eval x * p.eval (r k) < 0 :=
    mul_neg_of_pos_mul_neg_one_pow_succ h_sign₀ hx₂
  rw [mul_neg_iff] at this
  rcases this with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · obtain ⟨c, hc_in, hc_root⟩ :=
      intermediate_value_Ioo' hx₁.le h_cont (Set.mem_Ioo.mpr ⟨h₂, h₁⟩)
    exact ⟨c, hc_root, hc_in.2⟩
  · obtain ⟨c, hc_in, hc_root⟩ :=
      intermediate_value_Ioo hx₁.le h_cont (Set.mem_Ioo.mpr ⟨h₁, h₂⟩)
    exact ⟨c, hc_root, hc_in.2⟩

lemma exists_root_above_max_of_wronskian_pos {n : ℕ} (hn : n ≠ 0)
    {p q : ℝ[X]} (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = n + 1) (hq_deg : q.natDegree = n)
    (hW : ∀ t : ℝ, 0 < p.derivative.eval t * q.eval t - p.eval t * q.derivative.eval t)
    (r : Fin n → ℝ) (hr_mono : StrictMono r) (hr_roots : ∀ k, q.IsRoot (r k)) :
    ∃ x, p.IsRoot x ∧ r ⟨n - 1, Nat.sub_lt (Nat.pos_of_ne_zero hn) Nat.one_pos⟩ < x := by
  set k : Fin n := ⟨n - 1, Nat.sub_lt (Nat.pos_of_ne_zero hn) Nat.one_pos⟩
  have hsign : 0 < p.eval (r k) * (-1) ^ (n - (n - 1)) :=
    sign_p_at_root_of_wronskian_pos' hq_pos hq_deg hW r hr_mono hr_roots k
  have : n - (n - 1) = 1 := by lia
  rw [this, pow_one] at hsign
  have : p.eval (r k) < 0 := by simp_all
  have h_tendsto_top : Filter.Tendsto (fun x ↦ p.eval x) Filter.atTop Filter.atTop := by
    apply Polynomial.tendsto_atTop_of_leadingCoeff_nonneg
    · rw [← Polynomial.natDegree_pos_iff_degree_pos, hp_deg]
      exact Nat.succ_pos n
    · exact hp_pos.le
  obtain ⟨x, hx₁, hx₂⟩ := (Filter.Eventually.and
    (Filter.eventually_gt_atTop (r k))
    (h_tendsto_top.eventually_gt_atTop 0)).exists
  have h_cont : ContinuousOn (fun t ↦ p.eval t) (Set.Icc (r k) x) :=
    p.continuous.continuousOn
  obtain ⟨c, hc_in, hc_root⟩ :=
    intermediate_value_Ioo hx₁.le h_cont (Set.mem_Ioo.mpr ⟨this, hx₂⟩)
  exact ⟨c, hc_root, hc_in.1⟩

lemma apply_lt_of_card_lt_le {m : ℕ} {t : Fin m → ℝ} (ht : StrictMono t) {c : ℝ}
    {k : Fin m} (h_card : k.val + 1 ≤ (Finset.univ.filter (fun i ↦ t i < c)).card) :
    t k < c := by
  rwa [← Tuple.lt_card_lt_iff_apply_lt_of_monotone ht.monotone]

lemma lt_apply_of_card_le_le {m : ℕ} {t : Fin m → ℝ} (ht : StrictMono t) {c : ℝ}
    {k : Fin m} (h_card : (Finset.univ.filter (fun i ↦ t i ≤ c)).card ≤ k.val) :
    c < t k := by
  rwa [← not_le, ← Tuple.lt_card_le_iff_apply_le_of_monotone ht.monotone, not_lt]

lemma card_le_filter_of_inj_roots {N l : ℕ} {p : ℝ[X]} {t : Fin N → ℝ}
    (ht_surj : ∀ x ∈ p.roots, ∃ i, t i = x)
    (hp_ne : p ≠ 0) (g : Fin l → ℝ) (hg_inj : Function.Injective g)
    (hg_root : ∀ j, p.IsRoot (g j)) (P : ℝ → Prop) [DecidablePred P]
    (hg_prop : ∀ j, P (g j)) :
    l ≤ (Finset.univ.filter (fun i ↦ P (t i))).card := by
  have h_mem (j : Fin l) : ∃ i : Fin N, t i = g j :=
    ht_surj (g j) (mem_roots'.mpr ⟨hp_ne, hg_root j⟩)
  choose idx h_idx using h_mem
  have h_idx_inj : Function.Injective idx := fun a b hab ↦
    hg_inj ((h_idx a).symm.trans ((congr_arg t hab).trans (h_idx b)))
  have h_sub : Finset.univ.image idx ⊆ Finset.univ.filter (fun i ↦ P (t i)) := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (h_idx y).symm ▸ hg_prop y⟩
  rw [← Fintype.card_fin l, ← Finset.card_univ,
    ← Finset.card_image_of_injective _ h_idx_inj]
  exact Finset.card_le_card h_sub

lemma card_lt_le_of_inj_roots {N l : ℕ} {p : ℝ[X]} {t : Fin N → ℝ}
    (ht_surj : ∀ x ∈ p.roots, ∃ i, t i = x)
    (hp_ne : p ≠ 0) {c : ℝ} (g : Fin l → ℝ) (hg_inj : Function.Injective g)
    (hg_root : ∀ j, p.IsRoot (g j)) (hg_lt : ∀ j, g j < c) :
    l ≤ (Finset.univ.filter (fun i ↦ t i < c)).card :=
  card_le_filter_of_inj_roots ht_surj hp_ne g hg_inj hg_root (fun x ↦ x < c) hg_lt

lemma card_gt_le_of_inj_roots {N l : ℕ} {p : ℝ[X]} {t : Fin N → ℝ}
    (ht_surj : ∀ x ∈ p.roots, ∃ i, t i = x)
    (hp_ne : p ≠ 0) {c : ℝ} (g : Fin l → ℝ) (hg_inj : Function.Injective g)
    (hg_root : ∀ j, p.IsRoot (g j)) (hg_gt : ∀ j, c < g j) :
    l ≤ (Finset.univ.filter (fun i ↦ c < t i)).card :=
  card_le_filter_of_inj_roots ht_surj hp_ne g hg_inj hg_root (fun x ↦ c < x) hg_gt

lemma Polynomial.roots_nodup_of_wronskian_pos {p q : ℝ[X]}
    (hW : ∀ t : ℝ, 0 < q.derivative.eval t * p.eval t - q.eval t * p.derivative.eval t) :
    p.roots.Nodup ∧ q.roots.Nodup := by
  constructor
  · apply Polynomial.roots_nodup_of_splits_and_simple
    intro r hr hd
    have := hW r
    simp_all
  · apply Polynomial.roots_nodup_of_splits_and_simple
    intro r hr hd
    have := hW r
    simp_all

lemma StrictPrecSameDegree.of_wronskian_pos {n : ℕ}
    {p q : ℝ[X]} (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = n) (hq_deg : q.natDegree = n)
    (hp_splits : p.Splits) (hq_splits : q.Splits)
    (hW : ∀ t : ℝ, 0 < q.derivative.eval t * p.eval t -
    q.eval t * p.derivative.eval t) :
    StrictPrecSameDegree p q := by
  rcases n with (_ | n)
  · rw [eq_C_of_natDegree_eq_zero hp_deg] at hW ⊢
    rw [eq_C_of_natDegree_eq_zero hq_deg] at hW ⊢
    simp_all
  · have h_real_roots := Polynomial.roots_nodup_of_wronskian_pos hW
    obtain ⟨s, hs_mono, hs_roots⟩ :
      ∃ s : Fin (n + 1) → ℝ, StrictMono s ∧ ∀ k, p.IsRoot (s k) :=
      Polynomial.exists_strictMono_roots hp_splits hp_deg h_real_roots.1
    obtain ⟨r, hr_mono, hr_roots⟩ :
      ∃ r : Fin (n + 1) → ℝ, StrictMono r ∧ ∀ k, q.IsRoot (r k) :=
      Polynomial.exists_strictMono_roots hq_splits hq_deg h_real_roots.2
    have hs_surj : ∀ x ∈ p.roots, ∃ k, s k = x :=
      fun x hx ↦ exists_index_eq_of_mem_roots s hs_mono hs_roots
        (leadingCoeff_ne_zero.mp hp_pos.ne') hp_deg.le x hx
    have hr_surj : ∀ x ∈ q.roots, ∃ k, r k = x :=
      fun x hx ↦ exists_index_eq_of_mem_roots r hr_mono hr_roots
        (leadingCoeff_ne_zero.mp hq_pos.ne') hq_deg.le x hx
    have h_inter := Polynomial.exists_root_between_roots_of_wronskian_pos
      hp_pos hq_pos hp_deg hq_deg hW
      r hr_mono hr_roots
    have h_inter' := StrictMono.fin_interlacing_of_root_between s r hs_mono ?_ ?_
    · exact StrictPrecSameDegree.of_fin_interlacing s r hs_mono hr_mono
        h_inter'.1 h_inter'.2 p q (leadingCoeff_ne_zero.mp hp_pos.ne')
        (leadingCoeff_ne_zero.mp hq_pos.ne') hp_splits hq_splits hp_deg hq_deg
        h_real_roots.1 h_real_roots.2 hs_surj hr_surj
    · obtain ⟨x, hx₁, hx₂⟩ := h_inter.1
      have hx_mem : x ∈ p.roots :=
        mem_roots'.mpr ⟨leadingCoeff_ne_zero.mp hp_pos.ne', hx₁⟩
      obtain ⟨k, rfl⟩ := hs_surj x hx_mem
      exact lt_of_le_of_lt (hs_mono.monotone (Nat.zero_le _)) hx₂
    · intro k
      obtain ⟨x, hx_root, hx_between⟩ := h_inter.2 k
      have hx_mem : x ∈ p.roots :=
        mem_roots'.mpr ⟨leadingCoeff_ne_zero.mp hp_pos.ne', hx_root⟩
      grind

lemma strictMono_of_lt_and_lt {n : ℕ} {α : Type*} [LinearOrder α]
    (u : Fin (n + 1) → α) (s : Fin n → α)
    (hu_hi : ∀ i : Fin n, u i.castSucc < s i)
    (hu_lo : ∀ i : Fin n, s i < u i.succ) :
    StrictMono u := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  exact lt_trans (hu_hi i) (hu_lo i)

lemma interlace_of_interlaced_roots {n : ℕ} {p : ℝ[X]} (hp_ne : p ≠ 0)
    (t : Fin (n + 1) → ℝ) (ht_mono : StrictMono t) (ht_surj : ∀ x ∈ p.roots, ∃ i, t i = x)
    (u : Fin (n + 1) → ℝ) (hu_mono : StrictMono u) (hu_root : ∀ i, p.IsRoot (u i))
    (s : Fin n → ℝ) (hs_mono : StrictMono s)
    (hu_hi : ∀ i : Fin n, u i.castSucc < s i)
    (hu_lo : ∀ i : Fin n, s i < u i.succ)
    (k : Fin n) : t k.castSucc < s k ∧ s k < t k.succ := by
  have h_le : k.val + 1 ≤ n + 1 := by lia
  let g_low : Fin (k.val + 1) → ℝ := fun j ↦ u (Fin.castLE h_le j)
  have hg_low_lt (j : Fin (k.val + 1)) : g_low j < s k := by
    simp only [g_low]
    have h_lt' : (Fin.castLE h_le j).val < n := by
      simp [Fin.castLE]
      lia
    have h_lt_j := hu_hi ⟨(Fin.castLE h_le j).val, h_lt'⟩
    refine lt_of_lt_of_le h_lt_j (hs_mono.monotone ?_)
    simp only [Fin.le_def, Fin.val_castLE]
    lia
  have hg_low_mono : StrictMono g_low :=
    fun a b hab ↦ hu_mono (Fin.strictMono_castLE h_le hab)
  have h_card_l : k.val + 1 ≤ (Finset.univ.filter (fun i ↦ t i < s k)).card :=
    card_lt_le_of_inj_roots ht_surj hp_ne g_low hg_low_mono.injective
      (fun j ↦ hu_root _) hg_low_lt
  have h_lt_high (j : Fin (n - k.val)) : k.val + j.val + 1 < n + 1 := by lia
  let g_high : Fin (n - k.val) → ℝ := fun j => u ⟨k.val + j.val + 1, h_lt_high j⟩
  have hg_high_gt (j : Fin (n - k.val)) : s k < g_high j := by
    simp only [g_high]
    have h_pos' : k.val + j.val < n := by lia
    have hlo := hu_lo ⟨k.val + j.val, h_pos'⟩
    refine lt_of_le_of_lt (hs_mono.monotone ?_) hlo
    simp only [Fin.le_def]
    lia
  have hg_high_mono : StrictMono g_high := by
    intro a b hab
    simp only [g_high]
    apply hu_mono
    simp only [Fin.lt_def]
    simp [*]
  have h_card_h : n - k.val ≤ (Finset.univ.filter (fun i ↦ s k < t i)).card :=
    card_gt_le_of_inj_roots ht_surj hp_ne g_high hg_high_mono.injective
      (fun j ↦ hu_root _) hg_high_gt
  refine ⟨apply_lt_of_card_lt_le ht_mono h_card_l, lt_apply_of_card_le_le ht_mono ?_⟩
  have h_part : (Finset.univ.filter (fun i ↦ t i ≤ s k)).card +
      (Finset.univ.filter (fun i ↦ s k < t i)).card = n + 1 := by
    have h_eq : (Finset.univ.filter (fun i : Fin (n + 1) ↦ s k < t i)) =
        (Finset.univ.filter (fun i => ¬ t i ≤ s k)) := by
      simp
    rw [h_eq, Finset.card_filter_add_card_filter_not]
    simp
  simp only [Fin.val_succ]
  lia

lemma exists_strictMono_u_of_bounds {α : Type*} [LinearOrder α] {n : ℕ} (hn : n ≠ 0)
    (s : Fin n → α)
    (xl xh : α) (h_xl_lt : xl < s ⟨0, Nat.pos_of_ne_zero hn⟩)
    (h_xh_gt : s ⟨n - 1, Nat.sub_lt (Nat.pos_of_ne_zero hn) Nat.one_pos⟩ < xh)
    (xb : Fin (n - 1) → α)
    (h_xb_lo : ∀ j : Fin (n - 1), s ⟨j.val, by lia⟩ < xb j)
    (h_xb_hi : ∀ j : Fin (n - 1), xb j < s ⟨j.val + 1, by lia⟩)
    (P : α → Prop) (h_xl_P : P xl) (h_xh_P : P xh) (h_xb_P : ∀ j : Fin (n - 1), P (xb j)) :
    ∃ u : Fin (n + 1) → α, StrictMono u ∧
      (∀ i : Fin n, u i.castSucc < s i) ∧
      (∀ i : Fin n, s i < u i.succ) ∧
      (∀ i : Fin (n + 1), P (u i)) := by
  let u : Fin (n + 1) → α := fun i ↦
    if h0 : i.val = 0 then xl
    else if hn' : i.val = n then xh
    else xb ⟨i.val - 1, by lia⟩
  have hu_hi (i : Fin (n + 1)) (hi : i.val < n) : u i < s ⟨i.val, hi⟩ := by
    simp only [u]
    split_ifs with h₀ hn'
    · have : i = ⟨0, by lia⟩ := Fin.ext h₀
      subst this
      exact h_xl_lt
    · lia
    · have h_lt_n₁ : i.val - 1 < n - 1 := by lia
      have hb := h_xb_hi ⟨i.val - 1, h_lt_n₁⟩
      have heq : (⟨i.val - 1 + 1, by lia⟩ : Fin n) = ⟨i.val, hi⟩ := Fin.ext (by lia)
      rwa [heq] at hb
  have hu_lo (i : Fin (n + 1)) (hi : 0 < i.val) : s ⟨i.val - 1, by lia⟩ < u i := by
    simp only [u]
    split_ifs with h₀ hn'
    · lia
    · have : i = ⟨n, by lia⟩ := Fin.ext hn'
      subst this
      exact h_xh_gt
    · exact h_xb_lo ⟨i.val - 1, by lia⟩
  have hu_mono : StrictMono u :=
    strictMono_of_lt_and_lt u s (fun i ↦ hu_hi i.castSucc i.isLt)
      (fun i ↦ hu_lo i.succ (by simp))
  refine
    ⟨u, hu_mono, fun i ↦ hu_hi i.castSucc i.isLt,
      fun i ↦ hu_lo i.succ (by simp), fun i ↦ ?_⟩
  simp only [u]
  split_ifs with h₀ hn'
  · exact h_xl_P
  · exact h_xh_P
  · exact h_xb_P ⟨i.val - 1, by lia⟩

lemma prec_of_wronskian_pos_succ {n : ℕ}
    {p q : ℝ[X]} (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = n + 1) (hq_deg : q.natDegree = n)
    (hp_splits : p.Splits) (hq_splits : q.Splits)
    (hW : ∀ t : ℝ, 0 < p.derivative.eval t * q.eval t - p.eval t * q.derivative.eval t) :
    Prec q p := by
  have hp_ne : p ≠ 0 := leadingCoeff_ne_zero.mp hp_pos.ne'
  have hq_ne : q ≠ 0 := leadingCoeff_ne_zero.mp hq_pos.ne'
  have hpq_nodup := Polynomial.roots_nodup_of_wronskian_pos hW
  have hp_nodup : p.roots.Nodup := hpq_nodup.2
  have hq_nodup : q.roots.Nodup := hpq_nodup.1
  obtain ⟨s, hs_mono, hs_roots⟩ := Polynomial.exists_strictMono_roots hq_splits hq_deg hq_nodup
  obtain ⟨t, ht_mono, ht_roots⟩ := Polynomial.exists_strictMono_roots hp_splits hp_deg hp_nodup
  have hs_surj : ∀ x ∈ q.roots, ∃ i, s i = x :=
    fun x hx ↦ exists_index_eq_of_mem_roots s hs_mono hs_roots hq_ne hq_deg.le x hx
  have ht_surj : ∀ x ∈ p.roots, ∃ i, t i = x :=
    fun x hx ↦ exists_index_eq_of_mem_roots t ht_mono ht_roots hp_ne hp_deg.le x hx
  rcases eq_or_ne n 0 with hn₀ | hn
  · subst hn₀
    have hq_roots : q.roots = 0 := by
      rw [← Multiset.card_eq_zero, ← Splits.natDegree_eq_card_roots hq_splits, hq_deg]
    have hp_roots : p.roots = {t 0} := by
      have : p.roots.card = 1 := by rw [← Splits.natDegree_eq_card_roots hp_splits, hp_deg]
      obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp this
      have ht₀_mem : t 0 ∈ p.roots := mem_roots'.mpr ⟨hp_ne, ht_roots 0⟩
      rw [ha] at ht₀_mem ⊢
      rw [Multiset.mem_singleton.mp ht₀_mem]
    refine ⟨⟨hq_ne, hq_splits⟩, ⟨hp_ne, hp_splits⟩, [], [t 0], by simp, by simp,
      by simp [hq_roots], by simp [hp_roots], ?_⟩
    left
    constructor <;> simp [ListInterlaces]
  classical
  obtain ⟨xl, h_xl_root, h_xl_lt⟩ :=
    exists_root_below_min_of_wronskian_pos hn hp_pos hq_pos hp_deg hq_deg hW s hs_mono hs_roots
  obtain ⟨xh, h_xh_root, h_xh_gt⟩ :=
    exists_root_above_max_of_wronskian_pos hn hp_pos hq_pos hp_deg hq_deg hW s hs_mono hs_roots
  have hj_lt (j : Fin (n - 1)) : j.val < n := by lia
  have hj_succ_lt (j : Fin (n - 1)) : j.val + 1 < n := by lia
  have h_between (j : Fin (n - 1)) :
      ∃ x, p.IsRoot x ∧ s ⟨j.val, hj_lt j⟩ < x ∧ x < s ⟨j.val + 1, hj_succ_lt j⟩ := by
    obtain ⟨x, hx_root, hx_lo, hx_hi⟩ :=
      exists_root_between_consecutive_of_wronskian_pos hq_pos hq_deg hW s hs_mono hs_roots
        ⟨j.val, hj_lt j⟩ (hj_succ_lt j)
    exact ⟨x, hx_root, hx_lo, hx_hi⟩
  choose xb h_xb_root h_xb_lo h_xb_hi using h_between
  obtain ⟨u, hu_mono, hu_hi, hu_lo, hu_root⟩ :=
    exists_strictMono_u_of_bounds hn s xl xh h_xl_lt h_xh_gt xb h_xb_lo h_xb_hi
      (fun x ↦ p.IsRoot x) h_xl_root h_xh_root h_xb_root
  have h_interlace (k : Fin n) : t k.castSucc < s k ∧ s k < t k.succ :=
    interlace_of_interlaced_roots hp_ne t ht_mono ht_surj u hu_mono hu_root s hs_mono hu_hi hu_lo k
  have h_len_st : (List.ofFn s).length + 1 = (List.ofFn t).length := by simp
  refine
    ⟨⟨hq_ne, hq_splits⟩, ⟨hp_ne, hp_splits⟩, q.roots.sort (· ≤ ·),
      p.roots.sort (· ≤ ·), Multiset.pairwise_sort _ _, Multiset.pairwise_sort _ _,
      by simp, by simp, Or.inl ⟨?_, ?_⟩⟩
  · rw [Multiset.length_sort, Multiset.length_sort]
    rw [← Splits.natDegree_eq_card_roots hp_splits, ← Splits.natDegree_eq_card_roots hq_splits,
      hp_deg, hq_deg]
  · rw [Polynomial.roots_sort_eq_ofFn hq_ne hq_splits hq_deg hq_nodup s hs_mono hs_surj,
      Polynomial.roots_sort_eq_ofFn hp_ne hp_splits hp_deg hp_nodup t ht_mono ht_surj]
    apply listInterlaces_of_interleaves_of_length h_len_st
    apply List.Interleaves.mono (r := fun a b : ℝ => a < b) (fun a b h => h.le)
    rw [← List.interleaves_reverse_reverse_of_length_add_one_eq_length
      (r := fun a b : ℝ => a > b) h_len_st]
    apply List.Interleaves.ofFn_succ s t
    · intro i j hij
      rcases j with ⟨j_val, hj⟩
      subst hij
      exact (h_interlace ⟨i.val, i.isLt⟩).2
    · intro i j hij
      have hlt : t (⟨j.val, j.isLt⟩ : Fin n).castSucc < s ⟨j.val, j.isLt⟩ :=
        (h_interlace ⟨j.val, j.isLt⟩).1
      have h_le_ij : ⟨i.val, i.isLt⟩ ≤ (⟨j.val, j.isLt⟩ : Fin n).castSucc := by
        simp only [Fin.le_def, Fin.val_castSucc]
        lia
      have hle : t ⟨i.val, i.isLt⟩ ≤ t (⟨j.val, j.isLt⟩ : Fin n).castSucc :=
        ht_mono.monotone h_le_ij
      exact lt_of_le_of_lt hle hlt
lemma StrictPrecSameDegree.of_splits_and_posDef {n : ℕ}
    {p q : ℝ[X]} (hp_pos : HasPosLeadingCoeff p) (hq_pos : HasPosLeadingCoeff q)
    (hp_deg : p.natDegree = n) (hq_deg : q.natDegree = n)
    (hp_splits : p.Splits) (hq_splits : q.Splits)
    (hB : (bezoutMatrix n q p).PosDef) :
    StrictPrecSameDegree p q :=
  match n with
  | 0 =>
    ⟨⟨leadingCoeff_ne_zero.mp hp_pos.ne', hp_splits⟩,
      ⟨leadingCoeff_ne_zero.mp hq_pos.ne', hq_splits⟩,
      hp_deg ▸ hq_deg ▸ rfl, by
        have hp_roots : p.roots = 0 :=
          Multiset.card_eq_zero.mp (hp_splits.natDegree_eq_card_roots.symm ▸ hp_deg)
        have hq_roots : q.roots = 0 :=
          Multiset.card_eq_zero.mp (hq_splits.natDegree_eq_card_roots.symm ▸ hq_deg)
        simp [hp_roots, hq_roots]⟩
  | m + 1 =>
    StrictPrecSameDegree.of_wronskian_pos hp_pos hq_pos hp_deg hq_deg hp_splits hq_splits fun t ↦
      bezoutMatrix.wronskian_pos_of_posDef hq_deg.le hp_deg.le hB t

end RealRooted
