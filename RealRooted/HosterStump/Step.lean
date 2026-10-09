import RealRooted.HosterStump.Diagram
import RealRooted.HosterStump.Sequence

/-!
# Hoster--Stump, Section 3.1: the induction for Theorem 3.3

The induction invariant `IsInterlacingDiagram n T` propagates from `n` and `shiftDown T`
to `n + 1` and `T` (`IsInterlacingDiagram.step`), by the Lemmas 3.8--3.13 of Hoster and
Stump, *Chow polynomials of simplicial posets* (arXiv:2508.15538).  Theorem 3.3
(`isInterlacingDiagram_range`) follows from the base cases `n = 2` in `Diagram.lean`.

Entries of the diagram at level `n + 1` are written through those at level `n`, with
`A = top n T'`, `B = mid n T'`, `C = bot n T'` where `T' = shiftDown T`.  The five
statements of Lemma 3.8 (rows, columns, diagonal) are proved from the induction hypothesis,
and `IsInterlacingDiagram.of_five` assembles the invariant from them by Wagner's chain lemma.
-/

open Polynomial

noncomputable section

namespace RealRooted.HosterStump

/-! ### Splitting of sums -/

private theorem splits_sum_Ico_of_interl (F : ℕ → ℝ[X]) (a : ℕ)
    (hnn : ∀ k, HasNonnegCoeffs (F k)) :
    ∀ b : ℕ, (∀ k, a ≤ k → k < b → F k ≠ 0 → (F k).Splits) →
      (∀ i j, a ≤ i → i < j → j < b → Interl (F i) (F j)) →
      ∑ k ∈ Finset.Ico a b, F k ≠ 0 → (∑ k ∈ Finset.Ico a b, F k).Splits := by
  intro b
  induction b with
  | zero =>
    intro _ _ h
    simp at h
  | succ b ih =>
    intro hsp hint hne
    by_cases hab : a ≤ b
    · rw [Finset.sum_Ico_succ_top hab] at hne ⊢
      refine splits_add_of_interl ?_ (hasNonnegCoeffs_finsetSum _ _ fun k _ => hnn k) (hnn b)
        (ih (fun k h1 h2 => hsp k h1 (by lia)) (fun i j h1 h2 h3 => hint i j h1 h2 (by lia)))
        (hsp b hab (by lia)) hne
      refine Interl.finsetSum_right_of_nonneg _ _ _ (fun i hi => ?_) fun k _ => hnn k
      have := Finset.mem_Ico.1 hi
      exact hint i b this.1 this.2 (by lia)
    · simp [Finset.Ico_eq_empty_of_le (show b + 1 ≤ a by lia)] at hne

/-! ### The data of the induction hypothesis -/

/-- The data of level `n` used in the induction step, with `A = top`, `B = mid`, `C = bot`. -/
private structure Lvl (n : ℕ) (A B C : ℕ → ℝ[X]) : Prop where
  nnA : ∀ k, HasNonnegCoeffs (A k)
  nnB : ∀ k, HasNonnegCoeffs (B k)
  nnC : ∀ k, HasNonnegCoeffs (C k)
  rowA : ∀ i j, i < j → j ≤ n → Interl (A i) (A j)
  rowB : ∀ i j, i < j → j ≤ n → Interl (B i) (B j)
  AB : ∀ i j, i ≤ j → j ≤ n → Interl (A i) (B j)
  AC : ∀ i j, i ≤ n → j ≤ n → Interl (A i) (C j)
  Bne : ∀ k, k ≤ n → B k ≠ 0
  spA : ∀ k, k ≤ n → A k ≠ 0 → (A k).Splits
  spB : ∀ k, k ≤ n → (B k).Splits
  add : ∀ k, B k = A k + C k
  A0 : A 0 = B 0

private theorem Lvl.of_diagram {n : ℕ} {T : Finset ℕ} (ih : IsInterlacingDiagram n T) :
    Lvl n (top n T) (mid n T) (bot n T) where
  nnA k := hasNonnegCoeffs_refined n k ∅ (T.erase 0)
  nnB k := hasNonnegCoeffs_refined n k ∅ T
  nnC k := hasNonnegCoeffs_refined n k {0} T
  rowA := ih.top_row
  rowB := ih.mid_row
  AB := ih.top_mid
  AC := ih.top_bot
  Bne := ih.mid_ne_zero
  spA k hk hne := (ih.splits k hk).1 hne
  spB k hk := (ih.splits k hk).2.1
  add := mid_eq_top_add_bot n T
  A0 := top_zero_eq_mid_zero n T

section Lvl

variable {n : ℕ} {A B C : ℕ → ℝ[X]}

private theorem Lvl.nnSA (h : Lvl n A B C) (s : Finset ℕ) : HasNonnegCoeffs (∑ k ∈ s, A k) :=
  hasNonnegCoeffs_finsetSum _ _ fun k _ => h.nnA k

private theorem Lvl.nnSB (h : Lvl n A B C) (s : Finset ℕ) : HasNonnegCoeffs (∑ k ∈ s, B k) :=
  hasNonnegCoeffs_finsetSum _ _ fun k _ => h.nnB k

private theorem Lvl.nnSC (h : Lvl n A B C) (s : Finset ℕ) : HasNonnegCoeffs (∑ k ∈ s, C k) :=
  hasNonnegCoeffs_finsetSum _ _ fun k _ => h.nnC k

private theorem Lvl.splitsSB (h : Lvl n A B C) {a b : ℕ} (hb : b ≤ n + 1) :
    ∑ k ∈ Finset.Ico a b, B k ≠ 0 → (∑ k ∈ Finset.Ico a b, B k).Splits :=
  splits_sum_Ico_of_interl B a h.nnB b (fun k _ hk _ => h.spB k (by lia))
    (fun i j _ hij hj => h.rowB i j hij (by lia))

private theorem Lvl.splitsSA (h : Lvl n A B C) {b : ℕ} (hb : b ≤ n + 1) :
    ∑ k ∈ Finset.range b, A k ≠ 0 → (∑ k ∈ Finset.range b, A k).Splits := by
  rw [Finset.range_eq_Ico]
  exact splits_sum_Ico_of_interl A 0 h.nnA b (fun k _ hk => h.spA k (by lia))
    (fun i j _ hij hj => h.rowA i j hij (by lia))

private theorem splits_X_mul_of_splits {P : ℝ[X]} (hP : P ≠ 0 → P.Splits) :
    X * P ≠ 0 → (X * P).Splits := fun hne => by
  have hP0 : P ≠ 0 := fun h => hne (by simp [h])
  exact (isRealRooted_X_mul hP0 (hP hP0)).2

/-! ### Nonvanishing at level `n + 1` -/

private theorem Lvl.top_ne (h : Lvl n A B C) {k : ℕ} (hk : k ≤ n) :
    ∑ j ∈ Finset.Ico k (n + 1), B j ≠ 0 := by
  rw [Finset.sum_Ico_succ_top hk]
  exact add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero (h.nnSB _) (h.nnB n) (h.Bne n le_rfl)

private theorem Lvl.bot_ne (h : Lvl n A B C) {k : ℕ} (hk1 : 1 ≤ k) :
    X * ∑ j ∈ Finset.range k, A j ≠ 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by lia⟩
  rw [Finset.sum_range_succ']
  refine mul_ne_zero X_ne_zero ?_
  rw [h.A0]
  exact add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero
    (hasNonnegCoeffs_finsetSum _ _ fun j _ => h.nnA _) (h.nnB 0) (h.Bne 0 (by lia))

private theorem Lvl.mid_ne (h : Lvl n A B C) {k : ℕ} (hk : k ≤ n + 1) :
    X * ∑ j ∈ Finset.range k, A j + ∑ j ∈ Finset.Ico k (n + 1), B j ≠ 0 := by
  rcases Nat.lt_or_ge n k with hlt | hle
  · obtain rfl : k = n + 1 := by lia
    simpa using h.bot_ne (k := n + 1) (by lia)
  · exact add_ne_zero_of_hasNonnegCoeffs_of_right_ne_zero ((h.nnSA _).X_mul) (h.nnSB _)
      (h.top_ne hle)

/-! ### Lemma 3.9: the top row -/

private theorem Lvl.top_row (h : Lvl n A B C) {i j : ℕ} (hij : i < j) (hj : j ≤ n + 1) :
    Interl (∑ k ∈ Finset.Ico i (n + 1), B k) (∑ k ∈ Finset.Ico j (n + 1), B k) := by
  rw [← Finset.sum_Ico_consecutive _ hij.le hj]
  refine interl_add_left_of_common_right_of_nonneg ?_ (Interl.refl (h.splitsSB (by lia)))
    (h.nnSB _) (h.nnSB _)
  refine Interl.finsetSum_pairwise_of_nonneg _ _ _ _ (fun l hl m hm => ?_)
    (fun _ _ => h.nnB _) fun _ _ => h.nnB _
  have h1 := Finset.mem_Ico.1 hl
  have h2 := Finset.mem_Ico.1 hm
  exact h.rowB l m (by lia) (by lia)

/-! ### Lemma 3.11: the bottom row -/

private theorem Lvl.bot_row (h : Lvl n A B C) {i j : ℕ} (hij : i < j) (hj : j ≤ n + 1) :
    Interl (X * ∑ k ∈ Finset.range i, A k) (X * ∑ k ∈ Finset.range j, A k) := by
  refine Interl.mul_X_both_of_nonneg ?_ (h.nnSA _) (h.nnSA _)
  rw [← Finset.sum_range_add_sum_Ico A hij.le]
  refine interl_add_right_of_common_left_of_nonneg (Interl.refl (h.splitsSA (by lia)))
    ?_ (h.nnSA _) (h.nnSA _)
  refine Interl.finsetSum_pairwise_of_nonneg _ _ _ _ (fun l hl m hm => ?_)
    (fun _ _ => h.nnA _) fun _ _ => h.nnA _
  have h1 := Finset.mem_range.1 hl
  have h2 := Finset.mem_Ico.1 hm
  exact h.rowA l m (by lia) (by lia)

/-! ### Lemma 3.12: columns -/

private theorem Lvl.col (h : Lvl n A B C) (k : ℕ) :
    Interl (∑ j ∈ Finset.Ico k (n + 1), B j) (X * ∑ j ∈ Finset.range k, A j) := by
  refine interl_mul_X_of_interl ?_ (h.nnSA _) (h.nnSB _)
  refine Interl.finsetSum_pairwise_of_nonneg _ _ _ _ (fun l hl m hm => ?_)
    (fun _ _ => h.nnA _) fun _ _ => h.nnB _
  have h1 := Finset.mem_range.1 hl
  have h2 := Finset.mem_Ico.1 hm
  exact h.AB l m (by lia) (by lia)

/-! ### Lemma 3.13: the diagonal -/

private theorem Lvl.diag (h : Lvl n A B C) :
    Interl (∑ j ∈ Finset.Ico n (n + 1), B j) (X * ∑ j ∈ Finset.range 1, A j) := by
  simpa using interl_mul_X_of_interl (h.AB 0 n (by lia) le_rfl) (h.nnA 0) (h.nnB n)

/-! ### Lemma 3.10: the middle row -/

end Lvl

private theorem mid_cons_aux {P W Bk Ak : ℝ[X]} (hBW : Interl Bk W) (hBP : Interl Bk (X * P))
    (hBA : Interl Bk (X * Ak)) (hWA : Interl W (X * Ak)) (hPA : Interl (X * P) (X * Ak))
    (nBk : HasNonnegCoeffs Bk) (nW : HasNonnegCoeffs W) (nP : HasNonnegCoeffs P)
    (nAk : HasNonnegCoeffs Ak) (hsplit : W + X * P ≠ 0 → (W + X * P).Splits) :
    Interl (X * P + (Bk + W)) (X * (P + Ak) + W) := by
  have key := Interl.window_three (f₁ := Bk) (f₂ := W) (f₃ := X * P) (f₄ := X * Ak) hBW hBP
    hBA hWA hPA nBk nW nP.X_mul nAk.X_mul hsplit
  rw [show X * P + (Bk + W) = Bk + W + X * P by ring,
    show X * (P + Ak) + W = W + X * P + X * Ak by ring]
  exact key

section Lvl

variable {n : ℕ} {A B C : ℕ → ℝ[X]}

private theorem Lvl.mid_cons (h : Lvl n A B C) {k : ℕ} (hk : k ≤ n) :
    Interl (X * ∑ j ∈ Finset.range k, A j + ∑ j ∈ Finset.Ico k (n + 1), B j)
      (X * ∑ j ∈ Finset.range (k + 1), A j + ∑ j ∈ Finset.Ico (k + 1) (n + 1), B j) := by
  have hPW : Interl (∑ j ∈ Finset.range k, A j)
      (∑ j ∈ Finset.Ico (k + 1) (n + 1), B j) := by
    refine Interl.finsetSum_pairwise_of_nonneg _ _ _ _ (fun l hl m hm => ?_)
      (fun _ _ => h.nnA _) fun _ _ => h.nnB _
    have h1 := Finset.mem_range.1 hl
    have h2 := Finset.mem_Ico.1 hm
    exact h.AB l m (by lia) (by lia)
  have hWP := interl_mul_X_of_interl hPW (h.nnSA _) (h.nnSB _)
  rw [Finset.sum_eq_sum_Ico_succ_bot (show k < n + 1 by lia), Finset.sum_range_succ]
  refine mid_cons_aux ?_ ?_ ?_ ?_ ?_ (h.nnB k) (h.nnSB _) (h.nnSA _) (h.nnA k) ?_
  · exact Interl.finsetSum_left_of_nonneg _ _ _ (fun j hj =>
      h.rowB k j (Finset.mem_Ico.1 hj).1 (by have := Finset.mem_Ico.1 hj; lia))
      fun _ _ => h.nnB _
  · refine interl_mul_X_of_interl ?_ (h.nnSA _) (h.nnB k)
    exact Interl.finsetSum_right_of_nonneg _ _ _ (fun l hl =>
      h.AB l k (by have := Finset.mem_range.1 hl; lia) hk) fun _ _ => h.nnA _
  · exact interl_mul_X_of_interl (h.AB k k le_rfl hk) (h.nnA k) (h.nnB k)
  · refine interl_mul_X_of_interl ?_ (h.nnA k) (h.nnSB _)
    exact Interl.finsetSum_left_of_nonneg _ _ _ (fun j hj =>
      h.AB k j (by have := Finset.mem_Ico.1 hj; lia) (by have := Finset.mem_Ico.1 hj; lia))
      fun _ _ => h.nnB _
  · refine Interl.mul_X_both_of_nonneg ?_ (h.nnSA _) (h.nnA k)
    exact Interl.finsetSum_right_of_nonneg _ _ _ (fun l hl =>
      h.rowA l k (by have := Finset.mem_range.1 hl; lia) hk) fun _ _ => h.nnA _
  · exact splits_add_of_interl hWP (h.nnSB _) (h.nnSA _).X_mul (h.splitsSB (by lia))
      (splits_X_mul_of_splits (h.splitsSA (by lia)))

private theorem Lvl.mid_end (h : Lvl n A B C) :
    Interl (X * ∑ j ∈ Finset.range 0, A j + ∑ j ∈ Finset.Ico 0 (n + 1), B j)
      (X * ∑ j ∈ Finset.range (n + 1), A j + ∑ j ∈ Finset.Ico (n + 1) (n + 1), B j) := by
  have hsum : ∑ j ∈ Finset.Ico 0 (n + 1), B j =
      ∑ j ∈ Finset.range (n + 1), A j + ∑ j ∈ Finset.range (n + 1), C j := by
    rw [← Finset.sum_add_distrib, ← Finset.range_eq_Ico]
    exact Finset.sum_congr rfl fun j _ => h.add j
  have hAC : Interl (∑ j ∈ Finset.range (n + 1), A j) (∑ j ∈ Finset.range (n + 1), C j) :=
    Interl.finsetSum_pairwise_of_nonneg _ _ _ _ (fun l hl m hm => h.AC l m
      (by have := Finset.mem_range.1 hl; lia) (by have := Finset.mem_range.1 hm; lia))
      (fun _ _ => h.nnA _) fun _ _ => h.nnC _
  have hAB : Interl (∑ j ∈ Finset.range (n + 1), A j)
      (∑ j ∈ Finset.Ico 0 (n + 1), B j) := by
    rw [hsum]
    exact interl_add_right_of_common_left_of_nonneg (Interl.refl (h.splitsSA le_rfl)) hAC
      (h.nnSA _) (h.nnSC _)
  simpa using interl_mul_X_of_interl hAB (h.nnSA _) (h.nnSB _)

private theorem Lvl.mid_row (h : Lvl n A B C) {i j : ℕ} (hij : i < j) (hj : j ≤ n + 1) :
    Interl (X * ∑ k ∈ Finset.range i, A k + ∑ k ∈ Finset.Ico i (n + 1), B k)
      (X * ∑ k ∈ Finset.range j, A k + ∑ k ∈ Finset.Ico j (n + 1), B k) :=
  interl_chain_of_consecutive_of_endpoint
    (fun k => X * ∑ j ∈ Finset.range k, A j + ∑ j ∈ Finset.Ico k (n + 1), B j) 0 (n + 1)
    (fun k _ hk => h.mid_ne hk) (fun k _ hk => h.mid_cons (by lia)) (by simpa using h.mid_end)
    i j (Nat.zero_le i) hij.le hj

/-! ### Splitting at level `n + 1` -/

private theorem Lvl.mid_splits (h : Lvl n A B C) {k : ℕ} (hk : k ≤ n + 1) :
    (X * ∑ j ∈ Finset.range k, A j + ∑ j ∈ Finset.Ico k (n + 1), B j).Splits := by
  rw [add_comm]
  refine splits_add_of_interl (h.col k) (h.nnSB _) (h.nnSA _).X_mul (h.splitsSB le_rfl)
    (splits_X_mul_of_splits (h.splitsSA hk)) ?_
  rw [add_comm]
  exact h.mid_ne hk

end Lvl

/-! ### Lemma 3.8: assembly by Wagner's chain lemma -/

/-- The path `t₀, …, tᵢ, mᵢ, …, mⱼ, bⱼ, …, b_N` of the proof of Lemma 3.8: if consecutive
entries and the two ends interlace, then `tᵢ ⪯ mⱼ` and `mᵢ ⪯ bⱼ` for `i ≤ j`. -/
private theorem path_col (N : ℕ) (t m b : ℕ → ℝ[X])
    (htne : ∀ k, k < N → t k ≠ 0) (hmne : ∀ k, k ≤ N → m k ≠ 0)
    (hbne : ∀ k, 1 ≤ k → k ≤ N → b k ≠ 0)
    (ht : ∀ i j, i < j → j ≤ N → Interl (t i) (t j))
    (hm : ∀ i j, i < j → j ≤ N → Interl (m i) (m j))
    (hb : ∀ i j, i < j → j ≤ N → Interl (b i) (b j))
    (htm : ∀ k, k ≤ N → Interl (t k) (m k)) (hmb : ∀ k, k ≤ N → Interl (m k) (b k))
    (hend : Interl (t 0) (b N)) {i j : ℕ} (hij : i ≤ j) (hjN : j ≤ N) (hiN : i < N)
    (hj : 1 ≤ j) : Interl (t i) (m j) ∧ Interl (m i) (b j) := by
  obtain ⟨F, hFt, hFm, hFb⟩ : ∃ F : ℕ → ℝ[X], (∀ p, p ≤ i → F p = t p) ∧
      (∀ p, i < p → p ≤ j + 1 → F p = m (p - 1)) ∧ (∀ p, j + 1 < p → F p = b (p - 2)) :=
    ⟨fun p => if p ≤ i then t p else if p ≤ j + 1 then m (p - 1) else b (p - 2),
      fun p hp => by simp [hp], fun p h1 h2 => by simp [Nat.not_le.2 h1, h2],
      fun p h1 => by simp [Nat.not_le.2 (show i < p by lia), Nat.not_le.2 h1]⟩
  have hchain := interl_chain_of_consecutive_of_endpoint F 0 (N + 2) (fun k _ hk => by
      by_cases h1 : k ≤ i
      · rw [hFt k h1]
        exact htne k (by lia)
      by_cases h2 : k ≤ j + 1
      · rw [hFm k (by lia) h2]
        exact hmne (k - 1) (by lia)
      · rw [hFb k (by lia)]
        exact hbne (k - 2) (by lia) (by lia))
    (fun k _ hk => by
      by_cases h1 : k + 1 ≤ i
      · rw [hFt k (by lia), hFt (k + 1) h1]
        exact ht k (k + 1) (by lia) (by lia)
      by_cases h2 : k = i
      · subst h2
        rw [hFt k le_rfl, hFm (k + 1) (by lia) (by lia), Nat.add_sub_cancel]
        exact htm k (by lia)
      by_cases h3 : k + 1 ≤ j + 1
      · rw [hFm k (by lia) (by lia), hFm (k + 1) (by lia) h3]
        rw [Nat.add_sub_cancel]
        exact hm (k - 1) k (by lia) (by lia)
      by_cases h4 : k = j + 1
      · subst h4
        rw [hFm (j + 1) (by lia) le_rfl, hFb (j + 1 + 1) (by lia), Nat.add_sub_cancel,
          show j + 1 + 1 - 2 = j by lia]
        exact hmb j hjN
      · rw [hFb k (by lia), hFb (k + 1) (by lia)]
        have := hb (k - 2) (k + 1 - 2) (by lia) (by lia)
        exact this)
    (by
      rw [hFt 0 (by lia), hFb (N + 2) (by lia), Nat.add_sub_cancel]
      exact hend)
  constructor
  · have := hchain i (j + 1) (by lia) (by lia) (by lia)
    rwa [hFt i le_rfl, hFm (j + 1) (by lia) le_rfl, Nat.add_sub_cancel] at this
  · have := hchain (i + 1) (j + 2) (by lia) (by lia) (by lia)
    rwa [hFm (i + 1) (by lia) (by lia), hFb (j + 2) (by lia), Nat.add_sub_cancel,
      Nat.add_sub_cancel] at this

/-- The path `t₀, …, tₙ, b₁, …, b_{n+1}` of the proof of Lemma 3.8: if consecutive entries
(in particular `tₙ ⪯ b₁`) and the two ends interlace, then `tᵢ ⪯ bⱼ` for `i ≤ n`,
`1 ≤ j ≤ n + 1`. -/
private theorem path_diag (n : ℕ) (t b : ℕ → ℝ[X])
    (htne : ∀ k, k ≤ n → t k ≠ 0) (hbne : ∀ k, 1 ≤ k → k ≤ n + 1 → b k ≠ 0)
    (ht : ∀ i j, i < j → j ≤ n → Interl (t i) (t j))
    (hb : ∀ i j, i < j → j ≤ n + 1 → Interl (b i) (b j))
    (hdiag : Interl (t n) (b 1)) (hend : Interl (t 0) (b (n + 1)))
    {i j : ℕ} (hi : i ≤ n) (hj1 : 1 ≤ j) (hj : j ≤ n + 1) : Interl (t i) (b j) := by
  obtain ⟨F, hFt, hFb⟩ : ∃ F : ℕ → ℝ[X], (∀ p, p ≤ n → F p = t p) ∧
      (∀ p, n < p → F p = b (p - n)) :=
    ⟨fun p => if p ≤ n then t p else b (p - n), fun p hp => by simp [hp],
      fun p hp => by simp [Nat.not_le.2 hp]⟩
  have hchain := interl_chain_of_consecutive_of_endpoint F 0 (2 * n + 1) (fun k _ hk => by
      by_cases h1 : k ≤ n
      · rw [hFt k h1]
        exact htne k h1
      · rw [hFb k (by lia)]
        exact hbne (k - n) (by lia) (by lia))
    (fun k _ hk => by
      by_cases h1 : k + 1 ≤ n
      · rw [hFt k (by lia), hFt (k + 1) h1]
        exact ht k (k + 1) (by lia) h1
      by_cases h2 : k = n
      · subst h2
        rw [hFt k le_rfl, hFb (k + 1) (by lia), show k + 1 - k = 1 by lia]
        exact hdiag
      · rw [hFb k (by lia), hFb (k + 1) (by lia)]
        exact hb (k - n) (k + 1 - n) (by lia) (by lia))
    (by
      rw [hFt 0 (by lia), hFb (2 * n + 1) (by lia), show 2 * n + 1 - n = n + 1 by lia]
      exact hend)
  have := hchain i (n + j) (by lia) (by lia) (by lia)
  rwa [hFt i hi, hFb (n + j) (by lia), Nat.add_sub_cancel_left] at this

private theorem nn_top (n : ℕ) (T : Finset ℕ) (k : ℕ) : HasNonnegCoeffs (top n T k) :=
  hasNonnegCoeffs_refined n k ∅ (T.erase 0)

private theorem nn_mid (n : ℕ) (T : Finset ℕ) (k : ℕ) : HasNonnegCoeffs (mid n T k) :=
  hasNonnegCoeffs_refined n k ∅ T

private theorem nn_bot (n : ℕ) (T : Finset ℕ) (k : ℕ) : HasNonnegCoeffs (bot n T k) :=
  hasNonnegCoeffs_refined n k {0} T

/-- Hoster--Stump, Lemma 3.8: the diagram `D_{n+1}(T)` is an interlacing diagram as soon as
its three rows interlace, every top entry interlaces the bottom entry below it, and
`top_n ⪯ bot_1`, together with the nonvanishing and splitting statements. -/
theorem IsInterlacingDiagram.of_five {n : ℕ} {T : Finset ℕ}
    (htne : ∀ k, k ≤ n → top (n + 1) T k ≠ 0)
    (hbne : ∀ k, 1 ≤ k → k ≤ n + 1 → bot (n + 1) T k ≠ 0)
    (hmne : ∀ k, k ≤ n + 1 → mid (n + 1) T k ≠ 0)
    (hsp : ∀ k, k ≤ n + 1 → (top (n + 1) T k ≠ 0 → (top (n + 1) T k).Splits) ∧
      (mid (n + 1) T k).Splits ∧ (bot (n + 1) T k ≠ 0 → (bot (n + 1) T k).Splits))
    (ht : ∀ i j, i < j → j ≤ n + 1 → Interl (top (n + 1) T i) (top (n + 1) T j))
    (hm : ∀ i j, i < j → j ≤ n + 1 → Interl (mid (n + 1) T i) (mid (n + 1) T j))
    (hb : ∀ i j, i < j → j ≤ n + 1 → Interl (bot (n + 1) T i) (bot (n + 1) T j))
    (hcol : ∀ k, k ≤ n + 1 → Interl (top (n + 1) T k) (bot (n + 1) T k))
    (hdiag : Interl (top (n + 1) T n) (bot (n + 1) T 1)) :
    IsInterlacingDiagram (n + 1) T := by
  have htm : ∀ k, k ≤ n + 1 → Interl (top (n + 1) T k) (mid (n + 1) T k) := fun k hk => by
    rw [mid_eq_top_add_bot]
    exact interl_add_right_of_common_left_of_nonneg (Interl.refl (hsp k hk).1) (hcol k hk)
      (nn_top _ _ _) (nn_bot _ _ _)
  have hmb : ∀ k, k ≤ n + 1 → Interl (mid (n + 1) T k) (bot (n + 1) T k) := fun k hk => by
    rw [mid_eq_top_add_bot]
    exact interl_add_left_of_common_right_of_nonneg (hcol k hk) (Interl.refl (hsp k hk).2.2)
      (nn_top _ _ _) (nn_bot _ _ _)
  have hend : Interl (top (n + 1) T 0) (bot (n + 1) T (n + 1)) := by
    rw [top_zero_eq_mid_zero, bot_self_eq_mid_self]
    exact hm 0 (n + 1) (by lia) le_rfl
  refine ⟨ht, hm, hb, ?_, ?_, ?_, hmne, hsp⟩
  · intro i j hij hj
    by_cases hj0 : j = 0
    · subst hj0
      obtain rfl : i = 0 := by lia
      exact htm 0 (by lia)
    by_cases hi : i = n + 1
    · rw [hi, top_self]
      exact interl_zero_left _
    · exact (path_col (n + 1) _ _ _ (fun k hk => htne k (by lia)) hmne hbne ht hm hb htm hmb
        hend hij hj (by lia) (by lia)).1
  · intro i j hij hj
    by_cases hj0 : j = 0
    · rw [hj0, bot_zero]
      exact interl_zero_right _
    by_cases hi : i = n + 1
    · obtain rfl : j = n + 1 := by lia
      rw [hi]
      exact hmb _ le_rfl
    · exact (path_col (n + 1) _ _ _ (fun k hk => htne k (by lia)) hmne hbne ht hm hb htm hmb
        hend hij hj (by lia) (by lia)).2
  · intro i j hi hj
    by_cases hj0 : j = 0
    · rw [hj0, bot_zero]
      exact interl_zero_right _
    by_cases hin : i = n + 1
    · rw [hin, top_self]
      exact interl_zero_left _
    · exact path_diag n _ _ htne hbne (fun a c h1 h2 => ht a c h1 (by lia))
        hb hdiag hend (by lia) (by lia) hj

/-! ### The induction step -/

/-- Hoster--Stump, Section 3.1 (Lemmas 3.9--3.13 and 3.8): if `D_n(T')` with
`T' = shiftDown T` is an interlacing diagram, then so is `D_{n+1}(T)`, for `0 ∈ T`. -/
theorem IsInterlacingDiagram.step {n : ℕ} {T : Finset ℕ} (hT : 0 ∈ T)
    (ih : IsInterlacingDiagram n (shiftDown T)) : IsInterlacingDiagram (n + 1) T := by
  have h := Lvl.of_diagram ih
  refine IsInterlacingDiagram.of_five ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro k hk
    rw [top_succ]
    exact h.top_ne hk
  · intro k hk1 _
    rw [bot_succ hT]
    exact h.bot_ne hk1
  · intro k hk
    rw [mid_succ hT]
    exact h.mid_ne hk
  · intro k hk
    rw [top_succ, mid_succ hT, bot_succ hT]
    exact ⟨h.splitsSB le_rfl, h.mid_splits hk, splits_X_mul_of_splits (h.splitsSA hk)⟩
  · intro i j hij hj
    rw [top_succ, top_succ]
    exact h.top_row hij hj
  · intro i j hij hj
    rw [mid_succ hT, mid_succ hT]
    exact h.mid_row hij hj
  · intro i j hij hj
    rw [bot_succ hT, bot_succ hT]
    exact h.bot_row hij hj
  · intro k _
    rw [top_succ, bot_succ hT]
    exact h.col k
  · rw [top_succ, bot_succ hT]
    exact h.diag

/-- Hoster--Stump, Theorem 3.3: for `n ≥ 2` the diagrams `D_n([1, n])` and `D_n([1, n - 1])`
(here `range n` and `range (n - 1)`, with `0`-based positions) are interlacing diagrams. -/
theorem isInterlacingDiagram_range (n : ℕ) (hn : 2 ≤ n) :
    IsInterlacingDiagram n (Finset.range n) ∧ IsInterlacingDiagram n (Finset.range (n - 1)) := by
  induction n, hn using Nat.le_induction with
  | base => exact ⟨isInterlacingDiagram_two_range_two, isInterlacingDiagram_two_range_one⟩
  | succ n hn ih =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by lia⟩
    refine ⟨IsInterlacingDiagram.step (Finset.mem_range.2 (by lia)) ?_,
      IsInterlacingDiagram.step (Finset.mem_range.2 (by lia)) ?_⟩
    · rw [shiftDown_range]
      exact ih.1
    · rw [Nat.add_sub_cancel, shiftDown_range]
      exact ih.2

end RealRooted.HosterStump
