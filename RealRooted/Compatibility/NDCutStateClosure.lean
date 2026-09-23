import RealRooted.Compatibility.CutTransformClosure
import RealRooted.Compatibility.Three

/-!
# Successor state order for ordered P/Q cut families

The directed compatibility bridge turns the ordered P/Q hypotheses into
proper-position relations on individual atoms.  Finite cone closure then
orders the reversed inclusive prefixes and forward strict suffixes.
-/

open Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted

/-- Ordered P/Q compatibility recovers the strict interlacing order encoded by
the interface: the `P` block is read in reverse and the `Q` block forward. -/
theorem OrderedCutCompatible.pqInterlacing {m : ℕ}
    {P Q : Fin m → ℝ[X]} (h : OrderedCutCompatible P Q) :
    IsInterlacingSeqNonneg ((List.ofFn P).reverse ++ List.ofFn Q) := by
  refine ⟨?_, ?_⟩
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · rw [List.mem_reverse, List.mem_ofFn] at hp
      rcases hp with ⟨i, rfl⟩
      exact ⟨h.p_splits i, h.p_nonneg i⟩
    · rw [List.mem_ofFn] at hp
      rcases hp with ⟨i, rfl⟩
      exact ⟨h.q_splits i, h.q_nonneg i⟩
  · rw [isInterlacingSeq_iff_pairwise, List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.pairwise_reverse, List.pairwise_ofFn]
      intro i j hij
      exact prec_of_compatible_and_X_mul_left
        (h.p_pos j).ne_zero (h.p_pos i).ne_zero
        (h.p_nonneg j) (h.p_nonneg i)
        (h.pp_reverse hij.le) (h.xpp_reverse hij.le)
    · rw [List.pairwise_ofFn]
      intro i j hij
      exact prec_of_compatible_and_X_mul_left
        (h.q_pos i).ne_zero (h.q_pos j).ne_zero
        (h.q_nonneg i) (h.q_nonneg j)
        (h.qq_forward hij.le) (h.xqq_forward hij.le)
    · intro p hp q hq
      rw [List.mem_reverse, List.mem_ofFn] at hp
      rw [List.mem_ofFn] at hq
      rcases hp with ⟨i, rfl⟩
      rcases hq with ⟨j, rfl⟩
      exact prec_of_compatible_and_X_mul_left
        (h.p_pos i).ne_zero (h.q_pos j).ne_zero
        (h.p_nonneg i) (h.q_nonneg j) (h.pq i j) (h.xpq i j)

private def cutPrefixWeights {m : ℕ} (P : Fin m → ℝ[X])
    (j : Fin m) : List (ℝ × ℝ[X]) :=
  List.ofFn fun i ↦ (if i ≤ j then 1 else 0, P i)

private def cutStrictSuffixWeights {m : ℕ} (Q : Fin m → ℝ[X])
    (j : Fin m) : List (ℝ × ℝ[X]) :=
  List.ofFn fun i ↦ (if j < i then 1 else 0, Q i)

private theorem weightedSum_cutPrefixWeights {m : ℕ}
    (P : Fin m → ℝ[X]) (j : Fin m) :
    weightedSum (cutPrefixWeights P j) = cutPrefix P j := by
  rw [cutPrefixWeights, weightedSum_ofFn]
  unfold cutPrefix
  apply Fintype.sum_congr
  intro i
  by_cases hij : i ≤ j <;> simp [hij]

private theorem weightedSum_cutStrictSuffixWeights {m : ℕ}
    (Q : Fin m → ℝ[X]) (j : Fin m) :
    weightedSum (cutStrictSuffixWeights Q j) = cutStrictSuffix Q j := by
  rw [cutStrictSuffixWeights, weightedSum_ofFn]
  unfold cutStrictSuffix
  apply Fintype.sum_congr
  intro i
  by_cases hji : j < i <;> simp [hji]

private theorem cutPrefix_nonneg {m : ℕ} {P : Fin m → ℝ[X]}
    (hP : ∀ i, HasNonnegCoeffs (P i)) (j : Fin m) :
    HasNonnegCoeffs (cutPrefix P j) := by
  unfold cutPrefix
  apply hasNonnegCoeffs_finsetSum
  intro i _
  by_cases hij : i ≤ j
  · simpa [hij] using hP i
  · simp [hij, hasNonnegCoeffs_zero]

private theorem cutStrictSuffix_nonneg {m : ℕ} {Q : Fin m → ℝ[X]}
    (hQ : ∀ i, HasNonnegCoeffs (Q i)) (j : Fin m) :
    HasNonnegCoeffs (cutStrictSuffix Q j) := by
  unfold cutStrictSuffix
  apply hasNonnegCoeffs_finsetSum
  intro i _
  by_cases hji : j < i
  · simpa [hji] using hQ i
  · simp [hji, hasNonnegCoeffs_zero]

private theorem cutPrefix_realRooted {m : ℕ} {P Q : Fin m → ℝ[X]}
    (h : OrderedCutCompatible P Q) (j : Fin m) :
    cutPrefix P j ≠ 0 ∧ (cutPrefix P j).Splits := by
  have hmem : ∀ ap ∈ cutPrefixWeights P j,
      ap.2 ∈ List.ofFn P ++ List.ofFn Q := by
    intro ap hap
    rcases List.mem_ofFn.mp hap with ⟨i, rfl⟩
    simp
  have hnonneg : ∀ ap ∈ cutPrefixWeights P j, 0 ≤ ap.1 := by
    intro ap hap
    rcases List.mem_ofFn.mp hap with ⟨i, rfl⟩
    by_cases hij : i ≤ j <;> simp [hij]
  have hpos : ∀ ap ∈ cutPrefixWeights P j,
      HasPosLeadingCoeff ap.2 := by
    intro ap hap
    rcases List.mem_ofFn.mp hap with ⟨i, rfl⟩
    exact h.p_pos i
  have hex : ∃ ap ∈ cutPrefixWeights P j, 0 < ap.1 := by
    refine ⟨(1, P j), ?_, by simp⟩
    rw [cutPrefixWeights, List.mem_ofFn]
    exact ⟨j, by simp⟩
  have hsum_pos : HasPosLeadingCoeff
      (weightedSum (cutPrefixWeights P j)) :=
    hasPosLeadingCoeff_weightedSum _ hnonneg hpos hex
  rcases h.familyCompatible_pq (cutPrefixWeights P j) hmem hnonneg with
    hzero | hrr
  · exact False.elim (hsum_pos.ne_zero hzero)
  · simpa [weightedSum_cutPrefixWeights] using hrr

private theorem cutStrictSuffix_splits_of_ne {m : ℕ}
    {P Q : Fin m → ℝ[X]} (h : OrderedCutCompatible P Q) (j : Fin m)
    (hne : cutStrictSuffix Q j ≠ 0) : (cutStrictSuffix Q j).Splits := by
  have hmem : ∀ ap ∈ cutStrictSuffixWeights Q j,
      ap.2 ∈ List.ofFn P ++ List.ofFn Q := by
    intro ap hap
    rcases List.mem_ofFn.mp hap with ⟨i, rfl⟩
    simp
  have hnonneg : ∀ ap ∈ cutStrictSuffixWeights Q j, 0 ≤ ap.1 := by
    intro ap hap
    rcases List.mem_ofFn.mp hap with ⟨i, rfl⟩
    by_cases hji : j < i <;> simp [hji]
  rcases h.familyCompatible_pq (cutStrictSuffixWeights Q j) hmem hnonneg with
    hzero | hrr
  · exact False.elim (hne (by simpa [weightedSum_cutStrictSuffixWeights] using hzero))
  · simpa [weightedSum_cutStrictSuffixWeights] using hrr.2

private def cutMiddle {m : ℕ} (F : Fin m → ℝ[X])
    (i j : Fin m) : ℝ[X] :=
  ∑ k : Fin m, if i < k ∧ k ≤ j then F k else 0

private theorem cutMiddle_nonneg {m : ℕ} {F : Fin m → ℝ[X]}
    (hF : ∀ i, HasNonnegCoeffs (F i)) (i j : Fin m) :
    HasNonnegCoeffs (cutMiddle F i j) := by
  unfold cutMiddle
  apply hasNonnegCoeffs_finsetSum
  intro k _
  by_cases hk : i < k ∧ k ≤ j
  · simpa [hk] using hF k
  · simp [hk, hasNonnegCoeffs_zero]

private theorem cutPrefix_eq_add_cutMiddle {m : ℕ}
    (F : Fin m → ℝ[X]) {i j : Fin m} (hij : i ≤ j) :
    cutPrefix F j = cutPrefix F i + cutMiddle F i j := by
  unfold cutPrefix cutMiddle
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hki : k ≤ i
  · have hkj : k ≤ j := hki.trans hij
    simp [hki, hkj, not_lt_of_ge hki]
  · have hik : i < k := lt_of_not_ge hki
    by_cases hkj : k ≤ j
    · simp [hki, hik, hkj]
    · simp [hki, hik, hkj]

private theorem cutStrictSuffix_eq_cutMiddle_add {m : ℕ}
    (F : Fin m → ℝ[X]) {i j : Fin m} (hij : i ≤ j) :
    cutStrictSuffix F i = cutMiddle F i j + cutStrictSuffix F j := by
  unfold cutStrictSuffix cutMiddle
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hik : i < k
  · by_cases hkj : k ≤ j
    · simp [hik, hkj, not_lt_of_ge hkj]
    · have hjk : j < k := lt_of_not_ge hkj
      simp [hik, hkj, hjk]
  · have hnotjk : ¬j < k := fun hjk ↦ hik (hij.trans_lt hjk)
    simp [hik, hnotjk]

private theorem cutPrefix_prec0_reverse {m : ℕ}
    {P Q : Fin m → ℝ[X]} (h : OrderedCutCompatible P Q)
    {i j : Fin m} (hij : i ≤ j) :
    Interl (cutPrefix P j) (cutPrefix P i) := by
  have hmid : Interl (cutMiddle P i j) (cutPrefix P i) := by
    unfold cutMiddle cutPrefix
    apply Interl.finsetSum_pairwise_of_nonneg Finset.univ Finset.univ
    · intro k _ l _
      by_cases hk : i < k ∧ k ≤ j
      · by_cases hl : l ≤ i
        · simp only [hk, hl, ite_true]
          apply StrictInterl.toInterl
          exact prec_of_compatible_and_X_mul_left
            (h.p_pos k).ne_zero (h.p_pos l).ne_zero
            (h.p_nonneg k) (h.p_nonneg l)
            (h.pp_reverse (hl.trans hk.1.le))
            (h.xpp_reverse (hl.trans hk.1.le))
        · simp [hk, hl, interl_zero_right]
      · simp [hk, interl_zero_left]
    · intro k _
      by_cases hk : i < k ∧ k ≤ j
      · simpa [hk] using h.p_nonneg k
      · simp [hk, hasNonnegCoeffs_zero]
    · intro k _
      by_cases hk : k ≤ i
      · simpa [hk] using h.p_nonneg k
      · simp [hk, hasNonnegCoeffs_zero]
  have hpre_rr := cutPrefix_realRooted h i
  have hself : Interl (cutPrefix P i) (cutPrefix P i) :=
    Interl.refl fun _ => hpre_rr.2
  rw [cutPrefix_eq_add_cutMiddle P hij]
  exact interl_add_left_of_common_right_of_nonneg hself hmid
    (cutPrefix_nonneg h.p_nonneg i) (cutMiddle_nonneg h.p_nonneg i j)

private theorem cutPrefix_prec0_cutStrictSuffix {m : ℕ}
    {P Q : Fin m → ℝ[X]} (h : OrderedCutCompatible P Q)
    (i j : Fin m) : Interl (cutPrefix P i) (cutStrictSuffix Q j) := by
  unfold cutPrefix cutStrictSuffix
  apply Interl.finsetSum_pairwise_of_nonneg Finset.univ Finset.univ
  · intro k _ l _
    by_cases hk : k ≤ i
    · by_cases hl : j < l
      · simp only [hk, hl, ite_true]
        exact (prec_of_compatible_and_X_mul_left
          (h.p_pos k).ne_zero (h.q_pos l).ne_zero
          (h.p_nonneg k) (h.q_nonneg l) (h.pq k l) (h.xpq k l)).toInterl
      · simp [hk, hl, interl_zero_right]
    · simp [hk, interl_zero_left]
  · intro k _
    by_cases hk : k ≤ i
    · simpa [hk] using h.p_nonneg k
    · simp [hk, hasNonnegCoeffs_zero]
  · intro k _
    by_cases hk : j < k
    · simpa [hk] using h.q_nonneg k
    · simp [hk, hasNonnegCoeffs_zero]

private theorem cutStrictSuffix_prec0_forward {m : ℕ}
    {P Q : Fin m → ℝ[X]} (h : OrderedCutCompatible P Q)
    {i j : Fin m} (hij : i ≤ j) :
    Interl (cutStrictSuffix Q i) (cutStrictSuffix Q j) := by
  have hmid : Interl (cutMiddle Q i j) (cutStrictSuffix Q j) := by
    unfold cutMiddle cutStrictSuffix
    apply Interl.finsetSum_pairwise_of_nonneg Finset.univ Finset.univ
    · intro k _ l _
      by_cases hk : i < k ∧ k ≤ j
      · by_cases hl : j < l
        · simp only [hk, hl, ite_true]
          exact (prec_of_compatible_and_X_mul_left
            (h.q_pos k).ne_zero (h.q_pos l).ne_zero
            (h.q_nonneg k) (h.q_nonneg l)
            (h.qq_forward (hk.2.trans hl.le))
            (h.xqq_forward (hk.2.trans hl.le))).toInterl
        · simp [hk, hl, interl_zero_right]
      · simp [hk, interl_zero_left]
    · intro k _
      by_cases hk : i < k ∧ k ≤ j
      · simpa [hk] using h.q_nonneg k
      · simp [hk, hasNonnegCoeffs_zero]
    · intro k _
      by_cases hk : j < k
      · simpa [hk] using h.q_nonneg k
      · simp [hk, hasNonnegCoeffs_zero]
  have hself : Interl (cutStrictSuffix Q j) (cutStrictSuffix Q j) :=
    Interl.refl (cutStrictSuffix_splits_of_ne h j)
  rw [cutStrictSuffix_eq_cutMiddle_add Q hij]
  exact interl_add_left_of_common_right_of_nonneg hmid hself
    (cutMiddle_nonneg h.q_nonneg i j) (cutStrictSuffix_nonneg h.q_nonneg j)

/-- Ordered P/Q compatibility controls the exact zero-aware successor state
order consisting of reversed inclusive prefixes followed by strict suffixes. -/
theorem OrderedCutCompatible.ndCutStateInterlacing {m : ℕ}
    {P Q : Fin m → ℝ[X]} (h : OrderedCutCompatible P Q) :
    IsInterlacingSeq0NonnegRealRooted
      ((List.ofFn (cutPrefix P)).reverse ++ List.ofFn (cutStrictSuffix Q)) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [isInterlacingSeq0_iff_pairwise, List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.pairwise_reverse, List.pairwise_ofFn]
      intro i j hij
      exact cutPrefix_prec0_reverse h hij.le
    · rw [List.pairwise_ofFn]
      intro i j hij
      exact cutStrictSuffix_prec0_forward h hij.le
    · intro p hp q hq
      rw [List.mem_reverse, List.mem_ofFn] at hp
      rw [List.mem_ofFn] at hq
      rcases hp with ⟨i, rfl⟩
      rcases hq with ⟨j, rfl⟩
      exact cutPrefix_prec0_cutStrictSuffix h i j
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · rw [List.mem_reverse, List.mem_ofFn] at hp
      rcases hp with ⟨i, rfl⟩
      exact cutPrefix_nonneg h.p_nonneg i
    · rw [List.mem_ofFn] at hp
      rcases hp with ⟨j, rfl⟩
      exact cutStrictSuffix_nonneg h.q_nonneg j
  · intro p hp hp0
    rcases List.mem_append.mp hp with hp | hp
    · rw [List.mem_reverse, List.mem_ofFn] at hp
      rcases hp with ⟨i, rfl⟩
      exact cutPrefix_realRooted h i
    · rw [List.mem_ofFn] at hp
      rcases hp with ⟨j, rfl⟩
      exact ⟨hp0, cutStrictSuffix_splits_of_ne h j hp0⟩

end RealRooted
