import RealRooted.CommonInterleaver.RootDesc
import RealRooted.HosterStumpInterlacing
import RealRooted.PFPolynomial
import RealRooted.ThresholdMatrix.Basic
import RealRooted.WagnerX.NonnegativeRoots

/-!
# Hoster--Stump, Section 2: sequence-level glue

Zero-aware Wagner chain lemma, preservation of interlacing sequences under lower and upper
partial sums (Lemma 2.3(2),(3)), and the four-polynomial window lemma behind Lemma 2.3(4),(5),
all for the zero-aware relation `Interl`.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace HosterStump

/-- Zero-aware form of Wagner's chain lemma (Hoster--Stump, Lemma 2.2): if all `F k` with
`a ≤ k ≤ b` are nonzero, consecutive ones interlace, and the extremes interlace, then every
pair `F i`, `F j` with `a ≤ i ≤ j ≤ b` interlaces. -/
theorem interl_chain_of_consecutive_of_endpoint (F : ℕ → ℝ[X]) (a b : ℕ)
    (hne : ∀ k, a ≤ k → k ≤ b → F k ≠ 0)
    (hcons : ∀ k, a ≤ k → k < b → Interl (F k) (F (k + 1)))
    (hext : Interl (F a) (F b)) :
    ∀ i j, a ≤ i → i ≤ j → j ≤ b → Interl (F i) (F j) := by
  intro i j hai hij hjb
  have hab : a ≤ b := by lia
  exact (strictInterl_chain_of_consecutive_of_endpoint F a b
    (fun k hak hkb => (hcons k hak hkb).toStrictInterl_of_ne (hne k hak (by lia))
      (hne (k + 1) (by lia) (by lia)))
    (hext.toStrictInterl_of_ne (hne a le_rfl hab) (hne b hab le_rfl)) i j hai hij hjb).toInterl

private theorem pairwise_of_getD {R : ℝ[X] → ℝ[X] → Prop} (l : List ℝ[X])
    (h : ∀ i j, i < j → j < l.length → R (l.getD i 0) (l.getD j 0)) : l.Pairwise R := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have := h i j hij hj
  rwa [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at this

private theorem isInterlacingSeq0NonnegRealRooted_of_getD (gs : List ℝ[X])
    (hnn : ∀ k, k < gs.length → HasNonnegCoeffs (gs.getD k 0))
    (hsp : ∀ k, k < gs.length → gs.getD k 0 ≠ 0 → (gs.getD k 0).Splits)
    (hint : ∀ i j, i < j → j < gs.length → Interl (gs.getD i 0) (gs.getD j 0)) :
    IsInterlacingSeq0NonnegRealRooted gs := by
  refine ⟨⟨isInterlacingSeq0_iff_pairwise.2 (pairwise_of_getD gs hint), ?_⟩, ?_⟩
  · intro f hf
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hf
    have := hnn k hk
    rwa [List.getD_eq_getElem _ _ hk] at this
  · intro f hf hf0
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hf
    have := hsp k hk
    rw [List.getD_eq_getElem _ _ hk] at this
    exact ⟨hf0, this hf0⟩

/-- Zero-aware Wagner chain for lists (Hoster--Stump, Lemma 2.2): a list of nonzero,
real-rooted polynomials with nonnegative coefficients, whose consecutive entries interlace
and whose first and last entries interlace, is an interlacing sequence. -/
theorem isInterlacingSeq0NonnegRealRooted_of_chain (fs : List ℝ[X])
    (hnn : ∀ f ∈ fs, HasNonnegCoeffs f) (hne : ∀ f ∈ fs, f ≠ 0)
    (hsplits : ∀ f ∈ fs, f.Splits)
    (hcons : ∀ k, k + 1 < fs.length → Interl (fs.getD k 0) (fs.getD (k + 1) 0))
    (hext : Interl (fs.getD 0 0) (fs.getD (fs.length - 1) 0)) :
    IsInterlacingSeq0NonnegRealRooted fs := by
  have hmem : ∀ k, k < fs.length → fs.getD k 0 ∈ fs := fun k hk => by
    rw [List.getD_eq_getElem _ _ hk]
    exact List.getElem_mem hk
  refine isInterlacingSeq0NonnegRealRooted_of_getD fs
    (fun k hk => hnn _ (hmem k hk)) (fun k hk _ => hsplits _ (hmem k hk)) ?_
  intro i j hij hj
  exact interl_chain_of_consecutive_of_endpoint (fun k => fs.getD k 0) 0 (fs.length - 1)
    (fun k _ hk => hne _ (hmem k (by lia))) (fun k _ hk => hcons k (by lia)) hext i j
    (Nat.zero_le i) hij.le (by lia)

/-! ### Partial sums as finite sums -/

private theorem sum_take_eq_sum_range (fs : List ℝ[X]) (k : ℕ) :
    (fs.take k).sum = ∑ m ∈ Finset.range k, fs.getD m 0 := by
  induction fs generalizing k with
  | nil => simp
  | cons f fs ih =>
    cases k with
    | zero => simp
    | succ k => simp [Finset.sum_range_succ', ih, add_comm]

private theorem sum_drop_eq_sum_Ico (fs : List ℝ[X]) (k : ℕ) :
    (fs.drop k).sum = ∑ m ∈ Finset.Ico k fs.length, fs.getD m 0 := by
  by_cases hk : k ≤ fs.length
  · have h1 := List.sum_take_add_sum_drop fs k
    have h2 : fs.sum = ∑ m ∈ Finset.range fs.length, fs.getD m 0 := by
      simpa using sum_take_eq_sum_range fs fs.length
    rw [sum_take_eq_sum_range, h2, ← Finset.sum_range_add_sum_Ico _ hk] at h1
    exact add_left_cancel h1
  · rw [List.drop_eq_nil_of_le (by lia), Finset.Ico_eq_empty_of_le (by lia)]
    simp

private theorem lowerPartialSums_length (fs : List ℝ[X]) :
    (lowerPartialSums fs).length = fs.length := by
  induction fs with
  | nil => simp [lowerPartialSums]
  | cons f fs ih => simp [lowerPartialSums, ih]

private theorem lowerPartialSums_getD (fs : List ℝ[X]) (k : ℕ) (hk : k < fs.length) :
    (lowerPartialSums fs).getD k 0 = ∑ m ∈ Finset.range (k + 1), fs.getD m 0 := by
  induction fs generalizing k with
  | nil => simp at hk
  | cons f fs ih =>
    cases k with
    | zero => simp [lowerPartialSums]
    | succ k =>
      have hk' : k < fs.length := by simpa using hk
      have hk'' : k < (lowerPartialSums fs).length := by rwa [lowerPartialSums_length]
      rw [Finset.sum_range_succ' _ (k + 1)]
      simp only [lowerPartialSums, List.getD_cons_succ, List.getD_cons_zero]
      rw [List.getD_eq_getElem _ _ (by simpa using hk''), List.getElem_map,
        ← List.getD_eq_getElem _ _ hk'', ih k hk', add_comm]

private theorem lowerPartialSums_append_singleton (l : List ℝ[X]) (a : ℝ[X]) :
    lowerPartialSums (l ++ [a]) = lowerPartialSums l ++ [l.sum + a] := by
  induction l with
  | nil => simp [lowerPartialSums]
  | cons f l ih => simp [lowerPartialSums, ih, add_assoc]

private theorem upperPartialSums_cons (f : ℝ[X]) (fs : List ℝ[X]) :
    upperPartialSums (f :: fs) = (f + fs.sum) :: upperPartialSums fs := by
  simp [upperPartialSums, lowerPartialSums_append_singleton, add_comm]

private theorem upperPartialSums_length (fs : List ℝ[X]) :
    (upperPartialSums fs).length = fs.length := by
  simp [upperPartialSums, lowerPartialSums_length]

private theorem upperPartialSums_getD (fs : List ℝ[X]) (k : ℕ) :
    (upperPartialSums fs).getD k 0 = (fs.drop k).sum := by
  induction fs generalizing k with
  | nil => simp [upperPartialSums, lowerPartialSums]
  | cons f fs ih =>
    cases k with
    | zero => simp [upperPartialSums_cons]
    | succ k => rw [upperPartialSums_cons, List.getD_cons_succ, List.drop_succ_cons, ih]

private theorem sum_drop_take_eq_sum_Ico (fs : List ℝ[X]) (k j : ℕ) :
    ((fs.drop k).take j).sum = ∑ m ∈ Finset.Ico k (k + j), fs.getD m 0 := by
  rw [sum_take_eq_sum_range, Finset.sum_Ico_eq_sum_range]
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

private theorem movingWindowSums_length (w : ℕ) (fs : List ℝ[X]) :
    (movingWindowSums w fs).length = fs.length - w := by
  simp [movingWindowSums]

private theorem movingWindowSums_getD (w : ℕ) (fs : List ℝ[X]) (k : ℕ)
    (hk : k < fs.length - w) :
    (movingWindowSums w fs).getD k 0 = ∑ m ∈ Finset.Ico k (k + (w + 1)), fs.getD m 0 := by
  rw [List.getD_eq_getElem _ _ (by rw [movingWindowSums_length]; exact hk),
    ← sum_drop_take_eq_sum_Ico]
  simp [movingWindowSums]

private theorem xShiftedSplitSums_length (fs : List ℝ[X]) :
    (xShiftedSplitSums fs).length = fs.length + 1 := by
  simp [xShiftedSplitSums]

private theorem xShiftedSplitSums_getD (fs : List ℝ[X]) (k : ℕ) (hk : k < fs.length + 1) :
    (xShiftedSplitSums fs).getD k 0 =
      X * ∑ m ∈ Finset.Ico 0 k, fs.getD m 0 + ∑ m ∈ Finset.Ico k fs.length, fs.getD m 0 := by
  rw [List.getD_eq_getElem _ _ (by rw [xShiftedSplitSums_length]; exact hk),
    ← sum_drop_eq_sum_Ico, ← Finset.range_eq_Ico, ← sum_take_eq_sum_range]
  simp [xShiftedSplitSums]

/-- Window lemma for four pairwise interlacing polynomials (the engine of Hoster--Stump,
Lemma 2.3(4),(5)): `f₁ + f₂ + f₃ ⪯ f₂ + f₃ + f₄`.  The relation `f₂ ⪯ f₃` is needed only
through the splitting hypothesis on `f₂ + f₃`. -/
theorem Interl.window_three {f₁ f₂ f₃ f₄ : ℝ[X]}
    (h12 : Interl f₁ f₂) (h13 : Interl f₁ f₃) (h14 : Interl f₁ f₄)
    (h24 : Interl f₂ f₄) (h34 : Interl f₃ f₄)
    (hn₁ : HasNonnegCoeffs f₁) (hn₂ : HasNonnegCoeffs f₂) (hn₃ : HasNonnegCoeffs f₃)
    (hn₄ : HasNonnegCoeffs f₄) (hsplit : f₂ + f₃ ≠ 0 → (f₂ + f₃).Splits) :
    Interl (f₁ + f₂ + f₃) (f₂ + f₃ + f₄) := by
  have hn₂₃ : HasNonnegCoeffs (f₂ + f₃) := hn₂.add hn₃
  rw [add_assoc]
  refine interl_add_left_of_common_right_of_nonneg ?_ ?_ hn₁ hn₂₃
  · exact interl_add_right_of_common_left_of_nonneg
      (interl_add_right_of_common_left_of_nonneg h12 h13 hn₂ hn₃) h14 hn₂₃ hn₄
  · exact interl_add_right_of_common_left_of_nonneg (Interl.refl hsplit)
      (interl_add_left_of_common_right_of_nonneg h24 h34 hn₂ hn₃) hn₂₃ hn₄

/-- Two interlacing polynomials with nonnegative coefficients have a splitting sum. -/
theorem splits_add_of_interl {f g : ℝ[X]} (h : Interl f g)
    (nf : HasNonnegCoeffs f) (ng : HasNonnegCoeffs g)
    (sf : f ≠ 0 → f.Splits) (sg : g ≠ 0 → g.Splits) : f + g ≠ 0 → (f + g).Splits := by
  intro hfg
  by_cases hf : f = 0
  · simpa [hf] using sg (by simpa [hf] using hfg)
  · have := interl_add_right_of_common_left_of_nonneg (Interl.refl sf) h nf ng
    exact (this.toStrictInterl_of_ne hf hfg).2.1.2

private theorem splits_add_X_mul_of_interl {P W : ℝ[X]} (hPW : Interl P W)
    (nnP : HasNonnegCoeffs P) (nnW : HasNonnegCoeffs W)
    (sP : P ≠ 0 → P.Splits) (sW : W ≠ 0 → W.Splits) :
    W + X * P ≠ 0 → (W + X * P).Splits := by
  intro hne
  have hWXP : Interl W (X * P) := interl_mul_X_of_interl hPW nnP nnW
  have hfs : IsInterlacingSeq0Nonneg [W, X * P] :=
    ⟨isInterlacingSeq0_iff_pairwise.2 (by simpa using hWXP), by
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl
      · exact nnW
      · exact nnP.X_mul⟩
  have hreal : ∀ f ∈ [W, X * P], f ≠ 0 → (f ≠ 0 ∧ f.Splits) := by
    intro f hf hf0
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · exact ⟨hf0, sW hf0⟩
    · have hP0 : P ≠ 0 := fun h => hf0 (by simp [h])
      exact isRealRooted_X_mul hP0 (sP hP0)
  simpa using (isRealRooted_sum_of_isInterlacingSeq0Nonneg hfs hreal (by simpa using hne)).2

private theorem interl_X_mul_add_add_X_mul {P M W : ℝ[X]} (hPM : Interl P M)
    (hPW : Interl P W) (hMW : Interl M W) (nnP : HasNonnegCoeffs P)
    (nnM : HasNonnegCoeffs M) (nnW : HasNonnegCoeffs W) (sP : P ≠ 0 → P.Splits)
    (sM : M ≠ 0 → M.Splits) (sW : W ≠ 0 → W.Splits) :
    Interl (X * P + (M + W)) (X * (P + M) + W) := by
  have key := Interl.window_three (f₁ := M) (f₂ := W) (f₃ := X * P) (f₄ := X * M) hMW
    (interl_mul_X_of_interl hPM nnP nnM) (interl_mul_X_of_interl (Interl.refl sM) nnM nnM)
    (interl_mul_X_of_interl hMW nnM nnW) (hPM.mul_X_both_of_nonneg nnP nnM) nnM nnW nnP.X_mul
    nnM.X_mul (splits_add_X_mul_of_interl hPW nnP nnW sP sW)
  rw [show X * P + (M + W) = M + W + X * P by ring,
    show X * (P + M) + W = W + X * P + X * M by ring]
  exact key

end HosterStump

/-! ### Facts about an interlacing sequence, indexed by `getD` -/

namespace IsInterlacingSeq0NonnegRealRooted

private theorem nonnegCoeffs_getD {fs : List ℝ[X]} (h : IsInterlacingSeq0NonnegRealRooted fs)
    (m : ℕ) : HasNonnegCoeffs (fs.getD m 0) := by
  by_cases hm : m < fs.length
  · rw [List.getD_eq_getElem _ _ hm]
    exact h.nonnegCoeffs _ (List.getElem_mem hm)
  · rw [List.getD_eq_default _ _ (by lia)]
    exact hasNonnegCoeffs_zero

private theorem interl_getD {fs : List ℝ[X]} (h : IsInterlacingSeq0NonnegRealRooted fs)
    {i j : ℕ} (hij : i < j) : Interl (fs.getD i 0) (fs.getD j 0) := by
  by_cases hj : j < fs.length
  · have := (List.pairwise_iff_getElem.1 (isInterlacingSeq0_iff_pairwise.1 h.interlacingSeq0))
      i j (by lia) hj hij
    rwa [List.getD_eq_getElem _ _ (by lia), List.getD_eq_getElem _ _ hj]
  · rw [List.getD_eq_default fs 0 (n := j) (by lia)]
    exact interl_zero_right _

private theorem splits_sum_of_sublist {fs gs : List ℝ[X]}
    (h : IsInterlacingSeq0NonnegRealRooted fs) (hgs : gs.Sublist fs) (hne : gs.sum ≠ 0) :
    gs.sum.Splits :=
  (isRealRooted_sum_of_isInterlacingSeq0Nonneg (h.sublist hgs).1 (h.sublist hgs).2 hne).2

private theorem splits_sum_Ico {fs : List ℝ[X]} (h : IsInterlacingSeq0NonnegRealRooted fs)
    (a b : ℕ) (hne : ∑ m ∈ Finset.Ico a b, fs.getD m 0 ≠ 0) :
    (∑ m ∈ Finset.Ico a b, fs.getD m 0).Splits := by
  by_cases hab : a ≤ b
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hab
    rw [← HosterStump.sum_drop_take_eq_sum_Ico] at hne ⊢
    exact splits_sum_of_sublist h ((List.take_sublist _ _).trans (List.drop_sublist _ _)) hne
  · simp [Finset.Ico_eq_empty_of_le (show b ≤ a by lia)] at hne

private theorem nonnegCoeffs_sum_Ico {fs : List ℝ[X]} (h : IsInterlacingSeq0NonnegRealRooted fs)
    (a b : ℕ) : HasNonnegCoeffs (∑ m ∈ Finset.Ico a b, fs.getD m 0) :=
  hasNonnegCoeffs_finsetSum _ _ fun m _ => nonnegCoeffs_getD h m

/-- Sums over index intervals `[a, b)` and `[c, d)` with `b ≤ c` interlace. -/
private theorem interl_sum_Ico {fs : List ℝ[X]} (h : IsInterlacingSeq0NonnegRealRooted fs)
    {a b c d : ℕ} (hbc : b ≤ c) :
    Interl (∑ m ∈ Finset.Ico a b, fs.getD m 0) (∑ m ∈ Finset.Ico c d, fs.getD m 0) :=
  Interl.finsetSum_pairwise_of_nonneg _ _ _ _
    (fun ℓ hℓ m hm => interl_getD h (by rw [Finset.mem_Ico] at hℓ hm; lia))
    (fun m _ => nonnegCoeffs_getD h m) fun m _ => nonnegCoeffs_getD h m

/-- Lower partial sums of an interlacing sequence form an interlacing sequence
(Hoster--Stump, Lemma 2.3(2)): `[f₀, f₀ + f₁, f₀ + f₁ + f₂, …]`. -/
theorem lowerPartialSums {fs : List ℝ[X]} (h : IsInterlacingSeq0NonnegRealRooted fs) :
    IsInterlacingSeq0NonnegRealRooted (HosterStump.lowerPartialSums fs) := by
  have hlen := HosterStump.lowerPartialSums_length fs
  have hget : ∀ k, k < fs.length → (HosterStump.lowerPartialSums fs).getD k 0 =
      ∑ m ∈ Finset.Ico 0 (k + 1), fs.getD m 0 := fun k hk => by
    rw [HosterStump.lowerPartialSums_getD _ _ hk, Finset.range_eq_Ico]
  refine HosterStump.isInterlacingSeq0NonnegRealRooted_of_getD _ ?_ ?_ ?_
  · intro k hk
    rw [hget k (by lia)]
    exact nonnegCoeffs_sum_Ico h _ _
  · intro k hk hne
    rw [hget k (by lia)] at hne ⊢
    exact splits_sum_Ico h _ _ hne
  · intro i j hij hj
    rw [hlen] at hj
    rw [hget i (by lia), hget j hj,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le (i + 1)) (show i + 1 ≤ j + 1 by lia)]
    refine interl_add_right_of_common_left_of_nonneg (Interl.refl (splits_sum_Ico h _ _)) ?_
      (nonnegCoeffs_sum_Ico h _ _) (nonnegCoeffs_sum_Ico h _ _)
    refine Interl.finsetSum_left_of_nonneg _ _ _ ?_ fun m _ => nonnegCoeffs_getD h m
    intro ℓ hℓ
    rw [Finset.mem_Ico] at hℓ
    exact Interl.finsetSum_right_of_nonneg _ _ _
      (fun m hm => interl_getD h (by rw [Finset.mem_Ico] at hm; lia))
      fun m _ => nonnegCoeffs_getD h m

/-- Upper partial sums of an interlacing sequence form an interlacing sequence
(Hoster--Stump, Lemma 2.3(3)): `[Σ fₖ, Σ_{k ≥ 1} fₖ, …, f_{n-1}]`. -/
theorem upperPartialSums {fs : List ℝ[X]} (h : IsInterlacingSeq0NonnegRealRooted fs) :
    IsInterlacingSeq0NonnegRealRooted (HosterStump.upperPartialSums fs) := by
  have hlen := HosterStump.upperPartialSums_length fs
  have hget : ∀ k, (HosterStump.upperPartialSums fs).getD k 0 =
      ∑ m ∈ Finset.Ico k fs.length, fs.getD m 0 := fun k => by
    rw [HosterStump.upperPartialSums_getD, HosterStump.sum_drop_eq_sum_Ico]
  refine HosterStump.isInterlacingSeq0NonnegRealRooted_of_getD _ ?_ ?_ ?_
  · intro k _
    rw [hget k]
    exact nonnegCoeffs_sum_Ico h _ _
  · intro k _ hne
    rw [hget k] at hne ⊢
    exact splits_sum_Ico h _ _ hne
  · intro i j hij hj
    rw [hlen] at hj
    rw [hget i, hget j, ← Finset.sum_Ico_consecutive _ hij.le hj.le]
    exact interl_add_left_of_common_right_of_nonneg (interl_sum_Ico h le_rfl)
      (Interl.refl (splits_sum_Ico h _ _)) (nonnegCoeffs_sum_Ico h _ _)
      (nonnegCoeffs_sum_Ico h _ _)

/-- Moving window sums of an interlacing sequence form an interlacing sequence
(Hoster--Stump, Lemma 2.3(4)): the sums of `w + 1` consecutive terms. -/
theorem movingWindowSums (w : ℕ) {fs : List ℝ[X]} (h : IsInterlacingSeq0NonnegRealRooted fs) :
    IsInterlacingSeq0NonnegRealRooted (HosterStump.movingWindowSums w fs) := by
  have hlen := HosterStump.movingWindowSums_length w fs
  have hget := HosterStump.movingWindowSums_getD w fs
  refine HosterStump.isInterlacingSeq0NonnegRealRooted_of_getD _ ?_ ?_ ?_
  · intro k hk
    rw [hget k (by lia)]
    exact nonnegCoeffs_sum_Ico h _ _
  · intro k hk hne
    rw [hget k (by lia)] at hne ⊢
    exact splits_sum_Ico h _ _ hne
  · intro i j hij hj
    rw [hlen] at hj
    rw [hget i (by lia), hget j hj]
    rcases le_or_gt j (i + w) with hov | hdis
    · rw [← Finset.sum_Ico_consecutive _ hij.le (show j ≤ i + (w + 1) by lia),
        ← Finset.sum_Ico_consecutive _ (show j ≤ i + (w + 1) by lia)
          (show i + (w + 1) ≤ j + (w + 1) by lia)]
      refine interl_add_left_of_common_right_of_nonneg ?_ ?_ (nonnegCoeffs_sum_Ico h _ _)
        (nonnegCoeffs_sum_Ico h _ _)
      · exact interl_add_right_of_common_left_of_nonneg (interl_sum_Ico h le_rfl)
          (interl_sum_Ico h (by lia)) (nonnegCoeffs_sum_Ico h _ _) (nonnegCoeffs_sum_Ico h _ _)
      · exact interl_add_right_of_common_left_of_nonneg (Interl.refl (splits_sum_Ico h _ _))
          (interl_sum_Ico h le_rfl) (nonnegCoeffs_sum_Ico h _ _) (nonnegCoeffs_sum_Ico h _ _)
    · exact interl_sum_Ico h (by lia)

/-- The `X`-shifted split sums `X · (f₀ + ⋯ + f_{k-1}) + (f_k + ⋯ + f_{n-1})`,
`0 ≤ k ≤ n`, of an interlacing sequence form an interlacing sequence
(Hoster--Stump, Lemma 2.3(5)). -/
theorem xShiftedSplitSums {fs : List ℝ[X]} (h : IsInterlacingSeq0NonnegRealRooted fs) :
    IsInterlacingSeq0NonnegRealRooted (HosterStump.xShiftedSplitSums fs) := by
  have hlen := HosterStump.xShiftedSplitSums_length fs
  have hget := HosterStump.xShiftedSplitSums_getD fs
  have nn := nonnegCoeffs_sum_Ico h
  have sp := splits_sum_Ico h
  refine HosterStump.isInterlacingSeq0NonnegRealRooted_of_getD _ ?_ ?_ ?_
  · intro k hk
    rw [hget k (by lia)]
    exact ((nn _ _).X_mul).add (nn _ _)
  · intro k hk hne
    rw [hget k (by lia)] at hne ⊢
    rw [add_comm] at hne ⊢
    exact HosterStump.splits_add_X_mul_of_interl (interl_sum_Ico h (le_refl k))
      (nn _ _) (nn _ _) (sp _ _) (sp _ _) hne
  · intro i j hij hj
    rw [hlen] at hj
    rw [hget i (by lia), hget j (by lia)]
    have e1 : ∑ m ∈ Finset.Ico i fs.length, fs.getD m 0 =
        ∑ m ∈ Finset.Ico i j, fs.getD m 0 + ∑ m ∈ Finset.Ico j fs.length, fs.getD m 0 :=
      (Finset.sum_Ico_consecutive _ hij.le (by lia)).symm
    have e2 : ∑ m ∈ Finset.Ico 0 j, fs.getD m 0 =
        ∑ m ∈ Finset.Ico 0 i, fs.getD m 0 + ∑ m ∈ Finset.Ico i j, fs.getD m 0 :=
      (Finset.sum_Ico_consecutive _ (Nat.zero_le i) hij.le).symm
    rw [e1, e2]
    exact HosterStump.interl_X_mul_add_add_X_mul (interl_sum_Ico h le_rfl)
      (interl_sum_Ico h hij.le) (interl_sum_Ico h le_rfl) (nn _ _) (nn _ _) (nn _ _)
      (sp _ _) (sp _ _) (sp _ _)

end IsInterlacingSeq0NonnegRealRooted
end RealRooted
