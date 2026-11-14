module

public import RealRooted.GammaTransform.Basic
public import RealRooted.InterlacingSequenceBasic
public import RealRooted.StaircaseSum
public import RealRooted.ThresholdMatrix.Basic
import RealRooted.GammaTransform.Preservation
import RealRooted.RowThresholdOne
import RealRooted.Mathlib.Algebra.BigOperators.Group.List
import RealRooted.WagnerX.NonnegativeRoots

/-!
# Signed staircase induction for peak polynomials

We transport the D/U recurrence through the gamma transform and obtain a
marker-one threshold matrix. This gives an alternative to the six-condition
proof for the peak polynomials of P. Alexandersson, A. Jal and M. Quemener,
*Rook-Eulerian polynomials and permutation ideals*.

Columns are zero-based: column `k` represents the signed values `±(k+1)`.
The signed vector is ordered `-m, …, -1, +1, …, +m`. The concrete enumerator
identification is separate from the abstract recurrence proved here.
-/

@[expose] public section

open Polynomial Finset
open scoped BigOperators

noncomputable section

namespace RealRooted.Applications.PeakPolynomials

/-- The refinement with negative first sign in column `k`. -/
def signedDown (n : ℕ) (D U : ℕ → ℝ[X]) (k : ℕ) : ℝ[X] :=
  C 2 * gammaTransform (n - 2) ((D k).comp (C 4 * X)) +
    gammaTransform (n - 1) ((U k).comp (C 4 * X))

/-- The refinement with positive first sign in column `k`. -/
def signedUp (n : ℕ) (D U : ℕ → ℝ[X]) (k : ℕ) : ℝ[X] :=
  C 2 * X * gammaTransform (n - 2) ((D k).comp (C 4 * X)) +
    gammaTransform (n - 1) ((U k).comp (C 4 * X))

/-- The signed first-entry refinements in increasing signed order. -/
def signedVector (n m : ℕ) (D U : ℕ → ℝ[X]) : List ℝ[X] :=
  (List.range m).reverse.map (signedDown n D U) ++
    (List.range m).map (signedUp n D U)

/-- Degree bounds, coefficient signs, and signed interlacing at one level. -/
structure SignedPeakInvariant (n m : ℕ) (D U : ℕ → ℝ[X]) : Prop where
  /-- The level has at least one row. -/
  one_le : 1 ≤ n
  /-- A one-row placement cannot start with a descent. -/
  D_eq_zero_of_eq_one : n = 1 → ∀ k, D k = 0
  /-- Initial descents give the tighter peak bound. -/
  natDegree_D : ∀ k, (D k).natDegree ≤ (n - 2) / 2
  /-- Peaks cannot be adjacent. -/
  natDegree_U : ∀ k, (U k).natDegree ≤ (n - 1) / 2
  /-- The descent refinement has nonnegative coefficients. -/
  nonneg_D : ∀ k, HasNonnegCoeffs (D k)
  /-- The ascent refinement has nonnegative coefficients. -/
  nonneg_U : ∀ k, HasNonnegCoeffs (U k)
  /-- Signed first-entry refinements form a zero-aware interlacing sequence. -/
  interlacing : IsInterlacingSeq0NonnegRealRooted (signedVector n m D U)

private theorem natDegree_rescale (p : ℝ[X]) :
    (p.comp (C 4 * X)).natDegree = p.natDegree := by
  rw [natDegree_comp, natDegree_C_mul (by norm_num : (4 : ℝ) ≠ 0)]
  simp

private theorem signed_pair {n : ℕ} {D U : ℕ → ℝ[X]}
    (hn : 1 ≤ n) (hD0 : n = 1 → ∀ k, D k = 0)
    (hD : ∀ k, (D k).natDegree ≤ (n - 2) / 2) (k : ℕ) :
    signedDown n D U k + signedUp n D U k =
      C 2 * gammaTransform (n - 1) ((D k + U k).comp (C 4 * X)) := by
  rw [add_comp, gammaTransform_add]
  by_cases hn1 : n = 1
  · simp only [signedDown, signedUp, hD0 hn1 k, zero_comp, gammaTransform_zero,
      mul_zero, zero_add, map_ofNat]
    ring
  · have heq : n - 1 = (n - 2) + 1 := by lia
    have hpad := gammaTransform_pad_one (by rw [natDegree_rescale]; exact hD k)
    rw [heq, hpad]
    unfold signedDown signedUp
    rw [heq]
    simp only [map_ofNat]
    ring

private theorem signed_mixed {n : ℕ} {D U : ℕ → ℝ[X]}
    (hn : 1 ≤ n) (hD0 : n = 1 → ∀ k, D k = 0)
    (hU : ∀ k, (U k).natDegree ≤ (n - 1) / 2) (k : ℕ) :
    X * signedDown n D U k + signedUp n D U k =
      gammaTransform n ((X * D k + U k).comp (C 4 * X)) := by
  rw [add_comp, mul_comp, X_comp, gammaTransform_add]
  have hpad : gammaTransform n ((U k).comp (C 4 * X)) =
      (X + 1) * gammaTransform (n - 1) ((U k).comp (C 4 * X)) := by
    conv_lhs => rw [show n = (n - 1) + 1 by lia]
    exact gammaTransform_pad_one (by rw [natDegree_rescale]; exact hU k)
  rw [hpad]
  by_cases hn1 : n = 1
  · simp [signedDown, signedUp, hD0 hn1 k]
    ring
  · have heq : n = (n - 2) + 2 := by lia
    have hX : gammaTransform n (C 4 * X * (D k).comp (C 4 * X)) =
        C 4 * X * gammaTransform (n - 2) ((D k).comp (C 4 * X)) := by
      rw [mul_assoc, gammaTransform_C_mul]
      conv_lhs => rw [heq, gammaTransform_X_mul_two]
      ring
    rw [hX]
    unfold signedDown signedUp
    simp only [map_ofNat]
    ring

/-- Summing the signed refinements gives the denominator-free signing identity.
Only the level and descent-degree hypotheses are needed for this identity. -/
theorem sum_signedVector {n : ℕ} (m : ℕ) (D U : ℕ → ℝ[X])
    (hn : 1 ≤ n) (hD0 : n = 1 → ∀ k, D k = 0)
    (hD : ∀ k, (D k).natDegree ≤ (n - 2) / 2) :
    (signedVector n m D U).sum = gammaTransform (n - 1)
      (C 2 * (∑ k ∈ Finset.range m, (D k + U k)).comp (C 4 * X)) := by
  rw [signedVector, List.sum_append, List.map_reverse, List.sum_reverse,
    List.sum_map_range, List.sum_map_range, ← Finset.sum_add_distrib]
  simp only [Polynomial.sum_comp, gammaTransform_C_mul, gammaTransform_finset_sum,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => signed_pair hn hD0 hD k

private theorem staircase_low (a b : ℕ → ℝ[X]) {m k : ℕ} (hk : k ≤ m) :
    staircaseSum ((List.range m).reverse.map a ++ (List.range m).map b) (m - k) =
      (∑ j ∈ Finset.range k, (a j + b j)) +
        ∑ j ∈ Finset.Ico k m, (X * a j + b j) := by
  rw [List.map_reverse]
  let as := (List.range m).map a
  let bs := (List.range m).map b
  have hle : m - k ≤ as.reverse.length := by simp [as]
  have hsub : as.length - (m - k) = k := by
    simp only [as, List.length_map, List.length_range]
    lia
  change staircaseSum (as.reverse ++ bs) (m - k) = _
  unfold staircaseSum
  rw [List.take_append_of_le_length hle, List.drop_append_of_le_length hle,
    List.take_reverse, List.drop_reverse, hsub, List.sum_reverse, List.sum_append,
    List.sum_reverse]
  simp only [as, bs, ← List.map_take, List.take_range, min_eq_left hk,
    List.sum_map_range, List.sum_drop_map_range_eq_sum_Ico]
  rw [← Finset.sum_range_add_sum_Ico b hk]
  simp only [Finset.sum_add_distrib, Finset.mul_sum]
  ring

private theorem staircase_high (a b : ℕ → ℝ[X]) {m k : ℕ} (hk : k ≤ m) :
    staircaseSum ((List.range m).reverse.map a ++ (List.range m).map b) (m + k) =
      X * (∑ j ∈ Finset.range k, (a j + b j)) +
        ∑ j ∈ Finset.Ico k m, (X * a j + b j) := by
  rw [List.map_reverse]
  let as := (List.range m).map a
  let bs := (List.range m).map b
  have hlen : as.reverse.length ≤ m + k := by simp [as]
  change staircaseSum (as.reverse ++ bs) (m + k) = _
  unfold staircaseSum
  rw [List.take_append, List.drop_append,
    List.take_of_length_le hlen, List.drop_eq_nil_of_le hlen]
  simp only [as, bs, List.length_reverse, List.length_map, List.length_range,
    Nat.add_sub_cancel_left, List.sum_append, List.sum_reverse, List.sum_nil, zero_add,
    ← List.map_take, List.take_range, min_eq_left hk,
    List.sum_map_range, List.sum_drop_map_range_eq_sum_Ico]
  rw [← Finset.sum_range_add_sum_Ico a hk]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- The selected thresholds, including the repeated middle threshold. -/
def signedThresholds (m r : ℕ) : List ℕ :=
  (List.range r).reverse.map (fun k => m - k) ++
    (List.range r).map (fun k => m + k)

/-- The selected thresholds are weakly increasing. -/
theorem pairwise_signedThresholds (m r : ℕ) :
    (signedThresholds m r).Pairwise (· ≤ ·) := by
  rw [signedThresholds, List.pairwise_append]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.pairwise_map, List.pairwise_reverse, List.pairwise_iff_get]
    intro i j hij
    simp only [List.get_eq_getElem, List.getElem_range]
    exact Nat.sub_le_sub_left (Nat.le_of_lt hij) m
  · rw [List.pairwise_map, List.pairwise_iff_get]
    intro i j hij
    simp only [List.get_eq_getElem, List.getElem_range]
    lia
  · intro a ha b hb
    simp only [List.mem_map] at ha hb
    obtain ⟨i, _, rfl⟩ := ha
    obtain ⟨j, _, rfl⟩ := hb
    lia

/-- The two signed outputs of one D/U step are staircase sums at `m-k` and
`m+k`, including both boundary thresholds when the new width is `m+1`. -/
theorem signed_step_entries {n m r : ℕ} {D U D' U' : ℕ → ℝ[X]}
    (h : SignedPeakInvariant n m D U) (hr : r ≤ m + 1)
    (hD : ∀ k < r, D' k = ∑ j ∈ Finset.range k, (D j + U j))
    (hU : ∀ k < r, U' k = ∑ j ∈ Finset.Ico k m, (X * D j + U j))
    {k : ℕ} (hk : k < r) :
    signedDown (n + 1) D' U' k = staircaseSum (signedVector n m D U) (m - k) ∧
      signedUp (n + 1) D' U' k = staircaseSum (signedVector n m D U) (m + k) := by
  have hkm : k ≤ m := by lia
  have hpair := signed_pair (U := U) h.one_le h.D_eq_zero_of_eq_one h.natDegree_D
  have hmixed := signed_mixed (D := D) h.one_le h.D_eq_zero_of_eq_one h.natDegree_U
  have hsumD : C 2 * gammaTransform (n - 1) ((D' k).comp (C 4 * X)) =
      ∑ j ∈ Finset.range k, (signedDown n D U j + signedUp n D U j) := by
    rw [hD k hk, Polynomial.sum_comp, gammaTransform_finset_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => (hpair j).symm
  have hsumU : gammaTransform n ((U' k).comp (C 4 * X)) =
      ∑ j ∈ Finset.Ico k m, (X * signedDown n D U j + signedUp n D U j) := by
    rw [hU k hk, Polynomial.sum_comp, gammaTransform_finset_sum]
    exact Finset.sum_congr rfl fun j _ => (hmixed j).symm
  constructor
  · rw [signedVector, staircase_low _ _ hkm]
    have heq : n + 1 - 2 = n - 1 := by lia
    simpa only [signedDown, Nat.add_sub_cancel, heq] using
      congrArg₂ (· + ·) hsumD hsumU
  · rw [signedVector, staircase_high _ _ hkm]
    have hs := congrArg₂ (fun a b : ℝ[X] => X * a + b) hsumD hsumU
    have heq : n + 1 - 2 = n - 1 := by lia
    calc
      signedUp (n + 1) D' U' k =
          X * (C 2 * gammaTransform (n - 1) ((D' k).comp (C 4 * X))) +
            gammaTransform n ((U' k).comp (C 4 * X)) := by
        rw [signedUp, heq, Nat.add_sub_cancel]
        ring
      _ = _ := hs

/-- The signed D/U step is exactly a marker-one threshold matrix action. -/
theorem signedVector_step {n m r : ℕ} {D U D' U' : ℕ → ℝ[X]}
    (h : SignedPeakInvariant n m D U) (hr : r ≤ m + 1)
    (hD : ∀ k < r, D' k = ∑ j ∈ Finset.range k, (D j + U j))
    (hU : ∀ k < r, U' k = ∑ j ∈ Finset.Ico k m, (X * D j + U j)) :
    signedVector (n + 1) r D' U' =
      matPolyAction (thresholdMatrix (2 * m)
        ((signedThresholds m r).map (fun t => (t, 1)))) (signedVector n m D U) := by
  have hlen : (signedVector n m D U).length = 2 * m := by
    simp [signedVector, two_mul]
  have haction : matPolyAction (thresholdMatrix (2 * m)
        ((signedThresholds m r).map (fun t => (t, 1)))) (signedVector n m D U) =
      (signedThresholds m r).map (staircaseSum (signedVector n m D U)) := by
    rw [← hlen]
    simp [matPolyAction, thresholdMatrix, thresholdRow_one_action_eq_staircaseSum]
  rw [haction, signedVector, signedThresholds, List.map_append, List.map_map,
    List.map_map]
  congr 1
  · apply List.map_congr_left
    intro k hk
    exact (signed_step_entries h hr hD hU (by simpa using hk)).1
  · apply List.map_congr_left
    intro k hk
    exact (signed_step_entries h hr hD hU (by simpa using hk)).2

/-- Every signed refinement of the one-row seed is the constant one. -/
theorem signedPeakInvariant_one (m : ℕ) :
    SignedPeakInvariant 1 m 0 (fun k => if k < m then 1 else 0) := by
  have hmem : ∀ p ∈ signedVector 1 m 0 (fun k => if k < m then 1 else 0),
      p = 1 := by
    intro p hp
    simp only [signedVector, List.mem_append, List.mem_map, List.mem_reverse,
      List.mem_range] at hp
    rcases hp with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩ <;>
      simp [signedDown, signedUp, hk, gammaTransform, gammaBasisTerm]
  refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ k
    rfl
  · intro k
    simp
  · intro k
    split_ifs <;> simp
  · intro k
    exact hasNonnegCoeffs_zero
  · intro k
    split_ifs
    · exact hasNonnegCoeffs_one
    · exact hasNonnegCoeffs_zero
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [isInterlacingSeq0_iff_pairwise]
      apply List.pairwise_iff_get.mpr
      intro i j _
      rw [hmem _ (List.get_mem _ _), hmem _ (List.get_mem _ _)]
      exact Interl.refl fun _ => Polynomial.Splits.one
    · intro p hp
      rw [hmem p hp]
      exact hasNonnegCoeffs_one
    · intro p hp _
      rw [hmem p hp]
      exact ⟨one_ne_zero, Polynomial.Splits.one⟩

private theorem step_degrees {n m r : ℕ} {D U D' U' : ℕ → ℝ[X]}
    (h : SignedPeakInvariant n m D U)
    (hD : ∀ k < r, D' k = ∑ j ∈ Finset.range k, (D j + U j))
    (hU : ∀ k < r, U' k = ∑ j ∈ Finset.Ico k m, (X * D j + U j))
    (hz : ∀ k, r ≤ k → D' k = 0 ∧ U' k = 0) :
    (∀ k, (D' k).natDegree ≤ (n + 1 - 2) / 2) ∧
      (∀ k, (U' k).natDegree ≤ (n + 1 - 1) / 2) := by
  constructor
  · intro k
    by_cases hk : k < r
    · rw [hD k hk]
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro j _
      apply natDegree_add_le_of_degree_le
      · have hj := h.natDegree_D j
        lia
      · have hj := h.natDegree_U j
        lia
    · simp [(hz k (by lia)).1]
  · intro k
    by_cases hk : k < r
    · rw [hU k hk]
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro j _
      apply natDegree_add_le_of_degree_le
      · by_cases hn : n = 1
        · simp [h.D_eq_zero_of_eq_one hn j]
        · have hj := h.natDegree_D j
          have hmul := Polynomial.natDegree_mul_le (p := (X : ℝ[X])) (q := D j)
          have hn1 := h.one_le
          simp only [natDegree_X] at hmul
          lia
      · have hj := h.natDegree_U j
        lia
    · simp [(hz k (by lia)).2]

/-- A D/U recurrence step preserves the signed peak invariant. The support
condition extends the output degree and coefficient bounds to every column. -/
theorem SignedPeakInvariant.step {n m r : ℕ} {D U D' U' : ℕ → ℝ[X]}
    (h : SignedPeakInvariant n m D U) (hr : r ≤ m + 1)
    (hD : ∀ k < r, D' k = ∑ j ∈ Finset.range k, (D j + U j))
    (hU : ∀ k < r, U' k = ∑ j ∈ Finset.Ico k m, (X * D j + U j))
    (hz : ∀ k, r ≤ k → D' k = 0 ∧ U' k = 0) :
    SignedPeakInvariant (n + 1) r D' U' := by
  have hdeg := step_degrees h hD hU hz
  refine ⟨by have hn := h.one_le; lia, ?_, hdeg.1, hdeg.2, ?_, ?_, ?_⟩
  · intro hn
    have hn1 := h.one_le
    lia
  · intro k
    by_cases hk : k < r
    · rw [hD k hk]
      exact hasNonnegCoeffs_finsetSum _ _ fun j _ => (h.nonneg_D j).add (h.nonneg_U j)
    · rw [(hz k (by lia)).1]
      exact hasNonnegCoeffs_zero
  · intro k
    by_cases hk : k < r
    · rw [hU k hk]
      exact hasNonnegCoeffs_finsetSum _ _ fun j _ =>
        (hasNonnegCoeffs_X.mul (h.nonneg_D j)).add (h.nonneg_U j)
    · rw [(hz k (by lia)).2]
      exact hasNonnegCoeffs_zero
  · rw [signedVector_step h hr hD hU]
    refine thresholdMatrix_preserves_interlacing_seq0_of_entry_weak _ ?_ ?_
      _ (by simp [signedVector, two_mul]) h.interlacing.1 h.interlacing.2
    · intro p hp
      obtain ⟨t, _, rfl⟩ := List.mem_map.mp hp
      exact hasNonnegCoeffs_one
    · intro i j a b hij hab
      simp only [List.get_eq_getElem, List.getElem_map]
      apply has2x2_thresholdEntry_one ?_ hab
      by_cases heq : i.val = j.val
      · simp [heq]
      · exact List.pairwise_iff_get.mp (pairwise_signedThresholds m r)
          ⟨i.val, by simpa using i.isLt⟩ ⟨j.val, by simpa using j.isLt⟩
          (by change i.val < j.val; lia)

/-- The unsigned collapse fits the peak degree box. -/
theorem SignedPeakInvariant.natDegree_sum {n m : ℕ} {D U : ℕ → ℝ[X]}
    (h : SignedPeakInvariant n m D U) :
    (∑ k ∈ Finset.range m, (D k + U k)).natDegree ≤ (n - 1) / 2 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k _
  apply natDegree_add_le_of_degree_le
  · have hk := h.natDegree_D k
    lia
  · exact h.natDegree_U k

/-- The unsigned D/U collapse splits, by signed interlacing and inverse gamma
transformation. The zero polynomial is treated separately. -/
theorem SignedPeakInvariant.splits_sum {n m : ℕ} {D U : ℕ → ℝ[X]}
    (h : SignedPeakInvariant n m D U) :
    (∑ k ∈ Finset.range m, (D k + U k)).Splits := by
  let P : ℝ[X] := ∑ k ∈ Finset.range m, (D k + U k)
  change P.Splits
  by_cases hp : P = 0
  · simp [hp]
  let γ : ℝ[X] := C 2 * P.comp (C 4 * X)
  have hγdeg : γ.natDegree ≤ (n - 1) / 2 := by
    dsimp [γ]
    rw [natDegree_C_mul (by norm_num : (2 : ℝ) ≠ 0), natDegree_rescale]
    exact h.natDegree_sum
  have hγne : γ ≠ 0 := by
    apply mul_ne_zero (by simp)
    intro heq
    apply hp
    exact (Polynomial.comp_C_mul_X_eq_zero_iff (by norm_num)).mp heq
  have hsum : (signedVector n m D U).sum = gammaTransform (n - 1) γ :=
    sum_signedVector m D U h.one_le h.D_eq_zero_of_eq_one h.natDegree_D
  have hsumne : (signedVector n m D U).sum ≠ 0 := by
    rw [hsum]
    exact fun hz => hγne ((gammaTransform_eq_zero_iff_of_natDegree_le hγdeg).mp hz)
  have hrr := isRealRooted_sum_of_isInterlacingSeq0Nonneg
    h.interlacing.1 h.interlacing.2 hsumne
  have hnonneg : HasNonnegCoeffs (signedVector n m D U).sum :=
    hasNonnegCoeffs_sum _ h.interlacing.1.2
  have hγrr := isRealRooted_and_hasRootsNonpos_of_isRealRooted_gammaTransform_of_natDegree_le
    hγdeg (hsum ▸ hrr.1) (hsum ▸ hrr.2)
    (hsum ▸ roots_nonpos_of_hasNonnegCoeffs hnonneg)
  have hcomp : (P.comp (C 4 * X)).Splits :=
    (Polynomial.splits_mul_iff_right (by simp) (Polynomial.Splits.C 2)).mp hγrr.1.2
  exact (Polynomial.splits_iff_comp_splits_of_natDegree_eq_one
    (by rw [natDegree_C_mul (by norm_num : (4 : ℝ) ≠ 0)]; simp)).mpr hcomp

-- The board (2,3,3): D = (0,1), U = (1+X,X).
example : signedThresholds 1 2 = [0, 1, 1, 2] := rfl

example : signedThresholds 2 2 = [1, 2, 2, 3] := rfl

example : (∑ k ∈ Finset.range 2,
    ((if k = 1 then 1 else 0) +
      (if k = 0 then 1 + X else if k = 1 then X else 0))) =
    (2 + 2 * X : ℝ[X]) := by
  norm_num [Finset.sum_range_succ]
  ring

example : signedVector 3 2 (fun k => if k = 1 then 1 else 0)
    (fun k => if k = 0 then 1 + X else if k = 1 then X else 0) =
    [2 + 6 * X, 1 + 6 * X + X ^ 2, 1 + 6 * X + X ^ 2, 6 * X + 2 * X ^ 2] := by
  norm_num [signedVector, signedDown, signedUp, List.range_succ, gammaTransform,
    gammaBasisTerm, Finset.sum_range_succ, Polynomial.add_comp, Polynomial.mul_comp,
    Polynomial.X_comp, map_ofNat, Polynomial.coeff_one]
  refine ⟨?_, ?_, ?_⟩ <;> ring

example : (signedVector 3 2 (fun k => if k = 1 then 1 else 0)
    (fun k => if k = 0 then 1 + X else if k = 1 then X else 0)).sum =
    4 + 24 * X + 4 * X ^ 2 := by
  norm_num [signedVector, signedDown, signedUp, List.range_succ, gammaTransform,
    gammaBasisTerm, Finset.sum_range_succ, Polynomial.add_comp, Polynomial.mul_comp,
    Polynomial.X_comp, map_ofNat, Polynomial.coeff_one]
  ring

end RealRooted.Applications.PeakPolynomials
