import RealRooted.Compatibility.NDCutInvariant
import RealRooted.RowThresholdOne

/-!
# Staircase representation of structural N/D cut outputs

For the structural mixtures `P i = N i + D i` and
`Q i = X * N i + D i`, every cut output is a marker-one staircase sum of
the ordered state list `reverse N ++ D`.  The `P` outputs use the first `m`
thresholds in reverse order, while the `Q` outputs use the last `m`
thresholds in forward order; the middle threshold `m` is omitted.
-/

open Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted

/-- The selected marker-one thresholds, in the order of reversed `P` outputs
followed by forward `Q` outputs.  The threshold `m` is intentionally absent. -/
def ndCutThresholds (m : ℕ) : List ℕ :=
  (List.ofFn fun j : Fin m ↦ m - 1 - j.val).reverse ++
    List.ofFn fun j : Fin m ↦ m + j.val + 1

@[simp]
theorem length_ndCutThresholds (m : ℕ) :
    (ndCutThresholds m).length = 2 * m := by
  simp [ndCutThresholds, two_mul]

/-- The selected threshold rows, all with marker one. -/
def ndCutThresholdRows (m : ℕ) : List (ℕ × ℝ[X]) :=
  (ndCutThresholds m).map fun t ↦ (t, 1)

@[simp]
theorem length_ndCutThresholdRows (m : ℕ) :
    (ndCutThresholdRows m).length = 2 * m := by
  simp [ndCutThresholdRows]

/-- The sum of a dropped tail of `List.ofFn` is the complementary filtered
finite sum. -/
theorem sum_drop_ofFn {m : ℕ} (f : Fin m → ℝ[X]) (t : ℕ) :
    ((List.ofFn f).drop t).sum = ∑ i with t ≤ i.val, f i := by
  have hsplit := congrArg List.sum (List.take_append_drop t (List.ofFn f))
  rw [List.sum_append, List.sum_take_ofFn, List.sum_ofFn] at hsplit
  have hpartition :=
    Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i : Fin m ↦ i.val < t) f
  simp only [not_lt] at hpartition
  exact add_left_cancel (hsplit.trans hpartition.symm)

/-- A low threshold in `reverse a ++ b` cuts inside the reversed first
block. -/
theorem staircaseSum_reverse_append_low (a b : List ℝ[X]) (t : ℕ)
    (ht : t ≤ a.length) :
    staircaseSum (a.reverse ++ b) (a.length - t) =
      X * (a.drop t).sum + (a.take t).sum + b.sum := by
  have hle : a.length - t ≤ a.reverse.length := by simp
  have hsub : a.length - (a.length - t) = t := by lia
  unfold staircaseSum
  rw [List.take_append_of_le_length hle, List.drop_append_of_le_length hle,
    List.take_reverse, List.drop_reverse, hsub, List.sum_reverse,
    List.sum_append, List.sum_reverse]
  ring

/-- A high threshold in `reverse a ++ b` marks the whole reversed first
block and cuts inside the second block. -/
theorem staircaseSum_reverse_append_high (a b : List ℝ[X]) (t : ℕ) :
    staircaseSum (a.reverse ++ b) (a.length + t) =
      X * a.sum + X * (b.take t).sum + (b.drop t).sum := by
  unfold staircaseSum
  rw [List.take_append, List.drop_append]
  have hlen : a.reverse.length ≤ a.length + t := by simp
  rw [List.take_of_length_le hlen, List.drop_eq_nil_of_le hlen]
  simp only [List.length_reverse, Nat.add_sub_cancel_left, List.sum_append,
    List.sum_reverse, List.sum_nil, zero_add]
  ring

private theorem filtered_take_eq_cutPrefix {m : ℕ}
    (f : Fin m → ℝ[X]) (j : Fin m) :
    (∑ i with i.val < j.val + 1, f i) = cutPrefix f j := by
  unfold cutPrefix
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Nat.lt_succ_iff, Fin.le_iff_val_le_val]

private theorem filtered_drop_eq_cutStrictSuffix {m : ℕ}
    (f : Fin m → ℝ[X]) (j : Fin m) :
    (∑ i with j.val + 1 ≤ i.val, f i) = cutStrictSuffix f j := by
  unfold cutStrictSuffix
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Nat.succ_le_iff, Fin.lt_def]

private theorem cutPartition {m : ℕ} (f : Fin m → ℝ[X]) (j : Fin m) :
    cutPrefix f j + cutStrictSuffix f j = ∑ i, f i := by
  unfold cutPrefix cutStrictSuffix
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hij : i ≤ j
  · simp [hij, not_lt_of_ge hij]
  · simp [hij, lt_of_not_ge hij]

private theorem cutPrefix_add {m : ℕ} (f g : Fin m → ℝ[X]) (j : Fin m) :
    cutPrefix (fun i ↦ f i + g i) j = cutPrefix f j + cutPrefix g j := by
  unfold cutPrefix
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hij : i ≤ j <;> simp [hij]

private theorem cutStrictSuffix_add {m : ℕ}
    (f g : Fin m → ℝ[X]) (j : Fin m) :
    cutStrictSuffix (fun i ↦ f i + g i) j =
      cutStrictSuffix f j + cutStrictSuffix g j := by
  unfold cutStrictSuffix
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hij : j < i <;> simp [hij]

private theorem cutStrictSuffix_X_mul {m : ℕ}
    (f : Fin m → ℝ[X]) (j : Fin m) :
    cutStrictSuffix (fun i ↦ X * f i) j = X * cutStrictSuffix f j := by
  unfold cutStrictSuffix
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hij : j < i <;> simp [hij]

/-- The unmarked cut output is the staircase sum at the corresponding low
threshold in the structural state order. -/
theorem cutTransformP_ndCut_eq_staircaseSum {m : ℕ}
    (N D : Fin m → ℝ[X]) (j : Fin m) :
    cutTransformP (ndCutP N D) (ndCutQ N D) j =
      staircaseSum (ndCutStateOrder N D) (m - 1 - j.val) := by
  have ht : j.val + 1 ≤ m := Nat.succ_le_iff.mpr j.isLt
  have hthreshold : m - 1 - j.val = m - (j.val + 1) := by
    rw [Nat.sub_sub]
    rw [Nat.add_comm]
  rw [hthreshold, ndCutStateOrder]
  have hstair :=
    staircaseSum_reverse_append_low (List.ofFn N) (List.ofFn D) (j.val + 1)
      (by
        rw [List.length_ofFn]
        exact ht)
  simp only [List.length_ofFn] at hstair
  rw [hstair]
  simp only [sum_drop_ofFn, List.sum_take_ofFn, List.sum_ofFn,
    filtered_take_eq_cutPrefix, filtered_drop_eq_cutStrictSuffix]
  unfold cutTransformP ndCutP ndCutQ
  rw [cutPrefix_add, cutStrictSuffix_add, cutStrictSuffix_X_mul,
    ← cutPartition D j]
  ring

/-- The marked cut output is the staircase sum at the corresponding high
threshold in the structural state order. -/
theorem cutTransformQ_ndCut_eq_staircaseSum {m : ℕ}
    (N D : Fin m → ℝ[X]) (j : Fin m) :
    cutTransformQ (ndCutP N D) (ndCutQ N D) j =
      staircaseSum (ndCutStateOrder N D) (m + j.val + 1) := by
  rw [show m + j.val + 1 = m + (j.val + 1) from Nat.add_assoc m j.val 1,
    ndCutStateOrder]
  have hstair :=
    staircaseSum_reverse_append_high (List.ofFn N) (List.ofFn D) (j.val + 1)
  simp only [List.length_ofFn] at hstair
  rw [hstair]
  simp only [sum_drop_ofFn, List.sum_take_ofFn, List.sum_ofFn,
    filtered_take_eq_cutPrefix, filtered_drop_eq_cutStrictSuffix]
  unfold cutTransformQ ndCutP ndCutQ
  rw [cutPrefix_add, cutStrictSuffix_add, cutStrictSuffix_X_mul,
    ← cutPartition N j]
  ring

/-- Applying the selected thresholds to the structural state list gives
exactly the reversed `P` cut-output block followed by the forward `Q` block. -/
theorem map_staircaseSum_ndCutThresholds {m : ℕ}
    (N D : Fin m → ℝ[X]) :
    (ndCutThresholds m).map (staircaseSum (ndCutStateOrder N D)) =
      (List.ofFn (cutTransformP (ndCutP N D) (ndCutQ N D))).reverse ++
        List.ofFn (cutTransformQ (ndCutP N D) (ndCutQ N D)) := by
  simp only [ndCutThresholds, List.map_append, List.map_reverse,
    ← List.ofFn_comp']
  congr 2
  · apply congrArg List.ofFn
    funext j
    exact (cutTransformP_ndCut_eq_staircaseSum N D j).symm
  · funext j
    exact (cutTransformQ_ndCut_eq_staircaseSum N D j).symm

/-- Matrix-action form of `map_staircaseSum_ndCutThresholds`, ready for the
marker-one preservation theorem. -/
theorem matPolyAction_ndCutThresholdRows {m : ℕ}
    (N D : Fin m → ℝ[X]) :
    matPolyAction
        (thresholdMatrix (ndCutStateOrder N D).length (ndCutThresholdRows m))
        (ndCutStateOrder N D) =
      (List.ofFn (cutTransformP (ndCutP N D) (ndCutQ N D))).reverse ++
        List.ofFn (cutTransformQ (ndCutP N D) (ndCutQ N D)) := by
  rw [← map_staircaseSum_ndCutThresholds]
  unfold matPolyAction thresholdMatrix ndCutThresholdRows
  simp only [List.map_map]
  apply List.map_congr_left
  intro t _
  simpa only [Function.comp_apply, length_ndCutStateOrder] using
    thresholdRow_one_action_eq_staircaseSum (ndCutStateOrder N D) t

end RealRooted
