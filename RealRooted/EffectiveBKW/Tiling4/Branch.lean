module

public import RealRooted.EffectiveBKW.Tiling4.Basic
public import RealRooted.EffectiveBKW.Tiling4.Endpoint
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!+# The real characteristic branch on the entire pair ray

We select a real root between `t` and `-t`. On the negative-discriminant ray,
factoring the cubic at this root gives a positive quadratic factor. This proves
uniqueness and continuity directly from signs and the intermediate value theorem.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace RealRooted.EffectiveBKW.Tiling4

/-- For negative `t`, the characteristic cubic has a real root strictly between `t` and `-t`. -/
theorem exists_characteristic_root {t : ℝ} (ht : t < 0) :
    ∃ r ∈ Ioo t (-t), characteristic t r = 0 := by
  have hc : Continuous (characteristic t) := by unfold characteristic; fun_prop
  have hlo : characteristic t t = -2 * t ^ 2 := by unfold characteristic; ring
  have hhi : characteristic t (-t) = 2 * t ^ 2 := by unfold characteristic; ring
  have hs : (0 : ℝ) ∈ Ioo (characteristic t t) (characteristic t (-t)) := by
    rw [hlo, hhi]
    constructor <;> nlinarith [sq_pos_of_neg ht]
  exact intermediate_value_Ioo (by linarith) hc.continuousOn hs

/-- A choice of real characteristic root for every negative parameter. -/
noncomputable def realRoot (t : ℝ) : ℝ :=
  if h : t < 0 then (exists_characteristic_root h).choose else 0

/-- The chosen root stays between the elementary sign witnesses. -/
theorem realRoot_mem {t : ℝ} (ht : t < 0) : realRoot t ∈ Ioo t (-t) := by
  simpa only [realRoot, dite_eq_left ht] using (exists_characteristic_root ht).choose_spec.1

/-- The chosen value is a characteristic root at every negative parameter. -/
theorem characteristic_realRoot {t : ℝ} (ht : t < 0) : characteristic t (realRoot t) = 0 := by
  simpa only [realRoot, dite_eq_left ht] using (exists_characteristic_root ht).choose_spec.2

/-- Factoring off a real root leaves a completed-square quadratic. -/
theorem characteristic_eq_mul {t r : ℝ} (hr : characteristic t r = 0) (u : ℝ) :
    characteristic t u = (u - r) * ((u - pairReal t r) ^ 2 + pairImagSq t r) := by
  have h : characteristic t u =
      (u - r) * ((u - pairReal t r) ^ 2 + pairImagSq t r) + characteristic t r := by
    dsimp [characteristic, pairReal, pairImagSq, pairNormSq]
    ring
  simpa only [hr, add_zero] using h

/-- The cubic is negative exactly to the left of its real root when the pair is nonreal. -/
theorem characteristic_neg_iff {t r : ℝ} (hr : characteristic t r = 0)
    (hy : 0 < pairImagSq t r) (u : ℝ) : characteristic t u < 0 ↔ u < r := by
  have hp : 0 < (u - pairReal t r) ^ 2 + pairImagSq t r := by positivity
  rw [characteristic_eq_mul hr]
  constructor
  · intro h
    rcases mul_neg_iff.mp h with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · linarith
    · linarith
  · intro h
    exact mul_neg_of_neg_of_pos (sub_neg.mpr h) hp

/-- The cubic is positive exactly to the right of its real root when the pair is nonreal. -/
theorem characteristic_pos_iff {t r : ℝ} (hr : characteristic t r = 0)
    (hy : 0 < pairImagSq t r) (u : ℝ) : 0 < characteristic t u ↔ r < u := by
  have hp : 0 < (u - pairReal t r) ^ 2 + pairImagSq t r := by positivity
  rw [characteristic_eq_mul hr, mul_pos_iff_of_pos_right hp, sub_pos]

/-- The negative-discriminant condition gives uniqueness of the real root. -/
theorem characteristic_eq_zero_iff {t r : ℝ} (hr : characteristic t r = 0)
    (hy : 0 < pairImagSq t r) (u : ℝ) : characteristic t u = 0 ↔ u = r := by
  have hp : (u - pairReal t r) ^ 2 + pairImagSq t r ≠ 0 := by positivity
  rw [characteristic_eq_mul hr, mul_eq_zero, or_iff_left hp, sub_eq_zero]

/-- A selection of real characteristic roots is continuous on a nonreal-pair domain. -/
theorem continuousOn_of_characteristic {J : Set ℝ} {r : ℝ → ℝ}
    (hr : ∀ t ∈ J, characteristic t (r t) = 0)
    (hy : ∀ t ∈ J, 0 < pairImagSq t (r t)) : ContinuousOn r J := by
  intro t ht
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hs := (characteristic_neg_iff (hr t ht) (hy t ht) a).mpr ha
    have hc : Continuous (fun u ↦ characteristic u a) := by unfold characteristic; fun_prop
    have he : ∀ᶠ u in 𝓝 t, characteristic u a < 0 :=
      hc.continuousAt.eventually (eventually_lt_nhds hs)
    filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with u hu hmem
    exact (characteristic_neg_iff (hr u hmem) (hy u hmem) a).mp hu
  · intro b hb
    have hs := (characteristic_pos_iff (hr t ht) (hy t ht) b).mpr hb
    have hc : Continuous (fun u ↦ characteristic u b) := by unfold characteristic; fun_prop
    have he : ∀ᶠ u in 𝓝 t, 0 < characteristic u b :=
      hc.continuousAt.eventually (eventually_gt_nhds hs)
    filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with u hu hmem
    exact (characteristic_pos_iff (hr u hmem) (hy u hmem) b).mp hu

/-- The selected real root leaves a genuine nonreal pair on the entire ray. -/
theorem pairImagSq_realRoot_pos {t : ℝ} (ht : t < rightEdge) :
    0 < pairImagSq t (realRoot t) := by
  have ht0 : t < 0 := ht.trans rightEdge_neg
  apply pairImagSq_pos (characteristic_realRoot ht0) ht0.ne
  exact (edgeFunction_neg_iff t).mpr ht

/-- The selected root is continuous throughout the pair ray. -/
theorem continuousOn_realRoot : ContinuousOn realRoot (Iio rightEdge) := by
  apply continuousOn_of_characteristic
  · intro t ht
    exact characteristic_realRoot (ht.trans rightEdge_neg)
  · exact fun _ ht ↦ pairImagSq_realRoot_pos ht

/-- The exact pair expansion on `(-∞, t_R)`, with one real remainder mode and no cutoff. -/
noncomputable def expansion : PairExpansion polynomial (Iio rightEdge) :=
  pairExpansion (Iio rightEdge) realRoot continuousOn_realRoot
    (fun _ ht ↦ characteristic_realRoot (ht.trans rightEdge_neg))
    (fun _ ht ↦ pairImagSq_realRoot_pos ht)
    (fun _ ht ↦ (ht.trans rightEdge_neg).ne)

end RealRooted.EffectiveBKW.Tiling4
