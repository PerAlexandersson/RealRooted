import Mathlib.Analysis.Complex.OpenMapping

/-!
# Complex polynomial consequences of the open mapping theorem

This file contains general-purpose compatibility lemmas intended for eventual
upstreaming to Mathlib.
-/

open Filter Metric Set
open scoped Topology

noncomputable section

namespace Polynomial

private theorem neg_eval_div_eval_image_mem_nhds
    (A B : Polynomial ℂ) (hA : A ≠ 0)
    (hA0 : A.eval 0 = 0) (hB0 : B.eval 0 ≠ 0)
    (U : Set ℂ) (hU : U ∈ 𝓝 0) :
    (fun t => -A.eval t / B.eval t) ''
        (U ∩ {t | B.eval t ≠ 0}) ∈ 𝓝 0 := by
  let H : ℂ → ℂ := fun t => -A.eval t / B.eval t
  have hAa : AnalyticAt ℂ (fun t => A.eval t) 0 :=
    AnalyticOnNhd.eval_polynomial A 0 (Set.mem_univ 0)
  have hBa : AnalyticAt ℂ (fun t => B.eval t) 0 :=
    AnalyticOnNhd.eval_polynomial B 0 (Set.mem_univ 0)
  have hHa : AnalyticAt ℂ H 0 := hAa.neg.div hBa hB0
  have hH0 : H 0 = 0 := by simp [H, hA0]
  have hnotconst : ¬∀ᶠ t in 𝓝 0, H t = H 0 := by
    intro hconst
    have hBne : ∀ᶠ t in 𝓝 0, B.eval t ≠ 0 :=
      B.continuousAt.eventually_ne hB0
    have hAzero : ∀ᶠ t in 𝓝 0, A.eval t = 0 := by
      filter_upwards [hconst, hBne] with t ht hBt
      rw [hH0] at ht
      simpa [H, hBt] using ht
    have hinf : Set.Infinite {t : ℂ | A.eval t = 0} :=
      infinite_of_mem_nhds 0 hAzero
    apply hA
    apply Polynomial.eq_zero_of_infinite_isRoot
    simpa only [Polynomial.IsRoot] using hinf
  have hmap : 𝓝 0 ≤ Filter.map H (𝓝 0) := by
    simpa [hH0] using
      hHa.eventually_constant_or_nhds_le_map_nhds_aux.resolve_left hnotconst
  have hBne : {t : ℂ | B.eval t ≠ 0} ∈ 𝓝 0 :=
    B.continuousAt.eventually_ne hB0
  exact hmap (image_mem_map (inter_mem hU hBne))

/-- If `A` is nonzero and vanishes at zero while `B` does not vanish there,
then every neighborhood of zero contains a point where `-A / B` lies in the
open upper half-plane. -/
theorem exists_neg_self_div_im_pos_of_mem_nhds
    (A B : Polynomial ℂ) (hA : A ≠ 0)
    (hA0 : A.eval 0 = 0) (hB0 : B.eval 0 ≠ 0)
    (U : Set ℂ) (hU : U ∈ 𝓝 0) :
    ∃ t ∈ U, A.eval t ≠ 0 ∧ B.eval t ≠ 0 ∧ 0 < (-A.eval t / B.eval t).im := by
  have himage := neg_eval_div_eval_image_mem_nhds A B hA hA0 hB0 U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp himage
  let w : ℂ := (ε / 2 : ℝ) * Complex.I
  have hwball : w ∈ ball (0 : ℂ) ε := by
    rw [mem_ball, dist_zero_right]
    simp [w, Real.norm_eq_abs, abs_of_pos hε]
    linarith
  have hwim : 0 < w.im := by
    simp [w]
    linarith
  obtain ⟨t, htS, htH⟩ := hball hwball
  change -A.eval t / B.eval t = w at htH
  have hBt : B.eval t ≠ 0 := htS.2
  have hwne : w ≠ 0 := by
    intro hw
    apply (ne_of_gt hwim)
    simpa using congrArg Complex.im hw
  have hAt : A.eval t ≠ 0 := by
    intro hAt
    have : -A.eval t / B.eval t = 0 := by simp [hAt]
    rw [this] at htH
    exact hwne htH.symm
  refine ⟨t, htS.1, hAt, hBt, ?_⟩
  rw [htH]
  exact hwim

/-- If `A` is nonzero and vanishes at zero while `B` does not vanish there,
then every neighborhood of zero contains a point where `-B / A` lies in the
open upper half-plane. -/
theorem exists_neg_div_im_pos_of_mem_nhds
    (A B : Polynomial ℂ) (hA : A ≠ 0)
    (hA0 : A.eval 0 = 0) (hB0 : B.eval 0 ≠ 0)
    (U : Set ℂ) (hU : U ∈ 𝓝 0) :
    ∃ t ∈ U, A.eval t ≠ 0 ∧ B.eval t ≠ 0 ∧ 0 < (-B.eval t / A.eval t).im := by
  have himage := neg_eval_div_eval_image_mem_nhds A B hA hA0 hB0 U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp himage
  let w : ℂ := -(ε / 2 : ℝ) * Complex.I
  have hwball : w ∈ ball (0 : ℂ) ε := by
    rw [mem_ball, dist_zero_right]
    simp [w, Real.norm_eq_abs, abs_of_pos hε]
    linarith
  have hwim : w.im < 0 := by
    simp [w]
    linarith
  obtain ⟨t, htS, htH⟩ := hball hwball
  change -A.eval t / B.eval t = w at htH
  have hBt : B.eval t ≠ 0 := htS.2
  have hwne : w ≠ 0 := by
    intro hw
    apply (ne_of_lt hwim)
    simpa using congrArg Complex.im hw
  have hAt : A.eval t ≠ 0 := by
    intro hAt
    have : -A.eval t / B.eval t = 0 := by simp [hAt]
    rw [this] at htH
    exact hwne htH.symm
  refine ⟨t, htS.1, hAt, hBt, ?_⟩
  have hroot : -B.eval t / A.eval t = w⁻¹ := by
    rw [← htH]
    field_simp
  rw [hroot, Complex.inv_im]
  exact div_pos (neg_pos.mpr hwim) (Complex.normSq_pos.mpr hwne)

end Polynomial
