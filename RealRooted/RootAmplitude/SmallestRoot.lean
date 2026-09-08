import RealRooted.Mathlib.Algebra.Order.BigOperators.Ring.Multiset
import RealRooted.RootAmplitude.Polynomial
import RealRooted.RootVieta

/-!
# Amplitude at a smallest negative root

A lower bound on the reciprocal-root square sum forces the largest reciprocal
root to carry a fixed proportion of the total.  The elementary product bound
then controls the normalized derivative at a root of smallest magnitude.

The low-coefficient corollary uses the canonical `RootVieta` identities rather
than introducing another reciprocal-root polynomial.
-/

open Polynomial

namespace RealRooted.RootAmplitude

noncomputable section

/-- If the square sum is at least `c` times the square of the sum, a maximal
positive entry is at least `c` times the sum. -/
theorem mul_sum_le_max_of_sq_sum_ge {v : Multiset ℝ}
    (hpos : ∀ x ∈ v, 0 < x) {m c : ℝ}
    (hm : m ∈ v) (hmax : ∀ x ∈ v, x ≤ m)
    (hratio : c * v.sum ^ 2 ≤ (v.map (fun x => x ^ 2)).sum) :
    c * v.sum ≤ m := by
  have hsquare : (v.map (fun x => x ^ 2)).sum
      ≤ (v.map (fun x => m * x)).sum := by
    refine Multiset.sum_map_le_sum_map _ _ ?_
    intro x hx
    nlinarith [hpos x hx, hmax x hx]
  rw [Multiset.sum_map_mul_left, Multiset.map_id'] at hsquare
  have hsum : 0 < v.sum := by
    have hmpos : 0 < m := hpos m hm
    have hrest : 0 ≤ (v.erase m).sum :=
      Multiset.sum_nonneg fun x hx =>
        (hpos x (Multiset.mem_of_mem_erase hx)).le
    have hsplit : v.sum = m + (v.erase m).sum := by
      conv_lhs => rw [← Multiset.cons_erase hm]
      rw [Multiset.sum_cons]
    linarith
  nlinarith

/-- A reciprocal square-sum proportion `c > 1/2` gives the sharp elementary
lower factor `(2c - 1) / c` at a simple negative root of smallest magnitude. -/
theorem amplitude_at_smallest_root_of_sq_ratio
    {p : ℝ[X]} (hp : p.Splits) (hzero : 0 < p.eval 0)
    (hneg : ∀ r ∈ p.roots, r < 0) {c : ℝ}
    (hc : 1 / 2 < c)
    (hratio :
      c * (p.roots.map (fun r : ℝ => -r⁻¹)).sum ^ 2
        ≤ ((p.roots.map (fun r : ℝ => -r⁻¹)).map (fun x => x ^ 2)).sum)
    {s : ℝ} (hs : s ∈ p.roots) (hcount : p.roots.count s = 1)
    (hmin : ∀ r ∈ p.roots, -s ≤ -r) :
    p.eval 0 * ((2 * c - 1) / c) ≤ |s * p.derivative.eval s| := by
  classical
  have hcpos : 0 < c := lt_trans (by norm_num) hc
  have hzero' : p.eval 0 ≠ 0 := hzero.ne'
  have hsneg : s < 0 := hneg s hs
  have hsne : s ≠ 0 := hsneg.ne
  set V : Multiset ℝ := p.roots.map (fun r => -r⁻¹) with hV
  set m : ℝ := -s⁻¹ with hm
  have hmpos : 0 < m := by
    rw [hm, neg_pos, inv_eq_one_div]
    exact div_neg_of_pos_of_neg one_pos hsneg
  have hVpos : ∀ x ∈ V, 0 < x := by
    intro x hx
    rw [hV, Multiset.mem_map] at hx
    obtain ⟨r, hr, rfl⟩ := hx
    rw [neg_pos, inv_eq_one_div]
    exact div_neg_of_pos_of_neg one_pos (hneg r hr)
  have hmV : m ∈ V := by
    rw [hV, Multiset.mem_map]
    exact ⟨s, hs, rfl⟩
  have hVmax : ∀ x ∈ V, x ≤ m := by
    intro x hx
    rw [hV, Multiset.mem_map] at hx
    obtain ⟨r, hr, rfl⟩ := hx
    have hrneg : r < 0 := hneg r hr
    have hrs : r ≤ s := by linarith [hmin r hr]
    have hrspos : (0 : ℝ) < r * s := mul_pos_of_neg_of_neg hrneg hsneg
    have hrne : r ≠ 0 := hrneg.ne
    have hidentity : (r⁻¹ - s⁻¹) * (r * s) = s - r := by
      field_simp [hrne, hsne]
    rw [hm, neg_le_neg_iff]
    nlinarith
  have hmax : c * V.sum ≤ m := by
    apply mul_sum_le_max_of_sq_sum_ge hVpos hmV hVmax
    simpa [hV] using hratio
  have hms : (-s) * m = 1 := by
    rw [hm]
    field_simp
  have herase :
      V.sum = m + ((p.roots.erase s).map (fun r : ℝ => -r⁻¹)).sum := by
    rw [hV]
    conv_lhs => rw [← Multiset.cons_erase hs]
    rw [Multiset.map_cons, Multiset.sum_cons]
  have hesum : ((p.roots.erase s).map (fun r : ℝ => -r⁻¹)).sum = V.sum - m := by
    rw [herase]
    ring
  set W : Multiset ℝ := (p.roots.erase s).map (fun r => s / r) with hW
  have hWsum : W.sum = (-s) * (V.sum - m) := by
    rw [hW, show ((p.roots.erase s).map (fun r : ℝ => s / r))
        = ((p.roots.erase s).map (fun r : ℝ => (-s) * (-r⁻¹))) from
      Multiset.map_congr rfl (by
        intro r hr
        have hrneg : r < 0 := hneg r (Multiset.mem_of_mem_erase hr)
        field_simp [hrneg.ne]),
      Multiset.sum_map_mul_left, hesum]
  have hscaled : (-s) * V.sum ≤ 1 / c := by
    rw [le_div_iff₀ hcpos]
    have hmul := mul_le_mul_of_nonneg_left hmax (neg_pos.mpr hsneg).le
    nlinarith [hmul, hms]
  have hWbound : W.sum ≤ (1 - c) / c := by
    rw [hWsum]
    have hrewrite : (1 - c) / c = 1 / c - 1 := by field_simp
    rw [hrewrite]
    nlinarith [hscaled, hms]
  have hWnonnegative : ∀ x ∈ W, 0 ≤ x := by
    intro x hx
    rw [hW, Multiset.mem_map] at hx
    obtain ⟨r, hr, rfl⟩ := hx
    exact (div_pos_of_neg_of_neg hsneg
      (hneg r (Multiset.mem_of_mem_erase hr))).le
  have hWleOne : ∀ x ∈ W, x ≤ 1 := by
    intro x hx
    rw [hW, Multiset.mem_map] at hx
    obtain ⟨r, hr, rfl⟩ := hx
    have hrmem := Multiset.mem_of_mem_erase hr
    have hrneg := hneg r hrmem
    rw [div_le_one_of_neg hrneg]
    linarith [hmin r hrmem]
  have hproduct := Multiset.one_sub_sum_le_prod_one_sub W hWnonnegative hWleOne
  have hlower : (2 * c - 1) / c
      ≤ (W.map (fun x => 1 - x)).prod := by
    have hidentity : (2 * c - 1) / c = 1 - (1 - c) / c := by
      field_simp
      ring
    rw [hidentity]
    linarith
  have hlowerPos : 0 < (2 * c - 1) / c := by
    exact div_pos (by linarith) hcpos
  have hproductNonnegative : 0 ≤ (W.map (fun x => 1 - x)).prod :=
    le_trans hlowerPos.le hlower
  have hproductRewrite :
      ((p.roots.erase s).map (fun r : ℝ => 1 - s / r)).prod
        = (W.map (fun x => 1 - x)).prod := by
    simp only [hW, Multiset.map_map, Function.comp_apply]
  have hamp := eval_deriv_root_div_eval_zero hp hs hcount hzero'
  rw [hproductRewrite] at hamp
  have habs : |s * p.derivative.eval s / p.eval 0|
      = (W.map (fun x => 1 - x)).prod := by
    rw [hamp, abs_neg, abs_of_nonneg hproductNonnegative]
  have hdiv : |s * p.derivative.eval s / p.eval 0|
      = |s * p.derivative.eval s| / p.eval 0 := by
    rw [abs_div, abs_of_pos hzero]
  rw [hdiv] at habs
  rw [← habs] at hlower
  rw [le_div_iff₀ hzero] at hlower
  simpa [mul_comm] using hlower

/-- The Newton-type inequality on the three lowest coefficients yields the
one-fifth amplitude bound at a simple negative root of smallest magnitude. -/
theorem amplitude_at_smallest_root {p : ℝ[X]}
    (hp : p.Splits) (hzero : 0 < p.eval 0)
    (hneg : ∀ r ∈ p.roots, r < 0)
    (hNewton : (9 / 2) * p.coeff 0 * p.coeff 2 ≤ p.coeff 1 ^ 2)
    {s : ℝ} (hs : s ∈ p.roots) (hcount : p.roots.count s = 1)
    (hmin : ∀ r ∈ p.roots, -s ≤ -r) :
    p.eval 0 / 5 ≤ |s * p.derivative.eval s| := by
  classical
  have hzero' : p.eval 0 ≠ 0 := hzero.ne'
  have hpne : p ≠ 0 := by
    intro hpzero
    subst p
    simp at hzero
  have hlc : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hpne
  have hroots : p.roots.card = p.natDegree := hp.natDegree_eq_card_roots.symm
  have hrootNe : ∀ r ∈ p.roots, r ≠ 0 := fun r hr =>
    (hneg r hr).ne
  set V : Multiset ℝ := p.roots.map (fun r => -r⁻¹) with hV
  have hsum := RootVieta.poly_sum p hroots hlc hrootNe
  have hsum' : p.coeff 1 / p.coeff 0 = V.sum := by
    simpa [hV, one_div] using hsum
  have hsquare := RootVieta.poly_sum_sq p hroots hlc hrootNe
  have hsquare' : V.sum ^ 2 - (V.map (fun x => x ^ 2)).sum
      = 2 * (p.coeff 2 / p.coeff 0) := by
    simpa [hV, one_div, Multiset.map_map, Function.comp_def] using hsquare
  have hcoeffZero : p.coeff 0 = p.eval 0 := Polynomial.coeff_zero_eq_eval_zero p
  have hcoeffOne : p.coeff 1 = p.eval 0 * V.sum := by
    rw [hcoeffZero] at hsum'
    apply (div_eq_iff hzero').mp hsum' |>.trans
    ring
  have hcoeffTwo : 2 * p.coeff 2
      = p.eval 0 * (V.sum ^ 2 - (V.map (fun x => x ^ 2)).sum) := by
    rw [hcoeffZero] at hsquare'
    field_simp [hzero'] at hsquare'
    nlinarith
  have hratio : (5 / 9) * V.sum ^ 2
      ≤ (V.map (fun x => x ^ 2)).sum := by
    rw [hcoeffZero, hcoeffOne] at hNewton
    nlinarith [hNewton, hcoeffTwo, mul_pos hzero hzero]
  have hmain := amplitude_at_smallest_root_of_sq_ratio hp hzero hneg
    (c := 5 / 9) (by norm_num) (by simpa [hV] using hratio) hs hcount hmin
  norm_num at hmain
  simpa [div_eq_mul_inv] using hmain

end

end RealRooted.RootAmplitude
