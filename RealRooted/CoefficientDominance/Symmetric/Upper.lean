import RealRooted.CoefficientDominance.Symmetric.Finite
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Analytic elementary-symmetric sandwich bounds

Positive finite families admit exponential upper bounds for their elementary
symmetric values. Combined with the leading-product lower bound, these control
consecutive logarithmic ratios.
-/

namespace RealRooted.CoefficientDominance.Symmetric

open Finset

/-- An upper bound for the middle elementary symmetric value gives a lower bound
for the corresponding consecutive logarithmic ratio. -/
theorem log_ratio_ge {x : ℕ → ℝ} (hpos : ∀ i, 0 < x i) {n j : ℕ} (hj : j + 2 ≤ n)
    {T : ℝ} (hup : esym x n (j + 1) ≤ topProd x (j + 1) * Real.exp T) :
    Real.log (esym x n (j + 1) ^ 2 / (esym x n j * esym x n (j + 2))) - 2 * T
      ≤ Real.log (x j / x (j + 1)) := by
  have hA : 0 < esym x n (j + 1) := esym_pos hpos (by lia)
  have hB : 0 < esym x n j := esym_pos hpos (by lia)
  have hC : 0 < esym x n (j + 2) := esym_pos hpos (by lia)
  have hPj : 0 < topProd x j := topProd_pos hpos j
  have hPj2 : 0 < topProd x (j + 2) := topProd_pos hpos (j + 2)
  have hlowB : topProd x j ≤ esym x n j :=
    topProd_le_esym (fun i => (hpos i).le) (by lia)
  have hlowC : topProd x (j + 2) ≤ esym x n (j + 2) :=
    topProd_le_esym (fun i => (hpos i).le) (by lia)
  have hkey : esym x n (j + 1) ^ 2 / (esym x n j * esym x n (j + 2))
      ≤ (x j / x (j + 1)) * Real.exp (2 * T) := by
    have hsq : esym x n (j + 1) ^ 2
        ≤ (topProd x (j + 1)) ^ 2 * Real.exp (2 * T) := by
      have hsq' : esym x n (j + 1) ^ 2
          ≤ (topProd x (j + 1) * Real.exp T) ^ 2 := by
        have hnn : (0 : ℝ) ≤ esym x n (j + 1) := hA.le
        nlinarith [hup, hnn]
      calc
        esym x n (j + 1) ^ 2 ≤ (topProd x (j + 1) * Real.exp T) ^ 2 := hsq'
        _ = (topProd x (j + 1)) ^ 2 * Real.exp (2 * T) := by
          rw [mul_pow, ← Real.exp_nat_mul]
          ring_nf
    have hden : topProd x j * topProd x (j + 2) ≤ esym x n j * esym x n (j + 2) :=
      mul_le_mul hlowB hlowC hPj2.le hB.le
    have hdpos : 0 < topProd x j * topProd x (j + 2) := mul_pos hPj hPj2
    calc
      esym x n (j + 1) ^ 2 / (esym x n j * esym x n (j + 2))
          ≤ ((topProd x (j + 1)) ^ 2 * Real.exp (2 * T))
              / (topProd x j * topProd x (j + 2)) := by
            apply div_le_div₀ (by positivity) hsq hdpos hden
      _ = (x j / x (j + 1)) * Real.exp (2 * T) := by
        rw [topProd_sq hpos j]
        field_simp
  have hxr : 0 < x j / x (j + 1) := div_pos (hpos j) (hpos (j + 1))
  have hlog := Real.log_le_log (div_pos (sq_pos_of_pos hA) (mul_pos hB hC)) hkey
  rw [Real.log_mul (ne_of_gt hxr) (Real.exp_ne_zero _), Real.log_exp] at hlog
  linarith

/-- Evaluating the generating product bounds one elementary symmetric term. -/
theorem esym_mul_pow_le (x : ℕ → ℝ) (hnn : ∀ i, 0 ≤ x i) {n j : ℕ} {t : ℝ}
    (ht : 0 ≤ t) :
    esym x n j * t ^ j ≤ ∏ i ∈ range n, (1 + x i * t) := by
  have hexp : ∏ i ∈ range n, (x i * t + 1)
      = ∑ U ∈ (range n).powerset, ∏ i ∈ U, (x i * t) := by
    rw [Finset.prod_add]
    exact Finset.sum_congr rfl (fun U _ => by simp)
  have hterm : ∀ U ∈ (range n).powersetCard j,
      (∏ i ∈ U, x i) * t ^ j = ∏ i ∈ U, (x i * t) := by
    intro U hU
    rw [mem_powersetCard] at hU
    rw [Finset.prod_mul_distrib, Finset.prod_const, hU.2]
  have hsub : (range n).powersetCard j ⊆ (range n).powerset := by
    intro U hU
    rw [mem_powersetCard] at hU
    exact Finset.mem_powerset.mpr hU.1
  have hle : ∑ U ∈ (range n).powersetCard j, ∏ i ∈ U, (x i * t)
      ≤ ∑ U ∈ (range n).powerset, ∏ i ∈ U, (x i * t) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun U _ _ => ?_)
    exact Finset.prod_nonneg (fun i _ => mul_nonneg (hnn i) ht)
  calc
    esym x n j * t ^ j
        = ∑ U ∈ (range n).powersetCard j, (∏ i ∈ U, x i) * t ^ j := by
          rw [esym_eq_sum, Finset.sum_mul]
    _ = ∑ U ∈ (range n).powersetCard j, ∏ i ∈ U, (x i * t) :=
      Finset.sum_congr rfl hterm
    _ ≤ ∑ U ∈ (range n).powerset, ∏ i ∈ U, (x i * t) := hle
    _ = ∏ i ∈ range n, (x i * t + 1) := hexp.symm
    _ = ∏ i ∈ range n, (1 + x i * t) :=
      Finset.prod_congr rfl (fun i _ => by ring)

/-- The upper half of the elementary-symmetric sandwich, split into head and
tail factors. -/
theorem esym_le_topProd_mul (x : ℕ → ℝ) (hpos : ∀ i, 0 < x i) {n j : ℕ}
    (hjn : j ≤ n) :
    esym x n j ≤ topProd x j * (∏ i ∈ range j, (1 + x (j - 1) / x i))
      * ∏ l ∈ Ico j n, (1 + x l / x (j - 1)) := by
  set c : ℝ := x (j - 1) with hc
  have hcpos : 0 < c := hpos _
  have hkey := esym_mul_pow_le x (fun i => (hpos i).le) (n := n) (j := j)
    (t := 1 / c) (by positivity)
  rw [show ∏ i ∈ range n, (1 + x i * (1 / c)) =
      (∏ i ∈ range j, (1 + x i * (1 / c))) * ∏ l ∈ Ico j n, (1 + x l * (1 / c)) by
        rw [← Finset.prod_union]
        · congr 1
          rw [Finset.range_eq_Ico, Finset.range_eq_Ico, ← Finset.Ico_union_Ico_eq_Ico
            (Nat.zero_le j) hjn]
        · rw [Finset.range_eq_Ico]
          exact Finset.Ico_disjoint_Ico_consecutive 0 j n] at hkey
  have hhead : (∏ i ∈ range j, (1 + x i * (1 / c))) * c ^ j
      = topProd x j * ∏ i ∈ range j, (1 + c / x i) := by
    rw [show (c : ℝ) ^ j = ∏ _i ∈ range j, c by
      rw [Finset.prod_const, card_range]]
    rw [← Finset.prod_mul_distrib, topProd, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    have hxi : x i ≠ 0 := ne_of_gt (hpos i)
    field_simp
    ring
  have hcj : (0 : ℝ) < c ^ j := by positivity
  rw [div_pow, one_pow, mul_one_div, div_le_iff₀ hcj] at hkey
  calc
    esym x n j
        ≤ ((∏ i ∈ range j, (1 + x i * (1 / c)))
            * ∏ l ∈ Ico j n, (1 + x l * (1 / c))) * c ^ j := hkey
    _ = ((∏ i ∈ range j, (1 + x i * (1 / c))) * c ^ j)
          * ∏ l ∈ Ico j n, (1 + x l * (1 / c)) := by ring
    _ = (topProd x j * ∏ i ∈ range j, (1 + c / x i))
          * ∏ l ∈ Ico j n, (1 + x l / c) := by
        rw [hhead]
        congr 1
        exact Finset.prod_congr rfl (fun l _ => by rw [mul_one_div])
    _ = topProd x j * (∏ i ∈ range j, (1 + c / x i))
          * ∏ l ∈ Ico j n, (1 + x l / c) := by ring

/-- A product of positive additive factors is bounded by the exponential of
their additive corrections. -/
theorem prod_one_add_le_exp {s : Finset ℕ} (u : ℕ → ℝ) (hu : ∀ i ∈ s, 0 ≤ u i) :
    ∏ i ∈ s, (1 + u i) ≤ Real.exp (∑ i ∈ s, u i) := by
  rw [Real.exp_sum]
  refine Finset.prod_le_prod (fun i hi => by linarith [hu i hi]) (fun i _ => ?_)
  rw [add_comm]
  exact Real.add_one_le_exp _

/-- The correction sum above a distinguished index. -/
noncomputable def headSum (x : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ range j, x (j - 1) / x i

/-- The correction sum below a distinguished index. -/
noncomputable def tailSum (x : ℕ → ℝ) (n j : ℕ) : ℝ :=
  ∑ l ∈ Ico j n, x l / x (j - 1)

/-- The exponential form of the elementary-symmetric sandwich. -/
theorem esym_le_exp (x : ℕ → ℝ) (hpos : ∀ i, 0 < x i) {n j : ℕ} (hjn : j ≤ n) :
    esym x n j ≤ topProd x j * Real.exp (headSum x j + tailSum x n j) := by
  have hP : 0 < topProd x j := topProd_pos hpos j
  have h1 : ∏ i ∈ range j, (1 + x (j - 1) / x i) ≤ Real.exp (headSum x j) :=
    prod_one_add_le_exp _ (fun i _ => le_of_lt (div_pos (hpos _) (hpos i)))
  have h2 : ∏ l ∈ Ico j n, (1 + x l / x (j - 1)) ≤ Real.exp (tailSum x n j) :=
    prod_one_add_le_exp _ (fun l _ => le_of_lt (div_pos (hpos l) (hpos _)))
  have hp1 : (0 : ℝ) ≤ ∏ i ∈ range j, (1 + x (j - 1) / x i) :=
    Finset.prod_nonneg (fun i _ => by
      have h := le_of_lt (div_pos (hpos (j - 1)) (hpos i))
      linarith)
  calc
    esym x n j
        ≤ topProd x j * (∏ i ∈ range j, (1 + x (j - 1) / x i))
            * ∏ l ∈ Ico j n, (1 + x l / x (j - 1)) := esym_le_topProd_mul x hpos hjn
    _ ≤ topProd x j * Real.exp (headSum x j) * Real.exp (tailSum x n j) := by
        have hstep : topProd x j * (∏ i ∈ range j, (1 + x (j - 1) / x i))
            ≤ topProd x j * Real.exp (headSum x j) :=
          mul_le_mul_of_nonneg_left h1 hP.le
        refine mul_le_mul hstep h2 (Finset.prod_nonneg (fun l _ => by
          have h := le_of_lt (div_pos (hpos l) (hpos (j - 1)))
          linarith)) ?_
        exact mul_nonneg hP.le (Real.exp_pos _).le
    _ = topProd x j * Real.exp (headSum x j + tailSum x n j) := by
      rw [Real.exp_add]
      ring

/-- The unconditional logarithmic-ratio form of the sandwich. -/
theorem log_ratio_ge_of_pos {x : ℕ → ℝ} (hpos : ∀ i, 0 < x i) {n j : ℕ}
    (hj : j + 2 ≤ n) :
    Real.log (esym x n (j + 1) ^ 2 / (esym x n j * esym x n (j + 2)))
        - 2 * (headSum x (j + 1) + tailSum x n (j + 1))
      ≤ Real.log (x j / x (j + 1)) := by
  refine log_ratio_ge hpos hj ?_
  exact esym_le_exp x hpos (n := n) (j := j + 1) (by lia)

end RealRooted.CoefficientDominance.Symmetric
