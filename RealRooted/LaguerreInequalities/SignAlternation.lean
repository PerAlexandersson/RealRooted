/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Splits
import RealRooted.Bezoutian.WronskianConverse
import Mathlib.Analysis.Polynomial.Basic

/-!
# Splitting from sign alternation at the roots of a derivative-degree companion

Let `G` be a split real polynomial with simple roots `r₀ < ⋯ < r_{n-1}` and let `F` be a real
polynomial of degree `n + 1` whose leading coefficient has the same sign as that of `G`.
If `F (rₖ) * G' (rₖ) < 0` at every root `rₖ` of `G`, then `F` takes alternating signs at the
roots of `G`, hence has a root in each gap, one below `r₀` and one above `r_{n-1}`: `F` has
`n + 1` distinct real roots and splits.  This is the Wronskian-positivity argument of
`RealRooted.Bezoutian.WronskianConverse`, where only the Wronskian at the roots of `G` is
used.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- A polynomial with values of opposite signs at `a ≤ b` has a root strictly between them. -/
private theorem exists_isRoot_Ioo_of_mul_neg {F : ℝ[X]} {a b : ℝ} (hab : a ≤ b)
    (h : F.eval a * F.eval b < 0) : ∃ x, F.IsRoot x ∧ a < x ∧ x < b := by
  rcases mul_neg_iff.mp h with h | h
  · obtain ⟨c, hc, hc0⟩ := intermediate_value_Ioo' hab F.continuous.continuousOn
      (Set.mem_Ioo.mpr ⟨h.2, h.1⟩)
    exact ⟨c, hc0, hc⟩
  · obtain ⟨c, hc, hc0⟩ := intermediate_value_Ioo hab F.continuous.continuousOn
      (Set.mem_Ioo.mpr ⟨h.1, h.2⟩)
    exact ⟨c, hc0, hc⟩

/-- The sign of `F` at the `k`-th root of `G` is `(-1) ^ (n - k)`. -/
private theorem eval_mul_neg_one_pow_pos {n : ℕ} {F G : ℝ[X]} (hG : 0 < G.leadingCoeff)
    (hdeg : G.natDegree = n) {r : Fin n → ℝ} (hr : StrictMono r) (hroots : ∀ k, G.IsRoot (r k))
    (hsign : ∀ ρ, G.IsRoot ρ → F.eval ρ * (derivative G).eval ρ < 0) (k : Fin n) :
    0 < F.eval (r k) * (-1) ^ (n - k.val) := by
  have hG_ne : G ≠ 0 := leadingCoeff_ne_zero.mp hG.ne'
  have hG_eq := Polynomial.splits_eq_C_mul_prod hG_ne hdeg r hroots hr.injective
  have hder : (derivative G).eval (r k) =
      G.leadingCoeff * ∏ j ∈ Finset.univ.erase k, (r k - r j) := by
    conv_lhs => rw [hG_eq]
    exact Polynomial.eval_derivative_C_mul_prod_X_sub_C_univ_at_root _ r k
  have hprod := prod_sub_eq_neg_one_pow_mul_prod_abs r hr k
  have hA : 0 < ∏ j ∈ Finset.univ.erase k, |r k - r j| :=
    Finset.prod_pos fun j hj => abs_pos.mpr <| sub_ne_zero.mpr <|
      hr.injective.ne (Finset.ne_of_mem_erase hj).symm
  have h := hsign _ (hroots k)
  rw [hder, hprod] at h
  have hk : n - k.val = (n - 1 - k.val) + 1 := by have := k.isLt; lia
  rw [hk, pow_succ]
  set s : ℝ := (-1) ^ (n - 1 - k.val)
  set A := ∏ j ∈ Finset.univ.erase k, |r k - r j|
  have h' : (F.eval (r k) * s) * (G.leadingCoeff * A) < 0 := by
    calc _ = F.eval (r k) * (G.leadingCoeff * (s * A)) := by ring
      _ < 0 := h
  have := neg_of_mul_neg_left h' (mul_pos hG hA).le
  linarith

private theorem splits_of_pos_leadingCoeff {F G : ℝ[X]} (hG : G.Splits)
    (hG_pos : 0 < G.leadingCoeff) (hdeg : F.natDegree = G.natDegree + 1)
    (hF_pos : 0 < F.leadingCoeff)
    (hsign : ∀ ρ, G.IsRoot ρ → F.eval ρ * (derivative G).eval ρ < 0) : F.Splits := by
  rcases Nat.eq_zero_or_pos G.natDegree with h0 | hn
  · exact Splits.of_natDegree_le_one (by lia)
  generalize hnG : G.natDegree = n at hdeg hn
  have hnodup : G.roots.Nodup :=
    Polynomial.roots_nodup_of_splits_and_simple fun r hr hd => by
      have := hsign r hr
      rw [IsRoot.def.mp hd, mul_zero] at this
      exact lt_irrefl _ this
  obtain ⟨r, hr_mono, hr_roots⟩ := Polynomial.exists_strictMono_roots hG hnG hnodup
  have hsgn := eval_mul_neg_one_pow_pos hG_pos hnG hr_mono hr_roots hsign
  have hn0 : n ≠ 0 := hn.ne'
  set k₀ : Fin n := ⟨0, hn⟩
  set k₁ : Fin n := ⟨n - 1, by lia⟩
  -- a root below the smallest root of `G`
  obtain ⟨xl, hxl_root, hxl_lt⟩ : ∃ x, F.IsRoot x ∧ x < r k₀ := by
    have h₀ : 0 < F.eval (r k₀) * (-1) ^ n := by simpa [k₀] using hsgn k₀
    obtain ⟨x, hx₁, hx₂⟩ := (Filter.Eventually.and (Filter.eventually_lt_atBot (r k₀))
      ((tendsto_eval_mul_neg_one_pow_atBot hF_pos hdeg).eventually_gt_atTop 0)).exists
    obtain ⟨c, hc, hc₁, hc₂⟩ := exists_isRoot_Ioo_of_mul_neg hx₁.le
      (by simpa [mul_comm] using mul_neg_of_pos_mul_neg_one_pow_succ h₀ hx₂)
    exact ⟨c, hc, hc₂⟩
  -- a root above the largest root of `G`
  obtain ⟨xh, hxh_root, hxh_gt⟩ : ∃ x, F.IsRoot x ∧ r k₁ < x := by
    have h₁ : F.eval (r k₁) < 0 := by
      have := hsgn k₁
      have e : n - (n - 1) = 1 := by lia
      simp only [k₁, e, pow_one] at this
      linarith
    have h_top : Filter.Tendsto (fun x ↦ F.eval x) Filter.atTop Filter.atTop := by
      apply Polynomial.tendsto_atTop_of_leadingCoeff_nonneg
      · rw [← Polynomial.natDegree_pos_iff_degree_pos, hdeg]
        exact Nat.succ_pos n
      · exact hF_pos.le
    obtain ⟨x, hx₁, hx₂⟩ := (Filter.Eventually.and (Filter.eventually_gt_atTop (r k₁))
      (h_top.eventually_gt_atTop 0)).exists
    obtain ⟨c, hc, hc₁, hc₂⟩ := exists_isRoot_Ioo_of_mul_neg hx₁.le
      (mul_neg_of_neg_of_pos h₁ hx₂)
    exact ⟨c, hc, hc₁⟩
  -- a root between consecutive roots of `G`
  have hj_lt (j : Fin (n - 1)) : j.val < n := by lia
  have hj_succ_lt (j : Fin (n - 1)) : j.val + 1 < n := by lia
  have hbetween (j : Fin (n - 1)) : ∃ x, F.IsRoot x ∧ r ⟨j.val, hj_lt j⟩ < x ∧
      x < r ⟨j.val + 1, hj_succ_lt j⟩ := by
    have h₀ := hsgn ⟨j.val, hj_lt j⟩
    have h₁ := hsgn ⟨j.val + 1, hj_succ_lt j⟩
    have e : n - j.val = (n - (j.val + 1)) + 1 := by lia
    simp only at h₀ h₁
    rw [e] at h₀
    exact exists_isRoot_Ioo_of_mul_neg (hr_mono.monotone (by simp [Fin.le_def]))
      (mul_neg_of_pos_mul_neg_one_pow_succ h₁ h₀)
  choose xb hxb_root hxb_lo hxb_hi using hbetween
  obtain ⟨u, hu_mono, -, -, hu_root⟩ :=
    exists_strictMono_u_of_bounds hn0 r xl xh hxl_lt hxh_gt xb hxb_lo hxb_hi
      (fun x ↦ F.IsRoot x) hxl_root hxh_root hxb_root
  have hF_ne : F ≠ 0 := leadingCoeff_ne_zero.mp hF_pos.ne'
  rw [splits_iff_card_roots]
  refine le_antisymm (card_roots' F) ?_
  rw [hdeg]
  calc n + 1 = (Finset.univ.image u).card := by
        rw [Finset.card_image_of_injective _ hu_mono.injective]; simp
    _ ≤ F.roots.toFinset.card := by
        refine Finset.card_le_card fun x hx => ?_
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
        exact Multiset.mem_toFinset.mpr (mem_roots'.mpr ⟨hF_ne, hu_root i⟩)
    _ ≤ F.roots.card := Multiset.toFinset_card_le _

/-- **Splitting from sign alternation.** Let `G` be a split real polynomial and `F` a real
polynomial of degree `deg G + 1` whose leading coefficient has the same sign as that of `G`.
If `F ρ * G' ρ < 0` at every root `ρ` of `G`, then `F` splits. -/
theorem splits_of_eval_mul_derivative_neg {F G : ℝ[X]} (hG : G.Splits)
    (hdeg : F.natDegree = G.natDegree + 1) (hlc : 0 < F.leadingCoeff * G.leadingCoeff)
    (hsign : ∀ ρ, G.IsRoot ρ → F.eval ρ * (derivative G).eval ρ < 0) : F.Splits := by
  have hG0 : G.leadingCoeff ≠ 0 := by
    rintro h
    rw [h, mul_zero] at hlc
    exact lt_irrefl _ hlc
  rcases lt_or_gt_of_ne hG0 with hneg | hpos
  · have hF : F.leadingCoeff < 0 := by nlinarith
    have := splits_of_pos_leadingCoeff (F := -F) (G := -G) hG.neg
      (by simpa using hneg) (by simpa using hdeg) (by simpa using hF)
      (fun ρ hρ => by simpa using hsign ρ (by simpa using hρ))
    simpa using this.neg
  · exact splits_of_pos_leadingCoeff hG hpos hdeg (by nlinarith) hsign

end RealRooted
