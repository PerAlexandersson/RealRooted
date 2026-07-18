import RealRooted.Tactic.RootCount

open Polynomial

namespace RealRooted
namespace Tactic

example {f g : ℝ[X]} {μ : ℝ}
    (hμ : μ ≠ 0)
    (hdeg : f.natDegree < g.natDegree) :
    (f + C μ * g).natDegree = g.natDegree := by
  rr_natDegree_add_C_mul_lt using parameter_ne_zero := hμ, degree_lt := hdeg

example {f g : ℝ[X]} {μ : ℝ}
    (hμ : μ ≠ 0)
    (hdeg : f.natDegree < g.natDegree) :
    (f + C μ * g).leadingCoeff = μ * g.leadingCoeff := by
  rr_leadingCoeff_add_C_mul_lt using parameter_ne_zero := hμ, degree_lt := hdeg

example {f g : ℝ[X]} {A : ℝ}
    (hf_pos : 0 < f.leadingCoeff)
    (hg_pos : 0 < g.leadingCoeff)
    (hdeg : g.natDegree = f.natDegree + 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ μ : ℝ, 0 < μ → μ < δ →
      (f + C μ * g).Splits →
        ∃ r : ℝ, r ∈ (f + C μ * g).roots ∧ r < A := by
  rr_exists_root_lt_succDegree_add_right_small using
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    succ_degree := hdeg,
    bound := A

example {f g : ℝ[X]} {ρ : ℝ}
    (hf : f.Splits)
    (hdeg : f.natDegree < g.natDegree)
    (hρ : 0 < ρ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ μ : ℝ, 0 < μ → μ < δ → (f + C μ * g).Splits →
      ∀ a ∈ f.roots.toFinset,
        f.roots.count a ≤
          ((f + C μ * g).roots.filter (fun q => |q - a| < ρ)).card := by
  rr_degreeIncreasing_local_lower_count using
    left_splits := hf,
    degree_lt := hdeg,
    radius := ρ,
    radius_pos := hρ

example {f g : ℝ[X]} {μ₀ μ₁ μ ρ : ℝ}
    (hsplit : ∀ ν ∈ Set.Icc μ₀ μ₁, (f + C ν * g).Splits)
    (hdeg : ∀ ν ∈ Set.Icc μ₀ μ₁,
      (f + C ν * g).natDegree = (f + C μ₀ * g).natDegree)
    (hμ : μ ∈ Set.Icc μ₀ μ₁)
    (hρ : 0 < ρ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ ν ∈ Set.Icc μ₀ μ₁, |ν - μ| < ε →
      ∀ a ∈ (f + C μ * g).roots.toFinset,
        (f + C μ * g).roots.count a ≤
          ((f + C ν * g).roots.filter (fun q => |q - a| < ρ)).card := by
  rr_positiveParameter_local_lower_count using
    splits_on_interval := hsplit,
    degree_on_interval := hdeg,
    parameter_mem := hμ,
    radius_pos := hρ

example {f g : ℝ[X]} {μ₀ μ₁ x : ℝ}
    (hμ₁ : μ₀ ≤ μ₁)
    (hdeg : ∀ μ ∈ Set.Icc μ₀ μ₁,
      (f + C μ * g).natDegree = (f + C μ₀ * g).natDegree)
    (hrr : ∀ μ ∈ Set.Icc μ₀ μ₁, (f + C μ * g).Splits)
    (hne : ∀ μ ∈ Set.Icc μ₀ μ₁, ¬ (f + C μ * g).IsRoot x)
    (hlower : ∀ μ ∈ Set.Icc μ₀ μ₁, ∀ ρ > 0, ∃ ε > 0,
      ∀ ν ∈ Set.Icc μ₀ μ₁, |ν - μ| < ε →
        ∀ a ∈ (f + C μ * g).roots.toFinset,
          (f + C μ * g).roots.count a ≤
            ((f + C ν * g).roots.filter (fun r => |r - a| < ρ)).card) :
    ((f + C μ₀ * g).roots.filter (x < ·)).card =
      ((f + C μ₁ * g).roots.filter (x < ·)).card := by
  rr_rightFamily_card_roots_gt_eq_local_lower using
    interval_order := hμ₁,
    degree_on_interval := hdeg,
    splits_on_interval := hrr,
    threshold_not_root := hne,
    local_lower := hlower

example {f g : ℝ[X]} {x : ℝ}
    (hf_pos : 0 < f.leadingCoeff)
    (hg_pos : 0 < g.leadingCoeff)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits)
    (hx : x ∉ f.roots)
    (hlocal_lower : ∀ ρ : ℝ, 0 < ρ → ∃ δ : ℝ, 0 < δ ∧ ∀ μ : ℝ,
      0 < μ → μ < δ →
      (f + C μ * g).Splits ∧
        ∀ a ∈ f.roots.toFinset,
          f.roots.count a ≤
            ((f + C μ * g).roots.filter (fun q => |q - a| < ρ)).card)
    (hfg_split : ∀ μ : ℝ, 0 < μ → μ ≤ 1 → (f + C μ * g).Splits)
    (hfg_no : ∀ μ : ℝ, 0 < μ → μ ≤ 1 → ¬ (f + C μ * g).IsRoot x)
    (hgf_split : ∀ ν ∈ Set.Icc (0 : ℝ) 1, (g + C ν * f).Splits)
    (hgf_no : ∀ ν ∈ Set.Icc (0 : ℝ) 1, ¬ (g + C ν * f).IsRoot x) :
    (f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card := by
  rr_card_filter_gt_endpoint_eq_local_lower using
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    succ_degree := hdeg,
    left_splits := hf_split,
    threshold_not_left_root := hx,
    small_local_lower := hlocal_lower,
    right_family_splits := hfg_split,
    right_family_not_root := hfg_no,
    swapped_family_splits := hgf_split,
    swapped_family_not_root := hgf_no

example {f g : ℝ[X]} {β x : ℝ}
    (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1)
    (hprod : 0 < f.eval x * g.eval x) :
    (C (1 - β) * f + C β * g).eval x ≠ 0 := by
  rr_closedSegment_eval_ne_zero_same_sign using
    parameter_nonneg := hβ0,
    parameter_le_one := hβ1,
    eval_product_pos := hprod

example {f g : ℝ[X]} {β x : ℝ}
    (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1)
    (hprod : 0 < f.eval x * g.eval x) :
    ¬ (C (1 - β) * f + C β * g).IsRoot x := by
  rr_closedSegment_not_isRoot_same_sign using
    parameter_nonneg := hβ0,
    parameter_le_one := hβ1,
    eval_product_pos := hprod

example {f g : ℝ[X]} {μ x : ℝ}
    (hμ : 0 ≤ μ)
    (hprod : 0 < f.eval x * g.eval x) :
    (f + C μ * g).eval x ≠ 0 := by
  rr_rightFamily_eval_ne_zero_same_sign using
    parameter_nonneg := hμ,
    eval_product_pos := hprod

example (s : Multiset ℝ) (x : ℝ) :
    ∃ x' : ℝ, x < x' ∧ ∀ r ∈ s, r ≤ x ∨ x' < r := by
  rr_exists_threshold_no_mem_Ioc

example {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0) (x : ℝ) :
    ∃ x' : ℝ, x ≤ x' ∧ f.eval x' ≠ 0 ∧ g.eval x' ≠ 0 ∧
      (f.roots.filter (· ≤ x')).card = (f.roots.filter (· ≤ x)).card ∧
      (g.roots.filter (· ≤ x')).card = (g.roots.filter (· ≤ x)).card := by
  rr_exists_nonRoot_threshold_count_eq using
    left_ne_zero := hf,
    right_ne_zero := hg,
    threshold := x

example {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0) (x : ℝ) :
    ∃ x' : ℝ, x ≤ x' ∧ f.eval x' ≠ 0 ∧ g.eval x' ≠ 0 ∧
      (f.roots.filter (x' < ·)).card = (f.roots.filter (x < ·)).card ∧
      (g.roots.filter (x' < ·)).card = (g.roots.filter (x < ·)).card := by
  rr_exists_nonRoot_threshold_count_gt_eq using
    left_ne_zero := hf,
    right_ne_zero := hg,
    threshold := x

example {f g : ℝ[X]}
    (hf : f ≠ 0)
    (hg : g ≠ 0)
    (hbound : ∀ x : ℝ, f.eval x ≠ 0 → g.eval x ≠ 0 →
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1) :
    ∀ x : ℝ,
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1 := by
  rr_rootCount_diff_le_one_nonRoot using
    left_ne_zero := hf,
    right_ne_zero := hg,
    nonroot_bound := hbound

example {f g : ℝ[X]}
    (hf : f ≠ 0)
    (hg : g ≠ 0)
    (hbound : ∀ x : ℝ, f.eval x ≠ 0 → g.eval x ≠ 0 →
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1) :
    ∀ x : ℝ,
      |((f.roots.filter (· ≤ x)).card : ℤ) -
          (g.roots.filter (· ≤ x)).card| ≤ 1 := by
  rr_rootCount_abs_diff_le_one_nonRoot using
    left_ne_zero := hf,
    right_ne_zero := hg,
    nonroot_bound := hbound

example {f g : ℝ[X]}
    (hf : f ≠ 0)
    (hg : g ≠ 0)
    (hbound : ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1) :
    ∀ x : ℝ,
      ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 1 := by
  rr_rootCount_diff_le_one_nonRoot_isRoot using
    left_ne_zero := hf,
    right_ne_zero := hg,
    nonroot_bound := hbound

example {f g : ℝ[X]}
    (hf : f ≠ 0)
    (hg : g ≠ 0)
    (hbound : ∀ x : ℝ, f.eval x ≠ 0 → g.eval x ≠ 0 →
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1) :
    ∀ x : ℝ,
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1 := by
  rr_rootCountAbove_diff_le_one_nonRoot using
    left_ne_zero := hf,
    right_ne_zero := hg,
    nonroot_bound := hbound

example {f g : ℝ[X]}
    (hf : f ≠ 0)
    (hg : g ≠ 0)
    (hbound : ∀ x : ℝ, ¬ f.IsRoot x → ¬ g.IsRoot x →
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1) :
    ∀ x : ℝ,
      ((f.roots.filter (x < ·)).card : ℤ) - (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) - (f.roots.filter (x < ·)).card ≤ 1 := by
  rr_rootCountAbove_diff_le_one_nonRoot_isRoot using
    left_ne_zero := hf,
    right_ne_zero := hg,
    nonroot_bound := hbound

example {f g : ℝ[X]}
    (h : ∀ x : ℝ,
      |((f.roots.filter (· ≤ x)).card : ℤ) -
          (g.roots.filter (· ≤ x)).card| ≤ 1 ∧
      |((f.roots.filter (x < ·)).card : ℤ) -
          (g.roots.filter (x < ·)).card| ≤ 1) :
    ∀ x : ℝ,
      max
        |((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card|
        |((f.roots.filter (x < ·)).card : ℤ) -
          (g.roots.filter (x < ·)).card| ≤ 1 := by
  rr_rootCount_max_abs_diff_le_one using bundled_bound := h

example {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hsucc : g.natDegree = f.natDegree + 1) :
    f.roots.card = f.natDegree := by
  rr_left_card_roots_succDegree using
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    pos_combo := hfg,
    succ_degree := hsucc

example {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hsucc : f.natDegree = g.natDegree + 1) :
    g.roots.card = g.natDegree := by
  rr_right_card_roots_succDegree using
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    pos_combo := hfg,
    succ_degree := hsucc

example {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hsucc : g.natDegree = f.natDegree + 1) :
    f ≠ 0 ∧ f.roots.card = f.natDegree := by
  rr_left_ne_zero_card_roots_succDegree using
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    pos_combo := hfg,
    succ_degree := hsucc

example {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hsucc : f.natDegree = g.natDegree + 1) :
    g ≠ 0 ∧ g.roots.card = g.natDegree := by
  rr_right_ne_zero_card_roots_succDegree using
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    pos_combo := hfg,
    succ_degree := hsucc

end Tactic
end RealRooted
