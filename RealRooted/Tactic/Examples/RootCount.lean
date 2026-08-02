import RealRooted.Tactic.RootCount

open Polynomial

namespace RealRooted
namespace Tactic

example {f g : ℝ[X]} {μ : ℝ}
    (hμ : μ ≠ 0)
    (hdeg : f.natDegree < g.natDegree) :
    (f + C μ * g).natDegree = g.natDegree := by
  rr_natDegree_add_C_mul_lt using parameter_ne_zero := hμ, degree_lt := hdeg

example {F G : Nat → ℝ[X]} {μ : Nat → ℝ}
    (hμ : ∀ i : Nat, μ i ≠ 0)
    (hdeg : ∀ i : Nat, (F i).natDegree < (G i).natDegree) :
    ∀ i : Nat, (F i + C (μ i) * G i).natDegree = (G i).natDegree := by
  rr_natDegree_add_C_mul_lt_sequence using
    parameter_ne_zero := hμ,
    degree_lt := hdeg

example {f g : ℝ[X]} {μ : ℝ}
    (hμ : μ ≠ 0)
    (hdeg : f.natDegree < g.natDegree) :
    (f + C μ * g).leadingCoeff = μ * g.leadingCoeff := by
  rr_leadingCoeff_add_C_mul_lt using parameter_ne_zero := hμ, degree_lt := hdeg

example {F G : Nat → ℝ[X]} {μ : Nat → ℝ}
    (hμ : ∀ i : Nat, μ i ≠ 0)
    (hdeg : ∀ i : Nat, (F i).natDegree < (G i).natDegree) :
    ∀ i : Nat,
      (F i + C (μ i) * G i).leadingCoeff = μ i * (G i).leadingCoeff := by
  rr_leadingCoeff_add_C_mul_lt_sequence using
    parameter_ne_zero := hμ,
    degree_lt := hdeg

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

example {F G : Nat → ℝ[X]} {A : Nat → ℝ}
    (hF_pos : ∀ i : Nat, 0 < (F i).leadingCoeff)
    (hG_pos : ∀ i : Nat, 0 < (G i).leadingCoeff)
    (hdeg : ∀ i : Nat, (G i).natDegree = (F i).natDegree + 1) :
    ∀ i : Nat, ∃ δ : ℝ, 0 < δ ∧ ∀ μ : ℝ, 0 < μ → μ < δ →
      (F i + C μ * G i).Splits →
        ∃ r : ℝ, r ∈ (F i + C μ * G i).roots ∧ r < A i := by
  rr_exists_root_lt_succDegree_add_right_small_sequence using
    left_pos_lc := hF_pos,
    right_pos_lc := hG_pos,
    succ_degree := hdeg,
    bound := A

example {F G : Nat → ℝ[X]} {ρ : Nat → ℝ}
    (hF : ∀ i : Nat, (F i).Splits)
    (hdeg : ∀ i : Nat, (F i).natDegree < (G i).natDegree)
    (hρ : ∀ i : Nat, 0 < ρ i) :
    ∀ i : Nat,
      ∃ δ : ℝ, 0 < δ ∧ ∀ μ : ℝ, 0 < μ → μ < δ →
        (F i + C μ * G i).Splits →
          ∀ a ∈ (F i).roots.toFinset,
            (F i).roots.count a ≤
              ((F i + C μ * G i).roots.filter
                (fun q => |q - a| < ρ i)).card := by
  rr_degreeIncreasing_local_lower_count_sequence using
    left_splits := hF,
    degree_lt := hdeg,
    radius := ρ,
    radius_pos := hρ

example {F G : Nat → ℝ[X]} {μ₀ μ₁ μ ρ : Nat → ℝ}
    (hsplit : ∀ i : Nat, ∀ ν ∈ Set.Icc (μ₀ i) (μ₁ i),
      (F i + C ν * G i).Splits)
    (hdeg : ∀ i : Nat, ∀ ν ∈ Set.Icc (μ₀ i) (μ₁ i),
      (F i + C ν * G i).natDegree =
        (F i + C (μ₀ i) * G i).natDegree)
    (hμ : ∀ i : Nat, μ i ∈ Set.Icc (μ₀ i) (μ₁ i))
    (hρ : ∀ i : Nat, 0 < ρ i) :
    ∀ i : Nat,
      ∃ ε : ℝ, 0 < ε ∧
        ∀ ν ∈ Set.Icc (μ₀ i) (μ₁ i), |ν - μ i| < ε →
          ∀ a ∈ (F i + C (μ i) * G i).roots.toFinset,
            (F i + C (μ i) * G i).roots.count a ≤
              ((F i + C ν * G i).roots.filter
                (fun q => |q - a| < ρ i)).card := by
  rr_positiveParameter_local_lower_count_sequence using
    splits_on_interval := hsplit,
    degree_on_interval := hdeg,
    parameter_mem := hμ,
    radius_pos := hρ

example {F G : Nat → ℝ[X]} {μ₀ μ₁ x : Nat → ℝ}
    (hμ₁ : ∀ i : Nat, μ₀ i ≤ μ₁ i)
    (hdeg : ∀ i : Nat, ∀ μ ∈ Set.Icc (μ₀ i) (μ₁ i),
      (F i + C μ * G i).natDegree =
        (F i + C (μ₀ i) * G i).natDegree)
    (hrr : ∀ i : Nat, ∀ μ ∈ Set.Icc (μ₀ i) (μ₁ i),
      (F i + C μ * G i).Splits)
    (hne : ∀ i : Nat, ∀ μ ∈ Set.Icc (μ₀ i) (μ₁ i),
      ¬ (F i + C μ * G i).IsRoot (x i))
    (hlower : ∀ i : Nat, ∀ μ ∈ Set.Icc (μ₀ i) (μ₁ i),
      ∀ ρ > 0, ∃ ε > 0,
        ∀ ν ∈ Set.Icc (μ₀ i) (μ₁ i), |ν - μ| < ε →
          ∀ a ∈ (F i + C μ * G i).roots.toFinset,
            (F i + C μ * G i).roots.count a ≤
              ((F i + C ν * G i).roots.filter
                (fun r => |r - a| < ρ)).card) :
    ∀ i : Nat,
      ((F i + C (μ₀ i) * G i).roots.filter (x i < ·)).card =
        ((F i + C (μ₁ i) * G i).roots.filter (x i < ·)).card := by
  rr_rightFamily_card_roots_gt_eq_local_lower_sequence using
    interval_order := hμ₁,
    degree_on_interval := hdeg,
    splits_on_interval := hrr,
    threshold_not_root := hne,
    local_lower := hlower

example {F G : Nat → ℝ[X]} {x : Nat → ℝ}
    (hF_pos : ∀ i : Nat, 0 < (F i).leadingCoeff)
    (hG_pos : ∀ i : Nat, 0 < (G i).leadingCoeff)
    (hdeg : ∀ i : Nat, (G i).natDegree = (F i).natDegree + 1)
    (hF_split : ∀ i : Nat, (F i).Splits)
    (hx : ∀ i : Nat, x i ∉ (F i).roots)
    (hlocal_lower : ∀ i : Nat, ∀ ρ : ℝ, 0 < ρ →
      ∃ δ : ℝ, 0 < δ ∧ ∀ μ : ℝ, 0 < μ → μ < δ →
        (F i + C μ * G i).Splits ∧
          ∀ a ∈ (F i).roots.toFinset,
            (F i).roots.count a ≤
              ((F i + C μ * G i).roots.filter
                (fun q => |q - a| < ρ)).card)
    (hfg_split : ∀ i : Nat, ∀ μ : ℝ, 0 < μ → μ ≤ 1 →
      (F i + C μ * G i).Splits)
    (hfg_no : ∀ i : Nat, ∀ μ : ℝ, 0 < μ → μ ≤ 1 →
      ¬ (F i + C μ * G i).IsRoot (x i))
    (hgf_split : ∀ i : Nat, ∀ ν ∈ Set.Icc (0 : ℝ) 1,
      (G i + C ν * F i).Splits)
    (hgf_no : ∀ i : Nat, ∀ ν ∈ Set.Icc (0 : ℝ) 1,
      ¬ (G i + C ν * F i).IsRoot (x i)) :
    ∀ i : Nat,
      ((F i).roots.filter (x i < ·)).card =
        ((G i).roots.filter (x i < ·)).card := by
  rr_card_filter_gt_endpoint_eq_local_lower_sequence using
    left_pos_lc := hF_pos,
    right_pos_lc := hG_pos,
    succ_degree := hdeg,
    left_splits := hF_split,
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

example {F G : Nat → ℝ[X]} {β x : Nat → ℝ}
    (hβ0 : ∀ i : Nat, 0 ≤ β i)
    (hβ1 : ∀ i : Nat, β i ≤ 1)
    (hprod : ∀ i : Nat, 0 < (F i).eval (x i) * (G i).eval (x i)) :
    ∀ i : Nat,
      (C (1 - β i) * F i + C (β i) * G i).eval (x i) ≠ 0 := by
  rr_closedSegment_eval_ne_zero_same_sign_sequence using
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

example {F G : Nat → ℝ[X]} {β x : Nat → ℝ}
    (hβ0 : ∀ i : Nat, 0 ≤ β i)
    (hβ1 : ∀ i : Nat, β i ≤ 1)
    (hprod : ∀ i : Nat, 0 < (F i).eval (x i) * (G i).eval (x i)) :
    ∀ i : Nat, ¬ (C (1 - β i) * F i + C (β i) * G i).IsRoot (x i) := by
  rr_closedSegment_not_isRoot_same_sign_sequence using
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

example {F G : Nat → ℝ[X]} {μ x : Nat → ℝ}
    (hμ : ∀ i : Nat, 0 ≤ μ i)
    (hprod : ∀ i : Nat, 0 < (F i).eval (x i) * (G i).eval (x i)) :
    ∀ i : Nat, (F i + C (μ i) * G i).eval (x i) ≠ 0 := by
  rr_rightFamily_eval_ne_zero_same_sign_sequence using
    parameter_nonneg := hμ,
    eval_product_pos := hprod

example (s : Multiset ℝ) (x : ℝ) :
    ∃ x' : ℝ, x < x' ∧ ∀ r ∈ s, r ≤ x ∨ x' < r := by
  rr_exists_threshold_no_mem_Ioc

example (S : Nat → Multiset ℝ) (x : Nat → ℝ) :
    ∀ i : Nat, ∃ x' : ℝ, x i < x' ∧ ∀ r ∈ S i, r ≤ x i ∨ x' < r := by
  rr_exists_threshold_no_mem_Ioc_sequence

example {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0) (x : ℝ) :
    ∃ x' : ℝ, x ≤ x' ∧ f.eval x' ≠ 0 ∧ g.eval x' ≠ 0 ∧
      (f.roots.filter (· ≤ x')).card = (f.roots.filter (· ≤ x)).card ∧
      (g.roots.filter (· ≤ x')).card = (g.roots.filter (· ≤ x)).card := by
  rr_exists_nonRoot_threshold_count_eq using
    left_ne_zero := hf,
    right_ne_zero := hg,
    threshold := x

example {F G : Nat → ℝ[X]} {x : Nat → ℝ}
    (hF : ∀ i : Nat, F i ≠ 0)
    (hG : ∀ i : Nat, G i ≠ 0) :
    ∀ i : Nat,
      ∃ x' : ℝ, x i ≤ x' ∧ (F i).eval x' ≠ 0 ∧ (G i).eval x' ≠ 0 ∧
        ((F i).roots.filter (· ≤ x')).card =
          ((F i).roots.filter (· ≤ x i)).card ∧
        ((G i).roots.filter (· ≤ x')).card =
          ((G i).roots.filter (· ≤ x i)).card := by
  rr_exists_nonRoot_threshold_count_eq_sequence using
    left_ne_zero := hF,
    right_ne_zero := hG

example {f g : ℝ[X]} (hf : f ≠ 0) (hg : g ≠ 0) (x : ℝ) :
    ∃ x' : ℝ, x ≤ x' ∧ f.eval x' ≠ 0 ∧ g.eval x' ≠ 0 ∧
      (f.roots.filter (x' < ·)).card = (f.roots.filter (x < ·)).card ∧
      (g.roots.filter (x' < ·)).card = (g.roots.filter (x < ·)).card := by
  rr_exists_nonRoot_threshold_count_gt_eq using
    left_ne_zero := hf,
    right_ne_zero := hg,
    threshold := x

example {F G : Nat → ℝ[X]} {x : Nat → ℝ}
    (hF : ∀ i : Nat, F i ≠ 0)
    (hG : ∀ i : Nat, G i ≠ 0) :
    ∀ i : Nat,
      ∃ x' : ℝ, x i ≤ x' ∧ (F i).eval x' ≠ 0 ∧ (G i).eval x' ≠ 0 ∧
        ((F i).roots.filter (x' < ·)).card =
          ((F i).roots.filter (x i < ·)).card ∧
        ((G i).roots.filter (x' < ·)).card =
          ((G i).roots.filter (x i < ·)).card := by
  rr_exists_nonRoot_threshold_count_gt_eq_sequence using
    left_ne_zero := hF,
    right_ne_zero := hG

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

example {F G : Nat → ℝ[X]}
    (hF : ∀ i : Nat, F i ≠ 0)
    (hG : ∀ i : Nat, G i ≠ 0)
    (hbound : ∀ i : Nat, ∀ x : ℝ, (F i).eval x ≠ 0 → (G i).eval x ≠ 0 →
      (((F i).roots.filter (· ≤ x)).card : ℤ) -
          ((G i).roots.filter (· ≤ x)).card ≤ 1 ∧
        (((G i).roots.filter (· ≤ x)).card : ℤ) -
          ((F i).roots.filter (· ≤ x)).card ≤ 1) :
    ∀ i : Nat, ∀ x : ℝ,
      (((F i).roots.filter (· ≤ x)).card : ℤ) -
          ((G i).roots.filter (· ≤ x)).card ≤ 1 ∧
        (((G i).roots.filter (· ≤ x)).card : ℤ) -
          ((F i).roots.filter (· ≤ x)).card ≤ 1 := by
  rr_rootCount_diff_le_one_nonRoot_sequence using
    left_ne_zero := hF,
    right_ne_zero := hG,
    nonroot_bound := hbound

example {F G : Nat → ℝ[X]}
    (hF : ∀ i : Nat, F i ≠ 0)
    (hG : ∀ i : Nat, G i ≠ 0)
    (hbound : ∀ i : Nat, ∀ x : ℝ, (F i).eval x ≠ 0 → (G i).eval x ≠ 0 →
      (((F i).roots.filter (· ≤ x)).card : ℤ) -
          ((G i).roots.filter (· ≤ x)).card ≤ 1 ∧
        (((G i).roots.filter (· ≤ x)).card : ℤ) -
          ((F i).roots.filter (· ≤ x)).card ≤ 1) :
    ∀ i : Nat, ∀ x : ℝ,
      |(((F i).roots.filter (· ≤ x)).card : ℤ) -
          ((G i).roots.filter (· ≤ x)).card| ≤ 1 := by
  rr_rootCount_abs_diff_le_one_nonRoot_sequence using
    left_ne_zero := hF,
    right_ne_zero := hG,
    nonroot_bound := hbound

example {F G : Nat → ℝ[X]}
    (hF : ∀ i : Nat, F i ≠ 0)
    (hG : ∀ i : Nat, G i ≠ 0)
    (hbound : ∀ i : Nat, ∀ x : ℝ, ¬ (F i).IsRoot x → ¬ (G i).IsRoot x →
      (((F i).roots.filter (· ≤ x)).card : ℤ) -
          ((G i).roots.filter (· ≤ x)).card ≤ 1 ∧
        (((G i).roots.filter (· ≤ x)).card : ℤ) -
          ((F i).roots.filter (· ≤ x)).card ≤ 1) :
    ∀ i : Nat, ∀ x : ℝ,
      (((F i).roots.filter (· ≤ x)).card : ℤ) -
          ((G i).roots.filter (· ≤ x)).card ≤ 1 ∧
        (((G i).roots.filter (· ≤ x)).card : ℤ) -
          ((F i).roots.filter (· ≤ x)).card ≤ 1 := by
  rr_rootCount_diff_le_one_nonRoot_isRoot_sequence using
    left_ne_zero := hF,
    right_ne_zero := hG,
    nonroot_bound := hbound

example {F G : Nat → ℝ[X]}
    (hF : ∀ i : Nat, F i ≠ 0)
    (hG : ∀ i : Nat, G i ≠ 0)
    (hbound : ∀ i : Nat, ∀ x : ℝ, (F i).eval x ≠ 0 → (G i).eval x ≠ 0 →
      (((F i).roots.filter (x < ·)).card : ℤ) -
          ((G i).roots.filter (x < ·)).card ≤ 1 ∧
        (((G i).roots.filter (x < ·)).card : ℤ) -
          ((F i).roots.filter (x < ·)).card ≤ 1) :
    ∀ i : Nat, ∀ x : ℝ,
      (((F i).roots.filter (x < ·)).card : ℤ) -
          ((G i).roots.filter (x < ·)).card ≤ 1 ∧
        (((G i).roots.filter (x < ·)).card : ℤ) -
          ((F i).roots.filter (x < ·)).card ≤ 1 := by
  rr_rootCountAbove_diff_le_one_nonRoot_sequence using
    left_ne_zero := hF,
    right_ne_zero := hG,
    nonroot_bound := hbound

example {F G : Nat → ℝ[X]}
    (hF : ∀ i : Nat, F i ≠ 0)
    (hG : ∀ i : Nat, G i ≠ 0)
    (hbound : ∀ i : Nat, ∀ x : ℝ, ¬ (F i).IsRoot x → ¬ (G i).IsRoot x →
      (((F i).roots.filter (x < ·)).card : ℤ) -
          ((G i).roots.filter (x < ·)).card ≤ 1 ∧
        (((G i).roots.filter (x < ·)).card : ℤ) -
          ((F i).roots.filter (x < ·)).card ≤ 1) :
    ∀ i : Nat, ∀ x : ℝ,
      (((F i).roots.filter (x < ·)).card : ℤ) -
          ((G i).roots.filter (x < ·)).card ≤ 1 ∧
        (((G i).roots.filter (x < ·)).card : ℤ) -
          ((F i).roots.filter (x < ·)).card ≤ 1 := by
  rr_rootCountAbove_diff_le_one_nonRoot_isRoot_sequence using
    left_ne_zero := hF,
    right_ne_zero := hG,
    nonroot_bound := hbound

example {F G : Nat → ℝ[X]}
    (h : ∀ i : Nat, ∀ x : ℝ,
      |(((F i).roots.filter (· ≤ x)).card : ℤ) -
          ((G i).roots.filter (· ≤ x)).card| ≤ 1 ∧
        |(((F i).roots.filter (x < ·)).card : ℤ) -
          ((G i).roots.filter (x < ·)).card| ≤ 1) :
    ∀ i : Nat, ∀ x : ℝ,
      max
        |(((F i).roots.filter (· ≤ x)).card : ℤ) -
          ((G i).roots.filter (· ≤ x)).card|
        |(((F i).roots.filter (x < ·)).card : ℤ) -
          ((G i).roots.filter (x < ·)).card| ≤ 1 := by
  rr_rootCount_max_abs_diff_le_one_sequence using bundled_bound := h

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

example {F G : Nat → ℝ[X]}
    (hF_pos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG_pos : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hFG : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hsucc : ∀ i : Nat, (G i).natDegree = (F i).natDegree + 1) :
    ∀ i : Nat, (F i).roots.card = (F i).natDegree := by
  rr_left_card_roots_succDegree_sequence using
    left_pos_lc := hF_pos,
    right_pos_lc := hG_pos,
    pos_combo := hFG,
    succ_degree := hsucc

example {F G : Nat → ℝ[X]}
    (hF_pos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG_pos : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hFG : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hsucc : ∀ i : Nat, (F i).natDegree = (G i).natDegree + 1) :
    ∀ i : Nat, (G i).roots.card = (G i).natDegree := by
  rr_right_card_roots_succDegree_sequence using
    left_pos_lc := hF_pos,
    right_pos_lc := hG_pos,
    pos_combo := hFG,
    succ_degree := hsucc

example {F G : Nat → ℝ[X]}
    (hF_pos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG_pos : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hFG : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hsucc : ∀ i : Nat, (G i).natDegree = (F i).natDegree + 1) :
    ∀ i : Nat, F i ≠ 0 ∧ (F i).roots.card = (F i).natDegree := by
  rr_left_ne_zero_card_roots_succDegree_sequence using
    left_pos_lc := hF_pos,
    right_pos_lc := hG_pos,
    pos_combo := hFG,
    succ_degree := hsucc

example {F G : Nat → ℝ[X]}
    (hF_pos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG_pos : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hFG : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hsucc : ∀ i : Nat, (F i).natDegree = (G i).natDegree + 1) :
    ∀ i : Nat, G i ≠ 0 ∧ (G i).roots.card = (G i).natDegree := by
  rr_right_ne_zero_card_roots_succDegree_sequence using
    left_pos_lc := hF_pos,
    right_pos_lc := hG_pos,
    pos_combo := hFG,
    succ_degree := hsucc

example {p : ℝ[X]} {a b : ℝ}
    (hab : a ≤ b)
    (hno : ∀ x, a < x → x ≤ b → ¬ p.IsRoot x) :
    (p.roots.filter (· ≤ a)).card = (p.roots.filter (· ≤ b)).card := by
  rr_card_roots_filter_le_eq_no_isRoot_Ioc using
    interval_order := hab,
    no_roots := hno

example {p : ℝ[X]} {a b : ℝ}
    (hab : a ≤ b)
    (hno : ∀ x, a < x → x ≤ b → ¬ p.IsRoot x) :
    (p.roots.filter (a < ·)).card = (p.roots.filter (b < ·)).card := by
  rr_card_roots_filter_gt_eq_no_isRoot_Ioc using
    interval_order := hab,
    no_roots := hno

example {p : ℝ[X]} {a b : ℝ}
    (hab : a ≤ b)
    (hno : ∀ x, a < x → x ≤ b → ¬ p.IsRoot x) :
    (p.roots.filter (fun x => a < x ∧ x ≤ b)).card = 0 := by
  rr_card_roots_filter_Ioc_zero_no_isRoot_Ioc using
    interval_order := hab,
    no_roots := hno

example {p : ℝ[X]} {a b : ℝ}
    (hab : a ≤ b)
    (hno : ∀ x, a < x → x ≤ b → ¬ p.IsRoot x) :
    (p.roots.filter (· ≤ a)).card = (p.roots.filter (· ≤ b)).card ∧
      (p.roots.filter (a < ·)).card = (p.roots.filter (b < ·)).card ∧
        (p.roots.filter (fun x => a < x ∧ x ≤ b)).card = 0 := by
  rr_card_roots_filter_all_eq_no_isRoot_Ioc using
    interval_order := hab,
    no_roots := hno

example {p : ℝ[X]} {a b : ℝ} (hab : a ≤ b) :
    (p.roots.filter (· ≤ a)).card ≤ (p.roots.filter (· ≤ b)).card := by
  rr_card_roots_filter_le_mono using interval_order := hab

example {p : ℝ[X]} {a b : ℝ} (hab : a ≤ b) :
    (p.roots.filter (b < ·)).card ≤ (p.roots.filter (a < ·)).card := by
  rr_card_roots_filter_gt_antitone using interval_order := hab

example {p : ℝ[X]} {a b : ℝ} (hab : a ≤ b) :
    (p.roots.filter (· ≤ a)).card ≤ (p.roots.filter (· ≤ b)).card ∧
      (p.roots.filter (b < ·)).card ≤ (p.roots.filter (a < ·)).card := by
  rr_card_roots_filter_le_and_gt_mono using interval_order := hab

example {p : ℝ[X]} {a b : ℝ}
    (hab : a ≤ b)
    (hno : ∀ x, a ≤ x → x ≤ b → ¬ p.IsRoot x) :
    (p.roots.filter (· ≤ a)).card = (p.roots.filter (· ≤ b)).card := by
  rr_card_roots_filter_le_eq_no_isRoot_Icc using
    interval_order := hab,
    no_roots := hno

example {p : ℝ[X]} {a b : ℝ}
    (hab : a ≤ b)
    (hno : ∀ x, a ≤ x → x ≤ b → ¬ p.IsRoot x) :
    (p.roots.filter (a < ·)).card = (p.roots.filter (b < ·)).card := by
  rr_card_roots_filter_gt_eq_no_isRoot_Icc using
    interval_order := hab,
    no_roots := hno

example {p : ℝ[X]} {a b : ℝ}
    (hab : a ≤ b)
    (hno : ∀ x, a ≤ x → x ≤ b → ¬ p.IsRoot x) :
    (p.roots.filter (fun x => a < x ∧ x ≤ b)).card = 0 := by
  rr_card_roots_filter_Ioc_zero_no_isRoot_Icc using
    interval_order := hab,
    no_roots := hno

example {p : ℝ[X]} {a b : ℝ}
    (hab : a ≤ b)
    (hno : ∀ x, a ≤ x → x ≤ b → ¬ p.IsRoot x) :
    (p.roots.filter (· ≤ a)).card = (p.roots.filter (· ≤ b)).card ∧
      (p.roots.filter (a < ·)).card = (p.roots.filter (b < ·)).card ∧
        (p.roots.filter (fun x => a < x ∧ x ≤ b)).card = 0 := by
  rr_card_roots_filter_all_eq_no_isRoot_Icc using
    interval_order := hab,
    no_roots := hno

example {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hab : ∀ i : Nat, a i ≤ b i)
    (hno : ∀ i : Nat, ∀ x, a i < x → x ≤ b i → ¬ (P i).IsRoot x) :
    ∀ i : Nat,
      ((P i).roots.filter (· ≤ a i)).card =
        ((P i).roots.filter (· ≤ b i)).card := by
  rr_card_roots_filter_le_eq_no_isRoot_Ioc_sequence using
    interval_order := hab,
    no_roots := hno

example {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hab : ∀ i : Nat, a i ≤ b i)
    (hno : ∀ i : Nat, ∀ x, a i < x → x ≤ b i → ¬ (P i).IsRoot x) :
    ∀ i : Nat,
      ((P i).roots.filter (a i < ·)).card =
        ((P i).roots.filter (b i < ·)).card := by
  rr_card_roots_filter_gt_eq_no_isRoot_Ioc_sequence using
    interval_order := hab,
    no_roots := hno

example {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hab : ∀ i : Nat, a i ≤ b i)
    (hno : ∀ i : Nat, ∀ x, a i < x → x ≤ b i → ¬ (P i).IsRoot x) :
    ∀ i : Nat,
      ((P i).roots.filter (fun x => a i < x ∧ x ≤ b i)).card = 0 := by
  rr_card_roots_filter_Ioc_zero_no_isRoot_Ioc_sequence using
    interval_order := hab,
    no_roots := hno

example {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hab : ∀ i : Nat, a i ≤ b i)
    (hno : ∀ i : Nat, ∀ x, a i < x → x ≤ b i → ¬ (P i).IsRoot x) :
    ∀ i : Nat,
      ((P i).roots.filter (· ≤ a i)).card =
          ((P i).roots.filter (· ≤ b i)).card ∧
        ((P i).roots.filter (a i < ·)).card =
          ((P i).roots.filter (b i < ·)).card ∧
          ((P i).roots.filter (fun x => a i < x ∧ x ≤ b i)).card = 0 := by
  rr_card_roots_filter_all_eq_no_isRoot_Ioc_sequence using
    interval_order := hab,
    no_roots := hno

example {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hab : ∀ i : Nat, a i ≤ b i) :
    ∀ i : Nat,
      ((P i).roots.filter (· ≤ a i)).card ≤
        ((P i).roots.filter (· ≤ b i)).card := by
  rr_card_roots_filter_le_mono_sequence using interval_order := hab

example {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hab : ∀ i : Nat, a i ≤ b i) :
    ∀ i : Nat,
      ((P i).roots.filter (b i < ·)).card ≤
        ((P i).roots.filter (a i < ·)).card := by
  rr_card_roots_filter_gt_antitone_sequence using interval_order := hab

example {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hab : ∀ i : Nat, a i ≤ b i) :
    ∀ i : Nat,
      ((P i).roots.filter (· ≤ a i)).card ≤
          ((P i).roots.filter (· ≤ b i)).card ∧
        ((P i).roots.filter (b i < ·)).card ≤
          ((P i).roots.filter (a i < ·)).card := by
  rr_card_roots_filter_le_and_gt_mono_sequence using interval_order := hab

example {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hab : ∀ i : Nat, a i ≤ b i)
    (hno : ∀ i : Nat, ∀ x, a i ≤ x → x ≤ b i → ¬ (P i).IsRoot x) :
    ∀ i : Nat,
      ((P i).roots.filter (· ≤ a i)).card =
        ((P i).roots.filter (· ≤ b i)).card := by
  rr_card_roots_filter_le_eq_no_isRoot_Icc_sequence using
    interval_order := hab,
    no_roots := hno

example {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hab : ∀ i : Nat, a i ≤ b i)
    (hno : ∀ i : Nat, ∀ x, a i ≤ x → x ≤ b i → ¬ (P i).IsRoot x) :
    ∀ i : Nat,
      ((P i).roots.filter (a i < ·)).card =
        ((P i).roots.filter (b i < ·)).card := by
  rr_card_roots_filter_gt_eq_no_isRoot_Icc_sequence using
    interval_order := hab,
    no_roots := hno

example {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hab : ∀ i : Nat, a i ≤ b i)
    (hno : ∀ i : Nat, ∀ x, a i ≤ x → x ≤ b i → ¬ (P i).IsRoot x) :
    ∀ i : Nat,
      ((P i).roots.filter (fun x => a i < x ∧ x ≤ b i)).card = 0 := by
  rr_card_roots_filter_Ioc_zero_no_isRoot_Icc_sequence using
    interval_order := hab,
    no_roots := hno

example {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hab : ∀ i : Nat, a i ≤ b i)
    (hno : ∀ i : Nat, ∀ x, a i ≤ x → x ≤ b i → ¬ (P i).IsRoot x) :
    ∀ i : Nat,
      ((P i).roots.filter (· ≤ a i)).card =
          ((P i).roots.filter (· ≤ b i)).card ∧
        ((P i).roots.filter (a i < ·)).card =
          ((P i).roots.filter (b i < ·)).card ∧
          ((P i).roots.filter (fun x => a i < x ∧ x ≤ b i)).card = 0 := by
  rr_card_roots_filter_all_eq_no_isRoot_Icc_sequence using
    interval_order := hab,
    no_roots := hno

example {f g : ℝ[X]} {a b : ℝ}
    (hab : a ≤ b)
    (hf : ∀ x, a < x → x ≤ b → ¬ f.IsRoot x)
    (hg : ∀ x, a < x → x ≤ b → ¬ g.IsRoot x) :
    ((f.roots.filter (· ≤ a)).card : ℤ) - (g.roots.filter (· ≤ a)).card
      = ((f.roots.filter (· ≤ b)).card : ℤ) -
          (g.roots.filter (· ≤ b)).card := by
  rr_card_roots_filter_le_sub_eq_no_isRoot_Ioc using
    interval_order := hab,
    left_no_roots := hf,
    right_no_roots := hg

example {f g : ℝ[X]} {a b : ℝ}
    (hab : a ≤ b)
    (hf : ∀ x, a < x → x ≤ b → ¬ f.IsRoot x)
    (hg : ∀ x, a < x → x ≤ b → ¬ g.IsRoot x) :
    ((f.roots.filter (a < ·)).card : ℤ) - (g.roots.filter (a < ·)).card
      = ((f.roots.filter (b < ·)).card : ℤ) -
          (g.roots.filter (b < ·)).card := by
  rr_card_roots_filter_gt_sub_eq_no_isRoot_Ioc using
    interval_order := hab,
    left_no_roots := hf,
    right_no_roots := hg

example {f g : ℝ[X]} {a b : ℝ}
    (hab : a ≤ b)
    (hf : ∀ x, a < x → x ≤ b → ¬ f.IsRoot x)
    (hg : ∀ x, a < x → x ≤ b → ¬ g.IsRoot x)
    (h :
      ((f.roots.filter (· ≤ a)).card : ℤ) -
          (g.roots.filter (· ≤ a)).card ≤ 1 ∧
        ((g.roots.filter (· ≤ a)).card : ℤ) -
          (f.roots.filter (· ≤ a)).card ≤ 1) :
    ((f.roots.filter (· ≤ b)).card : ℤ) -
        (g.roots.filter (· ≤ b)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ b)).card : ℤ) -
        (f.roots.filter (· ≤ b)).card ≤ 1 := by
  rr_card_roots_filter_le_bound_no_isRoot_Ioc using
    interval_order := hab,
    left_no_roots := hf,
    right_no_roots := hg,
    source_bound := h

example {f g : ℝ[X]} {a b : ℝ}
    (hab : a ≤ b)
    (hf : ∀ x, a < x → x ≤ b → ¬ f.IsRoot x)
    (hg : ∀ x, a < x → x ≤ b → ¬ g.IsRoot x)
    (h :
      ((f.roots.filter (a < ·)).card : ℤ) -
          (g.roots.filter (a < ·)).card ≤ 1 ∧
        ((g.roots.filter (a < ·)).card : ℤ) -
          (f.roots.filter (a < ·)).card ≤ 1) :
    ((f.roots.filter (b < ·)).card : ℤ) -
        (g.roots.filter (b < ·)).card ≤ 1 ∧
      ((g.roots.filter (b < ·)).card : ℤ) -
        (f.roots.filter (b < ·)).card ≤ 1 := by
  rr_card_roots_filter_gt_bound_no_isRoot_Ioc using
    interval_order := hab,
    left_no_roots := hf,
    right_no_roots := hg,
    source_bound := h

example {f g : ℝ[X]} {a b : ℝ}
    (hab : a ≤ b)
    (hf : ∀ x, a < x → x ≤ b → ¬ f.IsRoot x)
    (hg : ∀ x, a < x → x ≤ b → ¬ g.IsRoot x)
    (hle :
      ((f.roots.filter (· ≤ a)).card : ℤ) -
          (g.roots.filter (· ≤ a)).card ≤ 1 ∧
        ((g.roots.filter (· ≤ a)).card : ℤ) -
          (f.roots.filter (· ≤ a)).card ≤ 1)
    (hgt :
      ((f.roots.filter (a < ·)).card : ℤ) -
          (g.roots.filter (a < ·)).card ≤ 1 ∧
        ((g.roots.filter (a < ·)).card : ℤ) -
          (f.roots.filter (a < ·)).card ≤ 1) :
    (((f.roots.filter (· ≤ b)).card : ℤ) -
        (g.roots.filter (· ≤ b)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ b)).card : ℤ) -
        (f.roots.filter (· ≤ b)).card ≤ 1) ∧
      (((f.roots.filter (b < ·)).card : ℤ) -
          (g.roots.filter (b < ·)).card ≤ 1 ∧
        ((g.roots.filter (b < ·)).card : ℤ) -
          (f.roots.filter (b < ·)).card ≤ 1) := by
  rr_card_roots_filter_le_and_gt_bound_no_isRoot_Ioc using
    interval_order := hab,
    left_no_roots := hf,
    right_no_roots := hg,
    lower_source_bound := hle,
    upper_source_bound := hgt

example {f g : ℝ[X]} {a b : ℝ}
    (hab : a ≤ b)
    (hf : ∀ x, a ≤ x → x ≤ b → ¬ f.IsRoot x)
    (hg : ∀ x, a ≤ x → x ≤ b → ¬ g.IsRoot x) :
    ((f.roots.filter (· ≤ a)).card : ℤ) - (g.roots.filter (· ≤ a)).card
      = ((f.roots.filter (· ≤ b)).card : ℤ) -
          (g.roots.filter (· ≤ b)).card := by
  rr_card_roots_filter_le_sub_eq_no_isRoot_Icc using
    interval_order := hab,
    left_no_roots := hf,
    right_no_roots := hg

example {f g : ℝ[X]} {a b : ℝ}
    (hab : a ≤ b)
    (hf : ∀ x, a ≤ x → x ≤ b → ¬ f.IsRoot x)
    (hg : ∀ x, a ≤ x → x ≤ b → ¬ g.IsRoot x) :
    ((f.roots.filter (a < ·)).card : ℤ) - (g.roots.filter (a < ·)).card
      = ((f.roots.filter (b < ·)).card : ℤ) -
          (g.roots.filter (b < ·)).card := by
  rr_card_roots_filter_gt_sub_eq_no_isRoot_Icc using
    interval_order := hab,
    left_no_roots := hf,
    right_no_roots := hg

example {f g : ℝ[X]} {a b : ℝ}
    (hab : a ≤ b)
    (hf : ∀ x, a ≤ x → x ≤ b → ¬ f.IsRoot x)
    (hg : ∀ x, a ≤ x → x ≤ b → ¬ g.IsRoot x)
    (h :
      ((f.roots.filter (· ≤ a)).card : ℤ) -
          (g.roots.filter (· ≤ a)).card ≤ 1 ∧
        ((g.roots.filter (· ≤ a)).card : ℤ) -
          (f.roots.filter (· ≤ a)).card ≤ 1) :
    ((f.roots.filter (· ≤ b)).card : ℤ) -
        (g.roots.filter (· ≤ b)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ b)).card : ℤ) -
        (f.roots.filter (· ≤ b)).card ≤ 1 := by
  rr_card_roots_filter_le_bound_no_isRoot_Icc using
    interval_order := hab,
    left_no_roots := hf,
    right_no_roots := hg,
    source_bound := h

example {f g : ℝ[X]} {a b : ℝ}
    (hab : a ≤ b)
    (hf : ∀ x, a ≤ x → x ≤ b → ¬ f.IsRoot x)
    (hg : ∀ x, a ≤ x → x ≤ b → ¬ g.IsRoot x)
    (h :
      ((f.roots.filter (a < ·)).card : ℤ) -
          (g.roots.filter (a < ·)).card ≤ 1 ∧
        ((g.roots.filter (a < ·)).card : ℤ) -
          (f.roots.filter (a < ·)).card ≤ 1) :
    ((f.roots.filter (b < ·)).card : ℤ) -
        (g.roots.filter (b < ·)).card ≤ 1 ∧
      ((g.roots.filter (b < ·)).card : ℤ) -
        (f.roots.filter (b < ·)).card ≤ 1 := by
  rr_card_roots_filter_gt_bound_no_isRoot_Icc using
    interval_order := hab,
    left_no_roots := hf,
    right_no_roots := hg,
    source_bound := h

example {f g : ℝ[X]} {a b : ℝ}
    (hab : a ≤ b)
    (hf : ∀ x, a ≤ x → x ≤ b → ¬ f.IsRoot x)
    (hg : ∀ x, a ≤ x → x ≤ b → ¬ g.IsRoot x)
    (hle :
      ((f.roots.filter (· ≤ a)).card : ℤ) -
          (g.roots.filter (· ≤ a)).card ≤ 1 ∧
        ((g.roots.filter (· ≤ a)).card : ℤ) -
          (f.roots.filter (· ≤ a)).card ≤ 1)
    (hgt :
      ((f.roots.filter (a < ·)).card : ℤ) -
          (g.roots.filter (a < ·)).card ≤ 1 ∧
        ((g.roots.filter (a < ·)).card : ℤ) -
          (f.roots.filter (a < ·)).card ≤ 1) :
    (((f.roots.filter (· ≤ b)).card : ℤ) -
        (g.roots.filter (· ≤ b)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ b)).card : ℤ) -
        (f.roots.filter (· ≤ b)).card ≤ 1) ∧
      (((f.roots.filter (b < ·)).card : ℤ) -
          (g.roots.filter (b < ·)).card ≤ 1 ∧
        ((g.roots.filter (b < ·)).card : ℤ) -
          (f.roots.filter (b < ·)).card ≤ 1) := by
  rr_card_roots_filter_le_and_gt_bound_no_isRoot_Icc using
    interval_order := hab,
    left_no_roots := hf,
    right_no_roots := hg,
    lower_source_bound := hle,
    upper_source_bound := hgt

example {F G : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hab : ∀ i : Nat, a i ≤ b i)
    (hF : ∀ i : Nat, ∀ x, a i < x → x ≤ b i → ¬ (F i).IsRoot x)
    (hG : ∀ i : Nat, ∀ x, a i < x → x ≤ b i → ¬ (G i).IsRoot x) :
    ∀ i : Nat,
      (((F i).roots.filter (· ≤ a i)).card : ℤ) -
          ((G i).roots.filter (· ≤ a i)).card =
        (((F i).roots.filter (· ≤ b i)).card : ℤ) -
          ((G i).roots.filter (· ≤ b i)).card := by
  rr_card_roots_filter_le_sub_eq_no_isRoot_Ioc_sequence using
    interval_order := hab,
    left_no_roots := hF,
    right_no_roots := hG

example {F G : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hab : ∀ i : Nat, a i ≤ b i)
    (hF : ∀ i : Nat, ∀ x, a i < x → x ≤ b i → ¬ (F i).IsRoot x)
    (hG : ∀ i : Nat, ∀ x, a i < x → x ≤ b i → ¬ (G i).IsRoot x) :
    ∀ i : Nat,
      (((F i).roots.filter (a i < ·)).card : ℤ) -
          ((G i).roots.filter (a i < ·)).card =
        (((F i).roots.filter (b i < ·)).card : ℤ) -
          ((G i).roots.filter (b i < ·)).card := by
  rr_card_roots_filter_gt_sub_eq_no_isRoot_Ioc_sequence using
    interval_order := hab,
    left_no_roots := hF,
    right_no_roots := hG

example {F G : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hab : ∀ i : Nat, a i ≤ b i)
    (hF : ∀ i : Nat, ∀ x, a i < x → x ≤ b i → ¬ (F i).IsRoot x)
    (hG : ∀ i : Nat, ∀ x, a i < x → x ≤ b i → ¬ (G i).IsRoot x)
    (h : ∀ i : Nat,
      (((F i).roots.filter (· ≤ a i)).card : ℤ) -
          ((G i).roots.filter (· ≤ a i)).card ≤ 1 ∧
        (((G i).roots.filter (· ≤ a i)).card : ℤ) -
          ((F i).roots.filter (· ≤ a i)).card ≤ 1) :
    ∀ i : Nat,
      (((F i).roots.filter (· ≤ b i)).card : ℤ) -
          ((G i).roots.filter (· ≤ b i)).card ≤ 1 ∧
        (((G i).roots.filter (· ≤ b i)).card : ℤ) -
          ((F i).roots.filter (· ≤ b i)).card ≤ 1 := by
  rr_card_roots_filter_le_bound_no_isRoot_Ioc_sequence using
    interval_order := hab,
    left_no_roots := hF,
    right_no_roots := hG,
    source_bound := h

example {F G : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hab : ∀ i : Nat, a i ≤ b i)
    (hF : ∀ i : Nat, ∀ x, a i < x → x ≤ b i → ¬ (F i).IsRoot x)
    (hG : ∀ i : Nat, ∀ x, a i < x → x ≤ b i → ¬ (G i).IsRoot x)
    (h : ∀ i : Nat,
      (((F i).roots.filter (a i < ·)).card : ℤ) -
          ((G i).roots.filter (a i < ·)).card ≤ 1 ∧
        (((G i).roots.filter (a i < ·)).card : ℤ) -
          ((F i).roots.filter (a i < ·)).card ≤ 1) :
    ∀ i : Nat,
      (((F i).roots.filter (b i < ·)).card : ℤ) -
          ((G i).roots.filter (b i < ·)).card ≤ 1 ∧
        (((G i).roots.filter (b i < ·)).card : ℤ) -
          ((F i).roots.filter (b i < ·)).card ≤ 1 := by
  rr_card_roots_filter_gt_bound_no_isRoot_Ioc_sequence using
    interval_order := hab,
    left_no_roots := hF,
    right_no_roots := hG,
    source_bound := h

example {F G : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hab : ∀ i : Nat, a i ≤ b i)
    (hF : ∀ i : Nat, ∀ x, a i < x → x ≤ b i → ¬ (F i).IsRoot x)
    (hG : ∀ i : Nat, ∀ x, a i < x → x ≤ b i → ¬ (G i).IsRoot x)
    (hle : ∀ i : Nat,
      (((F i).roots.filter (· ≤ a i)).card : ℤ) -
          ((G i).roots.filter (· ≤ a i)).card ≤ 1 ∧
        (((G i).roots.filter (· ≤ a i)).card : ℤ) -
          ((F i).roots.filter (· ≤ a i)).card ≤ 1)
    (hgt : ∀ i : Nat,
      (((F i).roots.filter (a i < ·)).card : ℤ) -
          ((G i).roots.filter (a i < ·)).card ≤ 1 ∧
        (((G i).roots.filter (a i < ·)).card : ℤ) -
          ((F i).roots.filter (a i < ·)).card ≤ 1) :
    ∀ i : Nat,
      ((((F i).roots.filter (· ≤ b i)).card : ℤ) -
          ((G i).roots.filter (· ≤ b i)).card ≤ 1 ∧
        (((G i).roots.filter (· ≤ b i)).card : ℤ) -
          ((F i).roots.filter (· ≤ b i)).card ≤ 1) ∧
        ((((F i).roots.filter (b i < ·)).card : ℤ) -
            ((G i).roots.filter (b i < ·)).card ≤ 1 ∧
          (((G i).roots.filter (b i < ·)).card : ℤ) -
            ((F i).roots.filter (b i < ·)).card ≤ 1) := by
  rr_card_roots_filter_le_and_gt_bound_no_isRoot_Ioc_sequence using
    interval_order := hab,
    left_no_roots := hF,
    right_no_roots := hG,
    lower_source_bound := hle,
    upper_source_bound := hgt

example {F G : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hab : ∀ i : Nat, a i ≤ b i)
    (hF : ∀ i : Nat, ∀ x, a i ≤ x → x ≤ b i → ¬ (F i).IsRoot x)
    (hG : ∀ i : Nat, ∀ x, a i ≤ x → x ≤ b i → ¬ (G i).IsRoot x) :
    ∀ i : Nat,
      (((F i).roots.filter (· ≤ a i)).card : ℤ) -
          ((G i).roots.filter (· ≤ a i)).card =
        (((F i).roots.filter (· ≤ b i)).card : ℤ) -
          ((G i).roots.filter (· ≤ b i)).card := by
  rr_card_roots_filter_le_sub_eq_no_isRoot_Icc_sequence using
    interval_order := hab,
    left_no_roots := hF,
    right_no_roots := hG

example {F G : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hab : ∀ i : Nat, a i ≤ b i)
    (hF : ∀ i : Nat, ∀ x, a i ≤ x → x ≤ b i → ¬ (F i).IsRoot x)
    (hG : ∀ i : Nat, ∀ x, a i ≤ x → x ≤ b i → ¬ (G i).IsRoot x) :
    ∀ i : Nat,
      (((F i).roots.filter (a i < ·)).card : ℤ) -
          ((G i).roots.filter (a i < ·)).card =
        (((F i).roots.filter (b i < ·)).card : ℤ) -
          ((G i).roots.filter (b i < ·)).card := by
  rr_card_roots_filter_gt_sub_eq_no_isRoot_Icc_sequence using
    interval_order := hab,
    left_no_roots := hF,
    right_no_roots := hG

example {F G : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hab : ∀ i : Nat, a i ≤ b i)
    (hF : ∀ i : Nat, ∀ x, a i ≤ x → x ≤ b i → ¬ (F i).IsRoot x)
    (hG : ∀ i : Nat, ∀ x, a i ≤ x → x ≤ b i → ¬ (G i).IsRoot x)
    (h : ∀ i : Nat,
      (((F i).roots.filter (· ≤ a i)).card : ℤ) -
          ((G i).roots.filter (· ≤ a i)).card ≤ 1 ∧
        (((G i).roots.filter (· ≤ a i)).card : ℤ) -
          ((F i).roots.filter (· ≤ a i)).card ≤ 1) :
    ∀ i : Nat,
      (((F i).roots.filter (· ≤ b i)).card : ℤ) -
          ((G i).roots.filter (· ≤ b i)).card ≤ 1 ∧
        (((G i).roots.filter (· ≤ b i)).card : ℤ) -
          ((F i).roots.filter (· ≤ b i)).card ≤ 1 := by
  rr_card_roots_filter_le_bound_no_isRoot_Icc_sequence using
    interval_order := hab,
    left_no_roots := hF,
    right_no_roots := hG,
    source_bound := h

example {F G : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hab : ∀ i : Nat, a i ≤ b i)
    (hF : ∀ i : Nat, ∀ x, a i ≤ x → x ≤ b i → ¬ (F i).IsRoot x)
    (hG : ∀ i : Nat, ∀ x, a i ≤ x → x ≤ b i → ¬ (G i).IsRoot x)
    (h : ∀ i : Nat,
      (((F i).roots.filter (a i < ·)).card : ℤ) -
          ((G i).roots.filter (a i < ·)).card ≤ 1 ∧
        (((G i).roots.filter (a i < ·)).card : ℤ) -
          ((F i).roots.filter (a i < ·)).card ≤ 1) :
    ∀ i : Nat,
      (((F i).roots.filter (b i < ·)).card : ℤ) -
          ((G i).roots.filter (b i < ·)).card ≤ 1 ∧
        (((G i).roots.filter (b i < ·)).card : ℤ) -
          ((F i).roots.filter (b i < ·)).card ≤ 1 := by
  rr_card_roots_filter_gt_bound_no_isRoot_Icc_sequence using
    interval_order := hab,
    left_no_roots := hF,
    right_no_roots := hG,
    source_bound := h

example {F G : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hab : ∀ i : Nat, a i ≤ b i)
    (hF : ∀ i : Nat, ∀ x, a i ≤ x → x ≤ b i → ¬ (F i).IsRoot x)
    (hG : ∀ i : Nat, ∀ x, a i ≤ x → x ≤ b i → ¬ (G i).IsRoot x)
    (hle : ∀ i : Nat,
      (((F i).roots.filter (· ≤ a i)).card : ℤ) -
          ((G i).roots.filter (· ≤ a i)).card ≤ 1 ∧
        (((G i).roots.filter (· ≤ a i)).card : ℤ) -
          ((F i).roots.filter (· ≤ a i)).card ≤ 1)
    (hgt : ∀ i : Nat,
      (((F i).roots.filter (a i < ·)).card : ℤ) -
          ((G i).roots.filter (a i < ·)).card ≤ 1 ∧
        (((G i).roots.filter (a i < ·)).card : ℤ) -
          ((F i).roots.filter (a i < ·)).card ≤ 1) :
    ∀ i : Nat,
      ((((F i).roots.filter (· ≤ b i)).card : ℤ) -
          ((G i).roots.filter (· ≤ b i)).card ≤ 1 ∧
        (((G i).roots.filter (· ≤ b i)).card : ℤ) -
          ((F i).roots.filter (· ≤ b i)).card ≤ 1) ∧
        ((((F i).roots.filter (b i < ·)).card : ℤ) -
            ((G i).roots.filter (b i < ·)).card ≤ 1 ∧
          (((G i).roots.filter (b i < ·)).card : ℤ) -
            ((F i).roots.filter (b i < ·)).card ≤ 1) := by
  rr_card_roots_filter_le_and_gt_bound_no_isRoot_Icc_sequence using
    interval_order := hab,
    left_no_roots := hF,
    right_no_roots := hG,
    lower_source_bound := hle,
    upper_source_bound := hgt

example {f g : ℝ[X]} {μ₀ μ₁ x : ℝ}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hμ₀ : 0 ≤ μ₀)
    (hμ₀μ₁ : μ₀ ≤ μ₁)
    (hne : ∀ μ ∈ Set.Icc μ₀ μ₁, ¬ (f + C μ * g).IsRoot x) :
    ((f + C μ₀ * g).roots.filter (x < ·)).card =
      ((f + C μ₁ * g).roots.filter (x < ·)).card := by
  rr_rightFamily_sameDegree_gt_count_eq using
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    pos_combo := hfg,
    same_degree := hdeg,
    left_parameter_nonneg := hμ₀,
    interval_order := hμ₀μ₁,
    threshold_not_root := hne

example {f g : ℝ[X]} {x : ℝ}
    (hdeg : ∀ μ ∈ Set.Icc (0 : ℝ) 1,
      (f + C μ * g).natDegree = (f + C (0 : ℝ) * g).natDegree)
    (hrr : ∀ μ ∈ Set.Icc (0 : ℝ) 1, (f + C μ * g).Splits)
    (hne : ∀ μ ∈ Set.Icc (0 : ℝ) 1, ¬ (f + C μ * g).IsRoot x) :
    ((f + C (0 : ℝ) * g).roots.filter (x < ·)).card =
      ((f + C (1 : ℝ) * g).roots.filter (x < ·)).card := by
  rr_rightFamily_zero_one_gt_count_eq using
    degree_on_interval := hdeg,
    splits_on_interval := hrr,
    threshold_not_root := hne

example {f g : ℝ[X]} {x : ℝ}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hxg : ¬ g.IsRoot x)
    (hno : ∀ {μ : ℝ}, 0 ≤ μ → ¬ (f + C μ * g).IsRoot x) :
    (f.roots.filter (x < ·)).card = (g.roots.filter (x < ·)).card := by
  rr_sameDegree_gt_count_eq_no_rightFamily using
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    pos_combo := hfg,
    same_degree := hdeg,
    right_not_root := hxg,
    no_right_family_roots := hno

example {f g : ℝ[X]} {x : ℝ}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hxg : ¬ g.IsRoot x)
    (hno : ∀ {μ : ℝ}, 0 ≤ μ → ¬ (f + C μ * g).IsRoot x) :
    ((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) -
        (f.roots.filter (x < ·)).card ≤ 1 := by
  rr_sameDegree_rootCountAbove_no_rightFamily using
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    pos_combo := hfg,
    same_degree := hdeg,
    right_not_root := hxg,
    no_right_family_roots := hno

example {f g : ℝ[X]} {x : ℝ}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hxf : ¬ f.IsRoot x)
    (hxg : ¬ g.IsRoot x)
    (hno : ¬ ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot x) :
    ((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) -
        (f.roots.filter (x < ·)).card ≤ 1 := by
  rr_sameDegree_rootCountAbove_no_pos_crossing using
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    pos_combo := hfg,
    same_degree := hdeg,
    left_not_root := hxf,
    right_not_root := hxg,
    no_positive_crossing := hno

example {f g : ℝ[X]} {x : ℝ}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hxf : ¬ f.IsRoot x)
    (hxg : ¬ g.IsRoot x)
    (hcross : ∃ μ : ℝ, 0 < μ ∧ (f + C μ * g).IsRoot x) :
    ((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) -
        (f.roots.filter (x < ·)).card ≤ 1 := by
  rr_sameDegree_rootCountAbove_pos_crossing using
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    pos_combo := hfg,
    same_degree := hdeg,
    no_common_roots := hno,
    left_not_root := hxf,
    right_not_root := hxg,
    positive_crossing := hcross

example {F G : Nat → ℝ[X]} {μ₀ μ₁ x : Nat → ℝ}
    (hF_pos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG_pos : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hFG : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hdeg : ∀ i : Nat, (G i).natDegree = (F i).natDegree)
    (hμ₀ : ∀ i : Nat, 0 ≤ μ₀ i)
    (hμ₀μ₁ : ∀ i : Nat, μ₀ i ≤ μ₁ i)
    (hne : ∀ i : Nat, ∀ μ ∈ Set.Icc (μ₀ i) (μ₁ i),
      ¬ (F i + C μ * G i).IsRoot (x i)) :
    ∀ i : Nat,
      ((F i + C (μ₀ i) * G i).roots.filter (x i < ·)).card =
        ((F i + C (μ₁ i) * G i).roots.filter (x i < ·)).card := by
  rr_rightFamily_sameDegree_gt_count_eq_sequence using
    left_pos_lc := hF_pos,
    right_pos_lc := hG_pos,
    pos_combo := hFG,
    same_degree := hdeg,
    left_parameter_nonneg := hμ₀,
    interval_order := hμ₀μ₁,
    threshold_not_root := hne

example {F G : Nat → ℝ[X]} {x : Nat → ℝ}
    (hdeg : ∀ i : Nat, ∀ μ ∈ Set.Icc (0 : ℝ) 1,
      (F i + C μ * G i).natDegree =
        (F i + C (0 : ℝ) * G i).natDegree)
    (hrr : ∀ i : Nat, ∀ μ ∈ Set.Icc (0 : ℝ) 1,
      (F i + C μ * G i).Splits)
    (hne : ∀ i : Nat, ∀ μ ∈ Set.Icc (0 : ℝ) 1,
      ¬ (F i + C μ * G i).IsRoot (x i)) :
    ∀ i : Nat,
      ((F i + C (0 : ℝ) * G i).roots.filter (x i < ·)).card =
        ((F i + C (1 : ℝ) * G i).roots.filter (x i < ·)).card := by
  rr_rightFamily_zero_one_gt_count_eq_sequence using
    degree_on_interval := hdeg,
    splits_on_interval := hrr,
    threshold_not_root := hne

example {F G : Nat → ℝ[X]} {x : Nat → ℝ}
    (hF_pos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG_pos : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hFG : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hdeg : ∀ i : Nat, (G i).natDegree = (F i).natDegree)
    (hxG : ∀ i : Nat, ¬ (G i).IsRoot (x i))
    (hno : ∀ i : Nat, ∀ {μ : ℝ}, 0 ≤ μ →
      ¬ (F i + C μ * G i).IsRoot (x i)) :
    ∀ i : Nat,
      ((F i).roots.filter (x i < ·)).card =
        ((G i).roots.filter (x i < ·)).card := by
  rr_sameDegree_gt_count_eq_no_rightFamily_sequence using
    left_pos_lc := hF_pos,
    right_pos_lc := hG_pos,
    pos_combo := hFG,
    same_degree := hdeg,
    right_not_root := hxG,
    no_right_family_roots := hno

example {F G : Nat → ℝ[X]} {x : Nat → ℝ}
    (hF_pos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG_pos : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hFG : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hdeg : ∀ i : Nat, (G i).natDegree = (F i).natDegree)
    (hxG : ∀ i : Nat, ¬ (G i).IsRoot (x i))
    (hno : ∀ i : Nat, ∀ {μ : ℝ}, 0 ≤ μ →
      ¬ (F i + C μ * G i).IsRoot (x i)) :
    ∀ i : Nat,
      (((F i).roots.filter (x i < ·)).card : ℤ) -
          ((G i).roots.filter (x i < ·)).card ≤ 1 ∧
        (((G i).roots.filter (x i < ·)).card : ℤ) -
          ((F i).roots.filter (x i < ·)).card ≤ 1 := by
  rr_sameDegree_rootCountAbove_no_rightFamily_sequence using
    left_pos_lc := hF_pos,
    right_pos_lc := hG_pos,
    pos_combo := hFG,
    same_degree := hdeg,
    right_not_root := hxG,
    no_right_family_roots := hno

example {F G : Nat → ℝ[X]} {x : Nat → ℝ}
    (hF_pos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG_pos : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hFG : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hdeg : ∀ i : Nat, (G i).natDegree = (F i).natDegree)
    (hxF : ∀ i : Nat, ¬ (F i).IsRoot (x i))
    (hxG : ∀ i : Nat, ¬ (G i).IsRoot (x i))
    (hno : ∀ i : Nat,
      ¬ ∃ μ : ℝ, 0 < μ ∧ (F i + C μ * G i).IsRoot (x i)) :
    ∀ i : Nat,
      (((F i).roots.filter (x i < ·)).card : ℤ) -
          ((G i).roots.filter (x i < ·)).card ≤ 1 ∧
        (((G i).roots.filter (x i < ·)).card : ℤ) -
          ((F i).roots.filter (x i < ·)).card ≤ 1 := by
  rr_sameDegree_rootCountAbove_no_pos_crossing_sequence using
    left_pos_lc := hF_pos,
    right_pos_lc := hG_pos,
    pos_combo := hFG,
    same_degree := hdeg,
    left_not_root := hxF,
    right_not_root := hxG,
    no_positive_crossing := hno

example {F G : Nat → ℝ[X]} {x : Nat → ℝ}
    (hF_pos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG_pos : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hFG : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hdeg : ∀ i : Nat, (G i).natDegree = (F i).natDegree)
    (hno : ∀ i : Nat, ∀ r, (F i).IsRoot r → ¬ (G i).IsRoot r)
    (hxF : ∀ i : Nat, ¬ (F i).IsRoot (x i))
    (hxG : ∀ i : Nat, ¬ (G i).IsRoot (x i))
    (hcross : ∀ i : Nat,
      ∃ μ : ℝ, 0 < μ ∧ (F i + C μ * G i).IsRoot (x i)) :
    ∀ i : Nat,
      (((F i).roots.filter (x i < ·)).card : ℤ) -
          ((G i).roots.filter (x i < ·)).card ≤ 1 ∧
        (((G i).roots.filter (x i < ·)).card : ℤ) -
          ((F i).roots.filter (x i < ·)).card ≤ 1 := by
  rr_sameDegree_rootCountAbove_pos_crossing_sequence using
    left_pos_lc := hF_pos,
    right_pos_lc := hG_pos,
    pos_combo := hFG,
    same_degree := hdeg,
    no_common_roots := hno,
    left_not_root := hxF,
    right_not_root := hxG,
    positive_crossing := hcross

example {f g : ℝ[X]} {x : ℝ}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hfdeg : f.natDegree ≤ 2) :
    ((f.roots.filter (· ≤ x)).card : ℤ) -
        (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) -
        (f.roots.filter (· ≤ x)).card ≤ 1 := by
  rr_posCombo_sameDegree_rootCount_degree_le_two using
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    left_nonneg_coeffs := hfnn,
    right_nonneg_coeffs := hgnn,
    pos_combo := hfg,
    same_degree := hdeg,
    no_common_roots := hno,
    left_degree_le_two := hfdeg,
    threshold := x

example {f g : ℝ[X]} {x : ℝ}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hfdeg : f.natDegree ≤ 2) :
    ((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) -
        (f.roots.filter (x < ·)).card ≤ 1 := by
  rr_posCombo_sameDegree_rootCountAbove_degree_le_two using
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    left_nonneg_coeffs := hfnn,
    right_nonneg_coeffs := hgnn,
    pos_combo := hfg,
    same_degree := hdeg,
    no_common_roots := hno,
    left_degree_le_two := hfdeg,
    threshold := x

example {f g : ℝ[X]}
    (hfdeg : f.natDegree ≤ 1) :
    (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
      (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0) := by
  rr_sameDegree_rootCrossing_degree_le_one using
    left_degree_le_one := hfdeg

example {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hfdeg : f.natDegree ≤ 2) :
    (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
      (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0) := by
  rr_posCombo_sameDegree_rootCrossing_degree_le_two using
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    left_nonneg_coeffs := hfnn,
    right_nonneg_coeffs := hgnn,
    pos_combo := hfg,
    same_degree := hdeg,
    no_common_roots := hno,
    left_degree_le_two := hfdeg

example {f g : ℝ[X]} {x : ℝ}
    (hcomp : Compatible f g)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hf_split : f.Splits)
    (hfdeg : f.natDegree ≤ 2) :
    ((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card ≤ 2 ∧
      ((g.roots.filter (x < ·)).card : ℤ) -
        (f.roots.filter (x < ·)).card ≤ 2 := by
  rr_compatible_succDegree_rootCountAbove_le_two using
    compatible := hcomp,
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    succ_degree := hdeg,
    left_splits := hf_split,
    left_degree_le_two := hfdeg,
    threshold := x

example {f g : ℝ[X]} {x : ℝ}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hfdeg : f.natDegree ≤ 3) :
    ((f.roots.filter (· ≤ x)).card : ℤ) -
        (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) -
        (f.roots.filter (· ≤ x)).card ≤ 1 := by
  rr_posCombo_sameDegree_rootCount_degree_le_three using
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    left_nonneg_coeffs := hfnn,
    right_nonneg_coeffs := hgnn,
    pos_combo := hfg,
    same_degree := hdeg,
    no_common_roots := hno,
    left_degree_le_three := hfdeg,
    threshold := x

example {f g : ℝ[X]} {x : ℝ}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hfdeg : f.natDegree ≤ 3) :
    ((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) -
        (f.roots.filter (x < ·)).card ≤ 1 := by
  rr_posCombo_sameDegree_rootCountAbove_degree_le_three using
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    left_nonneg_coeffs := hfnn,
    right_nonneg_coeffs := hgnn,
    pos_combo := hfg,
    same_degree := hdeg,
    no_common_roots := hno,
    left_degree_le_three := hfdeg,
    threshold := x

example {f g : ℝ[X]}
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hfdeg : f.natDegree ≤ 3) :
    (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
      (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0) := by
  rr_posCombo_sameDegree_rootCrossing_degree_le_three using
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    left_nonneg_coeffs := hfnn,
    right_nonneg_coeffs := hgnn,
    pos_combo := hfg,
    same_degree := hdeg,
    no_common_roots := hno,
    left_degree_le_three := hfdeg

example {f g : ℝ[X]} {x : ℝ}
    (hbelow : CubicInteriorTwoBelowStatement)
    (habove : CubicInteriorTwoAboveStatement)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hfdeg : f.natDegree ≤ 3) :
    ((f.roots.filter (· ≤ x)).card : ℤ) -
        (g.roots.filter (· ≤ x)).card ≤ 1 ∧
      ((g.roots.filter (· ≤ x)).card : ℤ) -
        (f.roots.filter (· ≤ x)).card ≤ 1 := by
  rr_posCombo_sameDegree_rootCount_cubicInterior using
    below_certificate := hbelow,
    above_certificate := habove,
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    left_nonneg_coeffs := hfnn,
    right_nonneg_coeffs := hgnn,
    pos_combo := hfg,
    same_degree := hdeg,
    no_common_roots := hno,
    left_degree_le_three := hfdeg,
    threshold := x

example {f g : ℝ[X]} {x : ℝ}
    (hbelow : CubicInteriorTwoBelowStatement)
    (habove : CubicInteriorTwoAboveStatement)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hfdeg : f.natDegree ≤ 3) :
    ((f.roots.filter (x < ·)).card : ℤ) -
        (g.roots.filter (x < ·)).card ≤ 1 ∧
      ((g.roots.filter (x < ·)).card : ℤ) -
        (f.roots.filter (x < ·)).card ≤ 1 := by
  rr_posCombo_sameDegree_rootCountAbove_cubicInterior using
    below_certificate := hbelow,
    above_certificate := habove,
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    left_nonneg_coeffs := hfnn,
    right_nonneg_coeffs := hgnn,
    pos_combo := hfg,
    same_degree := hdeg,
    no_common_roots := hno,
    left_degree_le_three := hfdeg,
    threshold := x

example {f g : ℝ[X]}
    (hbelow : CubicInteriorTwoBelowStatement)
    (habove : CubicInteriorTwoAboveStatement)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hfdeg : f.natDegree ≤ 3) :
    (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc g).getD j 0 ≤ (rootSeqDesc f).getD (j - 1) 0) ∧
      (∀ j, 1 ≤ j → j < f.natDegree →
        (rootSeqDesc f).getD j 0 ≤ (rootSeqDesc g).getD (j - 1) 0) := by
  rr_posCombo_sameDegree_rootCrossing_cubicInterior using
    below_certificate := hbelow,
    above_certificate := habove,
    left_pos_lc := hf_pos,
    right_pos_lc := hg_pos,
    left_nonneg_coeffs := hfnn,
    right_nonneg_coeffs := hgnn,
    pos_combo := hfg,
    same_degree := hdeg,
    no_common_roots := hno,
    left_degree_le_three := hfdeg

example {F G : Nat → ℝ[X]} {x : Nat → ℝ}
    (hF_pos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG_pos : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hFnn : ∀ i : Nat, HasNonnegCoeffs (F i))
    (hGnn : ∀ i : Nat, HasNonnegCoeffs (G i))
    (hFG : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hdeg : ∀ i : Nat, (G i).natDegree = (F i).natDegree)
    (hno : ∀ i : Nat, ∀ r, (F i).IsRoot r → ¬ (G i).IsRoot r)
    (hFdeg : ∀ i : Nat, (F i).natDegree ≤ 2) :
    ∀ i : Nat,
      (((F i).roots.filter (· ≤ x i)).card : ℤ) -
          ((G i).roots.filter (· ≤ x i)).card ≤ 1 ∧
        (((G i).roots.filter (· ≤ x i)).card : ℤ) -
          ((F i).roots.filter (· ≤ x i)).card ≤ 1 := by
  rr_posCombo_sameDegree_rootCount_degree_le_two_sequence using
    left_pos_lc := hF_pos,
    right_pos_lc := hG_pos,
    left_nonneg_coeffs := hFnn,
    right_nonneg_coeffs := hGnn,
    pos_combo := hFG,
    same_degree := hdeg,
    no_common_roots := hno,
    left_degree_le_two := hFdeg

example {F G : Nat → ℝ[X]} {x : Nat → ℝ}
    (hF_pos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG_pos : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hFnn : ∀ i : Nat, HasNonnegCoeffs (F i))
    (hGnn : ∀ i : Nat, HasNonnegCoeffs (G i))
    (hFG : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hdeg : ∀ i : Nat, (G i).natDegree = (F i).natDegree)
    (hno : ∀ i : Nat, ∀ r, (F i).IsRoot r → ¬ (G i).IsRoot r)
    (hFdeg : ∀ i : Nat, (F i).natDegree ≤ 2) :
    ∀ i : Nat,
      (((F i).roots.filter (x i < ·)).card : ℤ) -
          ((G i).roots.filter (x i < ·)).card ≤ 1 ∧
        (((G i).roots.filter (x i < ·)).card : ℤ) -
          ((F i).roots.filter (x i < ·)).card ≤ 1 := by
  rr_posCombo_sameDegree_rootCountAbove_degree_le_two_sequence using
    left_pos_lc := hF_pos,
    right_pos_lc := hG_pos,
    left_nonneg_coeffs := hFnn,
    right_nonneg_coeffs := hGnn,
    pos_combo := hFG,
    same_degree := hdeg,
    no_common_roots := hno,
    left_degree_le_two := hFdeg

example {F G : Nat → ℝ[X]}
    (hFdeg : ∀ i : Nat, (F i).natDegree ≤ 1) :
    ∀ i : Nat,
      (∀ j, 1 ≤ j → j < (F i).natDegree →
          (rootSeqDesc (G i)).getD j 0 ≤
            (rootSeqDesc (F i)).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < (F i).natDegree →
          (rootSeqDesc (F i)).getD j 0 ≤
            (rootSeqDesc (G i)).getD (j - 1) 0) := by
  rr_sameDegree_rootCrossing_degree_le_one_sequence using
    left_degree_le_one := hFdeg

example {F G : Nat → ℝ[X]}
    (hF_pos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG_pos : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hFnn : ∀ i : Nat, HasNonnegCoeffs (F i))
    (hGnn : ∀ i : Nat, HasNonnegCoeffs (G i))
    (hFG : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hdeg : ∀ i : Nat, (G i).natDegree = (F i).natDegree)
    (hno : ∀ i : Nat, ∀ r, (F i).IsRoot r → ¬ (G i).IsRoot r)
    (hFdeg : ∀ i : Nat, (F i).natDegree ≤ 2) :
    ∀ i : Nat,
      (∀ j, 1 ≤ j → j < (F i).natDegree →
          (rootSeqDesc (G i)).getD j 0 ≤
            (rootSeqDesc (F i)).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < (F i).natDegree →
          (rootSeqDesc (F i)).getD j 0 ≤
            (rootSeqDesc (G i)).getD (j - 1) 0) := by
  rr_posCombo_sameDegree_rootCrossing_degree_le_two_sequence using
    left_pos_lc := hF_pos,
    right_pos_lc := hG_pos,
    left_nonneg_coeffs := hFnn,
    right_nonneg_coeffs := hGnn,
    pos_combo := hFG,
    same_degree := hdeg,
    no_common_roots := hno,
    left_degree_le_two := hFdeg

example {F G : Nat → ℝ[X]} {x : Nat → ℝ}
    (hcomp : ∀ i : Nat, Compatible (F i) (G i))
    (hF_pos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG_pos : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hdeg : ∀ i : Nat, (G i).natDegree = (F i).natDegree + 1)
    (hFsplit : ∀ i : Nat, (F i).Splits)
    (hFdeg : ∀ i : Nat, (F i).natDegree ≤ 2) :
    ∀ i : Nat,
      (((F i).roots.filter (x i < ·)).card : ℤ) -
          ((G i).roots.filter (x i < ·)).card ≤ 2 ∧
        (((G i).roots.filter (x i < ·)).card : ℤ) -
          ((F i).roots.filter (x i < ·)).card ≤ 2 := by
  rr_compatible_succDegree_rootCountAbove_le_two_sequence using
    compatible := hcomp,
    left_pos_lc := hF_pos,
    right_pos_lc := hG_pos,
    succ_degree := hdeg,
    left_splits := hFsplit,
    left_degree_le_two := hFdeg

example {F G : Nat → ℝ[X]} {x : Nat → ℝ}
    (hF_pos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG_pos : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hFnn : ∀ i : Nat, HasNonnegCoeffs (F i))
    (hGnn : ∀ i : Nat, HasNonnegCoeffs (G i))
    (hFG : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hdeg : ∀ i : Nat, (G i).natDegree = (F i).natDegree)
    (hno : ∀ i : Nat, ∀ r, (F i).IsRoot r → ¬ (G i).IsRoot r)
    (hFdeg : ∀ i : Nat, (F i).natDegree ≤ 3) :
    ∀ i : Nat,
      (((F i).roots.filter (· ≤ x i)).card : ℤ) -
          ((G i).roots.filter (· ≤ x i)).card ≤ 1 ∧
        (((G i).roots.filter (· ≤ x i)).card : ℤ) -
          ((F i).roots.filter (· ≤ x i)).card ≤ 1 := by
  rr_posCombo_sameDegree_rootCount_degree_le_three_sequence using
    left_pos_lc := hF_pos,
    right_pos_lc := hG_pos,
    left_nonneg_coeffs := hFnn,
    right_nonneg_coeffs := hGnn,
    pos_combo := hFG,
    same_degree := hdeg,
    no_common_roots := hno,
    left_degree_le_three := hFdeg

example {F G : Nat → ℝ[X]} {x : Nat → ℝ}
    (hF_pos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG_pos : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hFnn : ∀ i : Nat, HasNonnegCoeffs (F i))
    (hGnn : ∀ i : Nat, HasNonnegCoeffs (G i))
    (hFG : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hdeg : ∀ i : Nat, (G i).natDegree = (F i).natDegree)
    (hno : ∀ i : Nat, ∀ r, (F i).IsRoot r → ¬ (G i).IsRoot r)
    (hFdeg : ∀ i : Nat, (F i).natDegree ≤ 3) :
    ∀ i : Nat,
      (((F i).roots.filter (x i < ·)).card : ℤ) -
          ((G i).roots.filter (x i < ·)).card ≤ 1 ∧
        (((G i).roots.filter (x i < ·)).card : ℤ) -
          ((F i).roots.filter (x i < ·)).card ≤ 1 := by
  rr_posCombo_sameDegree_rootCountAbove_degree_le_three_sequence using
    left_pos_lc := hF_pos,
    right_pos_lc := hG_pos,
    left_nonneg_coeffs := hFnn,
    right_nonneg_coeffs := hGnn,
    pos_combo := hFG,
    same_degree := hdeg,
    no_common_roots := hno,
    left_degree_le_three := hFdeg

example {F G : Nat → ℝ[X]}
    (hF_pos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG_pos : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hFnn : ∀ i : Nat, HasNonnegCoeffs (F i))
    (hGnn : ∀ i : Nat, HasNonnegCoeffs (G i))
    (hFG : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hdeg : ∀ i : Nat, (G i).natDegree = (F i).natDegree)
    (hno : ∀ i : Nat, ∀ r, (F i).IsRoot r → ¬ (G i).IsRoot r)
    (hFdeg : ∀ i : Nat, (F i).natDegree ≤ 3) :
    ∀ i : Nat,
      (∀ j, 1 ≤ j → j < (F i).natDegree →
          (rootSeqDesc (G i)).getD j 0 ≤
            (rootSeqDesc (F i)).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < (F i).natDegree →
          (rootSeqDesc (F i)).getD j 0 ≤
            (rootSeqDesc (G i)).getD (j - 1) 0) := by
  rr_posCombo_sameDegree_rootCrossing_degree_le_three_sequence using
    left_pos_lc := hF_pos,
    right_pos_lc := hG_pos,
    left_nonneg_coeffs := hFnn,
    right_nonneg_coeffs := hGnn,
    pos_combo := hFG,
    same_degree := hdeg,
    no_common_roots := hno,
    left_degree_le_three := hFdeg

example {F G : Nat → ℝ[X]} {x : Nat → ℝ}
    (hbelow : CubicInteriorTwoBelowStatement)
    (habove : CubicInteriorTwoAboveStatement)
    (hF_pos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG_pos : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hFnn : ∀ i : Nat, HasNonnegCoeffs (F i))
    (hGnn : ∀ i : Nat, HasNonnegCoeffs (G i))
    (hFG : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hdeg : ∀ i : Nat, (G i).natDegree = (F i).natDegree)
    (hno : ∀ i : Nat, ∀ r, (F i).IsRoot r → ¬ (G i).IsRoot r)
    (hFdeg : ∀ i : Nat, (F i).natDegree ≤ 3) :
    ∀ i : Nat,
      (((F i).roots.filter (· ≤ x i)).card : ℤ) -
          ((G i).roots.filter (· ≤ x i)).card ≤ 1 ∧
        (((G i).roots.filter (· ≤ x i)).card : ℤ) -
          ((F i).roots.filter (· ≤ x i)).card ≤ 1 := by
  rr_posCombo_sameDegree_rootCount_cubicInterior_sequence using
    below_certificate := hbelow,
    above_certificate := habove,
    left_pos_lc := hF_pos,
    right_pos_lc := hG_pos,
    left_nonneg_coeffs := hFnn,
    right_nonneg_coeffs := hGnn,
    pos_combo := hFG,
    same_degree := hdeg,
    no_common_roots := hno,
    left_degree_le_three := hFdeg

example {F G : Nat → ℝ[X]} {x : Nat → ℝ}
    (hbelow : CubicInteriorTwoBelowStatement)
    (habove : CubicInteriorTwoAboveStatement)
    (hF_pos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG_pos : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hFnn : ∀ i : Nat, HasNonnegCoeffs (F i))
    (hGnn : ∀ i : Nat, HasNonnegCoeffs (G i))
    (hFG : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hdeg : ∀ i : Nat, (G i).natDegree = (F i).natDegree)
    (hno : ∀ i : Nat, ∀ r, (F i).IsRoot r → ¬ (G i).IsRoot r)
    (hFdeg : ∀ i : Nat, (F i).natDegree ≤ 3) :
    ∀ i : Nat,
      (((F i).roots.filter (x i < ·)).card : ℤ) -
          ((G i).roots.filter (x i < ·)).card ≤ 1 ∧
        (((G i).roots.filter (x i < ·)).card : ℤ) -
          ((F i).roots.filter (x i < ·)).card ≤ 1 := by
  rr_posCombo_sameDegree_rootCountAbove_cubicInterior_sequence using
    below_certificate := hbelow,
    above_certificate := habove,
    left_pos_lc := hF_pos,
    right_pos_lc := hG_pos,
    left_nonneg_coeffs := hFnn,
    right_nonneg_coeffs := hGnn,
    pos_combo := hFG,
    same_degree := hdeg,
    no_common_roots := hno,
    left_degree_le_three := hFdeg

example {F G : Nat → ℝ[X]}
    (hbelow : CubicInteriorTwoBelowStatement)
    (habove : CubicInteriorTwoAboveStatement)
    (hF_pos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hG_pos : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hFnn : ∀ i : Nat, HasNonnegCoeffs (F i))
    (hGnn : ∀ i : Nat, HasNonnegCoeffs (G i))
    (hFG : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hdeg : ∀ i : Nat, (G i).natDegree = (F i).natDegree)
    (hno : ∀ i : Nat, ∀ r, (F i).IsRoot r → ¬ (G i).IsRoot r)
    (hFdeg : ∀ i : Nat, (F i).natDegree ≤ 3) :
    ∀ i : Nat,
      (∀ j, 1 ≤ j → j < (F i).natDegree →
          (rootSeqDesc (G i)).getD j 0 ≤
            (rootSeqDesc (F i)).getD (j - 1) 0) ∧
        (∀ j, 1 ≤ j → j < (F i).natDegree →
          (rootSeqDesc (F i)).getD j 0 ≤
            (rootSeqDesc (G i)).getD (j - 1) 0) := by
  rr_posCombo_sameDegree_rootCrossing_cubicInterior_sequence using
    below_certificate := hbelow,
    above_certificate := habove,
    left_pos_lc := hF_pos,
    right_pos_lc := hG_pos,
    left_nonneg_coeffs := hFnn,
    right_nonneg_coeffs := hGnn,
    pos_combo := hFG,
    same_degree := hdeg,
    no_common_roots := hno,
    left_degree_le_three := hFdeg

end Tactic
end RealRooted
