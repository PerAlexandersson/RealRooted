import RealRooted.Tactic.RootCount.CoreRules

/-!
# Root-count tactic regressions: core frontends

Regression examples for the scalar and `_sequence` root-count frontends of
`RealRooted.Tactic.RootCount.CoreRules`: degree and leading-coefficient transport,
root-count jumps at non-roots, threshold counts and the zero-parameter endpoint.
-/

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

section ZeroParameterEndpoint

section Scalar

variable {f g : ℝ[X]} {x μ : ℝ}
variable (hμ_pos : 0 < μ)
variable (hdeg : ∀ η ∈ Set.Icc (0 : ℝ) μ,
  (f + C η * g).natDegree = (f + C (0 : ℝ) * g).natDegree)
variable (_hsplit_prefix : ∀ _ν : ℝ, ∀ η ∈ Set.Icc (0 : ℝ) μ,
  (f + C η * g).Splits)
variable (hsplit : ∀ η ∈ Set.Icc (0 : ℝ) μ, (f + C η * g).Splits)
variable (hne : ∀ η ∈ Set.Icc (0 : ℝ) μ, ¬ (f + C η * g).IsRoot x)

/-- The named form exposes all four zero-endpoint transport certificates. -/
example :
    ((f + C μ * g).roots.filter (x < ·)).card =
      (f.roots.filter (x < ·)).card := by
  rr_rightFamily_card_roots_gt_eq_zero_param using
    parameter_pos := hμ_pos,
    degree_on_interval := hdeg,
    splits_on_interval := hsplit,
    threshold_not_root := hne

/-- Lookup rejects a split certificate whose extra prefix remains unresolved. -/
example :
    ((f + C μ * g).roots.filter (x < ·)).card =
      (f.roots.filter (x < ·)).card := by
  rr_rightFamily_card_roots_gt_eq_zero_param

end Scalar

section Sequence

variable {F G : Nat → ℝ[X]} {x μ : Nat → ℝ}
variable (hμ_pos : ∀ i : Nat, 0 < μ i)
variable (hdeg : ∀ i : Nat, ∀ η ∈ Set.Icc (0 : ℝ) (μ i),
  (F i + C η * G i).natDegree =
    (F i + C (0 : ℝ) * G i).natDegree)
variable (_hsplit_prefix : ∀ _ν : ℝ, ∀ i : Nat,
  ∀ η ∈ Set.Icc (0 : ℝ) (μ i), (F i + C η * G i).Splits)
variable (hsplit : ∀ i : Nat, ∀ η ∈ Set.Icc (0 : ℝ) (μ i),
  (F i + C η * G i).Splits)
variable (hne : ∀ i : Nat, ∀ η ∈ Set.Icc (0 : ℝ) (μ i),
  ¬ (F i + C η * G i).IsRoot (x i))

/-- The sequence form applies the proved zero-endpoint equality pointwise. -/
example : ∀ i : Nat,
    ((F i + C (μ i) * G i).roots.filter (x i < ·)).card =
      ((F i).roots.filter (x i < ·)).card := by
  rr_rightFamily_card_roots_gt_eq_zero_param_sequence using
    parameter_pos := hμ_pos,
    degree_on_interval := hdeg,
    splits_on_interval := hsplit,
    threshold_not_root := hne

/-- Sequence inference resolves complete pointwise certificate families. -/
example : ∀ i : Nat,
    ((F i + C (μ i) * G i).roots.filter (x i < ·)).card =
      ((F i).roots.filter (x i < ·)).card := by
  rr_rightFamily_card_roots_gt_eq_zero_param_sequence

end Sequence

end ZeroParameterEndpoint

end Tactic
end RealRooted
