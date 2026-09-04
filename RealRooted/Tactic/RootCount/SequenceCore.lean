import RealRooted.DegreeIncreasingLocalLowerCount
import RealRooted.PositiveParameterLocalLowerCount
import RealRooted.RootContinuity
import RealRooted.RootCountJump
import RealRooted.SmallPositiveParameterCount
import RealRooted.SuccDegreeLeftEndpoint

/-!
# Pointwise root-count sequence transports

Pointwise sequence forms of public root-count and local-continuity endpoints
used in succ-degree positive-parameter arguments.

For a constant-degree split pencil on `[0, μ]` that avoids a fixed threshold,
`rightFamily_card_roots_gt_eq_zero_param_sequence` applies the proved endpoint
pointwise. The target orientation is the upper-endpoint count equal to the
normalized zero-endpoint count:
`card (roots (f + C μ * g) above x) = card (roots f above x)`.
-/

open Polynomial

namespace RealRooted
namespace Tactic

theorem natDegree_add_C_mul_lt_sequence
    {F G : Nat → ℝ[X]} {μ : Nat → ℝ}
    (hμ : ∀ i : Nat, μ i ≠ 0)
    (hdeg : ∀ i : Nat, (F i).natDegree < (G i).natDegree) :
    ∀ i : Nat, (F i + C (μ i) * G i).natDegree = (G i).natDegree := fun i =>
  Polynomial.natDegree_add_C_mul_of_natDegree_lt (hμ i) (hdeg i)

theorem leadingCoeff_add_C_mul_lt_sequence
    {F G : Nat → ℝ[X]} {μ : Nat → ℝ}
    (hμ : ∀ i : Nat, μ i ≠ 0)
    (hdeg : ∀ i : Nat, (F i).natDegree < (G i).natDegree) :
    ∀ i : Nat,
      (F i + C (μ i) * G i).leadingCoeff = μ i * (G i).leadingCoeff :=
  fun i =>
    Polynomial.leadingCoeff_add_C_mul_of_natDegree_lt (hμ i) (hdeg i)

theorem exists_root_lt_succDegree_add_right_small_sequence
    {F G : Nat → ℝ[X]} (A : Nat → ℝ)
    (hFpos : ∀ i : Nat, 0 < (F i).leadingCoeff)
    (hGpos : ∀ i : Nat, 0 < (G i).leadingCoeff)
    (hdeg : ∀ i : Nat, (G i).natDegree = (F i).natDegree + 1) :
    ∀ i : Nat, ∃ δ : ℝ, 0 < δ ∧ ∀ μ : ℝ, 0 < μ → μ < δ →
      (F i + C μ * G i).Splits →
        ∃ r : ℝ, r ∈ (F i + C μ * G i).roots ∧ r < A i := fun i =>
  RealRooted.exists_root_lt_of_succDegree_add_right_small
    (hFpos i) (hGpos i) (hdeg i) (A i)

theorem degreeIncreasing_local_lower_count_sequence
    {F G : Nat → ℝ[X]} (ρ : Nat → ℝ)
    (hF : ∀ i : Nat, (F i).Splits)
    (hdeg : ∀ i : Nat, (F i).natDegree < (G i).natDegree)
    (hρ : ∀ i : Nat, 0 < ρ i) :
    ∀ i : Nat,
      ∃ δ : ℝ, 0 < δ ∧ ∀ μ : ℝ, 0 < μ → μ < δ →
        (F i + C μ * G i).Splits →
          ∀ a ∈ (F i).roots.toFinset,
            (F i).roots.count a ≤
              ((F i + C μ * G i).roots.filter
                (fun q => |q - a| < ρ i)).card := fun i =>
  RealRooted.degreeIncreasing_local_lower_count
    (hF i) (hdeg i) (ρ i) (hρ i)

theorem positiveParameter_local_lower_count_sequence
    {F G : Nat → ℝ[X]} {μ₀ μ₁ μ ρ : Nat → ℝ}
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
                (fun q => |q - a| < ρ i)).card := fun i =>
  RealRooted.positiveParameter_local_lower_count
    (hsplit i) (hdeg i) (hμ i) (hρ i)

theorem rightFamily_card_roots_gt_eq_zero_param_sequence
    {F G : Nat → ℝ[X]} {x μ : Nat → ℝ}
    (hμ_pos : ∀ i : Nat, 0 < μ i)
    (hdeg : ∀ i : Nat, ∀ η ∈ Set.Icc (0 : ℝ) (μ i),
      (F i + C η * G i).natDegree =
        (F i + C (0 : ℝ) * G i).natDegree)
    (hsplit : ∀ i : Nat, ∀ η ∈ Set.Icc (0 : ℝ) (μ i),
      (F i + C η * G i).Splits)
    (hne : ∀ i : Nat, ∀ η ∈ Set.Icc (0 : ℝ) (μ i),
      ¬ (F i + C η * G i).IsRoot (x i)) :
    ∀ i : Nat,
      ((F i + C (μ i) * G i).roots.filter (x i < ·)).card =
        ((F i).roots.filter (x i < ·)).card := fun i =>
  RealRooted.rightFamily_card_roots_gt_eq_zero_param_of_constant_degree
    (hμ_pos i) (hdeg i) (hsplit i) (hne i)

theorem rightFamily_card_roots_gt_eq_local_lower_sequence
    {F G : Nat → ℝ[X]} {μ₀ μ₁ x : Nat → ℝ}
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
        ((F i + C (μ₁ i) * G i).roots.filter (x i < ·)).card := fun i =>
  RealRooted.rightFamily_card_roots_gt_eq_of_local_lower_counts
    (hμ₁ i) (hdeg i) (hrr i) (hne i) (hlower i)

theorem card_filter_gt_endpoint_eq_local_lower_sequence
    {F G : Nat → ℝ[X]} {x : Nat → ℝ}
    (hFpos : ∀ i : Nat, 0 < (F i).leadingCoeff)
    (hGpos : ∀ i : Nat, 0 < (G i).leadingCoeff)
    (hdeg : ∀ i : Nat, (G i).natDegree = (F i).natDegree + 1)
    (hFsplit : ∀ i : Nat, (F i).Splits)
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
        ((G i).roots.filter (x i < ·)).card := fun i =>
  RealRooted.card_filter_gt_endpoint_eq_of_local_lower_counts
    (hFpos i) (hGpos i) (hdeg i) (hFsplit i) (hx i) (hlocal_lower i)
    (hfg_split i) (hfg_no i) (hgf_split i) (hgf_no i)

theorem closedSegment_eval_ne_zero_same_sign_sequence
    {F G : Nat → ℝ[X]} {β x : Nat → ℝ}
    (hβ0 : ∀ i : Nat, 0 ≤ β i)
    (hβ1 : ∀ i : Nat, β i ≤ 1)
    (hprod : ∀ i : Nat, 0 < (F i).eval (x i) * (G i).eval (x i)) :
    ∀ i : Nat,
      (C (1 - β i) * F i + C (β i) * G i).eval (x i) ≠ 0 := fun i =>
  RealRooted.closedSegment_eval_ne_zero_of_eval_mul_pos
    (hβ0 i) (hβ1 i) (hprod i)

theorem closedSegment_not_isRoot_same_sign_sequence
    {F G : Nat → ℝ[X]} {β x : Nat → ℝ}
    (hβ0 : ∀ i : Nat, 0 ≤ β i)
    (hβ1 : ∀ i : Nat, β i ≤ 1)
    (hprod : ∀ i : Nat, 0 < (F i).eval (x i) * (G i).eval (x i)) :
    ∀ i : Nat, ¬ (C (1 - β i) * F i + C (β i) * G i).IsRoot (x i) :=
  fun i =>
    RealRooted.closedSegment_not_isRoot_of_eval_mul_pos
      (hβ0 i) (hβ1 i) (hprod i)

theorem rightFamily_eval_ne_zero_same_sign_sequence
    {F G : Nat → ℝ[X]} {μ x : Nat → ℝ}
    (hμ : ∀ i : Nat, 0 ≤ μ i)
    (hprod : ∀ i : Nat, 0 < (F i).eval (x i) * (G i).eval (x i)) :
    ∀ i : Nat, (F i + C (μ i) * G i).eval (x i) ≠ 0 := fun i =>
  RealRooted.rightFamily_eval_ne_zero_of_eval_mul_pos (hμ i) (hprod i)

theorem exists_threshold_no_mem_Ioc_sequence (S : Nat → Multiset ℝ)
    (x : Nat → ℝ) :
    ∀ i : Nat, ∃ x' : ℝ, x i < x' ∧ ∀ r ∈ S i, r ≤ x i ∨ x' < r :=
  fun i => RealRooted.exists_threshold_no_mem_Ioc (S i) (x i)

theorem exists_nonRoot_threshold_count_eq_sequence
    {F G : Nat → ℝ[X]} {x : Nat → ℝ}
    (hF : ∀ i : Nat, F i ≠ 0)
    (hG : ∀ i : Nat, G i ≠ 0) :
    ∀ i : Nat,
      ∃ x' : ℝ, x i ≤ x' ∧ (F i).eval x' ≠ 0 ∧ (G i).eval x' ≠ 0 ∧
        ((F i).roots.filter (· ≤ x')).card =
          ((F i).roots.filter (· ≤ x i)).card ∧
        ((G i).roots.filter (· ≤ x')).card =
          ((G i).roots.filter (· ≤ x i)).card := fun i =>
  RealRooted.exists_nonRoot_threshold_count_eq (hF i) (hG i) (x i)

theorem exists_nonRoot_threshold_count_gt_eq_sequence
    {F G : Nat → ℝ[X]} {x : Nat → ℝ}
    (hF : ∀ i : Nat, F i ≠ 0)
    (hG : ∀ i : Nat, G i ≠ 0) :
    ∀ i : Nat,
      ∃ x' : ℝ, x i ≤ x' ∧ (F i).eval x' ≠ 0 ∧ (G i).eval x' ≠ 0 ∧
        ((F i).roots.filter (x' < ·)).card =
          ((F i).roots.filter (x i < ·)).card ∧
        ((G i).roots.filter (x' < ·)).card =
          ((G i).roots.filter (x i < ·)).card := fun i =>
  RealRooted.exists_nonRoot_threshold_count_gt_eq (hF i) (hG i) (x i)

theorem rootCount_diff_le_one_nonRoot_sequence
    {F G : Nat → ℝ[X]}
    (hF : ∀ i : Nat, F i ≠ 0)
    (hG : ∀ i : Nat, G i ≠ 0)
    (hbound : ∀ i : Nat, ∀ x : ℝ, (F i).eval x ≠ 0 → (G i).eval x ≠ 0 →
      (((F i).roots.filter (· ≤ x)).card : ℤ) -
          ((G i).roots.filter (· ≤ x)).card ≤ 1 ∧
        (((G i).roots.filter (· ≤ x)).card : ℤ) -
            ((F i).roots.filter (· ≤ x)).card ≤ (1 : ℤ)) :
    ∀ i : Nat, ∀ x : ℝ,
      (((F i).roots.filter (· ≤ x)).card : ℤ) -
          ((G i).roots.filter (· ≤ x)).card ≤ 1 ∧
        (((G i).roots.filter (· ≤ x)).card : ℤ) -
            ((F i).roots.filter (· ≤ x)).card ≤ (1 : ℤ) := fun i =>
  RealRooted.rootCount_diff_le_one_of_nonRoot (hF i) (hG i) (hbound i)

theorem rootCount_abs_diff_le_one_nonRoot_sequence
    {F G : Nat → ℝ[X]}
    (hF : ∀ i : Nat, F i ≠ 0)
    (hG : ∀ i : Nat, G i ≠ 0)
    (hbound : ∀ i : Nat, ∀ x : ℝ, (F i).eval x ≠ 0 → (G i).eval x ≠ 0 →
      (((F i).roots.filter (· ≤ x)).card : ℤ) -
          ((G i).roots.filter (· ≤ x)).card ≤ 1 ∧
        (((G i).roots.filter (· ≤ x)).card : ℤ) -
            ((F i).roots.filter (· ≤ x)).card ≤ (1 : ℤ)) :
    ∀ i : Nat, ∀ x : ℝ,
      |(((F i).roots.filter (· ≤ x)).card : ℤ) -
          ((G i).roots.filter (· ≤ x)).card| ≤ (1 : ℤ) := fun i =>
  RealRooted.rootCount_abs_diff_le_one_of_nonRoot (hF i) (hG i) (hbound i)

theorem rootCount_diff_le_one_nonRoot_isRoot_sequence
    {F G : Nat → ℝ[X]}
    (hF : ∀ i : Nat, F i ≠ 0)
    (hG : ∀ i : Nat, G i ≠ 0)
    (hbound : ∀ i : Nat, ∀ x : ℝ, ¬ (F i).IsRoot x → ¬ (G i).IsRoot x →
      (((F i).roots.filter (· ≤ x)).card : ℤ) -
          ((G i).roots.filter (· ≤ x)).card ≤ 1 ∧
        (((G i).roots.filter (· ≤ x)).card : ℤ) -
            ((F i).roots.filter (· ≤ x)).card ≤ (1 : ℤ)) :
    ∀ i : Nat, ∀ x : ℝ,
      (((F i).roots.filter (· ≤ x)).card : ℤ) -
          ((G i).roots.filter (· ≤ x)).card ≤ 1 ∧
        (((G i).roots.filter (· ≤ x)).card : ℤ) -
            ((F i).roots.filter (· ≤ x)).card ≤ (1 : ℤ) := fun i =>
  RealRooted.rootCount_diff_le_one_of_nonRoot_isRoot
    (hF i) (hG i) (hbound i)

theorem rootCountAbove_diff_le_one_nonRoot_sequence
    {F G : Nat → ℝ[X]}
    (hF : ∀ i : Nat, F i ≠ 0)
    (hG : ∀ i : Nat, G i ≠ 0)
    (hbound : ∀ i : Nat, ∀ x : ℝ, (F i).eval x ≠ 0 → (G i).eval x ≠ 0 →
      (((F i).roots.filter (x < ·)).card : ℤ) -
          ((G i).roots.filter (x < ·)).card ≤ 1 ∧
        (((G i).roots.filter (x < ·)).card : ℤ) -
            ((F i).roots.filter (x < ·)).card ≤ (1 : ℤ)) :
    ∀ i : Nat, ∀ x : ℝ,
      (((F i).roots.filter (x < ·)).card : ℤ) -
          ((G i).roots.filter (x < ·)).card ≤ 1 ∧
        (((G i).roots.filter (x < ·)).card : ℤ) -
            ((F i).roots.filter (x < ·)).card ≤ (1 : ℤ) := fun i =>
  RealRooted.rootCountAbove_diff_le_one_of_nonRoot
    (hF i) (hG i) (hbound i)

theorem rootCountAbove_diff_le_one_nonRoot_isRoot_sequence
    {F G : Nat → ℝ[X]}
    (hF : ∀ i : Nat, F i ≠ 0)
    (hG : ∀ i : Nat, G i ≠ 0)
    (hbound : ∀ i : Nat, ∀ x : ℝ, ¬ (F i).IsRoot x → ¬ (G i).IsRoot x →
      (((F i).roots.filter (x < ·)).card : ℤ) -
          ((G i).roots.filter (x < ·)).card ≤ 1 ∧
        (((G i).roots.filter (x < ·)).card : ℤ) -
            ((F i).roots.filter (x < ·)).card ≤ (1 : ℤ)) :
    ∀ i : Nat, ∀ x : ℝ,
      (((F i).roots.filter (x < ·)).card : ℤ) -
          ((G i).roots.filter (x < ·)).card ≤ 1 ∧
        (((G i).roots.filter (x < ·)).card : ℤ) -
            ((F i).roots.filter (x < ·)).card ≤ (1 : ℤ) := fun i =>
  RealRooted.rootCountAbove_diff_le_one_of_nonRoot_isRoot
    (hF i) (hG i) (hbound i)

theorem rootCount_max_abs_diff_le_one_sequence
    {F G : Nat → ℝ[X]}
    (h : ∀ i : Nat, ∀ x : ℝ,
      |(((F i).roots.filter (· ≤ x)).card : ℤ) -
          ((G i).roots.filter (· ≤ x)).card| ≤ 1 ∧
        |(((F i).roots.filter (x < ·)).card : ℤ) -
            ((G i).roots.filter (x < ·)).card| ≤ (1 : ℤ)) :
    ∀ i : Nat, ∀ x : ℝ,
      max
        |(((F i).roots.filter (· ≤ x)).card : ℤ) -
          ((G i).roots.filter (· ≤ x)).card|
        |(((F i).roots.filter (x < ·)).card : ℤ) -
          ((G i).roots.filter (x < ·)).card| ≤ (1 : ℤ) := fun i =>
  RealRooted.rootCount_max_abs_diff_le_one_of_bundled (h i)

theorem left_card_roots_succDegree_sequence
    {F G : Nat → ℝ[X]}
    (hFpos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hGpos : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hFG : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hsucc : ∀ i : Nat, (G i).natDegree = (F i).natDegree + 1) :
    ∀ i : Nat, (F i).roots.card = (F i).natDegree := fun i =>
  RealRooted.left_card_roots_of_succDegree
    (hFpos i) (hGpos i) (hFG i) (hsucc i)

theorem right_card_roots_succDegree_sequence
    {F G : Nat → ℝ[X]}
    (hFpos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hGpos : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hFG : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hsucc : ∀ i : Nat, (F i).natDegree = (G i).natDegree + 1) :
    ∀ i : Nat, (G i).roots.card = (G i).natDegree := fun i =>
  RealRooted.right_card_roots_of_succDegree
    (hFpos i) (hGpos i) (hFG i) (hsucc i)

theorem left_ne_zero_card_roots_succDegree_sequence
    {F G : Nat → ℝ[X]}
    (hFpos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hGpos : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hFG : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hsucc : ∀ i : Nat, (G i).natDegree = (F i).natDegree + 1) :
    ∀ i : Nat, F i ≠ 0 ∧ (F i).roots.card = (F i).natDegree := fun i =>
  RealRooted.left_ne_zero_and_card_roots_of_succDegree
    (hFpos i) (hGpos i) (hFG i) (hsucc i)

theorem right_ne_zero_card_roots_succDegree_sequence
    {F G : Nat → ℝ[X]}
    (hFpos : ∀ i : Nat, HasPosLeadingCoeff (F i))
    (hGpos : ∀ i : Nat, HasPosLeadingCoeff (G i))
    (hFG : ∀ i : Nat, PosComboRealRooted (F i) (G i))
    (hsucc : ∀ i : Nat, (F i).natDegree = (G i).natDegree + 1) :
    ∀ i : Nat, G i ≠ 0 ∧ (G i).roots.card = (G i).natDegree := fun i =>
  RealRooted.right_ne_zero_and_card_roots_of_succDegree
    (hFpos i) (hGpos i) (hFG i) (hsucc i)

theorem card_roots_filter_le_eq_no_isRoot_Ioc_sequence
    {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hab : ∀ i : Nat, a i ≤ b i)
    (hno : ∀ i : Nat, ∀ x : ℝ, a i < x → x ≤ b i → ¬ (P i).IsRoot x) :
    ∀ i : Nat,
      ((P i).roots.filter (· ≤ a i)).card =
        ((P i).roots.filter (· ≤ b i)).card := fun i =>
  RealRooted.card_roots_filter_le_eq_of_no_isRoot_Ioc (hab i) (hno i)

theorem card_roots_filter_gt_eq_no_isRoot_Ioc_sequence
    {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hab : ∀ i : Nat, a i ≤ b i)
    (hno : ∀ i : Nat, ∀ x : ℝ, a i < x → x ≤ b i → ¬ (P i).IsRoot x) :
    ∀ i : Nat,
      ((P i).roots.filter (a i < ·)).card =
        ((P i).roots.filter (b i < ·)).card := fun i =>
  RealRooted.card_roots_filter_gt_eq_of_no_isRoot_Ioc (hab i) (hno i)

theorem card_roots_filter_Ioc_zero_no_isRoot_Ioc_sequence
    {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hab : ∀ i : Nat, a i ≤ b i)
    (hno : ∀ i : Nat, ∀ x : ℝ, a i < x → x ≤ b i → ¬ (P i).IsRoot x) :
    ∀ i : Nat,
      ((P i).roots.filter (fun x => a i < x ∧ x ≤ b i)).card = 0 := fun i =>
  RealRooted.card_roots_filter_Ioc_eq_zero_of_no_isRoot_Ioc (hab i) (hno i)

theorem card_roots_filter_all_eq_no_isRoot_Ioc_sequence
    {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hab : ∀ i : Nat, a i ≤ b i)
    (hno : ∀ i : Nat, ∀ x : ℝ, a i < x → x ≤ b i → ¬ (P i).IsRoot x) :
    ∀ i : Nat,
      ((P i).roots.filter (· ≤ a i)).card =
          ((P i).roots.filter (· ≤ b i)).card ∧
        ((P i).roots.filter (a i < ·)).card =
          ((P i).roots.filter (b i < ·)).card ∧
          ((P i).roots.filter (fun x => a i < x ∧ x ≤ b i)).card = 0 :=
  fun i =>
    RealRooted.card_roots_filter_all_eq_of_no_isRoot_Ioc (hab i) (hno i)

theorem card_roots_filter_le_mono_sequence
    {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hab : ∀ i : Nat, a i ≤ b i) :
    ∀ i : Nat,
      ((P i).roots.filter (· ≤ a i)).card ≤
        ((P i).roots.filter (· ≤ b i)).card := fun i =>
  RealRooted.card_roots_filter_le_mono_of_le (hab i)

theorem card_roots_filter_gt_antitone_sequence
    {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hab : ∀ i : Nat, a i ≤ b i) :
    ∀ i : Nat,
      ((P i).roots.filter (b i < ·)).card ≤
        ((P i).roots.filter (a i < ·)).card := fun i =>
  RealRooted.card_roots_filter_gt_antitone_of_le (hab i)

theorem card_roots_filter_le_and_gt_mono_sequence
    {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hab : ∀ i : Nat, a i ≤ b i) :
    ∀ i : Nat,
      ((P i).roots.filter (· ≤ a i)).card ≤
          ((P i).roots.filter (· ≤ b i)).card ∧
        ((P i).roots.filter (b i < ·)).card ≤
          ((P i).roots.filter (a i < ·)).card := fun i =>
  RealRooted.card_roots_filter_le_and_gt_mono_of_le (hab i)

theorem card_roots_filter_le_eq_no_isRoot_Icc_sequence
    {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hab : ∀ i : Nat, a i ≤ b i)
    (hno : ∀ i : Nat, ∀ x : ℝ, a i ≤ x → x ≤ b i → ¬ (P i).IsRoot x) :
    ∀ i : Nat,
      ((P i).roots.filter (· ≤ a i)).card =
        ((P i).roots.filter (· ≤ b i)).card := fun i =>
  RealRooted.card_roots_filter_le_eq_of_no_isRoot_Icc (hab i) (hno i)

theorem card_roots_filter_gt_eq_no_isRoot_Icc_sequence
    {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hab : ∀ i : Nat, a i ≤ b i)
    (hno : ∀ i : Nat, ∀ x : ℝ, a i ≤ x → x ≤ b i → ¬ (P i).IsRoot x) :
    ∀ i : Nat,
      ((P i).roots.filter (a i < ·)).card =
        ((P i).roots.filter (b i < ·)).card := fun i =>
  RealRooted.card_roots_filter_gt_eq_of_no_isRoot_Icc (hab i) (hno i)

theorem card_roots_filter_Ioc_zero_no_isRoot_Icc_sequence
    {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hab : ∀ i : Nat, a i ≤ b i)
    (hno : ∀ i : Nat, ∀ x : ℝ, a i ≤ x → x ≤ b i → ¬ (P i).IsRoot x) :
    ∀ i : Nat,
      ((P i).roots.filter (fun x => a i < x ∧ x ≤ b i)).card = 0 := fun i =>
  RealRooted.card_roots_filter_Ioc_eq_zero_of_no_isRoot_Icc (hab i) (hno i)

theorem card_roots_filter_all_eq_no_isRoot_Icc_sequence
    {P : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hab : ∀ i : Nat, a i ≤ b i)
    (hno : ∀ i : Nat, ∀ x : ℝ, a i ≤ x → x ≤ b i → ¬ (P i).IsRoot x) :
    ∀ i : Nat,
      ((P i).roots.filter (· ≤ a i)).card =
          ((P i).roots.filter (· ≤ b i)).card ∧
        ((P i).roots.filter (a i < ·)).card =
          ((P i).roots.filter (b i < ·)).card ∧
          ((P i).roots.filter (fun x => a i < x ∧ x ≤ b i)).card = 0 :=
  fun i =>
    RealRooted.card_roots_filter_all_eq_of_no_isRoot_Icc (hab i) (hno i)

theorem card_roots_filter_le_sub_eq_no_isRoot_Ioc_sequence
    {F G : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hab : ∀ i : Nat, a i ≤ b i)
    (hF : ∀ i : Nat, ∀ x : ℝ, a i < x → x ≤ b i → ¬ (F i).IsRoot x)
    (hG : ∀ i : Nat, ∀ x : ℝ, a i < x → x ≤ b i → ¬ (G i).IsRoot x) :
    ∀ i : Nat,
      (((F i).roots.filter (· ≤ a i)).card : ℤ) -
          ((G i).roots.filter (· ≤ a i)).card =
        (((F i).roots.filter (· ≤ b i)).card : ℤ) -
          ((G i).roots.filter (· ≤ b i)).card := fun i =>
  RealRooted.card_roots_filter_le_sub_eq_of_no_isRoot_Ioc
    (hab i) (hF i) (hG i)

theorem card_roots_filter_gt_sub_eq_no_isRoot_Ioc_sequence
    {F G : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hab : ∀ i : Nat, a i ≤ b i)
    (hF : ∀ i : Nat, ∀ x : ℝ, a i < x → x ≤ b i → ¬ (F i).IsRoot x)
    (hG : ∀ i : Nat, ∀ x : ℝ, a i < x → x ≤ b i → ¬ (G i).IsRoot x) :
    ∀ i : Nat,
      (((F i).roots.filter (a i < ·)).card : ℤ) -
          ((G i).roots.filter (a i < ·)).card =
        (((F i).roots.filter (b i < ·)).card : ℤ) -
          ((G i).roots.filter (b i < ·)).card := fun i =>
  RealRooted.card_roots_filter_gt_sub_eq_of_no_isRoot_Ioc
    (hab i) (hF i) (hG i)

theorem card_roots_filter_le_bound_no_isRoot_Ioc_sequence
    {F G : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hab : ∀ i : Nat, a i ≤ b i)
    (hF : ∀ i : Nat, ∀ x : ℝ, a i < x → x ≤ b i → ¬ (F i).IsRoot x)
    (hG : ∀ i : Nat, ∀ x : ℝ, a i < x → x ≤ b i → ¬ (G i).IsRoot x)
    (h : ∀ i : Nat,
      (((F i).roots.filter (· ≤ a i)).card : ℤ) -
          ((G i).roots.filter (· ≤ a i)).card ≤ 1 ∧
        (((G i).roots.filter (· ≤ a i)).card : ℤ) -
          ((F i).roots.filter (· ≤ a i)).card ≤ (1 : ℤ)) :
    ∀ i : Nat,
      (((F i).roots.filter (· ≤ b i)).card : ℤ) -
          ((G i).roots.filter (· ≤ b i)).card ≤ 1 ∧
        (((G i).roots.filter (· ≤ b i)).card : ℤ) -
          ((F i).roots.filter (· ≤ b i)).card ≤ (1 : ℤ) := fun i =>
  RealRooted.card_roots_filter_le_bound_of_no_isRoot_Ioc
    (hab i) (hF i) (hG i) (h i)

theorem card_roots_filter_gt_bound_no_isRoot_Ioc_sequence
    {F G : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hab : ∀ i : Nat, a i ≤ b i)
    (hF : ∀ i : Nat, ∀ x : ℝ, a i < x → x ≤ b i → ¬ (F i).IsRoot x)
    (hG : ∀ i : Nat, ∀ x : ℝ, a i < x → x ≤ b i → ¬ (G i).IsRoot x)
    (h : ∀ i : Nat,
      (((F i).roots.filter (a i < ·)).card : ℤ) -
          ((G i).roots.filter (a i < ·)).card ≤ 1 ∧
        (((G i).roots.filter (a i < ·)).card : ℤ) -
          ((F i).roots.filter (a i < ·)).card ≤ (1 : ℤ)) :
    ∀ i : Nat,
      (((F i).roots.filter (b i < ·)).card : ℤ) -
          ((G i).roots.filter (b i < ·)).card ≤ 1 ∧
        (((G i).roots.filter (b i < ·)).card : ℤ) -
          ((F i).roots.filter (b i < ·)).card ≤ (1 : ℤ) := fun i =>
  RealRooted.card_roots_filter_gt_bound_of_no_isRoot_Ioc
    (hab i) (hF i) (hG i) (h i)

theorem card_roots_filter_le_and_gt_bound_no_isRoot_Ioc_sequence
    {F G : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hab : ∀ i : Nat, a i ≤ b i)
    (hF : ∀ i : Nat, ∀ x : ℝ, a i < x → x ≤ b i → ¬ (F i).IsRoot x)
    (hG : ∀ i : Nat, ∀ x : ℝ, a i < x → x ≤ b i → ¬ (G i).IsRoot x)
    (hle : ∀ i : Nat,
      (((F i).roots.filter (· ≤ a i)).card : ℤ) -
          ((G i).roots.filter (· ≤ a i)).card ≤ 1 ∧
        (((G i).roots.filter (· ≤ a i)).card : ℤ) -
          ((F i).roots.filter (· ≤ a i)).card ≤ (1 : ℤ))
    (hgt : ∀ i : Nat,
      (((F i).roots.filter (a i < ·)).card : ℤ) -
          ((G i).roots.filter (a i < ·)).card ≤ 1 ∧
        (((G i).roots.filter (a i < ·)).card : ℤ) -
          ((F i).roots.filter (a i < ·)).card ≤ (1 : ℤ)) :
    ∀ i : Nat,
      ((((F i).roots.filter (· ≤ b i)).card : ℤ) -
          ((G i).roots.filter (· ≤ b i)).card ≤ 1 ∧
        (((G i).roots.filter (· ≤ b i)).card : ℤ) -
          ((F i).roots.filter (· ≤ b i)).card ≤ (1 : ℤ)) ∧
        ((((F i).roots.filter (b i < ·)).card : ℤ) -
            ((G i).roots.filter (b i < ·)).card ≤ 1 ∧
          (((G i).roots.filter (b i < ·)).card : ℤ) -
            ((F i).roots.filter (b i < ·)).card ≤ (1 : ℤ)) := fun i =>
  RealRooted.card_roots_filter_le_and_gt_bound_of_no_isRoot_Ioc
    (hab i) (hF i) (hG i) (hle i) (hgt i)

theorem card_roots_filter_le_sub_eq_no_isRoot_Icc_sequence
    {F G : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hab : ∀ i : Nat, a i ≤ b i)
    (hF : ∀ i : Nat, ∀ x : ℝ, a i ≤ x → x ≤ b i → ¬ (F i).IsRoot x)
    (hG : ∀ i : Nat, ∀ x : ℝ, a i ≤ x → x ≤ b i → ¬ (G i).IsRoot x) :
    ∀ i : Nat,
      (((F i).roots.filter (· ≤ a i)).card : ℤ) -
          ((G i).roots.filter (· ≤ a i)).card =
        (((F i).roots.filter (· ≤ b i)).card : ℤ) -
          ((G i).roots.filter (· ≤ b i)).card := fun i =>
  RealRooted.card_roots_filter_le_sub_eq_of_no_isRoot_Icc
    (hab i) (hF i) (hG i)

theorem card_roots_filter_gt_sub_eq_no_isRoot_Icc_sequence
    {F G : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hab : ∀ i : Nat, a i ≤ b i)
    (hF : ∀ i : Nat, ∀ x : ℝ, a i ≤ x → x ≤ b i → ¬ (F i).IsRoot x)
    (hG : ∀ i : Nat, ∀ x : ℝ, a i ≤ x → x ≤ b i → ¬ (G i).IsRoot x) :
    ∀ i : Nat,
      (((F i).roots.filter (a i < ·)).card : ℤ) -
          ((G i).roots.filter (a i < ·)).card =
        (((F i).roots.filter (b i < ·)).card : ℤ) -
          ((G i).roots.filter (b i < ·)).card := fun i =>
  RealRooted.card_roots_filter_gt_sub_eq_of_no_isRoot_Icc
    (hab i) (hF i) (hG i)

theorem card_roots_filter_le_bound_no_isRoot_Icc_sequence
    {F G : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hab : ∀ i : Nat, a i ≤ b i)
    (hF : ∀ i : Nat, ∀ x : ℝ, a i ≤ x → x ≤ b i → ¬ (F i).IsRoot x)
    (hG : ∀ i : Nat, ∀ x : ℝ, a i ≤ x → x ≤ b i → ¬ (G i).IsRoot x)
    (h : ∀ i : Nat,
      (((F i).roots.filter (· ≤ a i)).card : ℤ) -
          ((G i).roots.filter (· ≤ a i)).card ≤ 1 ∧
        (((G i).roots.filter (· ≤ a i)).card : ℤ) -
          ((F i).roots.filter (· ≤ a i)).card ≤ (1 : ℤ)) :
    ∀ i : Nat,
      (((F i).roots.filter (· ≤ b i)).card : ℤ) -
          ((G i).roots.filter (· ≤ b i)).card ≤ 1 ∧
        (((G i).roots.filter (· ≤ b i)).card : ℤ) -
          ((F i).roots.filter (· ≤ b i)).card ≤ (1 : ℤ) := fun i =>
  RealRooted.card_roots_filter_le_bound_of_no_isRoot_Icc
    (hab i) (hF i) (hG i) (h i)

theorem card_roots_filter_gt_bound_no_isRoot_Icc_sequence
    {F G : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hab : ∀ i : Nat, a i ≤ b i)
    (hF : ∀ i : Nat, ∀ x : ℝ, a i ≤ x → x ≤ b i → ¬ (F i).IsRoot x)
    (hG : ∀ i : Nat, ∀ x : ℝ, a i ≤ x → x ≤ b i → ¬ (G i).IsRoot x)
    (h : ∀ i : Nat,
      (((F i).roots.filter (a i < ·)).card : ℤ) -
          ((G i).roots.filter (a i < ·)).card ≤ 1 ∧
        (((G i).roots.filter (a i < ·)).card : ℤ) -
          ((F i).roots.filter (a i < ·)).card ≤ (1 : ℤ)) :
    ∀ i : Nat,
      (((F i).roots.filter (b i < ·)).card : ℤ) -
          ((G i).roots.filter (b i < ·)).card ≤ 1 ∧
        (((G i).roots.filter (b i < ·)).card : ℤ) -
          ((F i).roots.filter (b i < ·)).card ≤ (1 : ℤ) := fun i =>
  RealRooted.card_roots_filter_gt_bound_of_no_isRoot_Icc
    (hab i) (hF i) (hG i) (h i)

theorem card_roots_filter_le_and_gt_bound_no_isRoot_Icc_sequence
    {F G : Nat → ℝ[X]} {a b : Nat → ℝ}
    (hab : ∀ i : Nat, a i ≤ b i)
    (hF : ∀ i : Nat, ∀ x : ℝ, a i ≤ x → x ≤ b i → ¬ (F i).IsRoot x)
    (hG : ∀ i : Nat, ∀ x : ℝ, a i ≤ x → x ≤ b i → ¬ (G i).IsRoot x)
    (hle : ∀ i : Nat,
      (((F i).roots.filter (· ≤ a i)).card : ℤ) -
          ((G i).roots.filter (· ≤ a i)).card ≤ 1 ∧
        (((G i).roots.filter (· ≤ a i)).card : ℤ) -
          ((F i).roots.filter (· ≤ a i)).card ≤ (1 : ℤ))
    (hgt : ∀ i : Nat,
      (((F i).roots.filter (a i < ·)).card : ℤ) -
          ((G i).roots.filter (a i < ·)).card ≤ 1 ∧
        (((G i).roots.filter (a i < ·)).card : ℤ) -
          ((F i).roots.filter (a i < ·)).card ≤ (1 : ℤ)) :
    ∀ i : Nat,
      ((((F i).roots.filter (· ≤ b i)).card : ℤ) -
          ((G i).roots.filter (· ≤ b i)).card ≤ 1 ∧
        (((G i).roots.filter (· ≤ b i)).card : ℤ) -
          ((F i).roots.filter (· ≤ b i)).card ≤ (1 : ℤ)) ∧
        ((((F i).roots.filter (b i < ·)).card : ℤ) -
            ((G i).roots.filter (b i < ·)).card ≤ 1 ∧
          (((G i).roots.filter (b i < ·)).card : ℤ) -
            ((F i).roots.filter (b i < ·)).card ≤ (1 : ℤ)) := fun i =>
  RealRooted.card_roots_filter_le_and_gt_bound_of_no_isRoot_Icc
    (hab i) (hF i) (hG i) (hle i) (hgt i)

end Tactic
end RealRooted
