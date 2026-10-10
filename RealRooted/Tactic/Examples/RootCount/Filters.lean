import RealRooted.Tactic.RootCount.CoreRules

/-!
# Root-count tactic regressions: filtered root counts

Regression examples for the `rr_card_roots_filter_*` frontends of
`RealRooted.Tactic.RootCount.CoreRules`: counts of roots above, below and between bounds
transported along a pencil without roots on an interval.
-/

open Polynomial

namespace RealRooted
namespace Tactic

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

end Tactic
end RealRooted
