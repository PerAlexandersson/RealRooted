import RealRooted.WeightedSum

/-!
# Weighted-sum tactic frontends

Thin wrappers for the finite Wagner weighted-sum APIs.
-/

open Polynomial

namespace RealRooted
namespace Tactic

theorem weightedSum_sequence_zero
    {L : Nat → List (ℝ × ℝ[X])}
    (hzero : ∀ i : Nat, ∀ ap ∈ L i, ap.1 = 0) :
    ∀ i : Nat, weightedSum (L i) = 0 := fun i =>
  RealRooted.weightedSum_eq_zero_of_forall_coeff_zero _ (hzero i)

theorem weightedSum_sequence_pos_lc
    {L : Nat → List (ℝ × ℝ[X])}
    (hnonneg : ∀ i : Nat, ∀ ap ∈ L i, 0 ≤ ap.1)
    (hpos : ∀ i : Nat, ∀ ap ∈ L i, HasPosLeadingCoeff ap.2)
    (hex : ∀ i : Nat, ∃ ap ∈ L i, 0 < ap.1) :
    ∀ i : Nat, HasPosLeadingCoeff (weightedSum (L i)) := fun i =>
  RealRooted.hasPosLeadingCoeff_weightedSum _ (hnonneg i) (hpos i) (hex i)

theorem weightedCompatibleLeft_sequence_singleton
    {H P : Nat → ℝ[X]} {a : Nat → ℝ}
    (ha : ∀ i : Nat, 0 < a i)
    (hprec : ∀ i : Nat, Prec (H i) (P i))
    (hpos : ∀ i : Nat, HasPosLeadingCoeff (P i)) :
    ∀ i : Nat, WeightedCompatibleLeft (H i) [(a i, P i)] := fun i =>
  RealRooted.WeightedCompatibleLeft.singleton (ha i) (hprec i) (hpos i)

theorem weightedCompatibleLeft_sequence_cons_zero
    {H P : Nat → ℝ[X]} {a : Nat → ℝ} {L : Nat → List (ℝ × ℝ[X])}
    (ha : ∀ i : Nat, a i = 0)
    (hprec : ∀ i : Nat, Prec (H i) (P i))
    (hpos : ∀ i : Nat, HasPosLeadingCoeff (P i))
    (hl : ∀ i : Nat, WeightedCompatibleLeft (H i) (L i)) :
    ∀ i : Nat, WeightedCompatibleLeft (H i) ((a i, P i) :: L i) := fun i =>
  RealRooted.WeightedCompatibleLeft.cons_zero (ha i) (hprec i) (hpos i) (hl i)

theorem weightedCompatibleLeft_sequence_cons_pos
    {H P : Nat → ℝ[X]} {a : Nat → ℝ} {L : Nat → List (ℝ × ℝ[X])}
    (ha : ∀ i : Nat, 0 < a i)
    (hprec : ∀ i : Nat, Prec (H i) (P i))
    (hpos : ∀ i : Nat, HasPosLeadingCoeff (P i))
    (hl : ∀ i : Nat, WeightedCompatibleLeft (H i) (L i))
    (hne : ∀ i : Nat, C (a i) * P i + weightedSum (L i) ≠ 0)
    (hsplits : ∀ i : Nat, (C (a i) * P i + weightedSum (L i)).Splits)
    (hcop : ∀ i : Nat, IsCoprime (C (a i) * P i) (weightedSum (L i))) :
    ∀ i : Nat, WeightedCompatibleLeft (H i) ((a i, P i) :: L i) := fun i =>
  RealRooted.WeightedCompatibleLeft.cons_pos
    (ha i) (hprec i) (hpos i) (hl i) (hne i) (hsplits i) (hcop i)

theorem weightedCompatibleLeft_sequence_prec
    {H : Nat → ℝ[X]} {L : Nat → List (ℝ × ℝ[X])}
    (hl : ∀ i : Nat, WeightedCompatibleLeft (H i) (L i)) :
    ∀ i : Nat, Prec (H i) (weightedSum (L i)) := fun i =>
  RealRooted.WeightedCompatibleLeft.prec (hl i)

theorem weightedSum_sequence_left_prec
    {H : Nat → ℝ[X]} {L : Nat → List (ℝ × ℝ[X])}
    (hl : ∀ i : Nat, WeightedCompatibleLeft (H i) (L i)) :
    ∀ i : Nat, Prec (H i) (weightedSum (L i)) := fun i =>
  RealRooted.prec_weightedSum_left (hl i)

theorem sum_sequence_left_prec
    {H : Nat → ℝ[X]} {L : Nat → List ℝ[X]}
    (hl : ∀ i : Nat,
      WeightedCompatibleLeft (H i) ((L i).map (fun p => ((1 : ℝ), p)))) :
    ∀ i : Nat, Prec (H i) (L i).sum := fun i =>
  RealRooted.prec_sum_left (hl i)

theorem weightedSum_sequence_right_prec
    {L : Nat → List (ℝ × ℝ[X])} {H : Nat → ℝ[X]}
    (hnonneg : ∀ i : Nat, ∀ ap ∈ L i, 0 ≤ ap.1)
    (hprec : ∀ i : Nat, ∀ ap ∈ L i, Prec ap.2 (H i))
    (hpos : ∀ i : Nat, ∀ ap ∈ L i, HasPosLeadingCoeff ap.2)
    (hex : ∀ i : Nat, ∃ ap ∈ L i, 0 < ap.1) :
    ∀ i : Nat, Prec (weightedSum (L i)) (H i) := fun i =>
  RealRooted.prec_weightedSum_right _ _ (hnonneg i) (hprec i) (hpos i) (hex i)

theorem sum_sequence_right_prec
    {L : Nat → List ℝ[X]} {H : Nat → ℝ[X]}
    (hprec : ∀ i : Nat, ∀ p ∈ L i, Prec p (H i))
    (hpos : ∀ i : Nat, ∀ p ∈ L i, HasPosLeadingCoeff p)
    (hne : ∀ i : Nat, L i ≠ []) :
    ∀ i : Nat, Prec (L i).sum (H i) := fun i =>
  RealRooted.prec_sum_right _ _ (hprec i) (hpos i) (hne i)

syntax (name := rr_weighted_sum_zero_named)
  "rr_weighted_sum_zero" " using " "weights_zero" ":=" term :
  tactic

syntax (name := rr_weighted_sum_sequence_zero_named)
  "rr_weighted_sum_sequence_zero" " using " "weights_zero" ":=" term :
  tactic

syntax (name := rr_weighted_sum_pos_lc_named)
  "rr_weighted_sum_pos_lc" " using "
    "weights_nonneg" ":=" term ","
    "terms_pos_lc" ":=" term ","
    "some_weight_pos" ":=" term :
  tactic

syntax (name := rr_weighted_sum_sequence_pos_lc_named)
  "rr_weighted_sum_sequence_pos_lc" " using "
    "weights_nonneg" ":=" term ","
    "terms_pos_lc" ":=" term ","
    "some_weight_pos" ":=" term :
  tactic

syntax (name := rr_weighted_compatible_left_singleton_named)
  "rr_weighted_compatible_left_singleton" " using "
    "weight_pos" ":=" term ","
    "prec" ":=" term ","
    "pos_lc" ":=" term :
  tactic

syntax (name := rr_weighted_compatible_left_sequence_singleton_named)
  "rr_weighted_compatible_left_sequence_singleton" " using "
    "weight_pos" ":=" term ","
    "prec" ":=" term ","
    "pos_lc" ":=" term :
  tactic

syntax (name := rr_weighted_compatible_left_cons_zero_named)
  "rr_weighted_compatible_left_cons_zero" " using "
    "weight_zero" ":=" term ","
    "prec" ":=" term ","
    "pos_lc" ":=" term ","
    "tail" ":=" term :
  tactic

syntax (name := rr_weighted_compatible_left_sequence_cons_zero_named)
  "rr_weighted_compatible_left_sequence_cons_zero" " using "
    "weight_zero" ":=" term ","
    "prec" ":=" term ","
    "pos_lc" ":=" term ","
    "tail" ":=" term :
  tactic

syntax (name := rr_weighted_compatible_left_cons_pos_named)
  "rr_weighted_compatible_left_cons_pos" " using "
    "weight_pos" ":=" term ","
    "prec" ":=" term ","
    "pos_lc" ":=" term ","
    "tail" ":=" term ","
    "sum_ne" ":=" term ","
    "sum_splits" ":=" term ","
    "coprime" ":=" term :
  tactic

syntax (name := rr_weighted_compatible_left_sequence_cons_pos_named)
  "rr_weighted_compatible_left_sequence_cons_pos" " using "
    "weight_pos" ":=" term ","
    "prec" ":=" term ","
    "pos_lc" ":=" term ","
    "tail" ":=" term ","
    "sum_ne" ":=" term ","
    "sum_splits" ":=" term ","
    "coprime" ":=" term :
  tactic

syntax (name := rr_weighted_compatible_left_prec_named)
  "rr_weighted_compatible_left_prec" " using " "compatible" ":=" term :
  tactic

syntax (name := rr_weighted_compatible_left_sequence_prec_named)
  "rr_weighted_compatible_left_sequence_prec" " using " "compatible" ":=" term :
  tactic

syntax (name := rr_weighted_sum_left_prec_named)
  "rr_weighted_sum_left_prec" " using " "compatible" ":=" term :
  tactic

syntax (name := rr_weighted_sum_sequence_left_prec_named)
  "rr_weighted_sum_sequence_left_prec" " using " "compatible" ":=" term :
  tactic

syntax (name := rr_sum_left_prec_named)
  "rr_sum_left_prec" " using " "compatible" ":=" term :
  tactic

syntax (name := rr_sum_sequence_left_prec_named)
  "rr_sum_sequence_left_prec" " using " "compatible" ":=" term :
  tactic

syntax (name := rr_weighted_sum_right_prec_named)
  "rr_weighted_sum_right_prec" " using "
    "weights_nonneg" ":=" term ","
    "all_prec" ":=" term ","
    "terms_pos_lc" ":=" term ","
    "some_weight_pos" ":=" term :
  tactic

syntax (name := rr_weighted_sum_sequence_right_prec_named)
  "rr_weighted_sum_sequence_right_prec" " using "
    "weights_nonneg" ":=" term ","
    "all_prec" ":=" term ","
    "terms_pos_lc" ":=" term ","
    "some_weight_pos" ":=" term :
  tactic

syntax (name := rr_sum_right_prec_named)
  "rr_sum_right_prec" " using "
    "all_prec" ":=" term ","
    "terms_pos_lc" ":=" term ","
    "nonempty" ":=" term :
  tactic

syntax (name := rr_sum_sequence_right_prec_named)
  "rr_sum_sequence_right_prec" " using "
    "all_prec" ":=" term ","
    "terms_pos_lc" ":=" term ","
    "nonempty" ":=" term :
  tactic

macro_rules
  | `(tactic| rr_weighted_sum_zero using weights_zero := $hzero:term) =>
      `(tactic| exact RealRooted.weightedSum_eq_zero_of_forall_coeff_zero _ $hzero)
  | `(tactic| rr_weighted_sum_sequence_zero using weights_zero := $hzero:term) =>
      `(tactic| exact RealRooted.Tactic.weightedSum_sequence_zero $hzero)
  | `(tactic|
      rr_weighted_sum_pos_lc using
        weights_nonneg := $hnonneg:term,
        terms_pos_lc := $hpos:term,
        some_weight_pos := $hex:term) =>
      `(tactic| exact RealRooted.hasPosLeadingCoeff_weightedSum _ $hnonneg $hpos $hex)
  | `(tactic|
      rr_weighted_sum_sequence_pos_lc using
        weights_nonneg := $hnonneg:term,
        terms_pos_lc := $hpos:term,
        some_weight_pos := $hex:term) =>
      `(tactic| exact RealRooted.Tactic.weightedSum_sequence_pos_lc $hnonneg $hpos $hex)
  | `(tactic|
      rr_weighted_compatible_left_singleton using
        weight_pos := $ha:term,
        prec := $hprec:term,
        pos_lc := $hpos:term) =>
      `(tactic| exact RealRooted.WeightedCompatibleLeft.singleton $ha $hprec $hpos)
  | `(tactic|
      rr_weighted_compatible_left_sequence_singleton using
        weight_pos := $ha:term,
        prec := $hprec:term,
        pos_lc := $hpos:term) =>
      `(tactic|
        exact RealRooted.Tactic.weightedCompatibleLeft_sequence_singleton
          $ha $hprec $hpos)
  | `(tactic|
      rr_weighted_compatible_left_cons_zero using
        weight_zero := $ha:term,
        prec := $hprec:term,
        pos_lc := $hpos:term,
        tail := $hl:term) =>
      `(tactic| exact RealRooted.WeightedCompatibleLeft.cons_zero $ha $hprec $hpos $hl)
  | `(tactic|
      rr_weighted_compatible_left_sequence_cons_zero using
        weight_zero := $ha:term,
        prec := $hprec:term,
        pos_lc := $hpos:term,
        tail := $hl:term) =>
      `(tactic|
        exact RealRooted.Tactic.weightedCompatibleLeft_sequence_cons_zero
          $ha $hprec $hpos $hl)
  | `(tactic|
      rr_weighted_compatible_left_cons_pos using
        weight_pos := $ha:term,
        prec := $hprec:term,
        pos_lc := $hpos:term,
        tail := $hl:term,
        sum_ne := $hne:term,
        sum_splits := $hsplits:term,
        coprime := $hcop:term) =>
      `(tactic|
        exact RealRooted.WeightedCompatibleLeft.cons_pos
          $ha $hprec $hpos $hl $hne $hsplits $hcop)
  | `(tactic|
      rr_weighted_compatible_left_sequence_cons_pos using
        weight_pos := $ha:term,
        prec := $hprec:term,
        pos_lc := $hpos:term,
        tail := $hl:term,
        sum_ne := $hne:term,
        sum_splits := $hsplits:term,
        coprime := $hcop:term) =>
      `(tactic|
        exact RealRooted.Tactic.weightedCompatibleLeft_sequence_cons_pos
          $ha $hprec $hpos $hl $hne $hsplits $hcop)
  | `(tactic| rr_weighted_compatible_left_prec using compatible := $hl:term) =>
      `(tactic| exact RealRooted.WeightedCompatibleLeft.prec $hl)
  | `(tactic| rr_weighted_compatible_left_sequence_prec using compatible := $hl:term) =>
      `(tactic| exact RealRooted.Tactic.weightedCompatibleLeft_sequence_prec $hl)
  | `(tactic| rr_weighted_sum_left_prec using compatible := $hl:term) =>
      `(tactic| exact RealRooted.prec_weightedSum_left $hl)
  | `(tactic| rr_weighted_sum_sequence_left_prec using compatible := $hl:term) =>
      `(tactic| exact RealRooted.Tactic.weightedSum_sequence_left_prec $hl)
  | `(tactic| rr_sum_left_prec using compatible := $hl:term) =>
      `(tactic| exact RealRooted.prec_sum_left $hl)
  | `(tactic| rr_sum_sequence_left_prec using compatible := $hl:term) =>
      `(tactic| exact RealRooted.Tactic.sum_sequence_left_prec $hl)
  | `(tactic|
      rr_weighted_sum_right_prec using
        weights_nonneg := $hnonneg:term,
        all_prec := $hprec:term,
        terms_pos_lc := $hpos:term,
        some_weight_pos := $hex:term) =>
      `(tactic|
        exact RealRooted.prec_weightedSum_right _ _ $hnonneg $hprec $hpos $hex)
  | `(tactic|
      rr_weighted_sum_sequence_right_prec using
        weights_nonneg := $hnonneg:term,
        all_prec := $hprec:term,
        terms_pos_lc := $hpos:term,
        some_weight_pos := $hex:term) =>
      `(tactic|
        exact RealRooted.Tactic.weightedSum_sequence_right_prec
          $hnonneg $hprec $hpos $hex)
  | `(tactic|
      rr_sum_right_prec using
        all_prec := $hprec:term,
        terms_pos_lc := $hpos:term,
        nonempty := $hne:term) =>
      `(tactic| exact RealRooted.prec_sum_right _ _ $hprec $hpos $hne)
  | `(tactic|
      rr_sum_sequence_right_prec using
        all_prec := $hprec:term,
        terms_pos_lc := $hpos:term,
        nonempty := $hne:term) =>
      `(tactic| exact RealRooted.Tactic.sum_sequence_right_prec $hprec $hpos $hne)

end Tactic
end RealRooted
