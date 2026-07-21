import RealRooted.Tactic.WeightedSum

open Polynomial

namespace RealRooted
namespace Tactic

example {l : List (ℝ × ℝ[X])} (hzero : ∀ ap ∈ l, ap.1 = 0) :
    weightedSum l = 0 := by
  rr_weighted_sum_zero using weights_zero := hzero

example {L : Nat → List (ℝ × ℝ[X])}
    (hzero : ∀ i : Nat, ∀ ap ∈ L i, ap.1 = 0) :
    ∀ i : Nat, weightedSum (L i) = 0 := by
  rr_weighted_sum_sequence_zero using weights_zero := hzero

example {l : List (ℝ × ℝ[X])}
    (hnonneg : ∀ ap ∈ l, 0 ≤ ap.1)
    (hpos : ∀ ap ∈ l, HasPosLeadingCoeff ap.2)
    (hex : ∃ ap ∈ l, 0 < ap.1) :
    HasPosLeadingCoeff (weightedSum l) := by
  rr_weighted_sum_pos_lc using
    weights_nonneg := hnonneg,
    terms_pos_lc := hpos,
    some_weight_pos := hex

example {L : Nat → List (ℝ × ℝ[X])}
    (hnonneg : ∀ i : Nat, ∀ ap ∈ L i, 0 ≤ ap.1)
    (hpos : ∀ i : Nat, ∀ ap ∈ L i, HasPosLeadingCoeff ap.2)
    (hex : ∀ i : Nat, ∃ ap ∈ L i, 0 < ap.1) :
    ∀ i : Nat, HasPosLeadingCoeff (weightedSum (L i)) := by
  rr_weighted_sum_sequence_pos_lc using
    weights_nonneg := hnonneg,
    terms_pos_lc := hpos,
    some_weight_pos := hex

example {h p : ℝ[X]} {a : ℝ}
    (ha : 0 < a) (hprec : Prec h p) (hpos : HasPosLeadingCoeff p) :
    WeightedCompatibleLeft h [(a, p)] := by
  rr_weighted_compatible_left_singleton using
    weight_pos := ha,
    prec := hprec,
    pos_lc := hpos

example {H P : Nat → ℝ[X]} {a : Nat → ℝ}
    (ha : ∀ i : Nat, 0 < a i)
    (hprec : ∀ i : Nat, Prec (H i) (P i))
    (hpos : ∀ i : Nat, HasPosLeadingCoeff (P i)) :
    ∀ i : Nat, WeightedCompatibleLeft (H i) [(a i, P i)] := by
  rr_weighted_compatible_left_sequence_singleton using
    weight_pos := ha,
    prec := hprec,
    pos_lc := hpos

example {h p : ℝ[X]} {a : ℝ} {l : List (ℝ × ℝ[X])}
    (ha : a = 0) (hprec : Prec h p) (hpos : HasPosLeadingCoeff p)
    (hl : WeightedCompatibleLeft h l) :
    WeightedCompatibleLeft h ((a, p) :: l) := by
  rr_weighted_compatible_left_cons_zero using
    weight_zero := ha,
    prec := hprec,
    pos_lc := hpos,
    tail := hl

example {H P : Nat → ℝ[X]} {a : Nat → ℝ} {L : Nat → List (ℝ × ℝ[X])}
    (ha : ∀ i : Nat, a i = 0)
    (hprec : ∀ i : Nat, Prec (H i) (P i))
    (hpos : ∀ i : Nat, HasPosLeadingCoeff (P i))
    (hl : ∀ i : Nat, WeightedCompatibleLeft (H i) (L i)) :
    ∀ i : Nat, WeightedCompatibleLeft (H i) ((a i, P i) :: L i) := by
  rr_weighted_compatible_left_sequence_cons_zero using
    weight_zero := ha,
    prec := hprec,
    pos_lc := hpos,
    tail := hl

example {h p : ℝ[X]} {a : ℝ} {l : List (ℝ × ℝ[X])}
    (ha : 0 < a) (hprec : Prec h p) (hpos : HasPosLeadingCoeff p)
    (hl : WeightedCompatibleLeft h l)
    (hne : C a * p + weightedSum l ≠ 0)
    (hsplits : (C a * p + weightedSum l).Splits)
    (hcop : IsCoprime (C a * p) (weightedSum l)) :
    WeightedCompatibleLeft h ((a, p) :: l) := by
  rr_weighted_compatible_left_cons_pos using
    weight_pos := ha,
    prec := hprec,
    pos_lc := hpos,
    tail := hl,
    sum_ne := hne,
    sum_splits := hsplits,
    coprime := hcop

example {H P : Nat → ℝ[X]} {a : Nat → ℝ} {L : Nat → List (ℝ × ℝ[X])}
    (ha : ∀ i : Nat, 0 < a i)
    (hprec : ∀ i : Nat, Prec (H i) (P i))
    (hpos : ∀ i : Nat, HasPosLeadingCoeff (P i))
    (hl : ∀ i : Nat, WeightedCompatibleLeft (H i) (L i))
    (hne : ∀ i : Nat, C (a i) * P i + weightedSum (L i) ≠ 0)
    (hsplits : ∀ i : Nat, (C (a i) * P i + weightedSum (L i)).Splits)
    (hcop : ∀ i : Nat, IsCoprime (C (a i) * P i) (weightedSum (L i))) :
    ∀ i : Nat, WeightedCompatibleLeft (H i) ((a i, P i) :: L i) := by
  rr_weighted_compatible_left_sequence_cons_pos using
    weight_pos := ha,
    prec := hprec,
    pos_lc := hpos,
    tail := hl,
    sum_ne := hne,
    sum_splits := hsplits,
    coprime := hcop

example {h : ℝ[X]} {l : List (ℝ × ℝ[X])}
    (hl : WeightedCompatibleLeft h l) :
    Prec h (weightedSum l) := by
  rr_weighted_compatible_left_prec using compatible := hl

example {H : Nat → ℝ[X]} {L : Nat → List (ℝ × ℝ[X])}
    (hl : ∀ i : Nat, WeightedCompatibleLeft (H i) (L i)) :
    ∀ i : Nat, Prec (H i) (weightedSum (L i)) := by
  rr_weighted_compatible_left_sequence_prec using compatible := hl

example {h : ℝ[X]} {l : List (ℝ × ℝ[X])}
    (hl : WeightedCompatibleLeft h l) :
    Prec h (weightedSum l) := by
  rr_weighted_sum_left_prec using compatible := hl

example {H : Nat → ℝ[X]} {L : Nat → List (ℝ × ℝ[X])}
    (hl : ∀ i : Nat, WeightedCompatibleLeft (H i) (L i)) :
    ∀ i : Nat, Prec (H i) (weightedSum (L i)) := by
  rr_weighted_sum_sequence_left_prec using compatible := hl

example {h : ℝ[X]} {l : List ℝ[X]}
    (hl : WeightedCompatibleLeft h (l.map (fun p => ((1 : ℝ), p)))) :
    Prec h l.sum := by
  rr_sum_left_prec using compatible := hl

example {H : Nat → ℝ[X]} {L : Nat → List ℝ[X]}
    (hl : ∀ i : Nat,
      WeightedCompatibleLeft (H i) ((L i).map (fun p => ((1 : ℝ), p)))) :
    ∀ i : Nat, Prec (H i) (L i).sum := by
  rr_sum_sequence_left_prec using compatible := hl

example {l : List (ℝ × ℝ[X])} {h : ℝ[X]}
    (hnonneg : ∀ ap ∈ l, 0 ≤ ap.1)
    (hprec : ∀ ap ∈ l, Prec ap.2 h)
    (hpos : ∀ ap ∈ l, HasPosLeadingCoeff ap.2)
    (hex : ∃ ap ∈ l, 0 < ap.1) :
    Prec (weightedSum l) h := by
  rr_weighted_sum_right_prec using
    weights_nonneg := hnonneg,
    all_prec := hprec,
    terms_pos_lc := hpos,
    some_weight_pos := hex

example {L : Nat → List (ℝ × ℝ[X])} {H : Nat → ℝ[X]}
    (hnonneg : ∀ i : Nat, ∀ ap ∈ L i, 0 ≤ ap.1)
    (hprec : ∀ i : Nat, ∀ ap ∈ L i, Prec ap.2 (H i))
    (hpos : ∀ i : Nat, ∀ ap ∈ L i, HasPosLeadingCoeff ap.2)
    (hex : ∀ i : Nat, ∃ ap ∈ L i, 0 < ap.1) :
    ∀ i : Nat, Prec (weightedSum (L i)) (H i) := by
  rr_weighted_sum_sequence_right_prec using
    weights_nonneg := hnonneg,
    all_prec := hprec,
    terms_pos_lc := hpos,
    some_weight_pos := hex

example {l : List ℝ[X]} {h : ℝ[X]}
    (hprec : ∀ p ∈ l, Prec p h)
    (hpos : ∀ p ∈ l, HasPosLeadingCoeff p)
    (hne : l ≠ []) :
    Prec l.sum h := by
  rr_sum_right_prec using
    all_prec := hprec,
    terms_pos_lc := hpos,
    nonempty := hne

example {L : Nat → List ℝ[X]} {H : Nat → ℝ[X]}
    (hprec : ∀ i : Nat, ∀ p ∈ L i, Prec p (H i))
    (hpos : ∀ i : Nat, ∀ p ∈ L i, HasPosLeadingCoeff p)
    (hne : ∀ i : Nat, L i ≠ []) :
    ∀ i : Nat, Prec (L i).sum (H i) := by
  rr_sum_sequence_right_prec using
    all_prec := hprec,
    terms_pos_lc := hpos,
    nonempty := hne

end Tactic
end RealRooted
