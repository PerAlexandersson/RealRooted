import RealRooted.Tactic.SecondDerivative

/-!
# OEIS LS4 second-derivative regression examples

Executable second-derivative factorization tests extracted from the OEIS
recurrence test bed.
-/

open Polynomial

namespace RealRooted
namespace Tactic

/-! ## LS4 second-derivative factorization shells -/

-- `A271703`: unsigned Lah shape
-- `P_{n+2}=X f+2X f'+X f''=(1+D)((X-1)f+Xf')`.
example {P : Nat → ℝ[X]}
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroots_nonpos : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 0)
    (hinner_pos : ∀ n : Nat,
      HasPosLeadingCoeff
        ((X - C (1 : ℝ)) * P (n + 1) + X * (P (n + 1)).derivative))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        X * P (n + 1) +
          (C (2 : ℝ) * X) * (P (n + 1)).derivative +
            X * (P (n + 1)).derivative.derivative)
    (hinner_deg_lo : ∀ n : Nat,
      (P (n + 1)).natDegree ≤
        ((X - C (1 : ℝ)) * P (n + 1) + X * (P (n + 1)).derivative).natDegree)
    (hinner_deg_hi : ∀ n : Nat,
      ((X - C (1 : ℝ)) * P (n + 1) + X * (P (n + 1)).derivative).natDegree ≤
        (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_plus_derivative_sequence_expanded_auto using
    outer := fun _ => (1 : ℝ),
    base_zero := hbase_zero,
    base_one := hbase_one,
    pos_lc := hpos,
    degree_two := hdeg_two,
    inner_pos_lc := hinner_pos,
    root_nonpos := hroots_nonpos,
    recurrence := hrec,
    inner_degree_lower := hinner_deg_lo,
    inner_degree_upper := hinner_deg_hi

-- `A271704`/`A271705`: unsigned Lah LS4 shell plus the current row
-- `(1+X)f+2Xf'+Xf''=f+(1+D)((X-1)f+Xf')`.
example {P : Nat → ℝ[X]}
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (houter_pos : ∀ n : Nat,
      HasPosLeadingCoeff
        (C (1 : ℝ) *
            ((X - C (1 : ℝ)) * P (n + 1) + X * (P (n + 1)).derivative) +
          ((X - C (1 : ℝ)) * P (n + 1) +
            X * (P (n + 1)).derivative).derivative))
    (houter_prec : ∀ n : Nat,
      Prec (P (n + 1))
        (C (1 : ℝ) *
            ((X - C (1 : ℝ)) * P (n + 1) + X * (P (n + 1)).derivative) +
          ((X - C (1 : ℝ)) * P (n + 1) +
            X * (P (n + 1)).derivative).derivative))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        (1 + X : ℝ[X]) * P (n + 1) +
          (C (2 : ℝ) * X) * (P (n + 1)).derivative +
            X * (P (n + 1)).derivative.derivative) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_ls4_plus_current_sequence_expanded_auto using
    outer := fun _ => (1 : ℝ),
    tail := fun _ => (1 : ℝ),
    base_zero := hbase_zero,
    base_one := hbase_one,
    pos_lc := hpos,
    outer_pos_lc := houter_pos,
    outer_prec := houter_prec,
    recurrence := hrec

-- `A105278`: Lah-type row
-- `P_{n+2}=(2+X)f+(2+2X)f'+Xf''=(1+D)((X+1)f+Xf')`.
example {P : Nat → ℝ[X]}
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroots_nonpos : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 0)
    (hinner_pos : ∀ n : Nat,
      HasPosLeadingCoeff
        ((X + C (1 : ℝ)) * P (n + 1) + X * (P (n + 1)).derivative))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        (C (2 : ℝ) + X) * P (n + 1) +
          (C (2 : ℝ) + C (2 : ℝ) * X) * (P (n + 1)).derivative +
            X * (P (n + 1)).derivative.derivative)
    (hinner_deg_lo : ∀ n : Nat,
      (P (n + 1)).natDegree ≤
        ((X + C (1 : ℝ)) * P (n + 1) + X * (P (n + 1)).derivative).natDegree)
    (hinner_deg_hi : ∀ n : Nat,
      ((X + C (1 : ℝ)) * P (n + 1) + X * (P (n + 1)).derivative).natDegree ≤
        (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_plus_derivative_sequence_expanded_auto using
    outer := fun _ => (1 : ℝ),
    base_zero := hbase_zero,
    base_one := hbase_one,
    pos_lc := hpos,
    degree_two := hdeg_two,
    inner_pos_lc := hinner_pos,
    root_nonpos := hroots_nonpos,
    recurrence := hrec,
    inner_degree_lower := hinner_deg_lo,
    inner_degree_upper := hinner_deg_hi

-- `A079640`: Stirling-first/Lah product, LS4 shell plus an indexed current row
-- `(n+3+X)f+(2+2X)f'+Xf''=(n+1)f+(1+D)((X+1)f+Xf')`.
example {P : Nat → ℝ[X]}
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (houter_pos : ∀ n : Nat,
      HasPosLeadingCoeff
        (C (1 : ℝ) *
            ((X + C (1 : ℝ)) * P (n + 1) + X * (P (n + 1)).derivative) +
          ((X + C (1 : ℝ)) * P (n + 1) +
            X * (P (n + 1)).derivative).derivative))
    (houter_prec : ∀ n : Nat,
      Prec (P (n + 1))
        (C (1 : ℝ) *
            ((X + C (1 : ℝ)) * P (n + 1) + X * (P (n + 1)).derivative) +
          ((X + C (1 : ℝ)) * P (n + 1) +
            X * (P (n + 1)).derivative).derivative))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        (C ((n : ℝ) + 3) + X) * P (n + 1) +
          (C (2 : ℝ) + C (2 : ℝ) * X) * (P (n + 1)).derivative +
            X * (P (n + 1)).derivative.derivative) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_ls4_plus_current_sequence_expanded_auto using
    outer := fun _ => (1 : ℝ),
    tail := fun n => (n : ℝ) + 1,
    base_zero := hbase_zero,
    base_one := hbase_one,
    pos_lc := hpos,
    outer_pos_lc := houter_pos,
    outer_prec := houter_prec,
    recurrence := hrec

-- `A048854`: generalized Lah `L[4,1]`
-- `(2+X)f+(8+8X)f'+16Xf''=(1/4+D)(4(X-2)f+16Xf')`.
example {P : Nat → ℝ[X]}
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroots_nonpos : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 0)
    (hinner_pos : ∀ n : Nat,
      HasPosLeadingCoeff
        ((C (4 : ℝ) * (X - C (2 : ℝ))) * P (n + 1) +
          (C (16 : ℝ) * X) * (P (n + 1)).derivative))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        (C (2 : ℝ) + X) * P (n + 1) +
          (C (8 : ℝ) + C (8 : ℝ) * X) * (P (n + 1)).derivative +
            (C (16 : ℝ) * X) * (P (n + 1)).derivative.derivative)
    (hinner_deg_lo : ∀ n : Nat,
      (P (n + 1)).natDegree ≤
        ((C (4 : ℝ) * (X - C (2 : ℝ))) * P (n + 1) +
          (C (16 : ℝ) * X) * (P (n + 1)).derivative).natDegree)
    (hinner_deg_hi : ∀ n : Nat,
      ((C (4 : ℝ) * (X - C (2 : ℝ))) * P (n + 1) +
          (C (16 : ℝ) * X) * (P (n + 1)).derivative).natDegree ≤
        (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_plus_derivative_sequence_expanded_auto using
    outer := fun _ => ((1 : ℝ) / 4),
    base_zero := hbase_zero,
    base_one := hbase_one,
    pos_lc := hpos,
    degree_two := hdeg_two,
    inner_pos_lc := hinner_pos,
    root_nonpos := hroots_nonpos,
    recurrence := hrec,
    inner_degree_lower := hinner_deg_lo,
    inner_degree_upper := hinner_deg_hi

-- `A088729`: doubled derivative branch
-- `(3+X)f+(4+3X)f'+2Xf''=(1+D)((X+2)f+2Xf')`.
example {P : Nat → ℝ[X]}
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroots_nonpos : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 0)
    (hinner_pos : ∀ n : Nat,
      HasPosLeadingCoeff
        ((X + C (2 : ℝ)) * P (n + 1) +
          (C (2 : ℝ) * X) * (P (n + 1)).derivative))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        (X + C (3 : ℝ)) * P (n + 1) +
          (C (4 : ℝ) + C (3 : ℝ) * X) * (P (n + 1)).derivative +
            (C (2 : ℝ) * X) * (P (n + 1)).derivative.derivative)
    (hinner_deg_lo : ∀ n : Nat,
      (P (n + 1)).natDegree ≤
        ((X + C (2 : ℝ)) * P (n + 1) +
          (C (2 : ℝ) * X) * (P (n + 1)).derivative).natDegree)
    (hinner_deg_hi : ∀ n : Nat,
      ((X + C (2 : ℝ)) * P (n + 1) +
          (C (2 : ℝ) * X) * (P (n + 1)).derivative).natDegree ≤
        (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_plus_derivative_sequence_expanded_auto using
    outer := fun _ => (1 : ℝ),
    base_zero := hbase_zero,
    base_one := hbase_one,
    pos_lc := hpos,
    degree_two := hdeg_two,
    inner_pos_lc := hinner_pos,
    root_nonpos := hroots_nonpos,
    recurrence := hrec,
    inner_degree_lower := hinner_deg_lo,
    inner_degree_upper := hinner_deg_hi

-- `A286724`: half-step Lah branch
-- `(2+X)f+(4+4X)f'+4Xf''=(1/2+D)(2Xf+4Xf')`.
example {P : Nat → ℝ[X]}
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroots_nonpos : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 0)
    (hinner_pos : ∀ n : Nat,
      HasPosLeadingCoeff
        ((C (2 : ℝ) * X) * P (n + 1) +
          (C (4 : ℝ) * X) * (P (n + 1)).derivative))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        (X + C (2 : ℝ)) * P (n + 1) +
          (C (4 : ℝ) + C (4 : ℝ) * X) * (P (n + 1)).derivative +
            (C (4 : ℝ) * X) * (P (n + 1)).derivative.derivative)
    (hinner_deg_lo : ∀ n : Nat,
      (P (n + 1)).natDegree ≤
        ((C (2 : ℝ) * X) * P (n + 1) +
          (C (4 : ℝ) * X) * (P (n + 1)).derivative).natDegree)
    (hinner_deg_hi : ∀ n : Nat,
      ((C (2 : ℝ) * X) * P (n + 1) +
          (C (4 : ℝ) * X) * (P (n + 1)).derivative).natDegree ≤
        (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_plus_derivative_sequence_expanded_auto using
    outer := fun _ => ((1 : ℝ) / 2),
    base_zero := hbase_zero,
    base_one := hbase_one,
    pos_lc := hpos,
    degree_two := hdeg_two,
    inner_pos_lc := hinner_pos,
    root_nonpos := hroots_nonpos,
    recurrence := hrec,
    inner_degree_lower := hinner_deg_lo,
    inner_degree_upper := hinner_deg_hi

-- `A290596`: third-step Lah branch with translated inner factor
-- `(2+X)f+(6+6X)f'+9Xf''=(1/3+D)(3(X-1)f+9Xf')`.
example {P : Nat → ℝ[X]}
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroots_nonpos : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 0)
    (hinner_pos : ∀ n : Nat,
      HasPosLeadingCoeff
        ((C (3 : ℝ) * (X - C (1 : ℝ))) * P (n + 1) +
          (C (9 : ℝ) * X) * (P (n + 1)).derivative))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        (X + C (2 : ℝ)) * P (n + 1) +
          (C (6 : ℝ) + C (6 : ℝ) * X) * (P (n + 1)).derivative +
            (C (9 : ℝ) * X) * (P (n + 1)).derivative.derivative)
    (hinner_deg_lo : ∀ n : Nat,
      (P (n + 1)).natDegree ≤
        ((C (3 : ℝ) * (X - C (1 : ℝ))) * P (n + 1) +
          (C (9 : ℝ) * X) * (P (n + 1)).derivative).natDegree)
    (hinner_deg_hi : ∀ n : Nat,
      ((C (3 : ℝ) * (X - C (1 : ℝ))) * P (n + 1) +
          (C (9 : ℝ) * X) * (P (n + 1)).derivative).natDegree ≤
        (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_plus_derivative_sequence_expanded_auto using
    outer := fun _ => ((1 : ℝ) / 3),
    base_zero := hbase_zero,
    base_one := hbase_one,
    pos_lc := hpos,
    degree_two := hdeg_two,
    inner_pos_lc := hinner_pos,
    root_nonpos := hroots_nonpos,
    recurrence := hrec,
    inner_degree_lower := hinner_deg_lo,
    inner_degree_upper := hinner_deg_hi

-- `A290598`: third-step Lah branch with positive translated inner factor
-- `(4+X)f+(12+6X)f'+9Xf''=(1/3+D)(3(X+1)f+9Xf')`.
example {P : Nat → ℝ[X]}
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroots_nonpos : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 0)
    (hinner_pos : ∀ n : Nat,
      HasPosLeadingCoeff
        ((C (3 : ℝ) * (X + C (1 : ℝ))) * P (n + 1) +
          (C (9 : ℝ) * X) * (P (n + 1)).derivative))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        (X + C (4 : ℝ)) * P (n + 1) +
          (C (12 : ℝ) + C (6 : ℝ) * X) * (P (n + 1)).derivative +
            (C (9 : ℝ) * X) * (P (n + 1)).derivative.derivative)
    (hinner_deg_lo : ∀ n : Nat,
      (P (n + 1)).natDegree ≤
        ((C (3 : ℝ) * (X + C (1 : ℝ))) * P (n + 1) +
          (C (9 : ℝ) * X) * (P (n + 1)).derivative).natDegree)
    (hinner_deg_hi : ∀ n : Nat,
      ((C (3 : ℝ) * (X + C (1 : ℝ))) * P (n + 1) +
          (C (9 : ℝ) * X) * (P (n + 1)).derivative).natDegree ≤
        (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_plus_derivative_sequence_expanded_auto using
    outer := fun _ => ((1 : ℝ) / 3),
    base_zero := hbase_zero,
    base_one := hbase_one,
    pos_lc := hpos,
    degree_two := hdeg_two,
    inner_pos_lc := hinner_pos,
    root_nonpos := hroots_nonpos,
    recurrence := hrec,
    inner_degree_lower := hinner_deg_lo,
    inner_degree_upper := hinner_deg_hi

-- `A292219`: fourth-step Lah branch
-- `(6+X)f+(24+8X)f'+16Xf''=(1/4+D)(4(X+2)f+16Xf')`.
example {P : Nat → ℝ[X]}
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroots_nonpos : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ 0)
    (hinner_pos : ∀ n : Nat,
      HasPosLeadingCoeff
        ((C (4 : ℝ) * (X + C (2 : ℝ))) * P (n + 1) +
          (C (16 : ℝ) * X) * (P (n + 1)).derivative))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        (X + C (6 : ℝ)) * P (n + 1) +
          (C (24 : ℝ) + C (8 : ℝ) * X) * (P (n + 1)).derivative +
            (C (16 : ℝ) * X) * (P (n + 1)).derivative.derivative)
    (hinner_deg_lo : ∀ n : Nat,
      (P (n + 1)).natDegree ≤
        ((C (4 : ℝ) * (X + C (2 : ℝ))) * P (n + 1) +
          (C (16 : ℝ) * X) * (P (n + 1)).derivative).natDegree)
    (hinner_deg_hi : ∀ n : Nat,
      ((C (4 : ℝ) * (X + C (2 : ℝ))) * P (n + 1) +
          (C (16 : ℝ) * X) * (P (n + 1)).derivative).natDegree ≤
        (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_plus_derivative_sequence_expanded_auto using
    outer := fun _ => ((1 : ℝ) / 4),
    base_zero := hbase_zero,
    base_one := hbase_one,
    pos_lc := hpos,
    degree_two := hdeg_two,
    inner_pos_lc := hinner_pos,
    root_nonpos := hroots_nonpos,
    recurrence := hrec,
    inner_degree_lower := hinner_deg_lo,
    inner_degree_upper := hinner_deg_hi

-- `A059110`: shifted Lah window
-- `(1+X)f+(2+2X)f'+(1+X)f''=(1+D)(Xf+(1+X)f')`.
example {P : Nat → ℝ[X]}
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroots_le_neg_one : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -1)
    (hinner_pos : ∀ n : Nat,
      HasPosLeadingCoeff
        (X * P (n + 1) + (1 + X : ℝ[X]) * (P (n + 1)).derivative))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        (1 + X : ℝ[X]) * P (n + 1) +
          (C (2 : ℝ) + C (2 : ℝ) * X) * (P (n + 1)).derivative +
            (1 + X : ℝ[X]) * (P (n + 1)).derivative.derivative)
    (hinner_deg_lo : ∀ n : Nat,
      (P (n + 1)).natDegree ≤
        (X * P (n + 1) + (1 + X : ℝ[X]) * (P (n + 1)).derivative).natDegree)
    (hinner_deg_hi : ∀ n : Nat,
      (X * P (n + 1) + (1 + X : ℝ[X]) * (P (n + 1)).derivative).natDegree ≤
        (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_mw_plus_derivative_sequence_expanded_auto using
    outer := fun _ => (1 : ℝ),
    base_zero := hbase_zero,
    base_one := hbase_one,
    pos_lc := hpos,
    degree_two := hdeg_two,
    inner_pos_lc := hinner_pos,
    root_upper := hroots_le_neg_one,
    recurrence := hrec,
    inner_degree_lower := hinner_deg_lo,
    inner_degree_upper := hinner_deg_hi

-- `A111596`: inverse-Lah stage recurrence
-- `Xf-2Xf'+Xf''=(-1+D)(-(X+1)f+Xf')`.
example {P : Nat → ℝ[X]}
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroots_nonneg : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ r)
    (hinner_neg : ∀ n : Nat,
      HasPosLeadingCoeff
        (-((-(X + C (1 : ℝ))) * P (n + 1) + X * (P (n + 1)).derivative)))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        X * P (n + 1) -
          (C (2 : ℝ) * X) * (P (n + 1)).derivative +
            X * (P (n + 1)).derivative.derivative)
    (hinner_deg_lo : ∀ n : Nat,
      (P (n + 1)).natDegree ≤
        ((-(X + C (1 : ℝ))) * P (n + 1) + X * (P (n + 1)).derivative).natDegree)
    (hinner_deg_hi : ∀ n : Nat,
      ((-(X + C (1 : ℝ))) * P (n + 1) + X * (P (n + 1)).derivative).natDegree ≤
        (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_neg_mw_plus_derivative_sequence_expanded_auto using
    outer := fun _ => (-1 : ℝ),
    base_zero := hbase_zero,
    base_one := hbase_one,
    pos_lc := hpos,
    degree_two := hdeg_two,
    inner_neg_lc := hinner_neg,
    root_nonneg := hroots_nonneg,
    recurrence := hrec,
    inner_degree_lower := hinner_deg_lo,
    inner_degree_upper := hinner_deg_hi

-- `A176231`: even Hermite coefficient triangle
-- `(X-1)f+(2-4X)f'+4Xf''=(-1/2+D)(-2(X+1)f+4Xf')`.
example {P : Nat → ℝ[X]}
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hroots_nonneg : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ r)
    (hinner_neg : ∀ n : Nat,
      HasPosLeadingCoeff
        (-((-(C (2 : ℝ) * (X + C (1 : ℝ)))) * P (n + 1) +
          (C (4 : ℝ) * X) * (P (n + 1)).derivative)))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        (X - C (1 : ℝ)) * P (n + 1) +
          (C (2 : ℝ) - C (4 : ℝ) * X) * (P (n + 1)).derivative +
            (C (4 : ℝ) * X) * (P (n + 1)).derivative.derivative)
    (hinner_deg_lo : ∀ n : Nat,
      (P (n + 1)).natDegree ≤
        ((-(C (2 : ℝ) * (X + C (1 : ℝ)))) * P (n + 1) +
          (C (4 : ℝ) * X) * (P (n + 1)).derivative).natDegree)
    (hinner_deg_hi : ∀ n : Nat,
      ((-(C (2 : ℝ) * (X + C (1 : ℝ)))) * P (n + 1) +
          (C (4 : ℝ) * X) * (P (n + 1)).derivative).natDegree ≤
        (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_neg_mw_plus_derivative_sequence_expanded_auto using
    outer := fun _ => (-(1 : ℝ) / 2),
    base_zero := hbase_zero,
    base_one := hbase_one,
    pos_lc := hpos,
    degree_two := hdeg_two,
    inner_neg_lc := hinner_neg,
    root_nonneg := hroots_nonneg,
    recurrence := hrec,
    inner_degree_lower := hinner_deg_lo,
    inner_degree_upper := hinner_deg_hi

end Tactic
end RealRooted
