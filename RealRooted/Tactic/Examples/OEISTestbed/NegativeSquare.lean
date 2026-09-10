import RealRooted.Tactic.LiuWang.SequenceNonpositive

/-!
# OEIS test-bed negative-square examples

Regression examples for negative-square Liu--Wang frontends.
-/

open Polynomial

namespace RealRooted
namespace Tactic

/-! ## Liu--Wang Family G: Narayana/Jacobi negative-square lag factors -/

-- `A001263`: Narayana/Catalan rows, `B_n(t)=-(n/(n+3))(1-t)^2`.
example {n : Nat} {r : ℝ} :
    (-(C ((n : ℝ) / ((n : ℝ) + 3))) * (1 - X) ^ 2 : ℝ[X]).eval r ≤ 0 := by
  rr_sign

-- `A001263`: denominator-fused Narayana lag after the active row shift.
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hraw : ∀ n : Nat,
      C ((n : ℝ) + 5) * P (n + 2) =
        C ((n : ℝ) + 5) * (A n * P (n + 1)) +
          C ((n : ℝ) + 2) * (-((1 - X : ℝ[X]) ^ 2) * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_negative_square_sequence_den_coeff_auto_split using
    base := hbase,
    pos_lc := hpos,
    square_factor := fun _ => 1 - X,
    coeff := fun n => ((n : ℝ) + 2) / ((n : ℝ) + 5),
    raw_coeff := fun n => (n : ℝ) + 2,
    den := fun n => (n : ℝ) + 5,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno

-- `A091044`: Pascal odd-entry triangle, `B_n(t)=-(1-t)^2`.
example {r : ℝ} :
    (-(C (1 : ℝ)) * (1 - X) ^ 2 : ℝ[X]).eval r ≤ 0 := by
  rr_sign

-- `A086645`/`A091042`: expanded `B_n(t)=-1+2t-t^2`.
example {r : ℝ} :
    (C (-1 : ℝ) + C (2 : ℝ) * X + C (-1 : ℝ) * X ^ 2 : ℝ[X]).eval r ≤ 0 := by
  rr_sign

-- `A001263`/`A008459`: scaled expanded `B_n(t)=-c(1-t)^2`.
example {r : ℝ} :
    (C (-2 / 5 : ℝ) + C (4 / 5 : ℝ) * X + C (-2 / 5 : ℝ) * X ^ 2 :
      ℝ[X]).eval r ≤ 0 := by
  rr_sign

-- `A059340`/`A122076`: expanded `B_n(t)=-1-2t-t^2`.
example {r : ℝ} :
    (C (-1 : ℝ) + C (-2 : ℝ) * X + C (-1 : ℝ) * X ^ 2 :
      ℝ[X]).eval r ≤ 0 := by
  rr_sign

-- `A090181`: denominator-fused Narayana variant with half-scaled denominator.
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hraw : ∀ n : Nat,
      C (((n : ℝ) + 4) / 2) * P (n + 2) =
        C (((n : ℝ) + 1) / 2) * (-((1 - X : ℝ[X]) ^ 2) * P n) +
          C (((n : ℝ) + 4) / 2) * (A n * P (n + 1)))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_negative_square_sequence_den_coeff_auto_split using
    base := hbase,
    pos_lc := hpos,
    square_factor := fun _ => 1 - X,
    coeff := fun n => ((n : ℝ) + 1) / ((n : ℝ) + 4),
    raw_coeff := fun n => ((n : ℝ) + 1) / 2,
    den := fun n => ((n : ℝ) + 4) / 2,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno

-- `A145596`: generalized Narayana rows, `B_n(t)=-(n/(n+3))(1-t)^2`.
example {n : Nat} {r : ℝ} :
    (-(C ((n : ℝ) / ((n : ℝ) + 3))) * (1 - X) ^ 2 : ℝ[X]).eval r ≤ 0 := by
  rr_sign

-- `A145596`: denominator-fused generalized Narayana lag.  The active left
-- denominator and raw lag coefficient are both negative.
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hraw : ∀ n : Nat,
      C (-(((n : ℝ) + 5) * ((n : ℝ) + 1) / 3)) * P (n + 2) =
        C (-(((n : ℝ) + 5) * ((n : ℝ) + 1) / 3)) * (A n * P (n + 1)) +
          C (-(((n : ℝ) + 2) * ((n : ℝ) + 1) / 3)) *
            (-((1 - X : ℝ[X]) ^ 2) * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_negative_square_sequence_den_coeff_auto_split using
    base := hbase,
    pos_lc := hpos,
    square_factor := fun _ => 1 - X,
    coeff := fun n => ((n : ℝ) + 2) / ((n : ℝ) + 5),
    raw_coeff := fun n => -(((n : ℝ) + 2) * ((n : ℝ) + 1) / 3),
    den := fun n => -(((n : ℝ) + 5) * ((n : ℝ) + 1) / 3),
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno

-- `A178343`: beta-binomial rows, `B_n(t)=-(n/(n-1))(1-t)^2`, active for `n>=2`.
example {n : Nat} (hn : 2 ≤ n) {r : ℝ} :
    (-(C ((n : ℝ) / ((n : ℝ) - 1))) * (1 - X) ^ 2 : ℝ[X]).eval r ≤ 0 := by
  rr_sign

-- `A178343`: denominator-fused beta-binomial lag after the active row shift.
example {P : Nat → ℝ[X]} {A : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hraw : ∀ n : Nat,
      C (((n : ℝ) + 1) ^ 2) * P (n + 2) =
        C (((n : ℝ) + 1) ^ 2) * (A n * P (n + 1)) +
          C (((n : ℝ) + 2) * ((n : ℝ) + 1)) *
            (-((1 - X : ℝ[X]) ^ 2) * P n))
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_negative_square_sequence_den_coeff_realrooted_auto_split using
    base := hbase,
    pos_lc := hpos,
    square_factor := fun _ => 1 - X,
    coeff := fun n => ((n : ℝ) + 2) / ((n : ℝ) + 1),
    raw_coeff := fun n => ((n : ℝ) + 2) * ((n : ℝ) + 1),
    den := fun n => ((n : ℝ) + 1) ^ 2,
    raw_recurrence := hraw,
    degree_succ := hdeg_succ,
    no_common_roots := hno


end Tactic
end RealRooted
