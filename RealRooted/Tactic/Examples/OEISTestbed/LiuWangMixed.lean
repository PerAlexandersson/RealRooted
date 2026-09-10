import RealRooted.Tactic.LiuWang.SequenceNonpositive
import RealRooted.Tactic.LiuWang.SequenceProducts

/-!
# OEIS test-bed mixed Liu--Wang examples

Regression examples for mixed Liu--Wang sequence frontends.
-/

open Polynomial

namespace RealRooted
namespace Tactic

/-! ## Liu--Wang Family E: positive `t`-lag factors -/

-- `A049403`: `B_n(t)=(n-1)t`.
example {n : Nat} (hn : 1 ≤ n) {r : ℝ} (hr : r ≤ 0) :
    (C ((n : ℝ) - 1) * X : ℝ[X]).eval r ≤ 0 := by
  rr_sign

-- `A049403`: root-sign package with the active-range scalar certificate.
example {p : ℝ[X]} (hrr : p ≠ 0 ∧ p.Splits) (hpnn : HasNonnegCoeffs p)
    {n : Nat} (hn : 1 ≤ n) :
    ∀ r, p.IsRoot r → (C ((n : ℝ) - 1) * X : ℝ[X]).eval r ≤ 0 := by
  rr_sign_at_roots using hrr, hpnn

-- `A061896`: Lucas-polynomial coefficient triangle, `B_n(t)=t`.
example {r : ℝ} (hr : r ≤ 0) :
    (C (1 : ℝ) * X : ℝ[X]).eval r ≤ 0 := by
  rr_sign

-- `A100862`: matching polynomial triangle, `B_n(t)=(n-2)t`.
example {n : Nat} (hn : 2 ≤ n) {r : ℝ} (hr : r ≤ 0) :
    (C ((n : ℝ) - 2) * X : ℝ[X]).eval r ≤ 0 := by
  rr_sign

-- `A154227`: triangular-number lag coefficient, `B_n(t)=n(n+1)t/2`.
example {n : Nat} {r : ℝ} (hr : r ≤ 0) :
    (C (((n : ℝ) * ((n : ℝ) + 1)) / 2) * X : ℝ[X]).eval r ≤ 0 := by
  rr_sign

-- `A154228`: square-pyramidal lag coefficient, `B_n(t)=n(n+1)(2n+1)t/6`.
example {n : Nat} {r : ℝ} (hr : r ≤ 0) :
    (C (((n : ℝ) * ((n : ℝ) + 1) * (2 * (n : ℝ) + 1)) / 6) * X :
      ℝ[X]).eval r ≤ 0 := by
  rr_sign

-- `A249248`: shifted positive lag coefficient, `B_n(t)=(n+2)t`.
example {n : Nat} {r : ℝ} (hr : r ≤ 0) :
    (C ((n : ℝ) + 2) * X : ℝ[X]).eval r ≤ 0 := by
  rr_sign

-- `A154986`: active coefficient `(m-1)(m-2)t`, after the row shift.
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        (1 + X : ℝ[X]) * P (n + 1) +
          (C (((n : ℝ) + 2) ^ 2 - 3 * ((n : ℝ) + 2) + 2) * X) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_current_one_add_X_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    nonneg_coeffs := hnonneg,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

-- `A334823`: `P_m=(1+2m)P_{m-1}-t^2P_{m-2}`.
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        C (1 + 2 * ((n : ℝ) + 2)) * P (n + 1) +
          (-(C (1 : ℝ)) * X ^ 2) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  rr_lw_negative_square_sequence_auto using
    base := hbase,
    pos_lc := hpos,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno

-- `A334824`: same negative-square lag with current factor `3+2m`.
example {P : Nat → ℝ[X]}
    (hbase : Prec (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        C (3 + 2 * ((n : ℝ) + 2)) * P (n + 1) +
          (-(C (1 : ℝ)) * X ^ 2) * P n)
    (hdeg_succ : ∀ n : Nat, (P n).natDegree + 1 = (P (n + 1)).natDegree)
    (hno : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → ¬ (P n).IsRoot r) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_lw_negative_square_sequence_realrooted_auto using
    base := hbase,
    pos_lc := hpos,
    recurrence := hrec,
    degree_succ := hdeg_succ,
    no_common_roots := hno


end Tactic
end RealRooted
