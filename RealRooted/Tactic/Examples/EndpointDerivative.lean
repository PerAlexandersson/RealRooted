import RealRooted.Tactic.EndpointDerivative

/-!
# Endpoint-derivative tactic examples

Abstract smoke tests for the two interval-preserving sequence frontends.
-/

open Polynomial Set

namespace RealRooted
namespace Tactic

section EndpointDerivative

variable {P : ℕ → ℝ[X]} {a b : ℝ}
variable (hab : a ≤ b)
variable (hbase_splits : (P 0).Splits)
variable (hbase_roots : ∀ r ∈ (P 0).roots, r ∈ Icc a b)
variable (hpos : ∀ n, HasPosLeadingCoeff (P n))
variable (hdeg : ∀ n, 1 ≤ (P n).natDegree)
variable (hrec : ∀ n,
  P (n + 1) = ((X - C a) * (X - C b)) * (P n).derivative)
variable (hdeg_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree)

example : ∀ n, Prec (P n) (P (n + 1)) := by
  rr_endpoint_derivative_sequence using
    lower_le_upper := hab,
    base_splits := hbase_splits,
    base_roots := hbase_roots,
    pos_lc := hpos,
    degree_pos := hdeg,
    recurrence := hrec

example : ∀ n, Interlaces (P n) (P (n + 1)) := by
  rr_endpoint_derivative_sequence_interlaces using
    lower_le_upper := hab,
    base_splits := hbase_splits,
    base_roots := hbase_roots,
    pos_lc := hpos,
    degree_pos := hdeg,
    recurrence := hrec,
    degree_succ := hdeg_succ

example : ∀ n, P n ≠ 0 ∧ (P n).Splits := by
  rr_endpoint_derivative_sequence_realrooted using
    lower_le_upper := hab,
    base_splits := hbase_splits,
    base_roots := hbase_roots,
    pos_lc := hpos,
    degree_pos := hdeg,
    recurrence := hrec

end EndpointDerivative

section EndpointProductDerivative

variable {P : ℕ → ℝ[X]} {a b : ℝ}
variable (hab : a ≤ b)
variable (hbase_splits : (P 0).Splits)
variable (hbase_roots : ∀ r ∈ (P 0).roots, r ∈ Icc a b)
variable (hpos : ∀ n, HasPosLeadingCoeff (P n))
variable (hdeg : ∀ n, 1 ≤ (P n).natDegree)
variable (hrec : ∀ n,
  P (n + 1) = (((X - C a) * (X - C b)) * P n).derivative)
variable (hdeg_succ : ∀ n, (P n).natDegree + 1 = (P (n + 1)).natDegree)

example : ∀ n, Prec (P n) (P (n + 1)) := by
  rr_endpoint_product_derivative_sequence using
    lower_le_upper := hab,
    base_splits := hbase_splits,
    base_roots := hbase_roots,
    pos_lc := hpos,
    degree_pos := hdeg,
    recurrence := hrec

example : ∀ n, Interlaces (P n) (P (n + 1)) := by
  rr_endpoint_product_derivative_sequence_interlaces using
    lower_le_upper := hab,
    base_splits := hbase_splits,
    base_roots := hbase_roots,
    pos_lc := hpos,
    degree_pos := hdeg,
    recurrence := hrec,
    degree_succ := hdeg_succ

example : ∀ n, P n ≠ 0 ∧ (P n).Splits := by
  rr_endpoint_product_derivative_sequence_realrooted using
    lower_le_upper := hab,
    base_splits := hbase_splits,
    base_roots := hbase_roots,
    pos_lc := hpos,
    degree_pos := hdeg,
    recurrence := hrec

end EndpointProductDerivative

end Tactic
end RealRooted
