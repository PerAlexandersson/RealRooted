import RealRooted.Tactic.MaWang.Factors

/-!
# Ma--Wang scalar-window regression examples

Regression examples for scalar-window Ma--Wang frontends.
-/

open Polynomial

namespace RealRooted
namespace Tactic

/-- Scalar left denominators are normalized before the Ma--Wang wrapper. -/
example {d : ℝ} (hd : d ≠ 0) {F RHS : ℝ[X]}
    (hraw : C d * F = RHS) :
    F = C d⁻¹ * RHS := by
  rr_mw_den_norm using
    recurrence := hraw,
    den_nonzero := hd

/-- The scalar denominator normalizer works in indexed recurrence side goals. -/
example {P RHS : Nat → ℝ[X]}
    (hraw : ∀ n : Nat, C ((n : ℝ) + 2) * P (n + 1) = RHS n) :
    ∀ n : Nat, P (n + 1) = C (((n : ℝ) + 2)⁻¹) * RHS n := by
  intro n
  rr_mw_den_norm using
    recurrence := hraw n,
    den_nonzero := rr_mw_active_den_at_term n

/-- A062190 has a negative scalar denominator after the active row shift. -/
example (n : Nat) :
    (1 - (3 / 4 : ℝ) * ((n : ℝ) + 2) -
      (1 / 4 : ℝ) * ((n : ℝ) + 2) ^ 2) ≠ 0 := by
  rr_mw_active_den_at n

example {f u : ℝ[X]}
    (hf : f.Splits)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ 0)
    (hdeg_lo : f.natDegree ≤ (u * f + X * f.derivative).natDegree)
    (hdeg_hi : (u * f + X * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + X * f.derivative))
    (hf_pos : HasPosLeadingCoeff f) :
    StrictInterl f (u * f + X * f.derivative) := by
  rr_mw_derivative_sign_roots_nonpos using
    splits := hf,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    target_pos_lc := hF_pos,
    source_pos_lc := hf_pos,
    roots_nonpos := hf_roots

example {f u : ℝ[X]} {c : ℝ}
    (hf : f.Splits)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ 0)
    (hc : 0 ≤ c)
    (hdeg_lo : f.natDegree ≤ (u * f + (C c * X * (1 - X)) * f.derivative).natDegree)
    (hdeg_hi :
      (u * f + (C c * X * (1 - X)) * f.derivative).natDegree ≤
        f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + (C c * X * (1 - X)) * f.derivative))
    (hf_pos : HasPosLeadingCoeff f) :
    StrictInterl f (u * f + (C c * X * (1 - X)) * f.derivative) := by
  rr_mw_derivative_sign_roots_nonpos using
    splits := hf,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    target_pos_lc := hF_pos,
    source_pos_lc := hf_pos,
    roots_nonpos := hf_roots

/-- Sequence endpoint for the `(1+X)(1+2X)P'` window shell. -/
example {P : Nat → ℝ[X]} {U : Nat → ℝ[X]}
    (hbase : StrictInterl (P 0) (P 1))
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (hroot_lo : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → -1 ≤ r)
    (hroot_hi : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → r ≤ -(1 / 2 : ℝ))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        U n * P (n + 1) +
          ((1 + X) * (1 + C (2 : ℝ) * X)) * (P (n + 1)).derivative)
    (hdeg_lo : ∀ n : Nat, (P (n + 1)).natDegree ≤ (P (n + 2)).natDegree)
    (hdeg_hi : ∀ n : Nat, (P (n + 2)).natDegree ≤ (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, StrictInterl (P n) (P (n + 1)) := by
  rr_mw_derivative_one_add_two_window_sequence using
    base := hbase,
    pos_lc := hpos,
    root_lower := hroot_lo,
    root_upper := hroot_hi,
    recurrence := hrec,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi


end Tactic
end RealRooted
