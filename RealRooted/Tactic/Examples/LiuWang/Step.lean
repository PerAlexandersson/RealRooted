import RealRooted.Tactic.LiuWang.Step

/-!
# Liu--Wang direct-step regression examples

Executable examples for the direct Liu--Wang dispatchers, helper syntax, and
one-step OEIS recurrence forms.
-/

open Polynomial

namespace RealRooted
namespace Tactic

example {c : ℝ} (hc : 0 ≤ c) : 0 ≤ c := by rr_lw_coeff_nonneg

example {n : Nat} : 0 ≤ (n : ℝ) + 1 := by rr_lw_coeff_nonneg

example {n : Nat} (hn : 1 ≤ n) : 0 ≤ (n : ℝ) - 1 := by rr_lw_coeff_nonneg

example : ∀ n : Nat, ((n : ℝ) + 1) ≠ 0 :=
  rr_lw_active_den_all_term

example {n : Nat} : ((n : ℝ) + 3)⁻¹ * ((n : ℝ) + 3) = 1 := by rr_lw_coeff_at n

example : ∀ n : Nat, ((n : ℝ) + 3)⁻¹ * ((n : ℝ) + 3) = 1 := by rr_lw_coeff_all

example {n : Nat} : ((n : ℝ) + 3)⁻¹ * ((n : ℝ) + 3) = 1 :=
  rr_lw_coeff_at_term n

example : ∀ n : Nat, ((n : ℝ) + 3)⁻¹ * ((n : ℝ) + 3) = 1 :=
  rr_lw_coeff_all_term

/-- Positive `t`-lag accepts the natural algebraic form `X * g`, not only
`(C 1 * X) * g`. -/
example {f g a : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ 0)
    (hF_pos : HasPosLeadingCoeff (a * f + X * g))
    (hdeg_lo : f.natDegree ≤ (a * f + X * g).natDegree)
    (hdeg_hi : (a * f + X * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    StrictInterl f (a * f + X * g) := by
  rr_lw_positive_X using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    roots_nonpos := hf_roots,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- Compatibility spelling for unit `X` lags that still supplies the trivial
coefficient certificate. -/
example {f g a : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ 0)
    (hunit : 0 ≤ (1 : ℝ))
    (hF_pos : HasPosLeadingCoeff (a * f + X * g))
    (hdeg_lo : f.natDegree ≤ (a * f + X * g).natDegree)
    (hdeg_hi : (a * f + X * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    StrictInterl f (a * f + X * g) := by
  rr_lw_positive_X using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    roots_nonpos := hf_roots,
    coeff_nonneg := hunit,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

/-- Explicit unit-`X` one-step alias for positive lags. -/
example {f g a : ℝ[X]}
    (hgf : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_roots : ∀ r, f.IsRoot r → r ≤ 0)
    (hF_pos : HasPosLeadingCoeff (a * f + X * g))
    (hdeg_lo : f.natDegree ≤ (a * f + X * g).natDegree)
    (hdeg_hi : (a * f + X * g).natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    StrictInterl f (a * f + X * g) := by
  rr_lw_positive_X_unit using
    interlacer := hgf,
    interlacer_pos_lc := hg_pos,
    roots_nonpos := hf_roots,
    target_pos_lc := hF_pos,
    degree_lower := hdeg_lo,
    degree_upper := hdeg_hi,
    no_common_roots := hno

end Tactic
end RealRooted
