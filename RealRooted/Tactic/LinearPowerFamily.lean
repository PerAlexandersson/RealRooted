module

public import RealRooted.LinearPowerFamily
public import RealRooted.Tactic.Finish

/-!
# Linear-power family tactic frontends

Thin tactic wrappers for the fixed linear-power helpers in
`RealRooted.LinearPowerFamily`.
-/

public section

open Lean.Elab.Tactic
open Polynomial

namespace RealRooted

/-- Real-rootedness consequence of the fixed positive linear-tail sequence
interlacing wrapper. -/
theorem isRealRooted_of_linear_tail_sequence
    {A : ℕ → ℝ[X]} {c a b u v : ℝ}
    (hc : 0 < c) (ha : 0 ≤ a) (hb : 0 < b) (hu : 0 < u) (hv : 0 < v)
    (h0 : A 0 = C c) (h1 : A 1 = C a + C b * X)
    (hstep : ∀ n, A (n + 2) = (C u + C v * X) * A (n + 1)) :
    ∀ n, A n ≠ 0 ∧ (A n).Splits :=
  isRealRooted_of_strictInterl_chain_from_step <| fun n =>
    (linear_tail_sequence_interlaces hc ha hb hu.le hv h0 h1 hstep n).toStrictInterl

/-- Real-rootedness consequence of the fixed positive monomial-tail sequence
interlacing wrapper. -/
theorem isRealRooted_of_monomial_tail_sequence
    {A : ℕ → ℝ[X]} {c a b u : ℝ}
    (hc : 0 < c) (ha : 0 ≤ a) (hb : 0 < b) (hu : 0 < u)
    (h0 : A 0 = C c) (h1 : A 1 = C a + C b * X)
    (hstep : ∀ n, A (n + 2) = (C u * X) * A (n + 1)) :
    ∀ n, A n ≠ 0 ∧ (A n).Splits :=
  isRealRooted_of_strictInterl_chain_from_step <| fun n =>
    (monomial_tail_sequence_interlaces hc ha hb hu h0 h1 hstep n).toStrictInterl

end RealRooted

