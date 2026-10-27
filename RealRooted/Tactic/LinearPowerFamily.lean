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

namespace Tactic

/-- Closes `Interlaces (C c * (C a + C b * X) ^ n) (C d * (C a + C b * X) ^ (n + 1))` from
`left_scalar : c`, `right_scalar : d`, `const : a`, `slope : b`, the nonvanishing
`left_scalar_ne` and `right_scalar_ne`, `slope_pos : 0 < b` and `index : n`. -/
syntax (name := rr_interlaces_C_mul_linear_pow_succ_named)
  "rr_interlaces_C_mul_linear_pow_succ" " using "
    "left_scalar" ":=" term ","
    "right_scalar" ":=" term ","
    "const" ":=" term ","
    "slope" ":=" term ","
    "left_scalar_ne" ":=" term ","
    "right_scalar_ne" ":=" term ","
    "slope_pos" ":=" term ","
    "index" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_interlaces_C_mul_linear_pow_succ using
        left_scalar := $c:term,
        right_scalar := $d:term,
        const := $a:term,
        slope := $b:term,
        left_scalar_ne := $hc:term,
        right_scalar_ne := $hd:term,
        slope_pos := $hb:term,
        index := $n:term) =>
      `(tactic|
        simpa only [C_0, C_1, zero_add, one_mul] using
          RealRooted.interlaces_C_mul_linear_pow_succ
            $c $d $a $b $hc $hd $hb $n)
end Tactic
end RealRooted
