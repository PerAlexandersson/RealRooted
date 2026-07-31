import RealRooted.LinearPowerFamily
import RealRooted.Tactic.Finish

/-!
# Linear-power family tactic frontends

Thin tactic wrappers for the fixed linear-power helpers in
`RealRooted.LinearPowerFamily`.
-/

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
  isRealRooted_of_interlaces_chain <|
    linear_tail_sequence_interlaces hc ha hb hu hv h0 h1 hstep

/-- Real-rootedness consequence of the fixed positive monomial-tail sequence
interlacing wrapper. -/
theorem isRealRooted_of_monomial_tail_sequence
    {A : ℕ → ℝ[X]} {c a b u : ℝ}
    (hc : 0 < c) (ha : 0 ≤ a) (hb : 0 < b) (hu : 0 < u)
    (h0 : A 0 = C c) (h1 : A 1 = C a + C b * X)
    (hstep : ∀ n, A (n + 2) = (C u * X) * A (n + 1)) :
    ∀ n, A n ≠ 0 ∧ (A n).Splits :=
  isRealRooted_of_interlaces_chain <|
    monomial_tail_sequence_interlaces hc ha hb hu h0 h1 hstep

namespace Tactic

syntax (name := rr_interlaces_linear_pow_named)
  "rr_interlaces_linear_pow" " using "
    "const" ":=" term ","
    "slope" ":=" term ","
    "slope_pos" ":=" term ","
    "index" ":=" term :
  tactic

syntax (name := rr_interlaces_C_mul_linear_pow_named)
  "rr_interlaces_C_mul_linear_pow" " using "
    "scalar" ":=" term ","
    "const" ":=" term ","
    "slope" ":=" term ","
    "scalar_ne" ":=" term ","
    "slope_pos" ":=" term ","
    "index" ":=" term :
  tactic

syntax (name := rr_hasNonnegCoeffs_linear_pow_named)
  "rr_hasNonnegCoeffs_linear_pow" " using "
    "a_nonneg" ":=" term ","
    "b_nonneg" ":=" term ","
    "index" ":=" term :
  tactic

syntax (name := rr_linear_tail_sequence_interlaces_named)
  "rr_linear_tail_sequence_interlaces" " using "
    "c_pos" ":=" term ","
    "a_nonneg" ":=" term ","
    "b_pos" ":=" term ","
    "u_pos" ":=" term ","
    "v_pos" ":=" term ","
    "base0" ":=" term ","
    "base1" ":=" term ","
    "recurrence" ":=" term ","
    "index" ":=" term :
  tactic

syntax (name := rr_linear_tail_sequence_realrooted_named)
  "rr_linear_tail_sequence_realrooted" " using "
    "c_pos" ":=" term ","
    "a_nonneg" ":=" term ","
    "b_pos" ":=" term ","
    "u_pos" ":=" term ","
    "v_pos" ":=" term ","
    "base0" ":=" term ","
    "base1" ":=" term ","
    "recurrence" ":=" term ","
    "index" ":=" term :
  tactic

syntax (name := rr_monomial_tail_sequence_interlaces_named)
  "rr_monomial_tail_sequence_interlaces" " using "
    "c_pos" ":=" term ","
    "a_nonneg" ":=" term ","
    "b_pos" ":=" term ","
    "u_pos" ":=" term ","
    "base0" ":=" term ","
    "base1" ":=" term ","
    "recurrence" ":=" term ","
    "index" ":=" term :
  tactic

syntax (name := rr_monomial_tail_sequence_realrooted_named)
  "rr_monomial_tail_sequence_realrooted" " using "
    "c_pos" ":=" term ","
    "a_nonneg" ":=" term ","
    "b_pos" ":=" term ","
    "u_pos" ":=" term ","
    "base0" ":=" term ","
    "base1" ":=" term ","
    "recurrence" ":=" term ","
    "index" ":=" term :
  tactic

syntax (name := rr_interlaces_X_sub_C_pow_mul_linear_pow_named)
  "rr_interlaces_X_sub_C_pow_mul_linear_pow" " using "
    "root" ":=" term ","
    "root_power" ":=" term ","
    "const" ":=" term ","
    "slope" ":=" term ","
    "slope_pos" ":=" term ","
    "index" ":=" term :
  tactic

syntax (name := rr_linear_power_sequence_interlaces_named)
  "rr_linear_power_sequence_interlaces" " using "
    "closed" ":=" term ","
    "exponent_step" ":=" term ","
    "slope_pos" ":=" term :
  tactic

syntax (name := rr_linear_power_sequence_realrooted_named)
  "rr_linear_power_sequence_realrooted" " using "
    "closed" ":=" term ","
    "exponent_step" ":=" term ","
    "slope_pos" ":=" term :
  tactic

syntax (name := rr_linear_power_scalar_sequence_interlaces_named)
  "rr_linear_power_scalar_sequence_interlaces" " using "
    "closed" ":=" term ","
    "scalar_ne_zero" ":=" term ","
    "exponent_step" ":=" term ","
    "slope_pos" ":=" term :
  tactic

syntax (name := rr_linear_power_scalar_sequence_realrooted_named)
  "rr_linear_power_scalar_sequence_realrooted" " using "
    "closed" ":=" term ","
    "scalar_ne_zero" ":=" term ","
    "exponent_step" ":=" term ","
    "slope_pos" ":=" term :
  tactic

syntax (name := rr_linear_power_exists_scalar_sequence_interlaces_named)
  "rr_linear_power_exists_scalar_sequence_interlaces" " using "
    "closed" ":=" term ","
    "exponent_step" ":=" term ","
    "slope_pos" ":=" term :
  tactic

syntax (name := rr_linear_power_exists_scalar_sequence_realrooted_named)
  "rr_linear_power_exists_scalar_sequence_realrooted" " using "
    "closed" ":=" term ","
    "exponent_step" ":=" term ","
    "slope_pos" ":=" term :
  tactic

syntax (name := rr_fixed_linear_power_sequence_interlaces_named)
  "rr_fixed_linear_power_sequence_interlaces" " using "
    "closed" ":=" term ","
    "exponent_step" ":=" term ","
    "slope_pos" ":=" term :
  tactic

syntax (name := rr_fixed_linear_power_sequence_realrooted_named)
  "rr_fixed_linear_power_sequence_realrooted" " using "
    "closed" ":=" term ","
    "exponent_step" ":=" term ","
    "slope_pos" ":=" term :
  tactic

syntax (name := rr_common_factor_linear_power_sequence_interlaces_named)
  "rr_common_factor_linear_power_sequence_interlaces" " using "
    "fixed_realrooted" ":=" term ","
    "closed" ":=" term ","
    "exponent_step" ":=" term ","
    "slope_pos" ":=" term :
  tactic

syntax (name := rr_common_factor_linear_power_sequence_realrooted_named)
  "rr_common_factor_linear_power_sequence_realrooted" " using "
    "fixed_realrooted" ":=" term ","
    "closed" ":=" term ","
    "exponent_step" ":=" term ","
    "slope_pos" ":=" term :
  tactic

syntax (name := rr_linear_tail_sequence_interlaces_compat_named)
  "rr_linear_tail_sequence_interlaces" " using "
    "constant" ":=" term ","
    "linear_const" ":=" term ","
    "linear_slope" ":=" term ","
    "tail_const" ":=" term ","
    "tail_slope" ":=" term ","
    "constant_pos" ":=" term ","
    "linear_const_nonneg" ":=" term ","
    "linear_slope_pos" ":=" term ","
    "tail_const_pos" ":=" term ","
    "tail_slope_pos" ":=" term ","
    "base0" ":=" term ","
    "base1" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_linear_tail_sequence_realrooted_compat_named)
  "rr_linear_tail_sequence_realrooted" " using "
    "constant" ":=" term ","
    "linear_const" ":=" term ","
    "linear_slope" ":=" term ","
    "tail_const" ":=" term ","
    "tail_slope" ":=" term ","
    "constant_pos" ":=" term ","
    "linear_const_nonneg" ":=" term ","
    "linear_slope_pos" ":=" term ","
    "tail_const_pos" ":=" term ","
    "tail_slope_pos" ":=" term ","
    "base0" ":=" term ","
    "base1" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_monomial_tail_sequence_interlaces_compat_named)
  "rr_monomial_tail_sequence_interlaces" " using "
    "constant" ":=" term ","
    "linear_const" ":=" term ","
    "linear_slope" ":=" term ","
    "tail_slope" ":=" term ","
    "constant_pos" ":=" term ","
    "linear_const_nonneg" ":=" term ","
    "linear_slope_pos" ":=" term ","
    "tail_slope_pos" ":=" term ","
    "base0" ":=" term ","
    "base1" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_monomial_tail_sequence_realrooted_compat_named)
  "rr_monomial_tail_sequence_realrooted" " using "
    "constant" ":=" term ","
    "linear_const" ":=" term ","
    "linear_slope" ":=" term ","
    "tail_slope" ":=" term ","
    "constant_pos" ":=" term ","
    "linear_const_nonneg" ":=" term ","
    "linear_slope_pos" ":=" term ","
    "tail_slope_pos" ":=" term ","
    "base0" ":=" term ","
    "base1" ":=" term ","
    "step" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_interlaces_linear_pow using
        const := $a:term,
        slope := $b:term,
        slope_pos := $hb:term,
        index := $n:term) =>
      `(tactic| exact RealRooted.interlaces_linear_pow $a $b $hb $n)
  | `(tactic|
      rr_interlaces_C_mul_linear_pow using
        scalar := $c:term,
        const := $a:term,
        slope := $b:term,
        scalar_ne := $hc:term,
        slope_pos := $hb:term,
        index := $n:term) =>
      `(tactic| exact RealRooted.interlaces_C_mul_linear_pow $c $a $b $hc $hb $n)
  | `(tactic|
      rr_hasNonnegCoeffs_linear_pow using
        a_nonneg := $ha:term,
        b_nonneg := $hb:term,
        index := $n:term) =>
      `(tactic| exact RealRooted.hasNonnegCoeffs_linear_pow $ha $hb $n)
  | `(tactic|
      rr_linear_tail_sequence_interlaces using
        c_pos := $hc:term,
        a_nonneg := $ha:term,
        b_pos := $hb:term,
        u_pos := $hu:term,
        v_pos := $hv:term,
        base0 := $h0:term,
        base1 := $h1:term,
        recurrence := $hstep:term,
        index := $n:term) =>
      `(tactic|
        exact RealRooted.linear_tail_sequence_interlaces
          $hc $ha $hb $hu $hv $h0 $h1 $hstep $n)
  | `(tactic|
      rr_linear_tail_sequence_realrooted using
        c_pos := $hc:term,
        a_nonneg := $ha:term,
        b_pos := $hb:term,
        u_pos := $hu:term,
        v_pos := $hv:term,
        base0 := $h0:term,
        base1 := $h1:term,
        recurrence := $hstep:term,
        index := $n:term) =>
      `(tactic|
        exact RealRooted.isRealRooted_of_linear_tail_sequence
          $hc $ha $hb $hu $hv $h0 $h1 $hstep $n)
  | `(tactic|
      rr_monomial_tail_sequence_interlaces using
        c_pos := $hc:term,
        a_nonneg := $ha:term,
        b_pos := $hb:term,
        u_pos := $hu:term,
        base0 := $h0:term,
        base1 := $h1:term,
        recurrence := $hstep:term,
        index := $n:term) =>
      `(tactic|
        exact RealRooted.monomial_tail_sequence_interlaces
          $hc $ha $hb $hu $h0 $h1 $hstep $n)
  | `(tactic|
      rr_monomial_tail_sequence_realrooted using
        c_pos := $hc:term,
        a_nonneg := $ha:term,
        b_pos := $hb:term,
        u_pos := $hu:term,
        base0 := $h0:term,
        base1 := $h1:term,
        recurrence := $hstep:term,
        index := $n:term) =>
      `(tactic|
        exact RealRooted.isRealRooted_of_monomial_tail_sequence
          $hc $ha $hb $hu $h0 $h1 $hstep $n)
  | `(tactic|
      rr_interlaces_X_sub_C_pow_mul_linear_pow using
        root := $r:term,
        root_power := $m:term,
        const := $a:term,
        slope := $b:term,
        slope_pos := $hb:term,
        index := $n:term) =>
      `(tactic|
        exact RealRooted.interlaces_X_sub_C_pow_mul_linear_pow
          $r $m $a $b $hb $n)
  | `(tactic|
      rr_linear_power_sequence_interlaces using
        closed := $hclosed:term,
        exponent_step := $hexponent:term,
        slope_pos := $hb:term) =>
      `(tactic|
        apply RealRooted.linearPowerSequence_interlaces $hclosed $hexponent $hb)
  | `(tactic|
      rr_linear_power_sequence_realrooted using
        closed := $hclosed:term,
        exponent_step := $hexponent:term,
        slope_pos := $hb:term) =>
      `(tactic|
        apply RealRooted.linearPowerSequence_realRooted $hclosed $hexponent $hb)
  | `(tactic|
      rr_linear_power_scalar_sequence_interlaces using
        closed := $hclosed:term,
        scalar_ne_zero := $hscalar:term,
        exponent_step := $hexponent:term,
        slope_pos := $hb:term) =>
      `(tactic|
        apply RealRooted.linearPowerScalarSequence_interlaces
          $hclosed $hscalar $hexponent $hb)
  | `(tactic|
      rr_linear_power_scalar_sequence_realrooted using
        closed := $hclosed:term,
        scalar_ne_zero := $hscalar:term,
        exponent_step := $hexponent:term,
        slope_pos := $hb:term) =>
      `(tactic|
        apply RealRooted.linearPowerScalarSequence_realRooted
          $hclosed $hscalar $hexponent $hb)
  | `(tactic|
      rr_linear_power_exists_scalar_sequence_interlaces using
        closed := $hclosed:term,
        exponent_step := $hexponent:term,
        slope_pos := $hb:term) =>
      `(tactic|
        apply RealRooted.linearPowerExistsScalarSequence_interlaces
          $hclosed $hexponent $hb)
  | `(tactic|
      rr_linear_power_exists_scalar_sequence_realrooted using
        closed := $hclosed:term,
        exponent_step := $hexponent:term,
        slope_pos := $hb:term) =>
      `(tactic|
        apply RealRooted.linearPowerExistsScalarSequence_realRooted
          $hclosed $hexponent $hb)
  | `(tactic|
      rr_fixed_linear_power_sequence_interlaces using
        closed := $hclosed:term,
        exponent_step := $hexponent:term,
        slope_pos := $hb:term) =>
      `(tactic|
        apply RealRooted.fixedLinearPowerSequence_interlaces $hclosed $hexponent $hb)
  | `(tactic|
      rr_fixed_linear_power_sequence_realrooted using
        closed := $hclosed:term,
        exponent_step := $hexponent:term,
        slope_pos := $hb:term) =>
      `(tactic|
        apply RealRooted.fixedLinearPowerSequence_realRooted $hclosed $hexponent $hb)
  | `(tactic|
      rr_common_factor_linear_power_sequence_interlaces using
        fixed_realrooted := $hfixed:term,
        closed := $hclosed:term,
        exponent_step := $hexponent:term,
        slope_pos := $hb:term) =>
      `(tactic|
        apply RealRooted.commonFactorLinearPowerSequence_interlaces
          $hfixed $hclosed $hexponent $hb)
  | `(tactic|
      rr_common_factor_linear_power_sequence_realrooted using
        fixed_realrooted := $hfixed:term,
        closed := $hclosed:term,
        exponent_step := $hexponent:term,
        slope_pos := $hb:term) =>
      `(tactic|
        apply RealRooted.commonFactorLinearPowerSequence_realRooted
          $hfixed $hclosed $hexponent $hb)
  | `(tactic|
      rr_linear_tail_sequence_interlaces using
        constant := $c:term,
        linear_const := $a:term,
        linear_slope := $b:term,
        tail_const := $u:term,
        tail_slope := $v:term,
        constant_pos := $hc:term,
        linear_const_nonneg := $ha:term,
        linear_slope_pos := $hb:term,
        tail_const_pos := $hu:term,
        tail_slope_pos := $hv:term,
        base0 := $h0:term,
        base1 := $h1:term,
        step := $hstep:term) =>
      `(tactic|
        apply RealRooted.linear_tail_sequence_interlaces
          (c := $c) (a := $a) (b := $b) (u := $u) (v := $v)
          $hc $ha $hb $hu $hv $h0 $h1 $hstep)
  | `(tactic|
      rr_linear_tail_sequence_realrooted using
        constant := $c:term,
        linear_const := $a:term,
        linear_slope := $b:term,
        tail_const := $u:term,
        tail_slope := $v:term,
        constant_pos := $hc:term,
        linear_const_nonneg := $ha:term,
        linear_slope_pos := $hb:term,
        tail_const_pos := $hu:term,
        tail_slope_pos := $hv:term,
        base0 := $h0:term,
        base1 := $h1:term,
        step := $hstep:term) =>
      `(tactic|
        apply RealRooted.isRealRooted_of_linear_tail_sequence
          (c := $c) (a := $a) (b := $b) (u := $u) (v := $v)
          $hc $ha $hb $hu $hv $h0 $h1 $hstep)
  | `(tactic|
      rr_monomial_tail_sequence_interlaces using
        constant := $c:term,
        linear_const := $a:term,
        linear_slope := $b:term,
        tail_slope := $u:term,
        constant_pos := $hc:term,
        linear_const_nonneg := $ha:term,
        linear_slope_pos := $hb:term,
        tail_slope_pos := $hu:term,
        base0 := $h0:term,
        base1 := $h1:term,
        step := $hstep:term) =>
      `(tactic|
        apply RealRooted.monomial_tail_sequence_interlaces
          (c := $c) (a := $a) (b := $b) (u := $u)
          $hc $ha $hb $hu $h0 $h1 $hstep)
  | `(tactic|
      rr_monomial_tail_sequence_realrooted using
        constant := $c:term,
        linear_const := $a:term,
        linear_slope := $b:term,
        tail_slope := $u:term,
        constant_pos := $hc:term,
        linear_const_nonneg := $ha:term,
        linear_slope_pos := $hb:term,
        tail_slope_pos := $hu:term,
        base0 := $h0:term,
        base1 := $h1:term,
        step := $hstep:term) =>
      `(tactic|
        apply RealRooted.isRealRooted_of_monomial_tail_sequence
          (c := $c) (a := $a) (b := $b) (u := $u)
          $hc $ha $hb $hu $h0 $h1 $hstep)

end Tactic
end RealRooted
