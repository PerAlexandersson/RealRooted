module

public import RealRooted.ScalarNormalization
public import RealRooted.Tactic.SideGoals

/-!
# Scalar denominator tactic

Tactic syntax for normalizing recurrences with scalar constant denominators.
-/

@[expose] public section

open Polynomial

namespace RealRooted

namespace Tactic

/-- Closes an elementary real arithmetic goal about `(n : ℝ)` by `nlinarith`, supplied with
`sq_nonneg ((n : ℝ) + 1)` and `0 ≤ (n : ℝ)`. -/
macro "rr_scalar_active_arith_at " n:term : tactic =>
  `(tactic|
    nlinarith [sq_nonneg (($n : ℝ) + 1), show 0 ≤ ($n : ℝ) by positivity])

/-- Closes a scalar nonnegativity side goal at row `n` by `rr_side_nonneg` or
`rr_scalar_active_arith_at n`. -/
macro "rr_scalar_active_nonneg_at " n:term : tactic =>
  `(tactic|
    solve
      | rr_side_nonneg
      | rr_scalar_active_arith_at $n)

/-- Closes a scalar denominator side goal at row `n` (nonvanishing, or positivity after `ne_of_gt`)
by `rr_side_ne`, `rr_side_pos` or `rr_scalar_active_arith_at n`. -/
macro "rr_scalar_active_den_at " n:term : tactic =>
  `(tactic|
    solve
      | rr_side_ne
      | rr_side_pos
      | rr_scalar_active_arith_at $n
      | apply ne_of_gt
        rr_side_pos
      | apply ne_of_gt
        rr_scalar_active_arith_at $n
      | apply ne_of_lt
        rr_scalar_active_arith_at $n)

/-- Closes the scalar denominator side goal at every row, by introducing `n` and running
`rr_scalar_active_den_at n`. -/
macro "rr_scalar_active_den_all" : tactic =>
  `(tactic| exact fun n => by rr_scalar_active_den_at n)

/-- Term form of `rr_scalar_active_den_all`: elaborates to `by rr_scalar_active_den_all`. -/
syntax (name := rr_scalar_active_den_all_term) "rr_scalar_active_den_all_term" : term

/-- Finishing step of `rr_scalar_coeff_at`: tries `norm_num [Nat.cast_add, Nat.cast_one]` and then
`ring_nf`. -/
syntax (name := rr_scalar_coeff_finish) "rr_scalar_coeff_finish" : tactic

/-- Closes a scalar coefficient identity at row `n` by `field_simp`, with denominators discharged by
`rr_scalar_active_den_at n` or `rr_side_ne` and the result finished by `rr_scalar_coeff_finish`, or
else by `norm_num` or `simp`. -/
macro "rr_scalar_coeff_at " n:term : tactic =>
  `(tactic|
    solve
      | field_simp (discharger := rr_scalar_active_den_at $n) <;> rr_scalar_coeff_finish
      | field_simp (discharger := rr_side_ne) <;> rr_scalar_coeff_finish
      | norm_num [Nat.cast_add, Nat.cast_one]
      | simp)

/-- Closes a scalar coefficient identity at every row, by introducing `n` and running
`rr_scalar_coeff_at n`. -/
macro "rr_scalar_coeff_all" : tactic =>
  `(tactic| exact fun n => by rr_scalar_coeff_at n)

/-- Term form of `rr_scalar_coeff_all`: elaborates to `by rr_scalar_coeff_all`. -/
syntax (name := rr_scalar_coeff_all_term) "rr_scalar_coeff_all_term" : term

macro_rules
  | `(tactic| rr_scalar_coeff_finish) =>
      `(tactic|
        try norm_num [Nat.cast_add, Nat.cast_one] <;>
        try ring_nf)
  | `(rr_scalar_active_den_all_term) =>
      `(by rr_scalar_active_den_all)
  | `(rr_scalar_coeff_all_term) =>
      `(by rr_scalar_coeff_all)

/-- Divides a recurrence by a nonzero scalar denominator. From `recurrence : C d * F = RHS` and
`den_nonzero : d ≠ 0`, it closes the divided goal for `F`: `F = A` if `RHS` is `C d * A`,
`F = A + C d⁻¹ * B` if `RHS` is `C d * A + B` or `B + C d * A`, and otherwise `F = C d⁻¹ * RHS`. -/
syntax (name := rr_scalar_den_norm_named)
  "rr_scalar_den_norm" " using "
    "recurrence" ":=" term ","
    "den_nonzero" ":=" term :
  tactic

/-- Alias of `rr_scalar_den_norm`, with the same arguments `recurrence` and `den_nonzero`. -/
syntax (name := rr_mw_den_norm_named)
  "rr_mw_den_norm" " using "
    "recurrence" ":=" term ","
    "den_nonzero" ":=" term :
  tactic

/-- Divides the recurrence `recurrence : C d * F = C d * A + C b * Q` by `den_nonzero : d ≠ 0` and
closes `F = A + C c * Q`, where `coeff_eq : d⁻¹ * b = c` is the scalar identity for the new
coefficient. -/
syntax (name := rr_scalar_den_norm_coeff_named)
  "rr_scalar_den_norm_coeff" " using "
    "recurrence" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term :
  tactic

/-- Alias of `rr_scalar_den_norm_coeff`, with the same arguments `recurrence`, `den_nonzero` and
`coeff_eq`. -/
syntax (name := rr_mw_den_norm_coeff_named)
  "rr_mw_den_norm_coeff" " using "
    "recurrence" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term :
  tactic

/-- Divides the recurrence `recurrence : C d * F = C d * A + C b * Q + C e * R` by
`den_nonzero : d ≠ 0` and closes `F = A + C c * Q + C f * R`, where `first_coeff_eq : d⁻¹ * b = c`
and `second_coeff_eq : d⁻¹ * e = f` are the scalar identities for the new coefficients. -/
syntax (name := rr_scalar_den_norm_two_coeff_named)
  "rr_scalar_den_norm_two_coeff" " using "
    "recurrence" ":=" term ","
    "den_nonzero" ":=" term ","
    "first_coeff_eq" ":=" term ","
    "second_coeff_eq" ":=" term :
  tactic

/-- Alias of `rr_scalar_den_norm_two_coeff`, with the same arguments `recurrence`, `den_nonzero`,
`first_coeff_eq` and `second_coeff_eq`. -/
syntax (name := rr_mw_den_norm_two_coeff_named)
  "rr_mw_den_norm_two_coeff" " using "
    "recurrence" ":=" term ","
    "den_nonzero" ":=" term ","
    "first_coeff_eq" ":=" term ","
    "second_coeff_eq" ":=" term :
  tactic

/-- Alias of `rr_scalar_active_den_at`. -/
macro "rr_mw_active_den_at " n:term : tactic =>
  `(tactic| rr_scalar_active_den_at $n)

/-- Alias of `rr_scalar_active_den_all`. -/
macro "rr_mw_active_den_all" : tactic =>
  `(tactic| rr_scalar_active_den_all)

/-- Alias of `rr_scalar_coeff_at`. -/
macro "rr_mw_coeff_at " n:term : tactic =>
  `(tactic| rr_scalar_coeff_at $n)

/-- Alias of `rr_scalar_coeff_all`. -/
macro "rr_mw_coeff_all" : tactic =>
  `(tactic| rr_scalar_coeff_all)

/-- Term form of `rr_mw_active_den_at`: elaborates to `by rr_mw_active_den_at n`. -/
syntax (name := rr_mw_active_den_at_term) "rr_mw_active_den_at_term " term : term

/-- Term form of `rr_mw_active_den_all`: elaborates to `by rr_mw_active_den_all`. -/
syntax (name := rr_mw_active_den_all_term) "rr_mw_active_den_all_term" : term

/-- Term form of `rr_mw_coeff_at`: elaborates to `by rr_mw_coeff_at n`. -/
syntax (name := rr_mw_coeff_at_term) "rr_mw_coeff_at_term " term : term

/-- Term form of `rr_mw_coeff_all`: elaborates to `by rr_mw_coeff_all`. -/
syntax (name := rr_mw_coeff_all_term) "rr_mw_coeff_all_term" : term

/-- Closes the goal by `exact h`, or else by `simpa using h` up to commutativity and associativity
of addition. -/
syntax (name := rr_scalar_exact_or_simpa_add_assoc)
  "rr_scalar_exact_or_simpa_add_assoc" term :
  tactic

/-- Closes the goal by `exact h`, or else by `simpa using h` up to commutativity and associativity
of addition and associativity of multiplication. -/
syntax (name := rr_scalar_exact_or_simpa_add_mul_assoc)
  "rr_scalar_exact_or_simpa_add_mul_assoc" term :
  tactic

macro_rules
  | `(rr_mw_active_den_at_term $n:term) =>
      `(by rr_mw_active_den_at $n)
  | `(rr_mw_active_den_all_term) =>
      `(by rr_mw_active_den_all)
  | `(rr_mw_coeff_at_term $n:term) =>
      `(by rr_mw_coeff_at $n)
  | `(rr_mw_coeff_all_term) =>
      `(by rr_mw_coeff_all)
  | `(tactic| rr_scalar_exact_or_simpa_add_assoc $h:term) =>
      `(tactic|
        with_reducible_and_instances
          first
            | exact $h
            | simpa [add_comm, add_left_comm, add_assoc] using $h)
  | `(tactic| rr_scalar_exact_or_simpa_add_mul_assoc $h:term) =>
      `(tactic|
        with_reducible_and_instances
          first
            | exact $h
            | simpa [add_comm, add_left_comm, add_assoc, mul_assoc] using $h)

macro_rules
  | `(tactic|
      rr_scalar_den_norm using
        recurrence := $hrec:term,
        den_nonzero := $hden:term) =>
      `(tactic|
        with_reducible_and_instances
          first
            | exact RealRooted.eq_of_C_mul_eq_C_mul $hden $hrec
            | rr_scalar_exact_or_simpa_add_assoc
                (RealRooted.eq_add_C_inv_mul_of_C_mul_eq_C_mul_add $hden $hrec)
            | rr_scalar_exact_or_simpa_add_assoc
                (RealRooted.eq_add_C_inv_mul_of_C_mul_eq_add_C_mul $hden $hrec)
            | exact RealRooted.eq_C_inv_mul_of_C_mul_eq $hden $hrec
            | simpa [one_div] using RealRooted.eq_C_inv_mul_of_C_mul_eq $hden $hrec)
  | `(tactic|
      rr_mw_den_norm using
        recurrence := $hrec:term,
        den_nonzero := $hden:term) =>
      `(tactic|
        rr_scalar_den_norm using
          recurrence := $hrec,
          den_nonzero := $hden)
  | `(tactic|
      rr_scalar_den_norm_coeff using
        recurrence := $hrec:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term) =>
      `(tactic|
        with_reducible_and_instances
          apply RealRooted.eq_add_C_mul_of_C_mul_eq_C_mul_add_C_mul $hden $hcoeff
          simpa only [add_comm, add_left_comm, add_assoc, mul_assoc] using $hrec)
  | `(tactic|
      rr_mw_den_norm_coeff using
        recurrence := $hrec:term,
        den_nonzero := $hden:term,
        coeff_eq := $hcoeff:term) =>
      `(tactic|
        rr_scalar_den_norm_coeff using
          recurrence := $hrec,
          den_nonzero := $hden,
          coeff_eq := $hcoeff)
  | `(tactic|
      rr_scalar_den_norm_two_coeff using
        recurrence := $hrec:term,
        den_nonzero := $hden:term,
        first_coeff_eq := $hcoeff_first:term,
        second_coeff_eq := $hcoeff_second:term) =>
      `(tactic|
        with_reducible_and_instances
          first
            | exact
                RealRooted.eq_add_C_mul_add_C_mul_of_C_mul_eq_C_mul_add_C_mul_add_C_mul
                  $hden $hcoeff_first $hcoeff_second $hrec
            | exact
                RealRooted.eq_add_C_mul_add_C_mul_of_C_mul_eq_C_mul_add_C_mul_add_C_mul
                  $hden $hcoeff_first $hcoeff_second
                  (by simpa [add_comm, add_left_comm, add_assoc, mul_assoc] using $hrec))
  | `(tactic|
      rr_mw_den_norm_two_coeff using
        recurrence := $hrec:term,
        den_nonzero := $hden:term,
        first_coeff_eq := $hcoeff_first:term,
        second_coeff_eq := $hcoeff_second:term) =>
      `(tactic|
        rr_scalar_den_norm_two_coeff using
          recurrence := $hrec,
          den_nonzero := $hden,
          first_coeff_eq := $hcoeff_first,
          second_coeff_eq := $hcoeff_second)

end Tactic
end RealRooted
