import RealRooted.ScalarNormalization
import RealRooted.Tactic.SideGoals

/-!
# Scalar denominator tactic

Tactic syntax for normalizing recurrences with scalar constant denominators.
-/

open Polynomial

namespace RealRooted

namespace Tactic

macro "rr_scalar_active_arith_at " n:term : tactic =>
  `(tactic|
    nlinarith [sq_nonneg (($n : ℝ) + 1), show 0 ≤ ($n : ℝ) by positivity])

macro "rr_scalar_active_nonneg_at " n:term : tactic =>
  `(tactic|
    solve
      | rr_side_nonneg
      | rr_scalar_active_arith_at $n)

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

macro "rr_scalar_active_den_all" : tactic =>
  `(tactic| exact fun n => by rr_scalar_active_den_at n)

syntax (name := rr_scalar_active_den_all_term) "rr_scalar_active_den_all_term" : term

syntax (name := rr_scalar_coeff_finish) "rr_scalar_coeff_finish" : tactic

macro "rr_scalar_coeff_at " n:term : tactic =>
  `(tactic|
    solve
      | field_simp (discharger := rr_scalar_active_den_at $n) <;> rr_scalar_coeff_finish
      | field_simp (discharger := rr_side_ne) <;> rr_scalar_coeff_finish
      | norm_num [Nat.cast_add, Nat.cast_one]
      | simp)

macro "rr_scalar_coeff_all" : tactic =>
  `(tactic| exact fun n => by rr_scalar_coeff_at n)

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

syntax (name := rr_scalar_den_norm_named)
  "rr_scalar_den_norm" " using "
    "recurrence" ":=" term ","
    "den_nonzero" ":=" term :
  tactic

syntax (name := rr_mw_den_norm_named)
  "rr_mw_den_norm" " using "
    "recurrence" ":=" term ","
    "den_nonzero" ":=" term :
  tactic

syntax (name := rr_scalar_den_norm_coeff_named)
  "rr_scalar_den_norm_coeff" " using "
    "recurrence" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term :
  tactic

syntax (name := rr_mw_den_norm_coeff_named)
  "rr_mw_den_norm_coeff" " using "
    "recurrence" ":=" term ","
    "den_nonzero" ":=" term ","
    "coeff_eq" ":=" term :
  tactic

syntax (name := rr_scalar_den_norm_two_coeff_named)
  "rr_scalar_den_norm_two_coeff" " using "
    "recurrence" ":=" term ","
    "den_nonzero" ":=" term ","
    "first_coeff_eq" ":=" term ","
    "second_coeff_eq" ":=" term :
  tactic

syntax (name := rr_mw_den_norm_two_coeff_named)
  "rr_mw_den_norm_two_coeff" " using "
    "recurrence" ":=" term ","
    "den_nonzero" ":=" term ","
    "first_coeff_eq" ":=" term ","
    "second_coeff_eq" ":=" term :
  tactic

macro "rr_mw_active_den_at " n:term : tactic =>
  `(tactic| rr_scalar_active_den_at $n)

macro "rr_mw_active_den_all" : tactic =>
  `(tactic| rr_scalar_active_den_all)

macro "rr_mw_coeff_at " n:term : tactic =>
  `(tactic| rr_scalar_coeff_at $n)

macro "rr_mw_coeff_all" : tactic =>
  `(tactic| rr_scalar_coeff_all)

syntax (name := rr_mw_active_den_at_term) "rr_mw_active_den_at_term " term : term

syntax (name := rr_mw_active_den_all_term) "rr_mw_active_den_all_term" : term

syntax (name := rr_mw_coeff_at_term) "rr_mw_coeff_at_term " term : term

syntax (name := rr_mw_coeff_all_term) "rr_mw_coeff_all_term" : term

syntax (name := rr_scalar_exact_or_simpa_add_assoc)
  "rr_scalar_exact_or_simpa_add_assoc" term :
  tactic

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
        first
          | exact $h
          | simpa [add_comm, add_left_comm, add_assoc] using $h)
  | `(tactic| rr_scalar_exact_or_simpa_add_mul_assoc $h:term) =>
      `(tactic|
        first
          | exact $h
          | simpa [add_comm, add_left_comm, add_assoc, mul_assoc] using $h)

macro_rules
  | `(tactic|
      rr_scalar_den_norm using
        recurrence := $hrec:term,
        den_nonzero := $hden:term) =>
      `(tactic|
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
        first
          | rr_scalar_exact_or_simpa_add_mul_assoc
              (RealRooted.eq_add_C_mul_of_C_mul_eq_C_mul_add_C_mul
                $hden $hcoeff $hrec)
          | rr_scalar_exact_or_simpa_add_mul_assoc
              (RealRooted.eq_add_C_mul_of_C_mul_eq_C_mul_add_comm_C_mul
                $hden $hcoeff $hrec))
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
