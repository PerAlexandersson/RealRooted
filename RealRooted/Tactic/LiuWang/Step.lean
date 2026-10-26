module

public import RealRooted.LiuWang
public import RealRooted.Tactic.Finish
public import RealRooted.Tactic.RootBounds
public import RealRooted.Tactic.ScalarDen
public import RealRooted.Tactic.SideGoals

/-!
# Generalized Liu--Wang tactic

Dispatcher tactics and certificate plumbing for the theorem API in
RealRooted.LiuWang.
-/

public section

open Polynomial

namespace RealRooted

/-- Term `fun n => by simpa using hrec n`, normalizing a recurrence certificate `hrec` for every
row. -/
syntax (name := rr_lw_recurrence_seq) "rr_lw_recurrence_seq " term : term

/-- Term `fun n => by simpa only [mul_assoc] using hrec n`, normalizing a recurrence certificate
`hrec` for every row up to associativity of multiplication. -/
syntax (name := rr_lw_recurrence_mul_assoc_seq) "rr_lw_recurrence_mul_assoc_seq " term : term

/-- Term `by simpa using h`, normalizing the certificate `h` to the expected form. -/
syntax (name := rr_lw_simpa) "rr_lw_simpa " term : term

macro_rules
  | `(rr_lw_recurrence_seq $hrec:term) =>
      `(fun n => by simpa using $hrec n)
  | `(rr_lw_recurrence_mul_assoc_seq $hrec:term) =>
      `(fun n => by simpa only [mul_assoc] using $hrec n)
  | `(rr_lw_simpa $h:term) =>
      `(by simpa using $h)

namespace Tactic

/-- Closes a nonnegativity side goal for a scalar coefficient by `rr_side_nonneg`. -/
syntax (name := rr_lw_coeff_nonneg) "rr_lw_coeff_nonneg" : tactic

macro_rules
  | `(tactic| rr_lw_coeff_nonneg) =>
      `(tactic| rr_side_nonneg)

/-- Term form of `rr_lw_coeff_nonneg`: elaborates to `by rr_lw_coeff_nonneg`. -/
syntax (name := rr_lw_coeff_nonneg_term) "rr_lw_coeff_nonneg_term" : term
/-- Term form of the sequence version of `rr_lw_coeff_nonneg`: elaborates to
`by rr_side_nonneg_seq`. -/
syntax (name := rr_lw_coeff_nonneg_seq_term) "rr_lw_coeff_nonneg_seq_term" : term

macro_rules
  | `(rr_lw_coeff_nonneg_term) =>
      `(by rr_lw_coeff_nonneg)
  | `(rr_lw_coeff_nonneg_seq_term) =>
      `(by rr_side_nonneg_seq)

/-- Closes the nonnegativity of a scalar coefficient at row `n`, such as `(n : ℝ) + 3`, as
`rr_scalar_active_nonneg_at n`. -/
macro "rr_lw_active_nonneg_at " n:term : tactic =>
  `(tactic| rr_scalar_active_nonneg_at $n)

/-- Introduces the row index `n` and closes the scalar nonnegativity side goal at row `n` by
`rr_lw_active_nonneg_at`. -/
macro "rr_lw_active_nonneg_seq" : tactic =>
  `(tactic| intro n <;> rr_lw_active_nonneg_at n)

/-- Closes the nonvanishing of the scalar denominators at every row, as
`rr_scalar_active_den_all`. -/
macro "rr_lw_active_den_all" : tactic =>
  `(tactic| rr_scalar_active_den_all)

/-- Closes a scalar coefficient identity at row `n` by field simplification, as
`rr_scalar_coeff_at n`. -/
macro "rr_lw_coeff_at " n:term : tactic =>
  `(tactic| rr_scalar_coeff_at $n)

/-- Closes a scalar coefficient identity at every row, as `rr_scalar_coeff_all`. -/
macro "rr_lw_coeff_all" : tactic =>
  `(tactic| rr_scalar_coeff_all)

/-- Refines the goal with the term `h` and closes the resulting scalar nonnegativity side goals by
`rr_lw_active_nonneg_seq`. -/
syntax (name := rr_lw_refine_active_nonneg_seq)
  "rr_lw_refine_active_nonneg_seq " term :
  tactic

macro_rules
  | `(tactic| rr_lw_refine_active_nonneg_seq $h:term) =>
      `(tactic| rr_refine_then $h with rr_lw_active_nonneg_seq)

/-- Closes a real-rootedness sequence goal from the term `h` by `rr_exact_realrooted_refine_then`,
closing the side goals by `rr_lw_active_nonneg_seq`. -/
syntax (name := rr_lw_exact_realrooted_active_nonneg_seq)
  "rr_lw_exact_realrooted_active_nonneg_seq " term :
  tactic

macro_rules
  | `(tactic| rr_lw_exact_realrooted_active_nonneg_seq $h:term) =>
      `(tactic| rr_exact_realrooted_refine_then $h with rr_lw_active_nonneg_seq)

/-- Term `fun n => by rr_lw_active_nonneg_at n`: scalar nonnegativity at every row. -/
syntax (name := rr_lw_active_nonneg) "rr_lw_active_nonneg" : term
/-- Term form of `rr_lw_active_den_all`: elaborates to `by rr_lw_active_den_all`. -/
syntax (name := rr_lw_active_den_all_term) "rr_lw_active_den_all_term" : term
/-- Term form of `rr_lw_coeff_at`: elaborates to `by rr_lw_coeff_at n`. -/
syntax (name := rr_lw_coeff_at_term) "rr_lw_coeff_at_term " term : term
/-- Term form of `rr_lw_coeff_all`: elaborates to `by rr_lw_coeff_all`. -/
syntax (name := rr_lw_coeff_all_term) "rr_lw_coeff_all_term" : term

macro_rules
  | `(rr_lw_active_nonneg) =>
      `(fun n => by rr_lw_active_nonneg_at n)
  | `(rr_lw_active_den_all_term) =>
      `(by rr_lw_active_den_all)
  | `(rr_lw_coeff_at_term $n:term) =>
      `(by rr_lw_coeff_at $n)
  | `(rr_lw_coeff_all_term) =>
      `(by rr_lw_coeff_all)

/-- Term `fun n => by simpa [add_comm, add_left_comm, add_assoc, mul_assoc] using hraw n`,
normalizing a raw recurrence certificate `hraw` for every row. -/
syntax (name := rr_lw_raw_recurrence_seq) "rr_lw_raw_recurrence_seq " term : term

macro_rules
  | `(rr_lw_raw_recurrence_seq $hraw:term) =>
      `(fun n => by
        simpa [add_comm, add_left_comm, add_assoc, mul_assoc] using $hraw n)

/-- Closes the discriminant side condition of a quadratic coefficient at row `n` by
`rr_lw_coeff_nonneg` or `nlinarith`. -/
macro "rr_lw_quadratic_discriminant_at " n:term : tactic =>
  `(tactic|
    solve
      | rr_lw_coeff_nonneg
      | nlinarith [sq_nonneg ($n : ℝ),
          sq_nonneg (($n : ℝ) + 1),
          sq_nonneg (($n : ℝ) + 2),
          show 0 ≤ ($n : ℝ) by positivity])

/-- Closes the side condition of a negative quadratic coefficient at row `n`, by
`rr_lw_active_nonneg_at n` or `rr_lw_quadratic_discriminant_at n`. -/
macro "rr_lw_negative_quadratic_side_at " n:term : tactic =>
  `(tactic|
    first
      | rr_lw_active_nonneg_at $n
      | rr_lw_quadratic_discriminant_at $n)

/-- Term `fun n => by rr_lw_quadratic_discriminant_at n`: the discriminant condition at every
row. -/
syntax (name := rr_lw_quadratic_discriminant) "rr_lw_quadratic_discriminant" : term
/-- Term `fun n => by rr_lw_negative_quadratic_side_at n`: the negative quadratic side condition at
every row. -/
syntax (name := rr_lw_negative_quadratic_side) "rr_lw_negative_quadratic_side" : term

macro_rules
  | `(rr_lw_quadratic_discriminant) =>
      `(fun n => by rr_lw_quadratic_discriminant_at n)
  | `(rr_lw_negative_quadratic_side) =>
      `(fun n => by rr_lw_negative_quadratic_side_at n)

/-- Closes `StrictInterl f (a * f + X * g)`, the unit positive `t`-lag step, from interlacing,
positive-leading-coefficient, nonpositive-root, degree, and no-common-root certificates, together
with `coeff_nonneg : 0 ≤ 1`. -/
syntax (name := rr_lw_positive_X_named)
  "rr_lw_positive_X" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "roots_nonpos" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `StrictInterl f (a * f + X * g)`, the unit positive `t`-lag step, from interlacing,
positive-leading-coefficient, nonpositive-root, degree, and no-common-root certificates. -/
syntax (name := rr_lw_positive_X_unit_alias_named)
  "rr_lw_positive_X" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "roots_nonpos" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Alias of `rr_lw_positive_X` without the `coeff_nonneg` argument. -/
syntax (name := rr_lw_positive_X_unit_named)
  "rr_lw_positive_X_unit" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "roots_nonpos" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_lw_positive_X using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        roots_nonpos := $hf_roots:term,
        coeff_nonneg := $hc:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        have _rr_lw_unit_coeff_nonneg : 0 ≤ (1 : ℝ) := $hc;
        rr_lw_positive_X using
          interlacer := $hgf,
          interlacer_pos_lc := $hg_pos,
          roots_nonpos := $hf_roots,
          target_pos_lc := $hF_pos,
          degree_lower := $hdeg_lo,
          degree_upper := $hdeg_hi,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_positive_X using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        roots_nonpos := $hf_roots:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_exact_or_simpa
          (RealRooted.LiuWang.strictInterl_positive_X_lag_of_roots_nonpos
            $hgf $hg_pos $hf_roots $hF_pos $hdeg_lo $hdeg_hi $hno),
          (RealRooted.LiuWang.strictInterl_positive_X_lag_of_roots_nonpos
            $hgf $hg_pos $hf_roots
            (rr_lw_simpa $hF_pos)
            (rr_lw_simpa $hdeg_lo)
            (rr_lw_simpa $hdeg_hi)
            $hno))
  | `(tactic|
      rr_lw_positive_X_unit using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        roots_nonpos := $hf_roots:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_positive_X using
          interlacer := $hgf,
          interlacer_pos_lc := $hg_pos,
          roots_nonpos := $hf_roots,
          target_pos_lc := $hF_pos,
          degree_lower := $hdeg_lo,
          degree_upper := $hdeg_hi,
          no_common_roots := $hno)

end Tactic
end RealRooted
