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

@[expose] public section

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

/-- Term `by simpa [mul_assoc] using h`, normalizing the certificate `h` up to associativity of
multiplication. -/
syntax (name := rr_lw_simpa_mul_assoc) "rr_lw_simpa_mul_assoc " term : term

macro_rules
  | `(rr_lw_recurrence_seq $hrec:term) =>
      `(fun n => by simpa using $hrec n)
  | `(rr_lw_recurrence_mul_assoc_seq $hrec:term) =>
      `(fun n => by simpa only [mul_assoc] using $hrec n)
  | `(rr_lw_simpa $h:term) =>
      `(by simpa using $h)
  | `(rr_lw_simpa_mul_assoc $h:term) =>
      `(by simpa [mul_assoc] using $h)

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

/-- Positional form of `rr_liu_wang`, taking the ten certificates in the order of its named form. -/
syntax (name := rr_liu_wang)
  "rr_liu_wang" " using " term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term :
  tactic

/-- Closes `StrictInterl f (a * f + polynomialWeightedSum ((b, g) :: l))` by the generalized
Liu--Wang theorem. The arguments are `interlacer : Interlaces g f` with `interlacer_pos_lc`,
`target_pos_lc` for the target polynomial, `degree_lower` and `degree_upper` bounding its degree
between `f.natDegree` and `f.natDegree + 1`, and `no_common_roots` for `f` and `g`;
`tail_interlaces`, `tail_pos_lc` and `tail_nonpos` describe the remaining summands (each interlaces
`f`, has positive leading coefficient, and its coefficient is nonpositive at the roots of `f`), and
`head_nonpos` says that `b` is nonpositive at the roots of `f`. -/
syntax (name := rr_liu_wang_named)
  "rr_liu_wang" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "tail_interlaces" ":=" term ","
    "tail_pos_lc" ":=" term ","
    "tail_nonpos" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term ","
    "head_nonpos" ":=" term :
  tactic

/-- Positional form of `rr_liu_wang_strict`, taking the ten certificates in the order of its named
form. -/
syntax (name := rr_liu_wang_strict)
  "rr_liu_wang_strict" " using " term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term :
  tactic

/-- Strict version of `rr_liu_wang`: the head coefficient `b` is negative at the roots of `f`
(`head_neg`), and the other arguments are as for `rr_liu_wang`. -/
syntax (name := rr_liu_wang_strict_named)
  "rr_liu_wang_strict" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "tail_interlaces" ":=" term ","
    "tail_pos_lc" ":=" term ","
    "tail_nonpos" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term ","
    "head_neg" ":=" term :
  tactic

/-- Positional form of `rr_liu_wang_strict_same`, taking the nine certificates in the order of its
named form. -/
syntax (name := rr_liu_wang_strict_same)
  "rr_liu_wang_strict_same" " using " term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term :
  tactic

/-- Version of `rr_liu_wang_strict` for a target of the same degree as `f`: `degree` replaces
`degree_lower` and `degree_upper`. -/
syntax (name := rr_liu_wang_strict_same_named)
  "rr_liu_wang_strict_same" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "tail_interlaces" ":=" term ","
    "tail_pos_lc" ":=" term ","
    "tail_nonpos" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree" ":=" term ","
    "no_common_roots" ":=" term ","
    "head_neg" ":=" term :
  tactic

/-- Positional form of `rr_liu_wang_strict_succ`, taking the nine certificates in the order of its
named form. -/
syntax (name := rr_liu_wang_strict_succ)
  "rr_liu_wang_strict_succ" " using " term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term :
  tactic

/-- Version of `rr_liu_wang_strict` for a target of degree `f.natDegree + 1`: `degree` replaces
`degree_lower` and `degree_upper`. -/
syntax (name := rr_liu_wang_strict_succ_named)
  "rr_liu_wang_strict_succ" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "tail_interlaces" ":=" term ","
    "tail_pos_lc" ":=" term ","
    "tail_nonpos" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree" ":=" term ","
    "no_common_roots" ":=" term ","
    "head_neg" ":=" term :
  tactic

/-- Closes `StrictInterl f (a * f + b * g)`, the two-polynomial Liu--Wang step. The arguments are
`interlacer : Interlaces g f` with `interlacer_pos_lc`, `target_pos_lc` for the target polynomial,
`degree_lower` and `degree_upper` bounding its degree between `f.natDegree` and `f.natDegree + 1`,
and `no_common_roots` for `f` and `g`, and `head_nonpos` says that `b` is nonpositive at the roots
of `f`. -/
syntax (name := rr_liu_wang_two_named)
  "rr_liu_wang_two" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term ","
    "head_nonpos" ":=" term :
  tactic

/-- Strict version of `rr_liu_wang_two`: the coefficient `b` is negative at the roots of `f`
(`head_neg`). -/
syntax (name := rr_liu_wang_two_strict_named)
  "rr_liu_wang_two_strict" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term ","
    "head_neg" ":=" term :
  tactic

/-- Version of `rr_liu_wang_two_strict` for a target of the same degree as `f`: `degree` replaces
`degree_lower` and `degree_upper`. -/
syntax (name := rr_liu_wang_two_strict_same_named)
  "rr_liu_wang_two_strict_same" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree" ":=" term ","
    "no_common_roots" ":=" term ","
    "head_neg" ":=" term :
  tactic

/-- Version of `rr_liu_wang_two_strict` for a target of degree `f.natDegree + 1`: `degree` replaces
`degree_lower` and `degree_upper`. -/
syntax (name := rr_liu_wang_two_strict_succ_named)
  "rr_liu_wang_two_strict_succ" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree" ":=" term ","
    "no_common_roots" ":=" term ","
    "head_neg" ":=" term :
  tactic

/-- Version of `rr_liu_wang_two_strict` where `degree_branch` states that the target degree is
either `f.natDegree` or `f.natDegree + 1`. -/
syntax (name := rr_liu_wang_two_strict_branch_named)
  "rr_liu_wang_two_strict_branch" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_branch" ":=" term ","
    "no_common_roots" ":=" term ","
    "head_neg" ":=" term :
  tactic

/-- Closes `StrictInterl f (a * f + (C c * X) * g)`, a positive `t`-lag step. The arguments are
`interlacer : Interlaces g f` with `interlacer_pos_lc`, `target_pos_lc` for the target polynomial,
`degree_lower` and `degree_upper` bounding its degree between `f.natDegree` and `f.natDegree + 1`,
and `no_common_roots` for `f` and `g`; `roots_nonpos` says that all roots of `f` are nonpositive and
`coeff_nonneg : 0 ≤ c`. -/
syntax (name := rr_lw_positive_t_named)
  "rr_lw_positive_t" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "roots_nonpos" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Version of `rr_lw_positive_t` that proves `coeff_nonneg` by `rr_lw_coeff_nonneg_term`. -/
syntax (name := rr_lw_positive_t_auto_named)
  "rr_lw_positive_t_auto" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "roots_nonpos" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `StrictInterl f (a * f + X * g)`, the unit positive `t`-lag step. The arguments are as
for `rr_lw_positive_t`, with `coeff_nonneg : 0 ≤ 1`. -/
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

/-- Closes `StrictInterl f (a * f + X * g)`, the unit positive `t`-lag step, from the arguments of
`rr_lw_positive_t` without `coeff_nonneg`. -/
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

/-- Version of `rr_lw_positive_t` that derives the nonpositivity of the roots of `f` from
`nonneg_coeffs : HasNonnegCoeffs f`. -/
syntax (name := rr_lw_positive_t_nonneg_named)
  "rr_lw_positive_t_nonneg" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Version of `rr_lw_positive_t_nonneg` that proves `coeff_nonneg` by `rr_lw_coeff_nonneg_term`. -/
syntax (name := rr_lw_positive_t_nonneg_auto_named)
  "rr_lw_positive_t_nonneg_auto" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `StrictInterl f (a * f + (X * q) * g)`, a positive `t Q(t)` lag step. The arguments are
as for `rr_lw_positive_t`, without `coeff_nonneg` and with `factor_nonneg`, which says that `q` is
nonnegative at the roots of `f`. -/
syntax (name := rr_lw_positive_X_mul_named)
  "rr_lw_positive_X_mul" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "roots_nonpos" ":=" term ","
    "factor_nonneg" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `StrictInterl f (a * f + (C c * X * q) * g)`, a positive `c t Q(t)` lag step. The
arguments are as for `rr_lw_positive_X_mul`, together with `coeff_nonneg : 0 ≤ c`. -/
syntax (name := rr_lw_positive_C_mul_X_mul_named)
  "rr_lw_positive_C_mul_X_mul" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "roots_nonpos" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "factor_nonneg" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Version of `rr_lw_positive_X_mul` that derives the nonpositivity of the roots of `f` from
`nonneg_coeffs : HasNonnegCoeffs f`. -/
syntax (name := rr_lw_positive_X_mul_nonneg_named)
  "rr_lw_positive_X_mul_nonneg" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "factor_nonneg" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Version of `rr_lw_positive_C_mul_X_mul` that derives the nonpositivity of the roots of `f` from
`nonneg_coeffs : HasNonnegCoeffs f`. -/
syntax (name := rr_lw_positive_C_mul_X_mul_nonneg_named)
  "rr_lw_positive_C_mul_X_mul_nonneg" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "factor_nonneg" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Version of `rr_lw_positive_C_mul_X_mul_nonneg` that proves `coeff_nonneg` by
`rr_lw_coeff_nonneg_term`. -/
syntax (name := rr_lw_positive_C_mul_X_mul_nonneg_auto_named)
  "rr_lw_positive_C_mul_X_mul_nonneg_auto" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "factor_nonneg" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `StrictInterl f (a * f + (-(C c) * q ^ 2) * g)`, a negative-square lag step that is
nonpositive everywhere. The arguments are `interlacer : Interlaces g f` with `interlacer_pos_lc`,
`target_pos_lc`, `degree_lower`, `degree_upper` and `no_common_roots`, as in `rr_liu_wang_two`, and
`coeff_nonneg : 0 ≤ c`. -/
syntax (name := rr_lw_negative_square_named)
  "rr_lw_negative_square" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Version of `rr_lw_negative_square` that proves `coeff_nonneg` by `rr_lw_coeff_nonneg_term`. -/
syntax (name := rr_lw_negative_square_auto_named)
  "rr_lw_negative_square_auto" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `StrictInterl f (a * f + (-(X ^ 2 + C b * X + C c)) * g)`, a negative monic quadratic lag
step. The arguments are `interlacer : Interlaces g f` with `interlacer_pos_lc`, `target_pos_lc`,
`degree_lower`, `degree_upper` and `no_common_roots`, as in `rr_liu_wang_two`, and
`discriminant : b ^ 2 ≤ 4 * c`. -/
syntax (name := rr_lw_negative_monic_quadratic_named)
  "rr_lw_negative_monic_quadratic" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "discriminant" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Version of `rr_lw_negative_monic_quadratic` that proves the discriminant condition by
`rr_lw_coeff_nonneg_term`. -/
syntax (name := rr_lw_negative_monic_quadratic_auto_named)
  "rr_lw_negative_monic_quadratic_auto" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `StrictInterl f (A * f + (-(C a * X ^ 2 + C b * X + C c)) * g)`, a negative quadratic lag
step. The arguments are `interlacer : Interlaces g f` with `interlacer_pos_lc`, `target_pos_lc`,
`degree_lower`, `degree_upper` and `no_common_roots`, as in `rr_liu_wang_two`,
`leading_nonneg : 0 ≤ a`, `constant_nonneg : 0 ≤ c` and `discriminant : b ^ 2 ≤ 4 * a * c`. -/
syntax (name := rr_lw_negative_quadratic_named)
  "rr_lw_negative_quadratic" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "leading_nonneg" ":=" term ","
    "constant_nonneg" ":=" term ","
    "discriminant" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Version of `rr_lw_negative_quadratic` that proves the sign and discriminant conditions by
`rr_lw_coeff_nonneg_term`. -/
syntax (name := rr_lw_negative_quadratic_auto_named)
  "rr_lw_negative_quadratic_auto" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `StrictInterl f (a * f + (-(C c)) * g)`, a negative constant lag step. The arguments are
`interlacer : Interlaces g f` with `interlacer_pos_lc`, `target_pos_lc`, `degree_lower`,
`degree_upper` and `no_common_roots`, as in `rr_liu_wang_two`, and `coeff_nonneg : 0 ≤ c`. -/
syntax (name := rr_lw_negative_const_named)
  "rr_lw_negative_const" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Version of `rr_lw_negative_const` that proves `coeff_nonneg` by `rr_lw_coeff_nonneg_term`. -/
syntax (name := rr_lw_negative_const_auto_named)
  "rr_lw_negative_const_auto" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Version of `rr_lw_negative_const` for the normalized coefficient form `C (-c) * g`. -/
syntax (name := rr_lw_negative_const_C_neg_named)
  "rr_lw_negative_const_C_neg" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Version of `rr_lw_negative_const_C_neg` that proves `coeff_nonneg` by
`rr_lw_coeff_nonneg_term`. -/
syntax (name := rr_lw_negative_const_C_neg_auto_named)
  "rr_lw_negative_const_C_neg_auto" " using "
    "interlacer" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "target_pos_lc" ":=" term ","
    "degree_lower" ":=" term ","
    "degree_upper" ":=" term ","
    "no_common_roots" ":=" term :
  tactic

/-- Closes `StrictInterl f (a * f + b * g)` for a target `F` given by the `recurrence`
`F = a * f + b * g`. The arguments are `interlaces : Interlaces g f` with `interlacer_pos_lc`,
`target_pos_lc : HasPosLeadingCoeff F`, `degree_succ : f.natDegree + 1 = F.natDegree`,
`no_common_roots` for `f` and `g`, and `lag_nonpos`, which says that `b` is nonpositive at the roots
of `f`. -/
syntax (name := rr_lw_nonpos_lag_step_named)
  "rr_lw_nonpos_lag_step" " using "
    "interlaces" ":=" term ","
    "interlacer_pos_lc" ":=" term ","
    "target_pos_lc" ":=" term ","
    "recurrence" ":=" term ","
    "degree_succ" ":=" term ","
    "no_common_roots" ":=" term ","
    "lag_nonpos" ":=" term :
  tactic

/-- Closes the goal by `exact` of the first term or, failing that, by `simpa using` the second
term. -/
syntax (name := rr_lw_exact_or_simpa)
  "rr_lw_exact_or_simpa" term ", " term :
  tactic

/-- Closes the goal by `exact` of the first term or, failing that, by `simpa [mul_assoc] using` the
second term. -/
syntax (name := rr_lw_exact_or_simpa_mul_assoc)
  "rr_lw_exact_or_simpa_mul_assoc" term ", " term :
  tactic

macro_rules
  | `(tactic| rr_lw_exact_or_simpa $hdirect:term, $hnormalized:term) =>
      `(tactic|
        rr_first_exact_or_simpa $hdirect, $hnormalized)
  | `(tactic| rr_lw_exact_or_simpa_mul_assoc $hdirect:term, $hnormalized:term) =>
      `(tactic|
        rr_first_exact_or_simpa_mul_assoc $hdirect, $hnormalized)
  | `(tactic|
      rr_liu_wang using
        $hgf:term, $hg_pos:term, $hl_inter:term, $hl_pos:term, $hl_nonpos:term,
        $hF_pos:term, $hdeg_lo:term, $hdeg_hi:term, $hno:term, $hb_nonpos:term) =>
      `(tactic|
        simpa using
          (RealRooted.strictInterl_generalizedLiuWang_of_no_common
            (rr_lw_simpa $hgf)
            (rr_lw_simpa $hg_pos)
            (rr_lw_simpa $hl_inter)
            (rr_lw_simpa $hl_pos)
            (rr_lw_simpa $hl_nonpos)
            (rr_lw_simpa $hF_pos)
            (rr_lw_simpa $hdeg_lo)
            (rr_lw_simpa $hdeg_hi)
            (rr_lw_simpa $hno)
            (rr_lw_simpa $hb_nonpos)))
  | `(tactic|
      rr_liu_wang using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        tail_interlaces := $hl_inter:term,
        tail_pos_lc := $hl_pos:term,
        tail_nonpos := $hl_nonpos:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term,
        head_nonpos := $hb_nonpos:term) =>
      `(tactic|
        rr_liu_wang using
          $hgf, $hg_pos, $hl_inter, $hl_pos, $hl_nonpos, $hF_pos, $hdeg_lo,
          $hdeg_hi, $hno, $hb_nonpos)
  | `(tactic|
      rr_liu_wang_strict using
        $hgf:term, $hg_pos:term, $hl_inter:term, $hl_pos:term, $hl_nonpos:term,
        $hF_pos:term, $hdeg_lo:term, $hdeg_hi:term, $hno:term, $hb_neg:term) =>
      `(tactic|
        simpa using
          (RealRooted.strictInterl_generalizedLiuWang_strict
            (rr_lw_simpa $hgf)
            (rr_lw_simpa $hg_pos)
            (rr_lw_simpa $hl_inter)
            (rr_lw_simpa $hl_pos)
            (rr_lw_simpa $hl_nonpos)
            (rr_lw_simpa $hF_pos)
            (rr_lw_simpa $hdeg_lo)
            (rr_lw_simpa $hdeg_hi)
            (rr_lw_simpa $hno)
            (rr_lw_simpa $hb_neg)))
  | `(tactic|
      rr_liu_wang_strict using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        tail_interlaces := $hl_inter:term,
        tail_pos_lc := $hl_pos:term,
        tail_nonpos := $hl_nonpos:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term,
        head_neg := $hb_neg:term) =>
      `(tactic|
        rr_liu_wang_strict using
          $hgf, $hg_pos, $hl_inter, $hl_pos, $hl_nonpos, $hF_pos, $hdeg_lo,
          $hdeg_hi, $hno, $hb_neg)
  | `(tactic|
      rr_liu_wang_strict_same using
        $hgf:term, $hg_pos:term, $hl_inter:term, $hl_pos:term, $hl_nonpos:term,
        $hF_pos:term, $hdeg:term, $hno:term, $hb_neg:term) =>
      `(tactic|
        simpa using
          (RealRooted.strictInterl_generalizedLiuWang_strict_same
            (rr_lw_simpa $hgf)
            (rr_lw_simpa $hg_pos)
            (rr_lw_simpa $hl_inter)
            (rr_lw_simpa $hl_pos)
            (rr_lw_simpa $hl_nonpos)
            (rr_lw_simpa $hF_pos)
            (rr_lw_simpa $hdeg)
            (rr_lw_simpa $hno)
            (rr_lw_simpa $hb_neg)))
  | `(tactic|
      rr_liu_wang_strict_same using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        tail_interlaces := $hl_inter:term,
        tail_pos_lc := $hl_pos:term,
        tail_nonpos := $hl_nonpos:term,
        target_pos_lc := $hF_pos:term,
        degree := $hdeg:term,
        no_common_roots := $hno:term,
        head_neg := $hb_neg:term) =>
      `(tactic|
        rr_liu_wang_strict_same using
          $hgf, $hg_pos, $hl_inter, $hl_pos, $hl_nonpos, $hF_pos, $hdeg,
          $hno, $hb_neg)
  | `(tactic|
      rr_liu_wang_strict_succ using
        $hgf:term, $hg_pos:term, $hl_inter:term, $hl_pos:term, $hl_nonpos:term,
        $hF_pos:term, $hdeg:term, $hno:term, $hb_neg:term) =>
      `(tactic|
        simpa using
          (RealRooted.strictInterl_generalizedLiuWang_strict_succ
            (rr_lw_simpa $hgf)
            (rr_lw_simpa $hg_pos)
            (rr_lw_simpa $hl_inter)
            (rr_lw_simpa $hl_pos)
            (rr_lw_simpa $hl_nonpos)
            (rr_lw_simpa $hF_pos)
            (rr_lw_simpa $hdeg)
            (rr_lw_simpa $hno)
            (rr_lw_simpa $hb_neg)))
  | `(tactic|
      rr_liu_wang_strict_succ using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        tail_interlaces := $hl_inter:term,
        tail_pos_lc := $hl_pos:term,
        tail_nonpos := $hl_nonpos:term,
        target_pos_lc := $hF_pos:term,
        degree := $hdeg:term,
        no_common_roots := $hno:term,
        head_neg := $hb_neg:term) =>
      `(tactic|
        rr_liu_wang_strict_succ using
          $hgf, $hg_pos, $hl_inter, $hl_pos, $hl_nonpos, $hF_pos, $hdeg,
          $hno, $hb_neg)
  | `(tactic|
      rr_liu_wang_two using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term,
        head_nonpos := $hb_nonpos:term) =>
      `(tactic|
        rr_first_exact_or_simpa
          (RealRooted.LiuWang.strictInterl_two_of_nonpos
            $hgf $hg_pos $hF_pos $hdeg_lo $hdeg_hi $hno $hb_nonpos),
          (RealRooted.LiuWang.strictInterl_two_of_nonpos
            $hgf $hg_pos
            (rr_lw_simpa $hF_pos)
            (rr_lw_simpa $hdeg_lo)
            (rr_lw_simpa $hdeg_hi)
            $hno
            (rr_lw_simpa $hb_nonpos)))
  | `(tactic|
      rr_liu_wang_two_strict using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term,
        head_neg := $hb_neg:term) =>
      `(tactic|
        rr_first_exact_or_simpa
          (RealRooted.MaWangInternal.strictInterl_of_interlaces_evalCoeff_neg
            $hgf $hg_pos $hF_pos $hdeg_lo $hdeg_hi $hno $hb_neg),
          (RealRooted.MaWangInternal.strictInterl_of_interlaces_evalCoeff_neg
            $hgf $hg_pos
            (rr_lw_simpa $hF_pos)
            (rr_lw_simpa $hdeg_lo)
            (rr_lw_simpa $hdeg_hi)
            $hno
            (rr_lw_simpa $hb_neg)))
  | `(tactic|
      rr_liu_wang_two_strict_same using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        target_pos_lc := $hF_pos:term,
        degree := $hdeg:term,
        no_common_roots := $hno:term,
        head_neg := $hb_neg:term) =>
      `(tactic|
        rr_first_exact_or_simpa
          (RealRooted.MaWangInternal.strictInterl_of_interlaces_evalCoeff_neg_same
            $hgf $hg_pos $hF_pos $hdeg $hno $hb_neg),
          (RealRooted.MaWangInternal.strictInterl_of_interlaces_evalCoeff_neg_same
            $hgf $hg_pos
            (rr_lw_simpa $hF_pos)
            (rr_lw_simpa $hdeg)
            $hno
            (rr_lw_simpa $hb_neg)))
  | `(tactic|
      rr_liu_wang_two_strict_succ using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        target_pos_lc := $hF_pos:term,
        degree := $hdeg:term,
        no_common_roots := $hno:term,
        head_neg := $hb_neg:term) =>
      `(tactic|
        rr_first_exact_or_simpa
          (RealRooted.MaWangInternal.strictInterl_of_interlaces_evalCoeff_neg_succ
            $hgf $hg_pos $hF_pos $hdeg $hno $hb_neg),
          (RealRooted.MaWangInternal.strictInterl_of_interlaces_evalCoeff_neg_succ
            $hgf $hg_pos
            (rr_lw_simpa $hF_pos)
            (rr_lw_simpa $hdeg)
            $hno
            (rr_lw_simpa $hb_neg)))
  | `(tactic|
      rr_liu_wang_two_strict_branch using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        target_pos_lc := $hF_pos:term,
        degree_branch := $hdegree:term,
        no_common_roots := $hno:term,
        head_neg := $hb_neg:term) =>
      `(tactic|
        rr_first_exact_or_simpa
          (RealRooted.LiuWang.strictInterl_two_strict_branch_of_neg
            $hgf $hg_pos $hF_pos $hdegree $hno $hb_neg),
          (RealRooted.LiuWang.strictInterl_two_strict_branch_of_neg
            $hgf $hg_pos
            (rr_lw_simpa $hF_pos)
            (rr_lw_simpa $hdegree)
            $hno
            (rr_lw_simpa $hb_neg)))
  | `(tactic|
      rr_lw_positive_t using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        roots_nonpos := $hf_roots:term,
        coeff_nonneg := $hc:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_exact_or_simpa
          (RealRooted.LiuWang.strictInterl_positive_t_lag_of_roots_nonpos
            $hgf $hg_pos $hf_roots $hc $hF_pos $hdeg_lo $hdeg_hi $hno),
          (RealRooted.LiuWang.strictInterl_positive_t_lag_of_roots_nonpos
            $hgf $hg_pos $hf_roots $hc
            (rr_lw_simpa $hF_pos)
            (rr_lw_simpa $hdeg_lo)
            (rr_lw_simpa $hdeg_hi)
            $hno))
  | `(tactic|
      rr_lw_positive_t_auto using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        roots_nonpos := $hf_roots:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_positive_t using
          interlacer := $hgf,
          interlacer_pos_lc := $hg_pos,
          roots_nonpos := $hf_roots,
          coeff_nonneg := rr_lw_coeff_nonneg_term,
          target_pos_lc := $hF_pos,
          degree_lower := $hdeg_lo,
          degree_upper := $hdeg_hi,
          no_common_roots := $hno)
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
  | `(tactic|
      rr_lw_positive_t_nonneg using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        nonneg_coeffs := $hf_nonneg:term,
        coeff_nonneg := $hc:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_exact_or_simpa
          (RealRooted.LiuWang.strictInterl_positive_t_lag_of_nonneg_coeffs
            $hgf $hg_pos $hf_nonneg $hc $hF_pos $hdeg_lo $hdeg_hi $hno),
          (RealRooted.LiuWang.strictInterl_positive_t_lag_of_nonneg_coeffs
            $hgf $hg_pos $hf_nonneg $hc
            (rr_lw_simpa $hF_pos)
            (rr_lw_simpa $hdeg_lo)
            (rr_lw_simpa $hdeg_hi)
            $hno))
  | `(tactic|
      rr_lw_positive_t_nonneg_auto using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        nonneg_coeffs := $hf_nonneg:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_lw_positive_t_nonneg using
          interlacer := $hgf,
          interlacer_pos_lc := $hg_pos,
          nonneg_coeffs := $hf_nonneg,
          coeff_nonneg := rr_lw_coeff_nonneg_term,
          target_pos_lc := $hF_pos,
          degree_lower := $hdeg_lo,
          degree_upper := $hdeg_hi,
          no_common_roots := $hno)
  | `(tactic|
      rr_lw_positive_X_mul using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        roots_nonpos := $hf_roots:term,
        factor_nonneg := $hQ:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_exact_or_simpa_mul_assoc
          (RealRooted.LiuWang.strictInterl_positive_X_mul_lag_of_roots_nonpos
            $hgf $hg_pos $hf_roots $hQ $hF_pos $hdeg_lo $hdeg_hi $hno),
          (RealRooted.LiuWang.strictInterl_positive_X_mul_lag_of_roots_nonpos
            $hgf $hg_pos $hf_roots $hQ
            (rr_lw_simpa_mul_assoc $hF_pos)
            (rr_lw_simpa_mul_assoc $hdeg_lo)
            (rr_lw_simpa_mul_assoc $hdeg_hi)
            $hno))
  | `(tactic|
      rr_lw_positive_C_mul_X_mul using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        roots_nonpos := $hf_roots:term,
        coeff_nonneg := $hc:term,
        factor_nonneg := $hQ:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_exact_or_simpa_mul_assoc
          (RealRooted.LiuWang.strictInterl_positive_C_mul_X_mul_lag_of_roots_nonpos
            $hgf $hg_pos $hf_roots $hc $hQ $hF_pos $hdeg_lo $hdeg_hi $hno),
          (RealRooted.LiuWang.strictInterl_positive_C_mul_X_mul_lag_of_roots_nonpos
            $hgf $hg_pos $hf_roots $hc $hQ
            (rr_lw_simpa_mul_assoc $hF_pos)
            (rr_lw_simpa_mul_assoc $hdeg_lo)
            (rr_lw_simpa_mul_assoc $hdeg_hi)
            $hno))
  | `(tactic|
      rr_lw_positive_X_mul_nonneg using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        nonneg_coeffs := $hf_nonneg:term,
        factor_nonneg := $hQ:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_exact_or_simpa_mul_assoc
          (RealRooted.LiuWang.strictInterl_positive_X_mul_lag_of_nonneg_coeffs
            $hgf $hg_pos $hf_nonneg $hQ $hF_pos $hdeg_lo $hdeg_hi $hno),
          (RealRooted.LiuWang.strictInterl_positive_X_mul_lag_of_nonneg_coeffs
            $hgf $hg_pos $hf_nonneg $hQ
            (rr_lw_simpa_mul_assoc $hF_pos)
            (rr_lw_simpa_mul_assoc $hdeg_lo)
            (rr_lw_simpa_mul_assoc $hdeg_hi)
            $hno))
  | `(tactic|
      rr_lw_positive_C_mul_X_mul_nonneg using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        nonneg_coeffs := $hf_nonneg:term,
        coeff_nonneg := $hc:term,
        factor_nonneg := $hQ:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_exact_or_simpa_mul_assoc
          (RealRooted.LiuWang.strictInterl_positive_C_mul_X_mul_lag_of_nonneg_coeffs
            $hgf $hg_pos $hf_nonneg $hc $hQ $hF_pos $hdeg_lo $hdeg_hi $hno),
          (RealRooted.LiuWang.strictInterl_positive_C_mul_X_mul_lag_of_nonneg_coeffs
            $hgf $hg_pos $hf_nonneg $hc $hQ
            (rr_lw_simpa_mul_assoc $hF_pos)
            (rr_lw_simpa_mul_assoc $hdeg_lo)
            (rr_lw_simpa_mul_assoc $hdeg_hi)
            $hno))
  | `(tactic|
      rr_lw_positive_C_mul_X_mul_nonneg_auto using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        nonneg_coeffs := $hf_nonneg:term,
        factor_nonneg := $hQ:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_exact_or_simpa_mul_assoc
          (RealRooted.LiuWang.strictInterl_positive_C_mul_X_mul_lag_of_nonneg_coeffs
            $hgf $hg_pos $hf_nonneg rr_lw_coeff_nonneg_term $hQ
            $hF_pos $hdeg_lo $hdeg_hi $hno),
          (RealRooted.LiuWang.strictInterl_positive_C_mul_X_mul_lag_of_nonneg_coeffs
            $hgf $hg_pos $hf_nonneg rr_lw_coeff_nonneg_term $hQ
            (rr_lw_simpa_mul_assoc $hF_pos)
            (rr_lw_simpa_mul_assoc $hdeg_lo)
            (rr_lw_simpa_mul_assoc $hdeg_hi)
            $hno))
  | `(tactic|
      rr_lw_negative_square using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        coeff_nonneg := $hc:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_exact_or_simpa
          (RealRooted.LiuWang.strictInterl_negative_square_lag
            $hgf $hg_pos $hc $hF_pos $hdeg_lo $hdeg_hi $hno),
          (RealRooted.LiuWang.strictInterl_negative_square_lag
            $hgf $hg_pos $hc
            (rr_lw_simpa $hF_pos)
            (rr_lw_simpa $hdeg_lo)
            (rr_lw_simpa $hdeg_hi)
            $hno))
  | `(tactic|
      rr_lw_negative_square_auto using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_exact_or_simpa
          (RealRooted.LiuWang.strictInterl_negative_square_lag
            $hgf $hg_pos rr_lw_coeff_nonneg_term $hF_pos $hdeg_lo $hdeg_hi $hno),
          (RealRooted.LiuWang.strictInterl_negative_square_lag
            $hgf $hg_pos rr_lw_coeff_nonneg_term
            (rr_lw_simpa $hF_pos)
            (rr_lw_simpa $hdeg_lo)
            (rr_lw_simpa $hdeg_hi)
            $hno))
  | `(tactic|
      rr_lw_negative_monic_quadratic using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        discriminant := $hdisc:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_exact_or_simpa
          (RealRooted.LiuWang.strictInterl_negative_monic_quadratic_lag
            $hgf $hg_pos $hdisc $hF_pos $hdeg_lo $hdeg_hi $hno),
          (RealRooted.LiuWang.strictInterl_negative_monic_quadratic_lag
            $hgf $hg_pos $hdisc
            (rr_lw_simpa $hF_pos)
            (rr_lw_simpa $hdeg_lo)
            (rr_lw_simpa $hdeg_hi)
            $hno))
  | `(tactic|
      rr_lw_negative_monic_quadratic_auto using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_exact_or_simpa
          (RealRooted.LiuWang.strictInterl_negative_monic_quadratic_lag
            $hgf $hg_pos rr_lw_coeff_nonneg_term $hF_pos $hdeg_lo $hdeg_hi $hno),
          (RealRooted.LiuWang.strictInterl_negative_monic_quadratic_lag
            $hgf $hg_pos rr_lw_coeff_nonneg_term
            (rr_lw_simpa $hF_pos)
            (rr_lw_simpa $hdeg_lo)
            (rr_lw_simpa $hdeg_hi)
            $hno))
  | `(tactic|
      rr_lw_negative_quadratic using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        leading_nonneg := $ha:term,
        constant_nonneg := $hc:term,
        discriminant := $hdisc:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_exact_or_simpa
          (RealRooted.LiuWang.strictInterl_negative_quadratic_lag
            $hgf $hg_pos $ha $hc $hdisc $hF_pos $hdeg_lo $hdeg_hi $hno),
          (RealRooted.LiuWang.strictInterl_negative_quadratic_lag
            $hgf $hg_pos $ha $hc $hdisc
            (rr_lw_simpa $hF_pos)
            (rr_lw_simpa $hdeg_lo)
            (rr_lw_simpa $hdeg_hi)
            $hno))
  | `(tactic|
      rr_lw_negative_quadratic_auto using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_exact_or_simpa
          (RealRooted.LiuWang.strictInterl_negative_quadratic_lag
            $hgf $hg_pos
            rr_lw_coeff_nonneg_term rr_lw_coeff_nonneg_term rr_lw_coeff_nonneg_term
            $hF_pos $hdeg_lo $hdeg_hi $hno),
          (RealRooted.LiuWang.strictInterl_negative_quadratic_lag
            $hgf $hg_pos
            rr_lw_coeff_nonneg_term rr_lw_coeff_nonneg_term rr_lw_coeff_nonneg_term
            (rr_lw_simpa $hF_pos)
            (rr_lw_simpa $hdeg_lo)
            (rr_lw_simpa $hdeg_hi)
            $hno))
  | `(tactic|
      rr_lw_negative_const using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        coeff_nonneg := $hc:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_exact_or_simpa
          (RealRooted.LiuWang.strictInterl_negative_const_lag
            $hgf $hg_pos $hc $hF_pos $hdeg_lo $hdeg_hi $hno),
          (RealRooted.LiuWang.strictInterl_negative_const_lag
            $hgf $hg_pos $hc
            (rr_lw_simpa $hF_pos)
            (rr_lw_simpa $hdeg_lo)
            (rr_lw_simpa $hdeg_hi)
            $hno))
  | `(tactic|
      rr_lw_negative_const_auto using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_exact_or_simpa
          (RealRooted.LiuWang.strictInterl_negative_const_lag
            $hgf $hg_pos rr_lw_coeff_nonneg_term $hF_pos $hdeg_lo $hdeg_hi $hno),
          (RealRooted.LiuWang.strictInterl_negative_const_lag
            $hgf $hg_pos rr_lw_coeff_nonneg_term
            (rr_lw_simpa $hF_pos)
            (rr_lw_simpa $hdeg_lo)
            (rr_lw_simpa $hdeg_hi)
            $hno))
  | `(tactic|
      rr_lw_negative_const_C_neg using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        coeff_nonneg := $hc:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_exact_or_simpa
          (RealRooted.LiuWang.strictInterl_negative_const_lag_C_neg
            $hgf $hg_pos $hc $hF_pos $hdeg_lo $hdeg_hi $hno),
          (RealRooted.LiuWang.strictInterl_negative_const_lag_C_neg
            $hgf $hg_pos $hc
            (rr_lw_simpa $hF_pos)
            (rr_lw_simpa $hdeg_lo)
            (rr_lw_simpa $hdeg_hi)
            $hno))
  | `(tactic|
      rr_lw_negative_const_C_neg_auto using
        interlacer := $hgf:term,
        interlacer_pos_lc := $hg_pos:term,
        target_pos_lc := $hF_pos:term,
        degree_lower := $hdeg_lo:term,
        degree_upper := $hdeg_hi:term,
        no_common_roots := $hno:term) =>
      `(tactic|
        rr_first_exact_or_simpa
          (RealRooted.LiuWang.strictInterl_negative_const_lag_C_neg
            $hgf $hg_pos rr_lw_coeff_nonneg_term $hF_pos $hdeg_lo $hdeg_hi $hno),
          (RealRooted.LiuWang.strictInterl_negative_const_lag_C_neg
            $hgf $hg_pos rr_lw_coeff_nonneg_term
            (rr_lw_simpa $hF_pos)
            (rr_lw_simpa $hdeg_lo)
            (rr_lw_simpa $hdeg_hi)
            $hno))

end Tactic
end RealRooted
