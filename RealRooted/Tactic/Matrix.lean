module

public import RealRooted.MatrixInterlacing
public import RealRooted.RowThreshold
public import RealRooted.StaircaseSum
public import RealRooted.Tactic.Lookup
public import RealRooted.Tactic.SideGoals

/-!
# Matrix-transfer tactic

Dispatcher tactics:

```lean
rr_matrix
rr_matrix0
rr_matrix0_weak
rr_matrix0_realrooted
rr_matrix0_filter_ne_zero
rr_matrix0_filter_ne_zero_weak
rr_row_threshold_matrix
rr_row_threshold_matrix0
rr_row_threshold_matrix0_weak
rr_row_threshold_matrix0_realrooted
rr_row_threshold_matrix0_filter_ne_zero
rr_row_threshold_matrix0_filter_ne_zero_weak
rr_row_threshold_entry_nonneg
```

Primary target:
refined vector recurrences already written as

```text
F_next = matPolyAction G F.
```

The tactics apply `matrix_preserves_interlacing_seq`,
`matrix_preserves_interlacing_seq0_of_2x2`, or row-threshold wrappers after
the user supplies the matrix action, rectangularity, entry nonnegativity, and
`2 x 2` Branden conditions.

Every matrix form has a bare variant inferring the matrix and input from the
goal. The positive-width forms also use an exact local width-positivity proof.
Bare forms use exact local length and input certificates, then the registered
matrix certificate attributes. The bare `rr_row_threshold_entry_nonneg` form
infers its matrix from the target.

Family J warning:
do not attack raw scalar long-lag recurrences.  First derive a refined vector
or production-matrix recurrence.
-/

@[expose] public section

namespace RealRooted
namespace Tactic

/-- Positional form of `rr_matrix using ...`: the same arguments as the named form, in the order
`n_pos`, `matrix`, `rectangular`, `entry_nonneg`, `two_by_two`, `input`, `input_length` and
`input_interlacing`. -/
syntax (name := rr_matrix)
  "rr_matrix" " using " term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term :
  tactic

/-- Closes `IsInterlacingSeqNonneg (matPolyAction G fs)` by the matrix-transfer theorem. Arguments:
`n_pos : 0 < n`; `matrix : G`, the matrix as a list of rows;
`rectangular : ∀ row ∈ G, row.length = n`; `entry_nonneg : ∀ row ∈ G, ∀ p ∈ row, HasNonnegCoeffs p`;
`two_by_two`, the `2 x 2` condition `Has2x2InterlacingProperty` for all rows `i₁ ≤ i₂` and columns
`j₁ ≤ j₂`; `input : fs`, the input list of polynomials; `input_length : fs.length = n`; and
`input_interlacing : IsInterlacingSeqNonneg fs`. -/
syntax (name := rr_matrix_named)
  "rr_matrix" " using "
    "n_pos" ":=" term ","
    "matrix" ":=" term ","
    "rectangular" ":=" term ","
    "entry_nonneg" ":=" term ","
    "two_by_two" ":=" term ","
    "input" ":=" term ","
    "input_length" ":=" term ","
    "input_interlacing" ":=" term :
  tactic

/-- Bare form of `rr_matrix`: infers the matrix and input from the goal, takes the positivity,
length and input certificates from the local context by `assumption`, and finds the rectangularity,
nonnegativity and `2 x 2` certificates among the registered `rr_matrix_*` lemmas. -/
syntax (name := rr_matrix_inferred) "rr_matrix" : tactic

/-- Positional form of `rr_matrix0 using ...`: the same arguments as the named form, in the order
`matrix`, `rectangular`, `entry_nonneg`, `two_by_two`, `input`, `input_length` and
`input_interlacing`. -/
syntax (name := rr_matrix0)
  "rr_matrix0" " using " term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term :
  tactic

/-- Closes `IsInterlacingSeq0Nonneg (matPolyAction G fs)` by the matrix-transfer theorem. Arguments:
`matrix : G`, the matrix as a list of rows; `rectangular : ∀ row ∈ G, row.length = n`;
`entry_nonneg : ∀ row ∈ G, ∀ p ∈ row, HasNonnegCoeffs p`; `two_by_two`, the `2 x 2` condition
`Has2x2InterlacingProperty0` for all rows `i₁ ≤ i₂` and columns `j₁ ≤ j₂`; `input : fs`, the input
list of polynomials; `input_length : fs.length = n`; and
`input_interlacing : IsInterlacingSeqNonneg fs`. -/
syntax (name := rr_matrix0_named)
  "rr_matrix0" " using "
    "matrix" ":=" term ","
    "rectangular" ":=" term ","
    "entry_nonneg" ":=" term ","
    "two_by_two" ":=" term ","
    "input" ":=" term ","
    "input_length" ":=" term ","
    "input_interlacing" ":=" term :
  tactic

/-- Bare form of `rr_matrix0`: infers the matrix and input from the goal, takes the length and input
certificates from the local context by `assumption`, and finds the rectangularity, nonnegativity and
`2 x 2` certificates among the registered `rr_matrix_*` lemmas. -/
syntax (name := rr_matrix0_inferred) "rr_matrix0" : tactic

/-- Positional form of `rr_matrix0_weak using ...`: the same arguments as the named form, in the
order `matrix`, `rectangular`, `entry_nonneg`, `two_by_two`, `input`, `input_length`,
`input_interlacing` and `input_real_rooted`. -/
syntax (name := rr_matrix0_weak)
  "rr_matrix0_weak" " using " term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term :
  tactic

/-- Closes `IsInterlacingSeq0Nonneg (matPolyAction G fs)` together with
`∀ f ∈ matPolyAction G fs, f ≠ 0 → f ≠ 0 ∧ f.Splits` by the matrix-transfer theorem. Arguments:
`matrix : G`, the matrix as a list of rows; `rectangular : ∀ row ∈ G, row.length = n`;
`entry_nonneg : ∀ row ∈ G, ∀ p ∈ row, HasNonnegCoeffs p`; `two_by_two`, the `2 x 2` condition
`Has2x2InterlacingProperty0` for all rows `i₁ ≤ i₂` and columns `j₁ ≤ j₂`; `input : fs`, the input
list of polynomials; `input_length : fs.length = n`;
`input_interlacing : IsInterlacingSeq0Nonneg fs`; and
`input_real_rooted : ∀ f ∈ fs, f ≠ 0 → f ≠ 0 ∧ f.Splits`. -/
syntax (name := rr_matrix0_weak_named)
  "rr_matrix0_weak" " using "
    "matrix" ":=" term ","
    "rectangular" ":=" term ","
    "entry_nonneg" ":=" term ","
    "two_by_two" ":=" term ","
    "input" ":=" term ","
    "input_length" ":=" term ","
    "input_interlacing" ":=" term ","
    "input_real_rooted" ":=" term :
  tactic

/-- Bare form of `rr_matrix0_weak`: infers the matrix and input from the goal, takes the length and
input certificates from the local context by `assumption`, and finds the rectangularity,
nonnegativity and `2 x 2` certificates among the registered `rr_matrix_*` lemmas. -/
syntax (name := rr_matrix0_weak_inferred) "rr_matrix0_weak" : tactic

/-- Positional form of `rr_matrix0_realrooted using ...`: the same arguments as the named form, in
the order `matrix`, `rectangular`, `entry_nonneg`, `two_by_two`, `input`, `input_length` and
`input_interlacing`. -/
syntax (name := rr_matrix0_realrooted)
  "rr_matrix0_realrooted" " using " term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term :
  tactic

/-- Closes `IsInterlacingSeq0Nonneg (matPolyAction G fs)` together with
`∀ f ∈ matPolyAction G fs, f ≠ 0 → f ≠ 0 ∧ f.Splits` by the matrix-transfer theorem. Arguments:
`matrix : G`, the matrix as a list of rows; `rectangular : ∀ row ∈ G, row.length = n`;
`entry_nonneg : ∀ row ∈ G, ∀ p ∈ row, HasNonnegCoeffs p`; `two_by_two`, the `2 x 2` condition
`Has2x2InterlacingProperty0` for all rows `i₁ ≤ i₂` and columns `j₁ ≤ j₂`; `input : fs`, the input
list of polynomials; `input_length : fs.length = n`; and
`input_interlacing : IsInterlacingSeqNonneg fs`. -/
syntax (name := rr_matrix0_realrooted_named)
  "rr_matrix0_realrooted" " using "
    "matrix" ":=" term ","
    "rectangular" ":=" term ","
    "entry_nonneg" ":=" term ","
    "two_by_two" ":=" term ","
    "input" ":=" term ","
    "input_length" ":=" term ","
    "input_interlacing" ":=" term :
  tactic

/-- Bare form of `rr_matrix0_realrooted`: infers the matrix and input from the goal, takes the
length and input certificates from the local context by `assumption`, and finds the rectangularity,
nonnegativity and `2 x 2` certificates among the registered `rr_matrix_*` lemmas. -/
syntax (name := rr_matrix0_realrooted_inferred)
  "rr_matrix0_realrooted" : tactic

/-- Positional form of `rr_matrix0_filter_ne_zero using ...`: the same arguments as the named form,
in the order `matrix`, `rectangular`, `entry_nonneg`, `two_by_two`, `input`, `input_length` and
`input_interlacing`. -/
syntax (name := rr_matrix0_filter_ne_zero)
  "rr_matrix0_filter_ne_zero" " using " term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term :
  tactic

/-- Closes `IsInterlacingSeqNonneg ((matPolyAction G fs).filter (· ≠ 0))` by the matrix-transfer
theorem. Arguments: `matrix : G`, the matrix as a list of rows;
`rectangular : ∀ row ∈ G, row.length = n`; `entry_nonneg : ∀ row ∈ G, ∀ p ∈ row, HasNonnegCoeffs p`;
`two_by_two`, the `2 x 2` condition `Has2x2InterlacingProperty0` for all rows `i₁ ≤ i₂` and columns
`j₁ ≤ j₂`; `input : fs`, the input list of polynomials; `input_length : fs.length = n`; and
`input_interlacing : IsInterlacingSeqNonneg fs`. -/
syntax (name := rr_matrix0_filter_ne_zero_named)
  "rr_matrix0_filter_ne_zero" " using "
    "matrix" ":=" term ","
    "rectangular" ":=" term ","
    "entry_nonneg" ":=" term ","
    "two_by_two" ":=" term ","
    "input" ":=" term ","
    "input_length" ":=" term ","
    "input_interlacing" ":=" term :
  tactic

/-- Bare form of `rr_matrix0_filter_ne_zero`: infers the matrix and input from the goal, takes the
length and input certificates from the local context by `assumption`, and finds the rectangularity,
nonnegativity and `2 x 2` certificates among the registered `rr_matrix_*` lemmas. -/
syntax (name := rr_matrix0_filter_ne_zero_inferred)
  "rr_matrix0_filter_ne_zero" : tactic

/-- Positional form of `rr_matrix0_filter_ne_zero_weak using ...`: the same arguments as the named
form, in the order `matrix`, `rectangular`, `entry_nonneg`, `two_by_two`, `input`, `input_length`,
`input_interlacing` and `input_real_rooted`. -/
syntax (name := rr_matrix0_filter_ne_zero_weak)
  "rr_matrix0_filter_ne_zero_weak" " using " term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term :
  tactic

/-- Closes `IsInterlacingSeqNonneg ((matPolyAction G fs).filter (· ≠ 0))` by the matrix-transfer
theorem. Arguments: `matrix : G`, the matrix as a list of rows;
`rectangular : ∀ row ∈ G, row.length = n`; `entry_nonneg : ∀ row ∈ G, ∀ p ∈ row, HasNonnegCoeffs p`;
`two_by_two`, the `2 x 2` condition `Has2x2InterlacingProperty0` for all rows `i₁ ≤ i₂` and columns
`j₁ ≤ j₂`; `input : fs`, the input list of polynomials; `input_length : fs.length = n`;
`input_interlacing : IsInterlacingSeq0Nonneg fs`; and
`input_real_rooted : ∀ f ∈ fs, f ≠ 0 → f ≠ 0 ∧ f.Splits`. -/
syntax (name := rr_matrix0_filter_ne_zero_weak_named)
  "rr_matrix0_filter_ne_zero_weak" " using "
    "matrix" ":=" term ","
    "rectangular" ":=" term ","
    "entry_nonneg" ":=" term ","
    "two_by_two" ":=" term ","
    "input" ":=" term ","
    "input_length" ":=" term ","
    "input_interlacing" ":=" term ","
    "input_real_rooted" ":=" term :
  tactic

/-- Bare form of `rr_matrix0_filter_ne_zero_weak`: infers the matrix and input from the goal, takes
the length and input certificates from the local context by `assumption`, and finds the
rectangularity, nonnegativity and `2 x 2` certificates among the registered `rr_matrix_*` lemmas. -/
syntax (name := rr_matrix0_filter_ne_zero_weak_inferred)
  "rr_matrix0_filter_ne_zero_weak" : tactic

/-- Closes `IsInterlacingSeqNonneg (matPolyAction G fs)` by the row-threshold matrix-transfer
theorem. Arguments: `n_pos : 0 < n`; `matrix : G`, the matrix as a list of rows;
`rectangular : ∀ row ∈ G, row.length = n`; `row_threshold : HasRowThresholdLinearStructure G`;
`two_by_two`, the `2 x 2` condition `Has2x2InterlacingProperty` for all rows `i₁ ≤ i₂` and columns
`j₁ ≤ j₂`; `input : fs`, the input list of polynomials; `input_length : fs.length = n`; and
`input_interlacing : IsInterlacingSeqNonneg fs`. -/
syntax (name := rr_row_threshold_matrix_named)
  "rr_row_threshold_matrix" " using "
    "n_pos" ":=" term ","
    "matrix" ":=" term ","
    "rectangular" ":=" term ","
    "row_threshold" ":=" term ","
    "two_by_two" ":=" term ","
    "input" ":=" term ","
    "input_length" ":=" term ","
    "input_interlacing" ":=" term :
  tactic

/-- Positional form of `rr_row_threshold_matrix using ...`: the same arguments as the named form, in
the order `n_pos`, `matrix`, `rectangular`, `row_threshold`, `two_by_two`, `input`, `input_length`
and `input_interlacing`. -/
syntax (name := rr_row_threshold_matrix)
  "rr_row_threshold_matrix" " using " term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term :
  tactic

/-- Bare form of `rr_row_threshold_matrix`: infers the matrix and input from the goal, takes the
positivity, length and input certificates from the local context by `assumption`, and finds the
row-threshold and `2 x 2` certificates among the registered `rr_matrix_*` lemmas. -/
syntax (name := rr_row_threshold_matrix_inferred)
  "rr_row_threshold_matrix" : tactic

/-- Closes `IsInterlacingSeq0Nonneg (matPolyAction G fs)` by the row-threshold matrix-transfer
theorem. Arguments: `matrix : G`, the matrix as a list of rows;
`rectangular : ∀ row ∈ G, row.length = n`; `row_threshold : HasRowThresholdLinearStructure G`;
`two_by_two`, the `2 x 2` condition `Has2x2InterlacingProperty0` for all rows `i₁ ≤ i₂` and columns
`j₁ ≤ j₂`; `input : fs`, the input list of polynomials; `input_length : fs.length = n`; and
`input_interlacing : IsInterlacingSeqNonneg fs`. -/
syntax (name := rr_row_threshold_matrix0_named)
  "rr_row_threshold_matrix0" " using "
    "matrix" ":=" term ","
    "rectangular" ":=" term ","
    "row_threshold" ":=" term ","
    "two_by_two" ":=" term ","
    "input" ":=" term ","
    "input_length" ":=" term ","
    "input_interlacing" ":=" term :
  tactic

/-- Positional form of `rr_row_threshold_matrix0 using ...`: the same arguments as the named form,
in the order `matrix`, `rectangular`, `row_threshold`, `two_by_two`, `input`, `input_length` and
`input_interlacing`. -/
syntax (name := rr_row_threshold_matrix0)
  "rr_row_threshold_matrix0" " using " term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term :
  tactic

/-- Bare form of `rr_row_threshold_matrix0`: infers the matrix and input from the goal, takes the
length and input certificates from the local context by `assumption`, and finds the row-threshold
and `2 x 2` certificates among the registered `rr_matrix_*` lemmas. -/
syntax (name := rr_row_threshold_matrix0_inferred)
  "rr_row_threshold_matrix0" : tactic

/-- Closes `IsInterlacingSeq0Nonneg (matPolyAction G fs)` together with
`∀ f ∈ matPolyAction G fs, f ≠ 0 → f ≠ 0 ∧ f.Splits` by the row-threshold matrix-transfer theorem.
Arguments: `matrix : G`, the matrix as a list of rows; `rectangular : ∀ row ∈ G, row.length = n`;
`row_threshold : HasRowThresholdLinearStructure G`; `two_by_two`, the `2 x 2` condition
`Has2x2InterlacingProperty0` for all rows `i₁ ≤ i₂` and columns `j₁ ≤ j₂`; `input : fs`, the input
list of polynomials; `input_length : fs.length = n`;
`input_interlacing : IsInterlacingSeq0Nonneg fs`; and
`input_real_rooted : ∀ f ∈ fs, f ≠ 0 → f ≠ 0 ∧ f.Splits`. -/
syntax (name := rr_row_threshold_matrix0_weak_named)
  "rr_row_threshold_matrix0_weak" " using "
    "matrix" ":=" term ","
    "rectangular" ":=" term ","
    "row_threshold" ":=" term ","
    "two_by_two" ":=" term ","
    "input" ":=" term ","
    "input_length" ":=" term ","
    "input_interlacing" ":=" term ","
    "input_real_rooted" ":=" term :
  tactic

/-- Positional form of `rr_row_threshold_matrix0_weak using ...`: the same arguments as the named
form, in the order `matrix`, `rectangular`, `row_threshold`, `two_by_two`, `input`, `input_length`,
`input_interlacing` and `input_real_rooted`. -/
syntax (name := rr_row_threshold_matrix0_weak)
  "rr_row_threshold_matrix0_weak" " using " term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term :
  tactic

/-- Bare form of `rr_row_threshold_matrix0_weak`: infers the matrix and input from the goal, takes
the length and input certificates from the local context by `assumption`, and finds the
row-threshold and `2 x 2` certificates among the registered `rr_matrix_*` lemmas. -/
syntax (name := rr_row_threshold_matrix0_weak_inferred)
  "rr_row_threshold_matrix0_weak" : tactic

/-- Closes `IsInterlacingSeqNonneg ((matPolyAction G fs).filter (· ≠ 0))` by the row-threshold
matrix-transfer theorem. Arguments: `matrix : G`, the matrix as a list of rows;
`rectangular : ∀ row ∈ G, row.length = n`; `row_threshold : HasRowThresholdLinearStructure G`;
`two_by_two`, the `2 x 2` condition `Has2x2InterlacingProperty0` for all rows `i₁ ≤ i₂` and columns
`j₁ ≤ j₂`; `input : fs`, the input list of polynomials; `input_length : fs.length = n`;
`input_interlacing : IsInterlacingSeq0Nonneg fs`; and
`input_real_rooted : ∀ f ∈ fs, f ≠ 0 → f ≠ 0 ∧ f.Splits`. -/
syntax (name := rr_row_threshold_matrix0_filter_ne_zero_weak_named)
  "rr_row_threshold_matrix0_filter_ne_zero_weak" " using "
    "matrix" ":=" term ","
    "rectangular" ":=" term ","
    "row_threshold" ":=" term ","
    "two_by_two" ":=" term ","
    "input" ":=" term ","
    "input_length" ":=" term ","
    "input_interlacing" ":=" term ","
    "input_real_rooted" ":=" term :
  tactic

/-- Positional form of `rr_row_threshold_matrix0_filter_ne_zero_weak using ...`: the same arguments
as the named form, in the order `matrix`, `rectangular`, `row_threshold`, `two_by_two`, `input`,
`input_length`, `input_interlacing` and `input_real_rooted`. -/
syntax (name := rr_row_threshold_matrix0_filter_ne_zero_weak)
  "rr_row_threshold_matrix0_filter_ne_zero_weak" " using " term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term :
  tactic

/-- Bare form of `rr_row_threshold_matrix0_filter_ne_zero_weak`: infers the matrix and input from
the goal, takes the length and input certificates from the local context by `assumption`, and finds
the row-threshold and `2 x 2` certificates among the registered `rr_matrix_*` lemmas. -/
syntax (name := rr_row_threshold_matrix0_filter_ne_zero_weak_inferred)
  "rr_row_threshold_matrix0_filter_ne_zero_weak" : tactic

/-- Closes `IsInterlacingSeq0Nonneg (matPolyAction G fs)` together with
`∀ f ∈ matPolyAction G fs, f ≠ 0 → f ≠ 0 ∧ f.Splits` by the row-threshold matrix-transfer theorem.
Arguments: `matrix : G`, the matrix as a list of rows; `rectangular : ∀ row ∈ G, row.length = n`;
`row_threshold : HasRowThresholdLinearStructure G`; `two_by_two`, the `2 x 2` condition
`Has2x2InterlacingProperty0` for all rows `i₁ ≤ i₂` and columns `j₁ ≤ j₂`; `input : fs`, the input
list of polynomials; `input_length : fs.length = n`; and
`input_interlacing : IsInterlacingSeqNonneg fs`. -/
syntax (name := rr_row_threshold_matrix0_realrooted_named)
  "rr_row_threshold_matrix0_realrooted" " using "
    "matrix" ":=" term ","
    "rectangular" ":=" term ","
    "row_threshold" ":=" term ","
    "two_by_two" ":=" term ","
    "input" ":=" term ","
    "input_length" ":=" term ","
    "input_interlacing" ":=" term :
  tactic

/-- Positional form of `rr_row_threshold_matrix0_realrooted using ...`: the same arguments as the
named form, in the order `matrix`, `rectangular`, `row_threshold`, `two_by_two`, `input`,
`input_length` and `input_interlacing`. -/
syntax (name := rr_row_threshold_matrix0_realrooted)
  "rr_row_threshold_matrix0_realrooted" " using " term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term :
  tactic

/-- Bare form of `rr_row_threshold_matrix0_realrooted`: infers the matrix and input from the goal,
takes the length and input certificates from the local context by `assumption`, and finds the
row-threshold and `2 x 2` certificates among the registered `rr_matrix_*` lemmas. -/
syntax (name := rr_row_threshold_matrix0_realrooted_inferred)
  "rr_row_threshold_matrix0_realrooted" : tactic

/-- Closes `IsInterlacingSeqNonneg ((matPolyAction G fs).filter (· ≠ 0))` by the row-threshold
matrix-transfer theorem. Arguments: `matrix : G`, the matrix as a list of rows;
`rectangular : ∀ row ∈ G, row.length = n`; `row_threshold : HasRowThresholdLinearStructure G`;
`two_by_two`, the `2 x 2` condition `Has2x2InterlacingProperty0` for all rows `i₁ ≤ i₂` and columns
`j₁ ≤ j₂`; `input : fs`, the input list of polynomials; `input_length : fs.length = n`; and
`input_interlacing : IsInterlacingSeqNonneg fs`. -/
syntax (name := rr_row_threshold_matrix0_filter_ne_zero_named)
  "rr_row_threshold_matrix0_filter_ne_zero" " using "
    "matrix" ":=" term ","
    "rectangular" ":=" term ","
    "row_threshold" ":=" term ","
    "two_by_two" ":=" term ","
    "input" ":=" term ","
    "input_length" ":=" term ","
    "input_interlacing" ":=" term :
  tactic

/-- Positional form of `rr_row_threshold_matrix0_filter_ne_zero using ...`: the same arguments as
the named form, in the order `matrix`, `rectangular`, `row_threshold`, `two_by_two`, `input`,
`input_length` and `input_interlacing`. -/
syntax (name := rr_row_threshold_matrix0_filter_ne_zero)
  "rr_row_threshold_matrix0_filter_ne_zero" " using " term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term ", "
    term :
  tactic

/-- Bare form of `rr_row_threshold_matrix0_filter_ne_zero`: infers the matrix and input from the
goal, takes the length and input certificates from the local context by `assumption`, and finds the
row-threshold and `2 x 2` certificates among the registered `rr_matrix_*` lemmas. -/
syntax (name := rr_row_threshold_matrix0_filter_ne_zero_inferred)
  "rr_row_threshold_matrix0_filter_ne_zero" : tactic

/-- Closes `∀ row ∈ G, ∀ p ∈ row, HasNonnegCoeffs p` from
`row_threshold : HasRowThresholdLinearStructure G`. -/
syntax (name := rr_row_threshold_entry_nonneg_named)
  "rr_row_threshold_entry_nonneg" " using "
    "row_threshold" ":=" term :
  tactic

/-- Positional form of `rr_row_threshold_entry_nonneg using ...`: takes the certificate
`row_threshold` directly. -/
syntax (name := rr_row_threshold_entry_nonneg)
  "rr_row_threshold_entry_nonneg" " using " term :
  tactic

/-- Bare form of `rr_row_threshold_entry_nonneg`: infers the matrix from the goal and finds the
row-threshold certificate among the registered `rr_matrix_threshold` lemmas. -/
syntax (name := rr_row_threshold_entry_nonneg_inferred)
  "rr_row_threshold_entry_nonneg" : tactic

-- The local length proof fixes the hidden width before positivity and frozen lookup.
macro_rules
  | `(tactic| rr_matrix) =>
      `(tactic|
        exact (by
          apply RealRooted.matrix_preserves_interlacing_seq
          case hfs_len => assumption
          case hn => assumption
          case hG_rect => rr_lookup [rr_matrix_rect]
          case hG_nonneg => rr_lookup [rr_matrix_nonneg]
          case hG_affine => rr_lookup [rr_matrix_2x2]
          case hfs => assumption))
  | `(tactic| rr_matrix0) =>
      `(tactic|
        exact (by
          apply RealRooted.matrix_preserves_interlacing_seq0_of_2x2
          case hfs_len => assumption
          case hG_rect => rr_lookup [rr_matrix_rect]
          case hG_nonneg => rr_lookup [rr_matrix_nonneg]
          case hG_affine => rr_lookup [rr_matrix_2x2]
          case hfs => assumption))
  | `(tactic| rr_matrix0_weak) =>
      `(tactic|
        exact (by
          apply RealRooted.matrix_preserves_interlacing_seq0_of_2x2_weak
          case hfs_len => assumption
          case hG_rect => rr_lookup [rr_matrix_rect]
          case hG_nonneg => rr_lookup [rr_matrix_nonneg]
          case hG_affine => rr_lookup [rr_matrix_2x2]
          case hfs => assumption
          case hfs_real => assumption))
  | `(tactic| rr_matrix0_realrooted) =>
      `(tactic|
        exact (by
          apply RealRooted.matrix_preserves_interlacing_seq0_of_2x2_realRooted
          case hfs_len => assumption
          case hG_rect => rr_lookup [rr_matrix_rect]
          case hG_nonneg => rr_lookup [rr_matrix_nonneg]
          case hG_affine => rr_lookup [rr_matrix_2x2]
          case hfs => assumption))
  | `(tactic| rr_matrix0_filter_ne_zero) =>
      `(tactic|
        exact (by
          apply RealRooted.matrix_preserves_interlacing_seq0_filter_ne_zero_of_2x2
          case hfs_len => assumption
          case hG_rect => rr_lookup [rr_matrix_rect]
          case hG_nonneg => rr_lookup [rr_matrix_nonneg]
          case hG_affine => rr_lookup [rr_matrix_2x2]
          case hfs => assumption))
  | `(tactic| rr_matrix0_filter_ne_zero_weak) =>
      `(tactic|
        exact (by
          apply
            RealRooted.matrix_preserves_interlacing_seq0_filter_ne_zero_of_2x2_weak
          case hfs_len => assumption
          case hG_rect => rr_lookup [rr_matrix_rect]
          case hG_nonneg => rr_lookup [rr_matrix_nonneg]
          case hG_affine => rr_lookup [rr_matrix_2x2]
          case hfs => assumption
          case hfs_real => assumption))
  | `(tactic| rr_row_threshold_matrix) =>
      `(tactic|
        exact (by
          apply RealRooted.rowThreshold_matrix_preserves_interlacing_seq_of_2x2
          case hfs_len => assumption
          case hn => assumption
          case hG_rect => rr_lookup [rr_matrix_rect]
          case hG_threshold => rr_lookup [rr_matrix_threshold]
          case hG_affine => rr_lookup [rr_matrix_2x2]
          case hfs => assumption))
  | `(tactic| rr_row_threshold_matrix0) =>
      `(tactic|
        exact (by
          apply RealRooted.rowThreshold_matrix_preserves_interlacing_seq0_of_2x2
          case hfs_len => assumption
          case hG_rect => rr_lookup [rr_matrix_rect]
          case hG_threshold => rr_lookup [rr_matrix_threshold]
          case hG_affine => rr_lookup [rr_matrix_2x2]
          case hfs => assumption))
  | `(tactic| rr_row_threshold_matrix0_weak) =>
      `(tactic|
        exact (by
          apply RealRooted.rowThreshold_matrix_preserves_interlacing_seq0_of_2x2_weak
          case hfs_len => assumption
          case hG_rect => rr_lookup [rr_matrix_rect]
          case hG_threshold => rr_lookup [rr_matrix_threshold]
          case hG_affine => rr_lookup [rr_matrix_2x2]
          case hfs => assumption
          case hfs_real => assumption))
  | `(tactic| rr_row_threshold_matrix0_realrooted) =>
      `(tactic|
        exact (by
          apply
            RealRooted.rowThreshold_matrix_preserves_interlacing_seq0_of_2x2_realRooted
          case hfs_len => assumption
          case hG_rect => rr_lookup [rr_matrix_rect]
          case hG_threshold => rr_lookup [rr_matrix_threshold]
          case hG_affine => rr_lookup [rr_matrix_2x2]
          case hfs => assumption))
  | `(tactic| rr_row_threshold_matrix0_filter_ne_zero) =>
      `(tactic|
        exact (by
          apply
            RealRooted.rowThreshold_matrix_preserves_interlacing_seq0_filter_ne_zero_of_2x2
          case hfs_len => assumption
          case hG_rect => rr_lookup [rr_matrix_rect]
          case hG_threshold => rr_lookup [rr_matrix_threshold]
          case hG_affine => rr_lookup [rr_matrix_2x2]
          case hfs => assumption))
  | `(tactic| rr_row_threshold_matrix0_filter_ne_zero_weak) =>
      `(tactic|
        exact (by
          apply
            RealRooted.rowThreshold_matrix_preserves_interlacing_seq0_filter_ne_zero_of_2x2_weak
          case hfs_len => assumption
          case hG_rect => rr_lookup [rr_matrix_rect]
          case hG_threshold => rr_lookup [rr_matrix_threshold]
          case hG_affine => rr_lookup [rr_matrix_2x2]
          case hfs => assumption
          case hfs_real => assumption))
  | `(tactic| rr_row_threshold_entry_nonneg) =>
      `(tactic|
        rr_row_threshold_entry_nonneg using
          row_threshold := (by rr_lookup [rr_matrix_threshold]))
  | `(tactic|
      rr_matrix using
        $hn:term, $G:term, $hG_rect:term, $hG_nonneg:term, $hG_affine:term,
        $fs:term, $hfs_len:term, $hfs:term) =>
      `(tactic|
        exact RealRooted.matrix_preserves_interlacing_seq
          $hn $G $hG_rect $hG_nonneg $hG_affine $fs $hfs_len $hfs)
  | `(tactic|
      rr_matrix using
        n_pos := $hn:term,
        matrix := $G:term,
        rectangular := $hG_rect:term,
        entry_nonneg := $hG_nonneg:term,
        two_by_two := $hG_affine:term,
        input := $fs:term,
        input_length := $hfs_len:term,
        input_interlacing := $hfs:term) =>
      `(tactic|
        rr_matrix using $hn, $G, $hG_rect, $hG_nonneg, $hG_affine, $fs,
          $hfs_len, $hfs)
  | `(tactic|
      rr_matrix0 using
        $G:term, $hG_rect:term, $hG_nonneg:term, $hG_affine:term, $fs:term,
        $hfs_len:term, $hfs:term) =>
      `(tactic|
        exact RealRooted.matrix_preserves_interlacing_seq0_of_2x2
          $G $hG_rect $hG_nonneg $hG_affine $fs $hfs_len $hfs)
  | `(tactic|
      rr_matrix0 using
        matrix := $G:term,
        rectangular := $hG_rect:term,
        entry_nonneg := $hG_nonneg:term,
        two_by_two := $hG_affine:term,
        input := $fs:term,
        input_length := $hfs_len:term,
        input_interlacing := $hfs:term) =>
      `(tactic|
        rr_matrix0 using $G, $hG_rect, $hG_nonneg, $hG_affine, $fs, $hfs_len,
          $hfs)
  | `(tactic|
      rr_matrix0_weak using
        $G:term, $hG_rect:term, $hG_nonneg:term, $hG_affine:term, $fs:term,
        $hfs_len:term, $hfs:term, $hfs_real:term) =>
      `(tactic|
        exact RealRooted.matrix_preserves_interlacing_seq0_of_2x2_weak
          $G $hG_rect $hG_nonneg $hG_affine $fs $hfs_len $hfs $hfs_real)
  | `(tactic|
      rr_matrix0_weak using
        matrix := $G:term,
        rectangular := $hG_rect:term,
        entry_nonneg := $hG_nonneg:term,
        two_by_two := $hG_affine:term,
        input := $fs:term,
        input_length := $hfs_len:term,
        input_interlacing := $hfs:term,
        input_real_rooted := $hfs_real:term) =>
      `(tactic|
        rr_matrix0_weak using $G, $hG_rect, $hG_nonneg, $hG_affine, $fs,
          $hfs_len, $hfs, $hfs_real)
  | `(tactic|
      rr_matrix0_realrooted using
        $G:term, $hG_rect:term, $hG_nonneg:term, $hG_affine:term, $fs:term,
        $hfs_len:term, $hfs:term) =>
      `(tactic|
        exact RealRooted.matrix_preserves_interlacing_seq0_of_2x2_realRooted
          $G $hG_rect $hG_nonneg $hG_affine $fs $hfs_len $hfs)
  | `(tactic|
      rr_matrix0_realrooted using
        matrix := $G:term,
        rectangular := $hG_rect:term,
        entry_nonneg := $hG_nonneg:term,
        two_by_two := $hG_affine:term,
        input := $fs:term,
        input_length := $hfs_len:term,
        input_interlacing := $hfs:term) =>
      `(tactic|
        rr_matrix0_realrooted using $G, $hG_rect, $hG_nonneg, $hG_affine, $fs,
          $hfs_len, $hfs)
  | `(tactic|
      rr_matrix0_filter_ne_zero using
        $G:term, $hG_rect:term, $hG_nonneg:term, $hG_affine:term, $fs:term,
        $hfs_len:term, $hfs:term) =>
      `(tactic|
        exact RealRooted.matrix_preserves_interlacing_seq0_filter_ne_zero_of_2x2
          $G $hG_rect $hG_nonneg $hG_affine $fs $hfs_len $hfs)
  | `(tactic|
      rr_matrix0_filter_ne_zero using
        matrix := $G:term,
        rectangular := $hG_rect:term,
        entry_nonneg := $hG_nonneg:term,
        two_by_two := $hG_affine:term,
        input := $fs:term,
        input_length := $hfs_len:term,
        input_interlacing := $hfs:term) =>
      `(tactic|
        rr_matrix0_filter_ne_zero using $G, $hG_rect, $hG_nonneg, $hG_affine,
          $fs, $hfs_len, $hfs)
  | `(tactic|
      rr_matrix0_filter_ne_zero_weak using
        $G:term, $hG_rect:term, $hG_nonneg:term, $hG_affine:term, $fs:term,
        $hfs_len:term, $hfs:term, $hfs_real:term) =>
      `(tactic|
        exact
          RealRooted.matrix_preserves_interlacing_seq0_filter_ne_zero_of_2x2_weak
            $G $hG_rect $hG_nonneg $hG_affine $fs $hfs_len $hfs $hfs_real)
  | `(tactic|
      rr_matrix0_filter_ne_zero_weak using
        matrix := $G:term,
        rectangular := $hG_rect:term,
        entry_nonneg := $hG_nonneg:term,
        two_by_two := $hG_affine:term,
        input := $fs:term,
        input_length := $hfs_len:term,
        input_interlacing := $hfs:term,
        input_real_rooted := $hfs_real:term) =>
      `(tactic|
        rr_matrix0_filter_ne_zero_weak using $G, $hG_rect, $hG_nonneg,
          $hG_affine, $fs, $hfs_len, $hfs, $hfs_real)
  | `(tactic|
      rr_row_threshold_matrix using
        $hn:term, $G:term, $hG_rect:term, $hG_threshold:term,
        $hG_affine:term, $fs:term, $hfs_len:term, $hfs:term) =>
      `(tactic|
        exact RealRooted.rowThreshold_matrix_preserves_interlacing_seq_of_2x2
          $hn $G $hG_rect $hG_threshold $hG_affine $fs $hfs_len $hfs)
  | `(tactic|
      rr_row_threshold_matrix using
        n_pos := $hn:term,
        matrix := $G:term,
        rectangular := $hG_rect:term,
        row_threshold := $hG_threshold:term,
        two_by_two := $hG_affine:term,
        input := $fs:term,
        input_length := $hfs_len:term,
        input_interlacing := $hfs:term) =>
      `(tactic|
        rr_row_threshold_matrix using $hn, $G, $hG_rect, $hG_threshold,
          $hG_affine, $fs, $hfs_len, $hfs)
  | `(tactic|
      rr_row_threshold_matrix0 using
        $G:term, $hG_rect:term, $hG_threshold:term, $hG_affine:term, $fs:term,
        $hfs_len:term, $hfs:term) =>
      `(tactic|
        exact RealRooted.rowThreshold_matrix_preserves_interlacing_seq0_of_2x2
          $G $hG_rect $hG_threshold $hG_affine $fs $hfs_len $hfs)
  | `(tactic|
      rr_row_threshold_matrix0 using
        matrix := $G:term,
        rectangular := $hG_rect:term,
        row_threshold := $hG_threshold:term,
        two_by_two := $hG_affine:term,
        input := $fs:term,
        input_length := $hfs_len:term,
        input_interlacing := $hfs:term) =>
      `(tactic|
        rr_row_threshold_matrix0 using $G, $hG_rect, $hG_threshold,
          $hG_affine, $fs, $hfs_len, $hfs)
  | `(tactic|
      rr_row_threshold_matrix0_weak using
        $G:term, $hG_rect:term, $hG_threshold:term, $hG_affine:term, $fs:term,
        $hfs_len:term, $hfs:term, $hfs_real:term) =>
      `(tactic|
        exact
          RealRooted.rowThreshold_matrix_preserves_interlacing_seq0_of_2x2_weak
            $G $hG_rect $hG_threshold $hG_affine $fs $hfs_len $hfs $hfs_real)
  | `(tactic|
      rr_row_threshold_matrix0_weak using
        matrix := $G:term,
        rectangular := $hG_rect:term,
        row_threshold := $hG_threshold:term,
        two_by_two := $hG_affine:term,
        input := $fs:term,
        input_length := $hfs_len:term,
        input_interlacing := $hfs:term,
        input_real_rooted := $hfs_real:term) =>
      `(tactic|
        rr_row_threshold_matrix0_weak using $G, $hG_rect, $hG_threshold,
          $hG_affine, $fs, $hfs_len, $hfs, $hfs_real)
  | `(tactic|
      rr_row_threshold_matrix0_filter_ne_zero_weak using
        $G:term, $hG_rect:term, $hG_threshold:term, $hG_affine:term, $fs:term,
        $hfs_len:term, $hfs:term, $hfs_real:term) =>
      `(tactic|
        exact
          RealRooted.rowThreshold_matrix_preserves_interlacing_seq0_filter_ne_zero_of_2x2_weak
            $G $hG_rect $hG_threshold $hG_affine $fs $hfs_len $hfs $hfs_real)
  | `(tactic|
      rr_row_threshold_matrix0_filter_ne_zero_weak using
        matrix := $G:term,
        rectangular := $hG_rect:term,
        row_threshold := $hG_threshold:term,
        two_by_two := $hG_affine:term,
        input := $fs:term,
        input_length := $hfs_len:term,
        input_interlacing := $hfs:term,
        input_real_rooted := $hfs_real:term) =>
      `(tactic|
        rr_row_threshold_matrix0_filter_ne_zero_weak using $G, $hG_rect,
          $hG_threshold, $hG_affine, $fs, $hfs_len, $hfs, $hfs_real)
  | `(tactic|
      rr_row_threshold_matrix0_realrooted using
        $G:term, $hG_rect:term, $hG_threshold:term, $hG_affine:term, $fs:term,
        $hfs_len:term, $hfs:term) =>
      `(tactic|
        exact
          RealRooted.rowThreshold_matrix_preserves_interlacing_seq0_of_2x2_realRooted
            $G $hG_rect $hG_threshold $hG_affine $fs $hfs_len $hfs)
  | `(tactic|
      rr_row_threshold_matrix0_realrooted using
        matrix := $G:term,
        rectangular := $hG_rect:term,
        row_threshold := $hG_threshold:term,
        two_by_two := $hG_affine:term,
        input := $fs:term,
        input_length := $hfs_len:term,
        input_interlacing := $hfs:term) =>
      `(tactic|
        rr_row_threshold_matrix0_realrooted using $G, $hG_rect, $hG_threshold,
          $hG_affine, $fs, $hfs_len, $hfs)
  | `(tactic|
      rr_row_threshold_matrix0_filter_ne_zero using
        $G:term, $hG_rect:term, $hG_threshold:term, $hG_affine:term, $fs:term,
        $hfs_len:term, $hfs:term) =>
      `(tactic|
        exact
          RealRooted.rowThreshold_matrix_preserves_interlacing_seq0_filter_ne_zero_of_2x2
            $G $hG_rect $hG_threshold $hG_affine $fs $hfs_len $hfs)
  | `(tactic|
      rr_row_threshold_matrix0_filter_ne_zero using
        matrix := $G:term,
        rectangular := $hG_rect:term,
        row_threshold := $hG_threshold:term,
        two_by_two := $hG_affine:term,
        input := $fs:term,
        input_length := $hfs_len:term,
        input_interlacing := $hfs:term) =>
      `(tactic|
        rr_row_threshold_matrix0_filter_ne_zero using $G, $hG_rect,
          $hG_threshold, $hG_affine, $fs, $hfs_len, $hfs)
  | `(tactic|
      rr_row_threshold_entry_nonneg using
        row_threshold := $hG_threshold:term) =>
      `(tactic| rr_row_threshold_entry_nonneg using $hG_threshold)
  | `(tactic| rr_row_threshold_entry_nonneg using $hG_threshold:term) =>
      `(tactic|
        exact RealRooted.hasRowThresholdLinearStructure_nonneg $hG_threshold)

end Tactic
end RealRooted
