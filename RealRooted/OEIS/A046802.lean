import RealRooted.ThresholdMatrix.HaglundZhang

/-!
# OEIS A046802

The sequence-facing surface of A046802.  Row zero is `1`; the remaining rows
are the terminal polynomials of the Haglund--Zhang binomial Eulerian
refinement.  The refined vector supplies the interlacing certificate.
-/

open Polynomial

noncomputable section

namespace RealRooted

namespace OEIS

/-- OEIS A046802, with its initial row `1` followed by the Haglund--Zhang
binomial Eulerian polynomials. -/
def A046802 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => HaglundZhang.binomialEulerianPolynomial n

/-- The refined Haglund--Zhang vector used as the interlacing certificate for
`A046802`. -/
abbrev A046802Refined (n : ℕ) : List ℝ[X] :=
  HaglundZhang.binomialRefined n

/-- Positive-index A046802 rows are the Haglund--Zhang terminal polynomials. -/
@[simp] theorem A046802_eq_binomialEulerianPolynomial (n : ℕ) :
    A046802 (n + 1) = HaglundZhang.binomialEulerianPolynomial n := rfl

/-- The A046802 refinement is the Haglund--Zhang refinement. -/
@[simp] theorem A046802Refined_eq_binomialRefined (n : ℕ) :
    A046802Refined n = HaglundZhang.binomialRefined n := rfl

/-- Every A046802 row has constant coefficient one. -/
@[simp] theorem coeff_zero_A046802 (n : ℕ) :
    (A046802 n).coeff 0 = 1 := by
  cases n with
  | zero => simp [A046802]
  | succ n => exact HaglundZhang.coeff_zero_binomialEulerianPolynomial n

/-- Interlacing certificate for the Haglund--Zhang refinement behind A046802. -/
theorem A046802_interlaces (n : ℕ) :
    IsInterlacingSeq0Nonneg (A046802Refined n) :=
  HaglundZhang.binomialRefined_interlaces n

/-- Real-rootedness certificate for each nonzero refined polynomial behind A046802. -/
theorem A046802_refined_realRooted (n : ℕ) :
    ∀ f ∈ A046802Refined n, f ≠ 0 → (f ≠ 0 ∧ f.Splits) :=
  HaglundZhang.binomialRefined_realRooted n

/-- Every A046802 row is nonzero. -/
theorem A046802_ne_zero (n : ℕ) :
    A046802 n ≠ 0 := by
  cases n with
  | zero => exact one_ne_zero
  | succ n => exact HaglundZhang.binomialEulerianPolynomial_ne_zero n

/-- Every A046802 row is nonzero and splits over the reals. -/
theorem A046802_realRooted (n : ℕ) :
    A046802 n ≠ 0 ∧ (A046802 n).Splits := by
  cases n with
  | zero => exact ⟨one_ne_zero, Polynomial.Splits.one⟩
  | succ n => exact HaglundZhang.binomialEulerianPolynomial_realRooted n

/-- Every A046802 row splits over the reals. -/
theorem A046802_splits (n : ℕ) :
    (A046802 n).Splits :=
  (A046802_realRooted n).2

/-! ### Kernel-checked initial rows -/

/-- The zeroth A046802 row. -/
@[simp] theorem A046802_zero :
    A046802 0 = 1 := rfl

/-- The first A046802 row. -/
theorem A046802_one :
    A046802 1 = 1 + X := by
  norm_num [A046802, HaglundZhang.binomialEulerianPolynomial,
    HaglundZhang.terminalPolynomial, HaglundZhang.binomialRefined,
    HaglundZhang.binomialMatrix, HaglundZhang.binomialThresholds,
    HaglundZhang.binomialRows, HaglundZhang.binomialMarker,
    HaglundZhang.row, HaglundZhang.matrix, thresholdMatrix,
    thresholdRow, thresholdEntry, matPolyAction, List.range_succ]

/-- The second A046802 row. -/
theorem A046802_two :
    A046802 2 = 1 + 3 * X + X ^ 2 := by
  norm_num [A046802, HaglundZhang.binomialEulerianPolynomial,
    HaglundZhang.terminalPolynomial, HaglundZhang.binomialRefined,
    HaglundZhang.binomialMatrix, HaglundZhang.binomialThresholds,
    HaglundZhang.binomialRows, HaglundZhang.binomialMarker,
    HaglundZhang.row, HaglundZhang.matrix, thresholdMatrix,
    thresholdRow, thresholdEntry, matPolyAction, List.range_succ]
  ring

/-- The third A046802 row. -/
theorem A046802_three :
    A046802 3 = 1 + 7 * X + 7 * X ^ 2 + X ^ 3 := by
  norm_num [A046802, HaglundZhang.binomialEulerianPolynomial,
    HaglundZhang.terminalPolynomial, HaglundZhang.binomialRefined,
    HaglundZhang.binomialMatrix, HaglundZhang.binomialThresholds,
    HaglundZhang.binomialRows, HaglundZhang.binomialMarker,
    HaglundZhang.row, HaglundZhang.matrix, thresholdMatrix,
    thresholdRow, thresholdEntry, matPolyAction, List.range_succ]
  ring

/-- Consecutive A046802 rows strictly interlace. -/
theorem A046802_strictInterl_succ (n : ℕ) :
    StrictInterl (A046802 n) (A046802 (n + 1)) := by
  cases n with
  | zero =>
      have hdeg : (1 + X : ℝ[X]).natDegree = 1 := by
        simp [show (1 + X : ℝ[X]) = X + C (1 : ℝ) by grind]
      have hstrict : StrictInterl (1 : ℝ[X]) (1 + X) :=
        (interlaces_one_linear hdeg).toStrictInterl
      simpa only [Nat.zero_add, A046802_zero, A046802_one] using hstrict
  | succ n =>
      exact HaglundZhang.binomialEulerianPolynomial_strictInterl_succ n

end OEIS

end RealRooted
