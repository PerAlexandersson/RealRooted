module

public import RealRooted.HermiteBiehler.OrientedPencil
public import RealRooted.Recurrence.RowModel
public import RealRooted.Recurrence.Uniqueness
public import RealRooted.SymmetricDecomposition.EulerianTransform
public import RealRooted.ThresholdMatrix.HaglundZhang
public import RealRooted.Wronskian.Converse

set_option rr.row.explain true
set_option linter.style.longLine false

/-!
# OEIS A046802

Row zero is `1`; the remaining rows are the terminal polynomials of the
Haglund--Zhang binomial Eulerian refinement, which supplies the interlacing
certificate.

## A recurrence bridge

The downstream rows use the classical order-two recurrence for the binomial
Eulerian polynomials.  We realize that recurrence through the Eulerian
transform.  The adjacent interlacing needed by the row-model registry follows
from the first two entries of the transform's reflection-interlacing row.
-/

@[expose] public section

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

namespace RealRooted.Applications.OEIS.A046802

open EulerianTransform

private theorem image_natDegree (n : ℕ) :
    (image n).natDegree = n := by
  cases n with
  | zero => simp [image]
  | succ n =>
      rw [image, natDegree_X_mul (generalizedEulerian_monic 1 n).ne_zero,
        generalizedEulerian_natDegree]

private theorem image_monic (n : ℕ) : (image n).Monic := by
  cases n with
  | zero => simp [image]
  | succ n =>
      rw [image]
      exact monic_X.mul (generalizedEulerian_monic 1 n)

private theorem one_add_X_monic : (1 + X : ℝ[X]).Monic := by
  simpa only [C_1, add_comm] using (monic_X_add_C (R := ℝ) 1)

private theorem binomial_monic (n : ℕ) : (binomial n).Monic := by
  simpa only [binomial, transform, Polynomial.basisTransformₗ_apply] using
    (Polynomial.basisTransform_monic_of_monic
      (B := image) image_natDegree image_monic (one_add_X_monic.pow n))

private theorem binomial_natDegree (n : ℕ) :
    (binomial n).natDegree = n := by
  apply le_antisymm (natDegree_binomial_le_and_reflect n).1.1
  have hinput : ((1 + X : ℝ[X]) ^ n).Monic :=
    one_add_X_monic.pow n
  have hcoeff := Polynomial.coeff_basisTransform_natDegree_eq_one_of_monic
    (B := image) image_natDegree image_monic hinput
  have hinputDegree : ((1 + X : ℝ[X]) ^ n).natDegree = n := by
    rw [one_add_X_monic.natDegree_pow]
    have hlinear : (1 + X : ℝ[X]).natDegree = 1 := by
      simpa only [C_1, add_comm] using (natDegree_X_add_C (R := ℝ) 1)
    rw [hlinear, mul_one]
  change (binomial n).coeff ((1 + X : ℝ[X]) ^ n |>.natDegree) = 1 at hcoeff
  rw [hinputDegree] at hcoeff
  exact le_natDegree_of_ne_zero (by simp [hcoeff])

private theorem basisImage_one_eq_sub (n : ℕ) :
    basisImage (n + 1) 1 = binomial (n + 1) - binomial n := by
  unfold basisImage binomial
  rw [show n + 1 - 1 = n by lia]
  rw [show X ^ 1 * (1 + X) ^ n =
      (1 + X) ^ (n + 1) - (1 + X) ^ n by
        rw [pow_succ]
        ring]
  exact transform.map_sub _ _

/-- Consecutive Eulerian-transform binomial rows strictly interlace. -/
theorem binomial_strictInterl_succ (n : ℕ) :
    StrictInterl (binomial n) (binomial (n + 1)) := by
  let d := n + 1
  let p := binomial d
  let g := binomial n
  let q := basisImage d 1
  have hdirect : IsInterlacingSeq0NonnegRealRooted (row d) :=
    (row_reflectionInterlacing d).closedSequence.sublist (by
      simp [BrandenVecchi.reflectionClosure])
  let first : Fin (row d).length := ⟨0, by simp [row]⟩
  let second : Fin (row d).length := ⟨1, by simp [row, d]⟩
  have hpq : Interl p q := by
    simpa [p, q, first, second, row, basisImage, binomial] using
      hdirect.interlacingSeq0.interl (i := first) (j := second) (by simp [first, second])
  have hp_pos : HasPosLeadingCoeff p :=
    hasPosLeadingCoeff_of_monic (binomial_monic d)
  have hg_pos : HasPosLeadingCoeff g :=
    hasPosLeadingCoeff_of_monic (binomial_monic n)
  have hq_pos : HasPosLeadingCoeff q := by
    have hinput : (X ^ 1 * (1 + X) ^ (d - 1) : ℝ[X]).Monic :=
      (monic_X.pow 1).mul (one_add_X_monic.pow (d - 1))
    exact hasPosLeadingCoeff_of_monic
      (Polynomial.basisTransform_monic_of_monic
        (B := image) image_natDegree image_monic hinput)
  have hp_ne : p ≠ 0 := hp_pos.ne_zero
  have hq_ne : q ≠ 0 := hq_pos.ne_zero
  have hpq_strict : StrictInterl p q := hpq.toStrictInterl_of_ne hp_ne hq_ne
  have hall_pq : AllComboRealRooted p q :=
    allComboRealRooted_of_strictInterl hpq_strict
  have hq_eq : q = p - g := by
    simp only [q, p, g, d]
    exact basisImage_one_eq_sub n
  have hall_pg : AllComboRealRooted p g := by
    apply hall_pq.linear_recombination
        (f := p) (g := q) (a := 1) (b := 0) (c := 1) (d := -1)
    · simp
    · rw [hq_eq]
      norm_num [map_neg, map_one]
  have hW : ∀ t : ℝ, 0 ≤ (wronskian g p).eval t := by
    intro t
    have h := wronskian_eval_nonneg_of_strictInterl hq_pos hp_pos hpq_strict t
    rw [hq_eq] at h
    convert h using 1
    unfold wronskian
    simp only [derivative_sub]
    ring
  have hstrict :=
    strictInterl_of_allComboRealRooted_of_wronskian_nonneg
      hp_pos hg_pos hall_pg hW
  simpa [p, g, d] using hstrict

/-- The order-two update in the downstream A046802 presentation. -/
def nextRow (n : ℕ) (p q : ℝ[X]) : ℝ[X] :=
  (X - X ^ 2) * p.derivative +
    (1 + C ((n : ℝ) + 2) * X) * p +
      C (-1 - (n : ℝ)) * X * q

private theorem binomial_step (n : ℕ) :
    binomial (n + 2) = nextRow n (binomial (n + 1)) (binomial n) := by
  rw [binomial_succ_succ]
  unfold nextRow
  push_cast
  norm_num [map_add, map_mul, map_ofNat]
  ring

/-- Every sequence with the A046802 initial rows and classical terminal
recurrence has strict adjacent interlacing.  The third advertised row keeps the registry
filter from trying this model on other sequences starting with `1, 1 + X` (A108426). -/
@[rr_row_model]
theorem interlaces_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hone : P 1 = 1 + X)
    (_htwo : P 2 = 1 + 3 * X + X ^ 2)
    (hrec : ∀ n, P (n + 2) = nextRow n (P (n + 1)) (P n))
    (n : ℕ) :
    Interlaces (P n) (P (n + 1)) := by
  have heq := sequence_eq_of_same_lag_two_recurrence nextRow
    (by simpa using hzero) (by simpa using hone) hrec binomial_step
  rw [heq n, heq (n + 1)]
  exact (binomial_strictInterl_succ n).toInterlaces (by
    rw [binomial_natDegree, binomial_natDegree])

end RealRooted.Applications.OEIS.A046802
