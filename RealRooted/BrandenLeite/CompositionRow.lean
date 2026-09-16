import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Composition rows of positive-order power series

This file develops the finite coefficient algebra behind the rows of
`1 / (1 - x h(z))`.  It is independent of Pólya-frequency, root, and
interlacing arguments.  The final section gives a generic finite
denominator/numerator recurrence interface which retains the low-index
inhomogeneous numerator terms.
-/

open Polynomial BigOperators

namespace RealRooted.BrandenLeite

noncomputable section

/-- The `n`th composition row of a formal power series. -/
def compositionRow {R : Type*} [CommSemiring R]
    (h : PowerSeries R) (n : ℕ) : R[X] :=
  ∑ k ∈ Finset.range (n + 1),
    C (PowerSeries.coeff n (h ^ k)) * X ^ k

/-- A power series with zero constant coefficient has no term of degree below
the exponent in any of its powers. -/
theorem coeff_pow_eq_zero_of_lt {R : Type*} [CommSemiring R]
    {h : PowerSeries R} (hzero : PowerSeries.constantCoeff h = 0)
    {n k : ℕ} (hnk : n < k) :
    PowerSeries.coeff n (h ^ k) = 0 := by
  obtain ⟨u, hu⟩ := PowerSeries.X_dvd_iff.mpr hzero
  rw [hu, mul_pow, PowerSeries.coeff_X_pow_mul']
  simp [Nat.not_le_of_lt hnk]

/-- The finite row definition has the expected coefficient at every index;
outside the displayed finite range both sides vanish. -/
theorem coeff_compositionRow {R : Type*} [CommSemiring R]
    {h : PowerSeries R} (hzero : PowerSeries.constantCoeff h = 0)
    (n k : ℕ) :
    (compositionRow h n).coeff k = PowerSeries.coeff n (h ^ k) := by
  rw [compositionRow, Polynomial.finsetSum_coeff]
  by_cases hk : k ∈ Finset.range (n + 1)
  · rw [Finset.sum_eq_single k]
    · simp
    · intro j hj hjk
      simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Ne.symm hjk]
    · exact fun hnot => (hnot hk).elim
  · have hnk : n < k := by simpa using hk
    rw [coeff_pow_eq_zero_of_lt hzero hnk]
    apply Finset.sum_eq_zero
    intro j hj
    have hjk : j ≠ k := by
      intro heq
      subst j
      exact hk hj
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Ne.symm hjk]

/-- The zeroth composition row is the constant polynomial one. -/
@[simp]
theorem compositionRow_zero {R : Type*} [CommSemiring R]
    (h : PowerSeries R) : compositionRow h 0 = 1 := by
  simp [compositionRow]

/-- Cauchy multiplication with a zero-constant left factor, with the vanished
zeroth summand removed and the remaining index shifted by one. -/
theorem coeff_mul_eq_sum_range_of_constantCoeff_eq_zero
    {R : Type*} [CommSemiring R] {h : PowerSeries R}
    (hzero : PowerSeries.constantCoeff h = 0)
    (g : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff (n + 1) (h * g) =
      ∑ j ∈ Finset.range (n + 1),
        PowerSeries.coeff (j + 1) h * PowerSeries.coeff (n - j) g := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ']
  rw [PowerSeries.coeff_zero_eq_constantCoeff, hzero, zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  congr 2
  lia

/-- Positive-order composition rows satisfy the exact finite convolution
recurrence.  Writing the row index as `n + 1` keeps every natural subtraction
guarded by membership in `range (n + 1)`. -/
theorem compositionRow_succ {R : Type*} [CommSemiring R]
    {h : PowerSeries R} (hzero : PowerSeries.constantCoeff h = 0)
    (n : ℕ) :
    compositionRow h (n + 1) =
      X * ∑ j ∈ Finset.range (n + 1),
        C (PowerSeries.coeff (j + 1) h) * compositionRow h (n - j) := by
  ext k
  rw [coeff_compositionRow hzero]
  cases k with
  | zero =>
      simp
  | succ k =>
      rw [Polynomial.coeff_X_mul]
      rw [Polynomial.finsetSum_coeff]
      simp_rw [Polynomial.coeff_C_mul, coeff_compositionRow hzero]
      rw [← coeff_mul_eq_sum_range_of_constantCoeff_eq_zero hzero (h ^ k) n]
      simp [pow_succ, mul_comm]

/-- The initial value and positive-order convolution recurrence uniquely
determine a polynomial sequence. -/
theorem eq_compositionRow_of_zero_and_succ
    {R : Type*} [CommSemiring R] {h : PowerSeries R}
    (hzero : PowerSeries.constantCoeff h = 0)
    (P : ℕ → R[X]) (hPzero : P 0 = 1)
    (hPsucc : ∀ n,
      P (n + 1) =
        X * ∑ j ∈ Finset.range (n + 1),
          C (PowerSeries.coeff (j + 1) h) * P (n - j)) :
    P = compositionRow h := by
  funext n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      cases n with
      | zero => simpa using hPzero
      | succ n =>
          rw [hPsucc, compositionRow_succ hzero]
          apply congrArg (X * ·)
          apply Finset.sum_congr rfl
          intro j hj
          rw [ih (n - j) (by lia)]

/-! ## Generic denominator/numerator recurrences -/

/-- Coefficients of the product of two sequence-generated power series are
the finite causal convolution of the two sequences. -/
theorem coeff_mk_mul_mk {R : Type*} [Semiring R]
    (D P : ℕ → R) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk D * PowerSeries.mk P) =
      ∑ j ∈ Finset.range (n + 1), D j * P (n - j) := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp

/-- A formal denominator/numerator identity is equivalent to its family of
finite coefficient identities. -/
theorem mk_mul_mk_eq_mk_iff {R : Type*} [Semiring R]
    (D P E : ℕ → R) :
    PowerSeries.mk D * PowerSeries.mk P = PowerSeries.mk E ↔
      ∀ n, ∑ j ∈ Finset.range (n + 1), D j * P (n - j) = E n := by
  constructor
  · intro h n
    have hcoeff := congrArg (PowerSeries.coeff n) h
    simpa [coeff_mk_mul_mk] using hcoeff
  · intro h
    apply PowerSeries.ext
    intro n
    simpa [coeff_mk_mul_mk] using h n

/-- Explicit inhomogeneous recurrence extracted from a finite
denominator/numerator coefficient identity.  The numerator term `E n` is
present at every index. -/
theorem eq_sub_sum_of_finite_denominator_numerator
    {R : Type*} [Ring R] {D E P : ℕ → R}
    (hDzero : D 0 = 1)
    (hP : ∀ n,
      ∑ j ∈ Finset.range (n + 1), D j * P (n - j) = E n)
    (n : ℕ) :
    P n = E n -
      ∑ j ∈ Finset.range n, D (j + 1) * P (n - (j + 1)) := by
  have hn := hP n
  rw [Finset.sum_range_succ', hDzero, one_mul] at hn
  rw [eq_sub_iff_add_eq]
  simpa [add_comm] using hn

/-- A causal denominator with constant coefficient one has at most one
coefficient sequence for a fixed numerator.  No homogeneity assumption is
made on the numerator. -/
theorem eq_of_finite_denominator_numerator
    {R : Type*} [Semiring R] [IsLeftCancelAdd R]
    {D E P Q : ℕ → R}
    (hDzero : D 0 = 1)
    (hP : ∀ n,
      ∑ j ∈ Finset.range (n + 1), D j * P (n - j) = E n)
    (hQ : ∀ n,
      ∑ j ∈ Finset.range (n + 1), D j * Q (n - j) = E n) :
    P = Q := by
  funext n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      have hp := hP n
      have hq := hQ n
      rw [Finset.sum_range_succ', hDzero, one_mul] at hp hq
      have htail :
          (∑ j ∈ Finset.range n, D (j + 1) * P (n - (j + 1))) =
            ∑ j ∈ Finset.range n, D (j + 1) * Q (n - (j + 1)) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [ih (n - (j + 1))
          (Nat.sub_lt (Nat.zero_lt_of_lt (Finset.mem_range.mp hj))
            (Nat.succ_pos j))]
      rw [htail] at hp
      exact add_left_cancel (hp.trans hq.symm)

/-- Formal-series uniqueness for a denominator with constant coefficient one,
derived from the finite coefficient theorem. -/
theorem eq_of_mk_mul_mk_eq_mk
    {R : Type*} [Semiring R] [IsLeftCancelAdd R]
    {D E P Q : ℕ → R}
    (hDzero : D 0 = 1)
    (hP : PowerSeries.mk D * PowerSeries.mk P = PowerSeries.mk E)
    (hQ : PowerSeries.mk D * PowerSeries.mk Q = PowerSeries.mk E) :
    P = Q := by
  exact eq_of_finite_denominator_numerator hDzero
    ((mk_mul_mk_eq_mk_iff D P E).mp hP)
    ((mk_mul_mk_eq_mk_iff D Q E).mp hQ)

end

end RealRooted.BrandenLeite
