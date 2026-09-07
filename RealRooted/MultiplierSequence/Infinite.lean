import RealRooted.EulerOperator.Shift
import RealRooted.HadamardProduct

/-!
# Infinite multiplier sequences

This file defines an infinite multiplier sequence by requiring every finite
degree restriction to preserve real-rootedness. It proves the equivalent
degree-free diagonal-operator formulation, elementary closure laws, forward
shifts, and bridges to shifted Euler operators and Hadamard products.

The analytic entire-function classification is deliberately not part of this
algebraic layer.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- A multiplier sequence preserves real-rootedness in every finite degree.
The zero output is recorded explicitly to match `IsFiniteMultiplierSequence`.
-/
def IsMultiplierSequence (gamma : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, IsFiniteMultiplierSequence n gamma

/-- A PF multiplier sequence preserves the zero-aware polynomial PF cone in
every finite degree. -/
def IsPFMultiplierSequence (gamma : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, IsFinitePFMultiplierSequence n gamma

/-- The finite-degree definition is equivalent to unrestricted preservation
by the associated diagonal operator. -/
theorem isMultiplierSequence_iff_preserves {gamma : ℕ → ℝ} :
    IsMultiplierSequence gamma ↔
      ∀ {p : ℝ[X]}, p.Splits →
        diagonalOperator gamma p = 0 ∨
          (diagonalOperator gamma p).Splits := by
  constructor
  · intro hgamma p hp
    exact hgamma p.natDegree le_rfl hp
  · intro hgamma _ p _ hp
    exact hgamma hp

/-- The finite-degree PF definition is equivalent to unrestricted
preservation of the polynomial PF cone. -/
theorem isPFMultiplierSequence_iff_preserves {gamma : ℕ → ℝ} :
    IsPFMultiplierSequence gamma ↔
      ∀ {p : ℝ[X]}, IsPFPolynomial p →
        IsPFPolynomial (diagonalOperator gamma p) := by
  constructor
  · intro hgamma p hp
    exact hgamma p.natDegree hp le_rfl
  · intro hgamma _ p hp _
    exact hgamma hp

theorem IsMultiplierSequence.finite {gamma : ℕ → ℝ}
    (hgamma : IsMultiplierSequence gamma) (n : ℕ) :
    IsFiniteMultiplierSequence n gamma :=
  hgamma n

theorem IsPFMultiplierSequence.finite {gamma : ℕ → ℝ}
    (hgamma : IsPFMultiplierSequence gamma) (n : ℕ) :
    IsFinitePFMultiplierSequence n gamma :=
  hgamma n

theorem IsMultiplierSequence.diagonalOperator_eq_zero_or_splits
    {gamma : ℕ → ℝ} (hgamma : IsMultiplierSequence gamma)
    {p : ℝ[X]} (hp : p.Splits) :
    diagonalOperator gamma p = 0 ∨ (diagonalOperator gamma p).Splits :=
  hgamma p.natDegree le_rfl hp

theorem IsPFMultiplierSequence.diagonalOperator_isPF
    {gamma : ℕ → ℝ} (hgamma : IsPFMultiplierSequence gamma)
    {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFPolynomial (diagonalOperator gamma p) :=
  hgamma p.natDegree hp le_rfl

/-- An infinite multiplier sequence may be composed with a finite one on the
finite one's degree box. -/
theorem IsMultiplierSequence.mul_finite
    {gamma delta : ℕ → ℝ} (hgamma : IsMultiplierSequence gamma)
    {n : ℕ} (hdelta : IsFiniteMultiplierSequence n delta) :
    IsFiniteMultiplierSequence n (fun k => gamma k * delta k) :=
  IsFiniteMultiplierSequence.mul (hgamma.finite n) hdelta

/-- PF version of `IsMultiplierSequence.mul_finite`. -/
theorem IsPFMultiplierSequence.mul_finite
    {gamma delta : ℕ → ℝ} (hgamma : IsPFMultiplierSequence gamma)
    {n : ℕ} (hdelta : IsFinitePFMultiplierSequence n delta) :
    IsFinitePFMultiplierSequence n (fun k => gamma k * delta k) :=
  IsFinitePFMultiplierSequence.mul (hgamma.finite n) hdelta

theorem IsMultiplierSequence.mul {gamma delta : ℕ → ℝ}
    (hgamma : IsMultiplierSequence gamma)
    (hdelta : IsMultiplierSequence delta) :
    IsMultiplierSequence (fun k => gamma k * delta k) :=
  fun n => hgamma.mul_finite (hdelta.finite n)

theorem IsPFMultiplierSequence.mul {gamma delta : ℕ → ℝ}
    (hgamma : IsPFMultiplierSequence gamma)
    (hdelta : IsPFMultiplierSequence delta) :
    IsPFMultiplierSequence (fun k => gamma k * delta k) :=
  fun n => hgamma.mul_finite (hdelta.finite n)

theorem isMultiplierSequence_const_sequence (a : ℝ) :
    IsMultiplierSequence (fun _ => a) :=
  fun n => isFiniteMultiplierSequence_const_sequence n a

theorem isMultiplierSequence_one_sequence :
    IsMultiplierSequence (fun _ => (1 : ℝ)) :=
  isMultiplierSequence_const_sequence 1

theorem isMultiplierSequence_zero_sequence :
    IsMultiplierSequence (fun _ => (0 : ℝ)) :=
  isMultiplierSequence_const_sequence 0

theorem isPFMultiplierSequence_const_sequence {a : ℝ} (ha : 0 ≤ a) :
    IsPFMultiplierSequence (fun _ => a) :=
  fun n => isFinitePFMultiplierSequence_const_sequence (n := n) ha

theorem isPFMultiplierSequence_one_sequence :
    IsPFMultiplierSequence (fun _ => (1 : ℝ)) :=
  isPFMultiplierSequence_const_sequence zero_le_one

theorem isPFMultiplierSequence_zero_sequence :
    IsPFMultiplierSequence (fun _ => (0 : ℝ)) :=
  isPFMultiplierSequence_const_sequence le_rfl

/-- Scalar multiplication of a multiplier sequence. No sign condition is
needed for preservation of real-rootedness. -/
theorem IsMultiplierSequence.const_mul {gamma : ℕ → ℝ}
    (hgamma : IsMultiplierSequence gamma) (a : ℝ) :
    IsMultiplierSequence (fun k => a * gamma k) :=
  (isMultiplierSequence_const_sequence a).mul hgamma

/-- Nonnegative scalar multiplication of a PF multiplier sequence. -/
theorem IsPFMultiplierSequence.const_mul {gamma : ℕ → ℝ}
    (hgamma : IsPFMultiplierSequence gamma) {a : ℝ} (ha : 0 ≤ a) :
    IsPFMultiplierSequence (fun k => a * gamma k) :=
  (isPFMultiplierSequence_const_sequence ha).mul hgamma

/-- A PF multiplier sequence is pointwise nonnegative. -/
theorem IsPFMultiplierSequence.nonneg {gamma : ℕ → ℝ}
    (hgamma : IsPFMultiplierSequence gamma) (k : ℕ) :
    0 ≤ gamma k := by
  have hp := hgamma.finite k (isPFPolynomial_X_pow k) (by simp)
  simpa using hp.hasNonnegCoeffs k

/-- A nonnegative multiplier sequence preserves the polynomial PF cone. -/
theorem IsMultiplierSequence.toPF {gamma : ℕ → ℝ}
    (hgamma : IsMultiplierSequence gamma)
    (hnonneg : ∀ k, 0 ≤ gamma k) :
    IsPFMultiplierSequence gamma :=
  fun n =>
    isFinitePFMultiplierSequence_of_finiteMultiplierSequence
      hnonneg (hgamma.finite n)

/-- Multiplying by `X` conjugates a forward shift of a diagonal sequence to
the original diagonal operator. -/
theorem X_mul_diagonalOperator_shift_one (gamma : ℕ → ℝ) (p : ℝ[X]) :
    X * diagonalOperator (fun k => gamma (k + 1)) p =
      diagonalOperator gamma (X * p) := by
  ext k
  cases k with
  | zero => simp
  | succ k => simp [coeff_X_mul]

/-- Dropping the first entry of a finite multiplier sequence consumes one
degree of its certificate. -/
theorem IsFiniteMultiplierSequence.shift_one
    {gamma : ℕ → ℝ} {n : ℕ}
    (hgamma : IsFiniteMultiplierSequence (n + 1) gamma) :
    IsFiniteMultiplierSequence n (fun k => gamma (k + 1)) := by
  intro p hp hp_splits
  by_cases hp0 : p = 0
  · subst p
    simp
  have hXdeg : (X * p).natDegree ≤ n + 1 := by
    rw [Polynomial.natDegree_X_mul hp0]
    exact Nat.add_le_add_right hp 1
  rcases hgamma hXdeg (Polynomial.splits_X_mul.mpr hp_splits) with
    hzero | hsplits
  · left
    have hXzero : X * diagonalOperator (fun k => gamma (k + 1)) p = 0 := by
      rw [X_mul_diagonalOperator_shift_one, hzero]
    exact (mul_eq_zero.mp hXzero).resolve_left X_ne_zero
  · right
    apply Polynomial.splits_X_mul.mp
    rw [X_mul_diagonalOperator_shift_one]
    exact hsplits

theorem IsMultiplierSequence.shift_one {gamma : ℕ → ℝ}
    (hgamma : IsMultiplierSequence gamma) :
    IsMultiplierSequence (fun k => gamma (k + 1)) :=
  fun n => IsFiniteMultiplierSequence.shift_one (hgamma.finite (n + 1))

/-- Forward shifts, the valid reindexing operation for multiplier sequences.
No closure under arbitrary reindexing is asserted. -/
theorem IsMultiplierSequence.shift {gamma : ℕ → ℝ}
    (hgamma : IsMultiplierSequence gamma) (r : ℕ) :
    IsMultiplierSequence (fun k => gamma (k + r)) := by
  induction r with
  | zero => simpa using hgamma
  | succ r ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih.shift_one

/-- The Euler diagonal `k` is an infinite multiplier sequence. -/
theorem isMultiplierSequence_natCast :
    IsMultiplierSequence (fun k => (k : ℝ)) := by
  rw [isMultiplierSequence_iff_preserves]
  intro p hp
  rw [← eulerOperator_eq_diagonalOperator_natCast]
  rcases eq_zero_or_splits_derivative (Or.inr hp) with hder | hder
  · left
    simp [hder]
  · right
    exact Polynomial.splits_X_mul.mpr hder

/-- Every nonnegative integral shift `k + r` of the Euler diagonal is an
infinite multiplier sequence. -/
theorem isMultiplierSequence_natCast_add_nat (r : ℕ) :
    IsMultiplierSequence (fun k => (k : ℝ) + r) := by
  simpa [Nat.cast_add] using isMultiplierSequence_natCast.shift r

theorem isMultiplierSequence_natCast_add_one :
    IsMultiplierSequence (fun k => (k : ℝ) + 1) := by
  simpa using isMultiplierSequence_natCast_add_nat 1

theorem isPFMultiplierSequence_natCast :
    IsPFMultiplierSequence (fun k => (k : ℝ)) :=
  isMultiplierSequence_natCast.toPF fun k => Nat.cast_nonneg k

theorem isPFMultiplierSequence_natCast_add_nat (r : ℕ) :
    IsPFMultiplierSequence (fun k => (k : ℝ) + r) :=
  (isMultiplierSequence_natCast_add_nat r).toPF fun k => by positivity

theorem isPFMultiplierSequence_natCast_add_one :
    IsPFMultiplierSequence (fun k => (k : ℝ) + 1) := by
  simpa using isPFMultiplierSequence_natCast_add_nat 1

/-- The diagonal sequence `k + a` realizes the shifted Euler operator. This
identity holds for every real `a`; multiplier preservation is asserted above
only for the nonnegative integral shifts proved there. -/
theorem diagonalOperator_natCast_add_eq_eulerShift (a : ℝ) (p : ℝ[X]) :
    diagonalOperator (fun k => (k : ℝ) + a) p = eulerShift a p := by
  ext k
  simp

/-- Hadamard multiplication by a polynomial whose coefficient sequence is a
multiplier sequence preserves splitting, with the usual explicit zero case.
-/
theorem IsMultiplierSequence.hadamardProduct_right
    {q : ℝ[X]} (hq : IsMultiplierSequence fun k => q.coeff k)
    {p : ℝ[X]} (hp : p.Splits) :
    hadamardProduct p q = 0 ∨ (hadamardProduct p q).Splits := by
  rw [hadamardProduct_eq_diagonalOperator]
  exact hq.diagonalOperator_eq_zero_or_splits hp

/-- PF version of `IsMultiplierSequence.hadamardProduct_right`. -/
theorem IsPFMultiplierSequence.hadamardProduct_right
    {q : ℝ[X]} (hq : IsPFMultiplierSequence fun k => q.coeff k)
    {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFPolynomial (hadamardProduct p q) := by
  rw [hadamardProduct_eq_diagonalOperator]
  exact hq.diagonalOperator_isPF hp

/-- Every Jensen polynomial of a nonnegative multiplier sequence is PF. -/
theorem isPFPolynomial_jensenPolynomial_of_multiplierSequence
    {gamma : ℕ → ℝ} (hgamma_nonneg : ∀ k, 0 ≤ gamma k)
    (hgamma : IsMultiplierSequence gamma) (n : ℕ) :
    IsPFPolynomial (jensenPolynomial n gamma) :=
  isPFPolynomial_jensenPolynomial_of_finiteMultiplierSequence
    hgamma_nonneg (hgamma.finite n)

/-- Every Jensen polynomial of a PF multiplier sequence is PF. -/
theorem isPFPolynomial_jensenPolynomial_of_PFMultiplierSequence
    {gamma : ℕ → ℝ} (hgamma : IsPFMultiplierSequence gamma) (n : ℕ) :
    IsPFPolynomial (jensenPolynomial n gamma) :=
  isPFPolynomial_jensenPolynomial_of_finitePFMultiplierSequence
    (hgamma.finite n)

end RealRooted
