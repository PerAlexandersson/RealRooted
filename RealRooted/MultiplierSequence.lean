import RealRooted.PFPolynomial

open Polynomial

noncomputable section

namespace RealRooted

/-!
# Finite multiplier sequences

This file records the finite-degree multiplier-sequence interface needed for
the PF side of the Hadamard/Schur--Szego machinery.  It deliberately stays
independent of `RealRooted.Hadamard`, so work here can proceed while the
Garloff--Wagner theorem file is being edited elsewhere.

The main classical input is the finite Polya--Schur theorem: for nonnegative
diagonal coefficients, preservation of real-rootedness up to degree `n` is
equivalent to the corresponding Jensen polynomial being PF.
-/

/-- Diagonal operator attached to a sequence `gamma`: it sends
`sum a_n X^n` to `sum gamma_n a_n X^n`. -/
def diagonalOperator (gamma : ℕ → ℝ) (p : ℝ[X]) : ℝ[X] :=
  p.sum fun n a => monomial n (gamma n * a)

@[simp] theorem coeff_diagonalOperator
    (gamma : ℕ → ℝ) (p : ℝ[X]) (n : ℕ) :
    (diagonalOperator gamma p).coeff n = gamma n * p.coeff n := by
  classical
  rw [diagonalOperator, Polynomial.coeff_sum]
  simp only [Polynomial.coeff_monomial]
  rw [Polynomial.sum_def]
  rw [Finset.sum_eq_single n]
  · simp
  · intro b _ hbn
    simp [hbn]
  · intro hn
    rw [(Polynomial.notMem_support_iff).mp hn]
    simp

/-- Nonnegative diagonal coefficients preserve nonnegative coefficients. -/
theorem HasNonnegCoeffs.diagonalOperator
    {gamma : ℕ → ℝ} {p : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hgamma : ∀ n, 0 ≤ gamma n) :
    HasNonnegCoeffs (diagonalOperator gamma p) := by
  intro n
  simpa using mul_nonneg (hgamma n) (hp n)

/-- The degree-`n` Jensen polynomial attached to a diagonal sequence. -/
def jensenPolynomial (n : ℕ) (gamma : ℕ → ℝ) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    C ((Nat.choose n k : ℝ) * gamma k) * X ^ k

/-- Finite multiplier sequence up to degree `n`: the diagonal operator
preserves real-rootedness, allowing the zero polynomial. -/
def IsFiniteMultiplierSequence (n : ℕ) (gamma : ℕ → ℝ) : Prop :=
  ∀ {p : ℝ[X]},
    p.natDegree ≤ n →
    p.Splits →
    diagonalOperator gamma p = 0 ∨ (diagonalOperator gamma p).Splits

/-- Finite PF multiplier sequence up to degree `n`: the diagonal operator
preserves the polynomial PF cone on polynomials of degree at most `n`. -/
def IsFinitePFMultiplierSequence (n : ℕ) (gamma : ℕ → ℝ) : Prop :=
  ∀ {p : ℝ[X]},
    IsPFPolynomial p →
    p.natDegree ≤ n →
    IsPFPolynomial (diagonalOperator gamma p)

/-- The finite Polya--Schur theorem in the nonnegative-coefficient convention:
a nonnegative diagonal sequence preserves real-rootedness up to degree `n` if
and only if its degree-`n` Jensen polynomial is PF. -/
def finitePolyaSchurNonnegStatement : Prop :=
  ∀ {n : ℕ} {gamma : ℕ → ℝ},
    (∀ k, 0 ≤ gamma k) →
      (IsFiniteMultiplierSequence n gamma ↔
        IsPFPolynomial (jensenPolynomial n gamma))

/-- Classical finite Polya--Schur theorem, recorded as a theorem stub so later
work can depend on the intended API shape. -/
theorem finitePolyaSchur_nonneg :
    finitePolyaSchurNonnegStatement := by
  sorry

/-- A nonnegative finite multiplier sequence preserves the PF cone on the same
degree range. -/
theorem isFinitePFMultiplierSequence_of_finiteMultiplierSequence
    {n : ℕ} {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hmult : IsFiniteMultiplierSequence n gamma) :
    IsFinitePFMultiplierSequence n gamma := by
  intro p hp hdeg
  by_cases hp0 : p = 0
  · subst p
    rw [show diagonalOperator gamma (0 : ℝ[X]) = 0 by ext k; simp]
    exact IsPFPolynomial.zero
  have hsplit := hmult hdeg (hp.ne_zero_and_splits hp0).2
  rcases hsplit with hzero | hsplits
  · rw [hzero]
    exact IsPFPolynomial.zero
  · exact IsPFPolynomial.of_realRooted_nonneg
      (hp.hasNonnegCoeffs.diagonalOperator hgamma) hsplits

/-- PF preservation obtained from the finite Polya--Schur classification and a
PF Jensen polynomial. -/
theorem isFinitePFMultiplierSequence_of_jensenPolynomial
    (hFPS : finitePolyaSchurNonnegStatement)
    {n : ℕ} {gamma : ℕ → ℝ}
    (hgamma : ∀ k, 0 ≤ gamma k)
    (hjensen : IsPFPolynomial (jensenPolynomial n gamma)) :
    IsFinitePFMultiplierSequence n gamma :=
  isFinitePFMultiplierSequence_of_finiteMultiplierSequence hgamma
    ((hFPS hgamma).2 hjensen)

end RealRooted
