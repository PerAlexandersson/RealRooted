import RealRooted.Tactic.PFBidiagonal

open Polynomial

noncomputable section

namespace RealRooted
namespace TacticExamples

example
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hpres : ∀ n : Nat, BidiagonalPFPreserver (alpha n) (beta n) (d n))
    (hrec : ∀ n : Nat,
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) := by
  rr_pf_bidiagonal_sequence using
    preserver := hpres,
    base := hbase,
    degree := hdeg,
    recurrence := hrec

example
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hpres : ∀ n : Nat, BidiagonalPFPreserver (alpha n) (beta n) (d n))
    (hrec : ∀ n : Nat,
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n))
    (n : Nat) :
    IsPFPolynomial (P n) := by
  rr_pf_bidiagonal_sequence using
    preserver := hpres,
    base := hbase,
    degree := hdeg,
    recurrence := hrec

example
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hpres : ∀ n : Nat, BidiagonalPFPreserver (alpha n) (beta n) (d n))
    (hrec : ∀ n : Nat,
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n)) :
    ∀ n : Nat, HasNonnegCoeffs (P n) := by
  rr_pf_bidiagonal_sequence using
    preserver := hpres,
    base := hbase,
    degree := hdeg,
    recurrence := hrec

example
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hpres : ∀ n : Nat, BidiagonalPFPreserver (alpha n) (beta n) (d n))
    (hrec : ∀ n : Nat,
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n))
    (n : Nat) :
    HasNonnegCoeffs (P n) := by
  rr_pf_bidiagonal_sequence using
    preserver := hpres,
    base := hbase,
    degree := hdeg,
    recurrence := hrec

example
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hpres : ∀ n : Nat, BidiagonalPFPreserver (alpha n) (beta n) (d n))
    (hrec : ∀ n : Nat,
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n)) :
    ∀ n : Nat, (P n).Splits := by
  rr_pf_bidiagonal_sequence using
    preserver := hpres,
    base := hbase,
    degree := hdeg,
    recurrence := hrec

example
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hpres : ∀ n : Nat, BidiagonalPFPreserver (alpha n) (beta n) (d n))
    (hrec : ∀ n : Nat,
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n))
    (n : Nat) :
    (P n).Splits := by
  rr_pf_bidiagonal_sequence using
    preserver := hpres,
    base := hbase,
    degree := hdeg,
    recurrence := hrec

example
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hpres : ∀ n : Nat, BidiagonalPFPreserver (alpha n) (beta n) (d n))
    (hrec : ∀ n : Nat,
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n))
    (n : Nat) :
    P n = 0 ∨ (P n).Splits := by
  rr_pf_bidiagonal_sequence using
    preserver := hpres,
    base := hbase,
    degree := hdeg,
    recurrence := hrec

example
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hpres : ∀ n : Nat, BidiagonalPFPreserver (alpha n) (beta n) (d n))
    (hne : ∀ n : Nat, P n ≠ 0)
    (hrec : ∀ n : Nat,
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_pf_bidiagonal_sequence using
    preserver := hpres,
    base := hbase,
    degree := hdeg,
    recurrence := hrec,
    nonzero := hne

example
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hpres : ∀ n : Nat, BidiagonalPFPreserver (alpha n) (beta n) (d n))
    (hne : ∀ n : Nat, P n ≠ 0)
    (hrec : ∀ n : Nat,
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n))
    (n : Nat) :
    P n ≠ 0 ∧ (P n).Splits := by
  rr_pf_bidiagonal_sequence using
    preserver := hpres,
    base := hbase,
    degree := hdeg,
    recurrence := hrec,
    nonzero := hne

example
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hpres : ∀ n : Nat, BidiagonalPFPreserver (alpha n) (beta n) (d n))
    (hne : ∀ n : Nat, P n ≠ 0)
    (hrec : ∀ n : Nat,
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_pf_bidiagonal_sequence using
    preserver := hpres,
    base := hbase,
    degree := hdeg,
    recurrence := hrec

example
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hpres : ∀ n : Nat, BidiagonalPFPreserver (alpha n) (beta n) (d n))
    (hne : ∀ n : Nat, P n ≠ 0)
    (hrec : ∀ n : Nat,
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n))
    (n : Nat) :
    P n ≠ 0 ∧ (P n).Splits := by
  rr_pf_bidiagonal_sequence using
    preserver := hpres,
    base := hbase,
    degree := hdeg,
    recurrence := hrec

example
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat,
      BidiagonalJensenPencilCertificate (alpha n) (beta n) (d n))
    (hne : ∀ n : Nat, P n ≠ 0)
    (hrec : ∀ n : Nat,
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_pf_bidiagonal_sequence using
    jensen_backend := hbackend,
    certificate := hcert,
    base := hbase,
    degree := hdeg,
    recurrence := hrec,
    nonzero := hne

example
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat,
      BidiagonalCubicResidualCertificate (alpha n) (beta n) (d n))
    (hne : ∀ n : Nat, P n ≠ 0)
    (hrec : ∀ n : Nat,
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_pf_bidiagonal_sequence using
    jensen_backend := hbackend,
    cubic_certificate := hcert,
    base := hbase,
    degree := hdeg,
    recurrence := hrec,
    nonzero := hne

/-- Coefficient check for the new operator.  OEIS second-derivative
normalization should reduce each concrete recurrence to this form. -/
example (alpha beta : ℕ → ℝ) (f : ℝ[X]) (k : ℕ) :
    (bidiagonalOperator alpha beta f).coeff (k + 1) =
      alpha (k + 1) * f.coeff (k + 1) + beta k * f.coeff k := by
  simp

example {alpha beta : ℕ → ℝ} {p : ℝ[X]}
    (hp : HasNonnegCoeffs p)
    (halpha : ∀ n : ℕ, 0 ≤ alpha n)
    (hbeta : ∀ n : ℕ, 0 ≤ beta n) :
    HasNonnegCoeffs (bidiagonalOperator alpha beta p) :=
  hp.bidiagonalOperator halpha hbeta

example (a0 a1 b1 b2 c2 c3 : ℝ) (p : ℝ[X]) :
    secondDerivativeBidiagonalForm a0 a1 b1 b2 c2 c3 p =
      bidiagonalOperator
        (fun k => secondDerivativeQuadraticCoeff a0 b1 c2 k)
        (fun k => secondDerivativeQuadraticCoeff a1 b2 c3 k)
        p :=
  secondDerivativeBidiagonalForm_eq_bidiagonalOperator a0 a1 b1 b2 c2 c3 p

example
    {P : Nat → ℝ[X]} {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hpres : ∀ n : Nat,
      BidiagonalPFPreserver
        (fun k => secondDerivativeQuadraticCoeff (a0 n) (b1 n) (c2 n) k)
        (fun k => secondDerivativeQuadraticCoeff (a1 n) (b2 n) (c3 n) k)
        (d n))
    (hrec : ∀ n : Nat,
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) := by
  rr_pf_second_derivative_bidiagonal_sequence using
    preserver := hpres,
    base := hbase,
    degree := hdeg,
    recurrence := hrec

example
    {P : Nat → ℝ[X]} {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hpres : ∀ n : Nat,
      BidiagonalPFPreserver
        (fun k => secondDerivativeQuadraticCoeff (a0 n) (b1 n) (c2 n) k)
        (fun k => secondDerivativeQuadraticCoeff (a1 n) (b2 n) (c3 n) k)
        (d n))
    (hne : ∀ n : Nat, P n ≠ 0)
    (hrec : ∀ n : Nat,
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_pf_second_derivative_bidiagonal_sequence using
    preserver := hpres,
    base := hbase,
    degree := hdeg,
    recurrence := hrec,
    nonzero := hne

example
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ}
    {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hpres : ∀ n : Nat, BidiagonalPFPreserver (alpha n) (beta n) (d n))
    (hnorm : ∀ n : Nat,
      secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n) =
        bidiagonalOperator (alpha n) (beta n) (P n))
    (hrec : ∀ n : Nat,
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) := by
  rr_pf_second_derivative_bidiagonal_sequence using
    preserver := hpres,
    base := hbase,
    degree := hdeg,
    normalizer := hnorm,
    recurrence := hrec

example
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ}
    {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hpres : ∀ n : Nat, BidiagonalPFPreserver (alpha n) (beta n) (d n))
    (hnorm : ∀ n : Nat,
      secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n) =
        bidiagonalOperator (alpha n) (beta n) (P n))
    (hne : ∀ n : Nat, P n ≠ 0)
    (hrec : ∀ n : Nat,
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_pf_second_derivative_bidiagonal_sequence using
    preserver := hpres,
    base := hbase,
    degree := hdeg,
    normalizer := hnorm,
    recurrence := hrec,
    nonzero := hne

example
    {P : Nat → ℝ[X]} {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat,
      BidiagonalJensenPencilCertificate
        (fun k => secondDerivativeQuadraticCoeff (a0 n) (b1 n) (c2 n) k)
        (fun k => secondDerivativeQuadraticCoeff (a1 n) (b2 n) (c3 n) k)
        (d n))
    (hrec : ∀ n : Nat,
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) := by
  rr_pf_second_derivative_bidiagonal_sequence using
    jensen_backend := hbackend,
    certificate := hcert,
    base := hbase,
    degree := hdeg,
    recurrence := hrec

example
    {P : Nat → ℝ[X]} {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat,
      BidiagonalJensenPencilCertificate
        (fun k => secondDerivativeQuadraticCoeff (a0 n) (b1 n) (c2 n) k)
        (fun k => secondDerivativeQuadraticCoeff (a1 n) (b2 n) (c3 n) k)
        (d n))
    (hne : ∀ n : Nat, P n ≠ 0)
    (hrec : ∀ n : Nat,
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_pf_second_derivative_bidiagonal_sequence using
    jensen_backend := hbackend,
    certificate := hcert,
    base := hbase,
    degree := hdeg,
    recurrence := hrec,
    nonzero := hne

example
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ}
    {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat,
      BidiagonalJensenPencilCertificate (alpha n) (beta n) (d n))
    (hnorm : ∀ n : Nat,
      secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n) =
        bidiagonalOperator (alpha n) (beta n) (P n))
    (hrec : ∀ n : Nat,
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) := by
  rr_pf_second_derivative_bidiagonal_sequence using
    jensen_backend := hbackend,
    certificate := hcert,
    base := hbase,
    degree := hdeg,
    normalizer := hnorm,
    recurrence := hrec

example
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ}
    {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat,
      BidiagonalJensenPencilCertificate (alpha n) (beta n) (d n))
    (hnorm : ∀ n : Nat,
      secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n) =
        bidiagonalOperator (alpha n) (beta n) (P n))
    (hne : ∀ n : Nat, P n ≠ 0)
    (hrec : ∀ n : Nat,
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_pf_second_derivative_bidiagonal_sequence using
    jensen_backend := hbackend,
    certificate := hcert,
    base := hbase,
    degree := hdeg,
    normalizer := hnorm,
    recurrence := hrec,
    nonzero := hne

/-- The coefficient multiplier for the A036969 recurrence. -/
def a036969Alpha (k : ℕ) : ℝ :=
  ((k : ℝ) + 1) ^ 2

/-- The shifted coefficient multiplier for the A036969 recurrence. -/
def a036969Beta (_k : ℕ) : ℝ :=
  1

/-- The residual after removing the common `(1 + X)^(d-2)` Jensen factor for
the A036969 `alpha` endpoint. -/
def a036969ResidualAlpha (d : ℕ) : ℝ[X] :=
  C (1 : ℝ) +
    C (3 * (d : ℝ) + 2) * X +
    C (((d : ℝ) + 1) ^ 2) * X ^ 2

/-- The residual after removing the common `(1 + X)^(d-2)` Jensen factor for
the A036969 shifted `beta` endpoint. -/
def a036969ResidualBeta : ℝ[X] :=
  X * (X + 1) ^ 2

/-- The residual pencil for the A036969 PF-bidiagonal certificate. -/
def a036969ResidualPencil (d : ℕ) (lam : ℝ) : ℝ[X] :=
  a036969ResidualAlpha d + C lam * a036969ResidualBeta

/-- The A036969 alpha residual has nonnegative coefficients. -/
theorem a036969ResidualAlpha_hasNonnegCoeffs (d : ℕ) :
    HasNonnegCoeffs (a036969ResidualAlpha d) := by
  have h0 : HasNonnegCoeffs (1 : ℝ[X]) := hasNonnegCoeffs_one
  have h1 : HasNonnegCoeffs (C (3 * (d : ℝ) + 2) * X) :=
    nonnegCoeffs_C_mul (by positivity) hasNonnegCoeffs_X
  have h2 : HasNonnegCoeffs (C (((d : ℝ) + 1) ^ 2) * X ^ 2) :=
    nonnegCoeffs_C_mul (by positivity) (hasNonnegCoeffs_X.pow 2)
  simpa [a036969ResidualAlpha, add_assoc] using h0.add (h1.add h2)

/-- The A036969 alpha residual is at most quadratic. -/
theorem natDegree_a036969ResidualAlpha_le (d : ℕ) :
    (a036969ResidualAlpha d).natDegree ≤ 3 := by
  unfold a036969ResidualAlpha
  compute_degree
  norm_num

/-- The A036969 alpha residual has nonnegative cubic discriminant. -/
theorem cubicDiscr_a036969ResidualAlpha_nonneg (d : ℕ) :
    0 ≤ cubicDiscr (a036969ResidualAlpha d) := by
  have hpoly :
      a036969ResidualAlpha d =
        C (0 : ℝ) * X ^ 3 +
          C (((d : ℝ) + 1) ^ 2) * X ^ 2 +
            C (3 * (d : ℝ) + 2) * X + C (1 : ℝ) := by
    simp [a036969ResidualAlpha]
    ring
  have hdisc :
      cubicDiscr (a036969ResidualAlpha d) =
        ((d : ℝ) + 1) ^ 4 * (5 * (d : ℝ) ^ 2 + 4 * (d : ℝ)) := by
    rw [hpoly, cubicDiscr_of_coeffs]
    ring
  rw [hdisc]
  positivity

/-- Cubic-discriminant certificate for the A036969 alpha residual. -/
theorem a036969ResidualAlpha_cubicPFDiscriminantCertificate (d : ℕ) :
    CubicPFDiscriminantCertificate (a036969ResidualAlpha d) :=
  ⟨a036969ResidualAlpha_hasNonnegCoeffs d,
    natDegree_a036969ResidualAlpha_le d,
    cubicDiscr_a036969ResidualAlpha_nonneg d⟩

/-- Cubic-discriminant certificate for the A036969 beta residual. -/
theorem a036969ResidualBeta_cubicPFDiscriminantCertificate :
    CubicPFDiscriminantCertificate a036969ResidualBeta := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [a036969ResidualBeta, mul_assoc] using
      (isPFPolynomial_X.mul (isPFPolynomial_X_add_one.pow 2)).hasNonnegCoeffs
  · unfold a036969ResidualBeta
    compute_degree
  · have hdeg : a036969ResidualBeta.natDegree ≤ 3 := by
      unfold a036969ResidualBeta
      compute_degree
    have hsplit : a036969ResidualBeta.Splits := by
      have hpf :=
        (isPFPolynomial_X.mul (isPFPolynomial_X_add_one.pow 2)).eq_zero_or_splits
      rcases hpf with hzero | hsplit
      · exfalso
        have hX : (X : ℝ[X]) ≠ 0 := X_ne_zero
        have hbase : (X + 1 : ℝ[X]) ≠ 0 := by
          simpa using Polynomial.X_add_C_ne_zero (1 : ℝ)
        have hpow : (X + 1 : ℝ[X]) ^ 2 ≠ 0 := pow_ne_zero 2 hbase
        exact (mul_ne_zero hX hpow) hzero
      · simpa [a036969ResidualBeta] using hsplit
    exact cubicDiscr_nonneg_of_splits_natDegree_le_three hdeg hsplit

private theorem a036969ResidualBeta_coeff_zero :
    a036969ResidualBeta.coeff 0 = 0 := by
  rw [a036969ResidualBeta]
  ring_nf
  repeat rw [Polynomial.coeff_add]
  simp [Polynomial.coeff_X_pow, Polynomial.coeff_X]

private theorem a036969ResidualBeta_coeff_one :
    a036969ResidualBeta.coeff 1 = 1 := by
  rw [a036969ResidualBeta]
  ring_nf
  repeat rw [Polynomial.coeff_add]
  simp [Polynomial.coeff_X_pow, Polynomial.coeff_X]

private theorem a036969ResidualBeta_coeff_two :
    a036969ResidualBeta.coeff 2 = 2 := by
  rw [a036969ResidualBeta]
  ring_nf
  repeat rw [Polynomial.coeff_add]
  simp [Polynomial.coeff_X_pow, Polynomial.coeff_X]

private theorem a036969ResidualBeta_coeff_three :
    a036969ResidualBeta.coeff 3 = 1 := by
  rw [a036969ResidualBeta]
  ring_nf
  repeat rw [Polynomial.coeff_add]
  simp [Polynomial.coeff_X_pow, Polynomial.coeff_X]

private theorem a036969ResidualAlpha_coeff_three (d : ℕ) :
    (a036969ResidualAlpha d).coeff 3 = 0 := by
  rw [a036969ResidualAlpha]
  rw [Polynomial.coeff_add, Polynomial.coeff_add]
  rw [Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul_X_pow]
  simp [Polynomial.coeff_one]

private theorem a036969ResidualAlpha_coeff_two (d : ℕ) :
    (a036969ResidualAlpha d).coeff 2 = ((d : ℝ) + 1) ^ 2 := by
  rw [a036969ResidualAlpha]
  rw [Polynomial.coeff_add, Polynomial.coeff_add]
  rw [Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul_X_pow]
  simp [Polynomial.coeff_one]

private theorem a036969ResidualAlpha_coeff_one (d : ℕ) :
    (a036969ResidualAlpha d).coeff 1 = 3 * (d : ℝ) + 2 := by
  rw [a036969ResidualAlpha]
  rw [Polynomial.coeff_add, Polynomial.coeff_add]
  rw [Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul_X_pow]
  simp [Polynomial.coeff_one]

private theorem a036969ResidualAlpha_coeff_zero (d : ℕ) :
    (a036969ResidualAlpha d).coeff 0 = 1 := by
  rw [a036969ResidualAlpha]
  rw [Polynomial.coeff_add, Polynomial.coeff_add]
  rw [Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul_X_pow]
  simp [Polynomial.coeff_one]

private theorem a036969ResidualPencil_coeff_three (d : ℕ) (lam : ℝ) :
    (a036969ResidualPencil d lam).coeff 3 = lam := by
  rw [a036969ResidualPencil, Polynomial.coeff_add, a036969ResidualAlpha_coeff_three]
  have hterm : (C lam * a036969ResidualBeta).coeff 3 = lam := by
    rw [Polynomial.coeff_C_mul, a036969ResidualBeta_coeff_three]
    ring
  rw [hterm]
  ring

private theorem a036969ResidualPencil_coeff_two (d : ℕ) (lam : ℝ) :
    (a036969ResidualPencil d lam).coeff 2 =
      ((d : ℝ) + 1) ^ 2 + 2 * lam := by
  rw [a036969ResidualPencil, Polynomial.coeff_add, a036969ResidualAlpha_coeff_two]
  have hterm : (C lam * a036969ResidualBeta).coeff 2 = 2 * lam := by
    rw [Polynomial.coeff_C_mul, a036969ResidualBeta_coeff_two]
    ring
  rw [hterm]

private theorem a036969ResidualPencil_coeff_one (d : ℕ) (lam : ℝ) :
    (a036969ResidualPencil d lam).coeff 1 =
      3 * (d : ℝ) + 2 + lam := by
  rw [a036969ResidualPencil, Polynomial.coeff_add, a036969ResidualAlpha_coeff_one]
  have hterm : (C lam * a036969ResidualBeta).coeff 1 = lam := by
    rw [Polynomial.coeff_C_mul, a036969ResidualBeta_coeff_one]
    ring
  rw [hterm]

private theorem a036969ResidualPencil_coeff_zero (d : ℕ) (lam : ℝ) :
    (a036969ResidualPencil d lam).coeff 0 = 1 := by
  rw [a036969ResidualPencil, Polynomial.coeff_add, a036969ResidualAlpha_coeff_zero]
  have hterm : (C lam * a036969ResidualBeta).coeff 0 = 0 := by
    rw [Polynomial.coeff_C_mul, a036969ResidualBeta_coeff_zero]
    ring
  rw [hterm]
  ring

/-- The A036969 residual pencil has nonnegative coefficients for
nonnegative pencil parameter. -/
theorem a036969ResidualPencil_hasNonnegCoeffs
    (d : ℕ) {lam : ℝ} (hlam : 0 ≤ lam) :
    HasNonnegCoeffs (a036969ResidualPencil d lam) := by
  have hbeta : HasNonnegCoeffs a036969ResidualBeta := by
    simpa [a036969ResidualBeta, mul_assoc] using
      (isPFPolynomial_X.mul (isPFPolynomial_X_add_one.pow 2)).hasNonnegCoeffs
  have hterm : HasNonnegCoeffs (C lam * a036969ResidualBeta) :=
    nonnegCoeffs_C_mul hlam hbeta
  simpa [a036969ResidualPencil] using
    (a036969ResidualAlpha_hasNonnegCoeffs d).add hterm

/-- The A036969 residual pencil has degree at most three. -/
theorem natDegree_a036969ResidualPencil_le (d : ℕ) (lam : ℝ) :
    (a036969ResidualPencil d lam).natDegree ≤ 3 := by
  unfold a036969ResidualPencil a036969ResidualAlpha a036969ResidualBeta
  compute_degree

/-- The A036969 residual pencil has nonnegative cubic discriminant for
nonnegative pencil parameter. -/
theorem cubicDiscr_a036969ResidualPencil_nonneg
    (d : ℕ) {lam : ℝ} (hlam : 0 ≤ lam) :
    0 ≤ cubicDiscr (a036969ResidualPencil d lam) := by
  cases d with
  | zero =>
      unfold cubicDiscr
      rw [a036969ResidualPencil_coeff_three, a036969ResidualPencil_coeff_two,
        a036969ResidualPencil_coeff_one, a036969ResidualPencil_coeff_zero]
      ring_nf
      norm_num
  | succ e =>
      have hdisc :
          cubicDiscr (a036969ResidualPencil (Nat.succ e) lam) =
            ((e : ℝ) + 1) *
              (5 * (e : ℝ) ^ 5 +
                6 * (e : ℝ) ^ 4 * lam +
                49 * (e : ℝ) ^ 4 +
                (e : ℝ) ^ 3 * lam ^ 2 +
                64 * (e : ℝ) ^ 3 * lam +
                192 * (e : ℝ) ^ 3 +
                31 * (e : ℝ) ^ 2 * lam ^ 2 +
                178 * (e : ℝ) ^ 2 * lam +
                376 * (e : ℝ) ^ 2 +
                4 * (e : ℝ) * lam ^ 3 +
                27 * (e : ℝ) * lam ^ 2 +
                168 * (e : ℝ) * lam +
                368 * (e : ℝ) +
                9 * lam ^ 2 + 36 * lam + 144) := by
        unfold cubicDiscr
        rw [a036969ResidualPencil_coeff_three, a036969ResidualPencil_coeff_two,
          a036969ResidualPencil_coeff_one, a036969ResidualPencil_coeff_zero]
        norm_num [Nat.cast_succ]
        ring_nf
      rw [hdisc]
      positivity

/-- Cubic-discriminant certificate for the A036969 residual pencil. -/
theorem a036969ResidualPencil_cubicPFDiscriminantCertificate
    (d : ℕ) {lam : ℝ} (hlam : 0 ≤ lam) :
    CubicPFDiscriminantCertificate (a036969ResidualPencil d lam) :=
  ⟨a036969ResidualPencil_hasNonnegCoeffs d hlam,
    natDegree_a036969ResidualPencil_le d lam,
    cubicDiscr_a036969ResidualPencil_nonneg d hlam⟩

/-- The A036969 differential recurrence normalizes to a coefficient-bidiagonal
operator with `alpha(k)=(k+1)^2` and `beta(k)=1`. -/
theorem secondDerivativeBidiagonalForm_a036969 (p : ℝ[X]) :
    secondDerivativeBidiagonalForm 1 1 3 0 1 0 p =
      bidiagonalOperator a036969Alpha a036969Beta p := by
  rw [secondDerivativeBidiagonalForm_eq_bidiagonalOperator]
  congr
  · funext k
    simp [a036969Alpha, secondDerivativeQuadraticCoeff]
    ring
  · funext k
    simp [a036969Beta, secondDerivativeQuadraticCoeff]

/-- The coefficient multiplier for the A071951 recurrence. -/
def a071951Alpha (k : ℕ) : ℝ :=
  ((k : ℝ) + 1) * ((k : ℝ) + 2)

/-- The shifted coefficient multiplier for the A071951 recurrence. -/
def a071951Beta (_k : ℕ) : ℝ :=
  1

/-- The A071951 differential recurrence normalizes to a coefficient-bidiagonal
operator with `alpha(k)=(k+1)(k+2)` and `beta(k)=1`. -/
theorem secondDerivativeBidiagonalForm_a071951 (p : ℝ[X]) :
    secondDerivativeBidiagonalForm 2 1 4 0 1 0 p =
      bidiagonalOperator a071951Alpha a071951Beta p := by
  refine secondDerivativeBidiagonalForm_eq_bidiagonalOperator_of_coeff_eq p ?_ ?_
  · intro k
    simp [a071951Alpha, secondDerivativeQuadraticCoeff]
    ring
  · intro k
    simp [a071951Beta, secondDerivativeQuadraticCoeff]

/-- The coefficient multiplier for the A080248 recurrence. -/
def a080248Alpha (k : ℕ) : ℝ :=
  (((k : ℝ) + 1) * ((k : ℝ) + 2)) / 2

/-- The shifted coefficient multiplier for the A080248 recurrence. -/
def a080248Beta (_k : ℕ) : ℝ :=
  1

/-- The A080248 differential recurrence normalizes to a coefficient-bidiagonal
operator with `alpha(k)=(k+1)(k+2)/2` and `beta(k)=1`. -/
theorem secondDerivativeBidiagonalForm_a080248 (p : ℝ[X]) :
    secondDerivativeBidiagonalForm 1 1 2 0 (1 / 2) 0 p =
      bidiagonalOperator a080248Alpha a080248Beta p := by
  refine secondDerivativeBidiagonalForm_eq_bidiagonalOperator_of_coeff_eq p ?_ ?_
  · intro k
    simp [a080248Alpha, secondDerivativeQuadraticCoeff]
    ring
  · intro k
    simp [a080248Beta, secondDerivativeQuadraticCoeff]

/-- The coefficient multiplier for the A156289 recurrence. -/
def a156289Alpha (k : ℕ) : ℝ :=
  ((k : ℝ) + 1) ^ 2

/-- The shifted coefficient multiplier for the A156289 recurrence. -/
def a156289Beta (k : ℕ) : ℝ :=
  2 * (k : ℝ) + 3

/-- The A156289 differential recurrence normalizes to a coefficient-bidiagonal
operator with `alpha(k)=(k+1)^2` and `beta(k)=2k+3`. -/
theorem secondDerivativeBidiagonalForm_a156289 (p : ℝ[X]) :
    secondDerivativeBidiagonalForm 1 3 3 2 1 0 p =
      bidiagonalOperator a156289Alpha a156289Beta p := by
  refine secondDerivativeBidiagonalForm_eq_bidiagonalOperator_of_coeff_eq p ?_ ?_
  · intro k
    simp [a156289Alpha, secondDerivativeQuadraticCoeff]
    ring
  · intro k
    simp [a156289Beta, secondDerivativeQuadraticCoeff]
    ring

/-- The coefficient multiplier for the A160562 recurrence. -/
def a160562Alpha (k : ℕ) : ℝ :=
  (2 * (k : ℝ) + 1) ^ 2

/-- The shifted coefficient multiplier for the A160562 recurrence. -/
def a160562Beta (_k : ℕ) : ℝ :=
  1

/-- The A160562 differential recurrence normalizes to a coefficient-bidiagonal
operator with `alpha(k)=(2k+1)^2` and `beta(k)=1`. -/
theorem secondDerivativeBidiagonalForm_a160562 (p : ℝ[X]) :
    secondDerivativeBidiagonalForm 1 1 8 0 4 0 p =
      bidiagonalOperator a160562Alpha a160562Beta p := by
  refine secondDerivativeBidiagonalForm_eq_bidiagonalOperator_of_coeff_eq p ?_ ?_
  · intro k
    simp [a160562Alpha, secondDerivativeQuadraticCoeff]
    ring
  · intro k
    simp [a160562Beta, secondDerivativeQuadraticCoeff]

/-- The coefficient multiplier for the A269945 recurrence. -/
def a269945Alpha (k : ℕ) : ℝ :=
  (k : ℝ) ^ 2

/-- The shifted coefficient multiplier for the A269945 recurrence. -/
def a269945Beta (_k : ℕ) : ℝ :=
  1

/-- The A269945 differential recurrence normalizes to a coefficient-bidiagonal
operator with `alpha(k)=k^2` and `beta(k)=1`. -/
theorem secondDerivativeBidiagonalForm_a269945 (p : ℝ[X]) :
    secondDerivativeBidiagonalForm 0 1 1 0 1 0 p =
      bidiagonalOperator a269945Alpha a269945Beta p := by
  refine secondDerivativeBidiagonalForm_eq_bidiagonalOperator_of_coeff_eq p ?_ ?_
  · intro k
    simp [a269945Alpha, secondDerivativeQuadraticCoeff]
    ring
  · intro k
    simp [a269945Beta, secondDerivativeQuadraticCoeff]

/-- The coefficient multiplier for the A166960 recurrence. -/
def a166960Alpha (k : ℕ) : ℝ :=
  ((k : ℝ) + 1) ^ 2

/-- The shifted coefficient multiplier for the A166960 recurrence. -/
def a166960Beta (n k : ℕ) : ℝ :=
  (n : ℝ) + 1 - (k : ℝ)

/-- The A166960 differential recurrence normalizes to a coefficient-bidiagonal
operator with `alpha(k)=(k+1)^2` and `beta(k)=n+1-k`. -/
theorem secondDerivativeBidiagonalForm_a166960 (n : ℕ) (p : ℝ[X]) :
    secondDerivativeBidiagonalForm 1 (1 + (n : ℝ)) 3 (-1) 1 0 p =
      bidiagonalOperator a166960Alpha (a166960Beta n) p := by
  refine secondDerivativeBidiagonalForm_eq_bidiagonalOperator_of_coeff_eq p ?_ ?_
  · intro k
    simp [a166960Alpha, secondDerivativeQuadraticCoeff]
    ring
  · intro k
    simp [a166960Beta, secondDerivativeQuadraticCoeff]
    ring

/-- The coefficient multiplier for the A166961 recurrence. -/
def a166961Alpha (k : ℕ) : ℝ :=
  ((k : ℝ) + 1) * (2 * (k : ℝ) + 1)

/-- The shifted coefficient multiplier for the A166961 recurrence. -/
def a166961Beta (n k : ℕ) : ℝ :=
  2 * (n : ℝ) + 1 - 2 * (k : ℝ)

/-- The A166961 differential recurrence normalizes to a coefficient-bidiagonal
operator with `alpha(k)=(k+1)(2k+1)` and `beta(k)=2n+1-2k`. -/
theorem secondDerivativeBidiagonalForm_a166961 (n : ℕ) (p : ℝ[X]) :
    secondDerivativeBidiagonalForm 1 (1 + 2 * (n : ℝ)) 5 (-2) 2 0 p =
      bidiagonalOperator a166961Alpha (a166961Beta n) p := by
  refine secondDerivativeBidiagonalForm_eq_bidiagonalOperator_of_coeff_eq p ?_ ?_
  · intro k
    simp [a166961Alpha, secondDerivativeQuadraticCoeff]
    ring
  · intro k
    simp [a166961Beta, secondDerivativeQuadraticCoeff]
    ring

/-- The coefficient multiplier for the A166962 recurrence. -/
def a166962Alpha (k : ℕ) : ℝ :=
  ((k : ℝ) + 1) * (3 * (k : ℝ) + 1)

/-- The shifted coefficient multiplier for the A166962 recurrence. -/
def a166962Beta (n k : ℕ) : ℝ :=
  3 * (n : ℝ) - 5 - 3 * (k : ℝ)

/-- The A166962 differential recurrence normalizes to a coefficient-bidiagonal
operator with `alpha(k)=(k+1)(3k+1)` and `beta(k)=3n-5-3k`. -/
theorem secondDerivativeBidiagonalForm_a166962 (n : ℕ) (p : ℝ[X]) :
    secondDerivativeBidiagonalForm 1 (-5 + 3 * (n : ℝ)) 7 (-3) 3 0 p =
      bidiagonalOperator a166962Alpha (a166962Beta n) p := by
  refine secondDerivativeBidiagonalForm_eq_bidiagonalOperator_of_coeff_eq p ?_ ?_
  · intro k
    simp [a166962Alpha, secondDerivativeQuadraticCoeff]
    ring
  · intro k
    simp [a166962Beta, secondDerivativeQuadraticCoeff]
    ring

/-- The coefficient multiplier for the A166972 recurrence. -/
def a166972Alpha (k : ℕ) : ℝ :=
  ((k : ℝ) + 1) * (3 * (k : ℝ) + 1)

/-- The shifted coefficient multiplier for the A166972 recurrence. -/
def a166972Beta (n k : ℕ) : ℝ :=
  (n : ℝ) - 1 - (k : ℝ)

/-- The A166972 differential recurrence normalizes to a coefficient-bidiagonal
operator with `alpha(k)=(k+1)(3k+1)` and `beta(k)=n-1-k`. -/
theorem secondDerivativeBidiagonalForm_a166972 (n : ℕ) (p : ℝ[X]) :
    secondDerivativeBidiagonalForm 1 (-1 + (n : ℝ)) 7 (-1) 3 0 p =
      bidiagonalOperator a166972Alpha (a166972Beta n) p := by
  refine secondDerivativeBidiagonalForm_eq_bidiagonalOperator_of_coeff_eq p ?_ ?_
  · intro k
    simp [a166972Alpha, secondDerivativeQuadraticCoeff]
    ring
  · intro k
    simp [a166972Beta, secondDerivativeQuadraticCoeff]
    ring

/-- The coefficient multiplier for the A191935 recurrence. -/
def a191935Alpha (_k : ℕ) : ℝ :=
  1

/-- The shifted coefficient multiplier for the A191935 recurrence. -/
def a191935Beta (n k : ℕ) : ℝ :=
  ((n : ℝ) + 1 - (k : ℝ)) * ((n : ℝ) + 2 - (k : ℝ))

/-- The A191935 differential recurrence normalizes to a coefficient-bidiagonal
operator with `alpha(k)=1` and `beta(k)=(n+1-k)(n+2-k)`. -/
theorem secondDerivativeBidiagonalForm_a191935 (n : ℕ) (p : ℝ[X]) :
    secondDerivativeBidiagonalForm
        1 (2 + 3 * (n : ℝ) + (n : ℝ) ^ 2)
        0 (-2 - 2 * (n : ℝ)) 0 1 p =
      bidiagonalOperator a191935Alpha (a191935Beta n) p := by
  refine secondDerivativeBidiagonalForm_eq_bidiagonalOperator_of_coeff_eq p ?_ ?_
  · intro k
    simp [a191935Alpha, secondDerivativeQuadraticCoeff]
  · intro k
    simp [a191935Beta, secondDerivativeQuadraticCoeff]
    ring

/-- The coefficient multiplier for the A371081 recurrence. -/
def a371081Alpha (n k : ℕ) : ℝ :=
  ((n : ℝ) + (k : ℝ) + 2) ^ 2

/-- The shifted coefficient multiplier for the A371081 recurrence. -/
def a371081Beta (_k : ℕ) : ℝ :=
  1

/-- The A371081 differential recurrence normalizes to a coefficient-bidiagonal
operator with `alpha(k)=(n+k+2)^2` and `beta(k)=1`. -/
theorem secondDerivativeBidiagonalForm_a371081 (n : ℕ) (p : ℝ[X]) :
    secondDerivativeBidiagonalForm
        (((n : ℝ) + 2) ^ 2) 1 (5 + 2 * (n : ℝ)) 0 1 0 p =
      bidiagonalOperator (a371081Alpha n) a371081Beta p := by
  refine secondDerivativeBidiagonalForm_eq_bidiagonalOperator_of_coeff_eq p ?_ ?_
  · intro k
    simp [a371081Alpha, secondDerivativeQuadraticCoeff]
    ring
  · intro k
    simp [a371081Beta, secondDerivativeQuadraticCoeff]

/-- The coefficient multiplier for the A371259 recurrence. -/
def a371259Alpha (n k : ℕ) : ℝ :=
  ((n : ℝ) + (k : ℝ) + 4) ^ 2

/-- The shifted coefficient multiplier for the A371259 recurrence. -/
def a371259Beta (_k : ℕ) : ℝ :=
  1

/-- The A371259 differential recurrence normalizes to a coefficient-bidiagonal
operator with `alpha(k)=(n+k+4)^2` and `beta(k)=1`. -/
theorem secondDerivativeBidiagonalForm_a371259 (n : ℕ) (p : ℝ[X]) :
    secondDerivativeBidiagonalForm
        (((n : ℝ) + 4) ^ 2) 1 (9 + 2 * (n : ℝ)) 0 1 0 p =
      bidiagonalOperator (a371259Alpha n) a371259Beta p := by
  refine secondDerivativeBidiagonalForm_eq_bidiagonalOperator_of_coeff_eq p ?_ ?_
  · intro k
    simp [a371259Alpha, secondDerivativeQuadraticCoeff]
    ring
  · intro k
    simp [a371259Beta, secondDerivativeQuadraticCoeff]

/-- The coefficient multiplier for the A390433 recurrence. -/
def a390433Alpha (n k : ℕ) : ℝ :=
  ((n : ℝ) + (k : ℝ) - 2) ^ 2

/-- The shifted coefficient multiplier for the A390433 recurrence. -/
def a390433Beta (_k : ℕ) : ℝ :=
  1

/-- The A390433 differential recurrence normalizes to a coefficient-bidiagonal
operator with `alpha(k)=(n+k-2)^2` and `beta(k)=1`. -/
theorem secondDerivativeBidiagonalForm_a390433 (n : ℕ) (p : ℝ[X]) :
    secondDerivativeBidiagonalForm
        (((n : ℝ) - 2) ^ 2) 1 (-3 + 2 * (n : ℝ)) 0 1 0 p =
      bidiagonalOperator (a390433Alpha n) a390433Beta p := by
  refine secondDerivativeBidiagonalForm_eq_bidiagonalOperator_of_coeff_eq p ?_ ?_
  · intro k
    simp [a390433Alpha, secondDerivativeQuadraticCoeff]
    ring
  · intro k
    simp [a390433Beta, secondDerivativeQuadraticCoeff]

example
    {alpha beta : ℕ → ℝ} {d : ℕ}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (hcert : BidiagonalJensenPencilCertificate alpha beta d) :
    BidiagonalPFPreserver alpha beta d :=
  bidiagonalPFPreserver_of_jensenPencil hbackend hcert

example {p : ℝ[X]}
    (hnn : HasNonnegCoeffs p)
    (hdeg : p.natDegree ≤ 3)
    (hdisc : 0 ≤ cubicDiscr p) :
    IsPFPolynomial p :=
  isPFPolynomial_of_cubicPFDiscriminantCertificate ⟨hnn, hdeg, hdisc⟩

example
    {alpha beta : ℕ → ℝ} {d m : ℕ}
    {A B : ℝ[X]} {S : ℝ → ℝ[X]}
    (halpha : jensenPolynomial d alpha = ((X + 1 : ℝ[X]) ^ m) * A)
    (hbeta : X * jensenPolynomial d beta = ((X + 1 : ℝ[X]) ^ m) * B)
    (hpencil : ∀ lam : ℝ, 0 ≤ lam →
      bidiagonalJensenPencil alpha beta d lam =
        ((X + 1 : ℝ[X]) ^ m) * S lam)
    (hA : CubicPFDiscriminantCertificate A)
    (hB : CubicPFDiscriminantCertificate B)
    (hS : ∀ lam : ℝ, 0 ≤ lam → CubicPFDiscriminantCertificate (S lam)) :
    BidiagonalJensenPencilCertificate alpha beta d := by
  rr_pf_bidiagonal_certificate using
    alpha_factor := halpha,
    beta_factor := hbeta,
    pencil_factor := hpencil,
    alpha_cubic := hA,
    beta_cubic := hB,
    pencil_cubic := hS

example
    {alpha beta : ℕ → ℝ} {d m : ℕ}
    {A B : ℝ[X]} {S : ℝ → ℝ[X]}
    (halpha : jensenPolynomial d alpha = ((X + 1 : ℝ[X]) ^ m) * A)
    (hbeta : X * jensenPolynomial d beta = ((X + 1 : ℝ[X]) ^ m) * B)
    (hpencil : ∀ lam : ℝ, 0 ≤ lam →
      bidiagonalJensenPencil alpha beta d lam =
        ((X + 1 : ℝ[X]) ^ m) * S lam)
    (hA : CubicPFDiscriminantCertificate A)
    (hB : CubicPFDiscriminantCertificate B)
    (hS : ∀ lam : ℝ, 0 ≤ lam → CubicPFDiscriminantCertificate (S lam)) :
    BidiagonalCubicResidualCertificate alpha beta d := by
  rr_pf_bidiagonal_cubic_certificate using
    alpha_factor := halpha,
    beta_factor := hbeta,
    pencil_factor := hpencil,
    alpha_cubic := hA,
    beta_cubic := hB,
    pencil_cubic := hS

example
    {alpha beta : ℕ → ℝ} {d : ℕ} {p : ℝ[X]}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (hcert : BidiagonalJensenPencilCertificate alpha beta d)
    (hp : IsPFPolynomial p)
    (hdeg : p.natDegree ≤ d) :
    IsPFPolynomial (bidiagonalOperator alpha beta p) :=
  isPFPolynomial_bidiagonalOperator_of_jensenPencil hbackend hcert hp hdeg

example
    {alpha beta : ℕ → ℝ} {d : ℕ}
    (hcert : BidiagonalJensenPencilCertificate alpha beta d)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    IsPFPolynomial (bidiagonalJensenPencil alpha beta d lam) :=
  hcert.2.2 lam hlam

example
    {alpha beta : ℕ → ℝ} {d : ℕ}
    (hcert : BidiagonalCubicResidualCertificate alpha beta d) :
    BidiagonalJensenPencilCertificate alpha beta d :=
  hcert.toJensenPencilCertificate

example
    {alpha beta : ℕ → ℝ} {d : ℕ}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (hcert : BidiagonalCubicResidualCertificate alpha beta d) :
    BidiagonalPFPreserver alpha beta d :=
  hcert.toPFPreserver hbackend

example
    {alpha beta : ℕ → ℝ} {d : ℕ} {p : ℝ[X]}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (hcert : BidiagonalCubicResidualCertificate alpha beta d)
    (hp : IsPFPolynomial p)
    (hdeg : p.natDegree ≤ d) :
    IsPFPolynomial (bidiagonalOperator alpha beta p) :=
  isPFPolynomial_bidiagonalOperator_of_cubicResidualCertificate hbackend hcert hp hdeg

example
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat,
      BidiagonalJensenPencilCertificate (alpha n) (beta n) (d n))
    (hrec : ∀ n : Nat,
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) := by
  rr_pf_bidiagonal_sequence using
    jensen_backend := hbackend,
    certificate := hcert,
    base := hbase,
    degree := hdeg,
    recurrence := hrec

example
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat,
      BidiagonalCubicResidualCertificate (alpha n) (beta n) (d n))
    (hrec : ∀ n : Nat,
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) := by
  rr_pf_bidiagonal_sequence using
    jensen_backend := hbackend,
    cubic_certificate := hcert,
    base := hbase,
    degree := hdeg,
    recurrence := hrec

example
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ}
    {d m : Nat → ℕ} {A B : Nat → ℝ[X]} {S : Nat → ℝ → ℝ[X]}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (halpha : ∀ n : Nat,
      jensenPolynomial (d n) (alpha n) = ((X + 1 : ℝ[X]) ^ m n) * A n)
    (hbeta : ∀ n : Nat,
      X * jensenPolynomial (d n) (beta n) =
        ((X + 1 : ℝ[X]) ^ m n) * B n)
    (hpencil : ∀ n : Nat, ∀ lam : ℝ, 0 ≤ lam →
      bidiagonalJensenPencil (alpha n) (beta n) (d n) lam =
        ((X + 1 : ℝ[X]) ^ m n) * S n lam)
    (hA : ∀ n : Nat, CubicPFDiscriminantCertificate (A n))
    (hB : ∀ n : Nat, CubicPFDiscriminantCertificate (B n))
    (hS : ∀ n : Nat, ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate (S n lam))
    (hrec : ∀ n : Nat,
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) := by
  rr_pf_bidiagonal_sequence_cubic using
    jensen_backend := hbackend,
    base := hbase,
    degree := hdeg,
    alpha_factor := halpha,
    beta_factor := hbeta,
    pencil_factor := hpencil,
    alpha_cubic := hA,
    beta_cubic := hB,
    pencil_cubic := hS,
    recurrence := hrec

example
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ}
    {d m : Nat → ℕ} {A B : Nat → ℝ[X]} {S : Nat → ℝ → ℝ[X]}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (halpha : ∀ n : Nat,
      jensenPolynomial (d n) (alpha n) = ((X + 1 : ℝ[X]) ^ m n) * A n)
    (hbeta : ∀ n : Nat,
      X * jensenPolynomial (d n) (beta n) =
        ((X + 1 : ℝ[X]) ^ m n) * B n)
    (hpencil : ∀ n : Nat, ∀ lam : ℝ, 0 ≤ lam →
      bidiagonalJensenPencil (alpha n) (beta n) (d n) lam =
        ((X + 1 : ℝ[X]) ^ m n) * S n lam)
    (hA : ∀ n : Nat, CubicPFDiscriminantCertificate (A n))
    (hB : ∀ n : Nat, CubicPFDiscriminantCertificate (B n))
    (hS : ∀ n : Nat, ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate (S n lam))
    (hne : ∀ n : Nat, P n ≠ 0)
    (hrec : ∀ n : Nat,
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_pf_bidiagonal_sequence_cubic using
    jensen_backend := hbackend,
    base := hbase,
    degree := hdeg,
    alpha_factor := halpha,
    beta_factor := hbeta,
    pencil_factor := hpencil,
    alpha_cubic := hA,
    beta_cubic := hB,
    pencil_cubic := hS,
    recurrence := hrec,
    nonzero := hne

example
    {P : Nat → ℝ[X]} {a0 a1 b1 b2 c2 c3 : Nat → ℝ}
    {d m : Nat → ℕ} {A B : Nat → ℝ[X]} {S : Nat → ℝ → ℝ[X]}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (halpha : ∀ n : Nat,
      jensenPolynomial (d n)
          (fun k => secondDerivativeQuadraticCoeff (a0 n) (b1 n) (c2 n) k) =
        ((X + 1 : ℝ[X]) ^ m n) * A n)
    (hbeta : ∀ n : Nat,
      X * jensenPolynomial (d n)
          (fun k => secondDerivativeQuadraticCoeff (a1 n) (b2 n) (c3 n) k) =
        ((X + 1 : ℝ[X]) ^ m n) * B n)
    (hpencil : ∀ n : Nat, ∀ lam : ℝ, 0 ≤ lam →
      bidiagonalJensenPencil
          (fun k => secondDerivativeQuadraticCoeff (a0 n) (b1 n) (c2 n) k)
          (fun k => secondDerivativeQuadraticCoeff (a1 n) (b2 n) (c3 n) k)
          (d n) lam =
        ((X + 1 : ℝ[X]) ^ m n) * S n lam)
    (hA : ∀ n : Nat, CubicPFDiscriminantCertificate (A n))
    (hB : ∀ n : Nat, CubicPFDiscriminantCertificate (B n))
    (hS : ∀ n : Nat, ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate (S n lam))
    (hrec : ∀ n : Nat,
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) := by
  rr_pf_second_derivative_bidiagonal_sequence_cubic using
    jensen_backend := hbackend,
    base := hbase,
    degree := hdeg,
    alpha_factor := halpha,
    beta_factor := hbeta,
    pencil_factor := hpencil,
    alpha_cubic := hA,
    beta_cubic := hB,
    pencil_cubic := hS,
    recurrence := hrec

example
    {P : Nat → ℝ[X]} {a0 a1 b1 b2 c2 c3 : Nat → ℝ}
    {d m : Nat → ℕ} {A B : Nat → ℝ[X]} {S : Nat → ℝ → ℝ[X]}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (halpha : ∀ n : Nat,
      jensenPolynomial (d n)
          (fun k => secondDerivativeQuadraticCoeff (a0 n) (b1 n) (c2 n) k) =
        ((X + 1 : ℝ[X]) ^ m n) * A n)
    (hbeta : ∀ n : Nat,
      X * jensenPolynomial (d n)
          (fun k => secondDerivativeQuadraticCoeff (a1 n) (b2 n) (c3 n) k) =
        ((X + 1 : ℝ[X]) ^ m n) * B n)
    (hpencil : ∀ n : Nat, ∀ lam : ℝ, 0 ≤ lam →
      bidiagonalJensenPencil
          (fun k => secondDerivativeQuadraticCoeff (a0 n) (b1 n) (c2 n) k)
          (fun k => secondDerivativeQuadraticCoeff (a1 n) (b2 n) (c3 n) k)
          (d n) lam =
        ((X + 1 : ℝ[X]) ^ m n) * S n lam)
    (hA : ∀ n : Nat, CubicPFDiscriminantCertificate (A n))
    (hB : ∀ n : Nat, CubicPFDiscriminantCertificate (B n))
    (hS : ∀ n : Nat, ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate (S n lam))
    (hne : ∀ n : Nat, P n ≠ 0)
    (hrec : ∀ n : Nat,
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_pf_second_derivative_bidiagonal_sequence_cubic using
    jensen_backend := hbackend,
    base := hbase,
    degree := hdeg,
    alpha_factor := halpha,
    beta_factor := hbeta,
    pencil_factor := hpencil,
    alpha_cubic := hA,
    beta_cubic := hB,
    pencil_cubic := hS,
    recurrence := hrec,
    nonzero := hne

example
    {P : Nat → ℝ[X]} {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat,
      BidiagonalCubicResidualCertificate
        (fun k => secondDerivativeQuadraticCoeff (a0 n) (b1 n) (c2 n) k)
        (fun k => secondDerivativeQuadraticCoeff (a1 n) (b2 n) (c3 n) k)
        (d n))
    (hrec : ∀ n : Nat,
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) := by
  rr_pf_second_derivative_bidiagonal_sequence using
    jensen_backend := hbackend,
    cubic_certificate := hcert,
    base := hbase,
    degree := hdeg,
    recurrence := hrec

example
    {P : Nat → ℝ[X]} {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat,
      BidiagonalCubicResidualCertificate
        (fun k => secondDerivativeQuadraticCoeff (a0 n) (b1 n) (c2 n) k)
        (fun k => secondDerivativeQuadraticCoeff (a1 n) (b2 n) (c3 n) k)
        (d n))
    (hne : ∀ n : Nat, P n ≠ 0)
    (hrec : ∀ n : Nat,
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_pf_second_derivative_bidiagonal_sequence using
    jensen_backend := hbackend,
    cubic_certificate := hcert,
    base := hbase,
    degree := hdeg,
    recurrence := hrec,
    nonzero := hne

/-- A036969-shaped recurrence shell.

This example has the actual differential recurrence and actual residual
polynomials.  The residual cubic certificates are discharged below; the
remaining hypotheses are the symbolic Jensen factorization leaves. -/
example
    {P : Nat → ℝ[X]} {d m : Nat → ℕ}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (halpha : ∀ n : Nat,
      jensenPolynomial (d n) a036969Alpha =
        ((X + 1 : ℝ[X]) ^ m n) * a036969ResidualAlpha (d n))
    (hbeta : ∀ n : Nat,
      X * jensenPolynomial (d n) a036969Beta =
        ((X + 1 : ℝ[X]) ^ m n) * a036969ResidualBeta)
    (hpencil : ∀ n : Nat, ∀ lam : ℝ, 0 ≤ lam →
      bidiagonalJensenPencil a036969Alpha a036969Beta (d n) lam =
        ((X + 1 : ℝ[X]) ^ m n) * a036969ResidualPencil (d n) lam)
    (hrec : ∀ n : Nat,
      P (n + 1) = secondDerivativeBidiagonalForm 1 1 3 0 1 0 (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) := by
  rr_pf_second_derivative_bidiagonal_sequence_cubic using
    jensen_backend := hbackend,
    base := hbase,
    degree := hdeg,
    alpha_factor := halpha,
    beta_factor := hbeta,
    pencil_factor := hpencil,
    alpha_cubic := (fun n => a036969ResidualAlpha_cubicPFDiscriminantCertificate (d n)),
    beta_cubic := (fun _ => a036969ResidualBeta_cubicPFDiscriminantCertificate),
    pencil_cubic := (fun n _lam hlam =>
      a036969ResidualPencil_cubicPFDiscriminantCertificate (d n) hlam),
    normalizer := (fun n => secondDerivativeBidiagonalForm_a036969 (P n)),
    recurrence := hrec

example
    {P : Nat → ℝ[X]} {d m : Nat → ℕ}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (halpha : ∀ n : Nat,
      jensenPolynomial (d n) a036969Alpha =
        ((X + 1 : ℝ[X]) ^ m n) * a036969ResidualAlpha (d n))
    (hbeta : ∀ n : Nat,
      X * jensenPolynomial (d n) a036969Beta =
        ((X + 1 : ℝ[X]) ^ m n) * a036969ResidualBeta)
    (hpencil : ∀ n : Nat, ∀ lam : ℝ, 0 ≤ lam →
      bidiagonalJensenPencil a036969Alpha a036969Beta (d n) lam =
        ((X + 1 : ℝ[X]) ^ m n) * a036969ResidualPencil (d n) lam)
    (hne : ∀ n : Nat, P n ≠ 0)
    (hrec : ∀ n : Nat,
      P (n + 1) = secondDerivativeBidiagonalForm 1 1 3 0 1 0 (P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_pf_second_derivative_bidiagonal_sequence_cubic using
    jensen_backend := hbackend,
    base := hbase,
    degree := hdeg,
    alpha_factor := halpha,
    beta_factor := hbeta,
    pencil_factor := hpencil,
    alpha_cubic := (fun n => a036969ResidualAlpha_cubicPFDiscriminantCertificate (d n)),
    beta_cubic := (fun _ => a036969ResidualBeta_cubicPFDiscriminantCertificate),
    pencil_cubic := (fun n _lam hlam =>
      a036969ResidualPencil_cubicPFDiscriminantCertificate (d n) hlam),
    normalizer := (fun n => secondDerivativeBidiagonalForm_a036969 (P n)),
    recurrence := hrec,
    nonzero := hne

/-- Same A036969 shell, but with all residual/factorization hints bundled in a
single per-row certificate.  This is the intended OEIS-facing interface once
the arithmetic leaves have been generated. -/
example
    {P : Nat → ℝ[X]} {d : Nat → ℕ}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat,
      BidiagonalCubicResidualCertificate a036969Alpha a036969Beta (d n))
    (hrec : ∀ n : Nat,
      P (n + 1) = secondDerivativeBidiagonalForm 1 1 3 0 1 0 (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) := by
  rr_pf_second_derivative_bidiagonal_sequence using
    jensen_backend := hbackend,
    cubic_certificate := hcert,
    base := hbase,
    degree := hdeg,
    normalizer := (fun n => secondDerivativeBidiagonalForm_a036969 (P n)),
    recurrence := hrec

example
    {P : Nat → ℝ[X]} {d : Nat → ℕ}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat,
      BidiagonalCubicResidualCertificate a036969Alpha a036969Beta (d n))
    (hne : ∀ n : Nat, P n ≠ 0)
    (hrec : ∀ n : Nat,
      P (n + 1) = secondDerivativeBidiagonalForm 1 1 3 0 1 0 (P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_pf_second_derivative_bidiagonal_sequence using
    jensen_backend := hbackend,
    cubic_certificate := hcert,
    base := hbase,
    degree := hdeg,
    normalizer := (fun n => secondDerivativeBidiagonalForm_a036969 (P n)),
    recurrence := hrec,
    nonzero := hne

end TacticExamples
end RealRooted
