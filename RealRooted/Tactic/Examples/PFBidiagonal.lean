import RealRooted.Tactic.PFBidiagonal

open Polynomial

noncomputable section

namespace RealRooted
namespace TacticExamples

example (a b c : ℝ) {d : ℕ} (hd : 2 ≤ d) :
    quadraticJensen a b c d =
      (X + 1) ^ (d - 2) * quadraticJensenResidual a b c d := by
  exact quadraticJensen_eq_factor_residual a b c hd

example {d : ℕ} (hd : 2 ≤ d) :
    bidiagonalJensenPencil
        (quadraticJensenWeight 1 2 1) (quadraticJensenWeight 0 0 1) d 1 =
      (X + 1) ^ (d - 2) * quadraticBidiagonalResidual 1 2 1 0 0 1 d := by
  exact quadraticBidiagonalJensenPencil_eq_factor_residual_one 1 2 1 0 0 1 hd

example {alpha beta alpha' beta' : ℕ → ℝ} {d : ℕ}
    (hpres : BidiagonalPFPreserver alpha' beta' d)
    (halpha : ∀ k, k ≤ d → alpha k = alpha' k)
    (hbeta : ∀ k, k ≤ d → beta k = beta' k) :
    BidiagonalPFPreserver alpha beta d := by
  exact hpres.of_eq_on_degree halpha hbeta

example
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    {d : ℕ} (hd : 2 ≤ d)
    (hA : CubicPFDiscriminantCertificate (quadraticJensenResidual 1 2 1 d))
    (hB : CubicPFDiscriminantCertificate (X * quadraticJensenResidual 0 0 1 d))
    (hS : ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate
        (quadraticBidiagonalPencilResidual 1 2 1 0 0 1 lam d)) :
    BidiagonalPFPreserver
      (quadraticJensenWeight 1 2 1) (quadraticJensenWeight 0 0 1) d := by
  exact quadraticBidiagonalPFPreserver_of_cubicResidualCertificate
    hbackend 1 2 1 0 0 1 hd hA hB hS

example {P : Nat → ℝ[X]}
    (hpf : ∀ n : Nat, IsPFPolynomial (P n)) :
    ∀ n : Nat, HasNonnegCoeffs (P n) := by
  rr_exact_pf_sequence hpf

example {P : Nat → ℝ[X]}
    (hpf : ∀ n : Nat, IsPFPolynomial (P n))
    (hne : ∀ n : Nat, P n ≠ 0) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_exact_pf_sequence hpf, nonzero := hne

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
    (_hbase : IsPFPolynomial (P 0))
    (_hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (_hpres : ∀ n : Nat, BidiagonalPFPreserver (alpha n) (beta n) (d n))
    (hne : ∀ n : Nat, P n ≠ 0)
    (_hrec : ∀ n : Nat,
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n)) :
    ∀ n : Nat, P n ≠ 0 := by
  rr_pf_bidiagonal_sequence using
    preserver := _hpres,
    base := _hbase,
    degree := _hdeg,
    recurrence := _hrec,
    nonzero := hne

example
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hpres : ∀ n : Nat, BidiagonalPFPreserver (alpha n) (beta n) (d n))
    (_hne : ∀ n : Nat, P n ≠ 0)
    (hrec : ∀ n : Nat,
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n)) :
    ∀ n : Nat, (P n).Splits := by
  rr_pf_bidiagonal_sequence using
    preserver := hpres,
    base := hbase,
    degree := hdeg,
    recurrence := hrec,
    nonzero := _hne

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

/-- The Euler operator `X d/dX` acts diagonally with multiplier `k`. -/
private theorem eulerOperator_eq_diagonalOperator (p : ℝ[X]) :
    X * derivative p = diagonalOperator (fun k => (k : ℝ)) p := by
  ext k
  cases k with
  | zero => simp [coeff_diagonalOperator]
  | succ k =>
      simp [Polynomial.coeff_X_mul, Polynomial.coeff_derivative, coeff_diagonalOperator]
      ring

/-- The multiplier `(k + 1)^2` is `(X d/dX + 1)^2` on coefficients. -/
private theorem diagonalOperator_succ_sq_eq_euler (p : ℝ[X]) :
    diagonalOperator (fun k => ((k : ℝ) + 1) ^ 2) p =
      X * derivative (X * derivative p) + C 2 * (X * derivative p) + p := by
  rw [eulerOperator_eq_diagonalOperator p]
  rw [eulerOperator_eq_diagonalOperator (diagonalOperator (fun k => (k : ℝ)) p)]
  ext k
  simp [coeff_diagonalOperator]
  ring

/-- The multiplier `(k + 1)(k + 2)` is `(X d/dX + 1)(X d/dX + 2)` on
coefficients. -/
private theorem diagonalOperator_succ_mul_succ_two_eq_euler (p : ℝ[X]) :
    diagonalOperator (fun k => ((k : ℝ) + 1) * ((k : ℝ) + 2)) p =
      X * derivative (X * derivative p) + C 3 * (X * derivative p) + C 2 * p := by
  rw [eulerOperator_eq_diagonalOperator p]
  rw [eulerOperator_eq_diagonalOperator (diagonalOperator (fun k => (k : ℝ)) p)]
  ext k
  simp [coeff_diagonalOperator]
  ring

private theorem diagonalOperator_succ_mul_succ_two_half_eq (p : ℝ[X]) :
    diagonalOperator (fun k => (((k : ℝ) + 1) * ((k : ℝ) + 2)) / 2) p =
      C (1 / 2 : ℝ) *
        diagonalOperator (fun k => ((k : ℝ) + 1) * ((k : ℝ) + 2)) p := by
  ext k
  simp [coeff_diagonalOperator]
  ring

private theorem diagonalOperator_sq_eq_euler (p : ℝ[X]) :
    diagonalOperator (fun k => (k : ℝ) ^ 2) p =
      X * derivative (X * derivative p) := by
  rw [eulerOperator_eq_diagonalOperator p]
  rw [eulerOperator_eq_diagonalOperator (diagonalOperator (fun k => (k : ℝ)) p)]
  ext k
  simp [coeff_diagonalOperator]
  ring

private theorem diagonalOperator_two_mul_add_one_sq_eq_euler (p : ℝ[X]) :
    diagonalOperator (fun k => (2 * (k : ℝ) + 1) ^ 2) p =
      C (4 : ℝ) * (X * derivative (X * derivative p)) +
        C (4 : ℝ) * (X * derivative p) + p := by
  rw [eulerOperator_eq_diagonalOperator p]
  rw [eulerOperator_eq_diagonalOperator (diagonalOperator (fun k => (k : ℝ)) p)]
  ext k
  simp [coeff_diagonalOperator]
  ring

private theorem X_add_one_pow_eq_pow_sub_two_mul_sq (d : ℕ) (hd : 2 ≤ d) :
    (X + 1 : ℝ[X]) ^ d =
      (X + 1 : ℝ[X]) ^ (d - 2) * (X + 1) ^ 2 := by
  simpa [Nat.sub_add_cancel hd] using
    (pow_add (X + 1 : ℝ[X]) (d - 2) 2)

private theorem natCast_sub_two_add_one_eq_sub_one (d : ℕ) (hd : 2 ≤ d) :
    ((d - 2 + 1 : ℕ) : ℝ[X]) = (d : ℝ[X]) - 1 := by
  have hnat : d - 2 + 1 = d - 1 := by lia
  have hd_one : 1 ≤ d := by lia
  rw [hnat]
  norm_num [Nat.cast_sub hd_one]

private theorem oneSequence_jensen_factor (d : ℕ) (hd : 2 ≤ d) :
    X * jensenPolynomial d (fun _ => (1 : ℝ)) =
      ((X + 1 : ℝ[X]) ^ (d - 2)) * a036969ResidualBeta := by
  rw [jensenPolynomial_one_sequence, a036969ResidualBeta]
  rw [X_add_one_pow_eq_pow_sub_two_mul_sq d hd]
  ring

/-- The A036969 alpha Jensen endpoint after removing the common residual
factor. -/
theorem a036969Alpha_jensen_factor (d : ℕ) (hd : 2 ≤ d) :
    jensenPolynomial d a036969Alpha =
      ((X + 1 : ℝ[X]) ^ (d - 2)) * a036969ResidualAlpha d := by
  rw [jensenPolynomial_eq_diagonalOperator_X_add_one_pow]
  change diagonalOperator (fun k => ((k : ℝ) + 1) ^ 2) ((X + 1 : ℝ[X]) ^ d) =
    ((X + 1 : ℝ[X]) ^ (d - 2)) * a036969ResidualAlpha d
  rw [diagonalOperator_succ_sq_eq_euler]
  simp only [a036969ResidualAlpha, Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_X, Polynomial.derivative_add, Polynomial.derivative_one,
    Polynomial.derivative_natCast, Polynomial.C_add, Polynomial.C_mul, Polynomial.C_pow,
    Polynomial.C_eq_natCast, Polynomial.C_1, one_mul, mul_one, add_zero]
  have hd1 : d - 1 = d - 2 + 1 := by lia
  have hd11 : d - 1 - 1 = d - 2 := by lia
  have hcast_poly := natCast_sub_two_add_one_eq_sub_one d hd
  have hC2 : (C (2 : ℝ) : ℝ[X]) = (2 : ℝ[X]) :=
    Polynomial.C_eq_natCast (R := ℝ) 2
  have hC3 : (C (3 : ℝ) : ℝ[X]) = (3 : ℝ[X]) :=
    Polynomial.C_eq_natCast (R := ℝ) 3
  rw [hd11, hd1, X_add_one_pow_eq_pow_sub_two_mul_sq d hd]
  rw [pow_add]
  rw [hcast_poly, hC2, hC3]
  ring

/-- The A036969 beta Jensen endpoint after removing the common residual
factor. -/
theorem a036969Beta_jensen_factor (d : ℕ) (hd : 2 ≤ d) :
    X * jensenPolynomial d a036969Beta =
      ((X + 1 : ℝ[X]) ^ (d - 2)) * a036969ResidualBeta := by
  change X * jensenPolynomial d (fun _ => (1 : ℝ)) =
    ((X + 1 : ℝ[X]) ^ (d - 2)) * a036969ResidualBeta
  exact oneSequence_jensen_factor d hd

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

private theorem a036969ResidualBeta_hasNonnegCoeffs :
    HasNonnegCoeffs a036969ResidualBeta :=
  a036969ResidualBeta_cubicPFDiscriminantCertificate.1

private theorem a036969ResidualBeta_coeff_zero :
    a036969ResidualBeta.coeff 0 = 0 := by
  rw [a036969ResidualBeta]
  ring_nf
  rr_coeff

private theorem a036969ResidualBeta_coeff_one :
    a036969ResidualBeta.coeff 1 = 1 := by
  rw [a036969ResidualBeta]
  ring_nf
  rr_coeff

private theorem a036969ResidualBeta_coeff_two :
    a036969ResidualBeta.coeff 2 = 2 := by
  rw [a036969ResidualBeta]
  ring_nf
  rr_coeff

private theorem a036969ResidualBeta_coeff_three :
    a036969ResidualBeta.coeff 3 = 1 := by
  rw [a036969ResidualBeta]
  ring_nf
  rr_coeff

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
  have hterm : HasNonnegCoeffs (C lam * a036969ResidualBeta) :=
    nonnegCoeffs_C_mul hlam a036969ResidualBeta_hasNonnegCoeffs
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

/-- Bundled cubic-residual certificate for the A036969 coefficient-bidiagonal
operator. -/
def a036969_bidiagonalCubicResidualCertificate (d : ℕ) (hd : 2 ≤ d) :
    BidiagonalCubicResidualCertificate a036969Alpha a036969Beta d := by
  rr_pf_bidiagonal_cubic_certificate using
    alpha_factor := a036969Alpha_jensen_factor d hd,
    beta_factor := a036969Beta_jensen_factor d hd,
    alpha_cubic := a036969ResidualAlpha_cubicPFDiscriminantCertificate d,
    beta_cubic := a036969ResidualBeta_cubicPFDiscriminantCertificate,
    pencil_cubic := by
      intro lam hlam
      simpa [a036969ResidualPencil] using
        a036969ResidualPencil_cubicPFDiscriminantCertificate d hlam

/-- The A036969 differential recurrence normalizes to a coefficient-bidiagonal
operator with `alpha(k)=(k+1)^2` and `beta(k)=1`. -/
theorem secondDerivativeBidiagonalForm_a036969 (p : ℝ[X]) :
    secondDerivativeBidiagonalForm 1 1 3 0 1 0 p =
      bidiagonalOperator a036969Alpha a036969Beta p := by
  rr_second_derivative_bidiagonal_normalizer [a036969Alpha, a036969Beta]

/-- The coefficient multiplier for the A071951 recurrence. -/
def a071951Alpha (k : ℕ) : ℝ :=
  ((k : ℝ) + 1) * ((k : ℝ) + 2)

/-- The shifted coefficient multiplier for the A071951 recurrence. -/
def a071951Beta (_k : ℕ) : ℝ :=
  1

/-- The residual after removing the common `(1 + X)^(d-2)` Jensen factor for
the A071951 `alpha` endpoint. -/
def a071951ResidualAlpha (d : ℕ) : ℝ[X] :=
  C (2 : ℝ) +
    C (4 * ((d : ℝ) + 1)) * X +
    C (((d : ℝ) + 1) * ((d : ℝ) + 2)) * X ^ 2

/-- The residual pencil for the A071951 PF-bidiagonal certificate. -/
def a071951ResidualPencil (d : ℕ) (lam : ℝ) : ℝ[X] :=
  a071951ResidualAlpha d + C lam * a036969ResidualBeta

/-- The A071951 alpha Jensen endpoint after removing the common residual
factor. -/
theorem a071951Alpha_jensen_factor (d : ℕ) (hd : 2 ≤ d) :
    jensenPolynomial d a071951Alpha =
      ((X + 1 : ℝ[X]) ^ (d - 2)) * a071951ResidualAlpha d := by
  rw [jensenPolynomial_eq_diagonalOperator_X_add_one_pow]
  change diagonalOperator (fun k => ((k : ℝ) + 1) * ((k : ℝ) + 2))
      ((X + 1 : ℝ[X]) ^ d) =
    ((X + 1 : ℝ[X]) ^ (d - 2)) * a071951ResidualAlpha d
  rw [diagonalOperator_succ_mul_succ_two_eq_euler]
  simp only [a071951ResidualAlpha, Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_X, Polynomial.derivative_add, Polynomial.derivative_one,
    Polynomial.derivative_natCast, Polynomial.C_add, Polynomial.C_mul,
    Polynomial.C_eq_natCast, Polynomial.C_1, one_mul, mul_one, add_zero]
  have hd1 : d - 1 = d - 2 + 1 := by lia
  have hd11 : d - 1 - 1 = d - 2 := by lia
  have hcast_poly := natCast_sub_two_add_one_eq_sub_one d hd
  have hC2 : (C (2 : ℝ) : ℝ[X]) = (2 : ℝ[X]) :=
    Polynomial.C_eq_natCast (R := ℝ) 2
  have hC3 : (C (3 : ℝ) : ℝ[X]) = (3 : ℝ[X]) :=
    Polynomial.C_eq_natCast (R := ℝ) 3
  have hC4 : (C (4 : ℝ) : ℝ[X]) = (4 : ℝ[X]) :=
    Polynomial.C_eq_natCast (R := ℝ) 4
  rw [hd11, hd1, X_add_one_pow_eq_pow_sub_two_mul_sq d hd]
  rw [pow_add]
  rw [hcast_poly, hC2, hC3, hC4]
  ring

/-- The A071951 beta Jensen endpoint after removing the common residual
factor. -/
theorem a071951Beta_jensen_factor (d : ℕ) (hd : 2 ≤ d) :
    X * jensenPolynomial d a071951Beta =
      ((X + 1 : ℝ[X]) ^ (d - 2)) * a036969ResidualBeta := by
  change X * jensenPolynomial d (fun _ => (1 : ℝ)) =
    ((X + 1 : ℝ[X]) ^ (d - 2)) * a036969ResidualBeta
  exact oneSequence_jensen_factor d hd

/-- The A071951 alpha residual has nonnegative coefficients. -/
theorem a071951ResidualAlpha_hasNonnegCoeffs (d : ℕ) :
    HasNonnegCoeffs (a071951ResidualAlpha d) := by
  have h0 : HasNonnegCoeffs (C (2 : ℝ)) :=
    hasNonnegCoeffs_C (by positivity)
  have h1 : HasNonnegCoeffs (C (4 * ((d : ℝ) + 1)) * X) :=
    nonnegCoeffs_C_mul (by positivity) hasNonnegCoeffs_X
  have h2 : HasNonnegCoeffs (C (((d : ℝ) + 1) * ((d : ℝ) + 2)) * X ^ 2) :=
    nonnegCoeffs_C_mul (by positivity) (hasNonnegCoeffs_X.pow 2)
  simpa [a071951ResidualAlpha, add_assoc] using h0.add (h1.add h2)

/-- The A071951 alpha residual is at most quadratic. -/
theorem natDegree_a071951ResidualAlpha_le (d : ℕ) :
    (a071951ResidualAlpha d).natDegree ≤ 3 := by
  unfold a071951ResidualAlpha
  compute_degree
  norm_num

/-- The A071951 alpha residual has nonnegative cubic discriminant. -/
theorem cubicDiscr_a071951ResidualAlpha_nonneg (d : ℕ) :
    0 ≤ cubicDiscr (a071951ResidualAlpha d) := by
  have hpoly :
      a071951ResidualAlpha d =
        C (0 : ℝ) * X ^ 3 +
          C (((d : ℝ) + 1) * ((d : ℝ) + 2)) * X ^ 2 +
            C (4 * ((d : ℝ) + 1)) * X + C (2 : ℝ) := by
    simp [a071951ResidualAlpha]
    ring
  have hdisc :
      cubicDiscr (a071951ResidualAlpha d) =
        (((d : ℝ) + 1) * ((d : ℝ) + 2)) ^ 2 *
          (8 * (d : ℝ) * ((d : ℝ) + 1)) := by
    rw [hpoly, cubicDiscr_of_coeffs]
    ring
  rw [hdisc]
  positivity

/-- Cubic-discriminant certificate for the A071951 alpha residual. -/
theorem a071951ResidualAlpha_cubicPFDiscriminantCertificate (d : ℕ) :
    CubicPFDiscriminantCertificate (a071951ResidualAlpha d) :=
  ⟨a071951ResidualAlpha_hasNonnegCoeffs d,
    natDegree_a071951ResidualAlpha_le d,
    cubicDiscr_a071951ResidualAlpha_nonneg d⟩

private theorem a071951ResidualAlpha_coeff_three (d : ℕ) :
    (a071951ResidualAlpha d).coeff 3 = 0 := by
  rw [a071951ResidualAlpha]
  rw [Polynomial.coeff_add, Polynomial.coeff_add]
  rw [Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul_X_pow]
  simp

private theorem a071951ResidualAlpha_coeff_two (d : ℕ) :
    (a071951ResidualAlpha d).coeff 2 =
      ((d : ℝ) + 1) * ((d : ℝ) + 2) := by
  rw [a071951ResidualAlpha]
  rw [Polynomial.coeff_add, Polynomial.coeff_add]
  rw [Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul_X_pow]
  simp

private theorem a071951ResidualAlpha_coeff_one (d : ℕ) :
    (a071951ResidualAlpha d).coeff 1 = 4 * ((d : ℝ) + 1) := by
  rw [a071951ResidualAlpha]
  rw [Polynomial.coeff_add, Polynomial.coeff_add]
  rw [Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul_X_pow]
  simp

private theorem a071951ResidualAlpha_coeff_zero (d : ℕ) :
    (a071951ResidualAlpha d).coeff 0 = 2 := by
  rw [a071951ResidualAlpha]
  rw [Polynomial.coeff_add, Polynomial.coeff_add]
  rw [Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul_X_pow]
  simp

private theorem a071951ResidualPencil_coeff_three (d : ℕ) (lam : ℝ) :
    (a071951ResidualPencil d lam).coeff 3 = lam := by
  rw [a071951ResidualPencil, Polynomial.coeff_add, a071951ResidualAlpha_coeff_three]
  have hterm : (C lam * a036969ResidualBeta).coeff 3 = lam := by
    rw [Polynomial.coeff_C_mul, a036969ResidualBeta_coeff_three]
    ring
  rw [hterm]
  ring

private theorem a071951ResidualPencil_coeff_two (d : ℕ) (lam : ℝ) :
    (a071951ResidualPencil d lam).coeff 2 =
      ((d : ℝ) + 1) * ((d : ℝ) + 2) + 2 * lam := by
  rw [a071951ResidualPencil, Polynomial.coeff_add, a071951ResidualAlpha_coeff_two]
  have hterm : (C lam * a036969ResidualBeta).coeff 2 = 2 * lam := by
    rw [Polynomial.coeff_C_mul, a036969ResidualBeta_coeff_two]
    ring
  rw [hterm]

private theorem a071951ResidualPencil_coeff_one (d : ℕ) (lam : ℝ) :
    (a071951ResidualPencil d lam).coeff 1 = 4 * ((d : ℝ) + 1) + lam := by
  rw [a071951ResidualPencil, Polynomial.coeff_add, a071951ResidualAlpha_coeff_one]
  have hterm : (C lam * a036969ResidualBeta).coeff 1 = lam := by
    rw [Polynomial.coeff_C_mul, a036969ResidualBeta_coeff_one]
    ring
  rw [hterm]

private theorem a071951ResidualPencil_coeff_zero (d : ℕ) (lam : ℝ) :
    (a071951ResidualPencil d lam).coeff 0 = 2 := by
  rw [a071951ResidualPencil, Polynomial.coeff_add, a071951ResidualAlpha_coeff_zero]
  have hterm : (C lam * a036969ResidualBeta).coeff 0 = 0 := by
    rw [Polynomial.coeff_C_mul, a036969ResidualBeta_coeff_zero]
    ring
  rw [hterm]
  ring

/-- The A071951 residual pencil has nonnegative coefficients for
nonnegative pencil parameter. -/
theorem a071951ResidualPencil_hasNonnegCoeffs
    (d : ℕ) {lam : ℝ} (hlam : 0 ≤ lam) :
    HasNonnegCoeffs (a071951ResidualPencil d lam) := by
  have hterm : HasNonnegCoeffs (C lam * a036969ResidualBeta) :=
    nonnegCoeffs_C_mul hlam a036969ResidualBeta_hasNonnegCoeffs
  simpa [a071951ResidualPencil] using
    (a071951ResidualAlpha_hasNonnegCoeffs d).add hterm

/-- The A071951 residual pencil has degree at most three. -/
theorem natDegree_a071951ResidualPencil_le (d : ℕ) (lam : ℝ) :
    (a071951ResidualPencil d lam).natDegree ≤ 3 := by
  unfold a071951ResidualPencil a071951ResidualAlpha a036969ResidualBeta
  compute_degree

/-- The A071951 residual pencil has nonnegative cubic discriminant for
nonnegative pencil parameter. -/
theorem cubicDiscr_a071951ResidualPencil_nonneg
    (d : ℕ) {lam : ℝ} (hlam : 0 ≤ lam) :
    0 ≤ cubicDiscr (a071951ResidualPencil d lam) := by
  cases d with
  | zero =>
      unfold cubicDiscr
      rw [a071951ResidualPencil_coeff_three, a071951ResidualPencil_coeff_two,
        a071951ResidualPencil_coeff_one, a071951ResidualPencil_coeff_zero]
      ring_nf
      norm_num
  | succ e =>
      have hdisc :
          cubicDiscr (a071951ResidualPencil (Nat.succ e) lam) =
            ((e : ℝ) + 1) *
              (8 * (e : ℝ) ^ 5 +
                8 * (e : ℝ) ^ 4 * lam +
                96 * (e : ℝ) ^ 4 +
                (e : ℝ) ^ 3 * lam ^ 2 +
                104 * (e : ℝ) ^ 3 * lam +
                456 * (e : ℝ) ^ 3 +
                41 * (e : ℝ) ^ 2 * lam ^ 2 +
                336 * (e : ℝ) ^ 2 * lam +
                1072 * (e : ℝ) ^ 2 +
                4 * (e : ℝ) * lam ^ 3 +
                32 * (e : ℝ) * lam ^ 2 +
                352 * (e : ℝ) * lam +
                1248 * (e : ℝ) +
                16 * lam ^ 2 + 64 * lam + 576) := by
        unfold cubicDiscr
        rw [a071951ResidualPencil_coeff_three, a071951ResidualPencil_coeff_two,
          a071951ResidualPencil_coeff_one, a071951ResidualPencil_coeff_zero]
        norm_num [Nat.cast_succ]
        ring_nf
      rw [hdisc]
      positivity

/-- Cubic-discriminant certificate for the A071951 residual pencil. -/
theorem a071951ResidualPencil_cubicPFDiscriminantCertificate
    (d : ℕ) {lam : ℝ} (hlam : 0 ≤ lam) :
    CubicPFDiscriminantCertificate (a071951ResidualPencil d lam) :=
  ⟨a071951ResidualPencil_hasNonnegCoeffs d hlam,
    natDegree_a071951ResidualPencil_le d lam,
    cubicDiscr_a071951ResidualPencil_nonneg d hlam⟩

/-- Bundled cubic-residual certificate for the A071951 coefficient-bidiagonal
operator. -/
def a071951_bidiagonalCubicResidualCertificate (d : ℕ) (hd : 2 ≤ d) :
    BidiagonalCubicResidualCertificate a071951Alpha a071951Beta d := by
  rr_pf_bidiagonal_cubic_certificate using
    alpha_factor := a071951Alpha_jensen_factor d hd,
    beta_factor := a071951Beta_jensen_factor d hd,
    alpha_cubic := a071951ResidualAlpha_cubicPFDiscriminantCertificate d,
    beta_cubic := a036969ResidualBeta_cubicPFDiscriminantCertificate,
    pencil_cubic := by
      intro lam hlam
      simpa [a071951ResidualPencil] using
        a071951ResidualPencil_cubicPFDiscriminantCertificate d hlam

/-- The A071951 differential recurrence normalizes to a coefficient-bidiagonal
operator with `alpha(k)=(k+1)(k+2)` and `beta(k)=1`. -/
theorem secondDerivativeBidiagonalForm_a071951 (p : ℝ[X]) :
    secondDerivativeBidiagonalForm 2 1 4 0 1 0 p =
      bidiagonalOperator a071951Alpha a071951Beta p := by
  rr_second_derivative_bidiagonal_normalizer [a071951Alpha, a071951Beta]

/-- The coefficient multiplier for the A080248 recurrence. -/
def a080248Alpha (k : ℕ) : ℝ :=
  (((k : ℝ) + 1) * ((k : ℝ) + 2)) / 2

/-- The shifted coefficient multiplier for the A080248 recurrence. -/
def a080248Beta (_k : ℕ) : ℝ :=
  1

/-- The residual after removing the common `(1 + X)^(d-2)` Jensen factor for
the A080248 `alpha` endpoint. -/
def a080248ResidualAlpha (d : ℕ) : ℝ[X] :=
  C (1 / 2 : ℝ) * a071951ResidualAlpha d

/-- The residual pencil for the A080248 PF-bidiagonal certificate. -/
def a080248ResidualPencil (d : ℕ) (lam : ℝ) : ℝ[X] :=
  a080248ResidualAlpha d + C lam * a036969ResidualBeta

/-- The A080248 alpha Jensen endpoint after removing the common residual
factor. -/
theorem a080248Alpha_jensen_factor (d : ℕ) (hd : 2 ≤ d) :
    jensenPolynomial d a080248Alpha =
      ((X + 1 : ℝ[X]) ^ (d - 2)) * a080248ResidualAlpha d := by
  rw [jensenPolynomial_eq_diagonalOperator_X_add_one_pow]
  change diagonalOperator (fun k => (((k : ℝ) + 1) * ((k : ℝ) + 2)) / 2)
      ((X + 1 : ℝ[X]) ^ d) =
    ((X + 1 : ℝ[X]) ^ (d - 2)) * a080248ResidualAlpha d
  rw [diagonalOperator_succ_mul_succ_two_half_eq]
  rw [← jensenPolynomial_eq_diagonalOperator_X_add_one_pow]
  change C (1 / 2 : ℝ) * jensenPolynomial d a071951Alpha =
    ((X + 1 : ℝ[X]) ^ (d - 2)) * a080248ResidualAlpha d
  rw [a071951Alpha_jensen_factor d hd]
  simp [a080248ResidualAlpha]
  ring

/-- The A080248 beta Jensen endpoint after removing the common residual
factor. -/
theorem a080248Beta_jensen_factor (d : ℕ) (hd : 2 ≤ d) :
    X * jensenPolynomial d a080248Beta =
      ((X + 1 : ℝ[X]) ^ (d - 2)) * a036969ResidualBeta := by
  change X * jensenPolynomial d (fun _ => (1 : ℝ)) =
    ((X + 1 : ℝ[X]) ^ (d - 2)) * a036969ResidualBeta
  exact oneSequence_jensen_factor d hd

/-- Cubic-discriminant certificate for the A080248 alpha residual. -/
theorem a080248ResidualAlpha_cubicPFDiscriminantCertificate (d : ℕ) :
    CubicPFDiscriminantCertificate (a080248ResidualAlpha d) := by
  refine ⟨?_, ?_, ?_⟩
  · exact nonnegCoeffs_C_mul (by positivity) (a071951ResidualAlpha_hasNonnegCoeffs d)
  · exact (Polynomial.natDegree_C_mul_le (1 / 2 : ℝ) (a071951ResidualAlpha d)).trans
      (natDegree_a071951ResidualAlpha_le d)
  · rw [a080248ResidualAlpha, cubicDiscr_C_mul]
    exact mul_nonneg (by positivity) (cubicDiscr_a071951ResidualAlpha_nonneg d)

private theorem a080248ResidualAlpha_coeff_three (d : ℕ) :
    (a080248ResidualAlpha d).coeff 3 = 0 := by
  rw [a080248ResidualAlpha, Polynomial.coeff_C_mul, a071951ResidualAlpha_coeff_three]
  ring

private theorem a080248ResidualAlpha_coeff_two (d : ℕ) :
    (a080248ResidualAlpha d).coeff 2 =
      (((d : ℝ) + 1) * ((d : ℝ) + 2)) / 2 := by
  rw [a080248ResidualAlpha, Polynomial.coeff_C_mul, a071951ResidualAlpha_coeff_two]
  ring

private theorem a080248ResidualAlpha_coeff_one (d : ℕ) :
    (a080248ResidualAlpha d).coeff 1 = 2 * ((d : ℝ) + 1) := by
  rw [a080248ResidualAlpha, Polynomial.coeff_C_mul, a071951ResidualAlpha_coeff_one]
  ring

private theorem a080248ResidualAlpha_coeff_zero (d : ℕ) :
    (a080248ResidualAlpha d).coeff 0 = 1 := by
  rw [a080248ResidualAlpha, Polynomial.coeff_C_mul, a071951ResidualAlpha_coeff_zero]
  ring

private theorem a080248ResidualPencil_coeff_three (d : ℕ) (lam : ℝ) :
    (a080248ResidualPencil d lam).coeff 3 = lam := by
  rw [a080248ResidualPencil, Polynomial.coeff_add, a080248ResidualAlpha_coeff_three]
  have hterm : (C lam * a036969ResidualBeta).coeff 3 = lam := by
    rw [Polynomial.coeff_C_mul, a036969ResidualBeta_coeff_three]
    ring
  rw [hterm]
  ring

private theorem a080248ResidualPencil_coeff_two (d : ℕ) (lam : ℝ) :
    (a080248ResidualPencil d lam).coeff 2 =
      (((d : ℝ) + 1) * ((d : ℝ) + 2)) / 2 + 2 * lam := by
  rw [a080248ResidualPencil, Polynomial.coeff_add, a080248ResidualAlpha_coeff_two]
  have hterm : (C lam * a036969ResidualBeta).coeff 2 = 2 * lam := by
    rw [Polynomial.coeff_C_mul, a036969ResidualBeta_coeff_two]
    ring
  rw [hterm]

private theorem a080248ResidualPencil_coeff_one (d : ℕ) (lam : ℝ) :
    (a080248ResidualPencil d lam).coeff 1 = 2 * ((d : ℝ) + 1) + lam := by
  rw [a080248ResidualPencil, Polynomial.coeff_add, a080248ResidualAlpha_coeff_one]
  have hterm : (C lam * a036969ResidualBeta).coeff 1 = lam := by
    rw [Polynomial.coeff_C_mul, a036969ResidualBeta_coeff_one]
    ring
  rw [hterm]

private theorem a080248ResidualPencil_coeff_zero (d : ℕ) (lam : ℝ) :
    (a080248ResidualPencil d lam).coeff 0 = 1 := by
  rw [a080248ResidualPencil, Polynomial.coeff_add, a080248ResidualAlpha_coeff_zero]
  have hterm : (C lam * a036969ResidualBeta).coeff 0 = 0 := by
    rw [Polynomial.coeff_C_mul, a036969ResidualBeta_coeff_zero]
    ring
  rw [hterm]
  ring

/-- The A080248 residual pencil has nonnegative coefficients for
nonnegative pencil parameter. -/
theorem a080248ResidualPencil_hasNonnegCoeffs
    (d : ℕ) {lam : ℝ} (hlam : 0 ≤ lam) :
    HasNonnegCoeffs (a080248ResidualPencil d lam) := by
  have hterm : HasNonnegCoeffs (C lam * a036969ResidualBeta) :=
    nonnegCoeffs_C_mul hlam a036969ResidualBeta_hasNonnegCoeffs
  have halpha : HasNonnegCoeffs (a080248ResidualAlpha d) :=
    (a080248ResidualAlpha_cubicPFDiscriminantCertificate d).1
  simpa [a080248ResidualPencil] using halpha.add hterm

/-- The A080248 residual pencil has degree at most three. -/
theorem natDegree_a080248ResidualPencil_le (d : ℕ) (lam : ℝ) :
    (a080248ResidualPencil d lam).natDegree ≤ 3 := by
  unfold a080248ResidualPencil a080248ResidualAlpha a071951ResidualAlpha
    a036969ResidualBeta
  compute_degree

/-- The A080248 residual pencil has nonnegative cubic discriminant for
nonnegative pencil parameter. -/
theorem cubicDiscr_a080248ResidualPencil_nonneg
    (d : ℕ) {lam : ℝ} (hlam : 0 ≤ lam) :
    0 ≤ cubicDiscr (a080248ResidualPencil d lam) := by
  cases d with
  | zero =>
      unfold cubicDiscr
      rw [a080248ResidualPencil_coeff_three, a080248ResidualPencil_coeff_two,
        a080248ResidualPencil_coeff_one, a080248ResidualPencil_coeff_zero]
      ring_nf
      norm_num
  | succ e =>
      have hdisc :
          cubicDiscr (a080248ResidualPencil (Nat.succ e) lam) =
            (((e : ℝ) + 1) / 4) *
              (2 * (e : ℝ) ^ 5 +
                4 * (e : ℝ) ^ 4 * lam +
                24 * (e : ℝ) ^ 4 +
                (e : ℝ) ^ 3 * lam ^ 2 +
                52 * (e : ℝ) ^ 3 * lam +
                114 * (e : ℝ) ^ 3 +
                41 * (e : ℝ) ^ 2 * lam ^ 2 +
                168 * (e : ℝ) ^ 2 * lam +
                268 * (e : ℝ) ^ 2 +
                8 * (e : ℝ) * lam ^ 3 +
                32 * (e : ℝ) * lam ^ 2 +
                176 * (e : ℝ) * lam +
                312 * (e : ℝ) +
                16 * lam ^ 2 + 32 * lam + 144) := by
        unfold cubicDiscr
        rw [a080248ResidualPencil_coeff_three, a080248ResidualPencil_coeff_two,
          a080248ResidualPencil_coeff_one, a080248ResidualPencil_coeff_zero]
        norm_num [Nat.cast_succ]
        ring_nf
      rw [hdisc]
      positivity

/-- Cubic-discriminant certificate for the A080248 residual pencil. -/
theorem a080248ResidualPencil_cubicPFDiscriminantCertificate
    (d : ℕ) {lam : ℝ} (hlam : 0 ≤ lam) :
    CubicPFDiscriminantCertificate (a080248ResidualPencil d lam) :=
  ⟨a080248ResidualPencil_hasNonnegCoeffs d hlam,
    natDegree_a080248ResidualPencil_le d lam,
    cubicDiscr_a080248ResidualPencil_nonneg d hlam⟩

/-- Bundled cubic-residual certificate for the A080248 coefficient-bidiagonal
operator. -/
def a080248_bidiagonalCubicResidualCertificate (d : ℕ) (hd : 2 ≤ d) :
    BidiagonalCubicResidualCertificate a080248Alpha a080248Beta d := by
  rr_pf_bidiagonal_cubic_certificate using
    alpha_factor := a080248Alpha_jensen_factor d hd,
    beta_factor := a080248Beta_jensen_factor d hd,
    alpha_cubic := a080248ResidualAlpha_cubicPFDiscriminantCertificate d,
    beta_cubic := a036969ResidualBeta_cubicPFDiscriminantCertificate,
    pencil_cubic := by
      intro lam hlam
      simpa [a080248ResidualPencil] using
        a080248ResidualPencil_cubicPFDiscriminantCertificate d hlam

/-- The A080248 differential recurrence normalizes to a coefficient-bidiagonal
operator with `alpha(k)=(k+1)(k+2)/2` and `beta(k)=1`. -/
theorem secondDerivativeBidiagonalForm_a080248 (p : ℝ[X]) :
    secondDerivativeBidiagonalForm 1 1 2 0 (1 / 2) 0 p =
      bidiagonalOperator a080248Alpha a080248Beta p := by
  rr_second_derivative_bidiagonal_normalizer [a080248Alpha, a080248Beta]

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
  rr_second_derivative_bidiagonal_normalizer [a156289Alpha, a156289Beta]

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
  rr_second_derivative_bidiagonal_normalizer [a160562Alpha, a160562Beta]

/-- The residual after removing the common `(1 + X)^(d-2)` Jensen factor for
the A160562 `alpha` endpoint. -/
def a160562ResidualAlpha (d : ℕ) : ℝ[X] :=
  C (1 : ℝ) +
    C (8 * (d : ℝ) + 2) * X +
    C ((2 * (d : ℝ) + 1) ^ 2) * X ^ 2

/-- The residual pencil for the A160562 PF-bidiagonal certificate. -/
def a160562ResidualPencil (d : ℕ) (lam : ℝ) : ℝ[X] :=
  a160562ResidualAlpha d + C lam * a036969ResidualBeta

/-- The A160562 alpha Jensen endpoint after removing the common residual
factor. -/
theorem a160562Alpha_jensen_factor (d : ℕ) (hd : 2 ≤ d) :
    jensenPolynomial d a160562Alpha =
      ((X + 1 : ℝ[X]) ^ (d - 2)) * a160562ResidualAlpha d := by
  rw [jensenPolynomial_eq_diagonalOperator_X_add_one_pow]
  change diagonalOperator (fun k => (2 * (k : ℝ) + 1) ^ 2)
      ((X + 1 : ℝ[X]) ^ d) =
    ((X + 1 : ℝ[X]) ^ (d - 2)) * a160562ResidualAlpha d
  rw [diagonalOperator_two_mul_add_one_sq_eq_euler]
  simp only [a160562ResidualAlpha, Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_X, Polynomial.derivative_add, Polynomial.derivative_one,
    Polynomial.derivative_natCast, Polynomial.C_add, Polynomial.C_mul,
    Polynomial.C_pow, Polynomial.C_eq_natCast, Polynomial.C_1, one_mul,
    mul_one, add_zero]
  have hd1 : d - 1 = d - 2 + 1 := by lia
  have hd11 : d - 1 - 1 = d - 2 := by lia
  have hcast_poly := natCast_sub_two_add_one_eq_sub_one d hd
  have hC2 : (C (2 : ℝ) : ℝ[X]) = (2 : ℝ[X]) :=
    Polynomial.C_eq_natCast (R := ℝ) 2
  have hC4 : (C (4 : ℝ) : ℝ[X]) = (4 : ℝ[X]) :=
    Polynomial.C_eq_natCast (R := ℝ) 4
  have hC8 : (C (8 : ℝ) : ℝ[X]) = (8 : ℝ[X]) :=
    Polynomial.C_eq_natCast (R := ℝ) 8
  rw [hd11, hd1, X_add_one_pow_eq_pow_sub_two_mul_sq d hd]
  rw [pow_add]
  rw [hcast_poly, hC2, hC4, hC8]
  ring

/-- The A160562 beta Jensen endpoint after removing the common residual
factor. -/
theorem a160562Beta_jensen_factor (d : ℕ) (hd : 2 ≤ d) :
    X * jensenPolynomial d a160562Beta =
      ((X + 1 : ℝ[X]) ^ (d - 2)) * a036969ResidualBeta := by
  change X * jensenPolynomial d (fun _ => (1 : ℝ)) =
    ((X + 1 : ℝ[X]) ^ (d - 2)) * a036969ResidualBeta
  exact oneSequence_jensen_factor d hd

/-- The A160562 alpha residual has nonnegative coefficients. -/
theorem a160562ResidualAlpha_hasNonnegCoeffs (d : ℕ) :
    HasNonnegCoeffs (a160562ResidualAlpha d) := by
  have h0 : HasNonnegCoeffs (1 : ℝ[X]) := hasNonnegCoeffs_one
  have h1 : HasNonnegCoeffs (C (8 * (d : ℝ) + 2) * X) :=
    nonnegCoeffs_C_mul (by positivity) hasNonnegCoeffs_X
  have h2 : HasNonnegCoeffs (C ((2 * (d : ℝ) + 1) ^ 2) * X ^ 2) :=
    nonnegCoeffs_C_mul (by positivity) (hasNonnegCoeffs_X.pow 2)
  simpa [a160562ResidualAlpha, add_assoc] using h0.add (h1.add h2)

/-- The A160562 alpha residual is at most quadratic. -/
theorem natDegree_a160562ResidualAlpha_le (d : ℕ) :
    (a160562ResidualAlpha d).natDegree ≤ 3 := by
  unfold a160562ResidualAlpha
  compute_degree
  norm_num

/-- The A160562 alpha residual has nonnegative cubic discriminant. -/
theorem cubicDiscr_a160562ResidualAlpha_nonneg (d : ℕ) :
    0 ≤ cubicDiscr (a160562ResidualAlpha d) := by
  have hpoly :
      a160562ResidualAlpha d =
        C (0 : ℝ) * X ^ 3 +
          C ((2 * (d : ℝ) + 1) ^ 2) * X ^ 2 +
            C (8 * (d : ℝ) + 2) * X + C (1 : ℝ) := by
    simp [a160562ResidualAlpha]
    ring
  have hdisc :
      cubicDiscr (a160562ResidualAlpha d) =
        (2 * (d : ℝ) + 1) ^ 4 * (16 * (d : ℝ) * (3 * (d : ℝ) + 1)) := by
    rw [hpoly, cubicDiscr_of_coeffs]
    ring
  rw [hdisc]
  positivity

/-- Cubic-discriminant certificate for the A160562 alpha residual. -/
theorem a160562ResidualAlpha_cubicPFDiscriminantCertificate (d : ℕ) :
    CubicPFDiscriminantCertificate (a160562ResidualAlpha d) :=
  ⟨a160562ResidualAlpha_hasNonnegCoeffs d,
    natDegree_a160562ResidualAlpha_le d,
    cubicDiscr_a160562ResidualAlpha_nonneg d⟩

private theorem a160562ResidualAlpha_coeff_three (d : ℕ) :
    (a160562ResidualAlpha d).coeff 3 = 0 := by
  rw [a160562ResidualAlpha]
  rw [Polynomial.coeff_add, Polynomial.coeff_add]
  rw [Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul_X_pow]
  simp [Polynomial.coeff_one]

private theorem a160562ResidualAlpha_coeff_two (d : ℕ) :
    (a160562ResidualAlpha d).coeff 2 = (2 * (d : ℝ) + 1) ^ 2 := by
  rw [a160562ResidualAlpha]
  rw [Polynomial.coeff_add, Polynomial.coeff_add]
  rw [Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul_X_pow]
  simp [Polynomial.coeff_one]

private theorem a160562ResidualAlpha_coeff_one (d : ℕ) :
    (a160562ResidualAlpha d).coeff 1 = 8 * (d : ℝ) + 2 := by
  rw [a160562ResidualAlpha]
  rw [Polynomial.coeff_add, Polynomial.coeff_add]
  rw [Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul_X_pow]
  simp [Polynomial.coeff_one]

private theorem a160562ResidualAlpha_coeff_zero (d : ℕ) :
    (a160562ResidualAlpha d).coeff 0 = 1 := by
  rw [a160562ResidualAlpha]
  rw [Polynomial.coeff_add, Polynomial.coeff_add]
  rw [Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul_X_pow]
  simp [Polynomial.coeff_one]

private theorem a160562ResidualPencil_coeff_three (d : ℕ) (lam : ℝ) :
    (a160562ResidualPencil d lam).coeff 3 = lam := by
  rw [a160562ResidualPencil, Polynomial.coeff_add, a160562ResidualAlpha_coeff_three]
  have hterm : (C lam * a036969ResidualBeta).coeff 3 = lam := by
    rw [Polynomial.coeff_C_mul, a036969ResidualBeta_coeff_three]
    ring
  rw [hterm]
  ring

private theorem a160562ResidualPencil_coeff_two (d : ℕ) (lam : ℝ) :
    (a160562ResidualPencil d lam).coeff 2 =
      (2 * (d : ℝ) + 1) ^ 2 + 2 * lam := by
  rw [a160562ResidualPencil, Polynomial.coeff_add, a160562ResidualAlpha_coeff_two]
  have hterm : (C lam * a036969ResidualBeta).coeff 2 = 2 * lam := by
    rw [Polynomial.coeff_C_mul, a036969ResidualBeta_coeff_two]
    ring
  rw [hterm]

private theorem a160562ResidualPencil_coeff_one (d : ℕ) (lam : ℝ) :
    (a160562ResidualPencil d lam).coeff 1 = 8 * (d : ℝ) + 2 + lam := by
  rw [a160562ResidualPencil, Polynomial.coeff_add, a160562ResidualAlpha_coeff_one]
  have hterm : (C lam * a036969ResidualBeta).coeff 1 = lam := by
    rw [Polynomial.coeff_C_mul, a036969ResidualBeta_coeff_one]
    ring
  rw [hterm]

private theorem a160562ResidualPencil_coeff_zero (d : ℕ) (lam : ℝ) :
    (a160562ResidualPencil d lam).coeff 0 = 1 := by
  rw [a160562ResidualPencil, Polynomial.coeff_add, a160562ResidualAlpha_coeff_zero]
  have hterm : (C lam * a036969ResidualBeta).coeff 0 = 0 := by
    rw [Polynomial.coeff_C_mul, a036969ResidualBeta_coeff_zero]
    ring
  rw [hterm]
  ring

/-- The A160562 residual pencil has nonnegative coefficients for
nonnegative pencil parameter. -/
theorem a160562ResidualPencil_hasNonnegCoeffs
    (d : ℕ) {lam : ℝ} (hlam : 0 ≤ lam) :
    HasNonnegCoeffs (a160562ResidualPencil d lam) := by
  have hterm : HasNonnegCoeffs (C lam * a036969ResidualBeta) :=
    nonnegCoeffs_C_mul hlam a036969ResidualBeta_hasNonnegCoeffs
  simpa [a160562ResidualPencil] using
    (a160562ResidualAlpha_hasNonnegCoeffs d).add hterm

/-- The A160562 residual pencil has degree at most three. -/
theorem natDegree_a160562ResidualPencil_le (d : ℕ) (lam : ℝ) :
    (a160562ResidualPencil d lam).natDegree ≤ 3 := by
  unfold a160562ResidualPencil a160562ResidualAlpha a036969ResidualBeta
  compute_degree

/-- The A160562 residual pencil has nonnegative cubic discriminant for
nonnegative pencil parameter. -/
theorem cubicDiscr_a160562ResidualPencil_nonneg
    (d : ℕ) {lam : ℝ} (hlam : 0 ≤ lam) :
    0 ≤ cubicDiscr (a160562ResidualPencil d lam) := by
  cases d with
  | zero =>
      unfold cubicDiscr
      rw [a160562ResidualPencil_coeff_three, a160562ResidualPencil_coeff_two,
        a160562ResidualPencil_coeff_one, a160562ResidualPencil_coeff_zero]
      ring_nf
      norm_num
  | succ e =>
      have hdisc :
          cubicDiscr (a160562ResidualPencil (Nat.succ e) lam) =
            16 * ((e : ℝ) + 1) *
              (48 * (e : ℝ) ^ 5 +
                16 * (e : ℝ) ^ 4 * lam +
                352 * (e : ℝ) ^ 4 +
                (e : ℝ) ^ 3 * lam ^ 2 +
                140 * (e : ℝ) ^ 3 * lam +
                1032 * (e : ℝ) ^ 3 +
                21 * (e : ℝ) ^ 2 * lam ^ 2 +
                312 * (e : ℝ) ^ 2 * lam +
                1512 * (e : ℝ) ^ 2 +
                (e : ℝ) * lam ^ 3 +
                21 * (e : ℝ) * lam ^ 2 +
                247 * (e : ℝ) * lam +
                1107 * (e : ℝ) +
                4 * lam ^ 2 + 56 * lam + 324) := by
        unfold cubicDiscr
        rw [a160562ResidualPencil_coeff_three, a160562ResidualPencil_coeff_two,
          a160562ResidualPencil_coeff_one, a160562ResidualPencil_coeff_zero]
        norm_num [Nat.cast_succ]
        ring_nf
      rw [hdisc]
      positivity

/-- Cubic-discriminant certificate for the A160562 residual pencil. -/
theorem a160562ResidualPencil_cubicPFDiscriminantCertificate
    (d : ℕ) {lam : ℝ} (hlam : 0 ≤ lam) :
    CubicPFDiscriminantCertificate (a160562ResidualPencil d lam) :=
  ⟨a160562ResidualPencil_hasNonnegCoeffs d hlam,
    natDegree_a160562ResidualPencil_le d lam,
    cubicDiscr_a160562ResidualPencil_nonneg d hlam⟩

/-- Bundled cubic-residual certificate for the A160562 coefficient-bidiagonal
operator. -/
def a160562_bidiagonalCubicResidualCertificate (d : ℕ) (hd : 2 ≤ d) :
    BidiagonalCubicResidualCertificate a160562Alpha a160562Beta d := by
  rr_pf_bidiagonal_cubic_certificate using
    alpha_factor := a160562Alpha_jensen_factor d hd,
    beta_factor := a160562Beta_jensen_factor d hd,
    alpha_cubic := a160562ResidualAlpha_cubicPFDiscriminantCertificate d,
    beta_cubic := a036969ResidualBeta_cubicPFDiscriminantCertificate,
    pencil_cubic := by
      intro lam hlam
      simpa [a160562ResidualPencil] using
        a160562ResidualPencil_cubicPFDiscriminantCertificate d hlam

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
  rr_second_derivative_bidiagonal_normalizer [a269945Alpha, a269945Beta]

/-- The residual after removing the common `(1 + X)^(d-2)` Jensen factor for
the A269945 `alpha` endpoint. -/
def a269945ResidualAlpha (d : ℕ) : ℝ[X] :=
  C (d : ℝ) * X + C ((d : ℝ) ^ 2) * X ^ 2

/-- The residual pencil for the A269945 PF-bidiagonal certificate. -/
def a269945ResidualPencil (d : ℕ) (lam : ℝ) : ℝ[X] :=
  a269945ResidualAlpha d + C lam * a036969ResidualBeta

/-- The A269945 alpha Jensen endpoint after removing the common residual
factor. -/
theorem a269945Alpha_jensen_factor (d : ℕ) (hd : 2 ≤ d) :
    jensenPolynomial d a269945Alpha =
      ((X + 1 : ℝ[X]) ^ (d - 2)) * a269945ResidualAlpha d := by
  rw [jensenPolynomial_eq_diagonalOperator_X_add_one_pow]
  change diagonalOperator (fun k => (k : ℝ) ^ 2) ((X + 1 : ℝ[X]) ^ d) =
    ((X + 1 : ℝ[X]) ^ (d - 2)) * a269945ResidualAlpha d
  rw [diagonalOperator_sq_eq_euler]
  simp only [a269945ResidualAlpha, Polynomial.derivative_mul, Polynomial.derivative_pow,
    Polynomial.derivative_X, Polynomial.derivative_add, Polynomial.derivative_one,
    Polynomial.derivative_natCast, Polynomial.C_pow, Polynomial.C_eq_natCast,
    one_mul, mul_one, add_zero]
  have hd1 : d - 1 = d - 2 + 1 := by lia
  have hd11 : d - 1 - 1 = d - 2 := by lia
  have hcast_poly := natCast_sub_two_add_one_eq_sub_one d hd
  rw [hd11, hd1]
  rw [pow_add]
  rw [hcast_poly]
  ring

/-- The A269945 beta Jensen endpoint after removing the common residual
factor. -/
theorem a269945Beta_jensen_factor (d : ℕ) (hd : 2 ≤ d) :
    X * jensenPolynomial d a269945Beta =
      ((X + 1 : ℝ[X]) ^ (d - 2)) * a036969ResidualBeta := by
  change X * jensenPolynomial d (fun _ => (1 : ℝ)) =
    ((X + 1 : ℝ[X]) ^ (d - 2)) * a036969ResidualBeta
  exact oneSequence_jensen_factor d hd

/-- The A269945 alpha residual has nonnegative coefficients. -/
theorem a269945ResidualAlpha_hasNonnegCoeffs (d : ℕ) :
    HasNonnegCoeffs (a269945ResidualAlpha d) := by
  have h1 : HasNonnegCoeffs (C (d : ℝ) * X) :=
    nonnegCoeffs_C_mul (by positivity) hasNonnegCoeffs_X
  have h2 : HasNonnegCoeffs (C ((d : ℝ) ^ 2) * X ^ 2) :=
    nonnegCoeffs_C_mul (by positivity) (hasNonnegCoeffs_X.pow 2)
  simpa [a269945ResidualAlpha] using h1.add h2

/-- The A269945 alpha residual is at most quadratic. -/
theorem natDegree_a269945ResidualAlpha_le (d : ℕ) :
    (a269945ResidualAlpha d).natDegree ≤ 3 := by
  unfold a269945ResidualAlpha
  compute_degree
  norm_num

/-- The A269945 alpha residual has nonnegative cubic discriminant. -/
theorem cubicDiscr_a269945ResidualAlpha_nonneg (d : ℕ) :
    0 ≤ cubicDiscr (a269945ResidualAlpha d) := by
  have hpoly :
      a269945ResidualAlpha d =
        C (0 : ℝ) * X ^ 3 +
          C ((d : ℝ) ^ 2) * X ^ 2 + C (d : ℝ) * X + C (0 : ℝ) := by
    simp [a269945ResidualAlpha]
    ring
  have hdisc :
      cubicDiscr (a269945ResidualAlpha d) = (d : ℝ) ^ 6 := by
    rw [hpoly, cubicDiscr_of_coeffs]
    ring
  rw [hdisc]
  positivity

/-- Cubic-discriminant certificate for the A269945 alpha residual. -/
theorem a269945ResidualAlpha_cubicPFDiscriminantCertificate (d : ℕ) :
    CubicPFDiscriminantCertificate (a269945ResidualAlpha d) :=
  ⟨a269945ResidualAlpha_hasNonnegCoeffs d,
    natDegree_a269945ResidualAlpha_le d,
    cubicDiscr_a269945ResidualAlpha_nonneg d⟩

private theorem a269945ResidualAlpha_coeff_three (d : ℕ) :
    (a269945ResidualAlpha d).coeff 3 = 0 := by
  rw [a269945ResidualAlpha]
  rw [Polynomial.coeff_add]
  rw [Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul_X_pow]
  simp

private theorem a269945ResidualAlpha_coeff_two (d : ℕ) :
    (a269945ResidualAlpha d).coeff 2 = (d : ℝ) ^ 2 := by
  rw [a269945ResidualAlpha]
  rw [Polynomial.coeff_add]
  rw [Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul_X_pow]
  simp

private theorem a269945ResidualAlpha_coeff_one (d : ℕ) :
    (a269945ResidualAlpha d).coeff 1 = (d : ℝ) := by
  rw [a269945ResidualAlpha]
  rw [Polynomial.coeff_add]
  rw [Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul_X_pow]
  simp

private theorem a269945ResidualAlpha_coeff_zero (d : ℕ) :
    (a269945ResidualAlpha d).coeff 0 = 0 := by
  rw [a269945ResidualAlpha]
  rw [Polynomial.coeff_add]
  rw [Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul_X_pow]
  simp

private theorem a269945ResidualPencil_coeff_three (d : ℕ) (lam : ℝ) :
    (a269945ResidualPencil d lam).coeff 3 = lam := by
  rw [a269945ResidualPencil, Polynomial.coeff_add, a269945ResidualAlpha_coeff_three]
  have hterm : (C lam * a036969ResidualBeta).coeff 3 = lam := by
    rw [Polynomial.coeff_C_mul, a036969ResidualBeta_coeff_three]
    ring
  rw [hterm]
  ring

private theorem a269945ResidualPencil_coeff_two (d : ℕ) (lam : ℝ) :
    (a269945ResidualPencil d lam).coeff 2 = (d : ℝ) ^ 2 + 2 * lam := by
  rw [a269945ResidualPencil, Polynomial.coeff_add, a269945ResidualAlpha_coeff_two]
  have hterm : (C lam * a036969ResidualBeta).coeff 2 = 2 * lam := by
    rw [Polynomial.coeff_C_mul, a036969ResidualBeta_coeff_two]
    ring
  rw [hterm]

private theorem a269945ResidualPencil_coeff_one (d : ℕ) (lam : ℝ) :
    (a269945ResidualPencil d lam).coeff 1 = (d : ℝ) + lam := by
  rw [a269945ResidualPencil, Polynomial.coeff_add, a269945ResidualAlpha_coeff_one]
  have hterm : (C lam * a036969ResidualBeta).coeff 1 = lam := by
    rw [Polynomial.coeff_C_mul, a036969ResidualBeta_coeff_one]
    ring
  rw [hterm]

private theorem a269945ResidualPencil_coeff_zero (d : ℕ) (lam : ℝ) :
    (a269945ResidualPencil d lam).coeff 0 = 0 := by
  rw [a269945ResidualPencil, Polynomial.coeff_add, a269945ResidualAlpha_coeff_zero]
  have hterm : (C lam * a036969ResidualBeta).coeff 0 = 0 := by
    rw [Polynomial.coeff_C_mul, a036969ResidualBeta_coeff_zero]
    ring
  rw [hterm]
  ring

/-- The A269945 residual pencil has nonnegative coefficients for
nonnegative pencil parameter. -/
theorem a269945ResidualPencil_hasNonnegCoeffs
    (d : ℕ) {lam : ℝ} (hlam : 0 ≤ lam) :
    HasNonnegCoeffs (a269945ResidualPencil d lam) := by
  have hterm : HasNonnegCoeffs (C lam * a036969ResidualBeta) :=
    nonnegCoeffs_C_mul hlam a036969ResidualBeta_hasNonnegCoeffs
  simpa [a269945ResidualPencil] using
    (a269945ResidualAlpha_hasNonnegCoeffs d).add hterm

/-- The A269945 residual pencil has degree at most three. -/
theorem natDegree_a269945ResidualPencil_le (d : ℕ) (lam : ℝ) :
    (a269945ResidualPencil d lam).natDegree ≤ 3 := by
  unfold a269945ResidualPencil a269945ResidualAlpha a036969ResidualBeta
  compute_degree

/-- The A269945 residual pencil has nonnegative cubic discriminant for
nonnegative pencil parameter. -/
theorem cubicDiscr_a269945ResidualPencil_nonneg
    (d : ℕ) {lam : ℝ} (hlam : 0 ≤ lam) :
    0 ≤ cubicDiscr (a269945ResidualPencil d lam) := by
  cases d with
  | zero =>
      unfold cubicDiscr
      rw [a269945ResidualPencil_coeff_three, a269945ResidualPencil_coeff_two,
        a269945ResidualPencil_coeff_one, a269945ResidualPencil_coeff_zero]
      ring_nf
      norm_num
  | succ e =>
      have hdisc :
          cubicDiscr (a269945ResidualPencil (Nat.succ e) lam) =
            ((e : ℝ) + 1) * ((e : ℝ) + lam + 1) ^ 2 *
              ((e : ℝ) ^ 3 + 3 * (e : ℝ) ^ 2 +
                4 * (e : ℝ) * lam + 3 * (e : ℝ) + 1) := by
        unfold cubicDiscr
        rw [a269945ResidualPencil_coeff_three, a269945ResidualPencil_coeff_two,
          a269945ResidualPencil_coeff_one, a269945ResidualPencil_coeff_zero]
        norm_num [Nat.cast_succ]
        ring
      rw [hdisc]
      positivity

/-- Cubic-discriminant certificate for the A269945 residual pencil. -/
theorem a269945ResidualPencil_cubicPFDiscriminantCertificate
    (d : ℕ) {lam : ℝ} (hlam : 0 ≤ lam) :
    CubicPFDiscriminantCertificate (a269945ResidualPencil d lam) :=
  ⟨a269945ResidualPencil_hasNonnegCoeffs d hlam,
    natDegree_a269945ResidualPencil_le d lam,
    cubicDiscr_a269945ResidualPencil_nonneg d hlam⟩

/-- Bundled cubic-residual certificate for the A269945 coefficient-bidiagonal
operator. -/
def a269945_bidiagonalCubicResidualCertificate (d : ℕ) (hd : 2 ≤ d) :
    BidiagonalCubicResidualCertificate a269945Alpha a269945Beta d := by
  rr_pf_bidiagonal_cubic_certificate using
    alpha_factor := a269945Alpha_jensen_factor d hd,
    beta_factor := a269945Beta_jensen_factor d hd,
    alpha_cubic := a269945ResidualAlpha_cubicPFDiscriminantCertificate d,
    beta_cubic := a036969ResidualBeta_cubicPFDiscriminantCertificate,
    pencil_cubic := by
      intro lam hlam
      simpa [a269945ResidualPencil] using
        a269945ResidualPencil_cubicPFDiscriminantCertificate d hlam

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
  rr_second_derivative_bidiagonal_normalizer [a166960Alpha, a166960Beta]

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
  rr_second_derivative_bidiagonal_normalizer [a166961Alpha, a166961Beta]

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
  rr_second_derivative_bidiagonal_normalizer [a166962Alpha, a166962Beta]

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
  rr_second_derivative_bidiagonal_normalizer [a166972Alpha, a166972Beta]

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
  rr_second_derivative_bidiagonal_normalizer [a191935Alpha, a191935Beta]

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
  rr_second_derivative_bidiagonal_normalizer [a371081Alpha, a371081Beta]

/-- A371081-shaped normalized recurrence shell. -/
example
    {P : Nat → ℝ[X]} {d : Nat → ℕ}
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hpres : ∀ n : Nat, BidiagonalPFPreserver (a371081Alpha n) a371081Beta (d n))
    (hrec : ∀ n : Nat,
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (((n : ℝ) + 2) ^ 2) 1 (5 + 2 * (n : ℝ)) 0 1 0 (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) := by
  rr_pf_second_derivative_bidiagonal_sequence using
    preserver := hpres,
    base := hbase,
    degree := hdeg,
    normalizer := (fun n => secondDerivativeBidiagonalForm_a371081 n (P n)),
    recurrence := hrec

/-- A371081-shaped tail shell with row degree `n`.

The first three rows are supplied as base cases; from `n >= 2`, a concrete
cubic-residual certificate can handle the shifted-square Jensen pencil. -/
example
    {P : Nat → ℝ[X]}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (hbase : ∀ n : Nat, n ≤ 2 → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, 2 ≤ n → (P n).natDegree ≤ n)
    (hcert : ∀ n : Nat, 2 ≤ n →
      BidiagonalCubicResidualCertificate (a371081Alpha n) a371081Beta n)
    (hrec : ∀ n : Nat, 2 ≤ n →
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (((n : ℝ) + 2) ^ 2) 1 (5 + 2 * (n : ℝ)) 0 1 0 (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) := by
  rr_pf_second_derivative_bidiagonal_sequence using
    jensen_backend := hbackend,
    cubic_certificate := hcert,
    cutoff := 2,
    base := hbase,
    degree := hdeg,
    normalizer := (fun n _hn => secondDerivativeBidiagonalForm_a371081 n (P n)),
    recurrence := hrec

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
  rr_second_derivative_bidiagonal_normalizer [a371259Alpha, a371259Beta]

/-- A371259-shaped normalized recurrence shell, real-rooted endpoint. -/
example
    {P : Nat → ℝ[X]} {d : Nat → ℕ}
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hpres : ∀ n : Nat, BidiagonalPFPreserver (a371259Alpha n) a371259Beta (d n))
    (hne : ∀ n : Nat, P n ≠ 0)
    (hrec : ∀ n : Nat,
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (((n : ℝ) + 4) ^ 2) 1 (9 + 2 * (n : ℝ)) 0 1 0 (P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_pf_second_derivative_bidiagonal_sequence using
    preserver := hpres,
    base := hbase,
    degree := hdeg,
    normalizer := (fun n => secondDerivativeBidiagonalForm_a371259 n (P n)),
    recurrence := hrec,
    nonzero := hne

/-- A371259-shaped tail shell with row degree `n`. -/
example
    {P : Nat → ℝ[X]}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (hbase : ∀ n : Nat, n ≤ 2 → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, 2 ≤ n → (P n).natDegree ≤ n)
    (hcert : ∀ n : Nat, 2 ≤ n →
      BidiagonalCubicResidualCertificate (a371259Alpha n) a371259Beta n)
    (hne : ∀ n : Nat, P n ≠ 0)
    (hrec : ∀ n : Nat, 2 ≤ n →
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (((n : ℝ) + 4) ^ 2) 1 (9 + 2 * (n : ℝ)) 0 1 0 (P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_pf_second_derivative_bidiagonal_sequence using
    jensen_backend := hbackend,
    cubic_certificate := hcert,
    cutoff := 2,
    base := hbase,
    degree := hdeg,
    normalizer := (fun n _hn => secondDerivativeBidiagonalForm_a371259 n (P n)),
    recurrence := hrec,
    nonzero := hne

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
  rr_second_derivative_bidiagonal_normalizer [a390433Alpha, a390433Beta]

/-- A390433-shaped normalized recurrence shell. -/
example
    {P : Nat → ℝ[X]} {d : Nat → ℕ}
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hpres : ∀ n : Nat, BidiagonalPFPreserver (a390433Alpha n) a390433Beta (d n))
    (hrec : ∀ n : Nat,
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (((n : ℝ) - 2) ^ 2) 1 (-3 + 2 * (n : ℝ)) 0 1 0 (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) := by
  rr_pf_second_derivative_bidiagonal_sequence using
    preserver := hpres,
    base := hbase,
    degree := hdeg,
    normalizer := (fun n => secondDerivativeBidiagonalForm_a390433 n (P n)),
    recurrence := hrec

/-- A390433-shaped tail shell with row degree `n`. -/
example
    {P : Nat → ℝ[X]}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (hbase : ∀ n : Nat, n ≤ 2 → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, 2 ≤ n → (P n).natDegree ≤ n)
    (hcert : ∀ n : Nat, 2 ≤ n →
      BidiagonalCubicResidualCertificate (a390433Alpha n) a390433Beta n)
    (hrec : ∀ n : Nat, 2 ≤ n →
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (((n : ℝ) - 2) ^ 2) 1 (-3 + 2 * (n : ℝ)) 0 1 0 (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) := by
  rr_pf_second_derivative_bidiagonal_sequence using
    jensen_backend := hbackend,
    cubic_certificate := hcert,
    cutoff := 2,
    base := hbase,
    degree := hdeg,
    normalizer := (fun n _hn => secondDerivativeBidiagonalForm_a390433 n (P n)),
    recurrence := hrec

example
    {alpha beta : ℕ → ℝ} {d : ℕ}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (hcert : BidiagonalJensenPencilCertificate alpha beta d) :
    BidiagonalPFPreserver alpha beta d := by
  rr_pf_bidiagonal_preserver using
    jensen_backend := hbackend,
    certificate := hcert

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
    {A B : ℝ[X]}
    (halpha : jensenPolynomial d alpha = ((X + 1 : ℝ[X]) ^ m) * A)
    (hbeta : X * jensenPolynomial d beta = ((X + 1 : ℝ[X]) ^ m) * B)
    (hA : CubicPFDiscriminantCertificate A)
    (hB : CubicPFDiscriminantCertificate B)
    (hS : ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate (A + C lam * B)) :
    BidiagonalJensenPencilCertificate alpha beta d := by
  rr_pf_bidiagonal_certificate using
    alpha_factor := halpha,
    beta_factor := hbeta,
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
    {alpha beta : ℕ → ℝ} {d m : ℕ}
    {A B : ℝ[X]}
    (halpha : jensenPolynomial d alpha = ((X + 1 : ℝ[X]) ^ m) * A)
    (hbeta : X * jensenPolynomial d beta = ((X + 1 : ℝ[X]) ^ m) * B)
    (hA : CubicPFDiscriminantCertificate A)
    (hB : CubicPFDiscriminantCertificate B)
    (hS : ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate (A + C lam * B)) :
    BidiagonalCubicResidualCertificate alpha beta d := by
  rr_pf_bidiagonal_cubic_certificate using
    alpha_factor := halpha,
    beta_factor := hbeta,
    alpha_cubic := hA,
    beta_cubic := hB,
    pencil_cubic := hS

example
    {alpha beta : ℕ → ℝ} {d : ℕ} {p : ℝ[X]}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (hcert : BidiagonalJensenPencilCertificate alpha beta d)
    (hp : IsPFPolynomial p)
    (hdeg : p.natDegree ≤ d) :
    IsPFPolynomial (bidiagonalOperator alpha beta p) := by
  rr_pf_bidiagonal_operator using
    jensen_backend := hbackend,
    certificate := hcert,
    input_pf := hp,
    degree := hdeg

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
    BidiagonalPFPreserver alpha beta d := by
  rr_pf_bidiagonal_preserver_cubic using
    jensen_backend := hbackend,
    cubic_certificate := hcert

example
    {alpha beta : ℕ → ℝ} {d : ℕ} {p : ℝ[X]}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (hcert : BidiagonalCubicResidualCertificate alpha beta d)
    (hp : IsPFPolynomial p)
    (hdeg : p.natDegree ≤ d) :
    IsPFPolynomial (bidiagonalOperator alpha beta p) := by
  rr_pf_bidiagonal_operator_cubic using
    jensen_backend := hbackend,
    cubic_certificate := hcert,
    input_pf := hp,
    degree := hdeg

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
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, N ≤ n → (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat, N ≤ n →
      BidiagonalJensenPencilCertificate (alpha n) (beta n) (d n))
    (hrec : ∀ n : Nat, N ≤ n →
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) := by
  rr_pf_bidiagonal_sequence using
    jensen_backend := hbackend,
    certificate := hcert,
    cutoff := N,
    base := hbase,
    degree := hdeg,
    recurrence := hrec

example
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, N ≤ n → (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat, N ≤ n →
      BidiagonalJensenPencilCertificate (alpha n) (beta n) (d n))
    (hne : ∀ n : Nat, P n ≠ 0)
    (hrec : ∀ n : Nat, N ≤ n →
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_pf_bidiagonal_sequence using
    jensen_backend := hbackend,
    certificate := hcert,
    cutoff := N,
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
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, N ≤ n → (P n).natDegree ≤ d n)
    (hpres : ∀ n : Nat, N ≤ n → BidiagonalPFPreserver (alpha n) (beta n) (d n))
    (hrec : ∀ n : Nat, N ≤ n →
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) := by
  rr_pf_bidiagonal_sequence using
    preserver := hpres,
    cutoff := N,
    base := hbase,
    degree := hdeg,
    recurrence := hrec

example
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, N ≤ n → (P n).natDegree ≤ d n)
    (hpres : ∀ n : Nat, N ≤ n → BidiagonalPFPreserver (alpha n) (beta n) (d n))
    (hne : ∀ n : Nat, P n ≠ 0)
    (hrec : ∀ n : Nat, N ≤ n →
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_pf_bidiagonal_sequence using
    preserver := hpres,
    cutoff := N,
    base := hbase,
    degree := hdeg,
    recurrence := hrec,
    nonzero := hne

example
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, N ≤ n → (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat, N ≤ n →
      BidiagonalCubicResidualCertificate (alpha n) (beta n) (d n))
    (hrec : ∀ n : Nat, N ≤ n →
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) := by
  rr_pf_bidiagonal_sequence using
    jensen_backend := hbackend,
    cubic_certificate := hcert,
    cutoff := N,
    base := hbase,
    degree := hdeg,
    recurrence := hrec

example
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, N ≤ n → (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat, N ≤ n →
      BidiagonalCubicResidualCertificate (alpha n) (beta n) (d n))
    (hne : ∀ n : Nat, P n ≠ 0)
    (hrec : ∀ n : Nat, N ≤ n →
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_pf_bidiagonal_sequence using
    jensen_backend := hbackend,
    cubic_certificate := hcert,
    cutoff := N,
    base := hbase,
    degree := hdeg,
    recurrence := hrec,
    nonzero := hne

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
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ}
    {d m : Nat → ℕ} {A B : Nat → ℝ[X]}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (halpha : ∀ n : Nat,
      jensenPolynomial (d n) (alpha n) = ((X + 1 : ℝ[X]) ^ m n) * A n)
    (hbeta : ∀ n : Nat,
      X * jensenPolynomial (d n) (beta n) =
        ((X + 1 : ℝ[X]) ^ m n) * B n)
    (hA : ∀ n : Nat, CubicPFDiscriminantCertificate (A n))
    (hB : ∀ n : Nat, CubicPFDiscriminantCertificate (B n))
    (hS : ∀ n : Nat, ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate (A n + C lam * B n))
    (hrec : ∀ n : Nat,
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) := by
  rr_pf_bidiagonal_sequence_cubic using
    jensen_backend := hbackend,
    base := hbase,
    degree := hdeg,
    alpha_factor := halpha,
    beta_factor := hbeta,
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
    {P : Nat → ℝ[X]} {a0 a1 b1 b2 c2 c3 : Nat → ℝ}
    {d m : Nat → ℕ} {A B : Nat → ℝ[X]}
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
    (hA : ∀ n : Nat, CubicPFDiscriminantCertificate (A n))
    (hB : ∀ n : Nat, CubicPFDiscriminantCertificate (B n))
    (hS : ∀ n : Nat, ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate (A n + C lam * B n))
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

example
    {P : Nat → ℝ[X]} {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, N ≤ n → (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat, N ≤ n →
      BidiagonalJensenPencilCertificate
        (fun k => secondDerivativeQuadraticCoeff (a0 n) (b1 n) (c2 n) k)
        (fun k => secondDerivativeQuadraticCoeff (a1 n) (b2 n) (c3 n) k)
        (d n))
    (hrec : ∀ n : Nat, N ≤ n →
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) := by
  rr_pf_second_derivative_bidiagonal_sequence using
    jensen_backend := hbackend,
    certificate := hcert,
    cutoff := N,
    base := hbase,
    degree := hdeg,
    recurrence := hrec

example
    {P : Nat → ℝ[X]} {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, N ≤ n → (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat, N ≤ n →
      BidiagonalJensenPencilCertificate
        (fun k => secondDerivativeQuadraticCoeff (a0 n) (b1 n) (c2 n) k)
        (fun k => secondDerivativeQuadraticCoeff (a1 n) (b2 n) (c3 n) k)
        (d n))
    (hne : ∀ n : Nat, P n ≠ 0)
    (hrec : ∀ n : Nat, N ≤ n →
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_pf_second_derivative_bidiagonal_sequence using
    jensen_backend := hbackend,
    certificate := hcert,
    cutoff := N,
    base := hbase,
    degree := hdeg,
    recurrence := hrec,
    nonzero := hne

example
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ}
    {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, N ≤ n → (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat, N ≤ n →
      BidiagonalJensenPencilCertificate (alpha n) (beta n) (d n))
    (hnorm : ∀ n : Nat, N ≤ n →
      secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n) =
        bidiagonalOperator (alpha n) (beta n) (P n))
    (hrec : ∀ n : Nat, N ≤ n →
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) := by
  rr_pf_second_derivative_bidiagonal_sequence using
    jensen_backend := hbackend,
    certificate := hcert,
    cutoff := N,
    base := hbase,
    degree := hdeg,
    normalizer := hnorm,
    recurrence := hrec

example
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ}
    {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, N ≤ n → (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat, N ≤ n →
      BidiagonalJensenPencilCertificate (alpha n) (beta n) (d n))
    (hnorm : ∀ n : Nat, N ≤ n →
      secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n) =
        bidiagonalOperator (alpha n) (beta n) (P n))
    (hne : ∀ n : Nat, P n ≠ 0)
    (hrec : ∀ n : Nat, N ≤ n →
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_pf_second_derivative_bidiagonal_sequence using
    jensen_backend := hbackend,
    certificate := hcert,
    cutoff := N,
    base := hbase,
    degree := hdeg,
    normalizer := hnorm,
    recurrence := hrec,
    nonzero := hne

example
    {P : Nat → ℝ[X]} {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, N ≤ n → (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat, N ≤ n →
      BidiagonalCubicResidualCertificate
        (fun k => secondDerivativeQuadraticCoeff (a0 n) (b1 n) (c2 n) k)
        (fun k => secondDerivativeQuadraticCoeff (a1 n) (b2 n) (c3 n) k)
        (d n))
    (hrec : ∀ n : Nat, N ≤ n →
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) := by
  rr_pf_second_derivative_bidiagonal_sequence using
    jensen_backend := hbackend,
    cubic_certificate := hcert,
    cutoff := N,
    base := hbase,
    degree := hdeg,
    recurrence := hrec

example
    {P : Nat → ℝ[X]} {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, N ≤ n → (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat, N ≤ n →
      BidiagonalCubicResidualCertificate
        (fun k => secondDerivativeQuadraticCoeff (a0 n) (b1 n) (c2 n) k)
        (fun k => secondDerivativeQuadraticCoeff (a1 n) (b2 n) (c3 n) k)
        (d n))
    (hne : ∀ n : Nat, P n ≠ 0)
    (hrec : ∀ n : Nat, N ≤ n →
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_pf_second_derivative_bidiagonal_sequence using
    jensen_backend := hbackend,
    cubic_certificate := hcert,
    cutoff := N,
    base := hbase,
    degree := hdeg,
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
  rr_h_second_derivative_sequence using
    route := pf_bidiagonal,
    jensen_backend := hbackend,
    cubic_certificate := hcert,
    base := hbase,
    degree := hdeg,
    recurrence := hrec

example
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ}
    {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, N ≤ n → (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat, N ≤ n →
      BidiagonalCubicResidualCertificate (alpha n) (beta n) (d n))
    (hnorm : ∀ n : Nat, N ≤ n →
      secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n) =
        bidiagonalOperator (alpha n) (beta n) (P n))
    (hne : ∀ n : Nat, P n ≠ 0)
    (hrec : ∀ n : Nat, N ≤ n →
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_h_second_derivative_sequence using
    route := pf_bidiagonal,
    jensen_backend := hbackend,
    cubic_certificate := hcert,
    cutoff := N,
    base := hbase,
    degree := hdeg,
    normalizer := hnorm,
    recurrence := hrec,
    nonzero := hne

/-- A036969-shaped recurrence shell.

This example has the actual differential recurrence and actual residual
polynomials.  The residual cubic certificates and endpoint factorizations are
discharged below; the remaining row-specific arithmetic input is the active
degree lower bound `2 ≤ d n`. -/
example
    {P : Nat → ℝ[X]} {d : Nat → ℕ}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hd : ∀ n : Nat, 2 ≤ d n)
    (hrec : ∀ n : Nat,
      P (n + 1) = secondDerivativeBidiagonalForm 1 1 3 0 1 0 (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) := by
  rr_pf_second_derivative_bidiagonal_sequence_cubic using
    jensen_backend := hbackend,
    base := hbase,
    degree := hdeg,
    alpha_factor := (fun n => a036969Alpha_jensen_factor (d n) (hd n)),
    beta_factor := (fun n => a036969Beta_jensen_factor (d n) (hd n)),
    alpha_cubic := (fun n => a036969ResidualAlpha_cubicPFDiscriminantCertificate (d n)),
    beta_cubic := (fun _ => a036969ResidualBeta_cubicPFDiscriminantCertificate),
    pencil_cubic := (fun n lam hlam => by
      simpa [a036969ResidualPencil] using
        a036969ResidualPencil_cubicPFDiscriminantCertificate (d n) hlam),
    normalizer := (fun n => secondDerivativeBidiagonalForm_a036969 (P n)),
    recurrence := hrec

example
    {P : Nat → ℝ[X]} {d : Nat → ℕ}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hd : ∀ n : Nat, 2 ≤ d n)
    (hne : ∀ n : Nat, P n ≠ 0)
    (hrec : ∀ n : Nat,
      P (n + 1) = secondDerivativeBidiagonalForm 1 1 3 0 1 0 (P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_pf_second_derivative_bidiagonal_sequence_cubic using
    jensen_backend := hbackend,
    base := hbase,
    degree := hdeg,
    alpha_factor := (fun n => a036969Alpha_jensen_factor (d n) (hd n)),
    beta_factor := (fun n => a036969Beta_jensen_factor (d n) (hd n)),
    alpha_cubic := (fun n => a036969ResidualAlpha_cubicPFDiscriminantCertificate (d n)),
    beta_cubic := (fun _ => a036969ResidualBeta_cubicPFDiscriminantCertificate),
    pencil_cubic := (fun n lam hlam => by
      simpa [a036969ResidualPencil] using
        a036969ResidualPencil_cubicPFDiscriminantCertificate (d n) hlam),
    normalizer := (fun n => secondDerivativeBidiagonalForm_a036969 (P n)),
    recurrence := hrec,
    nonzero := hne

/-- Same A036969 shell through the bundled per-row certificate constructor. -/
example
    {P : Nat → ℝ[X]} {d : Nat → ℕ}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hd : ∀ n : Nat, 2 ≤ d n)
    (hrec : ∀ n : Nat,
      P (n + 1) = secondDerivativeBidiagonalForm 1 1 3 0 1 0 (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) := by
  rr_pf_second_derivative_bidiagonal_sequence using
    jensen_backend := hbackend,
    cubic_certificate := (fun n => a036969_bidiagonalCubicResidualCertificate (d n) (hd n)),
    base := hbase,
    degree := hdeg,
    normalizer := (fun n => secondDerivativeBidiagonalForm_a036969 (P n)),
    recurrence := hrec

example
    {P : Nat → ℝ[X]} {d : Nat → ℕ}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hd : ∀ n : Nat, 2 ≤ d n)
    (hne : ∀ n : Nat, P n ≠ 0)
    (hrec : ∀ n : Nat,
      P (n + 1) = secondDerivativeBidiagonalForm 1 1 3 0 1 0 (P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_pf_second_derivative_bidiagonal_sequence using
    jensen_backend := hbackend,
    cubic_certificate := (fun n => a036969_bidiagonalCubicResidualCertificate (d n) (hd n)),
    base := hbase,
    degree := hdeg,
    normalizer := (fun n => secondDerivativeBidiagonalForm_a036969 (P n)),
    recurrence := hrec,
    nonzero := hne

/-- A071951 shell through the bundled per-row certificate constructor. -/
example
    {P : Nat → ℝ[X]} {d : Nat → ℕ}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hd : ∀ n : Nat, 2 ≤ d n)
    (hrec : ∀ n : Nat,
      P (n + 1) = secondDerivativeBidiagonalForm 2 1 4 0 1 0 (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) := by
  rr_pf_second_derivative_bidiagonal_sequence using
    jensen_backend := hbackend,
    cubic_certificate := (fun n => a071951_bidiagonalCubicResidualCertificate (d n) (hd n)),
    base := hbase,
    degree := hdeg,
    normalizer := (fun n => secondDerivativeBidiagonalForm_a071951 (P n)),
    recurrence := hrec

example
    {P : Nat → ℝ[X]} {d : Nat → ℕ}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hd : ∀ n : Nat, 2 ≤ d n)
    (hne : ∀ n : Nat, P n ≠ 0)
    (hrec : ∀ n : Nat,
      P (n + 1) = secondDerivativeBidiagonalForm 2 1 4 0 1 0 (P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_pf_second_derivative_bidiagonal_sequence using
    jensen_backend := hbackend,
    cubic_certificate := (fun n => a071951_bidiagonalCubicResidualCertificate (d n) (hd n)),
    base := hbase,
    degree := hdeg,
    normalizer := (fun n => secondDerivativeBidiagonalForm_a071951 (P n)),
    recurrence := hrec,
    nonzero := hne

/-- A080248 shell through the bundled per-row certificate constructor. -/
example
    {P : Nat → ℝ[X]} {d : Nat → ℕ}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hd : ∀ n : Nat, 2 ≤ d n)
    (hrec : ∀ n : Nat,
      P (n + 1) = secondDerivativeBidiagonalForm 1 1 2 0 (1 / 2) 0 (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) := by
  rr_pf_second_derivative_bidiagonal_sequence using
    jensen_backend := hbackend,
    cubic_certificate := (fun n => a080248_bidiagonalCubicResidualCertificate (d n) (hd n)),
    base := hbase,
    degree := hdeg,
    normalizer := (fun n => secondDerivativeBidiagonalForm_a080248 (P n)),
    recurrence := hrec

example
    {P : Nat → ℝ[X]} {d : Nat → ℕ}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hd : ∀ n : Nat, 2 ≤ d n)
    (hne : ∀ n : Nat, P n ≠ 0)
    (hrec : ∀ n : Nat,
      P (n + 1) = secondDerivativeBidiagonalForm 1 1 2 0 (1 / 2) 0 (P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_pf_second_derivative_bidiagonal_sequence using
    jensen_backend := hbackend,
    cubic_certificate := (fun n => a080248_bidiagonalCubicResidualCertificate (d n) (hd n)),
    base := hbase,
    degree := hdeg,
    normalizer := (fun n => secondDerivativeBidiagonalForm_a080248 (P n)),
    recurrence := hrec,
    nonzero := hne

/-- A160562 shell through the bundled per-row certificate constructor. -/
example
    {P : Nat → ℝ[X]} {d : Nat → ℕ}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hd : ∀ n : Nat, 2 ≤ d n)
    (hrec : ∀ n : Nat,
      P (n + 1) = secondDerivativeBidiagonalForm 1 1 8 0 4 0 (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) := by
  rr_pf_second_derivative_bidiagonal_sequence using
    jensen_backend := hbackend,
    cubic_certificate := (fun n => a160562_bidiagonalCubicResidualCertificate (d n) (hd n)),
    base := hbase,
    degree := hdeg,
    normalizer := (fun n => secondDerivativeBidiagonalForm_a160562 (P n)),
    recurrence := hrec

example
    {P : Nat → ℝ[X]} {d : Nat → ℕ}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hd : ∀ n : Nat, 2 ≤ d n)
    (hne : ∀ n : Nat, P n ≠ 0)
    (hrec : ∀ n : Nat,
      P (n + 1) = secondDerivativeBidiagonalForm 1 1 8 0 4 0 (P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_pf_second_derivative_bidiagonal_sequence using
    jensen_backend := hbackend,
    cubic_certificate := (fun n => a160562_bidiagonalCubicResidualCertificate (d n) (hd n)),
    base := hbase,
    degree := hdeg,
    normalizer := (fun n => secondDerivativeBidiagonalForm_a160562 (P n)),
    recurrence := hrec,
    nonzero := hne

/-- A269945 shell through the bundled per-row certificate constructor. -/
example
    {P : Nat → ℝ[X]} {d : Nat → ℕ}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hd : ∀ n : Nat, 2 ≤ d n)
    (hrec : ∀ n : Nat,
      P (n + 1) = secondDerivativeBidiagonalForm 0 1 1 0 1 0 (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) := by
  rr_pf_second_derivative_bidiagonal_sequence using
    jensen_backend := hbackend,
    cubic_certificate := (fun n => a269945_bidiagonalCubicResidualCertificate (d n) (hd n)),
    base := hbase,
    degree := hdeg,
    normalizer := (fun n => secondDerivativeBidiagonalForm_a269945 (P n)),
    recurrence := hrec

example
    {P : Nat → ℝ[X]} {d : Nat → ℕ}
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hd : ∀ n : Nat, 2 ≤ d n)
    (hne : ∀ n : Nat, P n ≠ 0)
    (hrec : ∀ n : Nat,
      P (n + 1) = secondDerivativeBidiagonalForm 0 1 1 0 1 0 (P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  rr_pf_second_derivative_bidiagonal_sequence using
    jensen_backend := hbackend,
    cubic_certificate := (fun n => a269945_bidiagonalCubicResidualCertificate (d n) (hd n)),
    base := hbase,
    degree := hdeg,
    normalizer := (fun n => secondDerivativeBidiagonalForm_a269945 (P n)),
    recurrence := hrec,
    nonzero := hne

end TacticExamples
end RealRooted
