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
  (X + 1) ^ 2

/-- The residual pencil for the A036969 PF-bidiagonal certificate. -/
def a036969ResidualPencil (d : ℕ) (lam : ℝ) : ℝ[X] :=
  a036969ResidualAlpha d + C lam * X * a036969ResidualBeta

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
polynomials.  The remaining hypotheses are exactly the symbolic
Jensen-factorization and cubic-discriminant leaves that the Family H paper
proof or certificate checker should provide. -/
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
    (hA : ∀ n : Nat,
      CubicPFDiscriminantCertificate (a036969ResidualAlpha (d n)))
    (hB : CubicPFDiscriminantCertificate a036969ResidualBeta)
    (hS : ∀ n : Nat, ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate (a036969ResidualPencil (d n) lam))
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
    alpha_cubic := hA,
    beta_cubic := (fun _ => hB),
    pencil_cubic := hS,
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
    (hA : ∀ n : Nat,
      CubicPFDiscriminantCertificate (a036969ResidualAlpha (d n)))
    (hB : CubicPFDiscriminantCertificate a036969ResidualBeta)
    (hS : ∀ n : Nat, ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate (a036969ResidualPencil (d n) lam))
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
    alpha_cubic := hA,
    beta_cubic := (fun _ => hB),
    pencil_cubic := hS,
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
