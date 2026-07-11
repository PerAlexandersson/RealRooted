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
    (hbackend : ∀ {alpha beta : ℕ → ℝ} {d : ℕ},
      BidiagonalJensenPencilCertificate alpha beta d →
      BidiagonalPFPreserver alpha beta d)
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

/-- A071951 has `alpha_k=(k+1)(k+2)` and `beta_k=1`. -/
example (p : ℝ[X]) :
    secondDerivativeBidiagonalForm 2 1 4 0 1 0 p =
      bidiagonalOperator
        (fun k => ((k : ℝ) + 1) * ((k : ℝ) + 2))
        (fun _ => 1)
        p := by
  rw [secondDerivativeBidiagonalForm_eq_bidiagonalOperator]
  congr
  · funext k
    simp [secondDerivativeQuadraticCoeff]
    ring
  · funext k
    simp [secondDerivativeQuadraticCoeff]

/-- A080248 has `alpha_k=(k+1)(k+2)/2` and `beta_k=1`. -/
example (p : ℝ[X]) :
    secondDerivativeBidiagonalForm 1 1 2 0 (1 / 2) 0 p =
      bidiagonalOperator
        (fun k => (((k : ℝ) + 1) * ((k : ℝ) + 2)) / 2)
        (fun _ => 1)
        p := by
  rw [secondDerivativeBidiagonalForm_eq_bidiagonalOperator]
  congr
  · funext k
    simp [secondDerivativeQuadraticCoeff]
    ring
  · funext k
    simp [secondDerivativeQuadraticCoeff]

/-- A156289 has `alpha_k=(k+1)^2` and `beta_k=2k+3`. -/
example (p : ℝ[X]) :
    secondDerivativeBidiagonalForm 1 3 3 2 1 0 p =
      bidiagonalOperator
        (fun k => ((k : ℝ) + 1) ^ 2)
        (fun k => 2 * (k : ℝ) + 3)
        p := by
  rw [secondDerivativeBidiagonalForm_eq_bidiagonalOperator]
  congr
  · funext k
    simp [secondDerivativeQuadraticCoeff]
    ring
  · funext k
    simp [secondDerivativeQuadraticCoeff]
    ring

/-- A160562 has `alpha_k=(2k+1)^2` and `beta_k=1`. -/
example (p : ℝ[X]) :
    secondDerivativeBidiagonalForm 1 1 8 0 4 0 p =
      bidiagonalOperator
        (fun k => (2 * (k : ℝ) + 1) ^ 2)
        (fun _ => 1)
        p := by
  rw [secondDerivativeBidiagonalForm_eq_bidiagonalOperator]
  congr
  · funext k
    simp [secondDerivativeQuadraticCoeff]
    ring
  · funext k
    simp [secondDerivativeQuadraticCoeff]

/-- A269945 has `alpha_k=k^2` and `beta_k=1`. -/
example (p : ℝ[X]) :
    secondDerivativeBidiagonalForm 0 1 1 0 1 0 p =
      bidiagonalOperator
        (fun k => (k : ℝ) ^ 2)
        (fun _ => 1)
        p := by
  rw [secondDerivativeBidiagonalForm_eq_bidiagonalOperator]
  congr
  · funext k
    simp [secondDerivativeQuadraticCoeff]
    ring
  · funext k
    simp [secondDerivativeQuadraticCoeff]

/-- A166960 has `alpha_k=(k+1)^2` and `beta_k=n+1-k`. -/
example (n : ℕ) (p : ℝ[X]) :
    secondDerivativeBidiagonalForm 1 (1 + (n : ℝ)) 3 (-1) 1 0 p =
      bidiagonalOperator
        (fun k => ((k : ℝ) + 1) ^ 2)
        (fun k => (n : ℝ) + 1 - (k : ℝ))
        p := by
  rw [secondDerivativeBidiagonalForm_eq_bidiagonalOperator]
  congr
  · funext k
    simp [secondDerivativeQuadraticCoeff]
    ring
  · funext k
    simp [secondDerivativeQuadraticCoeff]
    ring

/-- A166961 has `alpha_k=(k+1)(2k+1)` and `beta_k=2n+1-2k`. -/
example (n : ℕ) (p : ℝ[X]) :
    secondDerivativeBidiagonalForm 1 (1 + 2 * (n : ℝ)) 5 (-2) 2 0 p =
      bidiagonalOperator
        (fun k => ((k : ℝ) + 1) * (2 * (k : ℝ) + 1))
        (fun k => 2 * (n : ℝ) + 1 - 2 * (k : ℝ))
        p := by
  rw [secondDerivativeBidiagonalForm_eq_bidiagonalOperator]
  congr
  · funext k
    simp [secondDerivativeQuadraticCoeff]
    ring
  · funext k
    simp [secondDerivativeQuadraticCoeff]
    ring

/-- A166962 has `alpha_k=(k+1)(3k+1)` and `beta_k=3n-5-3k`. -/
example (n : ℕ) (p : ℝ[X]) :
    secondDerivativeBidiagonalForm 1 (-5 + 3 * (n : ℝ)) 7 (-3) 3 0 p =
      bidiagonalOperator
        (fun k => ((k : ℝ) + 1) * (3 * (k : ℝ) + 1))
        (fun k => 3 * (n : ℝ) - 5 - 3 * (k : ℝ))
        p := by
  rw [secondDerivativeBidiagonalForm_eq_bidiagonalOperator]
  congr
  · funext k
    simp [secondDerivativeQuadraticCoeff]
    ring
  · funext k
    simp [secondDerivativeQuadraticCoeff]
    ring

/-- A166972 has `alpha_k=(k+1)(3k+1)` and `beta_k=n-1-k`. -/
example (n : ℕ) (p : ℝ[X]) :
    secondDerivativeBidiagonalForm 1 (-1 + (n : ℝ)) 7 (-1) 3 0 p =
      bidiagonalOperator
        (fun k => ((k : ℝ) + 1) * (3 * (k : ℝ) + 1))
        (fun k => (n : ℝ) - 1 - (k : ℝ))
        p := by
  rw [secondDerivativeBidiagonalForm_eq_bidiagonalOperator]
  congr
  · funext k
    simp [secondDerivativeQuadraticCoeff]
    ring
  · funext k
    simp [secondDerivativeQuadraticCoeff]
    ring

/-- A191935 has `alpha_k=1` and `beta_k=(n+1-k)(n+2-k)`. -/
example (n : ℕ) (p : ℝ[X]) :
    secondDerivativeBidiagonalForm
        1 (2 + 3 * (n : ℝ) + (n : ℝ) ^ 2)
        0 (-2 - 2 * (n : ℝ)) 0 1 p =
      bidiagonalOperator
        (fun _ => 1)
        (fun k => ((n : ℝ) + 1 - (k : ℝ)) *
          ((n : ℝ) + 2 - (k : ℝ)))
        p := by
  rw [secondDerivativeBidiagonalForm_eq_bidiagonalOperator]
  congr
  · funext k
    simp [secondDerivativeQuadraticCoeff]
  · funext k
    simp [secondDerivativeQuadraticCoeff]
    ring

/-- A371081 has `alpha_k=(n+k+2)^2` and `beta_k=1`. -/
example (n : ℕ) (p : ℝ[X]) :
    secondDerivativeBidiagonalForm
        (((n : ℝ) + 2) ^ 2) 1 (5 + 2 * (n : ℝ)) 0 1 0 p =
      bidiagonalOperator
        (fun k => ((n : ℝ) + (k : ℝ) + 2) ^ 2)
        (fun _ => 1)
        p := by
  rw [secondDerivativeBidiagonalForm_eq_bidiagonalOperator]
  congr
  · funext k
    simp [secondDerivativeQuadraticCoeff]
    ring
  · funext k
    simp [secondDerivativeQuadraticCoeff]

/-- A371259 has `alpha_k=(n+k+4)^2` and `beta_k=1`. -/
example (n : ℕ) (p : ℝ[X]) :
    secondDerivativeBidiagonalForm
        (((n : ℝ) + 4) ^ 2) 1 (9 + 2 * (n : ℝ)) 0 1 0 p =
      bidiagonalOperator
        (fun k => ((n : ℝ) + (k : ℝ) + 4) ^ 2)
        (fun _ => 1)
        p := by
  rw [secondDerivativeBidiagonalForm_eq_bidiagonalOperator]
  congr
  · funext k
    simp [secondDerivativeQuadraticCoeff]
    ring
  · funext k
    simp [secondDerivativeQuadraticCoeff]

/-- A390433 has `alpha_k=(n+k-2)^2` and `beta_k=1`. -/
example (n : ℕ) (p : ℝ[X]) :
    secondDerivativeBidiagonalForm
        (((n : ℝ) - 2) ^ 2) 1 (-3 + 2 * (n : ℝ)) 0 1 0 p =
      bidiagonalOperator
        (fun k => ((n : ℝ) + (k : ℝ) - 2) ^ 2)
        (fun _ => 1)
        p := by
  rw [secondDerivativeBidiagonalForm_eq_bidiagonalOperator]
  congr
  · funext k
    simp [secondDerivativeQuadraticCoeff]
    ring
  · funext k
    simp [secondDerivativeQuadraticCoeff]

example
    {alpha beta : ℕ → ℝ} {d : ℕ}
    (hbackend : ∀ {alpha beta : ℕ → ℝ} {d : ℕ},
      BidiagonalJensenPencilCertificate alpha beta d →
      BidiagonalPFPreserver alpha beta d)
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
    {alpha beta : ℕ → ℝ} {d : ℕ} {p : ℝ[X]}
    (hbackend : ∀ {alpha beta : ℕ → ℝ} {d : ℕ},
      BidiagonalJensenPencilCertificate alpha beta d →
      BidiagonalPFPreserver alpha beta d)
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
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (hbackend : ∀ {alpha beta : ℕ → ℝ} {d : ℕ},
      BidiagonalJensenPencilCertificate alpha beta d →
      BidiagonalPFPreserver alpha beta d)
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
    (hbackend : ∀ {alpha beta : ℕ → ℝ} {d : ℕ},
      BidiagonalJensenPencilCertificate alpha beta d →
      BidiagonalPFPreserver alpha beta d)
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
    (hbackend : ∀ {alpha beta : ℕ → ℝ} {d : ℕ},
      BidiagonalJensenPencilCertificate alpha beta d →
      BidiagonalPFPreserver alpha beta d)
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
    {P : Nat → ℝ[X]} {a0 a1 b1 b2 c2 c3 : Nat → ℝ}
    {d m : Nat → ℕ} {A B : Nat → ℝ[X]} {S : Nat → ℝ → ℝ[X]}
    (hbackend : ∀ {alpha beta : ℕ → ℝ} {d : ℕ},
      BidiagonalJensenPencilCertificate alpha beta d →
      BidiagonalPFPreserver alpha beta d)
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
    {P : Nat → ℝ[X]} {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (hbackend : ∀ {alpha beta : ℕ → ℝ} {d : ℕ},
      BidiagonalJensenPencilCertificate alpha beta d →
      BidiagonalPFPreserver alpha beta d)
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

/-- A036969-shaped recurrence shell.

This example has the actual differential recurrence and actual residual
polynomials.  The remaining hypotheses are exactly the symbolic
Jensen-factorization and cubic-discriminant leaves that the Family H paper
proof or certificate checker should provide. -/
example
    {P : Nat → ℝ[X]} {d m : Nat → ℕ}
    (hbackend : ∀ {alpha beta : ℕ → ℝ} {d : ℕ},
      BidiagonalJensenPencilCertificate alpha beta d →
      BidiagonalPFPreserver alpha beta d)
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
  have hrecB : ∀ n : Nat,
      P (n + 1) = bidiagonalOperator a036969Alpha a036969Beta (P n) := by
    intro n
    rw [hrec n, secondDerivativeBidiagonalForm_a036969]
  rr_pf_bidiagonal_sequence_cubic using
    jensen_backend := hbackend,
    base := hbase,
    degree := hdeg,
    alpha_factor := halpha,
    beta_factor := hbeta,
    pencil_factor := hpencil,
    alpha_cubic := hA,
    beta_cubic := (fun _ => hB),
    pencil_cubic := hS,
    recurrence := hrecB

/-- Same A036969 shell, but with all residual/factorization hints bundled in a
single per-row certificate.  This is the intended OEIS-facing interface once
the arithmetic leaves have been generated. -/
example
    {P : Nat → ℝ[X]} {d : Nat → ℕ}
    (hbackend : ∀ {alpha beta : ℕ → ℝ} {d : ℕ},
      BidiagonalJensenPencilCertificate alpha beta d →
      BidiagonalPFPreserver alpha beta d)
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat,
      BidiagonalCubicResidualCertificate a036969Alpha a036969Beta (d n))
    (hrec : ∀ n : Nat,
      P (n + 1) = secondDerivativeBidiagonalForm 1 1 3 0 1 0 (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) := by
  have hrecB : ∀ n : Nat,
      P (n + 1) = bidiagonalOperator a036969Alpha a036969Beta (P n) := by
    intro n
    rw [hrec n, secondDerivativeBidiagonalForm_a036969]
  rr_pf_bidiagonal_sequence using
    jensen_backend := hbackend,
    cubic_certificate := hcert,
    base := hbase,
    degree := hdeg,
    recurrence := hrecB

end TacticExamples
end RealRooted
