import RealRooted.MultiplierSequence.Bidiagonal.Jensen.Contraction

/-!
# Cubic residual certificates for bidiagonal Jensen pencils

This module owns the model-independent residual-certificate data,
factorization builders, rowwise constructors, and one-polynomial
PF-preserver applications.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Build a Jensen-pencil certificate from a common `(1 + X)`-power
factorization and cubic residual discriminant certificates.

This is the Lean-facing shape of the Family H symbolic proof: for each row
degree, factor `J_alpha,d`, `X * J_beta,d`, and the full nonnegative pencil
through the same PF factor `(1 + X)^m`; then discharge only residual cubic
nonnegativity and discriminant side goals. -/
theorem bidiagonalJensenPencilCertificate_of_cubicResidual
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
  refine ⟨?_, ?_, ?_⟩
  · rw [halpha]
    exact isPFPolynomial_X_add_one_pow_mul m
      (isPFPolynomial_of_cubicPFDiscriminantCertificate hA)
  · rw [hbeta]
    exact isPFPolynomial_X_add_one_pow_mul m
      (isPFPolynomial_of_cubicPFDiscriminantCertificate hB)
  · intro lam hlam
    rw [hpencil lam hlam]
    exact isPFPolynomial_X_add_one_pow_mul m
      (isPFPolynomial_of_cubicPFDiscriminantCertificate (hS lam hlam))

/-- The full Jensen-pencil factorization follows from the two endpoint
factorizations when the residual pencil is `A + C lam * B`. -/
theorem bidiagonalJensenPencil_factor_of_endpoint_factors
    {alpha beta : ℕ → ℝ} {d m : ℕ} {A B : ℝ[X]}
    (halpha : jensenPolynomial d alpha = ((X + 1 : ℝ[X]) ^ m) * A)
    (hbeta : X * jensenPolynomial d beta = ((X + 1 : ℝ[X]) ^ m) * B)
    (lam : ℝ) :
    bidiagonalJensenPencil alpha beta d lam =
      ((X + 1 : ℝ[X]) ^ m) * (A + C lam * B) := by
  rw [bidiagonalJensenPencil]
  calc
    jensenPolynomial d alpha + C lam * X * jensenPolynomial d beta =
        ((X + 1 : ℝ[X]) ^ m) * A + C lam * X * jensenPolynomial d beta := by
      rw [halpha]
    _ = ((X + 1 : ℝ[X]) ^ m) * A +
        C lam * (X * jensenPolynomial d beta) := by
      ring
    _ = ((X + 1 : ℝ[X]) ^ m) * A + C lam *
        (((X + 1 : ℝ[X]) ^ m) * B) := by
      rw [hbeta]
    _ = ((X + 1 : ℝ[X]) ^ m) * (A + C lam * B) := by ring

/-- Build a Jensen-pencil certificate from endpoint factorizations and the
derived residual pencil `A + C lam * B`. -/
theorem bidiagonalJensenPencilCertificate_of_endpoint_cubicResidual
    {alpha beta : ℕ → ℝ} {d m : ℕ} {A B : ℝ[X]}
    (halpha : jensenPolynomial d alpha = ((X + 1 : ℝ[X]) ^ m) * A)
    (hbeta : X * jensenPolynomial d beta = ((X + 1 : ℝ[X]) ^ m) * B)
    (hA : CubicPFDiscriminantCertificate A)
    (hB : CubicPFDiscriminantCertificate B)
    (hS : ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate (A + C lam * B)) :
    BidiagonalJensenPencilCertificate alpha beta d :=
  bidiagonalJensenPencilCertificate_of_cubicResidual
    halpha hbeta
    (fun lam _hlam =>
      bidiagonalJensenPencil_factor_of_endpoint_factors halpha hbeta lam)
    hA hB hS

/-- Bundled cubic-residual certificate for one coefficient-bidiagonal
Jensen pencil.

This is the hint object intended for OEIS use.  A sequence-specific certificate
can choose its own common factor exponent, residual cubics, active-degree
cutoff, and arithmetic proof.  The tactic layer then only needs this bundle,
the recurrence, and the global PF-bidiagonal backend theorem. -/
structure BidiagonalCubicResidualCertificate
    (alpha beta : ℕ → ℝ) (d : ℕ) where
  m : ℕ
  alphaResidual : ℝ[X]
  betaResidual : ℝ[X]
  pencilResidual : ℝ → ℝ[X]
  alpha_factor :
    jensenPolynomial d alpha = ((X + 1 : ℝ[X]) ^ m) * alphaResidual
  beta_factor :
    X * jensenPolynomial d beta = ((X + 1 : ℝ[X]) ^ m) * betaResidual
  pencil_factor : ∀ lam : ℝ, 0 ≤ lam →
    bidiagonalJensenPencil alpha beta d lam =
      ((X + 1 : ℝ[X]) ^ m) * pencilResidual lam
  alpha_cubic : CubicPFDiscriminantCertificate alphaResidual
  beta_cubic : CubicPFDiscriminantCertificate betaResidual
  pencil_cubic : ∀ lam : ℝ, 0 ≤ lam →
    CubicPFDiscriminantCertificate (pencilResidual lam)

/-- Build the bundled cubic-residual certificate from its arithmetic leaves. -/
def bidiagonalCubicResidualCertificate_of_cubicResidual
    {alpha beta : ℕ → ℝ} {d m : ℕ}
    {A B : ℝ[X]} {S : ℝ → ℝ[X]}
    (halpha : jensenPolynomial d alpha = ((X + 1 : ℝ[X]) ^ m) * A)
    (hbeta : X * jensenPolynomial d beta = ((X + 1 : ℝ[X]) ^ m) * B)
    (hpencil : ∀ lam : ℝ, 0 ≤ lam →
      bidiagonalJensenPencil alpha beta d lam = ((X + 1 : ℝ[X]) ^ m) * S lam)
    (hA : CubicPFDiscriminantCertificate A)
    (hB : CubicPFDiscriminantCertificate B)
    (hS : ∀ lam : ℝ, 0 ≤ lam → CubicPFDiscriminantCertificate (S lam)) :
    BidiagonalCubicResidualCertificate alpha beta d where
  m := m
  alphaResidual := A
  betaResidual := B
  pencilResidual := S
  alpha_factor := halpha
  beta_factor := hbeta
  pencil_factor := hpencil
  alpha_cubic := hA
  beta_cubic := hB
  pencil_cubic := hS

/-- Build the bundled cubic-residual certificate from endpoint factorizations
and the derived residual pencil `A + C lam * B`. -/
def bidiagonalCubicResidualCertificate_of_endpoint_cubicResidual
    {alpha beta : ℕ → ℝ} {d m : ℕ} {A B : ℝ[X]}
    (halpha : jensenPolynomial d alpha = ((X + 1 : ℝ[X]) ^ m) * A)
    (hbeta : X * jensenPolynomial d beta = ((X + 1 : ℝ[X]) ^ m) * B)
    (hA : CubicPFDiscriminantCertificate A)
    (hB : CubicPFDiscriminantCertificate B)
    (hS : ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate (A + C lam * B)) :
    BidiagonalCubicResidualCertificate alpha beta d :=
  bidiagonalCubicResidualCertificate_of_cubicResidual
    halpha hbeta
    (fun lam _hlam =>
      bidiagonalJensenPencil_factor_of_endpoint_factors halpha hbeta lam)
    hA hB hS

/-- Build a rowwise bundled cubic-residual certificate sequence from its
arithmetic leaves. -/
def bidiagonalCubicResidualCertificate_sequence_of_cubicResidual
    {alpha beta : Nat → ℕ → ℝ} {d m : Nat → ℕ}
    {A B : Nat → ℝ[X]} {S : Nat → ℝ → ℝ[X]}
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
      CubicPFDiscriminantCertificate (S n lam)) :
    ∀ n : Nat, BidiagonalCubicResidualCertificate (alpha n) (beta n) (d n) :=
  fun n =>
    bidiagonalCubicResidualCertificate_of_cubicResidual
      (halpha n) (hbeta n) (hpencil n) (hA n) (hB n) (hS n)

/-- Tail-start version of
`bidiagonalCubicResidualCertificate_sequence_of_cubicResidual`. -/
def bidiagonalCubicResidualCertificate_sequence_of_cubicResidual_from
    {alpha beta : Nat → ℕ → ℝ} {d m : Nat → ℕ}
    {A B : Nat → ℝ[X]} {S : Nat → ℝ → ℝ[X]}
    (N : Nat)
    (halpha : ∀ n : Nat, N ≤ n →
      jensenPolynomial (d n) (alpha n) = ((X + 1 : ℝ[X]) ^ m n) * A n)
    (hbeta : ∀ n : Nat, N ≤ n →
      X * jensenPolynomial (d n) (beta n) =
        ((X + 1 : ℝ[X]) ^ m n) * B n)
    (hpencil : ∀ n : Nat, N ≤ n → ∀ lam : ℝ, 0 ≤ lam →
      bidiagonalJensenPencil (alpha n) (beta n) (d n) lam =
        ((X + 1 : ℝ[X]) ^ m n) * S n lam)
    (hA : ∀ n : Nat, N ≤ n → CubicPFDiscriminantCertificate (A n))
    (hB : ∀ n : Nat, N ≤ n → CubicPFDiscriminantCertificate (B n))
    (hS : ∀ n : Nat, N ≤ n → ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate (S n lam)) :
    ∀ n : Nat, N ≤ n →
      BidiagonalCubicResidualCertificate (alpha n) (beta n) (d n) :=
  fun n hn =>
    bidiagonalCubicResidualCertificate_of_cubicResidual
      (halpha n hn) (hbeta n hn) (hpencil n hn)
      (hA n hn) (hB n hn) (hS n hn)

/-- Build a rowwise bundled cubic-residual certificate sequence from endpoint
factorizations and the derived residual pencil `A n + C lam * B n`. -/
def bidiagonalCubicResidualCertificate_sequence_of_endpoint_cubicResidual
    {alpha beta : Nat → ℕ → ℝ} {d m : Nat → ℕ} {A B : Nat → ℝ[X]}
    (halpha : ∀ n : Nat,
      jensenPolynomial (d n) (alpha n) = ((X + 1 : ℝ[X]) ^ m n) * A n)
    (hbeta : ∀ n : Nat,
      X * jensenPolynomial (d n) (beta n) =
        ((X + 1 : ℝ[X]) ^ m n) * B n)
    (hA : ∀ n : Nat, CubicPFDiscriminantCertificate (A n))
    (hB : ∀ n : Nat, CubicPFDiscriminantCertificate (B n))
    (hS : ∀ n : Nat, ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate (A n + C lam * B n)) :
    ∀ n : Nat, BidiagonalCubicResidualCertificate (alpha n) (beta n) (d n) :=
  fun n =>
    bidiagonalCubicResidualCertificate_of_endpoint_cubicResidual
      (halpha n) (hbeta n) (hA n) (hB n) (hS n)

/-- Tail-start version of
`bidiagonalCubicResidualCertificate_sequence_of_endpoint_cubicResidual`. -/
def bidiagonalCubicResidualCertificate_sequence_of_endpoint_cubicResidual_from
    {alpha beta : Nat → ℕ → ℝ} {d m : Nat → ℕ} {A B : Nat → ℝ[X]}
    (N : Nat)
    (halpha : ∀ n : Nat, N ≤ n →
      jensenPolynomial (d n) (alpha n) = ((X + 1 : ℝ[X]) ^ m n) * A n)
    (hbeta : ∀ n : Nat, N ≤ n →
      X * jensenPolynomial (d n) (beta n) =
        ((X + 1 : ℝ[X]) ^ m n) * B n)
    (hA : ∀ n : Nat, N ≤ n → CubicPFDiscriminantCertificate (A n))
    (hB : ∀ n : Nat, N ≤ n → CubicPFDiscriminantCertificate (B n))
    (hS : ∀ n : Nat, N ≤ n → ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate (A n + C lam * B n)) :
    ∀ n : Nat, N ≤ n →
      BidiagonalCubicResidualCertificate (alpha n) (beta n) (d n) :=
  fun n hn =>
    bidiagonalCubicResidualCertificate_of_endpoint_cubicResidual
      (halpha n hn) (hbeta n hn) (hA n hn) (hB n hn) (hS n hn)

/-- Forget a bundled cubic-residual certificate to the Jensen-pencil
certificate used by the PF-bidiagonal backend. -/
theorem BidiagonalCubicResidualCertificate.toJensenPencilCertificate
    {alpha beta : ℕ → ℝ} {d : ℕ}
    (hcert : BidiagonalCubicResidualCertificate alpha beta d) :
    BidiagonalJensenPencilCertificate alpha beta d :=
  bidiagonalJensenPencilCertificate_of_cubicResidual
    hcert.alpha_factor hcert.beta_factor hcert.pencil_factor
    hcert.alpha_cubic hcert.beta_cubic hcert.pencil_cubic

/-- A bundled cubic-residual certificate gives a coefficient-bidiagonal PF
preserver once the global Jensen-pencil backend is available. -/
theorem BidiagonalCubicResidualCertificate.toPFPreserver
    {alpha beta : ℕ → ℝ} {d : ℕ}
    (hcert : BidiagonalCubicResidualCertificate alpha beta d) :
    BidiagonalPFPreserver alpha beta d :=
  bidiagonalPFPreserver_of_jensenPencil hcert.toJensenPencilCertificate

/-- Rowwise cubic-residual certificates give rowwise coefficient-bidiagonal
PF preservers. -/
theorem BidiagonalCubicResidualCertificate.toPFPreserver_sequence
    {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (hcert : ∀ n : Nat,
      BidiagonalCubicResidualCertificate (alpha n) (beta n) (d n)) :
    ∀ n : Nat, BidiagonalPFPreserver (alpha n) (beta n) (d n) :=
  fun n => (hcert n).toPFPreserver

/-- Tail-start rowwise version of
`BidiagonalCubicResidualCertificate.toPFPreserver_sequence`. -/
theorem BidiagonalCubicResidualCertificate.toPFPreserver_sequence_from
    (N : Nat) {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (hcert : ∀ n : Nat, N ≤ n →
      BidiagonalCubicResidualCertificate (alpha n) (beta n) (d n)) :
    ∀ n : Nat, N ≤ n → BidiagonalPFPreserver (alpha n) (beta n) (d n) :=
  fun n hn => (hcert n hn).toPFPreserver

/-- Apply a bundled cubic-residual certificate as a PF-bidiagonal preserver. -/
theorem bidiagonalPFPreserver_of_cubicResidualCertificate
    {alpha beta : ℕ → ℝ} {d : ℕ}
    (hcert : BidiagonalCubicResidualCertificate alpha beta d) :
    BidiagonalPFPreserver alpha beta d :=
  hcert.toPFPreserver

/-- Method-style compatibility spelling for cubic-residual PF-bidiagonal certificates. -/
theorem BidiagonalPFPreserver.of_cubicResidualCertificate
    {alpha beta : ℕ → ℝ} {d : ℕ}
    (hcert : BidiagonalCubicResidualCertificate alpha beta d) :
    BidiagonalPFPreserver alpha beta d :=
  bidiagonalPFPreserver_of_cubicResidualCertificate hcert

/-- Apply a PF-bidiagonal preserver certificate to one polynomial. -/
theorem isPFPolynomial_bidiagonalOperator_of_preserver
    {alpha beta : ℕ → ℝ} {d : ℕ} {p : ℝ[X]}
    (hpres : BidiagonalPFPreserver alpha beta d)
    (hp : IsPFPolynomial p)
    (hdeg : p.natDegree ≤ d) :
    IsPFPolynomial (bidiagonalOperator alpha beta p) :=
  hpres hp hdeg

/-- Apply a Jensen-pencil backend certificate to one polynomial. -/
theorem isPFPolynomial_bidiagonalOperator_of_jensenPencil
    {alpha beta : ℕ → ℝ} {d : ℕ} {p : ℝ[X]}
    (hcert : BidiagonalJensenPencilCertificate alpha beta d)
    (hp : IsPFPolynomial p)
    (hdeg : p.natDegree ≤ d) :
    IsPFPolynomial (bidiagonalOperator alpha beta p) :=
  isPFPolynomial_bidiagonalOperator_of_preserver
    hcert.toPFPreserver hp hdeg

/-- Apply a bundled cubic-residual certificate to one coefficient-bidiagonal
operator. -/
theorem isPFPolynomial_bidiagonalOperator_of_cubicResidualCertificate
    {alpha beta : ℕ → ℝ} {d : ℕ} {p : ℝ[X]}
    (hcert : BidiagonalCubicResidualCertificate alpha beta d)
    (hp : IsPFPolynomial p)
    (hdeg : p.natDegree ≤ d) :
    IsPFPolynomial (bidiagonalOperator alpha beta p) :=
  isPFPolynomial_bidiagonalOperator_of_preserver
    hcert.toPFPreserver hp hdeg


end RealRooted
