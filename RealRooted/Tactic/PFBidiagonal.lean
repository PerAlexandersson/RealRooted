import RealRooted.MultiplierSequence
import RealRooted.Tactic.Finish
import RealRooted.Tactic.Lookup

/-!
# PF bidiagonal operator shells

This file packages the coefficient-bidiagonal operator that appears in the
remaining one-step second-derivative OEIS recurrences.  The total-nonnegative
or PF-preserver theorem is not currently available in this repository, so this
file exposes a Lean-facing preserver certificate that concrete backends can
later discharge.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- Coefficient-bidiagonal operator

`bidiagonalOperator alpha beta` sends a coefficient vector `(a_k)` to
`(alpha_k a_k + beta_{k-1} a_{k-1})`, with the second term omitted at `k=0`.
Equivalently,

```text
L(p) = diagonalOperator alpha p + X * diagonalOperator beta p.
```
-/
def bidiagonalOperator (alpha beta : ℕ → ℝ) (p : ℝ[X]) : ℝ[X] :=
  diagonalOperator alpha p + X * diagonalOperator beta p

@[simp] theorem bidiagonalOperator_zero (alpha beta : ℕ → ℝ) :
    bidiagonalOperator alpha beta 0 = 0 := by
  simp [bidiagonalOperator]

@[simp] theorem coeff_bidiagonalOperator_zero
    (alpha beta : ℕ → ℝ) (p : ℝ[X]) :
    (bidiagonalOperator alpha beta p).coeff 0 = alpha 0 * p.coeff 0 := by
  simp [bidiagonalOperator]

@[simp] theorem coeff_bidiagonalOperator_succ
    (alpha beta : ℕ → ℝ) (p : ℝ[X]) (n : ℕ) :
    (bidiagonalOperator alpha beta p).coeff (n + 1) =
      alpha (n + 1) * p.coeff (n + 1) + beta n * p.coeff n := by
  simp [bidiagonalOperator]

/-- Quadratic coefficient shape produced by
`a + b X D + c X^2 D^2` on the diagonal, and by the shifted
`a X + b X^2 D + c X^3 D^2` part on the lower bidiagonal. -/
def secondDerivativeQuadraticCoeff (a b c : ℝ) (k : ℕ) : ℝ :=
  a + b * (k : ℝ) + c * (k : ℝ) * ((k : ℝ) - 1)

/-- Six-parameter second-derivative operator whose coefficient action is
lower bidiagonal.

The parameters are the coefficients of
`a₀ + a₁ X + b₁ X D + b₂ X² D + c₂ X² D² + c₃ X³ D²`.
The nested `X * (...)` presentation is deliberate: it keeps coefficient
normalization close to repeated uses of `coeff_X_mul`. -/
def secondDerivativeBidiagonalForm
    (a0 a1 b1 b2 c2 c3 : ℝ) (p : ℝ[X]) : ℝ[X] :=
  C a0 * p +
    C a1 * (X * p) +
    C b1 * (X * p.derivative) +
    C b2 * (X * (X * p.derivative)) +
    C c2 * (X * (X * p.derivative.derivative)) +
    C c3 * (X * (X * (X * p.derivative.derivative)))

/-- The six-parameter second-derivative form acts as a coefficient-bidiagonal
operator. -/
theorem secondDerivativeBidiagonalForm_eq_bidiagonalOperator
    (a0 a1 b1 b2 c2 c3 : ℝ) (p : ℝ[X]) :
    secondDerivativeBidiagonalForm a0 a1 b1 b2 c2 c3 p =
      bidiagonalOperator
        (fun k => secondDerivativeQuadraticCoeff a0 b1 c2 k)
        (fun k => secondDerivativeQuadraticCoeff a1 b2 c3 k)
        p := by
  ext k
  cases k with
  | zero =>
      simp [secondDerivativeBidiagonalForm, bidiagonalOperator,
        secondDerivativeQuadraticCoeff]
  | succ k =>
      cases k with
      | zero =>
          simp [secondDerivativeBidiagonalForm, bidiagonalOperator,
            secondDerivativeQuadraticCoeff, coeff_derivative]
          ring
      | succ k =>
          cases k with
          | zero =>
              simp [secondDerivativeBidiagonalForm, bidiagonalOperator,
                secondDerivativeQuadraticCoeff, coeff_derivative]
              ring
          | succ k =>
              simp [secondDerivativeBidiagonalForm, bidiagonalOperator,
                secondDerivativeQuadraticCoeff, coeff_derivative]
              ring

/-- Normalize a second-derivative differential form to a named coefficient
bidiagonal operator by identifying the two quadratic coefficient functions. -/
theorem secondDerivativeBidiagonalForm_eq_bidiagonalOperator_of_coeff_eq
    {alpha beta : ℕ → ℝ} {a0 a1 b1 b2 c2 c3 : ℝ} (p : ℝ[X])
    (halpha : ∀ k : ℕ, secondDerivativeQuadraticCoeff a0 b1 c2 k = alpha k)
    (hbeta : ∀ k : ℕ, secondDerivativeQuadraticCoeff a1 b2 c3 k = beta k) :
    secondDerivativeBidiagonalForm a0 a1 b1 b2 c2 c3 p =
      bidiagonalOperator alpha beta p := by
  rw [secondDerivativeBidiagonalForm_eq_bidiagonalOperator]
  congr
  · funext k
    exact halpha k
  · funext k
    exact hbeta k

/-- The bidiagonal operator raises degree by at most one. -/
theorem natDegree_bidiagonalOperator_le
    (alpha beta : ℕ → ℝ) (p : ℝ[X]) :
    (bidiagonalOperator alpha beta p).natDegree ≤ p.natDegree + 1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  cases n with
  | zero =>
      lia
  | succ n =>
      have hpn1 : p.coeff (n + 1) = 0 := by
        exact coeff_eq_zero_of_natDegree_lt (by lia)
      have hpn : p.coeff n = 0 := by
        exact coeff_eq_zero_of_natDegree_lt (by lia)
      simp [hpn1, hpn]

/-- Nonnegative bidiagonal entries preserve coefficient nonnegativity. -/
theorem HasNonnegCoeffs.bidiagonalOperator
    {alpha beta : ℕ → ℝ} {p : ℝ[X]}
    (hp : HasNonnegCoeffs p)
    (halpha : ∀ n : ℕ, 0 ≤ alpha n)
    (hbeta : ∀ n : ℕ, 0 ≤ beta n) :
    HasNonnegCoeffs (bidiagonalOperator alpha beta p) := by
  intro n
  cases n with
  | zero =>
      simpa using mul_nonneg (halpha 0) (hp 0)
  | succ n =>
      simpa using add_nonneg
        (mul_nonneg (halpha (n + 1)) (hp (n + 1)))
        (mul_nonneg (hbeta n) (hp n))

/-- Backend certificate for one coefficient-bidiagonal PF preserver.

Entrywise nonnegativity of `alpha` and `beta` is useful for coefficient
nonnegativity, but it is not by itself a proof of PF preservation.  Concrete
backends should prove this predicate from an appropriate total-nonnegativity,
stable-polynomial, or finite multiplier-sequence criterion. -/
def BidiagonalPFPreserver (alpha beta : ℕ → ℝ) (d : ℕ) : Prop :=
  ∀ {p : ℝ[X]},
    IsPFPolynomial p →
    p.natDegree ≤ d →
    IsPFPolynomial (bidiagonalOperator alpha beta p)

/-- Jensen-pencil attached to a coefficient-bidiagonal operator.

For a degree bound `d`, the two diagonal parts have finite Jensen kernels
`jensenPolynomial d alpha` and `jensenPolynomial d beta`.  The pencil

```text
J_alpha,d(t) + lambda * t * J_beta,d(t)
```

is the finite Schur--Szego/proper-position certificate we expect to use for
the Family H coefficient-bidiagonal operators. -/
def bidiagonalJensenPencil (alpha beta : ℕ → ℝ) (d : ℕ) (lam : ℝ) : ℝ[X] :=
  jensenPolynomial d alpha + C lam * X * jensenPolynomial d beta

@[simp] theorem bidiagonalJensenPencil_zero_lambda
    (alpha beta : ℕ → ℝ) (d : ℕ) :
    bidiagonalJensenPencil alpha beta d 0 = jensenPolynomial d alpha := by
  simp [bidiagonalJensenPencil]

/-- The Jensen pencil has degree at most `d+1`. -/
theorem natDegree_bidiagonalJensenPencil_le
    (alpha beta : ℕ → ℝ) (d : ℕ) (lam : ℝ) :
    (bidiagonalJensenPencil alpha beta d lam).natDegree ≤ d + 1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  have halpha : (jensenPolynomial d alpha).coeff n = 0 := by
    exact coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (natDegree_jensenPolynomial_le d alpha) (by lia))
  cases n with
  | zero =>
      simp [bidiagonalJensenPencil, halpha]
  | succ n =>
      have hbeta : (jensenPolynomial d beta).coeff n = 0 := by
        exact coeff_eq_zero_of_natDegree_lt
          (lt_of_le_of_lt (natDegree_jensenPolynomial_le d beta) (by lia))
      simp [bidiagonalJensenPencil, halpha, mul_assoc, hbeta]

/-- Small explicit PF certificate for a residual cubic.

For Family H, after the common `(1 + X)`-power is factored from the
Jensen-pencil, the remaining residual has degree at most three.  Nonnegative
coefficients plus a nonnegative cubic discriminant make this residual PF. -/
def CubicPFDiscriminantCertificate (p : ℝ[X]) : Prop :=
  HasNonnegCoeffs p ∧ p.natDegree ≤ 3 ∧ 0 ≤ cubicDiscr p

/-- Convert a cubic residual discriminant certificate to the PF predicate. -/
theorem isPFPolynomial_of_cubicPFDiscriminantCertificate
    {p : ℝ[X]} (hcert : CubicPFDiscriminantCertificate p) :
    IsPFPolynomial p :=
  IsPFPolynomial.of_realRooted_nonneg hcert.1 <|
    splits_of_natDegree_le_three_cubicDiscr_nonneg hcert.2.1 hcert.2.2

/-- Multiplication by a power of `1 + X` preserves the PF predicate. -/
theorem isPFPolynomial_X_add_one_pow_mul
    (m : ℕ) {p : ℝ[X]} (hp : IsPFPolynomial p) :
    IsPFPolynomial (((X + 1 : ℝ[X]) ^ m) * p) :=
  (isPFPolynomial_X_add_one.pow m).mul hp

/-- Finite Jensen-pencil certificate for a coefficient-bidiagonal PF backend.

The intended paper proof is:

1. certify that the whole nonnegative pencil
   `J_alpha,d + lambda * X * J_beta,d` is PF for `lambda >= 0`;
2. use the Schur--Szego/Garloff--Wagner proper-position theorem to transfer
   that finite pencil certificate to the operator
   `diagonal alpha + X * diagonal beta`.

This predicate records the concrete finite certificate, while the theorem
connecting it to `BidiagonalPFPreserver` remains a named backend statement. -/
def BidiagonalJensenPencilCertificate
    (alpha beta : ℕ → ℝ) (d : ℕ) : Prop :=
  IsPFPolynomial (jensenPolynomial d alpha) ∧
  IsPFPolynomial (X * jensenPolynomial d beta) ∧
  ∀ lam : ℝ, 0 ≤ lam →
    IsPFPolynomial (bidiagonalJensenPencil alpha beta d lam)

/-- Backend theorem statement: a valid finite Jensen-pencil certificate implies
that the corresponding coefficient-bidiagonal operator preserves PF
polynomials up to degree `d`. -/
def jensenPencilBidiagonalPreserverStatement : Prop :=
  ∀ {alpha beta : ℕ → ℝ} {d : ℕ},
    BidiagonalJensenPencilCertificate alpha beta d →
    BidiagonalPFPreserver alpha beta d

/-- Apply the named Jensen-pencil backend theorem. -/
theorem bidiagonalPFPreserver_of_jensenPencil
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    {alpha beta : ℕ → ℝ} {d : ℕ}
    (hcert : BidiagonalJensenPencilCertificate alpha beta d) :
    BidiagonalPFPreserver alpha beta d :=
  hbackend hcert

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
    _ = ((X + 1 : ℝ[X]) ^ m) * (A + C lam * B) := by
      ring

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
    (hcert : BidiagonalCubicResidualCertificate alpha beta d)
    (hbackend : jensenPencilBidiagonalPreserverStatement) :
    BidiagonalPFPreserver alpha beta d :=
  bidiagonalPFPreserver_of_jensenPencil hbackend hcert.toJensenPencilCertificate

/-- Apply a bundled cubic-residual certificate as a PF-bidiagonal preserver. -/
theorem bidiagonalPFPreserver_of_cubicResidualCertificate
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    {alpha beta : ℕ → ℝ} {d : ℕ}
    (hcert : BidiagonalCubicResidualCertificate alpha beta d) :
    BidiagonalPFPreserver alpha beta d :=
  hcert.toPFPreserver hbackend

/-- Compatibility name for notes and tactic scripts that speak about the
PF-bidiagonal backend as a theorem statement. -/
abbrev pfBidiagonalPreserverStatement
    (alpha beta : ℕ → ℝ) (d : ℕ) : Prop :=
  BidiagonalPFPreserver alpha beta d

/-- Apply a PF-bidiagonal preserver certificate to one polynomial. -/
theorem isPFPolynomial_bidiagonalOperator_of_preserver
    {alpha beta : ℕ → ℝ} {d : ℕ} {p : ℝ[X]}
    (hpres : BidiagonalPFPreserver alpha beta d)
    (hp : IsPFPolynomial p)
    (hdeg : p.natDegree ≤ d) :
    IsPFPolynomial (bidiagonalOperator alpha beta p) :=
  hpres hp hdeg

/-- Compatibility spelling for the first PF-bidiagonal scaffold. -/
theorem isPFPolynomial_bidiagonalOperator_of_classical
    {alpha beta : ℕ → ℝ} {d : ℕ} {p : ℝ[X]}
    (hpres : pfBidiagonalPreserverStatement alpha beta d)
    (hp : IsPFPolynomial p)
    (hdeg : p.natDegree ≤ d) :
    IsPFPolynomial (bidiagonalOperator alpha beta p) :=
  isPFPolynomial_bidiagonalOperator_of_preserver hpres hp hdeg

/-- Apply a Jensen-pencil backend certificate to one polynomial. -/
theorem isPFPolynomial_bidiagonalOperator_of_jensenPencil
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    {alpha beta : ℕ → ℝ} {d : ℕ} {p : ℝ[X]}
    (hcert : BidiagonalJensenPencilCertificate alpha beta d)
    (hp : IsPFPolynomial p)
    (hdeg : p.natDegree ≤ d) :
    IsPFPolynomial (bidiagonalOperator alpha beta p) :=
  isPFPolynomial_bidiagonalOperator_of_preserver
    (bidiagonalPFPreserver_of_jensenPencil hbackend hcert) hp hdeg

/-- Apply a bundled cubic-residual certificate to one coefficient-bidiagonal
operator. -/
theorem isPFPolynomial_bidiagonalOperator_of_cubicResidualCertificate
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    {alpha beta : ℕ → ℝ} {d : ℕ} {p : ℝ[X]}
    (hcert : BidiagonalCubicResidualCertificate alpha beta d)
    (hp : IsPFPolynomial p)
    (hdeg : p.natDegree ≤ d) :
    IsPFPolynomial (bidiagonalOperator alpha beta p) :=
  isPFPolynomial_bidiagonalOperator_of_preserver
    (hcert.toPFPreserver hbackend) hp hdeg

/-- Project splitting from a zero-aware PF certificate. -/
theorem splits_of_isPFPolynomial {p : ℝ[X]} (hp : IsPFPolynomial p) :
    p.Splits := by
  rcases hp.eq_zero_or_splits with rfl | hsplits
  · simp
  · exact hsplits

/-- Project one row from a PF sequence certificate. -/
theorem at_of_isPFPolynomial_sequence {P : Nat → ℝ[X]}
    (hP : ∀ n : Nat, IsPFPolynomial (P n)) (n : Nat) :
    IsPFPolynomial (P n) :=
  hP n

/-- Project row-wise coefficient nonnegativity from a PF sequence certificate. -/
theorem hasNonnegCoeffs_of_isPFPolynomial_sequence {P : Nat → ℝ[X]}
    (hP : ∀ n : Nat, IsPFPolynomial (P n)) :
    ∀ n : Nat, HasNonnegCoeffs (P n) :=
  fun n => (hP n).hasNonnegCoeffs

/-- Project row-wise zero-or-splitting from a PF sequence certificate. -/
theorem eq_zero_or_splits_of_isPFPolynomial_sequence {P : Nat → ℝ[X]}
    (hP : ∀ n : Nat, IsPFPolynomial (P n)) :
    ∀ n : Nat, P n = 0 ∨ (P n).Splits :=
  fun n => (hP n).eq_zero_or_splits

/-- Project row-wise splitting from a PF sequence certificate. -/
theorem splits_of_isPFPolynomial_sequence {P : Nat → ℝ[X]}
    (hP : ∀ n : Nat, IsPFPolynomial (P n)) :
    ∀ n : Nat, (P n).Splits :=
  fun n => splits_of_isPFPolynomial (hP n)

/-- Combine a PF sequence certificate with row-wise nonvanishing to obtain the
strict real-rootedness shape used by the scalar recurrence tactics. -/
theorem isRealRooted_of_isPFPolynomial_sequence {P : Nat → ℝ[X]}
    (hP : ∀ n : Nat, IsPFPolynomial (P n))
    (hne : ∀ n : Nat, P n ≠ 0) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  fun n => (hP n).ne_zero_and_splits (hne n)

/-- Sequence wrapper for first-order recurrences by coefficient-bidiagonal
PF-preserving operators. -/
theorem isPFPolynomial_of_bidiagonalOperator_sequence
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hpres : ∀ n : Nat, BidiagonalPFPreserver (alpha n) (beta n) (d n))
    (hrec : ∀ n : Nat,
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) := by
  intro n
  induction n with
  | zero =>
      exact hbase
  | succ n ih =>
      simpa [hrec n] using
        isPFPolynomial_bidiagonalOperator_of_preserver (hpres n) ih (hdeg n)

/-- Sequence wrapper for first-order recurrences whose PF-bidiagonal
certificate only starts from a cutoff row.  The finitely many rows before the
cutoff are supplied as base cases. -/
theorem isPFPolynomial_of_bidiagonalOperator_sequence_from
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, N ≤ n → (P n).natDegree ≤ d n)
    (hpres : ∀ n : Nat, N ≤ n → BidiagonalPFPreserver (alpha n) (beta n) (d n))
    (hrec : ∀ n : Nat, N ≤ n →
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) := by
  intro n
  exact Nat.strong_induction_on n fun n ih => by
    by_cases hn : n ≤ N
    · exact hbase n hn
    · cases n with
      | zero =>
          exact False.elim (hn (Nat.zero_le N))
      | succ m =>
          have hNm : N ≤ m := by lia
          have hPm : IsPFPolynomial (P m) := ih m (Nat.lt_succ_self m)
          simpa [hrec m hNm] using
            isPFPolynomial_bidiagonalOperator_of_preserver (hpres m hNm) hPm (hdeg m hNm)

/-- Sequence wrapper using per-row Jensen-pencil certificates. -/
theorem isPFPolynomial_of_bidiagonalOperator_sequence_of_jensenPencil
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat,
      BidiagonalJensenPencilCertificate (alpha n) (beta n) (d n))
    (hrec : ∀ n : Nat,
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_bidiagonalOperator_sequence hbase hdeg
    (fun n => bidiagonalPFPreserver_of_jensenPencil hbackend (hcert n)) hrec

/-- Tail-start sequence wrapper using per-row Jensen-pencil certificates. -/
theorem isPFPolynomial_of_bidiagonalOperator_sequence_of_jensenPencil_from
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, N ≤ n → (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat, N ≤ n →
      BidiagonalJensenPencilCertificate (alpha n) (beta n) (d n))
    (hrec : ∀ n : Nat, N ≤ n →
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_bidiagonalOperator_sequence_from N hbase hdeg
    (fun n hn => bidiagonalPFPreserver_of_jensenPencil hbackend (hcert n hn)) hrec

/-- Sequence wrapper using bundled cubic-residual certificates as row hints. -/
theorem isPFPolynomial_of_bidiagonalOperator_sequence_of_cubicResidualCertificate
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat,
      BidiagonalCubicResidualCertificate (alpha n) (beta n) (d n))
    (hrec : ∀ n : Nat,
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_bidiagonalOperator_sequence hbase hdeg
    (fun n => (hcert n).toPFPreserver hbackend) hrec

/-- Tail-start sequence wrapper using bundled cubic-residual certificates as
row hints. -/
theorem isPFPolynomial_of_bidiagonalOperator_sequence_of_cubicResidualCertificate_from
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, N ≤ n → (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat, N ≤ n →
      BidiagonalCubicResidualCertificate (alpha n) (beta n) (d n))
    (hrec : ∀ n : Nat, N ≤ n →
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_bidiagonalOperator_sequence_from N hbase hdeg
    (fun n hn => (hcert n hn).toPFPreserver hbackend) hrec

/-- Sequence wrapper for Family H-style second-derivative recurrences with an
explicit per-row PF-bidiagonal preserver.

This is the lightweight tactic surface: once a recurrence has been normalized
to the six-parameter differential form, a backend only has to prove the
coefficient-bidiagonal preserver for the corresponding `alpha` and `beta`
sequences. -/
theorem isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence
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
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_bidiagonalOperator_sequence hbase hdeg hpres
    (fun n => (hrec n).trans
      (secondDerivativeBidiagonalForm_eq_bidiagonalOperator
        (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)))

/-- Sequence wrapper for second-derivative recurrences whose preserver is
stated using named coefficient-bidiagonal functions. -/
theorem isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_norm
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
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_bidiagonalOperator_sequence hbase hdeg hpres
    (fun n => (hrec n).trans (hnorm n))

/-- Sequence wrapper for Family H-style second-derivative recurrences using
per-row Jensen-pencil certificates. -/
theorem isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_jensenPencil
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    {P : Nat → ℝ[X]} {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
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
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence hbase hdeg
    (fun n => bidiagonalPFPreserver_of_jensenPencil hbackend (hcert n)) hrec

/-- Tail-start second-derivative wrapper using per-row Jensen-pencil
certificates for the canonical coefficient functions. -/
theorem isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_jensenPencil_from
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    {P : Nat → ℝ[X]} {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
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
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_bidiagonalOperator_sequence_of_jensenPencil_from
    hbackend N hbase hdeg hcert
    (fun n hn => (hrec n hn).trans
      (secondDerivativeBidiagonalForm_eq_bidiagonalOperator
        (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)))

/-- Sequence wrapper for second-derivative recurrences whose Jensen
certificates are attached to named coefficient-bidiagonal functions. -/
theorem isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_jensenPencil_norm
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ}
    {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat, BidiagonalJensenPencilCertificate (alpha n) (beta n) (d n))
    (hnorm : ∀ n : Nat,
      secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n) =
        bidiagonalOperator (alpha n) (beta n) (P n))
    (hrec : ∀ n : Nat,
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_norm hbase hdeg
    (fun n => bidiagonalPFPreserver_of_jensenPencil hbackend (hcert n)) hnorm hrec

/-- Tail-start version of
`isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_jensenPencil_norm`. -/
theorem
    isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_jensenPencil_norm_from
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ}
    {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
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
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_bidiagonalOperator_sequence_of_jensenPencil_from
    hbackend N hbase hdeg hcert (fun n hn => (hrec n hn).trans (hnorm n hn))

/-- Sequence wrapper for second-derivative PF-bidiagonal recurrences using
bundled cubic-residual certificates as row hints. -/
theorem
    isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicResidualCertificate
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    {P : Nat → ℝ[X]} {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
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
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence hbase hdeg
    (fun n => (hcert n).toPFPreserver hbackend) hrec

/-- Short compatibility spelling for the bundled cubic-residual version of the
second-derivative PF-bidiagonal sequence wrapper. -/
theorem isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicCert
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    {P : Nat → ℝ[X]} {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
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
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicResidualCertificate
    hbackend hbase hdeg hcert hrec

/-- Tail-start version of
`isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicCert`.

This is the direct version for certificates attached to the canonical
quadratic coefficient functions of the second-derivative form. -/
theorem isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicCert_from
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    {P : Nat → ℝ[X]} {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
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
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_bidiagonalOperator_sequence_of_cubicResidualCertificate_from
    hbackend N hbase hdeg hcert
    (fun n hn => (hrec n hn).trans
      (secondDerivativeBidiagonalForm_eq_bidiagonalOperator
        (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)))

/-- Sequence wrapper for second-derivative recurrences whose certificate is
stated using named coefficient-bidiagonal functions.

This is useful for promoted sequence shells: the recurrence is often recorded
in differential form, while the generated Jensen/cubic certificate is attached
to named `alpha` and `beta` coefficient functions. -/
theorem
    isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicCert_norm
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ}
    {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat, BidiagonalCubicResidualCertificate (alpha n) (beta n) (d n))
    (hnorm : ∀ n : Nat,
      secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n) =
        bidiagonalOperator (alpha n) (beta n) (P n))
    (hrec : ∀ n : Nat,
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_bidiagonalOperator_sequence_of_cubicResidualCertificate
    hbackend hbase hdeg hcert (fun n => (hrec n).trans (hnorm n))

/-- Tail-start version of
`isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicCert_norm`.

This is useful for `n`-dependent coefficient-bidiagonal certificates whose
common Jensen factor only has the stable residual shape from a cutoff row
onward. -/
theorem
    isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicCert_norm_from
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ}
    {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, N ≤ n → (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat, N ≤ n →
      BidiagonalCubicResidualCertificate (alpha n) (beta n) (d n))
    (hnorm : ∀ n : Nat, N ≤ n →
      secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n) =
        bidiagonalOperator (alpha n) (beta n) (P n))
    (hrec : ∀ n : Nat, N ≤ n →
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_bidiagonalOperator_sequence_of_cubicResidualCertificate_from
    hbackend N hbase hdeg hcert (fun n hn => (hrec n hn).trans (hnorm n hn))

/-- Sequence wrapper whose per-row Jensen-pencil certificates are supplied by
common-factor residual cubic certificates. -/
theorem isPFPolynomial_of_bidiagonalOperator_sequence_of_cubicResidual
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ}
    {d m : Nat → ℕ} {A B : Nat → ℝ[X]} {S : Nat → ℝ → ℝ[X]}
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
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_bidiagonalOperator_sequence_of_cubicResidualCertificate
    hbackend hbase hdeg
    (fun n =>
      bidiagonalCubicResidualCertificate_of_cubicResidual
        (halpha n) (hbeta n) (hpencil n) (hA n) (hB n) (hS n))
    hrec

/-- Sequence wrapper whose residual pencil is derived from the endpoint
factorizations as `A n + C lam * B n`. -/
theorem isPFPolynomial_of_bidiagonalOperator_sequence_of_endpoint_cubicResidual
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ}
    {d m : Nat → ℕ} {A B : Nat → ℝ[X]}
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
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_bidiagonalOperator_sequence_of_cubicResidualCertificate
    hbackend hbase hdeg
    (fun n =>
      bidiagonalCubicResidualCertificate_of_endpoint_cubicResidual
        (halpha n) (hbeta n) (hA n) (hB n) (hS n))
    hrec

/-- Sequence wrapper for Family H-style second-derivative recurrences.

The recurrence is supplied in differential form using
`secondDerivativeBidiagonalForm`; this theorem normalizes it to
`bidiagonalOperator` and then applies the Jensen-pencil/cubic-residual PF
sequence wrapper. -/
theorem isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicResidual
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    {P : Nat → ℝ[X]} {a0 a1 b1 b2 c2 c3 : Nat → ℝ}
    {d m : Nat → ℕ} {A B : Nat → ℝ[X]} {S : Nat → ℝ → ℝ[X]}
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
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicCert
    hbackend hbase hdeg
    (fun n =>
      bidiagonalCubicResidualCertificate_of_cubicResidual
        (halpha n) (hbeta n) (hpencil n) (hA n) (hB n) (hS n))
    hrec

/-- Second-derivative sequence wrapper whose residual pencil is derived from
the endpoint factorizations as `A n + C lam * B n`. -/
theorem isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_endpoint_cubicResidual
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    {P : Nat → ℝ[X]} {a0 a1 b1 b2 c2 c3 : Nat → ℝ}
    {d m : Nat → ℕ} {A B : Nat → ℝ[X]}
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
    (hrec : ∀ n : Nat,
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicCert
    hbackend hbase hdeg
    (fun n =>
      bidiagonalCubicResidualCertificate_of_endpoint_cubicResidual
        (halpha n) (hbeta n) (hA n) (hB n) (hS n))
    hrec

/-- Sequence wrapper for second-derivative recurrences with unbundled
common-factor residual cubic certificates attached to named coefficient
bidiagonal functions. -/
theorem isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicResidual_norm
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ}
    {a0 a1 b1 b2 c2 c3 : Nat → ℝ}
    {d m : Nat → ℕ} {A B : Nat → ℝ[X]} {S : Nat → ℝ → ℝ[X]}
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
    (hnorm : ∀ n : Nat,
      secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n) =
        bidiagonalOperator (alpha n) (beta n) (P n))
    (hrec : ∀ n : Nat,
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicCert_norm
    hbackend hbase hdeg
    (fun n =>
      bidiagonalCubicResidualCertificate_of_cubicResidual
        (halpha n) (hbeta n) (hpencil n) (hA n) (hB n) (hS n))
    hnorm hrec

/-- Normalized second-derivative sequence wrapper whose residual pencil is
derived from the endpoint factorizations as `A n + C lam * B n`. -/
theorem isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_endpoint_cubicResidual_norm
    (hbackend : jensenPencilBidiagonalPreserverStatement)
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ}
    {a0 a1 b1 b2 c2 c3 : Nat → ℝ}
    {d m : Nat → ℕ} {A B : Nat → ℝ[X]}
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
    (hnorm : ∀ n : Nat,
      secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n) =
        bidiagonalOperator (alpha n) (beta n) (P n))
    (hrec : ∀ n : Nat,
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicCert_norm
    hbackend hbase hdeg
    (fun n =>
      bidiagonalCubicResidualCertificate_of_endpoint_cubicResidual
        (halpha n) (hbeta n) (hA n) (hB n) (hS n))
    hnorm hrec

namespace Tactic

syntax (name := rr_exact_pf_sequence_or_projection)
  "rr_exact_pf_sequence_or_projection" term :
  tactic

syntax (name := rr_exact_pf_sequence_realrooted)
  "rr_exact_pf_sequence_realrooted" term ", " term :
  tactic

syntax (name := rr_exact_pf_sequence)
  "rr_exact_pf_sequence" term ("," "nonzero" ":=" term)? :
  tactic

syntax (name := rr_second_derivative_bidiagonal_normalizer)
  "rr_second_derivative_bidiagonal_normalizer" " ["
    (Lean.Parser.Tactic.simpStar <|>
     Lean.Parser.Tactic.simpErase <|>
     Lean.Parser.Tactic.simpLemma),* "]" :
  tactic

syntax (name := rr_pf_bidiagonal_sequence_named)
  "rr_pf_bidiagonal_sequence" " using "
    "preserver" ":=" term ","
    ("cutoff" ":=" term ",")?
    "base" ":=" term ","
    "degree" ":=" term ","
    "recurrence" ":=" term
    ("," "nonzero" ":=" term)? :
  tactic

macro_rules
  | `(tactic| rr_exact_pf_sequence_or_projection $h:term) =>
      `(tactic|
        first
          | rr_first_exact
              $h,
              (RealRooted.at_of_isPFPolynomial_sequence $h _),
              RealRooted.hasNonnegCoeffs_of_isPFPolynomial_sequence $h,
              (RealRooted.hasNonnegCoeffs_of_isPFPolynomial_sequence $h _),
              RealRooted.splits_of_isPFPolynomial_sequence $h,
              (RealRooted.splits_of_isPFPolynomial_sequence $h _),
              RealRooted.eq_zero_or_splits_of_isPFPolynomial_sequence $h,
              (RealRooted.eq_zero_or_splits_of_isPFPolynomial_sequence $h _)
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_isPFPolynomial_sequence $h (by
                rr_lookup)))
  | `(tactic| rr_exact_pf_sequence_realrooted $h:term, $hne:term) =>
      `(tactic|
        first
          | rr_exact_pf_sequence_or_projection $h
          | rr_first_exact
              $hne,
              ($hne _)
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_isPFPolynomial_sequence $h $hne))
  | `(tactic| rr_exact_pf_sequence $h:term) =>
      `(tactic| rr_exact_pf_sequence_or_projection $h)
  | `(tactic| rr_exact_pf_sequence $h:term, nonzero := $hne:term) =>
      `(tactic| rr_exact_pf_sequence_realrooted $h, $hne)
  | `(tactic| rr_second_derivative_bidiagonal_normalizer [$defs,*]) =>
      `(tactic|
        refine RealRooted.secondDerivativeBidiagonalForm_eq_bidiagonalOperator_of_coeff_eq
          _ ?_ ?_ <;>
          intro k <;>
          simp [RealRooted.secondDerivativeQuadraticCoeff, $defs,*] <;>
          ring)
  | `(tactic|
      rr_pf_bidiagonal_sequence using
        preserver := $hPF:term,
        base := $hbase:term,
        degree := $hdeg:term,
        recurrence := $hrec:term
        $[, nonzero := $hne:term]?) =>
      `(tactic|
        rr_exact_pf_sequence
          (RealRooted.isPFPolynomial_of_bidiagonalOperator_sequence
            $hbase $hdeg $hPF $hrec)
          $[, nonzero := $hne]?)
  | `(tactic|
      rr_pf_bidiagonal_sequence using
        preserver := $hPF:term,
        cutoff := $N:term,
        base := $hbase:term,
        degree := $hdeg:term,
        recurrence := $hrec:term
        $[, nonzero := $hne:term]?) =>
      `(tactic|
        rr_exact_pf_sequence
          (RealRooted.isPFPolynomial_of_bidiagonalOperator_sequence_from
            $N $hbase $hdeg $hPF $hrec)
          $[, nonzero := $hne]?)

syntax (name := rr_pf_bidiagonal_certificate_cubic_named)
  "rr_pf_bidiagonal_certificate" " using "
    "alpha_factor" ":=" term ","
    "beta_factor" ":=" term ","
    ("pencil_factor" ":=" term ",")?
    "alpha_cubic" ":=" term ","
    "beta_cubic" ":=" term ","
    "pencil_cubic" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_pf_bidiagonal_certificate using
        alpha_factor := $halpha:term,
        beta_factor := $hbeta:term,
        pencil_factor := $hpencil:term,
        alpha_cubic := $hA:term,
        beta_cubic := $hB:term,
        pencil_cubic := $hS:term) =>
      `(tactic|
        exact RealRooted.bidiagonalJensenPencilCertificate_of_cubicResidual
          $halpha $hbeta $hpencil $hA $hB $hS)

macro_rules
  | `(tactic|
      rr_pf_bidiagonal_certificate using
        alpha_factor := $halpha:term,
        beta_factor := $hbeta:term,
        alpha_cubic := $hA:term,
        beta_cubic := $hB:term,
        pencil_cubic := $hS:term) =>
      `(tactic|
        exact RealRooted.bidiagonalJensenPencilCertificate_of_endpoint_cubicResidual
          $halpha $hbeta $hA $hB $hS)

syntax (name := rr_pf_bidiagonal_cubic_certificate_named)
  "rr_pf_bidiagonal_cubic_certificate" " using "
    "alpha_factor" ":=" term ","
    "beta_factor" ":=" term ","
    ("pencil_factor" ":=" term ",")?
    "alpha_cubic" ":=" term ","
    "beta_cubic" ":=" term ","
    "pencil_cubic" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_pf_bidiagonal_cubic_certificate using
        alpha_factor := $halpha:term,
        beta_factor := $hbeta:term,
        pencil_factor := $hpencil:term,
        alpha_cubic := $hA:term,
        beta_cubic := $hB:term,
        pencil_cubic := $hS:term) =>
      `(tactic|
        exact RealRooted.bidiagonalCubicResidualCertificate_of_cubicResidual
          $halpha $hbeta $hpencil $hA $hB $hS)

macro_rules
  | `(tactic|
      rr_pf_bidiagonal_cubic_certificate using
        alpha_factor := $halpha:term,
        beta_factor := $hbeta:term,
        alpha_cubic := $hA:term,
        beta_cubic := $hB:term,
        pencil_cubic := $hS:term) =>
      `(tactic|
        exact RealRooted.bidiagonalCubicResidualCertificate_of_endpoint_cubicResidual
          $halpha $hbeta $hA $hB $hS)

syntax (name := rr_pf_bidiagonal_preserver_named)
  "rr_pf_bidiagonal_preserver" " using "
    "jensen_backend" ":=" term ","
    "certificate" ":=" term :
  tactic

syntax (name := rr_pf_bidiagonal_preserver_cubic_named)
  "rr_pf_bidiagonal_preserver_cubic" " using "
    "jensen_backend" ":=" term ","
    "cubic_certificate" ":=" term :
  tactic

syntax (name := rr_pf_bidiagonal_operator_named)
  "rr_pf_bidiagonal_operator" " using "
    "jensen_backend" ":=" term ","
    "certificate" ":=" term ","
    "input_pf" ":=" term ","
    "degree" ":=" term :
  tactic

syntax (name := rr_pf_bidiagonal_operator_cubic_named)
  "rr_pf_bidiagonal_operator_cubic" " using "
    "jensen_backend" ":=" term ","
    "cubic_certificate" ":=" term ","
    "input_pf" ":=" term ","
    "degree" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_pf_bidiagonal_preserver using
        jensen_backend := $hbackend:term,
        certificate := $hcert:term) =>
      `(tactic|
        exact RealRooted.bidiagonalPFPreserver_of_jensenPencil $hbackend $hcert)
  | `(tactic|
      rr_pf_bidiagonal_preserver_cubic using
        jensen_backend := $hbackend:term,
        cubic_certificate := $hcert:term) =>
      `(tactic|
        exact RealRooted.bidiagonalPFPreserver_of_cubicResidualCertificate
          $hbackend $hcert)
  | `(tactic|
      rr_pf_bidiagonal_operator using
        jensen_backend := $hbackend:term,
        certificate := $hcert:term,
        input_pf := $hp:term,
        degree := $hdeg:term) =>
      `(tactic|
        exact RealRooted.isPFPolynomial_bidiagonalOperator_of_jensenPencil
          $hbackend $hcert $hp $hdeg)
  | `(tactic|
      rr_pf_bidiagonal_operator_cubic using
        jensen_backend := $hbackend:term,
        cubic_certificate := $hcert:term,
        input_pf := $hp:term,
        degree := $hdeg:term) =>
      `(tactic|
        exact RealRooted.isPFPolynomial_bidiagonalOperator_of_cubicResidualCertificate
          $hbackend $hcert $hp $hdeg)

syntax (name := rr_pf_bidiagonal_sequence_cubic_named)
  "rr_pf_bidiagonal_sequence_cubic" " using "
    "jensen_backend" ":=" term ","
    "base" ":=" term ","
    "degree" ":=" term ","
    "alpha_factor" ":=" term ","
    "beta_factor" ":=" term ","
    ("pencil_factor" ":=" term ",")?
    "alpha_cubic" ":=" term ","
    "beta_cubic" ":=" term ","
    "pencil_cubic" ":=" term ","
    "recurrence" ":=" term
    ("," "nonzero" ":=" term)? :
  tactic

macro_rules
  | `(tactic|
      rr_pf_bidiagonal_sequence_cubic using
        jensen_backend := $hbackend:term,
        base := $hbase:term,
        degree := $hdeg:term,
        alpha_factor := $halpha:term,
        beta_factor := $hbeta:term,
        pencil_factor := $hpencil:term,
        alpha_cubic := $hA:term,
        beta_cubic := $hB:term,
        pencil_cubic := $hS:term,
        recurrence := $hrec:term
        $[, nonzero := $hne:term]?) =>
      `(tactic|
        rr_exact_pf_sequence
          (RealRooted.isPFPolynomial_of_bidiagonalOperator_sequence_of_cubicResidual
            $hbackend $hbase $hdeg $halpha $hbeta $hpencil $hA $hB $hS $hrec)
          $[, nonzero := $hne]?)

macro_rules
  | `(tactic|
      rr_pf_bidiagonal_sequence_cubic using
        jensen_backend := $hbackend:term,
        base := $hbase:term,
        degree := $hdeg:term,
        alpha_factor := $halpha:term,
        beta_factor := $hbeta:term,
        alpha_cubic := $hA:term,
        beta_cubic := $hB:term,
        pencil_cubic := $hS:term,
        recurrence := $hrec:term
        $[, nonzero := $hne:term]?) =>
      `(tactic|
        rr_exact_pf_sequence
          (RealRooted.isPFPolynomial_of_bidiagonalOperator_sequence_of_endpoint_cubicResidual
            $hbackend $hbase $hdeg $halpha $hbeta $hA $hB $hS $hrec)
          $[, nonzero := $hne]?)

syntax (name := rr_pf_second_derivative_bidiagonal_sequence_cubic_named)
  "rr_pf_second_derivative_bidiagonal_sequence_cubic" " using "
    "jensen_backend" ":=" term ","
    "base" ":=" term ","
    "degree" ":=" term ","
    "alpha_factor" ":=" term ","
    "beta_factor" ":=" term ","
    ("pencil_factor" ":=" term ",")?
    "alpha_cubic" ":=" term ","
    "beta_cubic" ":=" term ","
    "pencil_cubic" ":=" term ","
    "recurrence" ":=" term
    ("," "nonzero" ":=" term)? :
  tactic

macro_rules
  | `(tactic|
      rr_pf_second_derivative_bidiagonal_sequence_cubic using
        jensen_backend := $hbackend:term,
        base := $hbase:term,
        degree := $hdeg:term,
        alpha_factor := $halpha:term,
        beta_factor := $hbeta:term,
        pencil_factor := $hpencil:term,
        alpha_cubic := $hA:term,
        beta_cubic := $hB:term,
        pencil_cubic := $hS:term,
        recurrence := $hrec:term
        $[, nonzero := $hne:term]?) =>
      `(tactic|
        rr_exact_pf_sequence
          (RealRooted.isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicResidual
            $hbackend $hbase $hdeg $halpha $hbeta $hpencil $hA $hB $hS $hrec)
          $[, nonzero := $hne]?)

macro_rules
  | `(tactic|
      rr_pf_second_derivative_bidiagonal_sequence_cubic using
        jensen_backend := $hbackend:term,
        base := $hbase:term,
        degree := $hdeg:term,
        alpha_factor := $halpha:term,
        beta_factor := $hbeta:term,
        alpha_cubic := $hA:term,
        beta_cubic := $hB:term,
        pencil_cubic := $hS:term,
        recurrence := $hrec:term
        $[, nonzero := $hne:term]?) =>
      `(tactic|
        rr_exact_pf_sequence
          (isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_endpoint_cubicResidual
            $hbackend $hbase $hdeg $halpha $hbeta $hA $hB $hS $hrec)
          $[, nonzero := $hne]?)

syntax (name := rr_pf_second_derivative_bidiagonal_sequence_cubic_normalized_named)
  "rr_pf_second_derivative_bidiagonal_sequence_cubic" " using "
    "jensen_backend" ":=" term ","
    "base" ":=" term ","
    "degree" ":=" term ","
    "alpha_factor" ":=" term ","
    "beta_factor" ":=" term ","
    ("pencil_factor" ":=" term ",")?
    "alpha_cubic" ":=" term ","
    "beta_cubic" ":=" term ","
    "pencil_cubic" ":=" term ","
    "normalizer" ":=" term ","
    "recurrence" ":=" term
    ("," "nonzero" ":=" term)? :
  tactic

macro_rules
  | `(tactic|
      rr_pf_second_derivative_bidiagonal_sequence_cubic using
        jensen_backend := $hbackend:term,
        base := $hbase:term,
        degree := $hdeg:term,
        alpha_factor := $halpha:term,
        beta_factor := $hbeta:term,
        pencil_factor := $hpencil:term,
        alpha_cubic := $hA:term,
        beta_cubic := $hB:term,
        pencil_cubic := $hS:term,
        normalizer := $hnorm:term,
        recurrence := $hrec:term
        $[, nonzero := $hne:term]?) =>
      `(tactic|
        rr_exact_pf_sequence
          (isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicResidual_norm
            $hbackend $hbase $hdeg $halpha $hbeta $hpencil $hA $hB $hS $hnorm
            $hrec)
          $[, nonzero := $hne]?)

macro_rules
  | `(tactic|
      rr_pf_second_derivative_bidiagonal_sequence_cubic using
        jensen_backend := $hbackend:term,
        base := $hbase:term,
        degree := $hdeg:term,
        alpha_factor := $halpha:term,
        beta_factor := $hbeta:term,
        alpha_cubic := $hA:term,
        beta_cubic := $hB:term,
        pencil_cubic := $hS:term,
        normalizer := $hnorm:term,
        recurrence := $hrec:term
        $[, nonzero := $hne:term]?) =>
      `(tactic|
        rr_exact_pf_sequence
          (isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_endpoint_cubicResidual_norm
            $hbackend $hbase $hdeg $halpha $hbeta $hA $hB $hS $hnorm $hrec)
          $[, nonzero := $hne]?)

syntax (name := rr_pf_bidiagonal_sequence_jensen_named)
  "rr_pf_bidiagonal_sequence" " using "
    "jensen_backend" ":=" term ","
    "certificate" ":=" term ","
    ("cutoff" ":=" term ",")?
    "base" ":=" term ","
    "degree" ":=" term ","
    "recurrence" ":=" term
    ("," "nonzero" ":=" term)? :
  tactic

macro_rules
  | `(tactic|
      rr_pf_bidiagonal_sequence using
        jensen_backend := $hbackend:term,
        certificate := $hcert:term,
        base := $hbase:term,
        degree := $hdeg:term,
        recurrence := $hrec:term
        $[, nonzero := $hne:term]?) =>
      `(tactic|
        rr_exact_pf_sequence
          (RealRooted.isPFPolynomial_of_bidiagonalOperator_sequence_of_jensenPencil
            $hbackend $hbase $hdeg $hcert $hrec)
          $[, nonzero := $hne]?)
  | `(tactic|
      rr_pf_bidiagonal_sequence using
        jensen_backend := $hbackend:term,
        certificate := $hcert:term,
        cutoff := $N:term,
        base := $hbase:term,
        degree := $hdeg:term,
        recurrence := $hrec:term
        $[, nonzero := $hne:term]?) =>
      `(tactic|
        rr_exact_pf_sequence
          (RealRooted.isPFPolynomial_of_bidiagonalOperator_sequence_of_jensenPencil_from
            $hbackend $N $hbase $hdeg $hcert $hrec)
          $[, nonzero := $hne]?)

syntax (name := rr_pf_bidiagonal_sequence_cubic_certificate_named)
  "rr_pf_bidiagonal_sequence" " using "
    "jensen_backend" ":=" term ","
    "cubic_certificate" ":=" term ","
    ("cutoff" ":=" term ",")?
    "base" ":=" term ","
    "degree" ":=" term ","
    "recurrence" ":=" term
    ("," "nonzero" ":=" term)? :
  tactic

macro_rules
  | `(tactic|
      rr_pf_bidiagonal_sequence using
        jensen_backend := $hbackend:term,
        cubic_certificate := $hcert:term,
        base := $hbase:term,
        degree := $hdeg:term,
        recurrence := $hrec:term
        $[, nonzero := $hne:term]?) =>
      `(tactic|
        rr_exact_pf_sequence
          (RealRooted.isPFPolynomial_of_bidiagonalOperator_sequence_of_cubicResidualCertificate
            $hbackend $hbase $hdeg $hcert $hrec)
          $[, nonzero := $hne]?)
  | `(tactic|
      rr_pf_bidiagonal_sequence using
        jensen_backend := $hbackend:term,
        cubic_certificate := $hcert:term,
        cutoff := $N:term,
        base := $hbase:term,
        degree := $hdeg:term,
        recurrence := $hrec:term
        $[, nonzero := $hne:term]?) =>
      `(tactic|
        rr_exact_pf_sequence
          (RealRooted.isPFPolynomial_of_bidiagonalOperator_sequence_of_cubicResidualCertificate_from
            $hbackend $N $hbase $hdeg $hcert $hrec)
          $[, nonzero := $hne]?)

syntax (name := rr_pf_second_derivative_bidiagonal_sequence_named)
  "rr_pf_second_derivative_bidiagonal_sequence" " using "
    "preserver" ":=" term ","
    "base" ":=" term ","
    "degree" ":=" term ","
    "recurrence" ":=" term
    ("," "nonzero" ":=" term)? :
  tactic

macro_rules
  | `(tactic|
      rr_pf_second_derivative_bidiagonal_sequence using
        preserver := $hPF:term,
        base := $hbase:term,
        degree := $hdeg:term,
        recurrence := $hrec:term
        $[, nonzero := $hne:term]?) =>
      `(tactic|
        rr_exact_pf_sequence
          (RealRooted.isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence
            $hbase $hdeg $hPF $hrec)
          $[, nonzero := $hne]?)

syntax (name := rr_pf_second_derivative_bidiagonal_sequence_preserver_normalized_named)
  "rr_pf_second_derivative_bidiagonal_sequence" " using "
    "preserver" ":=" term ","
    "base" ":=" term ","
    "degree" ":=" term ","
    "normalizer" ":=" term ","
    "recurrence" ":=" term
    ("," "nonzero" ":=" term)? :
  tactic

macro_rules
  | `(tactic|
      rr_pf_second_derivative_bidiagonal_sequence using
        preserver := $hPF:term,
        base := $hbase:term,
        degree := $hdeg:term,
        normalizer := $hnorm:term,
        recurrence := $hrec:term
        $[, nonzero := $hne:term]?) =>
      `(tactic|
        rr_exact_pf_sequence
          (RealRooted.isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_norm
            $hbase $hdeg $hPF $hnorm $hrec)
          $[, nonzero := $hne]?)

syntax (name := rr_pf_second_derivative_bidiagonal_sequence_jensen_named)
  "rr_pf_second_derivative_bidiagonal_sequence" " using "
    "jensen_backend" ":=" term ","
    "certificate" ":=" term ","
    ("cutoff" ":=" term ",")?
    "base" ":=" term ","
    "degree" ":=" term ","
    "recurrence" ":=" term
    ("," "nonzero" ":=" term)? :
  tactic

macro_rules
  | `(tactic|
      rr_pf_second_derivative_bidiagonal_sequence using
        jensen_backend := $hbackend:term,
        certificate := $hcert:term,
        base := $hbase:term,
        degree := $hdeg:term,
        recurrence := $hrec:term
        $[, nonzero := $hne:term]?) =>
      `(tactic|
        rr_exact_pf_sequence
          (RealRooted.isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_jensenPencil
            $hbackend $hbase $hdeg $hcert $hrec)
          $[, nonzero := $hne]?)
  | `(tactic|
      rr_pf_second_derivative_bidiagonal_sequence using
        jensen_backend := $hbackend:term,
        certificate := $hcert:term,
        cutoff := $N:term,
        base := $hbase:term,
        degree := $hdeg:term,
        recurrence := $hrec:term
        $[, nonzero := $hne:term]?) =>
      `(tactic|
        rr_exact_pf_sequence
          (isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_jensenPencil_from
            $hbackend $N $hbase $hdeg $hcert $hrec)
          $[, nonzero := $hne]?)

syntax (name := rr_pf_second_derivative_bidiagonal_sequence_jensen_normalized_named)
  "rr_pf_second_derivative_bidiagonal_sequence" " using "
    "jensen_backend" ":=" term ","
    "certificate" ":=" term ","
    ("cutoff" ":=" term ",")?
    "base" ":=" term ","
    "degree" ":=" term ","
    "normalizer" ":=" term ","
    "recurrence" ":=" term
    ("," "nonzero" ":=" term)? :
  tactic

macro_rules
  | `(tactic|
      rr_pf_second_derivative_bidiagonal_sequence using
        jensen_backend := $hbackend:term,
        certificate := $hcert:term,
        base := $hbase:term,
        degree := $hdeg:term,
        normalizer := $hnorm:term,
        recurrence := $hrec:term
        $[, nonzero := $hne:term]?) =>
      `(tactic|
        rr_exact_pf_sequence
          (RealRooted.isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_jensenPencil_norm
            $hbackend $hbase $hdeg $hcert $hnorm $hrec)
          $[, nonzero := $hne]?)
  | `(tactic|
      rr_pf_second_derivative_bidiagonal_sequence using
        jensen_backend := $hbackend:term,
        certificate := $hcert:term,
        cutoff := $N:term,
        base := $hbase:term,
        degree := $hdeg:term,
        normalizer := $hnorm:term,
        recurrence := $hrec:term
        $[, nonzero := $hne:term]?) =>
      `(tactic|
        rr_exact_pf_sequence
          (isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_jensenPencil_norm_from
            $hbackend $N $hbase $hdeg $hcert $hnorm $hrec)
          $[, nonzero := $hne]?)

syntax (name := rr_pf_second_derivative_bidiagonal_sequence_cubic_certificate_named)
  "rr_pf_second_derivative_bidiagonal_sequence" " using "
    "jensen_backend" ":=" term ","
    "cubic_certificate" ":=" term ","
    ("cutoff" ":=" term ",")?
    "base" ":=" term ","
    "degree" ":=" term ","
    "recurrence" ":=" term
    ("," "nonzero" ":=" term)? :
  tactic

macro_rules
  | `(tactic|
      rr_pf_second_derivative_bidiagonal_sequence using
        jensen_backend := $hbackend:term,
        cubic_certificate := $hcert:term,
        base := $hbase:term,
        degree := $hdeg:term,
        recurrence := $hrec:term
        $[, nonzero := $hne:term]?) =>
      `(tactic|
        rr_exact_pf_sequence
          (RealRooted.isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicCert
            $hbackend $hbase $hdeg $hcert $hrec)
          $[, nonzero := $hne]?)
  | `(tactic|
      rr_pf_second_derivative_bidiagonal_sequence using
        jensen_backend := $hbackend:term,
        cubic_certificate := $hcert:term,
        cutoff := $N:term,
        base := $hbase:term,
        degree := $hdeg:term,
        recurrence := $hrec:term
        $[, nonzero := $hne:term]?) =>
      `(tactic|
        rr_exact_pf_sequence
          (isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicCert_from
            $hbackend $N $hbase $hdeg $hcert $hrec)
          $[, nonzero := $hne]?)

syntax (name := rr_pf_second_derivative_bidiagonal_sequence_cubic_certificate_normalized_named)
  "rr_pf_second_derivative_bidiagonal_sequence" " using "
    "jensen_backend" ":=" term ","
    "cubic_certificate" ":=" term ","
    ("cutoff" ":=" term ",")?
    "base" ":=" term ","
    "degree" ":=" term ","
    "normalizer" ":=" term ","
    "recurrence" ":=" term
    ("," "nonzero" ":=" term)? :
  tactic

macro_rules
  | `(tactic|
      rr_pf_second_derivative_bidiagonal_sequence using
        jensen_backend := $hbackend:term,
        cubic_certificate := $hcert:term,
        base := $hbase:term,
        degree := $hdeg:term,
        normalizer := $hnorm:term,
        recurrence := $hrec:term
        $[, nonzero := $hne:term]?) =>
      `(tactic|
        rr_exact_pf_sequence
          (RealRooted.isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicCert_norm
            $hbackend $hbase $hdeg $hcert $hnorm $hrec)
          $[, nonzero := $hne]?)
  | `(tactic|
      rr_pf_second_derivative_bidiagonal_sequence using
        jensen_backend := $hbackend:term,
        cubic_certificate := $hcert:term,
        cutoff := $N:term,
        base := $hbase:term,
        degree := $hdeg:term,
        normalizer := $hnorm:term,
        recurrence := $hrec:term
        $[, nonzero := $hne:term]?) =>
      `(tactic|
        rr_exact_pf_sequence
          (isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicCert_norm_from
            $hbackend $N $hbase $hdeg $hcert $hnorm $hrec)
          $[, nonzero := $hne]?)

/-- Family-H second-derivative router for the known PF-bidiagonal route with a
bundled cubic-residual Jensen-pencil certificate. -/
syntax (name := rr_h_second_derivative_sequence_pf_bidiagonal_cubic)
  "rr_h_second_derivative_sequence" " using "
    "route" ":=" "pf_bidiagonal" ","
    "jensen_backend" ":=" term ","
    "cubic_certificate" ":=" term ","
    ("cutoff" ":=" term ",")?
    "base" ":=" term ","
    "degree" ":=" term ","
    ("normalizer" ":=" term ",")?
    "recurrence" ":=" term
    ("," "nonzero" ":=" term)? :
  tactic

macro_rules
  | `(tactic|
      rr_h_second_derivative_sequence using
        route := pf_bidiagonal,
        jensen_backend := $hbackend:term,
        cubic_certificate := $hcert:term,
        base := $hbase:term,
        degree := $hdeg:term,
        recurrence := $hrec:term
        $[, nonzero := $hne:term]?) =>
      `(tactic|
        rr_pf_second_derivative_bidiagonal_sequence using
          jensen_backend := $hbackend,
          cubic_certificate := $hcert,
          base := $hbase,
          degree := $hdeg,
          recurrence := $hrec
          $[, nonzero := $hne]?)
  | `(tactic|
      rr_h_second_derivative_sequence using
        route := pf_bidiagonal,
        jensen_backend := $hbackend:term,
        cubic_certificate := $hcert:term,
        cutoff := $N:term,
        base := $hbase:term,
        degree := $hdeg:term,
        recurrence := $hrec:term
        $[, nonzero := $hne:term]?) =>
      `(tactic|
        rr_pf_second_derivative_bidiagonal_sequence using
          jensen_backend := $hbackend,
          cubic_certificate := $hcert,
          cutoff := $N,
          base := $hbase,
          degree := $hdeg,
          recurrence := $hrec
          $[, nonzero := $hne]?)
  | `(tactic|
      rr_h_second_derivative_sequence using
        route := pf_bidiagonal,
        jensen_backend := $hbackend:term,
        cubic_certificate := $hcert:term,
        base := $hbase:term,
        degree := $hdeg:term,
        normalizer := $hnorm:term,
        recurrence := $hrec:term
        $[, nonzero := $hne:term]?) =>
      `(tactic|
        rr_pf_second_derivative_bidiagonal_sequence using
          jensen_backend := $hbackend,
          cubic_certificate := $hcert,
          base := $hbase,
          degree := $hdeg,
          normalizer := $hnorm,
          recurrence := $hrec
          $[, nonzero := $hne]?)
  | `(tactic|
      rr_h_second_derivative_sequence using
        route := pf_bidiagonal,
        jensen_backend := $hbackend:term,
        cubic_certificate := $hcert:term,
        cutoff := $N:term,
        base := $hbase:term,
        degree := $hdeg:term,
        normalizer := $hnorm:term,
        recurrence := $hrec:term
        $[, nonzero := $hne:term]?) =>
      `(tactic|
        rr_pf_second_derivative_bidiagonal_sequence using
          jensen_backend := $hbackend,
          cubic_certificate := $hcert,
          cutoff := $N,
          base := $hbase,
          degree := $hdeg,
          normalizer := $hnorm,
          recurrence := $hrec
          $[, nonzero := $hne]?)

end Tactic

end RealRooted
