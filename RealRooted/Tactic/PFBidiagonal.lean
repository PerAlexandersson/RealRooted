import RealRooted.MultiplierSequence

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

/-- Forget a bundled cubic-residual certificate to the Jensen-pencil
certificate used by the PF-bidiagonal backend. -/
theorem BidiagonalCubicResidualCertificate.toJensenPencilCertificate
    {alpha beta : ℕ → ℝ} {d : ℕ}
    (hcert : BidiagonalCubicResidualCertificate alpha beta d) :
    BidiagonalJensenPencilCertificate alpha beta d :=
  bidiagonalJensenPencilCertificate_of_cubicResidual
    hcert.alpha_factor hcert.beta_factor hcert.pencil_factor
    hcert.alpha_cubic hcert.beta_cubic hcert.pencil_cubic

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
  isPFPolynomial_of_bidiagonalOperator_sequence_of_jensenPencil
    hbackend hbase hdeg
    (fun n => (hcert n).toJensenPencilCertificate) hrec

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
    (fun n =>
      calc
        P (n + 1) =
            secondDerivativeBidiagonalForm
              (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n) := hrec n
        _ =
            bidiagonalOperator
              (fun k => secondDerivativeQuadraticCoeff (a0 n) (b1 n) (c2 n) k)
              (fun k => secondDerivativeQuadraticCoeff (a1 n) (b2 n) (c3 n) k)
              (P n) :=
            secondDerivativeBidiagonalForm_eq_bidiagonalOperator
              (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n))

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
  isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_jensenPencil
    hbackend hbase hdeg
    (fun n => (hcert n).toJensenPencilCertificate) hrec

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
  isPFPolynomial_of_bidiagonalOperator_sequence_of_jensenPencil
    hbackend hbase hdeg
    (fun n =>
      bidiagonalJensenPencilCertificate_of_cubicResidual
        (halpha n) (hbeta n) (hpencil n) (hA n) (hB n) (hS n))
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
  isPFPolynomial_of_bidiagonalOperator_sequence_of_cubicResidual
    hbackend hbase hdeg halpha hbeta hpencil hA hB hS
    (fun n =>
      calc
        P (n + 1) =
            secondDerivativeBidiagonalForm
              (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n) := hrec n
        _ =
            bidiagonalOperator
              (fun k => secondDerivativeQuadraticCoeff (a0 n) (b1 n) (c2 n) k)
              (fun k => secondDerivativeQuadraticCoeff (a1 n) (b2 n) (c3 n) k)
              (P n) :=
            secondDerivativeBidiagonalForm_eq_bidiagonalOperator
              (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n))

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
  isPFPolynomial_of_bidiagonalOperator_sequence_of_cubicResidual
    hbackend hbase hdeg halpha hbeta hpencil hA hB hS
    (fun n => (hrec n).trans (hnorm n))

namespace Tactic

syntax (name := rr_pf_bidiagonal_sequence_named)
  "rr_pf_bidiagonal_sequence" " using "
    "preserver" ":=" term ","
    "base" ":=" term ","
    "degree" ":=" term ","
    "recurrence" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_pf_bidiagonal_sequence using
        preserver := $hPF:term,
        base := $hbase:term,
        degree := $hdeg:term,
        recurrence := $hrec:term) =>
      `(tactic|
        exact RealRooted.isPFPolynomial_of_bidiagonalOperator_sequence
          $hbase $hdeg $hPF $hrec)

syntax (name := rr_pf_bidiagonal_certificate_cubic_named)
  "rr_pf_bidiagonal_certificate" " using "
    "alpha_factor" ":=" term ","
    "beta_factor" ":=" term ","
    "pencil_factor" ":=" term ","
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

syntax (name := rr_pf_bidiagonal_sequence_cubic_named)
  "rr_pf_bidiagonal_sequence_cubic" " using "
    "jensen_backend" ":=" term ","
    "base" ":=" term ","
    "degree" ":=" term ","
    "alpha_factor" ":=" term ","
    "beta_factor" ":=" term ","
    "pencil_factor" ":=" term ","
    "alpha_cubic" ":=" term ","
    "beta_cubic" ":=" term ","
    "pencil_cubic" ":=" term ","
    "recurrence" ":=" term :
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
        recurrence := $hrec:term) =>
      `(tactic|
        exact RealRooted.isPFPolynomial_of_bidiagonalOperator_sequence_of_cubicResidual
          $hbackend $hbase $hdeg $halpha $hbeta $hpencil $hA $hB $hS $hrec)

syntax (name := rr_pf_second_derivative_bidiagonal_sequence_cubic_named)
  "rr_pf_second_derivative_bidiagonal_sequence_cubic" " using "
    "jensen_backend" ":=" term ","
    "base" ":=" term ","
    "degree" ":=" term ","
    "alpha_factor" ":=" term ","
    "beta_factor" ":=" term ","
    "pencil_factor" ":=" term ","
    "alpha_cubic" ":=" term ","
    "beta_cubic" ":=" term ","
    "pencil_cubic" ":=" term ","
    "recurrence" ":=" term :
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
        recurrence := $hrec:term) =>
      `(tactic|
        exact
          RealRooted.isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicResidual
            $hbackend $hbase $hdeg $halpha $hbeta $hpencil $hA $hB $hS $hrec)

syntax (name := rr_pf_second_derivative_bidiagonal_sequence_cubic_normalized_named)
  "rr_pf_second_derivative_bidiagonal_sequence_cubic" " using "
    "jensen_backend" ":=" term ","
    "base" ":=" term ","
    "degree" ":=" term ","
    "alpha_factor" ":=" term ","
    "beta_factor" ":=" term ","
    "pencil_factor" ":=" term ","
    "alpha_cubic" ":=" term ","
    "beta_cubic" ":=" term ","
    "pencil_cubic" ":=" term ","
    "normalizer" ":=" term ","
    "recurrence" ":=" term :
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
        recurrence := $hrec:term) =>
      `(tactic|
        exact
          RealRooted.isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicResidual_norm
            $hbackend $hbase $hdeg $halpha $hbeta $hpencil $hA $hB $hS $hnorm
            $hrec)

syntax (name := rr_pf_bidiagonal_sequence_jensen_named)
  "rr_pf_bidiagonal_sequence" " using "
    "jensen_backend" ":=" term ","
    "certificate" ":=" term ","
    "base" ":=" term ","
    "degree" ":=" term ","
    "recurrence" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_pf_bidiagonal_sequence using
        jensen_backend := $hbackend:term,
        certificate := $hcert:term,
        base := $hbase:term,
        degree := $hdeg:term,
        recurrence := $hrec:term) =>
      `(tactic|
        exact RealRooted.isPFPolynomial_of_bidiagonalOperator_sequence_of_jensenPencil
          $hbackend $hbase $hdeg $hcert $hrec)

syntax (name := rr_pf_bidiagonal_sequence_cubic_certificate_named)
  "rr_pf_bidiagonal_sequence" " using "
    "jensen_backend" ":=" term ","
    "cubic_certificate" ":=" term ","
    "base" ":=" term ","
    "degree" ":=" term ","
    "recurrence" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_pf_bidiagonal_sequence using
        jensen_backend := $hbackend:term,
        cubic_certificate := $hcert:term,
        base := $hbase:term,
        degree := $hdeg:term,
        recurrence := $hrec:term) =>
      `(tactic|
        exact
          RealRooted.isPFPolynomial_of_bidiagonalOperator_sequence_of_cubicResidualCertificate
            $hbackend $hbase $hdeg $hcert $hrec)

syntax (name := rr_pf_second_derivative_bidiagonal_sequence_named)
  "rr_pf_second_derivative_bidiagonal_sequence" " using "
    "preserver" ":=" term ","
    "base" ":=" term ","
    "degree" ":=" term ","
    "recurrence" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_pf_second_derivative_bidiagonal_sequence using
        preserver := $hPF:term,
        base := $hbase:term,
        degree := $hdeg:term,
        recurrence := $hrec:term) =>
      `(tactic|
        exact RealRooted.isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence
          $hbase $hdeg $hPF $hrec)

syntax (name := rr_pf_second_derivative_bidiagonal_sequence_preserver_normalized_named)
  "rr_pf_second_derivative_bidiagonal_sequence" " using "
    "preserver" ":=" term ","
    "base" ":=" term ","
    "degree" ":=" term ","
    "normalizer" ":=" term ","
    "recurrence" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_pf_second_derivative_bidiagonal_sequence using
        preserver := $hPF:term,
        base := $hbase:term,
        degree := $hdeg:term,
        normalizer := $hnorm:term,
        recurrence := $hrec:term) =>
      `(tactic|
        exact RealRooted.isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_norm
          $hbase $hdeg $hPF $hnorm $hrec)

syntax (name := rr_pf_second_derivative_bidiagonal_sequence_jensen_named)
  "rr_pf_second_derivative_bidiagonal_sequence" " using "
    "jensen_backend" ":=" term ","
    "certificate" ":=" term ","
    "base" ":=" term ","
    "degree" ":=" term ","
    "recurrence" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_pf_second_derivative_bidiagonal_sequence using
        jensen_backend := $hbackend:term,
        certificate := $hcert:term,
        base := $hbase:term,
        degree := $hdeg:term,
        recurrence := $hrec:term) =>
      `(tactic|
        exact RealRooted.isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_jensenPencil
          $hbackend $hbase $hdeg $hcert $hrec)

syntax (name := rr_pf_second_derivative_bidiagonal_sequence_jensen_normalized_named)
  "rr_pf_second_derivative_bidiagonal_sequence" " using "
    "jensen_backend" ":=" term ","
    "certificate" ":=" term ","
    "base" ":=" term ","
    "degree" ":=" term ","
    "normalizer" ":=" term ","
    "recurrence" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_pf_second_derivative_bidiagonal_sequence using
        jensen_backend := $hbackend:term,
        certificate := $hcert:term,
        base := $hbase:term,
        degree := $hdeg:term,
        normalizer := $hnorm:term,
        recurrence := $hrec:term) =>
      `(tactic|
        exact
          RealRooted.isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_jensenPencil_norm
            $hbackend $hbase $hdeg $hcert $hnorm $hrec)

syntax (name := rr_pf_second_derivative_bidiagonal_sequence_cubic_certificate_named)
  "rr_pf_second_derivative_bidiagonal_sequence" " using "
    "jensen_backend" ":=" term ","
    "cubic_certificate" ":=" term ","
    "base" ":=" term ","
    "degree" ":=" term ","
    "recurrence" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_pf_second_derivative_bidiagonal_sequence using
        jensen_backend := $hbackend:term,
        cubic_certificate := $hcert:term,
        base := $hbase:term,
        degree := $hdeg:term,
        recurrence := $hrec:term) =>
      `(tactic|
        exact
          RealRooted.isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicCert
            $hbackend $hbase $hdeg $hcert $hrec)

syntax (name := rr_pf_second_derivative_bidiagonal_sequence_cubic_certificate_normalized_named)
  "rr_pf_second_derivative_bidiagonal_sequence" " using "
    "jensen_backend" ":=" term ","
    "cubic_certificate" ":=" term ","
    "base" ":=" term ","
    "degree" ":=" term ","
    "normalizer" ":=" term ","
    "recurrence" ":=" term :
  tactic

macro_rules
  | `(tactic|
      rr_pf_second_derivative_bidiagonal_sequence using
        jensen_backend := $hbackend:term,
        cubic_certificate := $hcert:term,
        base := $hbase:term,
        degree := $hdeg:term,
        normalizer := $hnorm:term,
        recurrence := $hrec:term) =>
      `(tactic|
        exact
          RealRooted.isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicCert_norm
            $hbackend $hbase $hdeg $hcert $hnorm $hrec)

end Tactic

end RealRooted
