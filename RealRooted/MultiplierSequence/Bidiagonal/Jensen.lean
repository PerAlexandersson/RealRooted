import RealRooted.Hadamard
import RealRooted.HermiteBiehler
import RealRooted.MultiplierSequence.Bidiagonal.SecondDerivative

/-!
# Bidiagonal Jensen pencils

This module owns the reusable finite Jensen-pencil interface for
coefficient-bidiagonal operators: its quadratic residual factorization,
small PF discriminant certificate, and certificate consequences.
-/

open Polynomial

noncomputable section

namespace RealRooted

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

/-- A degree-bounded bidiagonal output is the sum of the two fixed-degree
Schur--Szegő compositions attached to its Jensen endpoints. -/
theorem bidiagonalOperator_eq_schurSzegoComp
    {alpha beta : ℕ → ℝ} {d : ℕ} {p : ℝ[X]}
    (hp : p.natDegree ≤ d) :
    bidiagonalOperator alpha beta p =
      schurSzegoComp d (jensenPolynomial d alpha) p +
        X * schurSzegoComp d (jensenPolynomial d beta) p := by
  rw [bidiagonalOperator,
    schurSzegoComp_jensenPolynomial_eq_diagonalOperator_of_natDegree_le hp,
    schurSzegoComp_jensenPolynomial_eq_diagonalOperator_of_natDegree_le hp]

/-- Quadratic coefficient function `a k^2 + b k + c`. -/
def quadraticJensenWeight (a b c : ℝ) (k : ℕ) : ℝ :=
  a * (k : ℝ) ^ 2 + b * (k : ℝ) + c

/-- Jensen polynomial attached to `quadraticJensenWeight`. -/
def quadraticJensen (a b c : ℝ) (d : ℕ) : ℝ[X] :=
  jensenPolynomial d (quadraticJensenWeight a b c)

/-- The residual quadratic after removing the common `(1+X)^(d-2)` factor. -/
def quadraticJensenResidual (a b c : ℝ) (d : ℕ) : ℝ[X] :=
  C c * (X + 1) ^ 2 +
    C ((a + b) * (d : ℝ)) * X * (X + 1) +
      C (a * (d : ℝ) * ((d : ℝ) - 1)) * X ^ 2

/-- Cubic residual for a bidiagonal Jensen pencil with quadratic coefficient functions. -/
def quadraticBidiagonalResidual
    (aa ab ac ba bb bc : ℝ) (d : ℕ) : ℝ[X] :=
  quadraticJensenResidual aa ab ac d + X * quadraticJensenResidual ba bb bc d

/-- Cubic residual pencil for a bidiagonal Jensen pencil with quadratic coefficients. -/
def quadraticBidiagonalPencilResidual
    (aa ab ac ba bb bc lam : ℝ) (d : ℕ) : ℝ[X] :=
  quadraticJensenResidual aa ab ac d +
    C lam * X * quadraticJensenResidual ba bb bc d

theorem quadraticBidiagonalPencilResidual_one
    (aa ab ac ba bb bc : ℝ) (d : ℕ) :
    quadraticBidiagonalPencilResidual aa ab ac ba bb bc 1 d =
      quadraticBidiagonalResidual aa ab ac ba bb bc d := by
  simp [quadraticBidiagonalPencilResidual, quadraticBidiagonalResidual]

/-- The written second-derivative quadratic coefficient is a quadratic Jensen weight. -/
theorem secondDerivativeQuadraticCoeff_eq_quadraticJensenWeight
    (a b c : ℝ) :
    secondDerivativeQuadraticCoeff a b c = quadraticJensenWeight c (b - c) a := by
  funext k
  simp [secondDerivativeQuadraticCoeff, quadraticJensenWeight]
  ring

/-- `quadraticJensen` is the Jensen polynomial for `quadraticJensenWeight`. -/
theorem quadraticJensen_eq_jensenPolynomial (a b c : ℝ) (d : ℕ) :
    quadraticJensen a b c d =
      jensenPolynomial d (quadraticJensenWeight a b c) := rfl

/-- Factorization of a quadratic Jensen polynomial through its residual. -/
theorem quadraticJensen_eq_factor_residual
    (a b c : ℝ) {d : ℕ} (hd : 2 ≤ d) :
    quadraticJensen a b c d =
      (X + 1) ^ (d - 2) * quadraticJensenResidual a b c d := by
  change jensenPolynomial d (fun k => a * (k : ℝ) ^ 2 + b * (k : ℝ) + c) =
    (X + 1) ^ (d - 2) * quadraticJensenResidual a b c d
  simpa [quadraticJensenResidual] using
    jensenPolynomial_quadratic_sequence_factor a b c d hd

/-- Quadratic coefficient functions give a cubic residual pencil after the common factor. -/
theorem quadraticBidiagonalJensenPencil_eq_factor_residual
    (aa ab ac ba bb bc lam : ℝ) {d : ℕ} (hd : 2 ≤ d) :
    bidiagonalJensenPencil
        (quadraticJensenWeight aa ab ac)
        (quadraticJensenWeight ba bb bc) d lam =
      (X + 1) ^ (d - 2) *
        quadraticBidiagonalPencilResidual aa ab ac ba bb bc lam d := by
  rw [bidiagonalJensenPencil]
  change quadraticJensen aa ab ac d + C lam * X * quadraticJensen ba bb bc d =
    (X + 1) ^ (d - 2) *
      quadraticBidiagonalPencilResidual aa ab ac ba bb bc lam d
  rw [quadraticJensen_eq_factor_residual aa ab ac hd]
  rw [quadraticJensen_eq_factor_residual ba bb bc hd]
  simp [quadraticBidiagonalPencilResidual]
  ring

/-- The `lambda = 1` specialization of the quadratic bidiagonal residual factorization. -/
theorem quadraticBidiagonalJensenPencil_eq_factor_residual_one
    (aa ab ac ba bb bc : ℝ) {d : ℕ} (hd : 2 ≤ d) :
    bidiagonalJensenPencil
        (quadraticJensenWeight aa ab ac)
        (quadraticJensenWeight ba bb bc) d 1 =
      (X + 1) ^ (d - 2) *
        quadraticBidiagonalResidual aa ab ac ba bb bc d := by
  rw [quadraticBidiagonalJensenPencil_eq_factor_residual aa ab ac ba bb bc 1 hd]
  rw [quadraticBidiagonalPencilResidual_one]

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
  have halpha : (jensenPolynomial d alpha).coeff n = 0 :=
    coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (natDegree_jensenPolynomial_le d alpha) (by lia))
  cases n with
  | zero =>
      simp [bidiagonalJensenPencil, halpha]
  | succ n =>
      have hbeta : (jensenPolynomial d beta).coeff n = 0 :=
        coeff_eq_zero_of_natDegree_lt
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

This predicate records the concrete one-sided finite pencil condition.  The
condition does not by itself supply the orientation required by the
Garloff--Wagner proper-position theorem. The human proof instead uses a
one-sided root-count contraction; its general Lean formalization remains
incomplete. -/
def BidiagonalJensenPencilCertificate
    (alpha beta : ℕ → ℝ) (d : ℕ) : Prop :=
  IsPFPolynomial (jensenPolynomial d alpha) ∧
  IsPFPolynomial (X * jensenPolynomial d beta) ∧
  ∀ lam : ℝ, 0 ≤ lam →
    IsPFPolynomial (bidiagonalJensenPencil alpha beta d lam)

/-- A Jensen-pencil certificate is exactly strong enough to make its two
endpoints compatible in the Chudnovsky--Seymour nonnegative-combination
sense. -/
theorem BidiagonalJensenPencilCertificate.compatible
    {alpha beta : ℕ → ℝ} {d : ℕ}
    (hcert : BidiagonalJensenPencilCertificate alpha beta d) :
    Compatible (jensenPolynomial d alpha)
      (X * jensenPolynomial d beta) := by
  intro a b ha hb
  by_cases ha0 : a = 0
  · subst a
    have hpf : IsPFPolynomial
        (C b * (X * jensenPolynomial d beta)) := by
      by_cases hb0 : b = 0
      · subst b
        simpa using IsPFPolynomial.zero
      · exact hcert.2.1.const_mul (lt_of_le_of_ne hb (Ne.symm hb0))
    by_cases hzero : C b * (X * jensenPolynomial d beta) = 0
    · exact Or.inl (by simpa using hzero)
    · right
      simpa using
        (And.intro hzero (hpf.eq_zero_or_splits.resolve_left hzero))
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    let lam : ℝ := b / a
    have hlam : 0 ≤ lam := div_nonneg hb ha
    have hpf : IsPFPolynomial
        (C a * (bidiagonalJensenPencil alpha beta d lam)) :=
      (hcert.2.2 lam hlam).const_mul ha_pos
    have hpoly :
        C a * bidiagonalJensenPencil alpha beta d lam =
          C a * jensenPolynomial d alpha +
            C b * (X * jensenPolynomial d beta) := by
      simp only [bidiagonalJensenPencil, mul_add, lam]
      congr 1
      have hab : a * (b / a) = b := by field_simp [ha0]
      calc
        C a * (C (b / a) * X * jensenPolynomial d beta) =
            (C a * C (b / a)) * (X * jensenPolynomial d beta) := by ring
        _ = C (a * (b / a)) * (X * jensenPolynomial d beta) := by rw [Polynomial.C_mul]
        _ = C b * (X * jensenPolynomial d beta) := by rw [hab]
    rw [← hpoly]
    by_cases hzero : C a * bidiagonalJensenPencil alpha beta d lam = 0
    · exact Or.inl hzero
    · exact Or.inr ⟨hzero, hpf.eq_zero_or_splits.resolve_left hzero⟩

/-- A Jensen-pencil certificate makes the diagonal coefficients nonnegative
through the certified degree bound. -/
theorem BidiagonalJensenPencilCertificate.alpha_nonneg_of_le
    {alpha beta : ℕ → ℝ} {d k : ℕ}
    (hcert : BidiagonalJensenPencilCertificate alpha beta d) (hk : k ≤ d) :
    0 ≤ alpha k := by
  have hcoeff := hcert.1.hasNonnegCoeffs k
  rw [coeff_jensenPolynomial, if_pos hk] at hcoeff
  have hchoose : (0 : ℝ) < Nat.choose d k := by exact_mod_cast Nat.choose_pos hk
  nlinarith

/-- A Jensen-pencil certificate makes the subdiagonal coefficients
nonnegative through the certified degree bound. -/
theorem BidiagonalJensenPencilCertificate.beta_nonneg_of_le
    {alpha beta : ℕ → ℝ} {d k : ℕ}
    (hcert : BidiagonalJensenPencilCertificate alpha beta d) (hk : k ≤ d) :
    0 ≤ beta k := by
  have hcoeff := hcert.2.1.hasNonnegCoeffs (k + 1)
  simp [coeff_jensenPolynomial, hk] at hcoeff
  have hchoose : (0 : ℝ) < Nat.choose d k := by exact_mod_cast Nat.choose_pos hk
  nlinarith


end RealRooted
