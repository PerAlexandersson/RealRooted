import RealRooted.BorceaBranden.Applications.BidiagonalSymbol.RealConsequences
import RealRooted.Hadamard
import RealRooted.JensenPencilContraction
import RealRooted.MultiplierSequence.Bidiagonal
import RealRooted.MultiplierSequence.Bidiagonal.Jensen.LowDegree
import RealRooted.Tactic.Finish
import RealRooted.Tactic.PFPolynomial
import RealRooted.Tactic.Lookup

/-!
# PF bidiagonal operator shells

This file packages the coefficient-bidiagonal operator that appears in the
remaining one-step second-derivative OEIS recurrences. Genuine affine-symbol
stability gives a checked PF-preserver route. The weaker one-sided Jensen
pencil is proved by finite-free root-count contraction and PF closure.
-/

open Polynomial

noncomputable section

namespace RealRooted

/-- The root-count contraction core needed by the general Jensen-pencil
argument.

This is the zero-aware Schur--Szegő formulation of the finite-free
multiplicative-convolution step: composing both Jensen endpoints with the
same PF polynomial preserves compatibility after restoring the explicit
factor `X` on the second endpoint. -/
def schurSzegoPreservesJensenPencilCompatibilityStatement : Prop :=
  ∀ {d : ℕ} {A B p : ℝ[X]},
    IsPFPolynomial A →
    IsPFPolynomial (X * B) →
    IsPFPolynomial p →
    A.natDegree ≤ d →
    B.natDegree ≤ d →
    p.natDegree ≤ d →
    Compatible A (X * B) →
    Compatible (schurSzegoComp d A p)
      (X * schurSzegoComp d B p)

/-- The two endpoint compositions in the Jensen-pencil contraction core are
individually PF.  Thus the remaining content of the core statement is their
compatibility, not endpoint real-rootedness or root location. -/
theorem schurSzegoJensenEndpoints_pf
    {d : ℕ} {A B p : ℝ[X]}
    (hA : IsPFPolynomial A) (hXB : IsPFPolynomial (X * B))
    (hp : IsPFPolynomial p) (hAdeg : A.natDegree ≤ d)
    (hBdeg : B.natDegree ≤ d) (hpdeg : p.natDegree ≤ d) :
    IsPFPolynomial (schurSzegoComp d A p) ∧
      IsPFPolynomial (X * schurSzegoComp d B p) := by
  exact ⟨hA.schurSzegoComp hp hAdeg hpdeg,
    ((isPFPolynomial_of_X_mul hXB).schurSzegoComp hp hBdeg hpdeg).X_mul⟩

/-- The Schur--Szegő compatibility core implies the complete Jensen-pencil
bidiagonal preserver theorem. -/
theorem jensenPencilBidiagonalPreserver_of_schurSzegoCompatibility
    (hcore : schurSzegoPreservesJensenPencilCompatibilityStatement) :
    ∀ {alpha beta : ℕ → ℝ} {d : ℕ},
      BidiagonalJensenPencilCertificate alpha beta d →
      BidiagonalPFPreserver alpha beta d := by
  intro alpha beta d hcert p hp hdeg
  have hcompat :
      Compatible
        (schurSzegoComp d (jensenPolynomial d alpha) p)
        (X * schurSzegoComp d (jensenPolynomial d beta) p) :=
    hcore hcert.1 hcert.2.1 hp
      (natDegree_jensenPolynomial_le d alpha)
      (natDegree_jensenPolynomial_le d beta) hdeg hcert.compatible
  have hout_nonneg : HasNonnegCoeffs (bidiagonalOperator alpha beta p) :=
    hp.hasNonnegCoeffs.bidiagonalOperator_of_degree_le hdeg
      (fun k hk => hcert.alpha_nonneg_of_le hk)
      (fun k hk => hcert.beta_nonneg_of_le hk)
  apply IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits hout_nonneg
  rw [bidiagonalOperator_eq_schurSzegoComp hdeg]
  rcases hcompat 1 1 (by norm_num) (by norm_num) with hzero | hsplits
  · simpa using Or.inl hzero
  · exact Or.inr (by simpa using hsplits.2)

/-- Jensen-pencil implication for coefficient-bidiagonal PF preservers. -/
theorem jensenPencilBidiagonalPreserver :
    ∀ {alpha beta : ℕ → ℝ} {d : ℕ},
      BidiagonalJensenPencilCertificate alpha beta d →
      BidiagonalPFPreserver alpha beta d := by
  exact jensenPencilBidiagonalPreserver_of_schurSzegoCompatibility
    schurSzegoPreservesJensenPencilCompatibility

/-- Apply the named Jensen-pencil backend theorem. -/
theorem bidiagonalPFPreserver_of_jensenPencil
    {alpha beta : ℕ → ℝ} {d : ℕ}
    (hcert : BidiagonalJensenPencilCertificate alpha beta d) :
    BidiagonalPFPreserver alpha beta d :=
  jensenPencilBidiagonalPreserver hcert

/-- A Jensen-pencil certificate gives a coefficient-bidiagonal PF preserver
once the global backend is available. -/
theorem BidiagonalJensenPencilCertificate.toPFPreserver
    {alpha beta : ℕ → ℝ} {d : ℕ}
    (hcert : BidiagonalJensenPencilCertificate alpha beta d) :
    BidiagonalPFPreserver alpha beta d :=
  bidiagonalPFPreserver_of_jensenPencil hcert

/-- Rowwise Jensen-pencil certificates give rowwise coefficient-bidiagonal
PF preservers. -/
theorem BidiagonalJensenPencilCertificate.toPFPreserver_sequence
    {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (hcert : ∀ n : Nat,
      BidiagonalJensenPencilCertificate (alpha n) (beta n) (d n)) :
    ∀ n : Nat, BidiagonalPFPreserver (alpha n) (beta n) (d n) :=
  fun n => (hcert n).toPFPreserver

/-- Tail-start rowwise version of
`BidiagonalJensenPencilCertificate.toPFPreserver_sequence`. -/
theorem BidiagonalJensenPencilCertificate.toPFPreserver_sequence_from
    (N : Nat) {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (hcert : ∀ n : Nat, N ≤ n →
      BidiagonalJensenPencilCertificate (alpha n) (beta n) (d n)) :
    ∀ n : Nat, N ≤ n → BidiagonalPFPreserver (alpha n) (beta n) (d n) :=
  fun n hn => (hcert n hn).toPFPreserver

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

/-- Cubic-residual certificate specialized to quadratic Jensen coefficient functions. -/
def quadraticBidiagonalCubicResidualCertificate
    (aa ab ac ba bb bc : ℝ) {d : ℕ} (hd : 2 ≤ d)
    (hA : CubicPFDiscriminantCertificate (quadraticJensenResidual aa ab ac d))
    (hB : CubicPFDiscriminantCertificate (X * quadraticJensenResidual ba bb bc d))
    (hS : ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate
        (quadraticBidiagonalPencilResidual aa ab ac ba bb bc lam d)) :
    BidiagonalCubicResidualCertificate
      (quadraticJensenWeight aa ab ac)
      (quadraticJensenWeight ba bb bc) d where
  m := d - 2
  alphaResidual := quadraticJensenResidual aa ab ac d
  betaResidual := X * quadraticJensenResidual ba bb bc d
  pencilResidual := fun lam => quadraticBidiagonalPencilResidual aa ab ac ba bb bc lam d
  alpha_factor := quadraticJensen_eq_factor_residual aa ab ac hd
  beta_factor := by
    have hbeta := quadraticJensen_eq_factor_residual ba bb bc hd
    change X * quadraticJensen ba bb bc d =
      (X + 1) ^ (d - 2) * (X * quadraticJensenResidual ba bb bc d)
    rw [hbeta]
    ring
  pencil_factor := fun lam _ =>
    quadraticBidiagonalJensenPencil_eq_factor_residual aa ab ac ba bb bc lam hd
  alpha_cubic := hA
  beta_cubic := hB
  pencil_cubic := hS

/-- Cubic-residual certificate specialized to the canonical quadratic
coefficient functions of a second-derivative bidiagonal form. -/
def secondDerivativeBidiagonalCubicResidualCertificate
    {a0 a1 b1 b2 c2 c3 : ℝ} {d : ℕ} (hd : 2 ≤ d)
    (hA : CubicPFDiscriminantCertificate
      (quadraticJensenResidual c2 (b1 - c2) a0 d))
    (hB : CubicPFDiscriminantCertificate
      (X * quadraticJensenResidual c3 (b2 - c3) a1 d))
    (hS : ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate
        (quadraticBidiagonalPencilResidual
          c2 (b1 - c2) a0 c3 (b2 - c3) a1 lam d)) :
    BidiagonalCubicResidualCertificate
      (fun k => secondDerivativeQuadraticCoeff a0 b1 c2 k)
      (fun k => secondDerivativeQuadraticCoeff a1 b2 c3 k) d := by
  simpa [secondDerivativeQuadraticCoeff_eq_quadraticJensenWeight] using
    quadraticBidiagonalCubicResidualCertificate
      c2 (b1 - c2) a0 c3 (b2 - c3) a1 hd hA hB hS

/-- Rowwise canonical second-derivative cubic-residual certificates. -/
def secondDerivativeBidiagonalCubicResidualCertificate_sequence
    {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (hd : ∀ n : Nat, 2 ≤ d n)
    (hA : ∀ n : Nat, CubicPFDiscriminantCertificate
      (quadraticJensenResidual (c2 n) (b1 n - c2 n) (a0 n) (d n)))
    (hB : ∀ n : Nat, CubicPFDiscriminantCertificate
      (X * quadraticJensenResidual (c3 n) (b2 n - c3 n) (a1 n) (d n)))
    (hS : ∀ n : Nat, ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate
        (quadraticBidiagonalPencilResidual
          (c2 n) (b1 n - c2 n) (a0 n)
          (c3 n) (b2 n - c3 n) (a1 n) lam (d n))) :
    ∀ n : Nat,
      BidiagonalCubicResidualCertificate
        (fun k => secondDerivativeQuadraticCoeff (a0 n) (b1 n) (c2 n) k)
        (fun k => secondDerivativeQuadraticCoeff (a1 n) (b2 n) (c3 n) k)
        (d n) :=
  fun n =>
    secondDerivativeBidiagonalCubicResidualCertificate
      (a0 := a0 n) (a1 := a1 n) (b1 := b1 n)
      (b2 := b2 n) (c2 := c2 n) (c3 := c3 n)
      (hd n) (hA n) (hB n) (hS n)

/-- Tail-start version of
`secondDerivativeBidiagonalCubicResidualCertificate_sequence`. -/
def secondDerivativeBidiagonalCubicResidualCertificate_sequence_from
    {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (N : Nat)
    (hd : ∀ n : Nat, N ≤ n → 2 ≤ d n)
    (hA : ∀ n : Nat, N ≤ n → CubicPFDiscriminantCertificate
      (quadraticJensenResidual (c2 n) (b1 n - c2 n) (a0 n) (d n)))
    (hB : ∀ n : Nat, N ≤ n → CubicPFDiscriminantCertificate
      (X * quadraticJensenResidual (c3 n) (b2 n - c3 n) (a1 n) (d n)))
    (hS : ∀ n : Nat, N ≤ n → ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate
        (quadraticBidiagonalPencilResidual
          (c2 n) (b1 n - c2 n) (a0 n)
          (c3 n) (b2 n - c3 n) (a1 n) lam (d n))) :
    ∀ n : Nat, N ≤ n →
      BidiagonalCubicResidualCertificate
        (fun k => secondDerivativeQuadraticCoeff (a0 n) (b1 n) (c2 n) k)
        (fun k => secondDerivativeQuadraticCoeff (a1 n) (b2 n) (c3 n) k)
        (d n) :=
  fun n hn =>
    secondDerivativeBidiagonalCubicResidualCertificate
      (a0 := a0 n) (a1 := a1 n) (b1 := b1 n)
      (b2 := b2 n) (c2 := c2 n) (c3 := c3 n)
      (hd n hn) (hA n hn) (hB n hn) (hS n hn)

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

/-- Quadratic Jensen residual certificate route for a coefficient-bidiagonal preserver. -/
theorem quadraticBidiagonalPFPreserver_of_cubicResidualCertificate
    (aa ab ac ba bb bc : ℝ) {d : ℕ} (hd : 2 ≤ d)
    (hA : CubicPFDiscriminantCertificate (quadraticJensenResidual aa ab ac d))
    (hB : CubicPFDiscriminantCertificate (X * quadraticJensenResidual ba bb bc d))
    (hS : ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate
        (quadraticBidiagonalPencilResidual aa ab ac ba bb bc lam d)) :
    BidiagonalPFPreserver
      (quadraticJensenWeight aa ab ac)
      (quadraticJensenWeight ba bb bc) d :=
  bidiagonalPFPreserver_of_cubicResidualCertificate
    (quadraticBidiagonalCubicResidualCertificate aa ab ac ba bb bc hd hA hB hS)

/-- Quadratic residual certificate route for the canonical coefficient
functions of a second-derivative bidiagonal form. -/
theorem secondDerivativeBidiagonalPFPreserver_of_cubicResidualCertificate
    {a0 a1 b1 b2 c2 c3 : ℝ} {d : ℕ} (hd : 2 ≤ d)
    (hA : CubicPFDiscriminantCertificate
      (quadraticJensenResidual c2 (b1 - c2) a0 d))
    (hB : CubicPFDiscriminantCertificate
      (X * quadraticJensenResidual c3 (b2 - c3) a1 d))
    (hS : ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate
        (quadraticBidiagonalPencilResidual
          c2 (b1 - c2) a0 c3 (b2 - c3) a1 lam d)) :
    BidiagonalPFPreserver
      (fun k => secondDerivativeQuadraticCoeff a0 b1 c2 k)
      (fun k => secondDerivativeQuadraticCoeff a1 b2 c3 k) d :=
  bidiagonalPFPreserver_of_cubicResidualCertificate
    (secondDerivativeBidiagonalCubicResidualCertificate hd hA hB hS)

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

/-- Project splitting from a zero-aware PF certificate. -/
theorem splits_of_isPFPolynomial {p : ℝ[X]} (hp : IsPFPolynomial p) :
    p.Splits :=
  RealRooted.Tactic.pf_splits hp

/-- Project one row from a PF sequence certificate. -/
theorem at_of_isPFPolynomial_sequence {P : Nat → ℝ[X]}
    (hP : ∀ n : Nat, IsPFPolynomial (P n)) (n : Nat) :
    IsPFPolynomial (P n) :=
  hP n

/-- Project row-wise coefficient nonnegativity from a PF sequence certificate. -/
theorem hasNonnegCoeffs_of_isPFPolynomial_sequence {P : Nat → ℝ[X]}
    (hP : ∀ n : Nat, IsPFPolynomial (P n)) :
    ∀ n : Nat, HasNonnegCoeffs (P n) :=
  RealRooted.Tactic.pf_sequence_has_nonneg hP

/-- Project row-wise zero-or-splitting from a PF sequence certificate. -/
theorem eq_zero_or_splits_of_isPFPolynomial_sequence {P : Nat → ℝ[X]}
    (hP : ∀ n : Nat, IsPFPolynomial (P n)) :
    ∀ n : Nat, P n = 0 ∨ (P n).Splits :=
  RealRooted.Tactic.pf_sequence_zero_or_splits hP

/-- Project row-wise splitting from a PF sequence certificate. -/
theorem splits_of_isPFPolynomial_sequence {P : Nat → ℝ[X]}
    (hP : ∀ n : Nat, IsPFPolynomial (P n)) :
    ∀ n : Nat, (P n).Splits :=
  RealRooted.Tactic.pf_sequence_splits hP

/-- Combine a PF sequence certificate with row-wise nonvanishing to obtain the
strict real-rootedness shape used by the scalar recurrence tactics. -/
theorem isRealRooted_of_isPFPolynomial_sequence {P : Nat → ℝ[X]}
    (hP : ∀ n : Nat, IsPFPolynomial (P n))
    (hne : ∀ n : Nat, P n ≠ 0) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  RealRooted.Tactic.pf_sequence_realrooted hP hne

/-- Sequence wrapper for first-order recurrences by coefficient-bidiagonal
PF-preserving operators. -/
theorem isPFPolynomial_of_bidiagonalOperator_sequence
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hpres : ∀ n : Nat, BidiagonalPFPreserver (alpha n) (beta n) (d n))
    (hrec : ∀ n : Nat,
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  sequence_of_base_and_step hbase fun n hP => by
    simpa [hrec n] using
      isPFPolynomial_bidiagonalOperator_of_preserver (hpres n) hP (hdeg n)

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
    ∀ n : Nat, IsPFPolynomial (P n) :=
  sequence_of_base_interval_and_step_from N hbase fun n hn hP => by
    simpa [hrec n hn] using
      isPFPolynomial_bidiagonalOperator_of_preserver (hpres n hn) hP (hdeg n hn)

/-- Sequence wrapper using per-row Jensen-pencil certificates. -/
theorem isPFPolynomial_of_bidiagonalOperator_sequence_of_jensenPencil
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat,
      BidiagonalJensenPencilCertificate (alpha n) (beta n) (d n))
    (hrec : ∀ n : Nat,
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_bidiagonalOperator_sequence hbase hdeg
    (BidiagonalJensenPencilCertificate.toPFPreserver_sequence hcert) hrec

/-- Tail-start sequence wrapper using per-row Jensen-pencil certificates. -/
theorem isPFPolynomial_of_bidiagonalOperator_sequence_of_jensenPencil_from
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
    (BidiagonalJensenPencilCertificate.toPFPreserver_sequence_from
       N hcert) hrec

/-- Sequence wrapper using bundled cubic-residual certificates as row hints. -/
theorem isPFPolynomial_of_bidiagonalOperator_sequence_of_cubicResidualCertificate
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ} {d : Nat → ℕ}
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hcert : ∀ n : Nat,
      BidiagonalCubicResidualCertificate (alpha n) (beta n) (d n))
    (hrec : ∀ n : Nat,
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_bidiagonalOperator_sequence hbase hdeg
    (BidiagonalCubicResidualCertificate.toPFPreserver_sequence hcert) hrec

/-- Tail-start sequence wrapper using bundled cubic-residual certificates as
row hints. -/
theorem isPFPolynomial_of_bidiagonalOperator_sequence_of_cubicResidualCertificate_from
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
    (BidiagonalCubicResidualCertificate.toPFPreserver_sequence_from
       N hcert) hrec

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

/-- Tail-start version of
`isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence`. -/
theorem isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_from
    {P : Nat → ℝ[X]} {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, N ≤ n → (P n).natDegree ≤ d n)
    (hpres : ∀ n : Nat, N ≤ n →
      BidiagonalPFPreserver
        (fun k => secondDerivativeQuadraticCoeff (a0 n) (b1 n) (c2 n) k)
        (fun k => secondDerivativeQuadraticCoeff (a1 n) (b2 n) (c3 n) k)
        (d n))
    (hrec : ∀ n : Nat, N ≤ n →
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_bidiagonalOperator_sequence_from N hbase hdeg hpres
    (fun n hn => (hrec n hn).trans
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

/-- Tail-start version of
`isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_norm`. -/
theorem isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_norm_from
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ}
    {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, N ≤ n → (P n).natDegree ≤ d n)
    (hpres : ∀ n : Nat, N ≤ n →
      BidiagonalPFPreserver (alpha n) (beta n) (d n))
    (hnorm : ∀ n : Nat, N ≤ n →
      secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n) =
        bidiagonalOperator (alpha n) (beta n) (P n))
    (hrec : ∀ n : Nat, N ≤ n →
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_bidiagonalOperator_sequence_from N hbase hdeg hpres
    (fun n hn => (hrec n hn).trans (hnorm n hn))

/-- Sequence wrapper for Family H-style second-derivative recurrences using
per-row Jensen-pencil certificates. -/
theorem isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_jensenPencil
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
    (BidiagonalJensenPencilCertificate.toPFPreserver_sequence hcert) hrec

/-- Tail-start second-derivative wrapper using per-row Jensen-pencil
certificates for the canonical coefficient functions. -/
theorem isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_jensenPencil_from
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
  isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_from N hbase hdeg
    (BidiagonalJensenPencilCertificate.toPFPreserver_sequence_from
       N hcert) hrec

/-- Sequence wrapper for second-derivative recurrences whose Jensen
certificates are attached to named coefficient-bidiagonal functions. -/
theorem isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_jensenPencil_norm
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
    (BidiagonalJensenPencilCertificate.toPFPreserver_sequence hcert)
    hnorm hrec

/-- Tail-start version of
`isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_jensenPencil_norm`. -/
theorem
    isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_jensenPencil_norm_from
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
  isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_norm_from N hbase hdeg
    (BidiagonalJensenPencilCertificate.toPFPreserver_sequence_from
       N hcert) hnorm hrec

/-- Sequence wrapper for second-derivative PF-bidiagonal recurrences using
bundled cubic-residual certificates as row hints. -/
theorem
    isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicResidualCertificate
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
    (BidiagonalCubicResidualCertificate.toPFPreserver_sequence hcert) hrec

/-- Tail-start second-derivative wrapper using bundled cubic-residual
certificates attached to the canonical coefficient functions. -/
theorem
    isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicResidualCertificate_from
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
  isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_from N hbase hdeg
    (BidiagonalCubicResidualCertificate.toPFPreserver_sequence_from
       N hcert) hrec

/-- Short compatibility spelling for the bundled cubic-residual version of the
second-derivative PF-bidiagonal sequence wrapper. -/
theorem isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicCert
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
     hbase hdeg hcert hrec

/-- Tail-start version of
`isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicCert`.

This is the direct version for certificates attached to the canonical
quadratic coefficient functions of the second-derivative form. -/
theorem isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicCert_from
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
  isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicResidualCertificate_from
     N hbase hdeg hcert hrec

/-- Sequence wrapper for second-derivative recurrences whose certificate is
stated using named coefficient-bidiagonal functions.

This is useful for promoted sequence shells: the recurrence is often recorded
in differential form, while the generated Jensen/cubic certificate is attached
to named `alpha` and `beta` coefficient functions. -/
theorem
    isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicCert_norm
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
  isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_norm hbase hdeg
    (BidiagonalCubicResidualCertificate.toPFPreserver_sequence hcert)
    hnorm hrec

/-- Tail-start version of
`isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicCert_norm`.

This is useful for `n`-dependent coefficient-bidiagonal certificates whose
common Jensen factor only has the stable residual shape from a cutoff row
onward. -/
theorem
    isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicCert_norm_from
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
  isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_norm_from N hbase hdeg
    (BidiagonalCubicResidualCertificate.toPFPreserver_sequence_from
       N hcert) hnorm hrec

/-- Sequence wrapper whose per-row Jensen-pencil certificates are supplied by
common-factor residual cubic certificates. -/
theorem isPFPolynomial_of_bidiagonalOperator_sequence_of_cubicResidual
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
     hbase hdeg
    (bidiagonalCubicResidualCertificate_sequence_of_cubicResidual
      halpha hbeta hpencil hA hB hS)
    hrec

/-- Tail-start version of
`isPFPolynomial_of_bidiagonalOperator_sequence_of_cubicResidual`. -/
theorem isPFPolynomial_of_bidiagonalOperator_sequence_of_cubicResidual_from
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ}
    {d m : Nat → ℕ} {A B : Nat → ℝ[X]} {S : Nat → ℝ → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, N ≤ n → (P n).natDegree ≤ d n)
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
      CubicPFDiscriminantCertificate (S n lam))
    (hrec : ∀ n : Nat, N ≤ n →
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_bidiagonalOperator_sequence_of_cubicResidualCertificate_from
     N hbase hdeg
    (bidiagonalCubicResidualCertificate_sequence_of_cubicResidual_from
      N halpha hbeta hpencil hA hB hS)
    hrec

/-- Sequence wrapper whose residual pencil is derived from the endpoint
factorizations as `A n + C lam * B n`. -/
theorem isPFPolynomial_of_bidiagonalOperator_sequence_of_endpoint_cubicResidual
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
     hbase hdeg
    (bidiagonalCubicResidualCertificate_sequence_of_endpoint_cubicResidual
      halpha hbeta hA hB hS)
    hrec

/-- Tail-start version of
`isPFPolynomial_of_bidiagonalOperator_sequence_of_endpoint_cubicResidual`. -/
theorem isPFPolynomial_of_bidiagonalOperator_sequence_of_endpoint_cubicResidual_from
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ}
    {d m : Nat → ℕ} {A B : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, N ≤ n → (P n).natDegree ≤ d n)
    (halpha : ∀ n : Nat, N ≤ n →
      jensenPolynomial (d n) (alpha n) = ((X + 1 : ℝ[X]) ^ m n) * A n)
    (hbeta : ∀ n : Nat, N ≤ n →
      X * jensenPolynomial (d n) (beta n) =
        ((X + 1 : ℝ[X]) ^ m n) * B n)
    (hA : ∀ n : Nat, N ≤ n → CubicPFDiscriminantCertificate (A n))
    (hB : ∀ n : Nat, N ≤ n → CubicPFDiscriminantCertificate (B n))
    (hS : ∀ n : Nat, N ≤ n → ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate (A n + C lam * B n))
    (hrec : ∀ n : Nat, N ≤ n →
      P (n + 1) = bidiagonalOperator (alpha n) (beta n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_bidiagonalOperator_sequence_of_cubicResidualCertificate_from
     N hbase hdeg
    (bidiagonalCubicResidualCertificate_sequence_of_endpoint_cubicResidual_from
      N halpha hbeta hA hB hS)
    hrec

/-- Sequence wrapper for Family H-style second-derivative recurrences.

The recurrence is supplied in differential form using
`secondDerivativeBidiagonalForm`; this theorem normalizes it to
`bidiagonalOperator` and then applies the Jensen-pencil/cubic-residual PF
sequence wrapper. -/
theorem isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicResidual
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
     hbase hdeg
    (bidiagonalCubicResidualCertificate_sequence_of_cubicResidual
      halpha hbeta hpencil hA hB hS)
    hrec

/-- Tail-start version of
`isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicResidual`. -/
theorem isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicResidual_from
    {P : Nat → ℝ[X]} {a0 a1 b1 b2 c2 c3 : Nat → ℝ}
    {d m : Nat → ℕ} {A B : Nat → ℝ[X]} {S : Nat → ℝ → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, N ≤ n → (P n).natDegree ≤ d n)
    (halpha : ∀ n : Nat, N ≤ n →
      jensenPolynomial (d n)
          (fun k => secondDerivativeQuadraticCoeff (a0 n) (b1 n) (c2 n) k) =
        ((X + 1 : ℝ[X]) ^ m n) * A n)
    (hbeta : ∀ n : Nat, N ≤ n →
      X * jensenPolynomial (d n)
          (fun k => secondDerivativeQuadraticCoeff (a1 n) (b2 n) (c3 n) k) =
        ((X + 1 : ℝ[X]) ^ m n) * B n)
    (hpencil : ∀ n : Nat, N ≤ n → ∀ lam : ℝ, 0 ≤ lam →
      bidiagonalJensenPencil
          (fun k => secondDerivativeQuadraticCoeff (a0 n) (b1 n) (c2 n) k)
          (fun k => secondDerivativeQuadraticCoeff (a1 n) (b2 n) (c3 n) k)
          (d n) lam =
        ((X + 1 : ℝ[X]) ^ m n) * S n lam)
    (hA : ∀ n : Nat, N ≤ n → CubicPFDiscriminantCertificate (A n))
    (hB : ∀ n : Nat, N ≤ n → CubicPFDiscriminantCertificate (B n))
    (hS : ∀ n : Nat, N ≤ n → ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate (S n lam))
    (hrec : ∀ n : Nat, N ≤ n →
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicCert_from
     N hbase hdeg
    (bidiagonalCubicResidualCertificate_sequence_of_cubicResidual_from
      N halpha hbeta hpencil hA hB hS)
    hrec

/-- Second-derivative sequence wrapper whose residual pencil is derived from
the endpoint factorizations as `A n + C lam * B n`. -/
theorem isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_endpoint_cubicResidual
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
     hbase hdeg
    (bidiagonalCubicResidualCertificate_sequence_of_endpoint_cubicResidual
      halpha hbeta hA hB hS)
    hrec

/-- Tail-start version of
`isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_endpoint_cubicResidual`. -/
theorem
    isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_endpoint_cubicResidual_from
    {P : Nat → ℝ[X]} {a0 a1 b1 b2 c2 c3 : Nat → ℝ}
    {d m : Nat → ℕ} {A B : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, N ≤ n → (P n).natDegree ≤ d n)
    (halpha : ∀ n : Nat, N ≤ n →
      jensenPolynomial (d n)
          (fun k => secondDerivativeQuadraticCoeff (a0 n) (b1 n) (c2 n) k) =
        ((X + 1 : ℝ[X]) ^ m n) * A n)
    (hbeta : ∀ n : Nat, N ≤ n →
      X * jensenPolynomial (d n)
          (fun k => secondDerivativeQuadraticCoeff (a1 n) (b2 n) (c3 n) k) =
        ((X + 1 : ℝ[X]) ^ m n) * B n)
    (hA : ∀ n : Nat, N ≤ n → CubicPFDiscriminantCertificate (A n))
    (hB : ∀ n : Nat, N ≤ n → CubicPFDiscriminantCertificate (B n))
    (hS : ∀ n : Nat, N ≤ n → ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate (A n + C lam * B n))
    (hrec : ∀ n : Nat, N ≤ n →
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicCert_from
     N hbase hdeg
    (bidiagonalCubicResidualCertificate_sequence_of_endpoint_cubicResidual_from
      N halpha hbeta hA hB hS)
    hrec

/-- Second-derivative sequence wrapper using the quadratic Jensen
factorization of the canonical coefficient functions.

This is the Family H route when each row supplies only the active degree
condition `2 ≤ d n` and cubic certificates for the quadratic residual pencil. -/
theorem
    isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_quadraticCubicResidual
    {P : Nat → ℝ[X]} {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (hbase : IsPFPolynomial (P 0))
    (hdeg : ∀ n : Nat, (P n).natDegree ≤ d n)
    (hd : ∀ n : Nat, 2 ≤ d n)
    (hA : ∀ n : Nat, CubicPFDiscriminantCertificate
      (quadraticJensenResidual (c2 n) (b1 n - c2 n) (a0 n) (d n)))
    (hB : ∀ n : Nat, CubicPFDiscriminantCertificate
      (X * quadraticJensenResidual (c3 n) (b2 n - c3 n) (a1 n) (d n)))
    (hS : ∀ n : Nat, ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate
        (quadraticBidiagonalPencilResidual
          (c2 n) (b1 n - c2 n) (a0 n)
          (c3 n) (b2 n - c3 n) (a1 n) lam (d n)))
    (hrec : ∀ n : Nat,
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicCert
     hbase hdeg
    (secondDerivativeBidiagonalCubicResidualCertificate_sequence
      hd hA hB hS)
    hrec

/-- Tail-start version of
`isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_quadraticCubicResidual`. -/
theorem
    isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_quadraticCubicResidual_from
    {P : Nat → ℝ[X]} {a0 a1 b1 b2 c2 c3 : Nat → ℝ} {d : Nat → ℕ}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, N ≤ n → (P n).natDegree ≤ d n)
    (hd : ∀ n : Nat, N ≤ n → 2 ≤ d n)
    (hA : ∀ n : Nat, N ≤ n → CubicPFDiscriminantCertificate
      (quadraticJensenResidual (c2 n) (b1 n - c2 n) (a0 n) (d n)))
    (hB : ∀ n : Nat, N ≤ n → CubicPFDiscriminantCertificate
      (X * quadraticJensenResidual (c3 n) (b2 n - c3 n) (a1 n) (d n)))
    (hS : ∀ n : Nat, N ≤ n → ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate
        (quadraticBidiagonalPencilResidual
          (c2 n) (b1 n - c2 n) (a0 n)
          (c3 n) (b2 n - c3 n) (a1 n) lam (d n)))
    (hrec : ∀ n : Nat, N ≤ n →
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicCert_from
     N hbase hdeg
    (secondDerivativeBidiagonalCubicResidualCertificate_sequence_from
      N hd hA hB hS)
    hrec

/-- Sequence wrapper for second-derivative recurrences with unbundled
common-factor residual cubic certificates attached to named coefficient
bidiagonal functions. -/
theorem isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicResidual_norm
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
     hbase hdeg
    (bidiagonalCubicResidualCertificate_sequence_of_cubicResidual
      halpha hbeta hpencil hA hB hS)
    hnorm hrec

/-- Tail-start version of
`isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicResidual_norm`. -/
theorem
    isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicResidual_norm_from
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ}
    {a0 a1 b1 b2 c2 c3 : Nat → ℝ}
    {d m : Nat → ℕ} {A B : Nat → ℝ[X]} {S : Nat → ℝ → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, N ≤ n → (P n).natDegree ≤ d n)
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
      CubicPFDiscriminantCertificate (S n lam))
    (hnorm : ∀ n : Nat, N ≤ n →
      secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n) =
        bidiagonalOperator (alpha n) (beta n) (P n))
    (hrec : ∀ n : Nat, N ≤ n →
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicCert_norm_from
     N hbase hdeg
    (bidiagonalCubicResidualCertificate_sequence_of_cubicResidual_from
      N halpha hbeta hpencil hA hB hS)
    hnorm hrec

/-- Normalized second-derivative sequence wrapper whose residual pencil is
derived from the endpoint factorizations as `A n + C lam * B n`. -/
theorem isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_endpoint_cubicResidual_norm
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
     hbase hdeg
    (bidiagonalCubicResidualCertificate_sequence_of_endpoint_cubicResidual
      halpha hbeta hA hB hS)
    hnorm hrec

/-- Tail-start version of
`isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_endpoint_cubicResidual_norm`. -/
theorem
    isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_endpoint_cubicResidual_norm_from
    {P : Nat → ℝ[X]} {alpha beta : Nat → ℕ → ℝ}
    {a0 a1 b1 b2 c2 c3 : Nat → ℝ}
    {d m : Nat → ℕ} {A B : Nat → ℝ[X]}
    (N : Nat)
    (hbase : ∀ n : Nat, n ≤ N → IsPFPolynomial (P n))
    (hdeg : ∀ n : Nat, N ≤ n → (P n).natDegree ≤ d n)
    (halpha : ∀ n : Nat, N ≤ n →
      jensenPolynomial (d n) (alpha n) = ((X + 1 : ℝ[X]) ^ m n) * A n)
    (hbeta : ∀ n : Nat, N ≤ n →
      X * jensenPolynomial (d n) (beta n) =
        ((X + 1 : ℝ[X]) ^ m n) * B n)
    (hA : ∀ n : Nat, N ≤ n → CubicPFDiscriminantCertificate (A n))
    (hB : ∀ n : Nat, N ≤ n → CubicPFDiscriminantCertificate (B n))
    (hS : ∀ n : Nat, N ≤ n → ∀ lam : ℝ, 0 ≤ lam →
      CubicPFDiscriminantCertificate (A n + C lam * B n))
    (hnorm : ∀ n : Nat, N ≤ n →
      secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n) =
        bidiagonalOperator (alpha n) (beta n) (P n))
    (hrec : ∀ n : Nat, N ≤ n →
      P (n + 1) =
        secondDerivativeBidiagonalForm
          (a0 n) (a1 n) (b1 n) (b2 n) (c2 n) (c3 n) (P n)) :
    ∀ n : Nat, IsPFPolynomial (P n) :=
  isPFPolynomial_of_secondDerivativeBidiagonalForm_sequence_of_cubicCert_norm_from
     N hbase hdeg
    (bidiagonalCubicResidualCertificate_sequence_of_endpoint_cubicResidual_from
      N halpha hbeta hA hB hS)
    hnorm hrec


end RealRooted
