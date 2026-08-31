import RealRooted.MultiplierSequence.Bidiagonal.Jensen.CubicResidual

/-!
# Quadratic cubic-residual specializations

This module specializes cubic residual certificates to quadratic Jensen
weights and canonical second-derivative bidiagonal forms.
-/

open Polynomial

noncomputable section

namespace RealRooted

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


end RealRooted
