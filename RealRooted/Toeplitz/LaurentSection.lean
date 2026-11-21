/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Laurent Toeplitz sections and geometric diagonal similarity

We give finite sections for a two-sided coefficient function, with entry `b (i-j)`.
This differs from the existing lower-Toeplitz `RealRooted.toeplitzFin`.
Geometric changes of the Laurent variable preserve characteristic polynomials.
Real coefficients satisfying the corresponding balance relation therefore give
split characteristic polynomials in every size.

This is the elementary Hermitian alternative in Section 5 of the unpublished
manuscript *Real limiting spectra for balanced five-diagonal Toeplitz matrices*
(2026-10-29), tracked in RealRooted issue #2157. No limiting-spectrum theorem
is assumed or proved here.
-/

@[expose] public section

noncomputable section

namespace RealRooted.Toeplitz

/-- The `n`th finite Toeplitz section of a two-sided coefficient function. -/
def laurentSection {R : Type*} (b : ℤ → R) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  fun i j => b ((i : ℤ) - (j : ℤ))

/-- Geometric substitution of a Laurent variable is diagonal similarity on every
finite section; no finite-support assumption is needed for a finite matrix. -/
theorem laurentSection_geometric {K : Type*} [Field K] (b : ℤ → K) (n : ℕ)
    (r : K) (hr : r ≠ 0) :
    laurentSection (fun k => r ^ k * b k) n =
      Matrix.diagonal (fun i : Fin n => r ^ (i : ℤ)) * laurentSection b n *
        Matrix.diagonal (fun i : Fin n => r ^ (-(i : ℤ))) := by
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, laurentSection]
  rw [zpow_sub₀ hr]
  simp only [zpow_neg]
  ring

/-- Geometric substitution preserves the characteristic polynomial of every finite
Laurent Toeplitz section. -/
theorem charpoly_laurentSection_geometric {K : Type*} [Field K]
    (b : ℤ → K) (n : ℕ) (r : K) (hr : r ≠ 0) :
    (laurentSection (fun k => r ^ k * b k) n).charpoly = (laurentSection b n).charpoly := by
  rw [laurentSection_geometric b n r hr, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc]
  have hinv : Matrix.diagonal (fun i : Fin n => r ^ (-(i : ℤ))) *
      Matrix.diagonal (fun i : Fin n => r ^ (i : ℤ)) = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    simp only [← zpow_add₀ hr, neg_add_cancel, zpow_zero, Matrix.diagonal_one]
  rw [hinv, one_mul]

/-- A real Laurent coefficient function balanced by a nonzero geometric scale has
real spectrum in every finite size, expressed by splitting of its characteristic
polynomial. For bandwidth two the balance conditions are exactly
`b(-1) = r² b(1)` and `b(-2) = r⁴ b(2)`. -/
theorem splits_charpoly_laurentSection_of_balance (b : ℤ → ℝ) (n : ℕ)
    (r : ℝ) (hr : r ≠ 0) (hb : ∀ k, b (-k) = r ^ (2 * k) * b k) :
    (laurentSection b n).charpoly.Splits := by
  have hsym : (laurentSection (fun k => r ^ k * b k) n).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp only [laurentSection, star_trivial]
    have hd : (j : ℤ) - (i : ℤ) = -((i : ℤ) - (j : ℤ)) := by ring
    rw [hd, hb]
    rw [← mul_assoc, ← zpow_add₀ hr]
    congr 2
    ring
  rw [← charpoly_laurentSection_geometric b n r hr]
  exact hsym.splits_charpoly

/-- An explicit balanced five-diagonal subclass, with arbitrary real diagonal and
first/second symmetric coefficients and a nonzero geometric scale. If `s ≠ 0`,
both outer coefficients are nonzero. Every finite section has real spectrum,
without needing a premise about its limiting spectrum. -/
theorem splits_charpoly_fiveDiagonal (d a s r : ℝ) (hr : r ≠ 0) (n : ℕ) :
    (laurentSection (fun k : ℤ => r ^ (-k) *
      (if k = 0 then d else if k = 1 ∨ k = -1 then a
        else if k = 2 ∨ k = -2 then s else 0)) n).charpoly.Splits := by
  apply splits_charpoly_laurentSection_of_balance _ n r hr
  intro k
  have he :
      (if -k = 0 then d else if -k = 1 ∨ -k = -1 then a
        else if -k = 2 ∨ -k = -2 then s else 0) =
      (if k = 0 then d else if k = 1 ∨ k = -1 then a
        else if k = 2 ∨ k = -2 then s else 0) := by
    congr 1
    · lia
    · congr 1
      · lia
      · congr 1
        lia
  rw [neg_neg, he, ← mul_assoc, ← zpow_add₀ hr]
  congr 2
  ring

end RealRooted.Toeplitz
