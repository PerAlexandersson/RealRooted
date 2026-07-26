module

public import RealRooted.Mathlib.LinearAlgebra.Matrix.SignVariation
public import Mathlib.Data.Matrix.Mul

/-!
# Kernel sign-variation lower bounds

This file contains a small matrix-level predicate for variation-diminishing
arguments: every nonzero vector in the kernel of a finite matrix has at least a
specified number of sign variations.
-/

public section

noncomputable section

namespace Matrix

/-- A finite matrix has kernel sign-variation lower bound `r` if every nonzero
vector in its kernel has at least `r` sign variations. -/
def KernelSignVariationLowerBound {R : Type*} [Semiring R] [LinearOrder R]
    {m n : ℕ} (M : Matrix (Fin m) (Fin n) R) (r : ℕ) : Prop :=
  ∀ {v : Fin n → R}, M.mulVec v = 0 → v ≠ 0 → r ≤ Fin.signVariations v

protected lemma KernelSignVariationLowerBound.zero {R : Type*}
    [Semiring R] [LinearOrder R] {m n : ℕ} (M : Matrix (Fin m) (Fin n) R) :
    M.KernelSignVariationLowerBound 0 := by
  intro v hker hvec_ne
  exact Nat.zero_le _

lemma KernelSignVariationLowerBound.apply {R : Type*} [Semiring R] [LinearOrder R]
    {m n r : ℕ} {M : Matrix (Fin m) (Fin n) R}
    (hM : M.KernelSignVariationLowerBound r) {v : Fin n → R}
    (hker : M.mulVec v = 0) (hvec_ne : v ≠ 0) :
    r ≤ Fin.signVariations v :=
  hM hker hvec_ne

lemma KernelSignVariationLowerBound.mono {R : Type*} [Semiring R] [LinearOrder R]
    {m n r s : ℕ} {M : Matrix (Fin m) (Fin n) R}
    (hM : M.KernelSignVariationLowerBound r) (hsr : s ≤ r) :
    M.KernelSignVariationLowerBound s := by
  intro v hker hvec_ne
  exact hsr.trans (hM.apply hker hvec_ne)

end Matrix
