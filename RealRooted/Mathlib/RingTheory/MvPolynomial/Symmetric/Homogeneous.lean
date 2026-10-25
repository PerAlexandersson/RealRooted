/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

/-!
# Homogeneity of elementary symmetric polynomials
-/

@[expose] public section

namespace MvPolynomial

/-- The elementary symmetric polynomial of index `n` is homogeneous of
degree `n`. -/
theorem isHomogeneous_esymm
    {R σ : Type*} [CommSemiring R] [Fintype σ] (n : ℕ) :
    IsHomogeneous (esymm σ R n) n := by
  classical
  rw [esymm]
  apply IsHomogeneous.sum
  intro s hs
  have hcard : s.card = n := (Finset.mem_powersetCard.mp hs).2
  simpa [hcard] using IsHomogeneous.prod s
    (fun i => X i : σ → MvPolynomial σ R) (fun _ => 1)
    (fun i _ => isHomogeneous_X R i)

end MvPolynomial
