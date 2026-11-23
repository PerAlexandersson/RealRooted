/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.Algebra.Polynomial.MobiusTransform
import Mathlib.Tactic.FinCases

/-!
# Coefficient maps and homogeneous Möbius transforms
-/

public section

namespace Polynomial

/-- Changing coefficients commutes with the homogeneous Möbius transform. -/
theorem map_mobiusTransform {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (n : ℕ) (a b c d : R) (p : R[X]) :
    (mobiusTransform n a b c d p).map f =
      mobiusTransform n (f a) (f b) (f c) (f d) (p.map f) := by
  have h := MvPolynomial.map_eval₂Hom
    (Polynomial.C : R →+* R[X])
    (![C a * X + C b, C c * X + C d] : Fin 2 → R[X])
    (Polynomial.mapRingHom f) (p.homogenize n)
  rw [mobiusTransform, mobiusTransform, Polynomial.homogenize_map]
  simp only [MvPolynomial.aeval_def]
  rw [MvPolynomial.eval₂_map]
  convert h using 1
  · simp
  · congr 1
    · ext r
      simp
    · funext i
      fin_cases i <;> simp

end Polynomial
