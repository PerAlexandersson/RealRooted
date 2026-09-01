import RealRooted.Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.Tactic.FinCases

/-!
# Finite-degree Cayley transform of a polynomial

The transform

`cayleyTransform n p = (1 - T)^n p(T / (1 - T))`

is defined through homogeneous evaluation, so no rational-function side
conditions are needed. The definition is functorial in the coefficient ring.
-/

open Polynomial

noncomputable section

namespace Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

def cayleyTransform (n : ℕ) (p : R[X]) : R[X] :=
  MvPolynomial.aeval ![X, 1 - X] (p.homogenize n)

theorem map_cayleyTransform (f : R →+* S) (n : ℕ) (p : R[X]) :
    (cayleyTransform n p).map f = cayleyTransform n (p.map f) := by
  have h := MvPolynomial.map_eval₂Hom
    (Polynomial.C : R →+* R[X])
    (![(X : R[X]), (1 - X : R[X])] : Fin 2 → R[X])
    (Polynomial.mapRingHom f) (p.homogenize n)
  rw [cayleyTransform, cayleyTransform, Polynomial.homogenize_map]
  simp only [MvPolynomial.aeval_def]
  rw [MvPolynomial.eval₂_map]
  convert h using 1
  · simp
  · congr 1
    · ext r
      simp
    · funext i
      fin_cases i <;> simp

theorem cayleyTransform_sub (n : ℕ) (p q : R[X]) :
    cayleyTransform n (p - q) = cayleyTransform n p - cayleyTransform n q := by
  simp [cayleyTransform, Polynomial.homogenize_sub]

theorem cayleyTransform_add (n : ℕ) (p q : R[X]) :
    cayleyTransform n (p + q) = cayleyTransform n p + cayleyTransform n q := by
  simp [cayleyTransform, Polynomial.homogenize_add]

theorem cayleyTransform_C_mul (n : ℕ) (a : R) (p : R[X]) :
    cayleyTransform n (C a * p) = C a * cayleyTransform n p := by
  simp [cayleyTransform, Polynomial.homogenize_C_mul]

theorem cayleyTransform_finset_sum {ι : Type*} (n : ℕ)
    (s : Finset ι) (p : ι → R[X]) :
    cayleyTransform n (∑ i ∈ s, p i) = ∑ i ∈ s, cayleyTransform n (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cayleyTransform]
  | @insert i s hi ih => simp [hi, ih, cayleyTransform_add]

end Polynomial
