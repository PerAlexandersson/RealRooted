/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.Algebra.Polynomial.Orthogonal.Moment
public import Mathlib.Algebra.Group.EvenFunction

/-!
# Parity of monic orthogonal polynomials

Vanishing odd moments make the polynomial moment functional invariant under
reflection. Uniqueness in a nonsingular degree-`n` moment system then gives
parity `n` for its monic orthogonal polynomial. Positivity is not needed.
-/

public section

namespace Polynomial

section CommRing

variable {R : Type*} [CommRing R]

/-- Vanishing odd moments make the moment functional invariant under reflection. -/
theorem momentFunctional_comp_neg_X (m : ℕ → R)
    (hodd : ∀ k : ℕ, Odd k → m k = 0) (p : R[X]) :
    momentFunctional m (p.comp (-X)) = momentFunctional m p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [add_comp, momentFunctional_add, hp, hq]
  | monomial n a =>
      have hsign : (-1 : R) ^ n * m n = m n := by
        rcases Nat.even_or_odd n with hn | hn
        · rw [hn.neg_one_pow, one_mul]
        · rw [hodd n hn, mul_zero]
      have hpoly : (monomial n a).comp (-X) =
          C (a * (-1 : R) ^ n) * X ^ n := by
        rw [monomial_comp, neg_pow]
        simp only [map_mul, map_pow, map_neg, map_one]
        ring
      rw [hpoly, momentFunctional_C_mul, momentFunctional_X_pow,
        momentFunctional_monomial, mul_assoc, hsign]

/-- Reflecting both arguments preserves a moment pairing with vanishing odd moments. -/
theorem momentPairing_comp_neg_X (m : ℕ → R)
    (hodd : ∀ k : ℕ, Odd k → m k = 0) (p q : R[X]) :
    momentPairing m (p.comp (-X)) (q.comp (-X)) = momentPairing m p q := by
  change momentFunctional m (p.comp (-X) * q.comp (-X)) = _
  rw [← mul_comp, momentFunctional_comp_neg_X m hodd]
  rfl

/-- Reflection can be transferred between the two arguments of a symmetric moment pairing. -/
theorem momentPairing_comp_neg_X_right (m : ℕ → R)
    (hodd : ∀ k : ℕ, Odd k → m k = 0) (p q : R[X]) :
    momentPairing m p (q.comp (-X)) = momentPairing m (p.comp (-X)) q := by
  simpa only [comp_neg_X_comp_neg_X] using
    momentPairing_comp_neg_X m hodd (p.comp (-X)) q

end CommRing

section NontrivialCommRing

variable {R : Type*} [CommRing R] [Nontrivial R] [DecidableEq R]

/-- The monic orthogonal polynomial of degree `n` has parity `n` when odd moments vanish. -/
theorem monicMomentPolynomial_comp_neg_X (m : ℕ → R)
    (hodd : ∀ k : ℕ, Odd k → m k = 0) (n : ℕ)
    (hdet : IsUnit (momentHankelMatrix m n).det) :
    (monicMomentPolynomial m n).comp (-X) =
      C ((-1 : R) ^ n) * monicMomentPolynomial m n := by
  have hp := isMonicOfDegree_monicMomentPolynomial m n
  have hsign : (-1 : R) ^ n * (-1 : R) ^ n = 1 := by
    rw [← mul_pow]
    simp
  have hnorm : C ((-1 : R) ^ n) * (monicMomentPolynomial m n).comp (-X) =
      monicMomentPolynomial m n := by
    apply eq_monicMomentPolynomial m hdet
    · refine ⟨?_, ?_⟩
      · rw [natDegree_C_mul_eq_of_mul_eq_one hsign,
          natDegree_eq_of_degree_eq (degree_comp_neg_X), hp.natDegree_eq]
      · simpa only [hp.natDegree_eq, map_pow, map_neg, map_one] using
          hp.monic.neg_one_pow_natDegree_mul_comp_neg_X
    · intro i
      rw [momentPairing_C_mul_right, momentPairing_comp_neg_X_right m hodd]
      have hz : momentPairing m ((X ^ i.val).comp (-X))
          (monicMomentPolynomial m n) = 0 := by
        apply momentPairing_monicMomentPolynomial m n hdet
        rw [degree_comp_neg_X, degree_X_pow]
        exact WithBot.coe_lt_coe.mpr i.is_lt
      rw [hz, mul_zero]
  have h := congrArg (fun q : R[X] => C ((-1 : R) ^ n) * q) hnorm
  simpa only [← mul_assoc, ← map_mul, hsign, map_one, one_mul] using h

/-- Evaluation form of the parity identity for the actual monic moment polynomial. -/
theorem monicMomentPolynomial_eval_neg (m : ℕ → R)
    (hodd : ∀ k : ℕ, Odd k → m k = 0) (n : ℕ)
    (hdet : IsUnit (momentHankelMatrix m n).det) (x : R) :
    (monicMomentPolynomial m n).eval (-x) =
      (-1 : R) ^ n * (monicMomentPolynomial m n).eval x := by
  simpa only [eval_comp, eval_neg, eval_X, eval_mul, eval_C] using
    congrArg (fun p : R[X] => p.eval x) (monicMomentPolynomial_comp_neg_X m hodd n hdet)

/-- Even degree gives an even monic orthogonal polynomial for symmetric moments. -/
theorem even_monicMomentPolynomial (m : ℕ → R)
    (hodd : ∀ k : ℕ, Odd k → m k = 0) (n : ℕ)
    (hdet : IsUnit (momentHankelMatrix m n).det) (hn : Even n) :
    Function.Even (monicMomentPolynomial m n).eval := by
  intro x
  simpa only [hn.neg_one_pow, one_mul] using monicMomentPolynomial_eval_neg m hodd n hdet x

/-- Odd degree gives an odd monic orthogonal polynomial for symmetric moments. -/
theorem odd_monicMomentPolynomial (m : ℕ → R)
    (hodd : ∀ k : ℕ, Odd k → m k = 0) (n : ℕ)
    (hdet : IsUnit (momentHankelMatrix m n).det) (hn : Odd n) :
    Function.Odd (monicMomentPolynomial m n).eval := by
  intro x
  simpa only [hn.neg_one_pow, neg_one_mul] using monicMomentPolynomial_eval_neg m hodd n hdet x

end NontrivialCommRing

end Polynomial
