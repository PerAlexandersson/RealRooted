import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Tactic.NoncommRing

/-!
# A finite spectral expansion of the characteristic adjugate

For a list of proposed roots, `Polynomial.evalQuotient` is the Newton-form
quotient of a scalar polynomial by `X - a`.  Its defining identity does not
require the coefficient algebra to be commutative.  Specializing the algebra
to matrices and using Cayley--Hamilton identifies this quotient with the
adjugate of the characteristic matrix whenever the proposed roots factor the
characteristic polynomial.
-/

open Polynomial

namespace Polynomial

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- The monic polynomial whose roots, in order, are the entries of `roots`. -/
noncomputable def rootsProduct : List R → R[X]
  | [] => 1
  | r :: roots => (X - C r) * rootsProduct roots

@[simp]
theorem rootsProduct_eq_map_prod (roots : List R) :
    rootsProduct roots = (roots.map fun r => X - C r).prod := by
  induction roots with
  | nil => rfl
  | cons r roots ih => simp [rootsProduct, ih]

/-- Newton-form quotient of `rootsProduct roots` by `X - a`. -/
noncomputable def evalQuotient (a : A) : List R → A[X]
  | [] => 0
  | r :: roots =>
      (rootsProduct roots).map (algebraMap R A) +
        C (a - algebraMap R A r) * evalQuotient a roots

private theorem map_commute (p : R[X]) (q : A[X]) :
    Commute (p.map (algebraMap R A)) q := by
  induction p using Polynomial.induction_on' with
  | add p₁ p₂ h₁ h₂ =>
      rw [Polynomial.map_add]
      exact h₁.add_left h₂
  | monomial n r =>
      rw [map_monomial, ← C_mul_X_pow_eq_monomial]
      apply Commute.mul_left
      · change C (algebraMap R A r) * q = q * C (algebraMap R A r)
        simpa [Polynomial.C_eq_algebraMap] using (Algebra.commutes r q)
      · exact commute_X_pow q n

/-- Multiplying the Newton quotient by `X - a` recovers the original scalar
polynomial minus its value at `a`. -/
theorem evalQuotient_mul_X_sub_C (a : A) : ∀ roots : List R,
    evalQuotient a roots * (X - C a) =
      (rootsProduct roots).map (algebraMap R A) - C (aeval a (rootsProduct roots)) := by
  intro roots
  induction roots with
  | nil => simp [evalQuotient, rootsProduct]
  | cons r roots ih =>
      rw [evalQuotient, rootsProduct, add_mul, mul_assoc, ih]
      simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X,
        Polynomial.map_C, aeval_mul, aeval_sub, aeval_X, aeval_C, C_sub, C_mul]
      have hc := map_commute (rootsProduct roots) (C a)
      have hr := map_commute (rootsProduct roots) (C (algebraMap R A r))
      have hX := commute_X ((rootsProduct roots).map (algebraMap R A))
      have hc' := hc.eq
      have hr' := hr.eq
      have hX' := hX.eq
      simp only [mul_sub, sub_mul]
      rw [hc', hX']
      noncomm_ring

/-- Right multiplication by the monic linear polynomial `X - C a` is
injective, even when the coefficient ring has zero divisors. -/
theorem mul_X_sub_C_injective (a : A) :
    Function.Injective (fun p : A[X] => p * (X - C a)) := by
  intro p q hpq
  apply sub_eq_zero.mp
  let s := p - q
  have hs : s * (X - C a) = 0 := by
    simp only [s, sub_mul, hpq, sub_self]
  by_contra hs0
  have hs0' : s ≠ 0 := by simpa only [s] using hs0
  have hc := congrArg (fun u : A[X] => u.coeff (s.natDegree + 1)) hs
  rw [coeff_mul_X_sub_C, coeff_natDegree_succ_eq_zero] at hc
  simp only [zero_mul, sub_zero, coeff_zero] at hc
  exact (leadingCoeff_ne_zero.mpr hs0') (by simpa [coeff_natDegree] using hc)

end Polynomial

namespace Matrix

open Polynomial

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

/-- If `roots` factors the characteristic polynomial, the adjugate of the
characteristic matrix is the Newton-form quotient at the matrix itself. -/
theorem matPolyEquiv_adjugate_charmatrix_eq_evalQuotient
    (M : Matrix n n R) (roots : List R)
    (hchar : M.charpoly = rootsProduct roots) :
    matPolyEquiv (adjugate (charmatrix M)) = evalQuotient M roots := by
  apply mul_X_sub_C_injective M
  calc
    matPolyEquiv (adjugate (charmatrix M)) * (X - C M) =
        matPolyEquiv (adjugate (charmatrix M) * charmatrix M) := by
          rw [map_mul, matPolyEquiv_charmatrix]
    _ = M.charpoly.map (algebraMap R (Matrix n n R)) := by
      rw [adjugate_mul, matPolyEquiv_smul_one]
      rfl
    _ = (rootsProduct roots).map (algebraMap R (Matrix n n R)) := by rw [hchar]
    _ = evalQuotient M roots * (X - C M) := by
      rw [evalQuotient_mul_X_sub_C]
      rw [← hchar, Matrix.aeval_self_charpoly, C_0, sub_zero]

end Matrix
