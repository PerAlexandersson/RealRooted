/-
Copyright (c) 2026 RealRooted contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RealRooted contributors
-/
module

public import RealRooted.Mathlib.Algebra.Polynomial.Moment
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Linarith

/-!
# Monic orthogonal polynomials from a finite moment matrix


The finite Hankel matrix determines the lower coefficients of the monic polynomial
orthogonal to all lower powers. Invertibility, rather than positivity, is the exact
algebraic hypothesis. Positivity of the moment pairing is a sufficient condition.
-/

@[expose] public section

open Matrix

noncomputable section

namespace Polynomial

section CommSemiring

variable {R : Type*} [CommSemiring R] [DecidableEq R]

/-- The finite Hankel matrix formed by the first moments. -/
def momentHankelMatrix (μ : ℕ → R) (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  fun i j => μ (i.val + j.val)

/-- The moments of a finite coefficient vector are a finite scalar product. -/
theorem momentPairing_X_pow_ofFn (μ : ℕ → R) {n : ℕ}
    (i : ℕ) (v : Fin n → R) :
    momentPairing μ (X ^ i) (ofFn n v) =
      ∑ j : Fin n, μ (i + j.val) * v j := by
  rw [ofFn_eq_sum_monomial, momentPairing_sum_right]
  simp only [X_pow_eq_monomial, momentPairing_monomial, mul_one, mul_comm]

/-- The finite Hankel matrix is the matrix of the moment pairing in monomial
coordinates. -/
theorem momentPairing_ofFn_ofFn (μ : ℕ → R) {n : ℕ}
    (v w : Fin n → R) :
    momentPairing μ (ofFn n v) (ofFn n w) =
      dotProduct v (momentHankelMatrix μ n *ᵥ w) := by
  rw [ofFn_eq_sum_monomial v, momentPairing_comm, momentPairing_sum_right]
  change (∑ i : Fin n, momentPairing μ (ofFn n w) (monomial i.val (v i))) =
    ∑ i : Fin n, v i * (momentHankelMatrix μ n *ᵥ w) i
  apply Finset.sum_congr rfl
  intro i _
  rw [← C_mul_X_pow_eq_monomial, momentPairing_C_mul_right,
    momentPairing_comm, momentPairing_X_pow_ofFn]
  rfl

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] [Nontrivial R] [DecidableEq R]

/-- The lower coefficients obtained by solving the finite moment equations. -/
def momentOrthogonalCoefficients (μ : ℕ → R) (n : ℕ) : Fin n → R :=
  (momentHankelMatrix μ n)⁻¹ *ᵥ (fun i => -μ (n + i.val))

/-- The monic polynomial obtained from the finite moment solve. Its orthogonality
requires the determinant of the moment matrix to be a unit. -/
def monicMomentPolynomial (μ : ℕ → R) (n : ℕ) : R[X] :=
  X ^ n + ofFn n (momentOrthogonalCoefficients μ n)

/-- A finite vector of lower coefficients gives a monic polynomial of the
prescribed degree, including degree zero. -/
theorem isMonicOfDegree_X_pow_add_ofFn {n : ℕ} (v : Fin n → R) :
    IsMonicOfDegree (X ^ n + ofFn n v) n := by
  have hsmall : (ofFn n v).degree < ((X : R[X]) ^ n).degree := by
    simpa only [degree_X_pow] using ofFn_degree_lt v
  refine ⟨?_, ?_⟩
  · rw [natDegree_add_eq_left_of_degree_lt hsmall, natDegree_X_pow]
  · change (X ^ n + ofFn n v).leadingCoeff = 1
    rw [leadingCoeff_add_of_degree_lt' hsmall]
    exact monic_X_pow n

/-- A monic polynomial is reconstructed from its lower coefficients. -/
theorem IsMonicOfDegree.eq_X_pow_add_ofFn {p : R[X]} {n : ℕ}
    (hp : IsMonicOfDegree p n) :
    p = X ^ n + ofFn n (fun i : Fin n => p.coeff i.val) := by
  ext k
  by_cases hk : k < n
  · simp only [coeff_add, coeff_X_pow, ite_eq_right (ne_of_lt hk),
      ofFn_coeff_eq_val_of_lt _ hk, zero_add]
  · exact hp.coeff_eq (isMonicOfDegree_X_pow_add_ofFn _) (Nat.le_of_not_gt hk)

/-- The finite moment construction is always monic of the requested degree. -/
theorem isMonicOfDegree_monicMomentPolynomial (μ : ℕ → R) (n : ℕ) :
    IsMonicOfDegree (monicMomentPolynomial μ n) n :=
  isMonicOfDegree_X_pow_add_ofFn _

omit [Nontrivial R] in
@[simp] theorem monicMomentPolynomial_zero (μ : ℕ → R) :
    monicMomentPolynomial μ 0 = 1 := by
  simp [monicMomentPolynomial]

omit [Nontrivial R] in
/-- The lower coefficients of the constructed polynomial are the solved vector. -/
theorem coeff_monicMomentPolynomial (μ : ℕ → R) {n : ℕ} (i : Fin n) :
    (monicMomentPolynomial μ n).coeff i.val = momentOrthogonalCoefficients μ n i := by
  simp only [monicMomentPolynomial, coeff_add, coeff_X_pow,
    ite_eq_right (ne_of_lt i.is_lt), ofFn_coeff_eq_val_of_lt _ i.is_lt, zero_add]

omit [Nontrivial R] [DecidableEq R] in
/-- The coefficient vector solves the finite Hankel system when its determinant
is a unit. -/
theorem momentHankelMatrix_mulVec_coefficients (μ : ℕ → R) (n : ℕ)
    (hdet : IsUnit (momentHankelMatrix μ n).det) :
    momentHankelMatrix μ n *ᵥ momentOrthogonalCoefficients μ n =
      fun i => -μ (n + i.val) := by
  rw [momentOrthogonalCoefficients, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]

omit [Nontrivial R] in
/-- The lower orthogonality equations are exactly the finite Hankel equations. -/
theorem momentPairing_X_pow_add_ofFn (μ : ℕ → R) {n : ℕ}
    (v : Fin n → R) (i : Fin n) :
    momentPairing μ (X ^ i.val) (X ^ n + ofFn n v) =
      μ (n + i.val) + (momentHankelMatrix μ n *ᵥ v) i := by
  rw [momentPairing_add_right, momentPairing_X_pow_ofFn]
  change momentFunctional μ (X ^ i.val * X ^ n) + _ = _
  rw [← pow_add, momentFunctional_X_pow]
  simp only [momentHankelMatrix, Matrix.mulVec, dotProduct, Nat.add_comm]

omit [Nontrivial R] in
/-- The constructed polynomial is orthogonal to each lower power. -/
theorem momentPairing_X_pow_monicMomentPolynomial (μ : ℕ → R) (n : ℕ)
    (hdet : IsUnit (momentHankelMatrix μ n).det) (i : Fin n) :
    momentPairing μ (X ^ i.val) (monicMomentPolynomial μ n) = 0 := by
  rw [monicMomentPolynomial, momentPairing_X_pow_add_ofFn,
    momentHankelMatrix_mulVec_coefficients μ n hdet]
  simp

/-- Orthogonality to the lower powers characterizes the monic moment polynomial. -/
theorem eq_monicMomentPolynomial (μ : ℕ → R) {n : ℕ}
    (hdet : IsUnit (momentHankelMatrix μ n).det) {p : R[X]}
    (hp : IsMonicOfDegree p n)
    (horth : ∀ i : Fin n, momentPairing μ (X ^ i.val) p = 0) :
    p = monicMomentPolynomial μ n := by
  let v : Fin n → R := fun i => p.coeff i.val
  have hpv : p = X ^ n + ofFn n v := hp.eq_X_pow_add_ofFn
  have hv : momentHankelMatrix μ n *ᵥ v = fun i => -μ (n + i.val) := by
    funext i
    have hi := horth i
    rw [hpv, momentPairing_X_pow_add_ofFn] at hi
    exact eq_neg_of_add_eq_zero_right hi
  have hcoeff : v = momentOrthogonalCoefficients μ n := by
    calc
      v = (momentHankelMatrix μ n)⁻¹ *ᵥ (momentHankelMatrix μ n *ᵥ v) := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
      _ = momentOrthogonalCoefficients μ n := by rw [hv]; rfl
  rw [hpv, hcoeff]
  rfl

omit [DecidableEq R] in
/-- A nondegenerate finite moment system has exactly one monic polynomial
orthogonal to all lower powers. -/
theorem existsUnique_monic_moment_orthogonal (μ : ℕ → R) (n : ℕ)
    (hdet : IsUnit (momentHankelMatrix μ n).det) :
    ∃! p : R[X], IsMonicOfDegree p n ∧
      ∀ i : Fin n, momentPairing μ (X ^ i.val) p = 0 := by
  classical
  refine ⟨monicMomentPolynomial μ n,
    ⟨isMonicOfDegree_monicMomentPolynomial μ n,
      momentPairing_X_pow_monicMomentPolynomial μ n hdet⟩, ?_⟩
  intro p hp
  exact eq_monicMomentPolynomial μ hdet hp.1 hp.2

omit [Nontrivial R] in
/-- The constructed polynomial is orthogonal to every lower-degree polynomial. -/
theorem momentPairing_monicMomentPolynomial (μ : ℕ → R) (n : ℕ)
    (hdet : IsUnit (momentHankelMatrix μ n).det) {p : R[X]}
    (hp : p.degree < n) :
    momentPairing μ p (monicMomentPolynomial μ n) = 0 := by
  by_cases hp0 : p = 0
  · simp [hp0]
  have hpdeg : p.natDegree < n := (natDegree_lt_iff_degree_lt hp0).mpr hp
  have hpfn : p = ofFn n (toFn n p) :=
    (ofFn_comp_toFn_eq_id_of_natDegree_lt hpdeg).symm
  rw [momentPairing_comm, hpfn, ofFn_eq_sum_monomial, momentPairing_sum_right]
  apply Finset.sum_eq_zero
  intro i _
  rw [← C_mul_X_pow_eq_monomial, momentPairing_C_mul_right, momentPairing_comm,
    momentPairing_X_pow_monicMomentPolynomial μ n hdet]
  simp

end CommRing

/-- Positivity on squares of degree below `n` makes the finite moment matrix
positive definite. This applies to finite measures as well as continuous ones. -/
theorem momentHankelMatrix_posDef_of_pos (μ : ℕ → ℝ) (n : ℕ)
    (hpos : ∀ p : ℝ[X], p ≠ 0 → p.degree < n → 0 < momentPairing μ p p) :
    (momentHankelMatrix μ n).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · apply Matrix.IsHermitian.ext
    intro i j
    simp [momentHankelMatrix, Nat.add_comm]
  · intro v hv
    have hp : ofFn n v ≠ 0 := by
      intro hz
      apply hv
      apply injective_ofFn n
      simpa only [map_zero] using hz
    have hstrict := hpos (ofFn n v) hp (ofFn_degree_lt v)
    rw [momentPairing_ofFn_ofFn] at hstrict
    simpa only [Pi.star_apply, star_trivial] using hstrict

/-- A positive definite polynomial moment pairing gives positive definite
Hankel matrices of every finite size. -/
theorem momentHankelMatrix_posDef (μ : ℕ → ℝ)
    (hpos : (momentPairingBilinForm μ).toQuadraticMap.PosDef) (n : ℕ) :
    (momentHankelMatrix μ n).PosDef := by
  apply momentHankelMatrix_posDef_of_pos μ n
  intro p hp _
  exact hpos p hp

/-- Positive definiteness of the finite Gram matrix supplies the algebraic
nondegeneracy premise of the monic orthogonal construction. -/
theorem existsUnique_monic_moment_orthogonal_of_posDef (μ : ℕ → ℝ) (n : ℕ)
    (hpos : (momentHankelMatrix μ n).PosDef) :
    ∃! p : ℝ[X], IsMonicOfDegree p n ∧
      ∀ i : Fin n, momentPairing μ (X ^ i.val) p = 0 := by
  apply existsUnique_monic_moment_orthogonal μ n
  exact isUnit_iff_ne_zero.mpr hpos.det_pos.ne'

end Polynomial
