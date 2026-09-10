import RealRooted.Basic.Coefficients.Multivariate
import RealRooted.BorceaBranden.Applications.HarmonicSubstitution.BFJAuxiliary.Homogeneous
import RealRooted.Mathlib.Data.Nat.Choose.Nanjundiah
import RealRooted.Mathlib.RingTheory.MvPolynomial.Hyperbolic

/-!
# Dehomogenized BFJ output

This file packages the univariate polynomial obtained by setting the second
variable of the distinguished BFJ coefficient to one. It records the generic
scalar, degree, and coefficient-sign interfaces used by the numerator-product
argument.
-/

open Polynomial

namespace MvPolynomial

noncomputable section

/-- Dehomogenize the distinguished BFJ coefficient by evaluating it at
`(X, 1)`. -/
def bfjOutput {R : Type*} [CommSemiring R]
    (P Q : MvPolynomial (Fin 2) R) (b : ℕ) : R[X] :=
  MvPolynomial.aeval ![Polynomial.X, 1] (bfjCoefficient P Q b)

/-- The BFJ output is the affine-line restriction that sets the second
variable to one. -/
theorem bfjOutput_eq_affineLineRestriction
    {R : Type*} [CommSemiring R]
    (P Q : MvPolynomial (Fin 2) R) (b : ℕ) :
    bfjOutput P Q b =
      affineLineRestriction ![0, 1] ![1, 0] (bfjCoefficient P Q b) := by
  unfold bfjOutput affineLineRestriction
  simp only [aeval_def]
  congr 1
  funext i
  fin_cases i <;> simp

/-- Evaluation of the BFJ output is evaluation of its bivariate coefficient
at `(z, 1)`. -/
@[simp] theorem eval_bfjOutput
    {R : Type*} [CommSemiring R]
    (P Q : MvPolynomial (Fin 2) R) (b : ℕ) (z : R) :
    (bfjOutput P Q b).eval z =
      MvPolynomial.eval ![z, 1] (bfjCoefficient P Q b) := by
  rw [bfjOutput_eq_affineLineRestriction, eval_affineLineRestriction]
  apply congrArg (fun w : Fin 2 → R => MvPolynomial.eval w (bfjCoefficient P Q b))
  funext i
  fin_cases i <;> simp

/-- Mapping coefficients commutes with the dehomogenized BFJ output. -/
theorem map_bfjOutput {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (P Q : MvPolynomial (Fin 2) R) (b : ℕ) :
    Polynomial.map f (bfjOutput P Q b) =
      bfjOutput (map f P) (map f Q) b := by
  unfold bfjOutput
  rw [← map_bfjCoefficient]
  simp only [aeval_def]
  change (Polynomial.mapRingHom f)
      (MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, 1]
        (bfjCoefficient P Q b)) =
    MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, 1]
      (MvPolynomial.map f (bfjCoefficient P Q b))
  rw [MvPolynomial.map_eval₂Hom, MvPolynomial.eval₂Hom_map_hom]
  congr 1
  apply MvPolynomial.ringHom_ext'
  · ext r
    simp
  · intro i
    fin_cases i <;> simp

/-- The BFJ output is additive in its first input. -/
theorem bfjOutput_add_left {R : Type*} [CommSemiring R]
    (P P' Q : MvPolynomial (Fin 2) R) (b : ℕ) :
    bfjOutput (P + P') Q b = bfjOutput P Q b + bfjOutput P' Q b := by
  simp [bfjOutput, bfjCoefficient, bfjAuxiliary, addAuxiliary, add_mul]

/-- The BFJ output is additive in its second input. -/
theorem bfjOutput_add_right {R : Type*} [CommSemiring R]
    (P Q Q' : MvPolynomial (Fin 2) R) (b : ℕ) :
    bfjOutput P (Q + Q') b = bfjOutput P Q b + bfjOutput P Q' b := by
  simp [bfjOutput, bfjCoefficient, bfjAuxiliary, harmonicClear, mul_add]

/-- The BFJ output commutes with a scalar factor in its first input. -/
theorem bfjOutput_C_mul_left {R : Type*} [CommSemiring R]
    (c : R) (P Q : MvPolynomial (Fin 2) R) (b : ℕ) :
    bfjOutput (C c * P) Q b = Polynomial.C c * bfjOutput P Q b := by
  simp [bfjOutput, bfjCoefficient, bfjAuxiliary, addAuxiliary, mul_assoc]

/-- The BFJ output commutes with a scalar factor in its second input. -/
theorem bfjOutput_C_mul_right {R : Type*} [CommSemiring R]
    (c : R) (P Q : MvPolynomial (Fin 2) R) (b : ℕ) :
    bfjOutput P (C c * Q) b = Polynomial.C c * bfjOutput P Q b := by
  simp [bfjOutput, bfjCoefficient, bfjAuxiliary, harmonicClear, mul_assoc,
    mul_comm, mul_left_comm]

/-- The BFJ output distributes over a finite sum in its first input. -/
theorem bfjOutput_finsetSum_left {R ι : Type*} [CommSemiring R]
    (s : Finset ι) (P : ι → MvPolynomial (Fin 2) R)
    (Q : MvPolynomial (Fin 2) R) (b : ℕ) :
    bfjOutput (∑ i ∈ s, P i) Q b = ∑ i ∈ s, bfjOutput (P i) Q b := by
  classical
  induction s using Finset.induction with
  | empty => simp [bfjOutput, bfjCoefficient, bfjAuxiliary, addAuxiliary]
  | @insert i s hi ih => simp [hi, ih, bfjOutput_add_left]

/-- The BFJ output distributes over a finite sum in its second input. -/
theorem bfjOutput_finsetSum_right {R ι : Type*} [CommSemiring R]
    (s : Finset ι) (P : MvPolynomial (Fin 2) R)
    (Q : ι → MvPolynomial (Fin 2) R) (b : ℕ) :
    bfjOutput P (∑ i ∈ s, Q i) b = ∑ i ∈ s, bfjOutput P (Q i) b := by
  classical
  induction s using Finset.induction with
  | empty => simp [bfjOutput, bfjCoefficient, bfjAuxiliary, harmonicClear]
  | @insert i s hi ih => simp [hi, ih, bfjOutput_add_right]

/-- Homogeneous input degrees bound the degree of the dehomogenized BFJ
output. -/
theorem natDegree_bfjOutput_le {R : Type*} [CommSemiring R]
    {P Q : MvPolynomial (Fin 2) R} {a b : ℕ}
    (hP : P.IsHomogeneous a) (hQ : Q.IsHomogeneous b) :
    (bfjOutput P Q b).natDegree ≤ a + b := by
  have hhom := hP.bfjCoefficient hQ
  have hdegree := hhom.natDegree_affineLineRestriction_le ![0, 1] ![1, 0]
  rw [bfjOutput_eq_affineLineRestriction]
  exact hdegree

/-- The direct BFJ-output formula for two bounded monomials. -/
theorem bfjOutput_monomial_monomial
    {R : Type*} [CommSemiring R] (a b k l : ℕ) (hl : l ≤ b) :
    bfjOutput
      (X (0 : Fin 2) ^ k * X 1 ^ (a - k))
      (X (0 : Fin 2) ^ l * X 1 ^ (b - l)) b =
      ∑ j ∈ Finset.range (b + 1),
        (Nat.choose (b - l + k) j : R[X]) *
          (Nat.choose (a - k + l) (b - j) : R[X]) *
            Polynomial.X ^ (b + k - j) := by
  unfold bfjOutput bfjCoefficient bfjAuxiliary addAuxiliary harmonicClear
  change (MvPolynomial.aeval ![Polynomial.X, 1]).toRingHom
      (((optionEquivLeft R (Fin 2)) _).coeff (2 * b)) = _
  rw [← Polynomial.coeff_map]
  simp only [map_add, map_mul, map_pow, aeval_X, optionEquivLeft_X_some,
    optionEquivLeft_X_none, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_add, Polynomial.map_C, Polynomial.map_X,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  have hx0 : (MvPolynomial.aeval ![Polynomial.X, 1]).toRingHom
      (X (0 : Fin 2) : MvPolynomial (Fin 2) R) =
        (Polynomial.X : R[X]) := by simp
  have hx1 : (MvPolynomial.aeval ![Polynomial.X, 1]).toRingHom
      (X (1 : Fin 2) : MvPolynomial (Fin 2) R) = (1 : R[X]) := by simp
  rw [hx0, hx1]
  simp only [Polynomial.C_1, one_mul]
  have hzpow : (Polynomial.X : R[X][X]) ^ l * Polynomial.X ^ (b - l) =
      Polynomial.X ^ b := by
    rw [← pow_add]
    congr 1
    lia
  have hApow :
      (Polynomial.C (Polynomial.X : R[X]) + Polynomial.X) ^ k *
          (Polynomial.C Polynomial.X + Polynomial.X) ^ (b - l) =
        (Polynomial.X + Polynomial.C Polynomial.X) ^ (b - l + k) := by
    rw [← pow_add]
    congr 1
    · exact add_comm _ _
    · lia
  have hBpow :
      (1 + Polynomial.X : R[X][X]) ^ (a - k) *
          (1 + Polynomial.X) ^ l =
        (1 + Polynomial.X) ^ (a - k + l) := by
    rw [← pow_add]
  have hnormal :
      (Polynomial.C Polynomial.X + Polynomial.X) ^ k *
            (1 + Polynomial.X) ^ (a - k) *
          ((Polynomial.C Polynomial.X * Polynomial.X * (1 + Polynomial.X)) ^ l *
            (Polynomial.X * (Polynomial.C Polynomial.X + Polynomial.X)) ^ (b - l)) =
        Polynomial.X ^ b *
          (Polynomial.C ((Polynomial.X : R[X]) ^ l) *
            ((Polynomial.X + Polynomial.C Polynomial.X) ^ (b - l + k) *
              (1 + Polynomial.X) ^ (a - k + l))) := by
    calc
      _ = (Polynomial.C Polynomial.X) ^ l *
            (Polynomial.X ^ l * Polynomial.X ^ (b - l)) *
              ((Polynomial.C Polynomial.X + Polynomial.X) ^ k *
                (Polynomial.C Polynomial.X + Polynomial.X) ^ (b - l)) *
                  ((1 + Polynomial.X) ^ (a - k) *
                    (1 + Polynomial.X) ^ l) := by
        simp only [mul_pow]
        ring
      _ = _ := by
        rw [hzpow, hApow, hBpow, map_pow]
        ring
  rw [hnormal, show 2 * b = b + b by lia, Polynomial.coeff_X_pow_mul,
    Polynomial.coeff_C_mul, Polynomial.coeff_mul, Finset.mul_sum,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hjA : j ≤ b - l + k
  · have hexp : l + (b - l + k - j) = b + k - j := by lia
    rw [Polynomial.coeff_X_add_C_pow, Polynomial.coeff_one_add_X_pow]
    have hpow : (Polynomial.X : R[X]) ^ l *
        Polynomial.X ^ (b - l + k - j) = Polynomial.X ^ (b + k - j) := by
      rw [← pow_add, hexp]
    calc
      _ = (Polynomial.X ^ l * Polynomial.X ^ (b - l + k - j)) *
          (Nat.choose (b - l + k) j : R[X]) *
            (Nat.choose (a - k + l) (b - j) : R[X]) := by ring
      _ = _ := by rw [hpow]; ring
  · have hAj : b - l + k < j := Nat.lt_of_not_ge hjA
    rw [Polynomial.coeff_X_add_C_pow, Polynomial.coeff_one_add_X_pow,
      Nat.choose_eq_zero_of_lt hAj]
    simp

/-- The monomial BFJ-output formula reindexed on its exact support. -/
theorem bfjOutput_monomial_monomial_guarded
    {R : Type*} [CommSemiring R] (a b k l : ℕ)
    (hk : k ≤ a) (hl : l ≤ b) :
    bfjOutput
      (X (0 : Fin 2) ^ k * X 1 ^ (a - k))
      (X (0 : Fin 2) ^ l * X 1 ^ (b - l)) b =
      ∑ i ∈ Finset.Icc (max k l) (min (a + l) (b + k)),
        (Nat.choose (a - k + l) (i - k) : R[X]) *
          (Nat.choose (b - l + k) (i - l) : R[X]) * Polynomial.X ^ i := by
  rw [bfjOutput_monomial_monomial a b k l hl]
  exact Nat.sum_range_shifted_choose_reindex a b k l hk hl
    (fun i => (Polynomial.X : R[X]) ^ i)

namespace HasNonnegCoeffs

/-- Dehomogenizing the distinguished BFJ coefficient preserves
coefficientwise nonnegativity. -/
theorem bfjOutput {P Q : MvPolynomial (Fin 2) ℝ}
    (hP : HasNonnegCoeffs P) (hQ : HasNonnegCoeffs Q) (b : ℕ) :
    RealRooted.HasNonnegCoeffs (MvPolynomial.bfjOutput P Q b) := by
  exact (hP.bfjCoefficient hQ b).aeval_X_one

end HasNonnegCoeffs

end

end MvPolynomial
