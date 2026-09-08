import RealRooted.ClassicalHurwitzMatrix.Stability.Rotation
import RealRooted.HermiteBiehler.Converse

/-!
# Hermite--Biehler consequences of strict Hurwitz stability

This module transports the rotated odd/even polynomial into the existing
Hermite--Biehler converse. Leading-coefficient sign choices stay explicit: the
two useful normalizations are the original rotated pair and the pair obtained
by multiplying its Hermite--Biehler polynomial by `i`.
-/

open Polynomial

noncomputable section

namespace RealRooted

@[simp]
theorem leadingCoeff_hurwitzRotatedEvenPart (p : ℝ[X]) :
    (hurwitzRotatedEvenPart p).leadingCoeff =
      p.leadingCoeff * (-1) ^ p.natDegree := by
  rw [hurwitzRotatedEvenPart, Polynomial.leadingCoeff_comp]
  · simp
  · simp

@[simp]
theorem leadingCoeff_hurwitzRotatedOddPart (p : ℝ[X]) :
    (hurwitzRotatedOddPart p).leadingCoeff =
      -(p.leadingCoeff * (-1) ^ p.natDegree) := by
  rw [hurwitzRotatedOddPart, Polynomial.leadingCoeff_mul,
    Polynomial.leadingCoeff_neg, Polynomial.leadingCoeff_X,
    Polynomial.leadingCoeff_comp]
  · simp
  · simp

/-- The parity sign normalizes the leading coefficient of the rotated even
part back to the leading coefficient of the original polynomial. -/
theorem hasPosLeadingCoeff_sign_mul_hurwitzRotatedEvenPart {p : ℝ[X]}
    (hp : HasPosLeadingCoeff p) :
    HasPosLeadingCoeff
      (C ((-1 : ℝ) ^ p.natDegree) * hurwitzRotatedEvenPart p) := by
  have hs : ((-1 : ℝ) ^ p.natDegree) * (-1 : ℝ) ^ p.natDegree = 1 := by
    rw [← pow_add]
    simp [← two_mul]
  unfold HasPosLeadingCoeff at hp ⊢
  rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
    leadingCoeff_hurwitzRotatedEvenPart, mul_left_comm, hs, mul_one]
  exact hp

/-- The opposite parity sign normalizes the leading coefficient of the rotated
odd part back to the leading coefficient of the original polynomial. -/
theorem hasPosLeadingCoeff_neg_sign_mul_hurwitzRotatedOddPart {p : ℝ[X]}
    (hp : HasPosLeadingCoeff p) :
    HasPosLeadingCoeff
      (C (-((-1 : ℝ) ^ p.natDegree)) * hurwitzRotatedOddPart p) := by
  have hs : ((-1 : ℝ) ^ p.natDegree) * (-1 : ℝ) ^ p.natDegree = 1 := by
    rw [← pow_add]
    simp [← two_mul]
  unfold HasPosLeadingCoeff at hp ⊢
  rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
    leadingCoeff_hurwitzRotatedOddPart, neg_mul_neg, mul_left_comm, hs,
    mul_one]
  exact hp

namespace IsUpperHalfPlaneStable

/-- Multiplication by a nonzero constant preserves upper-half-plane stability. -/
theorem C_mul {p : ℂ[X]} (hp : IsUpperHalfPlaneStable p)
    {c : ℂ} (hc : c ≠ 0) :
    IsUpperHalfPlaneStable (C c * p) := by
  intro z hz
  simp only [eval_mul, eval_C]
  exact mul_ne_zero hc (hp z hz)

end IsUpperHalfPlaneStable

/-- Multiplication by `i` swaps the two Hermite--Biehler parts and negates the
new real part. -/
theorem C_I_mul_hermiteBiehlerPolynomial (f g : ℝ[X]) :
    C Complex.I * hermiteBiehlerPolynomial f g =
      hermiteBiehlerPolynomial (-g) f := by
  simp only [hermiteBiehlerPolynomial, complexify, Polynomial.map_neg]
  rw [mul_add, ← mul_assoc, ← C_mul, Complex.I_mul_I]
  simp [add_comm]

/-- Scaling both real parts scales their Hermite--Biehler polynomial by the
same real constant. -/
theorem hermiteBiehlerPolynomial_C_mul (a : ℝ) (f g : ℝ[X]) :
    hermiteBiehlerPolynomial (C a * f) (C a * g) =
      C (a : ℂ) * hermiteBiehlerPolynomial f g := by
  simp [hermiteBiehlerPolynomial, complexify]
  ring

/-- With positive leading coefficients in the direct normalization, strict
Hurwitz stability forces the rotated odd part to be in proper position with
respect to the rotated even part. -/
theorem IsStrictlyHurwitzStable.prec_rotatedParts_of_posLeading
    {odd even : ℝ[X]}
    (h : IsStrictlyHurwitzStable (oddEvenPolynomial odd even))
    (heven : HasPosLeadingCoeff (hurwitzRotatedEvenPart even))
    (hodd : HasPosLeadingCoeff (hurwitzRotatedOddPart odd))
    (hdegree : 1 ≤ (hurwitzRotatedEvenPart even).natDegree) :
    Prec (hurwitzRotatedOddPart odd) (hurwitzRotatedEvenPart even) :=
  prec_of_stable_general heven hodd
    h.upperHalfPlaneStable_rotatedParts hdegree

/-- With positive leading coefficients after multiplication by `i`, strict
Hurwitz stability forces the rotated even part to be in proper position with
respect to the negated rotated odd part. -/
theorem IsStrictlyHurwitzStable.prec_rotatedParts_swapped_of_posLeading
    {odd even : ℝ[X]}
    (h : IsStrictlyHurwitzStable (oddEvenPolynomial odd even))
    (hodd : HasPosLeadingCoeff (-hurwitzRotatedOddPart odd))
    (heven : HasPosLeadingCoeff (hurwitzRotatedEvenPart even))
    (hdegree : 1 ≤ (-hurwitzRotatedOddPart odd).natDegree) :
    Prec (hurwitzRotatedEvenPart even) (-hurwitzRotatedOddPart odd) := by
  apply prec_of_stable_general hodd heven _ hdegree
  rw [← C_I_mul_hermiteBiehlerPolynomial]
  exact h.upperHalfPlaneStable_rotatedParts.C_mul (by simp)

/-- In the even-degree parity shape, strict stability and positive leading
coefficients force the rotated odd part to precede the rotated even part. -/
theorem IsStrictlyHurwitzStable.prec_rotatedParts_of_evenShape
    {odd even : ℝ[X]}
    (h : IsStrictlyHurwitzStable (oddEvenPolynomial odd even))
    (hodd : HasPosLeadingCoeff odd) (heven : HasPosLeadingCoeff even)
    (hdegree : even.natDegree = odd.natDegree + 1) :
    Prec (hurwitzRotatedOddPart odd) (hurwitzRotatedEvenPart even) := by
  let s : ℝ := (-1 : ℝ) ^ even.natDegree
  have hs0 : s ≠ 0 := pow_ne_zero _ (by norm_num)
  have hsquare : s * s = 1 := by
    dsimp [s]
    rw [← pow_add]
    simp [← two_mul]
  have hsign : s = -((-1 : ℝ) ^ odd.natDegree) := by
    simp only [s, hdegree, pow_succ]
    ring
  have hstable : IsUpperHalfPlaneStable
      (hermiteBiehlerPolynomial
        (Polynomial.C s * hurwitzRotatedEvenPart even)
        (Polynomial.C s * hurwitzRotatedOddPart odd)) := by
    rw [hermiteBiehlerPolynomial_C_mul]
    exact h.upperHalfPlaneStable_rotatedParts.C_mul (by exact_mod_cast hs0)
  have heven' : HasPosLeadingCoeff
      (Polynomial.C s * hurwitzRotatedEvenPart even) := by
    simpa only [s] using
      hasPosLeadingCoeff_sign_mul_hurwitzRotatedEvenPart heven
  have hodd' : HasPosLeadingCoeff
      (Polynomial.C s * hurwitzRotatedOddPart odd) := by
    rw [hsign]
    exact hasPosLeadingCoeff_neg_sign_mul_hurwitzRotatedOddPart hodd
  have hdegree' : 1 ≤
      (Polynomial.C s * hurwitzRotatedEvenPart even).natDegree := by
    rw [Polynomial.natDegree_C_mul hs0, hurwitzRotatedEvenPart,
      Polynomial.natDegree_comp]
    simp only [natDegree_neg, natDegree_pow, natDegree_X]
    lia
  have hprec : Prec
      (Polynomial.C s * hurwitzRotatedOddPart odd)
      (Polynomial.C s * hurwitzRotatedEvenPart even) :=
    prec_of_stable_general heven' hodd' hstable hdegree'
  have hscaled := (hprec.C_mul_left hs0).C_mul_right hs0
  simpa [← mul_assoc, ← Polynomial.C_mul, hsquare] using hscaled

/-- In the odd-degree parity shape, strict stability and positive leading
coefficients force the rotated even part to precede the rotated odd part. -/
theorem IsStrictlyHurwitzStable.prec_rotatedParts_of_oddShape
    {odd even : ℝ[X]}
    (h : IsStrictlyHurwitzStable (oddEvenPolynomial odd even))
    (hodd : HasPosLeadingCoeff odd) (heven : HasPosLeadingCoeff even)
    (hdegree : even.natDegree = odd.natDegree) :
    Prec (hurwitzRotatedEvenPart even) (hurwitzRotatedOddPart odd) := by
  let s : ℝ := (-1 : ℝ) ^ odd.natDegree
  have hs0 : s ≠ 0 := pow_ne_zero _ (by norm_num)
  have hsquare : s * s = 1 := by
    dsimp [s]
    rw [← pow_add]
    simp [← two_mul]
  have hswap : IsUpperHalfPlaneStable
      (hermiteBiehlerPolynomial
        (-hurwitzRotatedOddPart odd) (hurwitzRotatedEvenPart even)) := by
    rw [← C_I_mul_hermiteBiehlerPolynomial]
    exact h.upperHalfPlaneStable_rotatedParts.C_mul (by simp)
  have hstable : IsUpperHalfPlaneStable
      (hermiteBiehlerPolynomial
        (Polynomial.C s * -hurwitzRotatedOddPart odd)
        (Polynomial.C s * hurwitzRotatedEvenPart even)) := by
    rw [hermiteBiehlerPolynomial_C_mul]
    exact hswap.C_mul (by exact_mod_cast hs0)
  have hodd' : HasPosLeadingCoeff
      (Polynomial.C s * -hurwitzRotatedOddPart odd) := by
    unfold HasPosLeadingCoeff at hodd ⊢
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      Polynomial.leadingCoeff_neg,
      leadingCoeff_hurwitzRotatedOddPart]
    simp only [neg_neg]
    rw [mul_left_comm, hsquare, mul_one]
    exact hodd
  have heven' : HasPosLeadingCoeff
      (Polynomial.C s * hurwitzRotatedEvenPart even) := by
    simpa only [s, hdegree] using
      hasPosLeadingCoeff_sign_mul_hurwitzRotatedEvenPart heven
  have hcomp_ne : odd.comp (-(X ^ 2)) ≠ 0 := by
    apply Polynomial.leadingCoeff_ne_zero.mp
    rw [Polynomial.leadingCoeff_comp]
    · exact mul_ne_zero hodd.ne' (pow_ne_zero _ (by norm_num))
    · simp
  have hdegree' : 1 ≤
      (Polynomial.C s * -hurwitzRotatedOddPart odd).natDegree := by
    rw [Polynomial.natDegree_C_mul hs0, natDegree_neg,
      hurwitzRotatedOddPart,
      Polynomial.natDegree_mul (by simp) hcomp_ne,
      natDegree_neg, Polynomial.natDegree_comp]
    simp only [natDegree_neg, natDegree_pow, natDegree_X]
    lia
  have hprec : Prec
      (Polynomial.C s * hurwitzRotatedEvenPart even)
      (Polynomial.C s * -hurwitzRotatedOddPart odd) :=
    prec_of_stable_general hodd' heven' hstable hdegree'
  have hscaled := (hprec.C_mul_left hs0).C_mul_right hs0
  have hneg : Prec
      (hurwitzRotatedEvenPart even) (-hurwitzRotatedOddPart odd) := by
    simpa [← mul_assoc, ← Polynomial.C_mul, hsquare] using hscaled
  simpa using hneg.C_mul_right (a := -1) (by norm_num)

end RealRooted
