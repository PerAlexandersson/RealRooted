module

public import RealRooted.HermiteBiehler

/-!
# Hermite--Biehler tactic frontends

Thin wrappers around the checked Hermite--Biehler forward, converse, and
odd/even Hurwitz bridges.
-/

public section

open Polynomial

namespace RealRooted
namespace Tactic

/-- If `p` and `q` have nonnegative coefficients and their Hermite--Biehler polynomial is
upper-half-plane stable, then their odd-even polynomial is Hurwitz stable. -/
theorem hermiteBiehlerOddEven_isHurwitzStable {p q : ℝ[X]}
    (hp : HasNonnegCoeffs p) (hq : HasNonnegCoeffs q)
    (hstable : IsUpperHalfPlaneStable (hermiteBiehlerPolynomial q p)) :
    IsHurwitzStable (oddEvenPolynomial p q) :=
  ⟨hasNonnegCoeffs_oddEvenPolynomial hp hq,
    hermiteBiehlerStableToHurwitzOddEven hp hq hstable⟩

/-- Pointwise Hermite--Biehler forward implication for sequences with positive leading
coefficients and the indicated strict interlacing orientation. -/
theorem hermiteBiehlerForwardPos_sequence {F G : Nat → ℝ[X]}
    (hF : ∀ n : Nat, HasPosLeadingCoeff (F n))
    (hG : ∀ n : Nat, HasPosLeadingCoeff (G n))
    (hstrictInterl : ∀ n : Nat, StrictInterl (G n) (F n)) :
    ∀ n : Nat, IsUpperHalfPlaneStable (hermiteBiehlerPolynomial (F n) (G n)) :=
  fun n => RealRooted.hermiteBiehlerForwardPos (hF n) (hG n) (hstrictInterl n)

/-- Pointwise Hermite--Biehler converse for sequences with positive leading coefficients and
upper-half-plane-stable Hermite--Biehler polynomials. -/
theorem hermiteBiehlerConverse_sequence {F G : Nat → ℝ[X]}
    (hF : ∀ n : Nat, HasPosLeadingCoeff (F n))
    (hG : ∀ n : Nat, HasPosLeadingCoeff (G n))
    (hstable :
      ∀ n : Nat, IsUpperHalfPlaneStable (hermiteBiehlerPolynomial (F n) (G n))) :
    ∀ n : Nat, StrictInterl (G n) (F n) ∨ StrictInterl (F n) (G n) :=
  fun n => RealRooted.hermiteBiehlerConverse (hF n) (hG n) (hstable n)

/-- Under positive-leading-coefficient and stability hypotheses, both members of each
Hermite--Biehler pair split. -/
theorem hermiteBiehlerSplits_sequence {F G : Nat → ℝ[X]}
    (hF : ∀ n : Nat, HasPosLeadingCoeff (F n))
    (hG : ∀ n : Nat, HasPosLeadingCoeff (G n))
    (hstable :
      ∀ n : Nat, IsUpperHalfPlaneStable (hermiteBiehlerPolynomial (F n) (G n))) :
    ∀ n : Nat, (F n).Splits ∧ (G n).Splits :=
  fun n => RealRooted.splits_of_stable (hF n) (hG n) (hstable n)

/-- Under positive-leading-coefficient and stability hypotheses, with each `F n` of positive
degree, `G n` strictly interlaces `F n`. -/
theorem hermiteBiehlerStrictInterl_sequence {F G : Nat → ℝ[X]}
    (hF : ∀ n : Nat, HasPosLeadingCoeff (F n))
    (hG : ∀ n : Nat, HasPosLeadingCoeff (G n))
    (hstable :
      ∀ n : Nat, IsUpperHalfPlaneStable (hermiteBiehlerPolynomial (F n) (G n)))
    (hdegree : ∀ n : Nat, 1 ≤ (F n).natDegree) :
    ∀ n : Nat, StrictInterl (G n) (F n) :=
  fun n => RealRooted.strictInterl_of_stable_general (hF n) (hG n) (hstable n) (hdegree n)

/-- Nonnegative coefficients and upper-half-plane stability of each Hermite--Biehler polynomial
give right-half-plane stability of the complexified odd-even polynomial. -/
theorem hermiteBiehlerOddEven_rightHalfPlaneStable_sequence {P Q : Nat → ℝ[X]}
    (hP : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hQ : ∀ n : Nat, HasNonnegCoeffs (Q n))
    (hstable :
      ∀ n : Nat, IsUpperHalfPlaneStable (hermiteBiehlerPolynomial (Q n) (P n))) :
    ∀ n : Nat,
      IsRightHalfPlaneStable (complexify (oddEvenPolynomial (P n) (Q n))) :=
  fun n => RealRooted.hermiteBiehlerStableToHurwitzOddEven (hP n) (hQ n) (hstable n)

/-- Nonnegative coefficients and upper-half-plane stability of each Hermite--Biehler polynomial
give Hurwitz stability of the corresponding odd-even polynomial. -/
theorem hermiteBiehlerOddEven_isHurwitzStable_sequence {P Q : Nat → ℝ[X]}
    (hP : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hQ : ∀ n : Nat, HasNonnegCoeffs (Q n))
    (hstable :
      ∀ n : Nat, IsUpperHalfPlaneStable (hermiteBiehlerPolynomial (Q n) (P n))) :
    ∀ n : Nat, IsHurwitzStable (oddEvenPolynomial (P n) (Q n)) :=
  fun n => hermiteBiehlerOddEven_isHurwitzStable (hP n) (hQ n) (hstable n)

end Tactic
end RealRooted
namespace RealRooted
namespace Tactic

end Tactic
end RealRooted
