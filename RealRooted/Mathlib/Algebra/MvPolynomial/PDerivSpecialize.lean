import RealRooted.Mathlib.Algebra.MvPolynomial.PDeriv
import RealRooted.Mathlib.Algebra.MvPolynomial.Specialize

/-!
# Partial derivatives and scalar specialization

This file keeps the interaction between partial differentiation and scalar
specialization separate from the basic specialization API.
-/

namespace MvPolynomial

/-- Differentiating in a specialized coordinate gives zero. -/
@[simp] theorem pderiv_specializeAt_self {σ R : Type*} [CommSemiring R]
    (i : σ) (c : R) (P : MvPolynomial σ R) :
    pderiv i (specializeAt i c P) = 0 := by
  classical
  induction P using MvPolynomial.induction_on with
  | C r => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P j hP =>
      by_cases hji : j = i
      · subst j
        simp [hP]
      · simp [hP, hji]

/-- Partial differentiation commutes with specialization in a different
coordinate. -/
theorem pderiv_specializeAt_of_ne {σ R : Type*} [CommSemiring R]
    {i j : σ} (hij : i ≠ j) (c : R) (P : MvPolynomial σ R) :
    pderiv i (specializeAt j c P) = specializeAt j c (pderiv i P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C r => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P k hP =>
      by_cases hkj : k = j
      · subst k
        simp [hP, hij]
      · by_cases hki : k = i
        · subst k
          simp [hP, hkj]
        · simp [hP, hki, hkj]

end MvPolynomial
