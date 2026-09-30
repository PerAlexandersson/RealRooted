import RealRooted.BorceaBranden.Applications.BidiagonalSymbol.RealConsequences

/-!
# Compatibility facade for affine finite-symbol consequences

The generic real finite-symbol API now lives in
`BorceaBranden.Applications.RealUnivariateSymbol` and its `Interlacing` child.
The bidiagonal consequences live in `BidiagonalSymbol.RealConsequences`.
This module preserves the older import path and declaration names.
-/

open Polynomial

noncomputable section

namespace RealRooted

namespace BorceaBranden

/-- Compatibility name for `complexificationLinearMap`. -/
noncomputable abbrev complexifyLinearMap
    (T : ℝ[X] →ₗ[ℝ] ℝ[X]) : ℂ[X] →ₗ[ℂ] ℂ[X] :=
  complexificationLinearMap T

@[simp] lemma complexifyLinearMap_monomial
    (T : ℝ[X] →ₗ[ℝ] ℝ[X]) (n : ℕ) (z : ℂ) :
    complexifyLinearMap T (Polynomial.monomial n z) =
      C z * complexify (T (X ^ n)) :=
  complexificationLinearMap_monomial T n z

@[simp] lemma complexifyLinearMap_X_pow
    (T : ℝ[X] →ₗ[ℝ] ℝ[X]) (n : ℕ) :
    complexifyLinearMap T ((X : ℂ[X]) ^ n) =
      complexify (T ((X : ℝ[X]) ^ n)) := by
  rw [Polynomial.X_pow_eq_monomial, complexifyLinearMap_monomial]
  simp

lemma complexifyLinearMap_complexify
    (T : ℝ[X] →ₗ[ℝ] ℝ[X]) (p : ℝ[X]) :
    complexifyLinearMap T (complexify p) = complexify (T p) :=
  complexificationLinearMap_complexify T p

/-- The complex degree-box bidiagonal operator is the complexification of the
real bidiagonal operator on a degree-bounded real input. -/
lemma complexBidiagonalDegreeBox_value
    (alpha beta : ℕ → ℝ) (d : ℕ) (p : ℝ[X])
    (hpdeg : p.natDegree ≤ d) :
    let f : MvPolynomial.degreeOfLE (Fin 1) ℂ (fun _ => d) :=
      ⟨(MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm (complexify p), by
        rw [MvPolynomial.mem_degreeOfLE_iff_degreeOf]
        intro i
        rw [Subsingleton.elim i default,
          MvPolynomial.degreeOf_uniqueAlgEquiv_symm]
        simpa [complexify] using hpdeg⟩
    MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)
        (complexUnivariateDegreeBoxOperator d
          (complexBidiagonalLinearMap alpha beta) f) =
      complexify (bidiagonalOperator alpha beta p) := by
  simp only [complexUnivariateDegreeBoxOperator, LinearMap.coe_mk,
    AddHom.coe_mk, AlgEquiv.apply_symm_apply]
  change complexBidiagonalLinearMap alpha beta (complexify p) = _
  apply Polynomial.ext
  intro k
  cases k with
  | zero => simp [complexBidiagonalLinearMap, bidiagonalOperator, complexify]
  | succ k =>
      simp [complexBidiagonalLinearMap, bidiagonalOperator, complexify,
        coeff_X_mul]

/-- The complex degree-box bidiagonal operator commutes with the
Hermite--Biehler combination of two real inputs. -/
lemma complexBidiagonalDegreeBox_hermiteBiehler_value
    (alpha beta : ℕ → ℝ) (d : ℕ) (p q : ℝ[X])
    (hpdeg : p.natDegree ≤ d) (hqdeg : q.natDegree ≤ d) :
    let f : MvPolynomial.degreeOfLE (Fin 1) ℂ (fun _ => d) :=
      ⟨(MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm
          (hermiteBiehlerPolynomial p q), by
        rw [MvPolynomial.mem_degreeOfLE_iff_degreeOf]
        intro i
        rw [Subsingleton.elim i default,
          MvPolynomial.degreeOf_uniqueAlgEquiv_symm]
        simpa using
          hermiteBiehlerPolynomial_natDegree_le hpdeg hqdeg⟩
    MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)
        (complexUnivariateDegreeBoxOperator d
          (complexBidiagonalLinearMap alpha beta) f) =
      hermiteBiehlerPolynomial
        (bidiagonalOperator alpha beta p)
        (bidiagonalOperator alpha beta q) := by
  simp only [complexUnivariateDegreeBoxOperator, LinearMap.coe_mk,
    AddHom.coe_mk, AlgEquiv.apply_symm_apply]
  apply Polynomial.ext
  intro k
  cases k with
  | zero =>
      simp [complexBidiagonalLinearMap, bidiagonalOperator,
        hermiteBiehlerPolynomial, complexify]
      ring
  | succ k =>
      simp [complexBidiagonalLinearMap, bidiagonalOperator,
        hermiteBiehlerPolynomial, complexify, coeff_X_mul]
      ring

end BorceaBranden

end RealRooted
