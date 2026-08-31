import RealRooted.BorceaBranden.Applications.BidiagonalSymbol
import RealRooted.BorceaBranden.Applications.RealUnivariateSymbol.Interlacing

/-!
# Real consequences of stable affine bidiagonal symbols

The affine-symbol calculation lives in `BidiagonalSymbol`; this module applies
the general real finite-symbol preservation theorems to that operator.
-/

open Polynomial

noncomputable section

namespace RealRooted.BorceaBranden

/-- A stable genuine affine algebraic symbol makes the associated real
bidiagonal operator preserve splitness up to the zero output. -/
theorem bidiagonalOperator_splits_of_affineSymbol_stable
    {alpha beta : ℕ → ℝ} {d : ℕ} {p : ℝ[X]}
    (hSymbol : MvUpperHalfPlaneStable
      (complexifyMv
        (Challenges.BorceaBranden.finiteAlgebraicSymbol d
          (bidiagonalLinearMap alpha beta))))
    (hpdeg : p.natDegree ≤ d) (hp : p.Splits) :
    bidiagonalOperator alpha beta p = 0 ∨
      (bidiagonalOperator alpha beta p).Splits :=
  linearMap_splits_of_finiteSymbol_stable hSymbol hpdeg hp

/-- With nonnegative bidiagonal coefficients, affine-symbol stability gives a
PF-preserving operator on the chosen degree box. -/
theorem bidiagonalOperator_isPF_of_affineSymbol_stable
    {alpha beta : ℕ → ℝ} {d : ℕ} {p : ℝ[X]}
    (hSymbol : MvUpperHalfPlaneStable
      (complexifyMv
        (Challenges.BorceaBranden.finiteAlgebraicSymbol d
          (bidiagonalLinearMap alpha beta))))
    (halpha : ∀ k, 0 ≤ alpha k) (hbeta : ∀ k, 0 ≤ beta k)
    (hpdeg : p.natDegree ≤ d) (hp : IsPFPolynomial p) :
    IsPFPolynomial (bidiagonalOperator alpha beta p) := by
  by_cases hp0 : p = 0
  · simpa [hp0] using IsPFPolynomial.zero
  apply IsPFPolynomial.of_realRooted_nonneg
  · exact hp.hasNonnegCoeffs.bidiagonalOperator halpha hbeta
  · rcases bidiagonalOperator_splits_of_affineSymbol_stable
        hSymbol hpdeg (hp.eq_zero_or_splits.resolve_left hp0) with hzero | hsplits
    · simp [hzero]
    · exact hsplits

/-- A stable affine symbol provides a degree-bounded PF preserver when the
relevant bidiagonal weights are nonnegative on that degree box. -/
theorem bidiagonalPFPreserver_of_affineSymbol
    {alpha beta : ℕ → ℝ} {d : ℕ}
    (hSymbol : MvUpperHalfPlaneStable
      (complexifyMv
        (Challenges.BorceaBranden.finiteAlgebraicSymbol d
          (bidiagonalLinearMap alpha beta))))
    (halpha : ∀ k, k ≤ d → 0 ≤ alpha k)
    (hbeta : ∀ k, k ≤ d → 0 ≤ beta k) :
    BidiagonalPFPreserver alpha beta d := by
  intro p hp hdeg
  by_cases hp0 : p = 0
  · simpa [hp0] using IsPFPolynomial.zero
  apply IsPFPolynomial.of_realRooted_nonneg
  · exact hp.hasNonnegCoeffs.bidiagonalOperator_of_degree_le hdeg halpha hbeta
  · rcases bidiagonalOperator_splits_of_affineSymbol_stable
        hSymbol hdeg (hp.eq_zero_or_splits.resolve_left hp0) with hzero | hsplits
    · simp [hzero]
    · exact hsplits

/-- A genuine stable affine symbol preserves an oriented interlacing pair when
the two nonzero outputs have positive leading coefficients. -/
theorem bidiagonalOperator_prec_of_affineSymbol_stable
    {alpha beta : ℕ → ℝ} {d : ℕ} {p q : ℝ[X]}
    (hSymbol : MvUpperHalfPlaneStable
      (complexifyMv
        (Challenges.BorceaBranden.finiteAlgebraicSymbol d
          (bidiagonalLinearMap alpha beta))))
    (hpdeg : p.natDegree ≤ d) (hqdeg : q.natDegree ≤ d)
    (hpq : Prec q p)
    (hp : HasPosLeadingCoeff p) (hq : HasPosLeadingCoeff q)
    (hpout : HasPosLeadingCoeff (bidiagonalOperator alpha beta p))
    (hqout : HasPosLeadingCoeff (bidiagonalOperator alpha beta q))
    (hpoutdeg : 1 ≤ (bidiagonalOperator alpha beta p).natDegree) :
    Prec (bidiagonalOperator alpha beta q) (bidiagonalOperator alpha beta p) :=
  linearMap_prec_of_finiteSymbol_stable
    hSymbol hpdeg hqdeg hpq hp hq hpout hqout hpoutdeg

end RealRooted.BorceaBranden

namespace RealRooted

/-- Compatibility wrapper for the affine-symbol PF-preserver theorem. The
finite-symbol application theorem is owned by `BorceaBranden`. -/
theorem bidiagonalPFPreserver_of_affineSymbol
    {alpha beta : ℕ → ℝ} {d : ℕ}
    (hSymbol : MvUpperHalfPlaneStable
      (complexifyMv
        (Challenges.BorceaBranden.finiteAlgebraicSymbol d
          (BorceaBranden.bidiagonalLinearMap alpha beta))))
    (halpha : ∀ k, k ≤ d → 0 ≤ alpha k)
    (hbeta : ∀ k, k ≤ d → 0 ≤ beta k) :
    BidiagonalPFPreserver alpha beta d :=
  BorceaBranden.bidiagonalPFPreserver_of_affineSymbol hSymbol halpha hbeta

end RealRooted
