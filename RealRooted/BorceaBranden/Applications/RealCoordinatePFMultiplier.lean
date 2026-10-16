import RealRooted.BorceaBranden.Applications.CoordinatePFMultiplier

/-!
# Real coordinate PF multipliers

This file supplies the real-coefficient companion to the complex coordinate
multiplier used by the finite-symbol stability theorem.
-/

namespace RealRooted.BorceaBranden

noncomputable section

/-- Apply a real diagonal sequence to one exponent coordinate of a real
multivariate polynomial. -/
def realCoordinateDiagonalOperator {σ : Type*} (gamma : ℕ → ℝ) (q : σ)
    (p : _root_.MvPolynomial σ ℝ) : _root_.MvPolynomial σ ℝ :=
  p.coeff.sum fun m a => _root_.MvPolynomial.monomial m (gamma (m q) * a)

@[simp]
theorem coeff_realCoordinateDiagonalOperator {σ : Type*} (gamma : ℕ → ℝ)
    (q : σ) (p : _root_.MvPolynomial σ ℝ) (m : σ →₀ ℕ) :
    (realCoordinateDiagonalOperator gamma q p).coeff m =
      gamma (m q) * p.coeff m := by
  classical
  rw [realCoordinateDiagonalOperator, _root_.MvPolynomial.sum_def,
    _root_.MvPolynomial.coeff_sum]
  by_cases hm : m ∈ p.support
  · simp [hm, _root_.MvPolynomial.coeff_monomial]
  · have hcoeff : p.coeff m = 0 := Finsupp.notMem_support_iff.mp hm
    simp [hm, hcoeff, _root_.MvPolynomial.coeff_monomial]

/-- Coordinate diagonal operators commute, including when the two selected
coordinates coincide. -/
theorem realCoordinateDiagonalOperator_comm {σ : Type*}
    (gamma delta : ℕ → ℝ) (i j : σ) (p : _root_.MvPolynomial σ ℝ) :
    realCoordinateDiagonalOperator gamma i
        (realCoordinateDiagonalOperator delta j p) =
      realCoordinateDiagonalOperator delta j
        (realCoordinateDiagonalOperator gamma i p) := by
  ext m
  simp only [coeff_realCoordinateDiagonalOperator]
  ring

/-- Complexification commutes with a real coordinate diagonal action. -/
theorem complexifyMv_realCoordinateDiagonalOperator {σ : Type*}
    (gamma : ℕ → ℝ) (q : σ) (p : _root_.MvPolynomial σ ℝ) :
    complexifyMv (realCoordinateDiagonalOperator gamma q p) =
      coordinateDiagonalOperator gamma q (complexifyMv p) := by
  ext m
  rw [coeff_coordinateDiagonalOperator]
  simp only [complexifyMv, _root_.MvPolynomial.coeff_map,
    coeff_realCoordinateDiagonalOperator, map_mul, Complex.ofRealHom_eq_coe]

/-- A coordinate diagonal action is nonzero if its diagonal entries and its
input are nonzero. -/
theorem realCoordinateDiagonalOperator_ne_zero {σ : Type*}
    {gamma : ℕ → ℝ} (hgamma : ∀ k, gamma k ≠ 0) (q : σ)
    {p : _root_.MvPolynomial σ ℝ} (hp : p ≠ 0) :
    realCoordinateDiagonalOperator gamma q p ≠ 0 := by
  intro hzero
  apply hp
  ext m
  have hcoeff := congrArg
    (fun r : _root_.MvPolynomial σ ℝ => r.coeff m) hzero
  simp only [coeff_realCoordinateDiagonalOperator] at hcoeff
  simp only [AddMonoidAlgebra.coeff_zero] at hcoeff
  exact (mul_eq_zero.mp hcoeff).resolve_left (hgamma (m q))

/-- An infinite PF multiplier sequence tensorizes over real multivariate
polynomials, in one coordinate at a time. -/
theorem IsPFMultiplierSequence.mvRealStableOrZero_realCoordinateDiagonalOperator
    {σ : Type*} [Finite σ] {gamma : ℕ → ℝ}
    (hgamma : IsPFMultiplierSequence gamma) (q : σ)
    {p : _root_.MvPolynomial σ ℝ} (hp : MvRealStable p) :
    MvRealStableOrZero (realCoordinateDiagonalOperator gamma q p) := by
  rw [mvRealStableOrZero_iff_complexifyMv,
    complexifyMv_realCoordinateDiagonalOperator]
  apply IsPFMultiplierSequence.coordinateDiagonalOperator_preserves_stability
    hgamma (p.degreeOf q) q
  · have hpq : p.degreeOf q ≤ p.degreeOf q := le_rfl
    rw [_root_.MvPolynomial.degreeOf_le_iff] at hpq ⊢
    intro m hm
    apply hpq m
    simpa [complexifyMv,
      _root_.MvPolynomial.support_map_of_injective p
        Complex.ofRealHom.injective] using hm
  · exact hp

/-- A nowhere-zero PF multiplier sequence preserves strict real stability in
one coordinate. -/
theorem IsPFMultiplierSequence.mvRealStable_realCoordinateDiagonalOperator
    {σ : Type*} [Finite σ] {gamma : ℕ → ℝ}
    (hgamma : IsPFMultiplierSequence gamma) (hgamma0 : ∀ k, gamma k ≠ 0)
    (q : σ) {p : _root_.MvPolynomial σ ℝ} (hp : MvRealStable p) :
    MvRealStable (realCoordinateDiagonalOperator gamma q p) := by
  rcases IsPFMultiplierSequence.mvRealStableOrZero_realCoordinateDiagonalOperator hgamma q hp with
      hzero | hstable
  · exact (realCoordinateDiagonalOperator_ne_zero hgamma0 q hp.ne_zero hzero).elim
  · exact hstable

end

end RealRooted.BorceaBranden
