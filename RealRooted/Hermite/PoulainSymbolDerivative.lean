module

public import RealRooted.Hermite.Poulain
public import RealRooted.PFPolynomial
public import RealRooted.EulerOperator.Shift
import RealRooted.DerivativeProduct.KernelWeyl
import RealRooted.LiebSokalPointwise
import Mathlib.Tactic

/-!
# Differential operators from a symbol and its derivative

For a real-rooted symbol `ψ` and `α ≥ 0`, the operator
`X ψ(D) + α ψ'(D)` preserves real-rootedness up to zero. We use the existing
univariate Weyl-symbol criterion: its signed symbol is
`x ψ(-y) + α ψ'(-y)`. Writing `q(y) = ψ(-y)`, this becomes
`q(y) (x - α q'(y) / q(y))`, which cannot vanish in the product of upper
half-planes because the logarithmic derivative of `q` has nonpositive
imaginary part. No hypothesis on the constant coefficient of `ψ` is needed.

The target and examples are recorded in
https://github.com/PerAlexandersson/RealRooted/issues/2544.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted.HermitePoulain

/-- The operator `X ψ(D) + α ψ'(D)` applied to `p`. -/
def symbolDerivativeOperator (ψ : ℝ[X]) (α : ℝ) (p : ℝ[X]) : ℝ[X] :=
  X * applyAsDifferentialOperator ψ p +
    C α * applyAsDifferentialOperator ψ.derivative p

/-- The signed symbol is nonvanishing on the product of upper half-planes. -/
private theorem symbol_nonzero {ψ : ℝ[X]} (hψ : ψ ≠ 0 ∧ ψ.Splits)
    {α : ℝ} (hα : 0 ≤ α) {x y : ℂ} (hx : 0 < x.im) (hy : 0 < y.im) :
    x * (complexify ψ).eval (-y) +
      (α : ℂ) * (complexify ψ.derivative).eval (-y) ≠ 0 := by
  let q : ℂ[X] := complexify (ψ.comp (-X))
  have hq0 : ψ.comp (-X) ≠ 0 := by
    intro h
    have := congrArg (fun p : ℝ[X] => p.comp (-X)) h
    exact hψ.1 (by simpa [comp_assoc] using this)
  have hq : ∀ z : ℂ, 0 < z.im → q.eval z ≠ 0 :=
    RealRooted.Polynomial.Splits.isUpperHalfPlaneStable_complexify hψ.2.comp_neg_X hq0
  have hqy := hq y hy
  have hratio := q.derivative_eval_div_eval_im_nonpos hq hy
  have hval : q.eval y = (complexify ψ).eval (-y) := by
    simp [q, complexify, Polynomial.map_comp]
  have hder : q.derivative.eval y = -(complexify ψ.derivative).eval (-y) := by
    simp [q, complexify, Polynomial.map_comp, derivative_comp]
  rw [hval, hder] at hratio
  rw [hval] at hqy
  intro hzero
  have heq : x = -(α : ℂ) *
      ((complexify ψ.derivative).eval (-y) / (complexify ψ).eval (-y)) := by
    rw [← mul_div_assoc]
    exact (eq_div_iff hqy).mpr (by linear_combination hzero)
  have him := congrArg Complex.im heq
  simp only [neg_div, Complex.neg_im] at hratio
  simp only [Complex.mul_im, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
    Complex.ofReal_im, neg_zero, zero_mul, add_zero] at him
  nlinarith

/-- A common truncation of the two constant-coefficient operators. -/
private theorem symbolDerivativeOperator_eq_sum (ψ : ℝ[X]) (α : ℝ) (p : ℝ[X]) :
    symbolDerivativeOperator ψ α p =
      ∑ j : Fin (ψ.natDegree + 1),
        (X * C (ψ.coeff j) + C α * C (ψ.derivative.coeff j)) *
          (derivative^[j.val]) p := by
  rw [symbolDerivativeOperator,
    applyAsDifferentialOperator_eq_sum_range (N := ψ.natDegree + 1)
      (Nat.lt_succ_self _) p,
    applyAsDifferentialOperator_eq_sum_range (N := ψ.natDegree + 1)
      (by have := natDegree_derivative_le ψ; lia) p]
  rw [Fin.sum_univ_eq_sum_range (fun j =>
    (X * C (ψ.coeff j) + C α * C (ψ.derivative.coeff j)) *
      (derivative^[j]) p) (ψ.natDegree + 1)]
  simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc]

/-- `X ψ(D) + α ψ'(D)` preserves real-rootedness up to zero for every
nonzero real-rooted symbol `ψ` and every nonnegative real parameter `α`. -/
theorem symbolDerivativeOperator_eq_zero_or_splits {ψ p : ℝ[X]}
    (hψ : ψ ≠ 0 ∧ ψ.Splits) {α : ℝ} (hα : 0 ≤ α) (hp : p.Splits) :
    symbolDerivativeOperator ψ α p = 0 ∨ (symbolDerivativeOperator ψ α p).Splits := by
  by_cases hp0 : p = 0
  · simp [symbolDerivativeOperator, hp0]
  rw [symbolDerivativeOperator_eq_sum]
  apply sum_mul_iterate_derivative_eq_zero_or_splits _ ?_ hp0 hp
  intro x y hx hy
  have heval (f : ℝ[X]) (hf : f.natDegree < ψ.natDegree + 1) :
      ∑ j : Fin (ψ.natDegree + 1), (f.coeff j : ℂ) * (-y) ^ j.val =
        (complexify f).eval (-y) := by
    rw [Fin.sum_univ_eq_sum_range
      (fun j => (f.coeff j : ℂ) * (-y) ^ j) (ψ.natDegree + 1)]
    simpa [complexify, eval_map] using
      (eval₂_eq_sum_range' Complex.ofRealHom hf (-y)).symm
  have hs := symbol_nonzero hψ hα hx hy
  convert hs using 1
  simp only [complexify, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_X,
    Polynomial.map_C, eval_add, eval_mul, eval_X, eval_C, Complex.ofRealHom_eq_coe,
    add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [heval ψ (Nat.lt_succ_self _),
    heval ψ.derivative (by have := natDegree_derivative_le ψ; lia)]
  rfl

/-- Nonnegative symbol coefficients give a constant-coefficient operator
which preserves nonnegative coefficients. -/
theorem hasNonnegCoeffs_applyAsDifferentialOperator {ψ p : ℝ[X]}
    (hψ : HasNonnegCoeffs ψ) (hp : HasNonnegCoeffs p) :
    HasNonnegCoeffs (applyAsDifferentialOperator ψ p) := by
  apply hasNonnegCoeffs_finsetSum
  intro j _
  exact hasNonnegCoeffs_C_mul (hψ j) (hp.iterate_derivative j)

/-- The PF addendum only needs nonnegative coefficients for the two
constant-coefficient operator images of the input. -/
theorem symbolDerivativeOperator_isPFPolynomial_of_hasNonnegCoeffs
    {ψ p : ℝ[X]} (hψ : ψ ≠ 0 ∧ ψ.Splits) {α : ℝ} (hα : 0 ≤ α)
    (hp : IsPFPolynomial p)
    (hψp : HasNonnegCoeffs (applyAsDifferentialOperator ψ p))
    (hdψp : HasNonnegCoeffs (applyAsDifferentialOperator ψ.derivative p)) :
    IsPFPolynomial (symbolDerivativeOperator ψ α p) := by
  apply IsPFPolynomial.of_nonnegCoeffs_eq_zero_or_splits
    ((hasNonnegCoeffs_X.mul hψp).add (hasNonnegCoeffs_C_mul hα hdψp))
  exact symbolDerivativeOperator_eq_zero_or_splits hψ hα hp.splits

/-- A nonzero real-rooted symbol with nonnegative coefficients gives a
PF-preserving symbol-derivative operator. -/
theorem symbolDerivativeOperator_isPFPolynomial {ψ p : ℝ[X]}
    (hψ : ψ ≠ 0 ∧ ψ.Splits) (hψnn : HasNonnegCoeffs ψ)
    {α : ℝ} (hα : 0 ≤ α) (hp : IsPFPolynomial p) :
    IsPFPolynomial (symbolDerivativeOperator ψ α p) :=
  symbolDerivativeOperator_isPFPolynomial_of_hasNonnegCoeffs hψ hα hp
    (hasNonnegCoeffs_applyAsDifferentialOperator hψnn hp.hasNonnegCoeffs)
    (hasNonnegCoeffs_applyAsDifferentialOperator hψnn.derivative hp.hasNonnegCoeffs)

/-- The symbol `ψ = X` gives the shifted Euler operator `θ + α`. -/
theorem symbolDerivativeOperator_X (α : ℝ) (p : ℝ[X]) :
    symbolDerivativeOperator X α p = eulerShift α p := by
  have hX : applyAsDifferentialOperator X p = p.derivative := by
    simpa using applyAsDifferentialOperator_X_mul 1 p
  simp [symbolDerivativeOperator, hX, eulerShift]

/-- Every nonnegative shifted Euler operator preserves real-rootedness up to zero. -/
theorem eulerShift_eq_zero_or_splits {α : ℝ} (hα : 0 ≤ α)
    {p : ℝ[X]} (hp : p.Splits) :
    eulerShift α p = 0 ∨ (eulerShift α p).Splits := by
  simpa only [symbolDerivativeOperator_X] using
    symbolDerivativeOperator_eq_zero_or_splits
      (ψ := X) ⟨X_ne_zero, Splits.X⟩ hα hp

/-- Powers of the symbol give `X D^m + α m D^(m-1)`, including `m = 0`. -/
theorem symbolDerivativeOperator_X_pow (m : ℕ) (α : ℝ) (p : ℝ[X]) :
    symbolDerivativeOperator (X ^ m) α p =
      X * (derivative^[m]) p + C (α * m) * (derivative^[m - 1]) p := by
  have hpow (n : ℕ) : applyAsDifferentialOperator (X ^ n) p = (derivative^[n]) p := by
    simpa using applyAsDifferentialOperator_X_pow_mul n 1 p
  rw [symbolDerivativeOperator, derivative_X_pow, applyAsDifferentialOperator_C_mul,
    hpow, hpow, ← mul_assoc, ← C_mul]

/-- For every `m`, `X D^m + α m D^(m-1)` preserves real-rootedness up to zero. -/
theorem X_mul_iterate_derivative_add_eq_zero_or_splits (m : ℕ)
    {α : ℝ} (hα : 0 ≤ α) {p : ℝ[X]} (hp : p.Splits) :
    X * (derivative^[m]) p + C (α * m) * (derivative^[m - 1]) p = 0 ∨
      (X * (derivative^[m]) p + C (α * m) * (derivative^[m - 1]) p).Splits := by
  simpa only [symbolDerivativeOperator_X_pow] using
    symbolDerivativeOperator_eq_zero_or_splits
      (ψ := X ^ m) ⟨pow_ne_zero _ X_ne_zero, Splits.X.pow m⟩ hα hp

/-- The quadratic symbol gives `X D² + β D` for every `β ≥ 0`. -/
theorem X_mul_derivative_derivative_add_eq_zero_or_splits
    {β : ℝ} (hβ : 0 ≤ β) {p : ℝ[X]} (hp : p.Splits) :
    X * p.derivative.derivative + C β * p.derivative = 0 ∨
      (X * p.derivative.derivative + C β * p.derivative).Splits := by
  simpa [Function.iterate_succ_apply'] using
    X_mul_iterate_derivative_add_eq_zero_or_splits 2 (α := β / 2) (by positivity) hp

/-- The symbol `X (1 + X)` gives the Darboux-shift differential operator. -/
theorem symbolDerivativeOperator_X_mul_one_add_X (α : ℝ) (p : ℝ[X]) :
    symbolDerivativeOperator (X * (1 + X)) α p =
      X * p.derivative.derivative + (X + C (2 * α)) * p.derivative + C α * p := by
  have hX : applyAsDifferentialOperator X p = p.derivative := by
    simpa using applyAsDifferentialOperator_X_mul 1 p
  simp only [symbolDerivativeOperator, derivative_mul, derivative_add, derivative_one,
    derivative_X, zero_add, one_mul, mul_one, applyAsDifferentialOperator_X_mul,
    applyAsDifferentialOperator_add, applyAsDifferentialOperator_one, derivative_add]
  rw [hX, C_mul, C_ofNat]
  ring

/-- `X D² + (X + 2α) D + α` preserves real-rootedness up to zero for `α ≥ 0`. -/
theorem X_mul_derivative_derivative_add_affine_eq_zero_or_splits
    {α : ℝ} (hα : 0 ≤ α) {p : ℝ[X]} (hp : p.Splits) :
    X * p.derivative.derivative + (X + C (2 * α)) * p.derivative + C α * p = 0 ∨
      (X * p.derivative.derivative + (X + C (2 * α)) * p.derivative + C α * p).Splits := by
  rw [← symbolDerivativeOperator_X_mul_one_add_X]
  exact symbolDerivativeOperator_eq_zero_or_splits
      (ψ := X * (1 + X))
      ⟨mul_ne_zero X_ne_zero (by
        have : (1 + X : ℝ[X]).coeff 0 = 1 := by simp
        intro h
        simp [h] at this), Splits.X.mul (Splits.of_natDegree_le_one (by compute_degree))⟩
      hα hp

end RealRooted.HermitePoulain
