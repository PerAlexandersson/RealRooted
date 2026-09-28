import RealRooted.BinaryRunTransformation.PointingPencil
import RealRooted.CriticalValueContinuation
import RealRooted.IteratedDerivativeShift

/-!
# Continuation for the binary-run deformation

This file connects the smooth binary-run family to the generic local root
continuation API.  It is the analytic layer used to prevent collisions while
the scaling parameter increases.
-/

open Filter Polynomial Topology
open scoped ContDiff

namespace RealRooted

noncomputable section

/-- A nondegenerate critical point of the shifted binary-run deformation has
a local `C¹` branch of critical points. -/
theorem exists_contDiffAt_shiftedBinaryRunDeformation_criticalPoint
    {n : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ n) {t x : ℝ}
    (hcritical :
      (shiftedBinaryRunDeformation n p t).derivative.IsRoot x)
    (hregular :
      (shiftedBinaryRunDeformation n p t).derivative.derivative.eval x ≠ 0) :
    ∃ ξ : ℝ → ℝ,
      ContDiffAt ℝ 1 ξ t ∧
        ξ t = x ∧
          ∀ᶠ u in 𝓝 t,
            (shiftedBinaryRunDeformation n p u).derivative.IsRoot (ξ u) := by
  apply exists_contDiffAt_polynomial_root
    (fun u => (shiftedBinaryRunDeformation n p u).derivative)
  · exact (contDiff_derivative_shiftedBinaryRunDeformation_eval_prod hp).contDiffAt.of_le
      (by simp)
  · exact hcritical
  · exact hregular

/-- Along a differentiable branch of critical points, the critical value has
the same parameter derivative as evaluation at a fixed point. -/
theorem hasDerivAt_shiftedBinaryRunDeformation_criticalValue
    {n : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ n) {t x ξ' : ℝ}
    (ht : t ≠ 0) {ξ : ℝ → ℝ} (hξ : HasDerivAt ξ ξ' t)
    (hξbase : ξ t = x)
    (hcritical :
      (shiftedBinaryRunDeformation n p t).derivative.eval x = 0) :
    HasDerivAt
      (fun u => (shiftedBinaryRunDeformation n p u).eval (ξ u))
      ((shiftedBinaryRunPointing n p t).eval x / t) t := by
  let B : ℕ → ℝ[X] := fun m =>
    (binaryRunPolynomial n m).comp (X + 1)
  have hsum : HasDerivAt
      (fun u => ∑ m ∈ Finset.range (n + 1),
        (p.coeff m * u ^ m) * (B m).eval (ξ u))
      (∑ m ∈ Finset.range (n + 1),
        ((p.coeff m * ((m : ℝ) * t ^ (m - 1))) * (B m).eval x +
          (p.coeff m * t ^ m) * ((B m).derivative.eval x * ξ'))) t := by
    apply HasDerivAt.fun_sum
    intro m hm
    convert
      ((hasDerivAt_pow m t).const_mul (p.coeff m)).mul
        (((B m).hasDerivAt (ξ t)).comp t hξ) using 1
    all_goals first
      | rfl
      | simp [Function.comp_apply, hξbase]
  have hfixed : HasDerivAt
      (fun u => ∑ m ∈ Finset.range (n + 1),
        (p.coeff m * u ^ m) * (B m).eval x)
      (∑ m ∈ Finset.range (n + 1),
        (p.coeff m * ((m : ℝ) * t ^ (m - 1))) * (B m).eval x) t := by
    apply HasDerivAt.fun_sum
    intro m hm
    exact ((hasDerivAt_pow m t).const_mul (p.coeff m)).mul_const _
  have hfixed_eq :
      (∑ m ∈ Finset.range (n + 1),
        (p.coeff m * ((m : ℝ) * t ^ (m - 1))) * (B m).eval x) =
        (shiftedBinaryRunPointing n p t).eval x / t := by
    apply HasDerivAt.unique hfixed
    convert hasDerivAt_shiftedBinaryRunDeformation_eval hp ht x using 1
    funext u
    rw [shiftedBinaryRunDeformation_eq_sum_range hp,
      Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, B]
  have hspace_eq :
      (∑ m ∈ Finset.range (n + 1),
        (p.coeff m * t ^ m) * ((B m).derivative.eval x * ξ')) = 0 := by
    have hderiv :
        (shiftedBinaryRunDeformation n p t).derivative.eval x =
          ∑ m ∈ Finset.range (n + 1),
            (p.coeff m * t ^ m) * (B m).derivative.eval x := by
      rw [shiftedBinaryRunDeformation_eq_sum_range hp]
      simp only [Polynomial.derivative_sum, Polynomial.derivative_C_mul,
        Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, B]
    calc
      _ = (∑ m ∈ Finset.range (n + 1),
          (p.coeff m * t ^ m) * (B m).derivative.eval x) * ξ' := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro m hm
        ring
      _ = 0 := by rw [← hderiv, hcritical, zero_mul]
  convert hsum using 1
  · funext u
    rw [shiftedBinaryRunDeformation_eq_sum_range hp,
      Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, B]
  · rw [Finset.sum_add_distrib, hfixed_eq, hspace_eq, add_zero]

/-- The squared critical value has derivative `2 Q Qₜ` along any
differentiable critical-point branch. -/
theorem hasDerivAt_sq_shiftedBinaryRunDeformation_criticalValue
    {n : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ n) {t x ξ' : ℝ}
    (ht : t ≠ 0) {ξ : ℝ → ℝ} (hξ : HasDerivAt ξ ξ' t)
    (hξbase : ξ t = x)
    (hcritical :
      (shiftedBinaryRunDeformation n p t).derivative.eval x = 0) :
    HasDerivAt
      (fun u =>
        ((shiftedBinaryRunDeformation n p u).eval (ξ u)) ^ 2)
      (2 * (shiftedBinaryRunDeformation n p t).eval x *
        ((shiftedBinaryRunPointing n p t).eval x / t)) t := by
  have hvalue := hasDerivAt_shiftedBinaryRunDeformation_criticalValue
    hp ht hξ hξbase hcritical
  convert hvalue.pow 2 using 1
  rw [hξbase]
  ring

/-- The pointing-pencil sign makes every squared critical value move
nondecreasingly while the shifted deformation is split and the critical value
is nonzero. -/
theorem shiftedBinaryRunDeformation_sqCriticalValue_deriv_nonneg
    {n : ℕ} (hn : 4 ≤ n) {p : ℝ[X]} (hp : IsPFPolynomial p)
    (hp0 : p ≠ 0) (hdegree : p.natDegree ≤ n) {t x : ℝ}
    (ht : 0 < t) (hx : x < 0)
    (hcritical :
      (shiftedBinaryRunDeformation n p t).derivative.eval x = 0)
    (hsplits : (shiftedBinaryRunDeformation n p t).Splits)
    (hpositiveDegree :
      1 ≤ (shiftedBinaryRunDeformation n p t).natDegree)
    (hvalue : (shiftedBinaryRunDeformation n p t).eval x ≠ 0) :
    0 ≤ 2 * (shiftedBinaryRunDeformation n p t).eval x *
      ((shiftedBinaryRunPointing n p t).eval x / t) := by
  let Q := shiftedBinaryRunDeformation n p t
  let A := (shiftedBinaryRunPointing n p t).eval x
  let B := Q.derivative.derivative.eval x
  let C := Q.eval x
  have hBC : B * C < 0 := by
    have hstrict := deriv2_mul_lt_deriv_sq_at_non_root
      hsplits hpositiveDegree hvalue
    rw [hcritical] at hstrict
    norm_num [Q, B, C] at hstrict ⊢
    exact hstrict
  have hAB : A * B ≤ 0 := by
    exact binaryRunDeformation_critical_sign_of_neg
      hn hp hp0 hdegree ht hx hcritical
  have hAC : 0 ≤ A * C := by
    rcases mul_neg_iff.mp hBC with ⟨hBpos, hCneg⟩ | ⟨hBneg, hCpos⟩
    · have hAnonpos : A ≤ 0 := by
        by_contra h
        exact (not_le_of_gt (mul_pos (lt_of_not_ge h) hBpos)) hAB
      exact mul_nonneg_of_nonpos_of_nonpos hAnonpos hCneg.le
    · have hAnonneg : 0 ≤ A := by
        by_contra h
        exact (not_le_of_gt (mul_pos_of_neg_of_neg (lt_of_not_ge h) hBneg)) hAB
      exact mul_nonneg hAnonneg hCpos.le
  have hdiv : 0 ≤ (C * A) / t :=
    div_nonneg (by simpa [mul_comm] using hAC) ht.le
  change 0 ≤ 2 * C * (A / t)
  calc
    0 ≤ 2 * ((C * A) / t) := mul_nonneg (by norm_num) hdiv
    _ = 2 * C * (A / t) := by field_simp

end

end RealRooted
