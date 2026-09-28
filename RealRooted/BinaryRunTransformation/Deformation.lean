import RealRooted.BinaryRunTransformation.CriticalValue

/-!
# The binary-run pointing deformation

This file packages the scaled input, its pointed companion, and the remainder
appearing in the stable pencil.  It also derives the critical-value sign from
the abstract signed-parity theorem.
-/

open Polynomial

namespace RealRooted

noncomputable section

/-- Scale every degree-`m` input coefficient by `λ^m`. -/
def scalePolynomial (t : ℝ) (p : ℝ[X]) : ℝ[X] :=
  p.comp (C t * X)

theorem coeff_scalePolynomial (t : ℝ) (p : ℝ[X]) (m : ℕ) :
    (scalePolynomial t p).coeff m = p.coeff m * t ^ m := by
  rw [scalePolynomial, Polynomial.comp_C_mul_X_coeff]

/-- The shifted output `Q(λ, 1 + Y)` of the binary-run deformation. -/
def shiftedBinaryRunDeformation (n : ℕ) (p : ℝ[X]) (t : ℝ) : ℝ[X] :=
  (binaryRunTransform n (scalePolynomial t p)).comp (X + 1)

/-- Pointing an input marks a chosen factor, or equivalently multiplies its
degree-`m` coefficient by `m`. -/
def pointPolynomial (p : ℝ[X]) : ℝ[X] :=
  X * p.derivative

/-- The shifted binary-run transform of the pointed scaled input.  Analytically
this is `λ ∂Q/∂λ`. -/
def shiftedBinaryRunPointing (n : ℕ) (p : ℝ[X]) (t : ℝ) : ℝ[X] :=
  (binaryRunTransform n (pointPolynomial (scalePolynomial t p))).comp (X + 1)

/-- The remainder `E = λ Q_λ - Y Q_Y` occurring in the contracted pencil. -/
def binaryRunPointingRemainder (n : ℕ) (p : ℝ[X]) (t : ℝ) : ℝ[X] :=
  shiftedBinaryRunPointing n p t -
    X * (shiftedBinaryRunDeformation n p t).derivative

theorem shiftedBinaryRunPointing_eq_remainder_add (n : ℕ)
    (p : ℝ[X]) (t : ℝ) :
    shiftedBinaryRunPointing n p t =
      binaryRunPointingRemainder n p t +
        X * (shiftedBinaryRunDeformation n p t).derivative := by
  simp [binaryRunPointingRemainder]

theorem natDegree_scalePolynomial_le (t : ℝ) (p : ℝ[X]) :
    (scalePolynomial t p).natDegree ≤ p.natDegree := by
  calc
    (scalePolynomial t p).natDegree ≤
        p.natDegree * (C t * X : ℝ[X]).natDegree :=
      Polynomial.natDegree_comp_le
    _ ≤ p.natDegree * 1 := by
      gcongr
      simpa using Polynomial.natDegree_C_mul_le t X
    _ = p.natDegree := by simp

/-- Fixed-range expansion of a shifted binary-run transform. -/
theorem comp_binaryRunTransform_eq_sum_range
    {n : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ n) :
    (binaryRunTransform n p).comp (X + 1) =
      ∑ m ∈ Finset.range (n + 1),
        C (p.coeff m) * (binaryRunPolynomial n m).comp (X + 1) := by
  rw [binaryRunTransform, Polynomial.basisTransform, Polynomial.sum_def]
  change (Polynomial.compRingHom (X + 1))
      (∑ m ∈ p.support, C (p.coeff m) * binaryRunPolynomial n m) = _
  rw [map_sum]
  simp_rw [map_mul, Polynomial.coe_compRingHom_apply, C_comp]
  apply Finset.sum_subset
  · intro m hm
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le <|
      (Polynomial.le_natDegree_of_ne_zero
        (Polynomial.mem_support_iff.mp hm)).trans hp
  · intro m hmrange hmsupport
    rw [Polynomial.notMem_support_iff.mp hmsupport]
    simp

/-- Fixed-range expansion of the shifted deformation.  This form exposes its
polynomial dependence on the scaling parameter. -/
theorem shiftedBinaryRunDeformation_eq_sum_range
    {n : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ n) (t : ℝ) :
    shiftedBinaryRunDeformation n p t =
      ∑ m ∈ Finset.range (n + 1),
        C (p.coeff m * t ^ m) *
          (binaryRunPolynomial n m).comp (X + 1) := by
  rw [shiftedBinaryRunDeformation,
    comp_binaryRunTransform_eq_sum_range
      ((natDegree_scalePolynomial_le t p).trans hp)]
  simp_rw [coeff_scalePolynomial]

theorem natDegree_pointPolynomial_le (p : ℝ[X]) :
    (pointPolynomial p).natDegree ≤ p.natDegree := by
  simpa [pointPolynomial] using
    Polynomial.natDegree_C_mul_add_affine_mul_derivative_le p 0 0 1

/-- Fixed-range expansion of the pointed shifted deformation. -/
theorem shiftedBinaryRunPointing_eq_sum_range
    {n : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ n) (t : ℝ) :
    shiftedBinaryRunPointing n p t =
      ∑ m ∈ Finset.range (n + 1),
        C ((m : ℝ) * (p.coeff m * t ^ m)) *
          (binaryRunPolynomial n m).comp (X + 1) := by
  rw [shiftedBinaryRunPointing,
    comp_binaryRunTransform_eq_sum_range
      ((natDegree_pointPolynomial_le (scalePolynomial t p)).trans
        ((natDegree_scalePolynomial_le t p).trans hp))]
  simp_rw [pointPolynomial, Polynomial.coeff_X_mul_derivative,
    coeff_scalePolynomial]

/-- Parameter differentiation is Euler pointing: at positive scale, the
parameter derivative of an evaluation is the pointed evaluation divided by
the scale. -/
theorem hasDerivAt_shiftedBinaryRunDeformation_eval
    {n : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ n) {t : ℝ}
    (ht : t ≠ 0) (x : ℝ) :
    HasDerivAt (fun u => (shiftedBinaryRunDeformation n p u).eval x)
      ((shiftedBinaryRunPointing n p t).eval x / t) t := by
  simp_rw [shiftedBinaryRunDeformation_eq_sum_range hp,
    shiftedBinaryRunPointing_eq_sum_range hp, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C]
  have hderiv : HasDerivAt
      (fun u => ∑ m ∈ Finset.range (n + 1),
        (p.coeff m * u ^ m) *
          ((binaryRunPolynomial n m).comp (X + 1)).eval x)
      (∑ m ∈ Finset.range (n + 1),
        (p.coeff m * ((m : ℝ) * t ^ (m - 1))) *
          ((binaryRunPolynomial n m).comp (X + 1)).eval x) t := by
    apply HasDerivAt.fun_sum
    intro m hm
    exact ((hasDerivAt_pow m t).const_mul (p.coeff m)).mul_const _
  convert hderiv using 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m hm
  cases m with
  | zero => simp
  | succ m =>
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
    rw [pow_succ]
    field_simp [ht]

theorem coeff_shiftedBinaryRunDeformation_eq_sum_range
    {n : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ n) (t : ℝ) (k : ℕ) :
    (shiftedBinaryRunDeformation n p t).coeff k =
      ∑ m ∈ Finset.range (n + 1),
        (scalePolynomial t p).coeff m *
          (((Nat.choose m k : ℝ) *
            (Nat.choose (n + 1 - m) k : ℝ)) /
              (Nat.choose n k : ℝ)) := by
  exact coeff_comp_binaryRunTransform_eq_sum_range
    ((natDegree_scalePolynomial_le t p).trans hp) k

theorem coeff_shiftedBinaryRunPointing_eq_sum_range
    {n : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ n) (t : ℝ) (k : ℕ) :
    (shiftedBinaryRunPointing n p t).coeff k =
      ∑ m ∈ Finset.range (n + 1),
        (m : ℝ) * (scalePolynomial t p).coeff m *
          (((Nat.choose m k : ℝ) *
            (Nat.choose (n + 1 - m) k : ℝ)) /
              (Nat.choose n k : ℝ)) := by
  rw [shiftedBinaryRunPointing]
  rw [coeff_comp_binaryRunTransform_eq_sum_range
    ((natDegree_pointPolynomial_le (scalePolynomial t p)).trans
      ((natDegree_scalePolynomial_le t p).trans hp))]
  apply Finset.sum_congr rfl
  intro m _
  rw [pointPolynomial, Polynomial.coeff_X_mul_derivative]

theorem natDegree_shiftedBinaryRunDeformation_le
    {n : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ n) (t : ℝ) :
    (shiftedBinaryRunDeformation n p t).natDegree ≤ (n + 1) / 2 :=
  natDegree_comp_binaryRunTransform_le
    ((natDegree_scalePolynomial_le t p).trans hp)

theorem natDegree_shiftedBinaryRunPointing_le
    {n : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ n) (t : ℝ) :
    (shiftedBinaryRunPointing n p t).natDegree ≤ (n + 1) / 2 := by
  apply natDegree_comp_binaryRunTransform_le
  exact (natDegree_pointPolynomial_le (scalePolynomial t p)).trans
    ((natDegree_scalePolynomial_le t p).trans hp)

theorem natDegree_binaryRunPointingRemainder_le
    {n : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ n) (t : ℝ) :
    (binaryRunPointingRemainder n p t).natDegree ≤ n / 2 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro k hk
  rw [binaryRunPointingRemainder, coeff_sub,
    Polynomial.coeff_X_mul_derivative]
  by_cases hkfar : (n + 1) / 2 < k
  · have hpoint := coeff_eq_zero_of_natDegree_lt <|
      lt_of_le_of_lt (natDegree_shiftedBinaryRunPointing_le hp t) hkfar
    have hq := coeff_eq_zero_of_natDegree_lt <|
      lt_of_le_of_lt (natDegree_shiftedBinaryRunDeformation_le hp t) hkfar
    rw [hpoint, hq]
    ring
  · have hkeq : 2 * k = n + 1 := by lia
    rw [coeff_shiftedBinaryRunPointing_eq_sum_range hp,
      coeff_shiftedBinaryRunDeformation_eq_sum_range hp,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_eq_zero
    intro m hm
    by_cases hmk : m = k
    · subst m
      ring
    rcases lt_or_gt_of_ne hmk with hmklt | hmkgt
    · rw [Nat.choose_eq_zero_of_lt hmklt]
      simp
    · have hother : n + 1 - m < k := by lia
      rw [Nat.choose_eq_zero_of_lt hother]
      simp

theorem natDegree_derivative_shiftedBinaryRunDeformation_le
    {n : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ n) (t : ℝ) :
    (shiftedBinaryRunDeformation n p t).derivative.natDegree ≤
      (n - 1) / 2 := by
  rw [(shiftedBinaryRunDeformation n p t).natDegree_derivative]
  have hq := natDegree_shiftedBinaryRunDeformation_le hp t
  lia

theorem natDegree_X_mul_secondDerivative_shiftedBinaryRunDeformation_le
    {n : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ n) (t : ℝ) :
    (X * (shiftedBinaryRunDeformation n p t).derivative.derivative).natDegree ≤
      (n - 1) / 2 := by
  exact (natDegree_pointPolynomial_le
      (shiftedBinaryRunDeformation n p t).derivative).trans
    (natDegree_derivative_shiftedBinaryRunDeformation_le hp t)

/-- The stable contracted pencil gives the sign needed at every negative
critical point of the shifted deformation. -/
theorem binaryRunDeformation_critical_sign_of_stablePencil
    {n : ℕ} (hn : 4 ≤ n) {p : ℝ[X]} (hp : p.natDegree ≤ n)
    {t r : ℝ} (hr : 0 < r)
    (hcritical :
      (shiftedBinaryRunDeformation n p t).derivative.eval
        (-(r ^ 2)⁻¹) = 0)
    (hstable : IsUpperHalfPlaneStablePencil
      (-(signedParityLift (n - 1)
        (shiftedBinaryRunDeformation n p t).derivative))
      (signedParityLift n (binaryRunPointingRemainder n p t))) :
    (shiftedBinaryRunPointing n p t).eval (-(r ^ 2)⁻¹) *
      (shiftedBinaryRunDeformation n p t).derivative.derivative.eval
        (-(r ^ 2)⁻¹) ≤ 0 := by
  have hsign := criticalValue_sign_of_stablePencil hn hr
    (natDegree_binaryRunPointingRemainder_le hp t)
    (natDegree_derivative_shiftedBinaryRunDeformation_le hp t)
    (natDegree_X_mul_secondDerivative_shiftedBinaryRunDeformation_le hp t)
    hcritical hstable
  rw [shiftedBinaryRunPointing_eq_remainder_add,
    eval_add, eval_mul, eval_X, hcritical, mul_zero, add_zero]
  exact hsign

end

end RealRooted
