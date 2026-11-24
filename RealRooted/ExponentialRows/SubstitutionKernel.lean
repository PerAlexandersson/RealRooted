module

public import RealRooted.ExponentialRows.Insertion
public import RealRooted.Basic.Coefficients
public import RealRooted.Mathlib.Algebra.Polynomial.BasisTransform
import RealRooted.Mathlib.RingTheory.PowerSeries.FiniteSubstitution
import RealRooted.Mathlib.RingTheory.PowerSeries.AffineSubstitution
import RealRooted.TuranHurwitz.CoefficientDerivation
public import Mathlib.Algebra.Polynomial.Derivation
public import RealRooted.Mathlib.RingTheory.PowerSeries.MapDerivation
import Mathlib.Tactic

/-!
# The formal exponential substitution kernel

We use factorial coefficients of `exp(t Φ(u))`, so that the polynomial basis
transform sends `X^n` to `n! [u^n] exp(t Φ(u))`.

Source: unpublished manuscript (RealRooted issue #2415), Theorem 1,
https://github.com/PerAlexandersson/RealRooted/issues/2415.
-/

@[expose] public section

open Polynomial Finset

namespace RealRooted.ExponentialRows

/-- The formal exponential `exp(t B(z))` over the coefficient ring `ℝ[t]`. -/
noncomputable def exponentialKernel (B : PowerSeries ℝ) : PowerSeries ℝ[X] :=
  (PowerSeries.exp ℝ[X]).subst (PowerSeries.C X * B.map C)

/-- The factorial coefficients of the formal substitution kernel. -/
noncomputable def exponentialKernelRow (B : PowerSeries ℝ) (n : ℕ) : ℝ[X] :=
  factorialCoeff (exponentialKernel B) n

/-- The linear operator sending `X^n` to the factorial kernel coefficient. -/
noncomputable def exponentialSubstitution (B : PowerSeries ℝ) : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  Polynomial.basisTransformₗ (exponentialKernelRow B)

private theorem rat_factorial_inv (k : ℕ) :
    algebraMap ℚ ℝ[X] (1 / (k.factorial : ℚ)) = C ((k.factorial : ℝ)⁻¹) := by
  change (algebraMap ℚ ℝ[X]) _ = (algebraMap ℝ ℝ[X]) _
  rw [IsScalarTower.algebraMap_apply ℚ ℝ ℝ[X]]
  congr 1
  norm_num

/-- The marked kernel exponent has zero constant coefficient. -/
theorem constantCoeff_kernelArgument {B : PowerSeries ℝ}
    (hB : PowerSeries.constantCoeff B = 0) :
    PowerSeries.constantCoeff (PowerSeries.C X * B.map C) = 0 := by
  rw [map_mul, PowerSeries.constantCoeff_C, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, hB, map_zero,
    mul_zero]

/-- The factorial coefficients of a rescaled exponential are powers. -/
theorem factorialCoeff_rescale_exp (p : ℝ[X]) (n : ℕ) :
    factorialCoeff (PowerSeries.rescale p (PowerSeries.exp ℝ[X])) n = p ^ n := by
  rw [factorialCoeff, PowerSeries.coeff_rescale, PowerSeries.coeff_exp, rat_factorial_inv,
    mul_comm (p ^ n) (C ((n.factorial : ℝ)⁻¹)), ← mul_assoc, ← map_mul,
    mul_inv_cancel₀ (by positivity), map_one, one_mul]

/-- The kernel coefficient is a finite sum indexed by the number of marked blocks. -/
theorem exponentialKernelRow_eq_sum {B : PowerSeries ℝ}
    (hB : PowerSeries.constantCoeff B = 0) (n : ℕ) :
    exponentialKernelRow B n = ∑ k ∈ range (n + 1),
      C ((n.factorial : ℝ) * (k.factorial : ℝ)⁻¹ * PowerSeries.coeff n (B ^ k)) * X ^ k := by
  rw [exponentialKernelRow, factorialCoeff, exponentialKernel,
    PowerSeries.coeff_subst_eq_sum_range _ _ (constantCoeff_kernelArgument hB), mul_sum]
  apply sum_congr rfl
  intro k _
  rw [PowerSeries.coeff_exp, rat_factorial_inv, mul_pow, ← map_pow,
    PowerSeries.coeff_C_mul, ← map_pow, PowerSeries.coeff_map]
  simp only [map_mul]
  ring

/-- Extracting one parameter coefficient removes the finite exponential sum. -/
theorem coeff_exponentialKernelRow {B : PowerSeries ℝ}
    (hB : PowerSeries.constantCoeff B = 0) (n k : ℕ) :
    (exponentialKernelRow B n).coeff k =
      (n.factorial : ℝ) * (k.factorial : ℝ)⁻¹ * PowerSeries.coeff n (B ^ k) := by
  rw [exponentialKernelRow_eq_sum hB, finsetSum_coeff]
  by_cases hk : k ≤ n
  · rw [sum_eq_single k]
    · rw [coeff_C_mul_X_pow]
      simp
    · intro j _ hj
      rw [coeff_C_mul_X_pow]
      simp [Ne.symm hj]
    · intro h
      exact (h (mem_range.mpr (by lia))).elim
  · have hkn : n < k := by lia
    rw [PowerSeries.coeff_pow_eq_zero_of_lt B hB hkn, mul_zero]
    apply sum_eq_zero
    intro j hj
    have hjk : k ≠ j := by have := mem_range.mp hj; lia
    rw [coeff_C_mul_X_pow]
    simp [hjk]

/-- The kernel row has degree at most its coefficient index, even when leading
coefficients vanish. -/
theorem natDegree_exponentialKernelRow_le {B : PowerSeries ℝ}
    (hB : PowerSeries.constantCoeff B = 0) (n : ℕ) :
    (exponentialKernelRow B n).natDegree ≤ n := by
  rw [exponentialKernelRow_eq_sum hB]
  apply natDegree_sum_le_of_forall_le
  intro k hk
  exact (natDegree_C_mul_X_pow_le _ _).trans (by have := mem_range.mp hk; lia)

/-- The empty kernel row is one. -/
@[simp] theorem exponentialKernelRow_zero {B : PowerSeries ℝ}
    (hB : PowerSeries.constantCoeff B = 0) : exponentialKernelRow B 0 = 1 := by
  simp [exponentialKernelRow_eq_sum hB]

/-- The exponential substitution operator fixes one. -/
@[simp] theorem exponentialSubstitution_one {B : PowerSeries ℝ}
    (hB : PowerSeries.constantCoeff B = 0) : exponentialSubstitution B 1 = 1 := by
  change basisTransform (exponentialKernelRow B) 1 = 1
  calc
    _ = basisTransform (exponentialKernelRow B) (C 1) := by rw [C_1]
    _ = C 1 * exponentialKernelRow B 0 := basisTransform_C _ _
    _ = 1 := by rw [C_1, one_mul, exponentialKernelRow_zero hB]

/-- The kernel transform preserves the constant coefficient. -/
theorem coeff_zero_exponentialSubstitution {B : PowerSeries ℝ}
    (hB : PowerSeries.constantCoeff B = 0) (p : ℝ[X]) :
    (exponentialSubstitution B p).coeff 0 = p.coeff 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add, coeff_add] using congrArg₂ (· + ·) hp hq
  | monomial n a =>
    simp only [exponentialSubstitution, basisTransformₗ_apply, basisTransform_monomial,
      coeff_C_mul, coeff_exponentialKernelRow hB]
    cases n <;> simp

/-- The exponential kernel transform does not increase polynomial degree. -/
theorem natDegree_exponentialSubstitution_le {B : PowerSeries ℝ}
    (hB : PowerSeries.constantCoeff B = 0) (p : ℝ[X]) :
    (exponentialSubstitution B p).natDegree ≤ p.natDegree :=
  Polynomial.basisTransform_natDegree_le_of_natDegree_le
    (natDegree_exponentialKernelRow_le hB) p

/-- A series with nonnegative coefficients has nonnegative powers. -/
private theorem coeff_pow_nonneg {B : PowerSeries ℝ}
    (hB : ∀ n, 0 ≤ PowerSeries.coeff n B) (k n : ℕ) :
    0 ≤ PowerSeries.coeff n (B ^ k) := by
  induction k generalizing n with
  | zero => simp only [pow_zero, PowerSeries.coeff_one]; split_ifs <;> positivity
  | succ k ih =>
    rw [pow_succ, PowerSeries.coeff_mul]
    exact sum_nonneg fun i _ => mul_nonneg (ih _) (hB _)

/-- Nonnegative kernel coefficients give a coefficientwise nonnegative linear transform. -/
theorem hasNonnegCoeffs_exponentialSubstitution {B : PowerSeries ℝ}
    (hB0 : PowerSeries.constantCoeff B = 0) (hB : ∀ n, 0 ≤ PowerSeries.coeff n B)
    {p : ℝ[X]} (hp : HasNonnegCoeffs p) :
    HasNonnegCoeffs (exponentialSubstitution B p) := by
  intro j
  change 0 ≤ (basisTransform (exponentialKernelRow B) p).coeff j
  rw [coeff_basisTransform, Polynomial.sum_def]
  apply sum_nonneg
  intro k _
  rw [coeff_exponentialKernelRow hB0]
  exact mul_nonneg (hp k) (mul_nonneg (by positivity) (coeff_pow_nonneg hB j k))

/-- The polynomial-parameter derivative of the exponential kernel is
multiplication by the marked series. -/
theorem parameterDerivative_exponentialKernel {B : PowerSeries ℝ}
    (hB : PowerSeries.constantCoeff B = 0) :
    PowerSeries.mapDerivation (Polynomial.derivative' (R := ℝ)) (exponentialKernel B) =
      B.map C * exponentialKernel B := by
  let G := PowerSeries.C X * B.map C
  have hG : PowerSeries.constantCoeff G = 0 := constantCoeff_kernelArgument hB
  have hsubst := PowerSeries.HasSubst.of_constantCoeff_zero' hG
  have he : exponentialKernel B = (PowerSeries.exp ℝ).subst G := by
    rw [exponentialKernel, ← PowerSeries.map_exp (C : ℝ →+* ℝ[X])]
    exact PowerSeries.subst_map_algebraMap G hsubst (PowerSeries.exp ℝ)
  have hD : PowerSeries.mapDerivation (Polynomial.derivative' (R := ℝ))
      (B.map C) = 0 := by
    ext n
    simp [PowerSeries.coeff_mapDerivation]
  rw [he, RealRooted.TuranHurwitz.mapDerivation_subst _ _ _ hG,
    PowerSeries.derivative_exp]
  simp only [G, PowerSeries.mapDerivation_mul, PowerSeries.mapDerivation_C,
    Polynomial.derivative'_apply, derivative_X, map_one, hD, mul_zero, one_mul, add_zero]
  exact mul_comm _ _

/-- The ODE for `Φ` becomes the differential recurrence for the kernel series. -/
theorem derivative_exponentialKernel_of_ode {B : PowerSeries ℝ} {a b l : ℝ}
    (hB : PowerSeries.constantCoeff B = 0)
    (hode : PowerSeries.derivative B =
      PowerSeries.C a + PowerSeries.C b * PowerSeries.X + PowerSeries.C l * B) :
    PowerSeries.derivative (exponentialKernel B) =
      PowerSeries.C (C a * X) * exponentialKernel B +
        PowerSeries.C (C l * X) *
          PowerSeries.mapDerivation (Polynomial.derivative' (R := ℝ)) (exponentialKernel B) +
        PowerSeries.C (C b * X) * (PowerSeries.X * exponentialKernel B) := by
  have harg : PowerSeries.derivative (PowerSeries.C X * B.map C) =
      PowerSeries.C X * (PowerSeries.derivative B).map C := by
    ext n
    simp only [PowerSeries.coeff_derivative, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_map, map_mul, map_add, map_one, map_natCast]
    ring
  rw [parameterDerivative_exponentialKernel hB]
  simp only [exponentialKernel]
  rw [PowerSeries.derivative_subst
    (PowerSeries.HasSubst.of_constantCoeff_zero' (constantCoeff_kernelArgument hB)),
    PowerSeries.derivative_exp, harg, hode]
  simp only [map_add, map_mul, PowerSeries.map_C, PowerSeries.map_X]
  ring

private theorem factorialCoeff_parameterDerivative (H : PowerSeries ℝ[X]) (n : ℕ) :
    factorialCoeff (PowerSeries.mapDerivation (Polynomial.derivative' (R := ℝ)) H) n =
      (factorialCoeff H n).derivative := by
  simp [factorialCoeff, PowerSeries.coeff_mapDerivation]

/-- The first kernel row is the linear coefficient of `Φ` times `t`. -/
theorem exponentialKernelRow_one_of_ode {B : PowerSeries ℝ} {a b l : ℝ}
    (hB : PowerSeries.constantCoeff B = 0)
    (hode : PowerSeries.derivative B =
      PowerSeries.C a + PowerSeries.C b * PowerSeries.X + PowerSeries.C l * B) :
    exponentialKernelRow B 1 = C a * X := by
  have h := congrArg (fun H => factorialCoeff H 0)
    (derivative_exponentialKernel_of_ode hB hode)
  rw [factorialCoeff_derivative, factorialCoeff_add, factorialCoeff_add,
    factorialCoeff_C_mul, factorialCoeff_C_mul, factorialCoeff_C_mul,
    factorialCoeff_parameterDerivative] at h
  have hz : factorialCoeff (PowerSeries.X * exponentialKernel B) 0 = 0 := by
    simp [factorialCoeff]
  change exponentialKernelRow B 1 = _ at h
  have hk0 : factorialCoeff (exponentialKernel B) 0 = 1 := exponentialKernelRow_zero hB
  simpa only [hk0, hz, derivative_one, mul_one, mul_zero, add_zero] using h

/-- The factorial kernel rows obey the three-term differential recurrence. -/
theorem exponentialKernelRow_add_two_of_ode {B : PowerSeries ℝ} {a b l : ℝ}
    (hB : PowerSeries.constantCoeff B = 0)
    (hode : PowerSeries.derivative B =
      PowerSeries.C a + PowerSeries.C b * PowerSeries.X + PowerSeries.C l * B) (n : ℕ) :
    exponentialKernelRow B (n + 2) = C a * X * exponentialKernelRow B (n + 1) +
      C l * X * (exponentialKernelRow B (n + 1)).derivative +
      C b * X * (C (n + 1 : ℝ) * exponentialKernelRow B n) := by
  have h := congrArg (fun H => factorialCoeff H (n + 1))
    (derivative_exponentialKernel_of_ode hB hode)
  rw [factorialCoeff_derivative, factorialCoeff_add, factorialCoeff_add,
    factorialCoeff_C_mul, factorialCoeff_C_mul, factorialCoeff_C_mul,
    factorialCoeff_parameterDerivative, factorialCoeff_X_mul] at h
  exact h

/-- The operator product rule for exponential substitution, derived from the
formal ODE without division by `λ` or a positivity restriction on `a`. -/
theorem exponentialSubstitution_linear_mul {B : PowerSeries ℝ} {a b l : ℝ}
    (hB : PowerSeries.constantCoeff B = 0)
    (hode : PowerSeries.derivative B =
      PowerSeries.C a + PowerSeries.C b * PowerSeries.X + PowerSeries.C l * B)
    (r : ℝ) (p : ℝ[X]) :
    exponentialSubstitution B ((X + C r) * p) =
      (C r + C a * X) * exponentialSubstitution B p +
        C l * X * (exponentialSubstitution B p).derivative +
        C b * X * exponentialSubstitution B p.derivative := by
  have hX (q : ℝ[X]) : exponentialSubstitution B (X * q) =
      C a * X * exponentialSubstitution B q +
        C l * X * (exponentialSubstitution B q).derivative +
        C b * X * exponentialSubstitution B q.derivative := by
    induction q using Polynomial.induction_on' with
    | add q v hq hv =>
      simp only [mul_add, map_add, hq, hv]
      ring
    | monomial n c =>
      simp only [exponentialSubstitution, basisTransformₗ_apply, X_mul_monomial,
        basisTransform_monomial, derivative_mul, derivative_C, zero_mul, zero_add]
      cases n with
      | zero =>
        simp [exponentialKernelRow_zero hB,
          exponentialKernelRow_one_of_ode hB hode]
        ring
      | succ n =>
        simp only [derivative_monomial, basisTransform_monomial,
          exponentialKernelRow_add_two_of_ode hB hode, map_mul, map_natCast,
          Nat.add_sub_cancel]
        simp only [map_add, map_natCast, map_one, Nat.cast_add, Nat.cast_one]
        ring
  rw [add_mul, map_add, hX, Polynomial.linearMap_C_mul]
  ring

/-- The ODE with nonnegative coefficients forces every coefficient of `Φ`
to be nonnegative, including the degenerate parameter faces. -/
theorem coeff_nonneg_of_substitution_ode {B : PowerSeries ℝ} {a b l : ℝ}
    (hB : PowerSeries.constantCoeff B = 0)
    (hode : PowerSeries.derivative B =
      PowerSeries.C a + PowerSeries.C b * PowerSeries.X + PowerSeries.C l * B)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hl : 0 ≤ l) (n : ℕ) :
    0 ≤ PowerSeries.coeff n B := by
  induction n with
  | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, hB]
  | succ n ih =>
    have h := congrArg (PowerSeries.coeff n) hode
    rw [PowerSeries.coeff_derivative, map_add, map_add,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul] at h
    have hc : 0 ≤ PowerSeries.coeff n (PowerSeries.C a) := by
      simp only [PowerSeries.coeff_C]
      split_ifs <;> positivity
    have hx : 0 ≤ PowerSeries.coeff n (PowerSeries.X : PowerSeries ℝ) := by
      simp only [PowerSeries.coeff_X]
      split_ifs <;> positivity
    have hnonneg : 0 ≤ PowerSeries.coeff (n + 1) B * (n + 1 : ℝ) := by
      rw [h]
      exact add_nonneg (add_nonneg hc (mul_nonneg hb hx)) (mul_nonneg hl ih)
    exact nonneg_of_mul_nonneg_left hnonneg (by positivity)

private theorem exponentialKernel_X : exponentialKernel (PowerSeries.X : PowerSeries ℝ) =
    PowerSeries.rescale X (PowerSeries.exp ℝ[X]) := by
  simp only [exponentialKernel, PowerSeries.map_X]
  rw [PowerSeries.rescale_eq_subst, PowerSeries.smul_eq_C_mul]

/-- Transforming the monomial exponential kernel produces the prescribed kernel. -/
theorem exponentialSubstitution_coeff_kernel_X (P : PowerSeries ℝ) :
    (PowerSeries.mk fun k => exponentialSubstitution P
      (PowerSeries.coeff k (exponentialKernel (PowerSeries.X : PowerSeries ℝ)))) =
        exponentialKernel P := by
  apply PowerSeries.ext
  intro k
  rw [PowerSeries.coeff_mk, exponentialKernel_X, PowerSeries.coeff_rescale,
    PowerSeries.coeff_exp]
  rw [rat_factorial_inv]
  rw [mul_comm, Polynomial.linearMap_C_mul]
  change C ((k.factorial : ℝ)⁻¹) *
    basisTransform (exponentialKernelRow P) (X ^ k) = _
  rw [basisTransform_X_pow, exponentialKernelRow, factorialCoeff,
    ← mul_assoc, ← map_mul, inv_mul_cancel₀ (by positivity), map_one, one_mul]


end RealRooted.ExponentialRows
