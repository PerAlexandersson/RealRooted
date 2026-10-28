module

public import RealRooted.BorceaBranden.Applications.PoissonStarFallingFactorial
public import RealRooted.BorceaBranden.Applications.PoissonStarGeneral
public import RealRooted.CubicDiscriminant
public import RealRooted.NarayanaTransformation.Basis

import RealRooted.QuadraticRoot
import RealRooted.CombinatorialExamples.Touchard

/-!
# Stirling transforms and grouped root regions

This file formalizes the transform identities and grouped cubic criterion from issue #2134.
The Touchard basis transform is the linear map `S` characterized by `S(X^n) = T_n(X)`.
Its multiplication law is the parameter-one Poisson product.  This gives a reusable PF
criterion for products, including a falling-factorial prefix.  We also prove the exact cubic
coefficient/discriminant criterion and the sharp grouped family proposed in the issue.

The transform identities are implicit in the inverse falling-factorial transform and the
Poisson product developed in the library.  The root criterion uses Brenti--Royle--Wagner,
*Location of zeros of chromatic and related polynomials of graphs* (1994), Theorem 4.7,
as motivation; the grouped cubic extension itself is proved directly here.
-/

public section

open Polynomial
open scoped BigOperators

namespace RealRooted

noncomputable section

/-! ## The Touchard transform and the Poisson product -/

/-- At step one, the Poisson falling factorial is the usual falling factorial. -/
theorem Poisson.stepFallingFactorial_one (n : ℕ) :
    Poisson.stepFallingFactorial 1 n = fallingFactorialPolynomial n := by
  simp [Poisson.stepFallingFactorial, fallingFactorialPolynomial]

/-- The step-one falling-factorial transform is the usual falling-factorial basis transform. -/
theorem Poisson.fallingFactorialTransform_one_eq_basisTransform (p : ℝ[X]) :
    Poisson.fallingFactorialTransform 1 p =
      basisTransform fallingFactorialPolynomial p := by
  unfold Poisson.fallingFactorialTransform
  exact congrArg (fun B : ℕ → ℝ[X] ↦ basisTransform B p)
    (funext Poisson.stepFallingFactorial_one)

private theorem touchardTransform_injective :
    Function.Injective (basisTransform touchard) :=
  Polynomial.basisTransform_injective_of_natDegree_eq natDegree_touchard touchard_ne_zero

/-- The falling-factorial transform is also a left inverse of the Touchard transform. -/
theorem Poisson.fallingFactorialTransform_touchard (p : ℝ[X]) :
    Poisson.fallingFactorialTransform 1 (basisTransform touchard p) = p := by
  rw [Poisson.fallingFactorialTransform_one_eq_basisTransform]
  apply touchardTransform_injective
  rw [basisTransform_touchard_fallingFactorial_leftInverse]

/-- The Touchard transform takes ordinary multiplication to the parameter-one Poisson
product. -/
theorem basisTransform_touchard_mul (p q : ℝ[X]) :
    basisTransform touchard (p * q) =
      Poisson.starC 1 (basisTransform touchard p) (basisTransform touchard q) := by
  apply Poisson.fallingFactorialTransform_injective 1
  rw [Poisson.fallingFactorialTransform_touchard,
    Poisson.fallingFactorialTransform_starC,
    Poisson.fallingFactorialTransform_touchard,
    Poisson.fallingFactorialTransform_touchard]

/-- Products whose individual Touchard transforms are PF again have PF Touchard transform. -/
theorem isPFPolynomial_basisTransform_touchard_mul {p q : ℝ[X]}
    (hp : IsPFPolynomial (basisTransform touchard p))
    (hq : IsPFPolynomial (basisTransform touchard q)) :
    IsPFPolynomial (basisTransform touchard (p * q)) := by
  rw [basisTransform_touchard_mul]
  exact Poisson.IsPFPolynomial.preservesPF zero_le_one hp _ hq

/-- Finite products of factors with PF Touchard transforms have PF Touchard transform. -/
theorem isPFPolynomial_basisTransform_touchard_prod
    {ι : Type*} (s : Finset ι) (f : ι → ℝ[X])
    (hf : ∀ i ∈ s, IsPFPolynomial (basisTransform touchard (f i))) :
    IsPFPolynomial (basisTransform touchard (∏ i ∈ s, f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact touchardTransformPreservesPF IsPFPolynomial.one
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact isPFPolynomial_basisTransform_touchard_mul (hf i (by simp))
        (ih fun j hj ↦ hf j (by simp [hj]))

/-- The grouped-factor criterion, including a nonnegative scalar and the zero case. -/
theorem isPFPolynomial_basisTransform_touchard_C_mul_prod
    {ι : Type*} (s : Finset ι) (f : ι → ℝ[X]) {c : ℝ} (hc : 0 ≤ c)
    (hf : ∀ i ∈ s, IsPFPolynomial (basisTransform touchard (f i))) :
    IsPFPolynomial (basisTransform touchard (C c * ∏ i ∈ s, f i)) := by
  rw [show C c * ∏ i ∈ s, f i = c • (∏ i ∈ s, f i) by
    rw [Polynomial.smul_eq_C_mul], Polynomial.basisTransform_smul]
  exact (IsPFPolynomial.of_C_nonneg hc).mul
    (isPFPolynomial_basisTransform_touchard_prod s f hf)

private theorem basisTransform_touchard_comp_X_add_one (p : ℝ[X]) :
    basisTransform touchard (p.comp (X + C 1)) =
      basisTransform touchard p + (basisTransform touchard p).derivative := by
  induction p using Polynomial.induction_on with
  | C a => simp [touchard]
  | add p q hp hq =>
      simp only [add_comp, Polynomial.basisTransform_add, derivative_add, hp, hq]
      ring
  | monomial n a ih =>
      rw [show C a * X ^ (n + 1) = X * (C a * X ^ n) by ring]
      rw [mul_comp, X_comp, basisTransform_touchard_mul_X_add_C]
      rw [ih, basisTransform_touchard_X_mul]
      simp only [derivative_add, derivative_mul, derivative_X, one_mul]
      simp only [map_one]
      ring

/-- A falling-factorial prefix becomes a monomial, while the remaining source is translated. -/
theorem basisTransform_touchard_fallingFactorialPolynomial_mul
    (m : ℕ) (p : ℝ[X]) :
    basisTransform touchard (fallingFactorialPolynomial m * p) =
      X ^ m * basisTransform touchard (p.comp (X + C (m : ℝ))) := by
  induction m with
  | zero => simp [fallingFactorialPolynomial]
  | succ m ih =>
      rw [fallingFactorialPolynomial_succ_mul]
      rw [show (X - C (m : ℝ)) * fallingFactorialPolynomial m * p =
          (X + C (-(m : ℝ))) * (fallingFactorialPolynomial m * p) by
        simp only [map_neg]
        ring]
      rw [basisTransform_touchard_mul_X_add_C, ih]
      rw [derivative_mul, derivative_X_pow]
      have hshift := basisTransform_touchard_comp_X_add_one
        (p.comp (X + C (m : ℝ)))
      rw [show (p.comp (X + C (m : ℝ))).comp (X + C 1) =
          p.comp (X + C ((m + 1 : ℕ) : ℝ)) by
        rw [Polynomial.comp_assoc]
        congr 1
        push_cast
        simp only [add_comp, X_comp, C_comp, map_add]
        ring] at hshift
      rw [hshift]
      cases m with
      | zero =>
          have hC0 : (C 0 : ℝ[X]) = 0 := map_zero C
          norm_num [hC0]
          ring
      | succ m =>
          rw [Nat.add_sub_cancel]
          push_cast
          simp only [map_neg, map_add, map_one]
          ring

/-- A falling-factorial prefix preserves the grouped PF certificate after translation. -/
theorem isPFPolynomial_basisTransform_touchard_fallingFactorial_mul
    (m : ℕ) {p : ℝ[X]}
    (hp : IsPFPolynomial
      (basisTransform touchard (p.comp (X + C (m : ℝ))))) :
    IsPFPolynomial
      (basisTransform touchard (fallingFactorialPolynomial m * p)) := by
  rw [basisTransform_touchard_fallingFactorialPolynomial_mul]
  exact (isPFPolynomial_X_pow m).mul hp

/-- Explicit grouped-factor interface for a falling-factorial prefix. -/
theorem isPFPolynomial_touchard_fallingFactorial_C_mul_prod
    {ι : Type*} (m : ℕ) (s : Finset ι) (f : ι → ℝ[X]) {c : ℝ}
    (hc : 0 ≤ c)
    (hf : ∀ i ∈ s, IsPFPolynomial
      (basisTransform touchard ((f i).comp (X + C (m : ℝ))))) :
    IsPFPolynomial
      (basisTransform touchard
        (fallingFactorialPolynomial m * (C c * ∏ i ∈ s, f i))) := by
  classical
  apply isPFPolynomial_basisTransform_touchard_fallingFactorial_mul
  have hprod : (∏ i ∈ s, f i).comp (X + C (m : ℝ)) =
      ∏ i ∈ s, (f i).comp (X + C (m : ℝ)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        rw [Finset.prod_insert hi, Finset.prod_insert hi, mul_comp,
          ih (fun j hj ↦ hf j (by simp [hj]))]
  rw [mul_comp, C_comp, hprod]
  exact isPFPolynomial_basisTransform_touchard_C_mul_prod s
    (fun i ↦ (f i).comp (X + C (m : ℝ))) hc hf

/-! ## Exact grouped cubics -/

private theorem basisTransform_touchard_X_add_C (r : ℝ) :
    basisTransform touchard (X + C r) = X + C r := by
  rw [Polynomial.basisTransform_add]
  rw [show (X : ℝ[X]) = X ^ 1 by simp, Polynomial.basisTransform_X_pow]
  simp [touchard]

/-- Touchard transform of a real linear factor times a conjugate-pair quadratic. -/
theorem basisTransform_touchard_linear_mul_quadratic (a b w : ℝ) :
    basisTransform touchard ((X + C a) * ((X + C b) ^ 2 + C w)) =
      X ^ 3 + C (3 + a + 2 * b) * X ^ 2 +
        C (1 + a + 2 * b + b ^ 2 + w + 2 * a * b) * X +
          C (a * (b ^ 2 + w)) := by
  rw [basisTransform_touchard_mul_X_add_C]
  rw [Polynomial.basisTransform_add]
  rw [show (X + C b) ^ 2 = (X + C b) * (X + C b) by ring]
  rw [basisTransform_touchard_mul_X_add_C]
  rw [basisTransform_touchard_X_add_C]
  simp only [Polynomial.basisTransform_C, touchard_zero, mul_one,
    derivative_add, derivative_X, derivative_C, add_zero]
  norm_num [map_add, map_mul, map_pow]
  simp only [map_ofNat]
  ring

/-- A monic cubic with coefficients `A,B,C` is PF exactly when the coefficients and cubic
discriminant are nonnegative.  Weak inequalities include repeated-root boundaries. -/
theorem isPFPolynomial_monic_cubic_iff (A B C₀ : ℝ) :
    IsPFPolynomial
        (X ^ 3 + C A * X ^ 2 + C B * X + C C₀) ↔
      0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ C₀ ∧
        0 ≤ A ^ 2 * B ^ 2 - 4 * B ^ 3 - 4 * A ^ 3 * C₀ -
          27 * C₀ ^ 2 + 18 * A * B * C₀ := by
  let p : ℝ[X] := X ^ 3 + C A * X ^ 2 + C B * X + C C₀
  have hp0 : p ≠ 0 := by
    intro hp
    have := congrArg (fun q : ℝ[X] ↦ q.coeff 3) hp
    simp [p] at this
  have hpdeg : p.natDegree ≤ 3 := by
    dsimp [p]
    compute_degree
  have hdisc : cubicDiscr p =
      A ^ 2 * B ^ 2 - 4 * B ^ 3 - 4 * A ^ 3 * C₀ -
        27 * C₀ ^ 2 + 18 * A * B * C₀ := by
    dsimp [p]
    rw [show X ^ 3 + C A * X ^ 2 + C B * X + C C₀ =
      C 1 * X ^ 3 + C A * X ^ 2 + C B * X + C C₀ by simp]
    rw [cubicDiscr_of_coeffs]
    ring
  constructor
  · intro hp
    have hA : 0 ≤ A := by simpa [p] using hp.hasNonnegCoeffs 2
    have hB : 0 ≤ B := by simpa [p] using hp.hasNonnegCoeffs 1
    have hC : 0 ≤ C₀ := by simpa [p] using hp.hasNonnegCoeffs 0
    have hsplits : p.Splits := hp.eq_zero_or_splits.resolve_left hp0
    have hd := cubicDiscr_nonneg_of_splits_natDegree_le_three hpdeg hsplits
    rw [hdisc] at hd
    exact ⟨hA, hB, hC, hd⟩
  · rintro ⟨hA, hB, hC, hd⟩
    apply IsPFPolynomial.of_realRooted_nonneg
    · exact (((hasNonnegCoeffs_X.pow 3).add
        ((hasNonnegCoeffs_C hA).mul (hasNonnegCoeffs_X.pow 2))).add
          ((hasNonnegCoeffs_C hB).mul hasNonnegCoeffs_X)).add
            (hasNonnegCoeffs_C hC)
    · apply splits_of_natDegree_le_three_cubicDiscr_nonneg hpdeg
      rw [hdisc]
      exact hd

/-- Exact coefficient/discriminant criterion for the grouped cubic source. -/
theorem isPFPolynomial_touchard_linear_mul_quadratic_iff
    (a b w : ℝ) :
    IsPFPolynomial
        (basisTransform touchard ((X + C a) * ((X + C b) ^ 2 + C w))) ↔
      let A := 3 + a + 2 * b
      let B := 1 + a + 2 * b + b ^ 2 + w + 2 * a * b
      let C₀ := a * (b ^ 2 + w)
      0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ C₀ ∧
        0 ≤ A ^ 2 * B ^ 2 - 4 * B ^ 3 - 4 * A ^ 3 * C₀ -
          27 * C₀ ^ 2 + 18 * A * B * C₀ := by
  rw [basisTransform_touchard_linear_mul_quadratic]
  exact isPFPolynomial_monic_cubic_iff _ _ _

/-- In the half-shifted subfamily the transformed cubic factors into a linear and a
quadratic factor. -/
theorem basisTransform_touchard_half_shifted_cubic (b w : ℝ) :
    basisTransform touchard
        ((X + C (b + 1 / 2)) * ((X + C b) ^ 2 + C w)) =
      (X + C (b + 1 / 2)) *
        (X ^ 2 + C (2 * b + 3) * X + C (b ^ 2 + w)) := by
  rw [basisTransform_touchard_linear_mul_quadratic]
  norm_num [map_add, map_mul, map_pow]
  simp only [map_ofNat]
  have hhalf : (C (1 / 2 : ℝ) : ℝ[X]) * 2 = 1 := by
    change C (1 / 2 : ℝ) * C 2 = C 1
    rw [← C_mul]
    norm_num
  linear_combination -X * hhalf

/-- Sharp grouped cubic region: for `w ≥ 0`, the half-shifted cubic has PF Touchard
transform exactly on `b ≥ -1/2` and `w ≤ 3b+9/4`. -/
theorem isPFPolynomial_touchard_half_shifted_cubic_iff
    {b w : ℝ} (hw : 0 ≤ w) :
    IsPFPolynomial
        (basisTransform touchard
          ((X + C (b + 1 / 2)) * ((X + C b) ^ 2 + C w))) ↔
      -(1 / 2 : ℝ) ≤ b ∧ w ≤ 3 * b + 9 / 4 := by
  let q : ℝ[X] := X ^ 2 + C (2 * b + 3) * X + C (b ^ 2 + w)
  have hq0 : q ≠ 0 := by
    exact (Polynomial.isMonicOfDegree_add_add_two
      (2 * b + 3) (b ^ 2 + w)).ne_zero
  rw [basisTransform_touchard_half_shifted_cubic]
  constructor
  · intro hp
    have hprod0 : (X + C (b + 1 / 2)) * q ≠ 0 :=
      mul_ne_zero (by simpa [sub_eq_add_neg] using X_sub_C_ne_zero (-(b + 1 / 2))) hq0
    have hroot : ((X + C (b + 1 / 2)) * q).IsRoot (-(b + 1 / 2)) := by
      simp [Polynomial.IsRoot]
    have hroot_nonpos := hp.roots_nonpos (-(b + 1 / 2))
      ((mem_roots hprod0).mpr hroot)
    have hqpf : IsPFPolynomial q := by
      apply hp.of_X_sub_C_mul_factor (u := -(b + 1 / 2))
      rw [show X - C (-(b + 1 / 2)) = X + C (b + 1 / 2) by
        simp only [map_neg, map_add]
        ring]
    have hqsplit : q.Splits := hqpf.eq_zero_or_splits.resolve_left hq0
    have hdisc : 0 ≤ (2 * b + 3) ^ 2 - 4 * (b ^ 2 + w) := by
      apply monicQuadraticPoly_splits_iff_discrim_nonneg.mp
      exact hqsplit
    constructor <;> nlinarith
  · rintro ⟨hb, hupper⟩
    have hlinear : IsPFPolynomial (X + C (b + 1 / 2)) :=
      isPFPolynomial_X_add_C (by linarith)
    have hqnn : HasNonnegCoeffs q := by
      dsimp [q]
      exact ((hasNonnegCoeffs_X.pow 2).add
        ((hasNonnegCoeffs_C (by linarith)).mul hasNonnegCoeffs_X)).add
          (hasNonnegCoeffs_C (by positivity))
    have hqsplit : q.Splits := by
      apply monicQuadraticPoly_splits_iff_discrim_nonneg.mpr
      nlinarith
    exact hlinear.mul (IsPFPolynomial.of_realRooted_nonneg hqnn hqsplit)

/-- The basic grouped example reaches `w = 1/2`, beyond the ungrouped quadratic region. -/
theorem isPFPolynomial_touchard_half_mul_y_sq_add_half :
    IsPFPolynomial
      (basisTransform touchard ((X + C (1 / 2)) * (X ^ 2 + C (1 / 2)))) := by
  have h := (isPFPolynomial_touchard_half_shifted_cubic_iff
    (b := 0) (w := 1 / 2) (by norm_num)).mpr (by norm_num)
  simpa only [map_zero, add_zero, zero_add] using h

/-- The corresponding ungrouped quadratic does not split over the reals. -/
theorem not_splits_basisTransform_touchard_y_sq_add_half :
    ¬(basisTransform touchard (X ^ 2 + C (1 / 2))).Splits := by
  rw [show basisTransform touchard (X ^ 2 + C (1 / 2)) =
      X ^ 2 + X + C (1 / 2) by
    rw [Polynomial.basisTransform_add, Polynomial.basisTransform_X_pow,
      Polynomial.basisTransform_C, touchard_two, touchard_zero]
    ring]
  simpa using
    (monicQuadraticPoly_not_splits_iff_discrim_neg.mpr (by norm_num) :
      ¬(X ^ 2 + C 1 * X + C (1 / 2) : ℝ[X]).Splits)

end

end RealRooted
