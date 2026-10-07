import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Tactic.LinearCombination

/-!
# Square roots of power series

For a `ℚ`-algebra `A` and `f : A⟦X⟧` with constant coefficient `1`, `PowerSeries.sqrt f` is
the binomial series `(1 + (f - 1)) ^ (1/2)`. It is the unique square root of `f` with
constant coefficient `1`; uniqueness needs no domain hypothesis, since the sum of two such
square roots is a unit.

## Main results

* `PowerSeries.sqrt_sq`: `sqrt f ^ 2 = f`.
* `PowerSeries.eq_sqrt_of_sq_eq`: uniqueness.
* `PowerSeries.map_sqrt`: compatibility with ring homomorphisms.
* `PowerSeries.two_mul_mul_derivative_sqrt`: the linear differential equation
  `2 f (sqrt f)' = f' sqrt f`.
-/

namespace PowerSeries

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- The square root `(1 + (f - 1)) ^ (1/2)` of a power series, by the binomial series.
It is meaningful when `constantCoeff f = 1`. -/
noncomputable def sqrt (f : A⟦X⟧) : A⟦X⟧ :=
  (binomialSeries A (2⁻¹ : ℚ)).subst (f - 1)

omit [Algebra ℚ A] in
private theorem constantCoeff_sub_one {f : A⟦X⟧} (hf : constantCoeff f = 1) :
    constantCoeff (f - 1) = 0 := by
  simp [hf]

theorem sqrt_sq {f : A⟦X⟧} (hf : constantCoeff f = 1) : sqrt f ^ 2 = f := by
  have ha : HasSubst (f - 1) := .of_constantCoeff_zero' (constantCoeff_sub_one hf)
  have hB : binomialSeries A (2⁻¹ : ℚ) ^ 2 = 1 + X := by
    rw [sq, ← binomialSeries_add, show (2⁻¹ + 2⁻¹ : ℚ) = ((1 : ℕ) : ℚ) by norm_num,
      binomialSeries_nat, pow_one]
  rw [sqrt, ← subst_pow ha, hB, ← coe_substAlgHom ha, map_add, map_one, coe_substAlgHom,
    subst_X ha]
  ring

@[simp]
theorem constantCoeff_sqrt {f : A⟦X⟧} (hf : constantCoeff f = 1) :
    constantCoeff (sqrt f) = 1 := by
  have := constantCoeff_subst_of_constantCoeff_zero (constantCoeff_sub_one hf)
    (binomialSeries A (2⁻¹ : ℚ))
  simp only [binomialSeries_constantCoeff, map_one] at this
  exact this

theorem isUnit_sqrt {f : A⟦X⟧} (hf : constantCoeff f = 1) : IsUnit (sqrt f) := by
  rw [isUnit_iff_constantCoeff, constantCoeff_sqrt hf]
  exact isUnit_one

private theorem isUnit_two : IsUnit (2 : A) := by
  have := (show IsUnit (2 : ℚ) by norm_num).map (algebraMap ℚ A)
  rwa [map_ofNat] at this

/-- Uniqueness of the square root with constant coefficient `1`. -/
theorem eq_sqrt_of_sq_eq {f t : A⟦X⟧} (hf : constantCoeff f = 1)
    (ht : constantCoeff t = 1) (h : t ^ 2 = f) : t = sqrt f := by
  have hu : IsUnit (t + sqrt f) := by
    rw [isUnit_iff_constantCoeff, map_add, ht, constantCoeff_sqrt hf, one_add_one_eq_two]
    exact isUnit_two
  have h0 : (t - sqrt f) * (t + sqrt f) = 0 := by
    linear_combination h - sqrt_sq hf
  exact sub_eq_zero.mp (hu.mul_left_eq_zero.mp h0)

@[simp]
theorem sqrt_one : sqrt (1 : A⟦X⟧) = 1 :=
  (eq_sqrt_of_sq_eq (by simp) (by simp) (by simp)).symm

theorem sqrt_sq_of_constantCoeff {t : A⟦X⟧} (ht : constantCoeff t = 1) : sqrt (t ^ 2) = t :=
  (eq_sqrt_of_sq_eq (by simp [ht]) ht rfl).symm

theorem sqrt_mul {f g : A⟦X⟧} (hf : constantCoeff f = 1) (hg : constantCoeff g = 1) :
    sqrt (f * g) = sqrt f * sqrt g :=
  (eq_sqrt_of_sq_eq (by simp [hf, hg]) (by simp [hf, hg])
    (by rw [mul_pow, sqrt_sq hf, sqrt_sq hg])).symm

/-- The square root commutes with ring homomorphisms between `ℚ`-algebras. -/
theorem map_sqrt {B : Type*} [CommRing B] [Algebra ℚ B] (φ : A →+* B) {f : A⟦X⟧}
    (hf : constantCoeff f = 1) : map φ (sqrt f) = sqrt (map φ f) := by
  have hφf : constantCoeff (map φ f) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      hf, map_one]
  refine eq_sqrt_of_sq_eq hφf ?_ ?_
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_sqrt hf, map_one]
  · rw [← map_pow, sqrt_sq hf]

theorem two_mul_sqrt_mul_derivative {f : A⟦X⟧} (hf : constantCoeff f = 1) :
    2 * sqrt f * derivative (sqrt f) = derivative f := by
  have := congrArg derivative (sqrt_sq hf)
  rw [sq, Derivation.leibniz, smul_eq_mul] at this
  linear_combination this

/-- The linear differential equation `2 f (sqrt f)' = f' sqrt f`. -/
theorem two_mul_mul_derivative_sqrt {f : A⟦X⟧} (hf : constantCoeff f = 1) :
    2 * f * derivative (sqrt f) = derivative f * sqrt f := by
  linear_combination (-2 * derivative (sqrt f)) * sqrt_sq hf +
    sqrt f * two_mul_sqrt_mul_derivative hf

end PowerSeries
