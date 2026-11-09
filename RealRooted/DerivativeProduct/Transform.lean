module

public import RealRooted.DerivativeProduct.Associative
public import RealRooted.Mathlib.Algebra.Polynomial.BasisTransform
import Mathlib.Tactic

/-!
# The generalized geometric transform and the diamond family

The *generalized geometric polynomials* `G_{β,n}` (Boyadzhiev; Dil–Kurt, *Polynomials related to
harmonic numbers and evaluation of harmonic number series II*, equation (7)) are defined by the
recurrence `G_{β,0} = 1`, `G_{β,n+1} = β * X * G_{β,n} + X * (X + 1) * G_{β,n}'`.  The linear
transform `T_β` sending `t ^ n` to `G_{β,n}` sends the descending Pochhammer polynomial
`t_(n) = t (t - 1) ... (t - n + 1)` to `(β)_n * X ^ n`, and it turns ordinary multiplication
into the diamond product `*_β` of `RealRooted.DerivativeProduct.Associative`:

`T_β (u * v) = T_β u *_β T_β v`.

This generalizes `fallingFactorialTransform_starC` for Poisson products.  Brändén's `E`
transform is the case `β = 1` (see `RealRooted.DerivativeProduct.Diamond`).
-/

@[expose] public section

open Polynomial

namespace RealRooted

noncomputable section

/-- The generalized geometric polynomials `G_{β,n}`, defined by
`G_{β,0} = 1` and `G_{β,n+1} = β * X * G_{β,n} + X * (1 + X) * G_{β,n}'`. -/
def generalizedGeometricPolynomial (β : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 =>
      C β * X * generalizedGeometricPolynomial β n +
        X * (1 + X) * derivative (generalizedGeometricPolynomial β n)

@[simp] theorem generalizedGeometricPolynomial_zero (β : ℝ) :
    generalizedGeometricPolynomial β 0 = 1 :=
  rfl

theorem generalizedGeometricPolynomial_succ (β : ℝ) (n : ℕ) :
    generalizedGeometricPolynomial β (n + 1) =
      C β * X * generalizedGeometricPolynomial β n +
        X * (1 + X) * derivative (generalizedGeometricPolynomial β n) :=
  rfl

/-- The linear transform sending `X ^ n` to the generalized geometric polynomial `G_{β,n}`. -/
def betaTransform (β : ℝ) (p : ℝ[X]) : ℝ[X] :=
  basisTransform (generalizedGeometricPolynomial β) p

@[simp] theorem betaTransform_X_pow (β : ℝ) (n : ℕ) :
    betaTransform β (X ^ n) = generalizedGeometricPolynomial β n :=
  basisTransform_X_pow _ n

theorem betaTransform_add (β : ℝ) (p q : ℝ[X]) :
    betaTransform β (p + q) = betaTransform β p + betaTransform β q :=
  basisTransform_add _ p q

theorem betaTransform_C_mul (β a : ℝ) (p : ℝ[X]) :
    betaTransform β (C a * p) = C a * betaTransform β p := by
  rw [← smul_eq_C_mul]
  exact basisTransform_smul _ a p

@[simp] theorem betaTransform_one (β : ℝ) : betaTransform β 1 = 1 := by
  have h := betaTransform_X_pow β 0
  rw [pow_zero] at h
  exact h

theorem betaTransform_C (β a : ℝ) : betaTransform β (C a) = C a := by
  simpa using betaTransform_C_mul β a 1

/-- Multiplication by `X` before `betaTransform` becomes a first-order differential operator
afterwards. -/
theorem betaTransform_X_mul (β : ℝ) (p : ℝ[X]) :
    betaTransform β (X * p) =
      C β * X * betaTransform β p + X * (1 + X) * derivative (betaTransform β p) :=
  basisTransform_X_mul_of_succ_derivative (generalizedGeometricPolynomial β) (C β * X)
    (X * (1 + X)) (fun _ ↦ rfl) p

/-- Affine-factor form of `betaTransform_X_mul`. -/
theorem betaTransform_X_add_C_mul (β r : ℝ) (p : ℝ[X]) :
    betaTransform β ((X + C r) * p) =
      (C β * X + C r) * betaTransform β p +
        X * (1 + X) * derivative (betaTransform β p) :=
  basisTransform_mul_X_add_C_of_succ_derivative (generalizedGeometricPolynomial β) (C β * X)
    (X * (1 + X)) (fun _ ↦ rfl) r p

/-- The transform `T_β` sends the descending Pochhammer polynomial `t_(n)` to
`(β)_n * X ^ n`. -/
theorem betaTransform_descPochhammer (β : ℝ) :
    ∀ n : ℕ, betaTransform β (descPochhammer ℝ n) =
      C ((ascPochhammer ℝ n).eval β) * X ^ n
  | 0 => by
      rw [descPochhammer_zero, ascPochhammer_zero, eval_one, C_1, one_mul, pow_zero,
        betaTransform_one]
  | n + 1 => by
      rw [descPochhammer_succ_right, mul_comm (descPochhammer ℝ n) (X - (n : ℝ[X])),
        show X - (n : ℝ[X]) = X + C (-(n : ℝ)) by simp [sub_eq_add_neg],
        betaTransform_X_add_C_mul, betaTransform_descPochhammer β n, ascPochhammer_succ_eval,
        derivative_C_mul_X_pow]
      cases n with
      | zero => simp
      | succ n =>
          rw [Nat.add_sub_cancel]
          push_cast
          simp only [map_mul, map_add, map_neg, map_natCast, map_one]
          ring

/-- Multiplication by `X` before `betaTransform` is `β` times the diamond product with `X`
afterwards. -/
theorem betaTransform_X_mul_eq {β : ℝ} (hβ : β ≠ 0) (p : ℝ[X]) :
    betaTransform β (X * p) = C β * betaProduct β X (betaTransform β p) := by
  rw [betaTransform_X_mul, betaProduct_X_left]
  have h : C β * C β⁻¹ = 1 := by
    rw [← C_mul, mul_inv_cancel₀ hβ, C_1]
  linear_combination (-(X * (X + 1) * derivative (betaTransform β p))) * h

private theorem betaTransform_X_mul_mul {β : ℝ} (hβ : 0 < β) {u : ℝ[X]}
    (hu : ∀ v, betaTransform β (u * v) = betaProduct β (betaTransform β u) (betaTransform β v))
    (v : ℝ[X]) :
    betaTransform β (X * u * v) =
      betaProduct β (betaTransform β (X * u)) (betaTransform β v) := by
  rw [mul_assoc, betaTransform_X_mul_eq hβ.ne' (u * v), hu v,
    ← betaProduct_assoc_X_left hβ, betaTransform_X_mul_eq hβ.ne' u, betaProduct_C_mul_left]

/-- The generalized geometric transform turns ordinary multiplication into the diamond product
`*_β`: `T_β (u * v) = T_β u *_β T_β v` for `β > 0`.  This generalizes
`fallingFactorialTransform_starC`.  Since `T_β` is surjective (`betaTransform_surjective`),
associativity and commutativity of `*_β` follow from those of ordinary multiplication; see also
`betaProduct_assoc` for a direct proof. -/
theorem betaTransform_mul {β : ℝ} (hβ : 0 < β) (u v : ℝ[X]) :
    betaTransform β (u * v) = betaProduct β (betaTransform β u) (betaTransform β v) := by
  induction u using Polynomial.induction_on generalizing v with
  | C a => rw [betaTransform_C_mul, betaTransform_C, betaProduct_C_left]
  | add p q hp hq =>
      rw [add_mul, betaTransform_add, betaTransform_add, betaProduct_add_left, hp v, hq v]
  | monomial n a ih =>
      rw [show C a * X ^ (n + 1) = X * (C a * X ^ n) by ring]
      exact betaTransform_X_mul_mul hβ ih v

/-- The preimage transform, sending `X ^ n` to `t_(n) / (β)_n`, a right inverse of
`betaTransform β` for `β > 0`. -/
def betaPreimage (β : ℝ) (p : ℝ[X]) : ℝ[X] :=
  basisTransform (fun n ↦ C ((ascPochhammer ℝ n).eval β)⁻¹ * descPochhammer ℝ n) p

theorem betaPreimage_add (β : ℝ) (p q : ℝ[X]) :
    betaPreimage β (p + q) = betaPreimage β p + betaPreimage β q :=
  basisTransform_add _ p q

/-- `betaPreimage β` is a right inverse of `betaTransform β` for `β > 0`. -/
theorem betaTransform_betaPreimage {β : ℝ} (hβ : 0 < β) (p : ℝ[X]) :
    betaTransform β (betaPreimage β p) = p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [betaPreimage_add, betaTransform_add, hp, hq]
  | monomial n a =>
      have hne : (ascPochhammer ℝ n).eval β ≠ 0 := (ascPochhammer_pos n β hβ).ne'
      have h : C ((ascPochhammer ℝ n).eval β)⁻¹ * C ((ascPochhammer ℝ n).eval β) = 1 := by
        rw [← C_mul, inv_mul_cancel₀ hne, C_1]
      rw [betaPreimage, basisTransform_monomial, betaTransform_C_mul, betaTransform_C_mul,
        betaTransform_descPochhammer, ← C_mul_X_pow_eq_monomial]
      linear_combination (C a * X ^ n) * h

/-- The generalized geometric transform is surjective for `β > 0`. -/
theorem betaTransform_surjective {β : ℝ} (hβ : 0 < β) : Function.Surjective (betaTransform β) :=
  fun p ↦ ⟨betaPreimage β p, betaTransform_betaPreimage hβ p⟩

/-- The diamond product `*_β` is the transport of ordinary multiplication through
`betaPreimage`. -/
theorem betaProduct_eq_betaTransform {β : ℝ} (hβ : 0 < β) (f g : ℝ[X]) :
    betaProduct β f g = betaTransform β (betaPreimage β f * betaPreimage β g) := by
  rw [betaTransform_mul hβ, betaTransform_betaPreimage hβ, betaTransform_betaPreimage hβ]

end

end RealRooted
