import RealRooted.Mathlib.RingTheory.PowerSeries.Sqrt
import RealRooted.Mathlib.RingTheory.PowerSeries.MapDerivation
import RealRooted.Mathlib.Algebra.Polynomial.Antiderivative
import Mathlib.Algebra.Polynomial.Derivation

/-!
# The kernel `√D(v, y)` and its moments

The kernel `D(v, y) = 1 - v(2 - v) y + (v/4) y²` in `ℚ[v]⟦y⟧`, the polynomials
`d_r(v) = [y^r] √D`, and the moments `m(r, J) = ∫_0^1 v^J d_r(v) dv`. The transformed
big-descent polynomials have Gegenbauer coordinates
`q_(J+2r, J) = (2J + 3)(c_r(J) - c_(r-1)(J)/2)` for `r ≥ 3`, with `c_r(J) = -m(r, J)`.

The key identity is the chain rule `2 ∂_v(D √D) = 3 √D ∂_v D`. With `a = 1 - y/2` and
`K_t = [y^t](a D √D)` it gives `K_t' = [y^t](3 y a (v - 1 + y/8) √D)`, and
`D(1, y) = a²` gives `K_t(1) = [y^t] a⁴`, which vanishes for `t ≥ 5`.
-/

open Polynomial

noncomputable section

namespace RealRooted.BigDescents321

/-- The kernel `D(v, y) = 1 - v(2 - v) y + (v/4) y²` in `ℚ[v]⟦y⟧`. -/
def kernelDisc : PowerSeries ℚ[X] :=
  1 - PowerSeries.C (X * (2 - X)) * PowerSeries.X +
    PowerSeries.C (C (1 / 4) * X) * PowerSeries.X ^ 2

@[simp] theorem constantCoeff_kernelDisc : PowerSeries.constantCoeff kernelDisc = 1 := by
  simp [kernelDisc]

/-- `√D` in `ℚ[v]⟦y⟧`. -/
def kernelSqrt : PowerSeries ℚ[X] := PowerSeries.sqrt kernelDisc

/-- `d_r(v) = [y^r] √D(v, y)`. -/
def kernelPoly (r : ℕ) : ℚ[X] := PowerSeries.coeff r kernelSqrt

/-- The partial derivative `∂_v` on `ℚ[v]⟦y⟧`. -/
abbrev partialV : PowerSeries ℚ[X] → PowerSeries ℚ[X] :=
  PowerSeries.mapDerivation (Polynomial.derivative' (R := ℚ))

theorem partialV_mul (f g : PowerSeries ℚ[X]) :
    partialV (f * g) = partialV f * g + f * partialV g :=
  PowerSeries.mapDerivation_mul _ f g

theorem partialV_kernelDisc :
    partialV kernelDisc = PowerSeries.C (2 * X - 2) * PowerSeries.X +
      PowerSeries.C (C (1 / 4)) * PowerSeries.X ^ 2 := by
  simp only [partialV, kernelDisc, PowerSeries.mapDerivation_add, PowerSeries.mapDerivation_sub,
    PowerSeries.mapDerivation_mul, PowerSeries.mapDerivation_C, PowerSeries.mapDerivation_X,
    PowerSeries.mapDerivation_one, PowerSeries.mapDerivation_X_pow, mul_zero, add_zero]
  simp only [derivative'_apply, derivative_mul, derivative_X, derivative_sub, derivative_ofNat,
    derivative_C, zero_mul, zero_add, mul_one, one_mul, zero_sub]
  rw [show (2 - X + X * -1 : ℚ[X]) = -(2 * X - 2) by ring, map_neg]
  ring

/-- The chain rule `2 ∂_v(D √D) = 3 √D ∂_v D`. -/
theorem two_mul_partialV_disc_mul_sqrt :
    2 * partialV (kernelDisc * kernelSqrt) = 3 * kernelSqrt * partialV kernelDisc := by
  have hS : kernelSqrt * kernelSqrt = kernelDisc := by
    rw [← sq]; exact PowerSeries.sqrt_sq constantCoeff_kernelDisc
  have h1 : partialV kernelDisc = 2 * kernelSqrt * partialV kernelSqrt := by
    rw [← hS, partialV_mul]; ring
  have h2 := partialV_mul kernelDisc kernelSqrt
  have hu : IsUnit kernelSqrt := PowerSeries.isUnit_sqrt constantCoeff_kernelDisc
  refine hu.mul_left_cancel ?_
  rw [h2]
  linear_combination (2 * kernelSqrt * kernelSqrt - 3 * kernelDisc) * h1 +
    (4 * kernelSqrt * partialV kernelSqrt - 3 * partialV kernelDisc) * hS

/-- `a = 1 - y/2` in `ℚ[v]⟦y⟧`. -/
def kernelHalf : PowerSeries ℚ[X] := 1 - PowerSeries.C (C (1 / 2)) * PowerSeries.X

theorem partialV_kernelHalf : partialV kernelHalf = 0 := by
  simp [partialV, kernelHalf, PowerSeries.mapDerivation_sub, PowerSeries.mapDerivation_mul]

/-- `K_t = [y^t] (a D √D)`. -/
def kernelK (t : ℕ) : ℚ[X] := PowerSeries.coeff t (kernelHalf * kernelDisc * kernelSqrt)

/-- `L_t = [y^t] ((3/2) a √D ∂_v D)`. -/
def kernelL (t : ℕ) : ℚ[X] :=
  PowerSeries.coeff t (PowerSeries.C (C (3 / 2)) * kernelHalf * kernelSqrt * partialV kernelDisc)

theorem derivative_kernelK (t : ℕ) : derivative (kernelK t) = kernelL t := by
  have h : partialV (kernelHalf * kernelDisc * kernelSqrt) =
      PowerSeries.C (C (3 / 2)) * kernelHalf * kernelSqrt * partialV kernelDisc := by
    have h2 := two_mul_partialV_disc_mul_sqrt
    have h4 : (2 : PowerSeries ℚ[X]) * PowerSeries.C (C (1 / 2)) = 1 := by
      rw [show (2 : PowerSeries ℚ[X]) = PowerSeries.C (C 2) by rw [map_ofNat C, map_ofNat],
        ← map_mul, ← C_mul]
      norm_num
    have h6 : (PowerSeries.C (C (3 / 2)) : PowerSeries ℚ[X]) = PowerSeries.C (C (1 / 2)) * 3 := by
      rw [show (3 : PowerSeries ℚ[X]) = PowerSeries.C (C 3) by rw [map_ofNat C, map_ofNat],
        ← map_mul, ← C_mul]
      norm_num
    have h5 : partialV (kernelDisc * kernelSqrt) =
        PowerSeries.C (C (3 / 2)) * kernelSqrt * partialV kernelDisc := by
      rw [h6]
      linear_combination PowerSeries.C (C (1 / 2)) * h2 - partialV (kernelDisc * kernelSqrt) * h4
    rw [mul_assoc, partialV_mul, partialV_kernelHalf, zero_mul, zero_add, h5]
    ring
  have := congrArg (PowerSeries.coeff t) h
  simpa [kernelK, kernelL, partialV] using this

/-! ### Evaluation at `v = 1` and `v = 0` -/

/-- `a = 1 - y/2` in `ℚ⟦y⟧`. -/
def halfQ : PowerSeries ℚ := 1 - PowerSeries.C (1 / 2) * PowerSeries.X

private theorem map_eval_kernelHalf (x : ℚ) :
    PowerSeries.map (evalRingHom x) kernelHalf = halfQ := by
  simp [kernelHalf, halfQ]

/-- `D(1, y) = (1 - y/2)²`. -/
private theorem map_eval_one_kernelDisc :
    PowerSeries.map (evalRingHom 1) kernelDisc = halfQ ^ 2 := by
  simp only [kernelDisc, halfQ, map_add, map_sub, map_mul, map_one, PowerSeries.map_C,
    PowerSeries.map_X, map_pow, coe_evalRingHom, eval_X, eval_ofNat, eval_C]
  have h : (PowerSeries.C (1 / 2 : ℚ)) * PowerSeries.C (1 / 2) = PowerSeries.C (1 / 4) := by
    rw [← map_mul]; norm_num
  have h2 : (2 : PowerSeries ℚ) * PowerSeries.C (1 / 2) = 1 := by
    rw [show (2 : PowerSeries ℚ) = PowerSeries.C 2 from (map_ofNat _ 2).symm, ← map_mul]
    norm_num
  have h7 : (PowerSeries.C (2 : ℚ)) = 2 := map_ofNat _ 2
  norm_num
  linear_combination (-PowerSeries.X ^ 2) * h + PowerSeries.X * h2 - PowerSeries.X * h7

private theorem map_eval_zero_kernelDisc :
    PowerSeries.map (evalRingHom 0) kernelDisc = 1 := by
  simp [kernelDisc]

private theorem constantCoeff_halfQ : PowerSeries.constantCoeff halfQ = 1 := by
  simp [halfQ]

/-- `K_t(1) = [y^t] (1 - y/2)⁴`. -/
theorem eval_one_kernelK (t : ℕ) :
    (kernelK t).eval 1 = PowerSeries.coeff t (halfQ ^ 4) := by
  have h : PowerSeries.map (evalRingHom 1) (kernelHalf * kernelDisc * kernelSqrt) =
      halfQ ^ 4 := by
    rw [map_mul, map_mul, map_eval_kernelHalf, kernelSqrt,
      PowerSeries.map_sqrt _ constantCoeff_kernelDisc, map_eval_one_kernelDisc,
      PowerSeries.sqrt_sq_of_constantCoeff constantCoeff_halfQ]
    ring
  rw [kernelK, ← coe_evalRingHom, ← PowerSeries.coeff_map, h]

/-- `K_t(0) = [y^t] (1 - y/2)`. -/
theorem eval_zero_kernelK (t : ℕ) :
    (kernelK t).eval 0 = PowerSeries.coeff t halfQ := by
  have h : PowerSeries.map (evalRingHom 0) (kernelHalf * kernelDisc * kernelSqrt) = halfQ := by
    rw [map_mul, map_mul, map_eval_kernelHalf, kernelSqrt,
      PowerSeries.map_sqrt _ constantCoeff_kernelDisc, map_eval_zero_kernelDisc,
      PowerSeries.sqrt_one, mul_one, mul_one]
  rw [kernelK, ← coe_evalRingHom, ← PowerSeries.coeff_map, h]

theorem halfQ_pow_four : halfQ ^ 4 = 1 - 2 * PowerSeries.X +
    PowerSeries.C (3 / 2) * PowerSeries.X ^ 2 - PowerSeries.C (1 / 2) * PowerSeries.X ^ 3 +
    PowerSeries.C (1 / 16) * PowerSeries.X ^ 4 := by
  simp only [halfQ]
  have h1 : (PowerSeries.C (1 / 2 : ℚ)) ^ 2 = PowerSeries.C (1 / 4) := by
    rw [← map_pow]; norm_num
  have h2 : (PowerSeries.C (1 / 2 : ℚ)) ^ 3 = PowerSeries.C (1 / 8) := by
    rw [← map_pow]; norm_num
  have h3 : (PowerSeries.C (1 / 2 : ℚ)) ^ 4 = PowerSeries.C (1 / 16) := by
    rw [← map_pow]; norm_num
  have h4 : (PowerSeries.C (3 / 2 : ℚ)) = 6 * PowerSeries.C (1 / 4) := by
    rw [show (6 : PowerSeries ℚ) = PowerSeries.C 6 from (map_ofNat _ 6).symm, ← map_mul]
    norm_num
  have h5 : (PowerSeries.C (1 / 2 : ℚ)) = 4 * PowerSeries.C (1 / 8) := by
    rw [show (4 : PowerSeries ℚ) = PowerSeries.C 4 from (map_ofNat _ 4).symm, ← map_mul]
    norm_num
  have h6 : (2 : PowerSeries ℚ) * PowerSeries.C (1 / 2) = 1 := by
    rw [show (2 : PowerSeries ℚ) = PowerSeries.C 2 from (map_ofNat _ 2).symm, ← map_mul]
    norm_num
  linear_combination (6 * PowerSeries.X ^ 2) * h1 - (4 * PowerSeries.X ^ 3) * h2 +
    PowerSeries.X ^ 4 * h3 - PowerSeries.X ^ 2 * h4 + PowerSeries.X ^ 3 * h5 -
    2 * PowerSeries.X * h6

/-! ### Expansions in the kernel polynomials -/

/-- `d_k` for `k : ℤ`, zero for negative `k`. -/
def kernelPolyZ (k : ℤ) : ℚ[X] := if k < 0 then 0 else kernelPoly k.toNat

private theorem coeff_C_mul_X_pow_mul_kernelSqrt (p : ℚ[X]) (s t : ℕ) :
    PowerSeries.coeff t (PowerSeries.C p * PowerSeries.X ^ s * kernelSqrt) =
      p * kernelPolyZ (t - s) := by
  rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', kernelPolyZ]
  by_cases h : s ≤ t
  · simp only [h, ↓reduceIte, show ¬ ((t : ℤ) - s < 0) by lia,
      show ((t : ℤ) - s).toNat = t - s by lia, kernelPoly]
  · simp only [h, ↓reduceIte, show ((t : ℤ) - s < 0) by lia, mul_zero]

private theorem two_mul_C_half_series :
    (2 : PowerSeries ℚ[X]) * PowerSeries.C (C (1 / 2)) = 1 := by
  rw [show (2 : PowerSeries ℚ[X]) = PowerSeries.C (C 2) by rw [map_ofNat C, map_ofNat],
    ← map_mul, ← C_mul]
  norm_num

private theorem four_mul_C_quarter_series :
    (4 : PowerSeries ℚ[X]) * PowerSeries.C (C (1 / 4)) = 1 := by
  rw [show (4 : PowerSeries ℚ[X]) = PowerSeries.C (C 4) by rw [map_ofNat C, map_ofNat],
    ← map_mul, ← C_mul]
  norm_num

/-- The coefficients of `8 a D = 8 - (8v(2 - v) + 4) y + (4v(2 - v) + 2v) y² - v y³`. -/
def kernelK8Coeff : ℕ → ℚ[X]
  | 0 => 8
  | 1 => -(8 * X * (2 - X) + 4)
  | 2 => 4 * X * (2 - X) + 2 * X
  | 3 => -X
  | _ => 0

/-- The coefficients of `24 a ∂_v D = 24(2v - 2) y + (6 - 12(2v - 2)) y² - 3 y³`. -/
def kernelL16Coeff : ℕ → ℚ[X]
  | 0 => 0
  | 1 => 24 * (2 * X - 2)
  | 2 => 6 - 12 * (2 * X - 2)
  | 3 => -3
  | _ => 0

private theorem eight_mul_kernelHalf_mul_kernelDisc :
    8 * (kernelHalf * kernelDisc) = ∑ s ∈ Finset.range 4,
      PowerSeries.C (kernelK8Coeff s) * PowerSeries.X ^ s := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, kernelK8Coeff, kernelHalf,
    kernelDisc, map_add, map_sub, map_mul, map_neg, map_ofNat, pow_zero, pow_one, zero_add,
    mul_one]
  linear_combination (-4 * PowerSeries.X + 4 * PowerSeries.C X * (2 - PowerSeries.C X) *
      PowerSeries.X ^ 2 - 4 * PowerSeries.C (C (1 / 4)) * PowerSeries.C X * PowerSeries.X ^ 3) *
      two_mul_C_half_series +
    (2 * PowerSeries.C X * PowerSeries.X ^ 2 - PowerSeries.C X * PowerSeries.X ^ 3) *
      four_mul_C_quarter_series

private theorem sixteen_mul_kernelL_series :
    16 * (PowerSeries.C (C (3 / 2)) * kernelHalf * kernelSqrt * partialV kernelDisc) =
      (∑ s ∈ Finset.range 4, PowerSeries.C (kernelL16Coeff s) * PowerSeries.X ^ s) *
        kernelSqrt := by
  have h32 : (2 : PowerSeries ℚ[X]) * PowerSeries.C (C (3 / 2)) = 3 := by
    rw [show (2 : PowerSeries ℚ[X]) = PowerSeries.C (C 2) by rw [map_ofNat C, map_ofNat],
      ← map_mul, ← C_mul]
    norm_num
    rw [map_ofNat C, map_ofNat]
  rw [partialV_kernelDisc]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, kernelL16Coeff, kernelHalf, map_sub,
    map_mul, map_neg, map_ofNat, map_zero, pow_zero, pow_one, zero_add, mul_one]
  set h := PowerSeries.C (C (1 / 2 : ℚ))
  set q := PowerSeries.C (C (1 / 4 : ℚ))
  set c := PowerSeries.C (C (3 / 2 : ℚ))
  set u : PowerSeries ℚ[X] := 2 * PowerSeries.C X - 2
  set Y : PowerSeries ℚ[X] := PowerSeries.X
  set T := u * Y + q * Y ^ 2 - h * u * Y ^ 2 - h * q * Y ^ 3
  linear_combination (8 * T * kernelSqrt) * h32 +
    (6 * Y ^ 2 * kernelSqrt - 3 * Y ^ 3 * kernelSqrt) * four_mul_C_quarter_series +
    (-12 * u * Y ^ 2 * kernelSqrt - 12 * q * Y ^ 3 * kernelSqrt) * two_mul_C_half_series

theorem eight_mul_kernelK (t : ℕ) :
    8 * kernelK t = ∑ s ∈ Finset.range 4, kernelK8Coeff s * kernelPolyZ (t - s) := by
  have h := congrArg (PowerSeries.coeff t)
    (congrArg (· * kernelSqrt) eight_mul_kernelHalf_mul_kernelDisc)
  simp only [Finset.sum_mul, map_sum, coeff_C_mul_X_pow_mul_kernelSqrt] at h
  have e : (8 : PowerSeries ℚ[X]) * (kernelHalf * kernelDisc) * kernelSqrt =
      PowerSeries.C 8 * (kernelHalf * kernelDisc * kernelSqrt) := by
    rw [map_ofNat]; ring
  simp only [e, PowerSeries.coeff_C_mul] at h
  exact h

theorem sixteen_mul_kernelL (t : ℕ) :
    16 * kernelL t = ∑ s ∈ Finset.range 4, kernelL16Coeff s * kernelPolyZ (t - s) := by
  have h := congrArg (PowerSeries.coeff t) sixteen_mul_kernelL_series
  simp only [Finset.sum_mul, map_sum, coeff_C_mul_X_pow_mul_kernelSqrt] at h
  rw [← h, kernelL, show (16 : PowerSeries ℚ[X]) = PowerSeries.C 16 from
    (map_ofNat _ 16).symm, PowerSeries.coeff_C_mul]

/-! ### Moments -/

/-- The moments `m(r, J) = ∫_0^1 v^J d_r(v) dv`, zero for `r < 0`. -/
def kernelMoment (r : ℤ) (J : ℕ) : ℚ := integral 0 1 (X ^ J * kernelPolyZ r)

private theorem integral_derivative_X_pow_mul (j : ℕ) (p : ℚ[X]) :
    integral 0 1 (C ((j + 1 : ℚ)) * X ^ j * p + X ^ (j + 1) * derivative p) = p.eval 1 := by
  have hp : derivative (X ^ (j + 1) * p) =
      C ((j + 1 : ℚ)) * X ^ j * p + X ^ (j + 1) * derivative p := by
    rw [derivative_mul, derivative_X_pow, Nat.add_sub_cancel]
    push_cast
    ring
  have h := integral_derivative (0 : ℚ) 1 (X ^ (j + 1) * p)
  rw [hp] at h
  simp only [eval_mul, eval_pow, eval_X, one_pow, one_mul, zero_pow (Nat.succ_ne_zero j),
    zero_mul, sub_zero] at h
  exact h

/-- The moment identity behind the recurrence of the Gegenbauer coordinates. -/
theorem kernelMoment_identity (t j : ℕ) :
    16 * (j + 1) * kernelMoment t j - 8 * (j + 1) * kernelMoment (t - 1) j +
      16 * (j + 4) * kernelMoment (t - 1) (j + 2) - 8 * (j + 4) * kernelMoment (t - 2) (j + 2) -
      16 * (2 * j + 5) * kernelMoment (t - 1) (j + 1) +
      10 * (2 * j + 5) * kernelMoment (t - 2) (j + 1) -
      (2 * j + 5) * kernelMoment (t - 3) (j + 1) = 16 * (kernelK t).eval 1 := by
  have hK := eight_mul_kernelK t
  have hL := sixteen_mul_kernelL t
  rw [← derivative_kernelK] at hL
  have hP : C (16 : ℚ) * (C ((j + 1 : ℚ)) * X ^ j * kernelK t +
      X ^ (j + 1) * derivative (kernelK t)) =
      C ((16 * (j + 1) : ℚ)) * (X ^ j * kernelPolyZ t) -
      C ((8 * (j + 1) : ℚ)) * (X ^ j * kernelPolyZ (t - 1)) +
      C ((16 * (j + 4) : ℚ)) * (X ^ (j + 2) * kernelPolyZ (t - 1)) -
      C ((8 * (j + 4) : ℚ)) * (X ^ (j + 2) * kernelPolyZ (t - 2)) -
      C ((16 * (2 * j + 5) : ℚ)) * (X ^ (j + 1) * kernelPolyZ (t - 1)) +
      C ((10 * (2 * j + 5) : ℚ)) * (X ^ (j + 1) * kernelPolyZ (t - 2)) -
      C ((2 * j + 5 : ℚ)) * (X ^ (j + 1) * kernelPolyZ (t - 3)) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, kernelK8Coeff, kernelL16Coeff,
      Nat.cast_ofNat, zero_add, CharP.cast_eq_zero, sub_zero] at hK hL
    simp only [map_mul, map_add, map_ofNat, map_natCast, map_one, pow_succ]
    linear_combination (2 * ((j : ℚ[X]) + 1) * X ^ j) * hK + X ^ j * X * hL
  have h := congrArg (integral (0 : ℚ) 1) hP
  rw [integral_C_mul, integral_derivative_X_pow_mul] at h
  simp only [LinearMap.map_add, LinearMap.map_sub, integral_C_mul] at h
  simp only [kernelMoment]
  linarith

/-- The moment identity at `i = 0`: `16 ∫_0^1 L_t = 16 (K_t(1) - K_t(0))`. -/
theorem kernelMoment_identity_zero (t : ℕ) :
    48 * kernelMoment (t - 1) 1 - 24 * kernelMoment (t - 2) 1 - 48 * kernelMoment (t - 1) 0 +
      30 * kernelMoment (t - 2) 0 - 3 * kernelMoment (t - 3) 0 =
      16 * ((kernelK t).eval 1 - (kernelK t).eval 0) := by
  have hL := sixteen_mul_kernelL t
  rw [← derivative_kernelK] at hL
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, kernelL16Coeff, Nat.cast_ofNat,
    zero_add, CharP.cast_eq_zero, sub_zero, zero_mul] at hL
  have hP : C (16 : ℚ) * derivative (kernelK t) =
      C (48 : ℚ) * (X ^ 1 * kernelPolyZ (t - 1)) - C (24 : ℚ) * (X ^ 1 * kernelPolyZ (t - 2)) -
      C (48 : ℚ) * (X ^ 0 * kernelPolyZ (t - 1)) + C (30 : ℚ) * (X ^ 0 * kernelPolyZ (t - 2)) -
      C (3 : ℚ) * (X ^ 0 * kernelPolyZ (t - 3)) := by
    simp only [map_ofNat, pow_zero, pow_one, one_mul]
    linear_combination hL
  have h := congrArg (integral (0 : ℚ) 1) hP
  rw [integral_C_mul, integral_derivative] at h
  simp only [LinearMap.map_add, LinearMap.map_sub, integral_C_mul] at h
  simp only [kernelMoment]
  linarith

@[simp] theorem kernelPoly_zero : kernelPoly 0 = 1 := by
  rw [kernelPoly, PowerSeries.coeff_zero_eq_constantCoeff_apply, kernelSqrt,
    PowerSeries.constantCoeff_sqrt constantCoeff_kernelDisc]

theorem kernelPoly_one : kernelPoly 1 = C (1 / 2) * X ^ 2 - X := by
  have h := congrArg (PowerSeries.coeff 1) (PowerSeries.sqrt_sq constantCoeff_kernelDisc)
  rw [sq, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.sub_zero,
    Nat.sub_self] at h
  have h0 : PowerSeries.coeff 0 (PowerSeries.sqrt kernelDisc) = 1 := kernelPoly_zero
  have hD : PowerSeries.coeff 1 kernelDisc = -(X * (2 - X)) := by
    simp [kernelDisc, mul_assoc, PowerSeries.coeff_X_pow]
  rw [h0, hD] at h
  have h2 : (2 : ℚ[X]) * C (1 / 2) = 1 := by
    rw [show (2 : ℚ[X]) = C 2 from (map_ofNat C 2).symm, ← C_mul]; norm_num
  change PowerSeries.coeff 1 (PowerSeries.sqrt kernelDisc) = _
  linear_combination C (1 / 2) * h - (PowerSeries.coeff 1 (PowerSeries.sqrt kernelDisc) + X) * h2

theorem kernelPolyZ_of_neg {k : ℤ} (hk : k < 0) : kernelPolyZ k = 0 := by
  simp [kernelPolyZ, hk]

theorem kernelMoment_of_neg {r : ℤ} (hr : r < 0) (J : ℕ) : kernelMoment r J = 0 := by
  simp [kernelMoment, kernelPolyZ_of_neg hr]

theorem kernelMoment_zero (J : ℕ) : kernelMoment 0 J = 1 / (J + 1) := by
  simp [kernelMoment, kernelPolyZ, integral_X_pow, invSucc]

end RealRooted.BigDescents321
