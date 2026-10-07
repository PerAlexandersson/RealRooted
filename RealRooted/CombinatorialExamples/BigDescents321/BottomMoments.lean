import RealRooted.CombinatorialExamples.BigDescents321.KernelSum
import RealRooted.CombinatorialExamples.BigDescents321.Coordinates
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.NormNum.NatFib

/-!
# Recurrences for the bottom kernel moments

The bottom Gegenbauer coordinates `q_(2r,0)` and `q_(2r+1,1)` of `Q_n` are given by the kernel
moments `m(r, 0) = Λ₊(d_r)` and `m(r, 1) = Λ₊(v d_r)`, where `d_r = [y^r] √D`. Each moment
sequence satisfies a linear recurrence in `r` alone. It comes from a creative-telescoping
certificate `A(y) ∂_y(v^J √D) + B(y) v^J √D = ∂_v(C(v, y) √D)`, which is a polynomial identity
after multiplying by `2D`, integrated over `v ∈ [0, 1]`.

## Main statements

* `kernelMoment_zero_rec`: `32(2r+1) m(r) - 32(2r-3) m(r-1) + 8(2r-7) m(r-2)
  - ((2r-11)/2) m(r-3) = 0` for `m = m(·, 0)` and `r ≥ 5`.
* `kernelMoment_zero_eq`: the closed form of `m(r, 0)` in Fibonacci numbers, `r ≥ 2`.
* `kernelMoment_one_sub`: `m(r,1) - m(r-1,1)/2` in terms of `m(·, 0)`, from the moment
  identity, so no separate certificate is needed for `J = 1`.
* `transformedCoord_bottom_pos`: `q_(n, n mod 2) > 0` for `n ≥ 25`.
-/

open Polynomial

noncomputable section

namespace RealRooted.BigDescents321

/-- The variable `v` as a constant power series in `y`. -/
private abbrev sV : PowerSeries ℚ[X] := PowerSeries.C X

/-- The variable `y`. -/
private abbrev sY : PowerSeries ℚ[X] := PowerSeries.X

private theorem four_mul_kernelDisc :
    4 * kernelDisc = 4 - 4 * sV * (2 - sV) * sY + sV * sY ^ 2 := by
  have h4 : (4 : PowerSeries ℚ[X]) * PowerSeries.C (C (1 / 4)) = 1 := by
    rw [show (4 : PowerSeries ℚ[X]) = PowerSeries.C (C 4) by rw [map_ofNat C, map_ofNat],
      ← map_mul, ← C_mul]
    norm_num
  simp only [kernelDisc, map_mul, map_sub, map_ofNat]
  linear_combination sV * sY ^ 2 * h4

private theorem derivative_ofNat (n : ℕ) [n.AtLeastTwo] :
    PowerSeries.derivative (no_index (OfNat.ofNat n : PowerSeries ℚ[X])) = 0 := by
  rw [← map_ofNat PowerSeries.C]
  exact PowerSeries.derivative_C

private theorem four_mul_derivative_kernelDisc :
    4 * PowerSeries.derivative kernelDisc = -4 * sV * (2 - sV) + 2 * sV * sY := by
  have h4 : (4 : PowerSeries ℚ[X]) * PowerSeries.C (C (1 / 4)) = 1 := by
    rw [show (4 : PowerSeries ℚ[X]) = PowerSeries.C (C 4) by rw [map_ofNat C, map_ofNat],
      ← map_mul, ← C_mul]
    norm_num
  simp only [kernelDisc, map_add, map_sub, Derivation.map_one_eq_zero, Derivation.leibniz,
    Derivation.leibniz_pow, PowerSeries.derivative_C, PowerSeries.derivative_X, smul_eq_mul,
    map_mul, map_ofNat, derivative_ofNat]
  linear_combination 2 * sV * sY * h4

private theorem four_mul_partialV_kernelDisc :
    4 * partialV kernelDisc = 4 * (2 * sV - 2) * sY + sY ^ 2 := by
  have h4 : (4 : PowerSeries ℚ[X]) * PowerSeries.C (C (1 / 4)) = 1 := by
    rw [show (4 : PowerSeries ℚ[X]) = PowerSeries.C (C 4) by rw [map_ofNat C, map_ofNat],
      ← map_mul, ← C_mul]
    norm_num
  rw [partialV_kernelDisc]
  simp only [map_sub, map_mul, map_ofNat]
  linear_combination sY ^ 2 * h4

private theorem partialV_sV : partialV sV = 1 := by
  simp [partialV]

private theorem partialV_sY : partialV sY = 0 := PowerSeries.mapDerivation_X _

private theorem partialV_ofNat (n : ℕ) [n.AtLeastTwo] :
    partialV (no_index (OfNat.ofNat n : PowerSeries ℚ[X])) = 0 := by
  rw [← map_ofNat PowerSeries.C]
  exact (PowerSeries.mapDerivation_C _ _).trans (by simp)

/-! ### The certificate for `J = 0` -/

/-- `A₀ = 2(-y⁴ + 16y³ - 64y² + 64y)`. -/
private abbrev certA0 : PowerSeries ℚ[X] := -2 * sY ^ 4 + 32 * sY ^ 3 - 128 * sY ^ 2 + 128 * sY

/-- `B₀ = 5y³ - 48y² + 64y + 64`. -/
private abbrev certB0 : PowerSeries ℚ[X] := 5 * sY ^ 3 - 48 * sY ^ 2 + 64 * sY + 64

/-- `C₀ = 2v(y³ - 8y² + 32) + 24y - 64`. -/
private abbrev certC0 : PowerSeries ℚ[X] := 2 * sV * (sY ^ 3 - 8 * sY ^ 2 + 32) + 24 * sY - 64

private theorem kernelCert0 :
    certA0 * PowerSeries.derivative kernelSqrt + certB0 * kernelSqrt =
      partialV (certC0 * kernelSqrt) := by
  set S := kernelSqrt
  set D := kernelDisc
  have hS : S * S = D := by rw [← sq]; exact PowerSeries.sqrt_sq constantCoeff_kernelDisc
  have hy : 2 * D * PowerSeries.derivative S = PowerSeries.derivative D * S :=
    PowerSeries.two_mul_mul_derivative_sqrt constantCoeff_kernelDisc
  have hv : 2 * D * partialV S = S * partialV D := by
    rw [← hS, partialV_mul]
    ring
  have hC : partialV certC0 = 2 * (sY ^ 3 - 8 * sY ^ 2 + 32) := by
    simp only [certC0, PowerSeries.mapDerivation_add, PowerSeries.mapDerivation_sub, partialV_mul,
      partialV_sV, partialV_ofNat, PowerSeries.mapDerivation_X_pow, PowerSeries.mapDerivation_X]
    ring
  have e1 := four_mul_derivative_kernelDisc
  have e2 := four_mul_kernelDisc
  have e3 := four_mul_partialV_kernelDisc
  have key : 8 * D * (certA0 * PowerSeries.derivative S + certB0 * S -
      partialV (certC0 * S)) = 0 := by
    rw [partialV_mul, hC]
    linear_combination 4 * certA0 * hy - 4 * certC0 * hv + certA0 * S * e1 +
      (2 * certB0 - 4 * (sY ^ 3 - 8 * sY ^ 2 + 32)) * S * e2 - certC0 * S * e3
  have h8 : (8 : PowerSeries ℚ[X]) * D ≠ 0 := by
    intro h
    have := congrArg PowerSeries.constantCoeff h
    rw [map_mul, map_ofNat, constantCoeff_kernelDisc, mul_one, map_zero] at this
    norm_num at this
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left h8)

private theorem coeff_kernelCert0_lhs {t : ℕ} (ht : 1 ≤ t) :
    PowerSeries.coeff (t + 3) (certA0 * PowerSeries.derivative kernelSqrt + certB0 * kernelSqrt) =
      C ((64 : ℚ) * (2 * t + 7)) * kernelPoly (t + 3) -
        C ((64 : ℚ) * (2 * t + 3)) * kernelPoly (t + 2) +
        C ((16 : ℚ) * (2 * t - 1)) * kernelPoly (t + 1) - C ((2 : ℚ) * t - 5) * kernelPoly t := by
  simp [certA0, certB0, add_mul, sub_mul, mul_assoc, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_derivative, kernelPoly, ht]
  simp only [show t + 1 + 1 = t + 2 from rfl, show t + 2 + 1 = t + 3 from rfl, map_ofNat]
  ring

private theorem map_eval_kernelSqrt_one :
    PowerSeries.map (evalRingHom 1) kernelSqrt = halfQ := by
  rw [kernelSqrt, PowerSeries.map_sqrt _ constantCoeff_kernelDisc, map_eval_one_kernelDisc,
    PowerSeries.sqrt_sq_of_constantCoeff constantCoeff_halfQ]

private theorem map_eval_kernelSqrt_zero :
    PowerSeries.map (evalRingHom 0) kernelSqrt = 1 := by
  rw [kernelSqrt, PowerSeries.map_sqrt _ constantCoeff_kernelDisc, map_eval_zero_kernelDisc,
    PowerSeries.sqrt_one]

theorem eval_one_kernelPoly (j : ℕ) : (kernelPoly j).eval 1 = PowerSeries.coeff j halfQ := by
  rw [kernelPoly, ← coe_evalRingHom, ← PowerSeries.coeff_map, map_eval_kernelSqrt_one]

theorem eval_zero_kernelPoly (j : ℕ) : (kernelPoly j).eval 0 = if j = 0 then 1 else 0 := by
  rw [kernelPoly, ← coe_evalRingHom, ← PowerSeries.coeff_map, map_eval_kernelSqrt_zero,
    PowerSeries.coeff_one]

theorem coeff_halfQ_of_two_le {j : ℕ} (h : 2 ≤ j) : PowerSeries.coeff j halfQ = 0 := by
  simp [halfQ, PowerSeries.coeff_one, PowerSeries.coeff_X, show j ≠ 0 by lia, show j ≠ 1 by lia]

private theorem coeff_certC0 (t : ℕ) :
    PowerSeries.coeff (t + 3) (certC0 * kernelSqrt) =
      C 2 * X * (kernelPoly t - 8 * kernelPoly (t + 1) + 32 * kernelPoly (t + 3)) +
        24 * kernelPoly (t + 2) - 64 * kernelPoly (t + 3) := by
  conv_lhs => simp [certC0, add_mul, sub_mul, mul_assoc, PowerSeries.coeff_X_pow_mul', kernelPoly]
  simp only [kernelPoly, map_ofNat]
  ring

/-- The boundary terms of the `J = 0` certificate vanish from `y⁵` on. -/
private theorem integral_coeff_partialV_certC0 {t : ℕ} (ht : 2 ≤ t) :
    integral 0 1 (PowerSeries.coeff (t + 3) (partialV (certC0 * kernelSqrt))) = 0 := by
  rw [PowerSeries.coeff_mapDerivation, derivative'_apply, integral_derivative, coeff_certC0]
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_ofNat, eval_one_kernelPoly,
    eval_zero_kernelPoly, coeff_halfQ_of_two_le ht, coeff_halfQ_of_two_le (show 2 ≤ t + 1 by lia),
    coeff_halfQ_of_two_le (show 2 ≤ t + 2 by lia), coeff_halfQ_of_two_le (show 2 ≤ t + 3 by lia),
    show t ≠ 0 by lia, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false, ↓reduceIte]
  ring

/-- The recurrence of `m(r, 0)`: for `t ≥ 2`,
`64(2t + 7) m(t+3) - 64(2t + 3) m(t+2) + 16(2t - 1) m(t+1) - (2t - 5) m(t) = 0`. -/
theorem kernelMoment_zero_rec {t : ℕ} (ht : 2 ≤ t) :
    64 * (2 * (t : ℚ) + 7) * kernelMoment (t + 3 : ℕ) 0 -
        64 * (2 * (t : ℚ) + 3) * kernelMoment (t + 2 : ℕ) 0 +
      16 * (2 * (t : ℚ) - 1) * kernelMoment (t + 1 : ℕ) 0 -
        (2 * (t : ℚ) - 5) * kernelMoment (t : ℕ) 0 = 0 := by
  have h := congrArg (fun F ↦ integral 0 1 (PowerSeries.coeff (t + 3) F)) kernelCert0
  rw [coeff_kernelCert0_lhs (by lia), integral_coeff_partialV_certC0 ht] at h
  simp only [map_add, map_sub, sub_mul, integral_C_mul] at h
  simp only [kernelMoment_natCast, pow_zero, one_mul]
  linear_combination h

/-! ### The closed form of `m(r, 0)` -/

/-- The closed form of `m(t + 2, 0)`: with `L = L_(2t+3)` and `F = F_(2t+3)`,
`((-10t² - 36t - 127/2) L + (10t² + 100t + 255/2) F) / (4^(t+2) (2t-1)(2t+1)(2t+3)(2t+5))`. -/
def momentZeroCF (t : ℕ) : ℚ :=
  ((-10 * (t : ℚ) ^ 2 - 36 * t - 127 / 2) * (Nat.fib (2 * t + 2) + Nat.fib (2 * t + 4)) +
      (10 * (t : ℚ) ^ 2 + 100 * t + 255 / 2) * Nat.fib (2 * t + 3)) /
    (4 ^ (t + 2) * ((2 * t - 1) * (2 * t + 1) * (2 * t + 3) * (2 * t + 5)))

/-- `F_(m + c + 1) = F_c F_m + F_(c+1) F_(m+1)`. -/
theorem fib_add_succ (m c : ℕ) :
    (Nat.fib (m + (c + 1)) : ℚ) = Nat.fib c * Nat.fib m + Nat.fib (c + 1) * Nat.fib (m + 1) := by
  have := Nat.fib_add c m
  rw [show c + m + 1 = m + (c + 1) by ring] at this
  exact_mod_cast this

theorem kernelMoment_two_zero : kernelMoment (2 : ℕ) 0 = -1 / 240 := by
  rw [kernelMoment_two, kernelMoment_one, kernelMoment_one, Nat.cast_zero, kernelMoment_zero]
  norm_num

private theorem kernelMoment_two_eq (J : ℕ) :
    kernelMoment (2 : ℕ) J = (2 * (1 / (2 * ((J : ℚ) + 1 + 3)) - 1 / ((J : ℚ) + 1 + 2)) -
      (1 / (2 * ((J : ℚ) + 2 + 3)) - 1 / ((J : ℚ) + 2 + 2)) + 1 / ((J : ℚ) + 1 + 1) / 2) / 4 := by
  rw [kernelMoment_two, kernelMoment_one, kernelMoment_one, Nat.cast_zero, kernelMoment_zero]
  push_cast
  ring

theorem kernelMoment_three_zero : kernelMoment (3 : ℕ) 0 = -17 / 6720 := by
  rw [kernelMoment_three, kernelMoment_two_eq, kernelMoment_two_eq]
  norm_num

theorem kernelMoment_four_zero : kernelMoment (4 : ℕ) 0 = -13 / 10080 := by
  have h := kernelMoment_rec 2 0
  rw [show ((2 + 2 : ℕ) : ℤ) = ((4 : ℕ) : ℤ) from rfl,
    show ((2 + 1 : ℕ) : ℤ) = ((3 : ℕ) : ℤ) from rfl, kernelMoment_three, kernelMoment_three,
    kernelMoment_two_eq, kernelMoment_two_eq, kernelMoment_two_eq, kernelMoment_two_eq] at h
  norm_num at h
  linarith

theorem two_mul_sub_one_ne_zero (s : ℕ) : (2 * (s : ℚ) - 1) ≠ 0 := by
  intro h
  have : (2 * s : ℚ) = 1 := by linarith
  norm_cast at this
  lia

/-- `F_(2s+2+k+1)` in the basis `F_(2s+2)`, `F_(2s+3)`. -/
private theorem fib_pair (s k : ℕ) :
    (Nat.fib (2 * s + 2 + (k + 1)) : ℚ) =
      Nat.fib k * Nat.fib (2 * s + 2) + Nat.fib (k + 1) * Nat.fib (2 * s + 3) :=
  fib_add_succ _ k

/-- The closed form satisfies the recurrence of `m(r, 0)`. -/
private theorem momentZeroCF_rec (s : ℕ) :
    64 * (2 * ((s + 2 : ℕ) : ℚ) + 7) * momentZeroCF (s + 3) -
        64 * (2 * ((s + 2 : ℕ) : ℚ) + 3) * momentZeroCF (s + 2) +
      16 * (2 * ((s + 2 : ℕ) : ℚ) - 1) * momentZeroCF (s + 1) -
        (2 * ((s + 2 : ℕ) : ℚ) - 5) * momentZeroCF s = 0 := by
  have f : ∀ k j : ℕ, 2 * s + 2 + (k + 1) = j →
      (Nat.fib j : ℚ) = Nat.fib k * Nat.fib (2 * s + 2) + Nat.fib (k + 1) * Nat.fib (2 * s + 3) :=
    fun k j h ↦ h ▸ fib_pair s k
  simp only [momentZeroCF]
  rw [f 7 (2 * (s + 3) + 4) (by ring), f 6 (2 * (s + 3) + 3) (by ring),
    f 5 (2 * (s + 3) + 2) (by ring), f 5 (2 * (s + 2) + 4) (by ring),
    f 4 (2 * (s + 2) + 3) (by ring), f 3 (2 * (s + 2) + 2) (by ring),
    f 3 (2 * (s + 1) + 4) (by ring), f 2 (2 * (s + 1) + 3) (by ring),
    f 1 (2 * (s + 1) + 2) (by ring), f 1 (2 * s + 4) (by ring)]
  norm_num
  have h0 := two_mul_sub_one_ne_zero s
  have h1 := two_mul_sub_one_ne_zero (s + 1)
  have h2 := two_mul_sub_one_ne_zero (s + 2)
  have h3 := two_mul_sub_one_ne_zero (s + 3)
  push_cast at h1 h2 h3 ⊢
  generalize (Nat.fib (2 * s + 2) : ℚ) = a
  generalize (Nat.fib (2 * s + 3) : ℚ) = b
  field_simp
  ring

/-- The closed form of `m(t + 2, 0)`. -/
theorem kernelMoment_zero_eq (t : ℕ) : kernelMoment (t + 2 : ℕ) 0 = momentZeroCF t := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  match t, ih with
  | 0, _ => rw [kernelMoment_two_zero]; norm_num [momentZeroCF]
  | 1, _ => rw [kernelMoment_three_zero]; norm_num [momentZeroCF]
  | 2, _ => rw [kernelMoment_four_zero]; norm_num [momentZeroCF]
  | s + 3, ih =>
    have hrec := kernelMoment_zero_rec (t := s + 2) (by lia)
    rw [show s + 2 + 3 = s + 3 + 2 by ring, show s + 2 + 1 = s + 1 + 2 by ring,
      ih (s + 2) (by lia), ih (s + 1) (by lia), ih s (by lia)] at hrec
    have hc := momentZeroCF_rec s
    have hpos : (64 * (2 * ((s + 2 : ℕ) : ℚ) + 7)) ≠ 0 := by positivity
    apply mul_left_cancel₀ hpos
    linear_combination hrec - hc

/-! ### The signs of the bottom coordinates -/

/-- The closed form of `q_(2r,0) = -3 (m(r,0) - m(r-1,0)/2)` for `r = s + 13`, in the Fibonacci
numbers `a = F_(2s+18)`, `b = F_(2s+19)`. -/
theorem kernelCoord_zero_closed (s : ℕ) :
    kernelCoord (s + 13 : ℕ) 0 =
      ((Nat.fib (2 * s + 18) : ℚ) * (120 * (s : ℚ) ^ 3 + 2484 * s ^ 2 + 15234 * s + 21123) +
        (Nat.fib (2 * s + 19) : ℚ) * (240 * (s : ℚ) ^ 3 + 5832 * s ^ 2 + 48612 * s + 140094)) /
      (4 ^ (s + 13) *
        ((2 * s + 19) * (2 * s + 21) * (2 * s + 23) * (2 * s + 25) * (2 * s + 27))) := by
  rw [kernelCoord_eq, corrCoordZ_of_three_le (by lia),
    show ((s + 13 : ℕ) : ℤ) - 1 = ((s + 10 + 2 : ℕ) : ℤ) by push_cast; ring,
    show s + 13 = s + 11 + 2 by ring, kernelMoment_zero_eq, kernelMoment_zero_eq]
  have f : ∀ k j : ℕ, 2 * s + 18 + (k + 1) = j →
      (Nat.fib j : ℚ) = Nat.fib k * Nat.fib (2 * s + 18) + Nat.fib (k + 1) * Nat.fib (2 * s + 19) :=
    fun k j h ↦ h ▸ (fib_add_succ _ k)
  simp only [momentZeroCF]
  rw [f 7 (2 * (s + 11) + 4) (by ring), f 6 (2 * (s + 11) + 3) (by ring),
    f 5 (2 * (s + 11) + 2) (by ring), f 5 (2 * (s + 10) + 4) (by ring),
    f 4 (2 * (s + 10) + 3) (by ring), f 3 (2 * (s + 10) + 2) (by ring)]
  simp only [Nat.reduceAdd, show Nat.fib 3 = 2 by decide, show Nat.fib 4 = 3 by decide,
    show Nat.fib 5 = 5 by decide, show Nat.fib 6 = 8 by decide, show Nat.fib 7 = 13 by decide,
    show Nat.fib 8 = 21 by decide]
  have h1 := two_mul_sub_one_ne_zero (s + 10)
  have h2 := two_mul_sub_one_ne_zero (s + 11)
  push_cast at h1 h2 ⊢
  field_simp
  ring

/-- `q_(2r,0) = -3 (m(r,0) - m(r-1,0)/2)` is positive for `r ≥ 13`. -/
theorem kernelCoord_zero_pos (s : ℕ) : 0 < kernelCoord (s + 13 : ℕ) 0 := by
  rw [kernelCoord_zero_closed]
  have hb : (0 : ℚ) < Nat.fib (2 * s + 19) := by exact_mod_cast Nat.fib_pos.mpr (by lia)
  have : 0 < (Nat.fib (2 * s + 19) : ℚ) *
      (240 * (s : ℚ) ^ 3 + 5832 * s ^ 2 + 48612 * s + 140094) := by positivity
  positivity

theorem coeff_halfQ_pow_four_of_five_le {t : ℕ} (h : 5 ≤ t) :
    PowerSeries.coeff t (halfQ ^ 4) = 0 := by
  rw [halfQ_pow_four]
  simp [PowerSeries.coeff_one, PowerSeries.coeff_X, PowerSeries.coeff_X_pow,
    PowerSeries.coeff_C_mul, show t ≠ 0 by lia, show t ≠ 1 by lia, show t ≠ 2 by lia,
    show t ≠ 3 by lia, show t ≠ 4 by lia]

/-- `m(r,1) - m(r-1,1)/2` in terms of `m(·,0)`, for `r ≥ 4`. -/
theorem kernelMoment_one_sub (r : ℕ) :
    48 * (kernelMoment (r + 4 : ℕ) 1 - kernelMoment (r + 3 : ℕ) 1 / 2) =
      48 * kernelMoment (r + 4 : ℕ) 0 - 30 * kernelMoment (r + 3 : ℕ) 0 +
        3 * kernelMoment (r + 2 : ℕ) 0 := by
  have h := kernelMoment_identity_zero (r + 5)
  rw [eval_one_kernelK, eval_zero_kernelK, coeff_halfQ_pow_four_of_five_le (by lia),
    coeff_halfQ_of_two_le (by lia)] at h
  rw [show ((r + 5 : ℕ) : ℤ) - 1 = ((r + 4 : ℕ) : ℤ) by push_cast; ring,
    show ((r + 5 : ℕ) : ℤ) - 2 = ((r + 3 : ℕ) : ℤ) by push_cast; ring,
    show ((r + 5 : ℕ) : ℤ) - 3 = ((r + 2 : ℕ) : ℤ) by push_cast; ring] at h
  linarith

/-- `q_(2r+1,1) = -5 (m(r,1) - m(r-1,1)/2)` is positive for `r ≥ 12`. -/
theorem kernelCoord_one_pos (s : ℕ) : 0 < kernelCoord (s + 12 : ℕ) 1 := by
  rw [kernelCoord_eq, corrCoordZ_of_three_le (by lia),
    show ((s + 12 : ℕ) : ℤ) - 1 = ((s + 8 + 3 : ℕ) : ℤ) by push_cast; ring,
    show s + 12 = s + 8 + 4 by ring]
  have h1 := kernelMoment_one_sub (s + 8)
  rw [show kernelMoment ((s + 8 + 4 : ℕ) : ℤ) 1 - kernelMoment ((s + 8 + 3 : ℕ) : ℤ) 1 / 2 =
    (48 * kernelMoment (s + 8 + 4 : ℕ) 0 - 30 * kernelMoment (s + 8 + 3 : ℕ) 0 +
      3 * kernelMoment (s + 8 + 2 : ℕ) 0) / 48 by linarith,
    show s + 8 + 4 = s + 10 + 2 by ring, show s + 8 + 3 = s + 9 + 2 by ring,
    kernelMoment_zero_eq, kernelMoment_zero_eq, kernelMoment_zero_eq]
  have f : ∀ k j : ℕ, 2 * s + 14 + (k + 1) = j →
      (Nat.fib j : ℚ) = Nat.fib k * Nat.fib (2 * s + 14) + Nat.fib (k + 1) * Nat.fib (2 * s + 15) :=
    fun k j h ↦ h ▸ (fib_add_succ _ k)
  simp only [momentZeroCF]
  rw [f 9 (2 * (s + 10) + 4) (by ring), f 8 (2 * (s + 10) + 3) (by ring),
    f 7 (2 * (s + 10) + 2) (by ring), f 7 (2 * (s + 9) + 4) (by ring),
    f 6 (2 * (s + 9) + 3) (by ring), f 5 (2 * (s + 9) + 2) (by ring),
    f 5 (2 * (s + 8) + 4) (by ring), f 4 (2 * (s + 8) + 3) (by ring),
    f 3 (2 * (s + 8) + 2) (by ring)]
  have ha : (0 : ℚ) ≤ Nat.fib (2 * s + 14) := Nat.cast_nonneg _
  have hb : (0 : ℚ) < Nat.fib (2 * s + 15) := by exact_mod_cast Nat.fib_pos.mpr (by lia)
  generalize (Nat.fib (2 * s + 14) : ℚ) = a at ha ⊢
  generalize (Nat.fib (2 * s + 15) : ℚ) = b at hb ⊢
  have hE : 0 < (a * (2000 * (s : ℚ) ^ 4 + 55360 * s ^ 3 + 587800 * s ^ 2 + 2837360 * s +
      5281725) + b * (3200 * (s : ℚ) ^ 4 + 87680 * s ^ 3 + 913600 * s ^ 2 + 4259680 * s +
      7441800)) / (4 ^ (s + 12) * (2 * ((2 * s + 15) * (2 * s + 17) * (2 * s + 19) *
        (2 * s + 21) * (2 * s + 23) * (2 * s + 25)))) := by
    have : 0 < b * (3200 * (s : ℚ) ^ 4 + 87680 * s ^ 3 + 913600 * s ^ 2 + 4259680 * s +
      7441800) := by positivity
    have : 0 ≤ a * (2000 * (s : ℚ) ^ 4 + 55360 * s ^ 3 + 587800 * s ^ 2 + 2837360 * s +
      5281725) := by positivity
    positivity
  refine hE.trans_eq ?_
  simp only [Nat.reduceAdd, show Nat.fib 3 = 2 by decide, show Nat.fib 4 = 3 by decide,
    show Nat.fib 5 = 5 by decide, show Nat.fib 6 = 8 by decide, show Nat.fib 7 = 13 by decide,
    show Nat.fib 8 = 21 by decide, show Nat.fib 9 = 34 by decide, show Nat.fib 10 = 55 by decide]
  have h1 := two_mul_sub_one_ne_zero (s + 8)
  have h2 := two_mul_sub_one_ne_zero (s + 9)
  have h3 := two_mul_sub_one_ne_zero (s + 10)
  push_cast at h1 h2 h3 ⊢
  field_simp
  ring

/-- The bottom coordinate signs: `q_(n,0) > 0` for even `n ≥ 26` and `q_(n,1) > 0` for odd
`n ≥ 25`. -/
theorem transformedCoord_bottom_pos {n : ℕ} (hn : 25 ≤ n) : 0 < transformedCoord n (n % 2) := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · obtain ⟨s, rfl⟩ : ∃ s, k = s + 13 := ⟨k - 13, by lia⟩
    rw [show 2 * (s + 13) % 2 = 0 by lia,
      transformedCoord_eq (r := ((s + 13 : ℕ) : ℤ)) (by push_cast; ring)]
    exact kernelCoord_zero_pos s
  · obtain ⟨s, rfl⟩ : ∃ s, k = s + 12 := ⟨k - 12, by lia⟩
    rw [show (2 * (s + 12) + 1) % 2 = 1 by lia,
      transformedCoord_eq (r := ((s + 12 : ℕ) : ℤ)) (by push_cast; ring)]
    exact kernelCoord_one_pos s

end RealRooted.BigDescents321
