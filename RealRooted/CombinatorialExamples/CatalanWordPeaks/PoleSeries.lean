/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import RealRooted.CombinatorialExamples.CatalanWordPeaks.Basic
public import Mathlib.RingTheory.PowerSeries.WellKnown
import RealRooted.CombinatorialExamples.CatalanWordPeaks.GeneratingFunction
public import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic

/-!
# Value and parameter derivative at the transition

We specialize the checked coefficient-formula generating function. The radical
branch is characterized algebraically by its square and constant coefficient.
Cancellation uses the integral-domain power-series API.

Source: ProgramComputer, *Strict peaks in Catalan words*, analytic proof,
ISC license. Copyright 2026 ProgramComputer

Permission to use, copy, modify, and/or distribute this software for any
purpose with or without fee is hereby granted, provided that the above
copyright notice and this permission notice appear in all copies.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
-/

@[expose] public noncomputable section

namespace RealRooted.CatalanWordPeaks.NearPoleSeries

open Polynomial Finset
open scoped BigOperators

local notation "P" => ℝ[X]
local notation "PS" => PowerSeries P
local notation "S" => PowerSeries ℝ
local notation "z" => (PowerSeries.X : PS)
local notation "x" => (PowerSeries.X : S)
local notation "c" => (PowerSeries.C : ℝ →+* S)

/-- The transition evaluation parameter. -/
def tau : ℝ := -11 / 16
/-- The subleading pole rate. -/
def a : ℝ := 27 / 16
/-- The leading derivative-pole rate. -/
def b : ℝ := 9 / 4

/-- The residual quadratic under the square root. -/
def Q : S := 1 + c (1/2) * x + c (9/16) * x^2
/-- The subleading linear pole factor. -/
def poleA : S := 1 - c a * x
/-- The leading linear pole factor. -/
def poleB : S := 1 - c b * x
/-- Formal geometric reciprocal of `1 - t*x`. -/
def geo (t : ℝ) : S := PowerSeries.rescale t (PowerSeries.mk 1)

/-- Coefficients of the formal geometric reciprocal. -/
@[simp] theorem coeff_geo (n : ℕ) (t : ℝ) :
    PowerSeries.coeff n (geo t) = t^n := by
  simp [geo]

/-- The geometric series inverts its linear pole factor. -/
theorem pole_mul_geo (t : ℝ) : (1 - c t*x) * geo t = 1 := by
  have h := congrArg (PowerSeries.rescale t) (PowerSeries.mk_one_mul_one_sub_eq_one ℝ)
  simpa [geo, PowerSeries.rescale_X, mul_comm] using h

private def K : S := 1 - c a * x^2
private def J : S := 1 + c a * x^2

/-- Evaluation of the formula-defined polynomial at the near-zero cutoff. -/
def F_tau : S := PowerSeries.mk fun n => (polynomial n).eval tau

/-- Evaluation of the derivative in the strict-peak variable at the cutoff. -/
def DtF_tau : S := PowerSeries.mk fun n => (Polynomial.derivative (polynomial n)).eval tau

/-- Coefficients of the value series. -/
@[simp] theorem coeff_F_tau (n : ℕ) :
    PowerSeries.coeff n F_tau = (polynomial n).eval tau := PowerSeries.coeff_mk _ _

/-- Coefficients of the parameter-derivative series. -/
@[simp] theorem coeff_DtF_tau (n : ℕ) :
    PowerSeries.coeff n DtF_tau = (Polynomial.derivative (polynomial n)).eval tau :=
  PowerSeries.coeff_mk _ _

private def specialize : PS →+* S :=
  PowerSeries.map (Polynomial.evalRingHom tau)

private def specializeDerivative : PS →+ S where
  toFun f := PowerSeries.mk fun n => (PowerSeries.coeff n f).derivative.eval tau
  map_zero' := by
    ext n
    simp only [PowerSeries.coeff_mk, map_zero, eval_zero]
  map_add' f g := by
    ext n
    simp only [PowerSeries.coeff_mk, map_add, eval_add]

private theorem coeff_specializeDerivative (n : ℕ) (f : PS) :
    PowerSeries.coeff n (specializeDerivative f) =
      (PowerSeries.coeff n f).derivative.eval tau := by
  change PowerSeries.coeff n (PowerSeries.mk fun k =>
    (PowerSeries.coeff k f).derivative.eval tau) = _
  rw [PowerSeries.coeff_mk]

private theorem specialize_G : specialize GeneratingFunction.series = F_tau := by
  ext n
  simp [specialize, GeneratingFunction.series]

private theorem specializeDerivative_G :
    specializeDerivative GeneratingFunction.series = DtF_tau := by
  ext n
  simp [coeff_specializeDerivative, GeneratingFunction.series]

private theorem specialize_C (p : P) :
    specialize (PowerSeries.C p) = c (p.eval tau) := PowerSeries.map_C _ _

private theorem specialize_X : specialize z = x := PowerSeries.map_X _

private theorem specializeDerivative_C (p : P) :
    specializeDerivative (PowerSeries.C p) = c (p.derivative.eval tau) := by
  ext n
  simp only [coeff_specializeDerivative, PowerSeries.coeff_C]
  split_ifs <;> simp

private theorem specializeDerivative_X : specializeDerivative z = 0 := by
  ext n
  simp only [coeff_specializeDerivative, PowerSeries.coeff_X, map_zero]
  split_ifs <;> simp

private theorem specializeDerivative_one : specializeDerivative 1 = 0 := by
  simpa using specializeDerivative_C (1 : P)

private theorem specializeDerivative_mul (f g : PS) :
    specializeDerivative (f*g) =
      specializeDerivative f * specialize g + specialize f * specializeDerivative g := by
  ext n
  simp only [coeff_specializeDerivative, PowerSeries.coeff_mul, specialize,
    PowerSeries.coeff_map, Polynomial.derivative_sum, Polynomial.derivative_mul,
    Polynomial.eval_finsetSum, Polynomial.eval_add, Polynomial.eval_mul,
    map_add, Finset.sum_add_distrib]
  rfl

private theorem specializeDerivative_sq (f : PS) :
    specializeDerivative (f^2) = 2 * specialize f * specializeDerivative f := by
  rw [pow_two, specializeDerivative_mul]
  ring

private theorem eval_one_sub_X : (1 - X : P).eval tau = a := by
  norm_num [tau, a]

private theorem eval_X_sub_one : (X - 1 : P).eval tau = -a := by
  norm_num [tau, a]

private theorem specialize_quadratic :
    K * F_tau - x*poleA*F_tau^2 = 1 := by
  have h := congrArg specialize GeneratingFunction.series_eq
  simp only [map_add, map_mul, map_pow, map_one, specialize_G, specialize_C,
    specialize_X, eval_one_sub_X, eval_X_sub_one, map_neg] at h
  unfold K poleA
  linear_combination h

private theorem derivative_eval_one_sub_X : (1 - X : P).derivative.eval tau = -1 := by
  simp

private theorem derivative_eval_X_sub_one : (X - 1 : P).derivative.eval tau = 1 := by
  simp

private theorem derivative_quadratic :
    (K - 2*x*poleA*F_tau)*DtF_tau = x^2*(F_tau^2-F_tau) := by
  have h := congrArg specializeDerivative GeneratingFunction.series_eq
  simp only [map_add, specializeDerivative_one, specializeDerivative_mul,
    specializeDerivative_sq, specializeDerivative_X, specializeDerivative_C,
    specialize_G, specializeDerivative_G, specialize_C, specialize_X,
    map_mul, map_pow, map_one, eval_one_sub_X, eval_X_sub_one, map_neg,
    derivative_eval_one_sub_X, derivative_eval_X_sub_one, map_one] at h
  unfold K poleA
  linear_combination h

/-- The subleading pole factor has constant term one. -/
@[simp] theorem constantCoeff_poleA : PowerSeries.constantCoeff poleA = 1 := by
  simp [poleA]

/-- The leading pole factor has constant term one. -/
@[simp] theorem constantCoeff_poleB : PowerSeries.constantCoeff poleB = 1 := by
  simp [poleB]

private theorem constantCoeff_K : PowerSeries.constantCoeff K = 1 := by
  simp [K]

private theorem half_mul_two : 2 * c (1/2) = 1 := by
  rw [← map_ofNat c 2, ← map_mul]
  norm_num

private theorem discriminant :
    K^2 - 4*x*poleA = poleB^2 * Q := by
  have h :
      (1 - Polynomial.C a * (X : P)^2)^2 - 4*X*(1 - Polynomial.C a*X) =
        (1 - Polynomial.C b*X)^2 *
          (1 + Polynomial.C (1/2)*X + Polynomial.C (9/16)*X^2) := by
    apply Polynomial.funext
    intro y
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_one, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_ofNat, a, b]
    ring
  let ev := Polynomial.eval₂RingHom c x
  have he := congrArg ev h
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_one] at he
  change (1 - c a * x^2)^2 - 4*x*(1 - c a*x) =
    (1 - c b*x)^2 * (1 + c (1/2)*x + c (9/16)*x^2)
  simpa only [ev, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_X] using he

private theorem cancel_unitConstant_zero {f g : S}
    (hf : PowerSeries.constantCoeff f ≠ 0) (hz : f*g = 0) : g = 0 :=
  (mul_eq_zero.mp hz).resolve_left (fun h => hf (by rw [h, map_zero]))

private theorem cancel_unitConstant {f g h : S}
    (hf : PowerSeries.constantCoeff f ≠ 0) (hfg : f*g = f*h) : g = h :=
  mul_left_cancel₀ (fun h => hf (by rw [h, map_zero])) hfg

/-- Upper-branch discriminant factorization selected by the constant coefficient. -/
private theorem branch_factor {R : S} (hR0 : PowerSeries.constantCoeff R = 1)
    (hR : R^2 = Q) :
    K - 2*x*poleA*F_tau = poleB*R := by
  let E := K - 2*x*poleA*F_tau
  have h₁ : E^2 = K^2 - 4*x*poleA := by
    dsimp [E]
    linear_combination (-4*x*poleA) * specialize_quadratic
  have h₂ : E^2 = (poleB*R)^2 := by rw [h₁, discriminant, mul_pow, hR]
  have hc : PowerSeries.constantCoeff (E + poleB*R) ≠ 0 := by
    norm_num [E, constantCoeff_K, hR0]
  apply sub_eq_zero.mp
  apply cancel_unitConstant_zero hc
  linear_combination h₂

/-- The constant-free numerator, shifted down by one power of the length
variable and multiplied by one half. -/
def H (R : S) : S :=
  c (1/2) * PowerSeries.mk fun n => PowerSeries.coeff (n+1) (1 - c a * x^2 - poleB*R)

/-- The part of the derivative numerator after removing the formal square root. -/
def B (Ri : S) : S := c (1/2) * x * (1 + c a * x^2) * Ri

/-- The shifted numerator coefficients in terms of the radical. -/
theorem coeff_H (R : S) (n : ℕ) :
    PowerSeries.coeff n (H R) =
      (b * PowerSeries.coeff n R - PowerSeries.coeff (n+1) R -
        (if n = 1 then a else 0)) / 2 := by
  unfold H poleB
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
  calc
    _ = (1/2) * (PowerSeries.coeff (n+1) (1 - c a*x^2 - R + c b*(x*R))) := by
      congr 1
      congr 1
      ring
    _ = _ := by
      simp only [map_add, map_sub, PowerSeries.coeff_one, Nat.succ_ne_zero, ite_false,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, PowerSeries.coeff_succ_X_mul,
        show n+1 = 2 ↔ n = 1 by lia]
      split_ifs <;> ring

/-- The derivative numerator has zero constant term. -/
@[simp] theorem coeff_B_zero (Ri : S) : PowerSeries.coeff 0 (B Ri) = 0 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [B]

/-- The derivative numerator coefficients in terms of the inverse radical. -/
theorem coeff_B_succ (Ri : S) (n : ℕ) :
    PowerSeries.coeff (n+1) (B Ri) =
      (PowerSeries.coeff n Ri +
        (if 2 ≤ n then a * PowerSeries.coeff (n-2) Ri else 0)) / 2 := by
  unfold B
  calc
    _ = PowerSeries.coeff (n+1) (c (1/2) * (x*(Ri + c a*(x^2*Ri)))) := by
      congr 1
      ring
    _ = _ := by
      rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul, map_add,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
      split_ifs <;> ring

/-- Restoring the removable length factor in the value numerator. -/
theorem X_mul_H {R : S} (hR0 : PowerSeries.constantCoeff R = 1) :
    x * H R = c (1/2) * (1 - c a * x^2 - poleB*R) := by
  have hf : PowerSeries.constantCoeff (K - poleB*R) = 0 := by
    simp [constantCoeff_K, hR0]
  have hs := PowerSeries.eq_X_mul_shift_add_const (K - poleB*R)
  rw [hf, map_zero, add_zero] at hs
  unfold H
  dsimp only [K] at hs
  rw [mul_left_comm, ← hs]

/-- The radical cancels its reciprocal in the derivative numerator. -/
theorem R_mul_B {R Ri : S} (hRi : R*Ri = 1) :
    R * B Ri = c (1/2) * x * (1 + c a * x^2) := by
  unfold B
  calc
    _ = (c (1/2) * x * (1 + c a * x^2)) * (R * Ri) := by ring
    _ = _ := by rw [hRi, mul_one]

/-- The value series as a radical numerator and simple pole. -/
theorem F_tau_eq {R : S} (hR0 : PowerSeries.constantCoeff R = 1)
    (hR : R^2 = Q) : F_tau = H R * geo a := by
  have hE := branch_factor hR0 hR
  have hX : x*(H R) = x*(poleA*F_tau) := by
    have hh := X_mul_H hR0
    change x*H R = c (1/2)*(K-poleB*R) at hh
    linear_combination hh + c (1/2)*hE + (x*poleA*F_tau)*half_mul_two
  have hH : H R = poleA*F_tau := by
    apply PowerSeries.ext
    intro n
    simpa only [PowerSeries.coeff_succ_X_mul] using
      congrArg (PowerSeries.coeff (n+1)) hX
  have hA : poleA*geo a = 1 := pole_mul_geo a
  rw [hH]
  linear_combination (-F_tau)*hA

private theorem pole_relation : 4*poleA - 3*poleB = 1 := by
  have hcoeff : 4 * c a = 3 * c b := by
    rw [← map_ofNat c 4, ← map_ofNat c 3, ← map_mul, ← map_mul]
    norm_num [a,b]
  unfold poleA poleB
  linear_combination (-x)*hcoeff

/-- The derivative series as simple and double pole terms. -/
theorem DtF_tau_eq {R Ri : S} (hR0 : PowerSeries.constantCoeff R = 1)
    (hR : R^2 = Q) (hRi : R*Ri = 1) :
    DtF_tau = (c (1/2)*x)*geo a + 4*B Ri*geo b -
      3*B Ri*geo a - x*H R*(geo a)^2 := by
  let E := poleB*R
  let h := c (1/2)
  have hE : E = K - 2*x*poleA*F_tau := (branch_factor hR0 hR).symm
  have hEvt : E*DtF_tau = x^2*(F_tau^2-F_tau) := by
    rw [hE]
    exact derivative_quadratic
  have hKJ : K + J = 2 := by unfold K J; ring
  have hhalf : 2*h = 1 := half_mul_two
  have hRB : R*B Ri = h*x*J := R_mul_B hRi
  have hmain : E*poleA*DtF_tau = x*E*(h-F_tau) + R*B Ri := by
    rw [hRB]
    linear_combination poleA*hEvt - x*(h-F_tau)*hE + x*specialize_quadratic -
      h*x*hKJ + (x^2*poleA*F_tau - x)*hhalf
  have hA : poleA*geo a = 1 := pole_mul_geo a
  have hB : poleB*geo b = 1 := pole_mul_geo b
  have hF : F_tau = H R*geo a := F_tau_eq hR0 hR
  have hn : PowerSeries.constantCoeff (E*poleA) ≠ 0 := by
    simp [E, hR0]
  apply cancel_unitConstant hn
  have hlin : 4*poleA*R*B Ri - 3*poleB*R*B Ri = R*B Ri := by
    linear_combination (R*B Ri)*pole_relation
  change E*poleA*DtF_tau =
    E*poleA*(h*x*geo a + 4*B Ri*geo b - 3*B Ri*geo a - x*H R*(geo a)^2)
  rw [hmain, hF]
  dsimp [E]
  linear_combination
    (-(poleB*R)*(h*x - 3*B Ri - x*H R*geo a))*hA -
    (4*B Ri*poleA*R)*hB - hlin

end RealRooted.CatalanWordPeaks.NearPoleSeries
