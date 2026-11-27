/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import RealRooted.CombinatorialExamples.CatalanWordPeaks.PoleSeries
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# Radical coefficients and the two needed pole residues

We merge the formal radical, its convergence bound and scalar evaluations.
Only the two residue evaluations used by the final coefficient bounds remain.

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

open PowerSeries Finset
open scoped BigOperators

local notation "S" => PowerSeries ℝ
local notation "x" => (PowerSeries.X : S)
local notation "c" => (PowerSeries.C : ℝ →+* S)
local notation "cf" => PowerSeries.coeff (R := ℝ)

/-- Coefficients of the formal inverse radical. -/
def invRootCoeff : ℕ → ℝ
  | 0 => 1
  | 1 => -1/4
  | n+2 => -(((2*(n:ℝ)+3)/2)*invRootCoeff (n+1) +
      (2*(n:ℝ)+2)*(9/16)*invRootCoeff n)/(2*((n:ℝ)+2))

/-- The formal inverse square-root branch. -/
def Ri : S := PowerSeries.mk invRootCoeff

/-- The formal square-root branch. -/
def R : S := Q * Ri

@[simp] private theorem coeff_Ri (n : ℕ) :
    PowerSeries.coeff n Ri = invRootCoeff n := PowerSeries.coeff_mk _ _

@[simp] private theorem invRootCoeff_zero : invRootCoeff 0 = 1 := rfl

@[simp] private theorem invRootCoeff_one : invRootCoeff 1 = -1/4 := rfl

private theorem invRootCoeff_succ_succ (n : ℕ) :
    invRootCoeff (n+2) = -(((2*(n:ℝ)+3)/2)*invRootCoeff (n+1) +
      (2*(n:ℝ)+2)*(9/16)*invRootCoeff n)/(2*((n:ℝ)+2)) := rfl

private def theta (f : S) : S :=
  PowerSeries.mk fun n => (n : ℝ) * PowerSeries.coeff n f

@[simp] private theorem coeff_theta (n : ℕ) (f : S) :
    PowerSeries.coeff n (theta f) = (n : ℝ) * PowerSeries.coeff n f :=
  PowerSeries.coeff_mk _ _

private theorem theta_mul (f g : S) :
    theta (f*g) = theta f*g + f*theta g := by
  ext n
  simp only [coeff_theta, map_add, PowerSeries.coeff_mul]
  rw [mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro i hi
  have hij : (i.1 : ℝ) + (i.2 : ℝ) = (n : ℝ) := by
    exact_mod_cast Finset.HasAntidiagonal.mem_antidiagonal.mp hi
  rw [← hij]
  ring

private theorem theta_Q :
    theta Q = c (1/2)*x + c (9/8)*x^2 := by
  ext n
  simp only [Q, coeff_theta, map_add, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_X, PowerSeries.coeff_X_pow, PowerSeries.coeff_one]
  by_cases h₀ : n = 0
  · norm_num [h₀]
  by_cases h₁ : n = 1
  · norm_num [h₁]
  by_cases h₂ : n = 2
  · norm_num [h₂]
  simp [h₀, h₁, h₂]

private theorem coeff_x_mul (f : S) (n : ℕ) :
    PowerSeries.coeff n (x*f) =
      if 1 ≤ n then PowerSeries.coeff (n-1) f else 0 := by
  simpa only [pow_one] using PowerSeries.coeff_X_pow_mul' f 1 n

private theorem theta_Ri_equation : 2*Q*theta Ri + theta Q*Ri = 0 := by
  rw [theta_Q]
  have hs :
      2*Q*theta Ri + (c (1/2)*x + c (9/8)*x^2)*Ri =
        c 2 * theta Ri + c 2*(c (1/2)*(x*theta Ri)) +
        c 2*(c (9/16)*(x^2*theta Ri)) + c (1/2)*(x*Ri) + c (9/8)*(x^2*Ri) := by
    unfold Q
    rw [map_ofNat]
    ring
  rw [hs]
  ext n
  simp only [map_add, PowerSeries.coeff_C_mul, coeff_x_mul,
    PowerSeries.coeff_X_pow_mul', coeff_theta, coeff_Ri, map_zero]
  obtain _ | _ | n := n
  · norm_num
  · norm_num
  · rw [ite_eq_left (by lia), ite_eq_left (by lia), ite_eq_left (by lia), ite_eq_left (by lia)]
    have hden : (2 : ℝ)*((n : ℝ)+2) ≠ 0 := by
      exact mul_ne_zero (by norm_num)
        (ne_of_gt (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) (by norm_num)))
    have he := (eq_div_iff hden).mp (invRootCoeff_succ_succ n)
    simp only [show n.succ.succ - 1 = n+1 by lia,
      show n.succ.succ - 2 = n by lia, Nat.cast_succ]
    linear_combination he

@[simp] private theorem constantCoeff_Q : PowerSeries.constantCoeff Q = 1 := by
  simp [Q]

@[simp] private theorem constantCoeff_Ri : PowerSeries.constantCoeff Ri = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_Ri, invRootCoeff_zero]

/-- The radical has constant coefficient one. -/
@[simp] theorem constantCoeff_R : PowerSeries.constantCoeff R = 1 := by
  simp [R]

private theorem Q_mul_Ri_sq : Q*Ri^2 = 1 := by
  have h : theta (Q*Ri^2) = 0 := by
    simp only [pow_two, theta_mul]
    linear_combination Ri*theta_Ri_equation
  ext n
  cases n with
  | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  | succ n =>
    have hh := congrArg (PowerSeries.coeff (n+1)) h
    simp only [coeff_theta, map_zero] at hh
    rw [PowerSeries.coeff_one, ite_eq_right (Nat.succ_ne_zero n)]
    exact (mul_eq_zero.mp hh).resolve_left (by exact_mod_cast Nat.succ_ne_zero n)

/-- The two radical branches are reciprocal. -/
theorem R_mul_Ri : R*Ri = 1 := by
  simpa only [R, pow_two, mul_assoc] using Q_mul_Ri_sq

/-- The radical squares to the residual quadratic. -/
theorem R_sq : R^2 = Q := by
  unfold R
  rw [mul_pow, pow_two Q, mul_assoc, Q_mul_Ri_sq, mul_one]

private lemma recurrence_bound {u : ℕ → ℝ}
    (c0 : u 0 = 1) (c1 : u 1 = -1 / 4)
    (rec : ∀ n : ℕ, u (n+2) = -(((2*(n:ℝ)+3)/2)*u (n+1) +
      ((2*(n:ℝ)+2)*(9/16))*u n)/(2*((n:ℝ)+2))) :
    ∀ n : ℕ, |u (n+1)| ≤ (1/4 : ℝ)*(5/4)^n := by
  have hs (n : ℕ) : |u (n+2)| ≤ (1/2 : ℝ)*|u (n+1)| + (9/16 : ℝ)*|u n| := by
    rw [rec, abs_div, abs_neg, abs_of_pos (show (0:ℝ)<2*((n:ℝ)+2) by positivity)]
    apply (div_le_iff₀ (by positivity)).mpr
    calc
      _ ≤ |((2*(n:ℝ)+3)/2)*u (n+1)| + |((2*(n:ℝ)+2)*(9/16))*u n| := abs_add_le _ _
      _ ≤ _ := by
        rw [abs_mul, abs_mul, abs_of_nonneg (show (0:ℝ)≤(2*(n:ℝ)+3)/2 by positivity),
          abs_of_nonneg (show (0:ℝ)≤(2*(n:ℝ)+2)*(9/16) by positivity)]
        nlinarith only [abs_nonneg (u n), abs_nonneg (u (n+1))]
  intro n
  induction n using Nat.twoStepInduction with
  | zero => norm_num [c1, abs_div]
  | one => norm_num [rec 0, c0, c1, abs_div]
  | more n h0 h1 =>
    have step := hs (n+1)
    calc
      _ ≤ (1/2 : ℝ)*|u (n+1+1)| + (9/16 : ℝ)*|u (n+1)| := step
      _ ≤ (1/2 : ℝ)*((1/4)*(5/4)^(n+1))+(9/16)*((1/4)*(5/4)^n) := by gcongr
      _ ≤ _ := by
        rw [pow_succ (5 / 4 : ℝ) (n+1), pow_succ (5 / 4 : ℝ) n]
        nlinarith [pow_pos (by norm_num : (0:ℝ)<5/4) n]

/-- The convergent coefficient evaluation used at the two positive poles. -/
private def poleValue (f : PowerSeries ℝ) (t : ℝ) : ℝ := ∑' n, coeff n f * t^n

private lemma absolute_from_geometric {f : PowerSeries ℝ} {A t : ℝ}
    (hf : ∀ n, |coeff n f| ≤ A * (5 / 4 : ℝ) ^ n) (ht : 0 ≤ t) (hT : (5 / 4 : ℝ) * t < 1) :
    Summable (fun n => |coeff n f| *t^n) ∧
      ∑' n, |coeff n f| *t^n ≤ A/(1-(5/4)*t) := by
  have hnon : 0 ≤ (5/4 : ℝ)*t := by positivity
  have hg := (summable_geometric_of_lt_one hnon hT).mul_left A
  have bound (n : ℕ) : |coeff n f| *t^n ≤ A*((5/4)*t)^n := by
    rw [mul_pow, ← mul_assoc]; gcongr; exact hf n
  have hh := Summable.of_nonneg_of_le
    (fun n => mul_nonneg (abs_nonneg _) (pow_nonneg ht n)) bound hg
  refine ⟨hh, (hh.tsum_le_tsum bound hg).trans_eq ?_⟩
  rw [tsum_mul_left, tsum_geometric_of_lt_one hnon hT]
  rfl

private lemma positive_value {f : PowerSeries ℝ} {t : ℝ}
    (h0 : coeff 0 f = 1)
    (hsmall : ∀ n : ℕ, |coeff (n+1) f| ≤ (1 / 4 : ℝ) * (5 / 4) ^ n)
    (ht : 0 ≤ t) (hT : (5 / 4 : ℝ) * t < 1) (hgap : (t/4)/(1-5/4 * t) < 1) :
    0 < poleValue f t := by
  have hnon : 0 ≤ (5 / 4 : ℝ)*t := by positivity
  have hg := (summable_geometric_of_lt_one hnon hT).mul_left (t/4)
  have bound (n : ℕ) : ‖coeff (n+1) f * t^(n+1)‖ ≤ (t/4)*((5/4)*t)^n := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg ht _), pow_succ, mul_pow]
    calc
      _ ≤ ((1 / 4 : ℝ)*(5/4)^n)*(t^n*t) := by gcongr; exact hsmall n
      _ = _ := by ring
  have hnorm := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) bound hg
  have htail := hnorm.of_norm
  have hbound := (norm_tsum_le_tsum_norm hnorm).trans (hnorm.tsum_le_tsum bound hg)
  rw [tsum_mul_left, tsum_geometric_of_lt_one hnon hT, ← div_eq_mul_inv, Real.norm_eq_abs] at hbound
  have hsum : Summable (fun n => coeff n f * t^n) := (summable_nat_add_iff 1).mp htail
  rw [poleValue, hsum.tsum_eq_zero_add, h0, pow_zero, mul_one]
  linarith [(abs_lt.mp (hbound.trans_lt hgap)).1]

private lemma value_mul {f g : PowerSeries ℝ} {t : ℝ}
    (hf : Summable (fun n => ‖coeff n f * t ^ n‖))
    (hg : Summable (fun n => ‖coeff n g * t ^ n‖)) :
    poleValue (f*g) t = poleValue f t * poleValue g t := by
  unfold poleValue
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg]
  apply tsum_congr
  intro n
  rw [coeff_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [← he, pow_add]
  ring

private lemma coeff_Ri_tail (n : ℕ) :
    |coeff (n+1) Ri| ≤ (1/4 : ℝ)*(5/4)^n := by
  simpa only [coeff_Ri] using
    recurrence_bound invRootCoeff_zero invRootCoeff_one invRootCoeff_succ_succ n

private lemma coeff_Ri_unit (n : ℕ) :
    |coeff n Ri| ≤ (5 / 4 : ℝ)^n := by
  cases n with
  | zero => norm_num
  | succ n =>
    have h := coeff_Ri_tail n
    rw [pow_succ]
    nlinarith [pow_pos (by norm_num : (0:ℝ)<5/4) n]

/-- A geometric coefficient majorant for its reciprocal. -/
lemma coeff_Ri_bound (n : ℕ) :
    |coeff n Ri| ≤ 3*(5 / 4 : ℝ)^n := by
  linarith [coeff_Ri_unit n, pow_pos (by norm_num : (0:ℝ)<5/4) n]

private lemma coeff_R_expansion (n : ℕ) :
    coeff n R = coeff n Ri +
      (1/2 : ℝ)*(if 1 ≤ n then coeff (n-1) Ri else 0) +
      (9/16 : ℝ)*(if 2 ≤ n then coeff (n-2) Ri else 0) := by
  have he : R = Ri + PowerSeries.C (1/2)*(X^1*Ri) + PowerSeries.C (9/16)*(X^2*Ri) := by
    unfold R Q
    ring
  rw [he]
  simp only [map_add, coeff_C_mul, coeff_X_pow_mul']

/-- A geometric coefficient majorant for the radical. -/
lemma coeff_R_bound (n : ℕ) :
    |coeff n R| ≤ 2*(5 / 4 : ℝ)^n := by
  rw [coeff_R_expansion]
  obtain _ | _ | n := n
  · norm_num
  · norm_num [abs_div]
  · simp only [ite_eq_left (show 1 ≤ n.succ.succ by lia),
      ite_eq_left (show 2 ≤ n.succ.succ by lia), Nat.succ_sub_one,
      show n.succ.succ-2=n by lia]
    calc
      _ ≤ |coeff (n+2) Ri| + |(1/2:ℝ)*coeff (n+1) Ri| +
        |(9/16:ℝ)*coeff n Ri| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ (5 / 4 : ℝ)^(n+2) + (1/2)*(5/4)^(n+1) + (9/16)*(5/4)^n := by
        rw [abs_mul, abs_mul]
        rw [abs_of_pos (by norm_num : (0 : ℝ) < 1/2), abs_of_pos (by norm_num : (0 : ℝ) < 9/16)]
        gcongr <;> apply coeff_Ri_unit
      _ ≤ _ := by
        change _ ≤ 2*(5 / 4 : ℝ)^(n+2)
        rw [pow_succ (5 / 4 : ℝ) (n+1), pow_succ (5 / 4 : ℝ) n]
        nlinarith [pow_pos (by norm_num : (0:ℝ)<5/4) n]

private lemma absSummable_at {f : PowerSeries ℝ} {A t : ℝ}
    (hf : ∀ n, |coeff n f| ≤ A * (5 / 4 : ℝ) ^ n) (ht : 0 ≤ t) (hT : (5 / 4 : ℝ) * t < 1) :
    Summable (fun n => ‖coeff n f * t^n‖) := by
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg ht _)] using
    (absolute_from_geometric hf ht hT).1

private lemma absSummable_R {t : ℝ} (ht : 0 ≤ t) (hT : (5 / 4 : ℝ) * t < 1) :
    Summable (fun n => ‖coeff n R * t^n‖) := absSummable_at coeff_R_bound ht hT

private lemma absSummable_Ri {t : ℝ} (ht : 0 ≤ t) (hT : (5 / 4 : ℝ) * t < 1) :
    Summable (fun n => ‖coeff n Ri * t^n‖) := absSummable_at coeff_Ri_bound ht hT

private lemma poleValue_Ri_pos {t : ℝ} (ht : 0 ≤ t) (hT : (5 / 4 : ℝ) * t < 1)
    (hgap : (t / 4) / (1 - 5 / 4 * t) < 1) : 0 < poleValue Ri t :=
  positive_value (by simp) coeff_Ri_tail ht hT hgap

/-- Evaluating by a convergent Taylor series with explicitly specified sum. -/
abbrev PoleHasSum (P : S) (t y : ℝ) := HasSum (fun n => cf n P * t^n) y

private theorem eval_X_mul {P : S} {t y : ℝ} (hp : PoleHasSum P t y) :
    PoleHasSum (x*P) t (t*y) := by
  have h : HasSum (fun n => cf (n+1) (x*P) * t^(n+1)) (t*y) := by
    refine (hp.mul_left t).congr_fun ?_
    intro n
    rw [PowerSeries.coeff_succ_X_mul, pow_succ]
    ring
  simpa only [Finset.sum_range_one, PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
    PowerSeries.constantCoeff_X, zero_mul, pow_zero, mul_one, add_zero] using
    (hasSum_nat_add_iff (f := fun n => cf n (x*P) * t^n) 1).mp h

private theorem eval_C_mul {P : S} {t y v : ℝ} (hp : PoleHasSum P t y) :
    PoleHasSum (c v*P) t (v*y) := by
  simpa only [PoleHasSum, PowerSeries.coeff_C_mul, mul_assoc] using hp.mul_left v

private theorem eval_sub {P T : S} {t y z : ℝ}
    (hp : PoleHasSum P t y) (hq : PoleHasSum T t z) : PoleHasSum (P-T) t (y-z) := by
  simpa only [PoleHasSum, map_sub, sub_mul] using hp.sub hq

private theorem eval_add {P T : S} {t y z : ℝ}
    (hp : PoleHasSum P t y) (hq : PoleHasSum T t z) : PoleHasSum (P+T) t (y+z) := by
  simpa only [PoleHasSum, map_add, add_mul] using hp.add hq

private theorem eval_one (t : ℝ) : PoleHasSum (1 : S) t 1 := by
  refine (hasSum_ite_eq (0 : ℕ) (1 : ℝ)).congr_fun ?_
  intro n
  by_cases hn : n = 0
  · simp [hn]
  · simp [PowerSeries.coeff_one, hn]

private theorem eval_x (t : ℝ) : PoleHasSum x t t := by
  simpa only [mul_one] using eval_X_mul (eval_one t)

private theorem eval_x_sq (t : ℝ) : PoleHasSum (x^2) t (t^2) := by
  simpa only [pow_two] using eval_X_mul (eval_x t)

private theorem eval_X_cancel {P : S} {t y : ℝ} (ht : t ≠ 0)
    (hp : PoleHasSum (x * P) t y) : PoleHasSum P t (y/t) := by
  have h := (hasSum_nat_add_iff' 1).mpr hp
  simp only [Finset.sum_range_one, PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
    PowerSeries.constantCoeff_X, zero_mul, pow_zero, mul_one, sub_zero] at h
  refine (h.mul_right t⁻¹).congr_fun ?_
  intro n
  rw [PowerSeries.coeff_succ_X_mul, pow_succ]
  field_simp

private theorem value_one (t : ℝ) : poleValue 1 t = 1 := (eval_one t).tsum_eq

private theorem value_Q (t : ℝ) : poleValue Q t = 1 + t/2 + (9/16)*t^2 := by
  have h := eval_add (eval_add (eval_one t) (eval_C_mul (v := 1/2) (eval_x t)))
    (eval_C_mul (v := 9/16) (eval_x_sq t))
  simpa only [poleValue, Q, div_eq_mul_inv, mul_comm, one_mul] using h.tsum_eq

private theorem poleValue_R_mul_Ri {t : ℝ}
    (hR : Summable (fun n => ‖cf n R * t ^ n‖))
    (hi : Summable (fun n => ‖cf n Ri * t ^ n‖)) :
    poleValue R t * poleValue Ri t = 1 := by
  rw [← value_mul hR hi, R_mul_Ri, value_one]

private theorem poleValue_R_sq {t : ℝ}
    (hR : Summable (fun n => ‖cf n R * t ^ n‖)) :
    poleValue R t ^ 2 = 1 + t/2 + (9/16)*t^2 := by
  rw [pow_two, ← value_mul hR hR, ← pow_two, R_sq, value_Q]

private theorem poleValue_R_pos {t : ℝ}
    (hR : Summable (fun n => ‖cf n R * t ^ n‖))
    (hi : Summable (fun n => ‖cf n Ri * t ^ n‖)) (hip : 0 < poleValue Ri t) :
    0 < poleValue R t := by
  have h := (eq_div_iff hip.ne').mpr (poleValue_R_mul_Ri hR hi)
  rw [h]
  positivity

private theorem eq_of_sq_eq_pos {u v : ℝ} (hu : 0 < u) (hv : 0 < v)
    (h : u ^ 2 = v ^ 2) : u = v := by
  nlinarith [sq_nonneg (u - v)]

private theorem poleValue_R_at_a : poleValue R (16/27) = 11/9 := by
  have hR := absSummable_R (t := 16/27) (by norm_num) (by norm_num)
  have hi := absSummable_Ri (t := 16/27) (by norm_num) (by norm_num)
  have hip := poleValue_Ri_pos (t := 16/27) (by norm_num) (by norm_num) (by norm_num)
  apply eq_of_sq_eq_pos (poleValue_R_pos hR hi hip) (by norm_num)
  rw [poleValue_R_sq hR]
  norm_num

private theorem sqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)

private theorem sq_sqrt3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

private theorem poleValue_R_at_b : poleValue R (4/9) = 2/Real.sqrt 3 := by
  have hR := absSummable_R (t := 4/9) (by norm_num) (by norm_num)
  have hi := absSummable_Ri (t := 4/9) (by norm_num) (by norm_num)
  have hip := poleValue_Ri_pos (t := 4/9) (by norm_num) (by norm_num) (by norm_num)
  apply eq_of_sq_eq_pos (poleValue_R_pos hR hi hip) (div_pos (by norm_num) sqrt3_pos)
  rw [poleValue_R_sq hR, div_pow (2:ℝ) (Real.sqrt 3), sq_sqrt3]
  norm_num

private theorem poleValue_Ri_at_b : poleValue Ri (4/9) = Real.sqrt 3/2 := by
  have hR := absSummable_R (t := 4/9) (by norm_num) (by norm_num)
  have hi := absSummable_Ri (t := 4/9) (by norm_num) (by norm_num)
  have h := poleValue_R_mul_Ri hR hi
  rw [poleValue_R_at_b] at h
  apply mul_left_cancel₀ ((div_pos (by norm_num : (0:ℝ) < 2) sqrt3_pos).ne')
  rw [h]
  field_simp [sqrt3_pos.ne']

/-- The value of the numerator after cancelling the removable factor x. -/
private theorem H_eval {P : S} {t y : ℝ} (hP : PowerSeries.constantCoeff P = 1)
    (ht : t ≠ 0) (hy : PoleHasSum P t y) :
    PoleHasSum (H P) t ((1-a*t^2-(1-b*t)*y)/(2*t)) := by
  have hM : PoleHasSum (poleB*P) t (y-b*(t*y)) := by
    unfold poleB
    rw [sub_mul, one_mul, mul_assoc]
    exact eval_sub hy (eval_C_mul (v := b) (eval_X_mul hy))
  have hh := eval_C_mul (v := 1/2)
    (eval_sub (eval_sub (eval_one t) (eval_C_mul (v := a) (eval_x_sq t))) hM)
  rw [← X_mul_H hP] at hh
  convert eval_X_cancel ht hh using 1
  ring

/-- The value of the derivative numerator. -/
private theorem B_eval {P : S} {t y : ℝ} (hy : PoleHasSum P t y) :
    PoleHasSum (B P) t (t*(1+a*t^2)*y/2) := by
  have hxx := eval_X_mul (eval_X_mul hy)
  have hh := eval_C_mul (v := 1/2)
    (eval_X_mul (eval_add hy (eval_C_mul (v := a) hxx)))
  have heq : B P = c (1/2)*(x*(P+c a*(x*(x*P)))) := by
    change c (1/2)*x*(1+c a*x^2)*P = _
    ring
  rw [heq]
  convert hh using 1
  ring

/-- The simple-pole residue is the convergent value of the numerator series. -/
theorem hasSum_H_at_a : PoleHasSum (H R) (16/27) (11/16) := by
  have hR := absSummable_R (t := 16/27) (by norm_num) (by norm_num)
  have hs := hR.of_norm.hasSum
  change PoleHasSum R (16/27) (poleValue R (16/27)) at hs
  rw [poleValue_R_at_a] at hs
  convert H_eval constantCoeff_R (by norm_num : (16/27 : ℝ) ≠ 0) hs using 1
  norm_num [a, b]

/-- The double-pole residue is the convergent value of the numerator series. -/
theorem hasSum_B_at_b : PoleHasSum (B Ri) (4/9) (4*Real.sqrt 3/27) := by
  have hi := absSummable_Ri (t := 4/9) (by norm_num) (by norm_num)
  have hs := hi.of_norm.hasSum
  change PoleHasSum Ri (4/9) (poleValue Ri (4/9)) at hs
  rw [poleValue_Ri_at_b] at hs
  convert B_eval hs using 1
  norm_num [a]
  ring

end RealRooted.CatalanWordPeaks.NearPoleSeries
