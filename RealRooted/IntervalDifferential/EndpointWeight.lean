/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Analysis.Complex.Basic
import RealRooted.Interlacing.SecondOrderPreservation
public import RealRooted.IntervalDifferential.Certificates
import RealRooted.IntervalDifferential.Degree
import RealRooted.Mathlib.Algebra.Polynomial.Derivative
import RealRooted.IntervalDifferential.LinearInsertion
import RealRooted.IntervalDifferential.RootSums
import RealRooted.SimpleRoots
import RealRooted.Wronskian.Algebra
import Mathlib.Tactic

/-!
# Interval insertion with a variable endpoint weight

Real spectral factors insert simple roots in the unit interval. Conjugate pairs
use root-sum inequalities and shifted linear test points. The disk and starting
thresholds give the structural long-cycle descent transfer (unpublished notes,
November 2026).
-/

@[expose] public noncomputable section

open Polynomial

namespace RealRooted.IntervalDifferential

/-- The interval differential operator `(X² - 1) ∂ + c X`. -/
def intervalOperator (c : ℝ) : ℝ[X] →ₗ[ℝ] ℝ[X] where
  toFun F := (X ^ 2 - 1) * F.derivative + C c * X * F
  map_add' F G := by
    simp only [derivative_add]
    ring
  map_smul' a F := by
    simp only [smul_eq_C_mul, derivative_mul, derivative_C, zero_mul, zero_add,
      RingHom.id_apply, smul_add]
    ring

/-- Insert a real spectral factor into the interval differential operator. -/
def intervalLinearFactor (c a : ℝ) (F : ℝ[X]) : ℝ[X] :=
  intervalOperator c F - C a * F

/-- Insert a conjugate pair into the interval differential operator. -/
def intervalQuadraticFactor (c a b : ℝ) (F : ℝ[X]) : ℝ[X] :=
  intervalLinearFactor c a (intervalLinearFactor c a F) + C (b ^ 2) * F

@[simp] theorem intervalOperator_apply (c : ℝ) (F : ℝ[X]) :
    intervalOperator c F = (X ^ 2 - 1) * F.derivative + C c * X * F := rfl

/-- A positive endpoint weight makes a linear insertion raise degree by one. -/
theorem intervalLinearFactor_natDegree (c a : ℝ) (F : ℝ[X]) (hc : 0 < c)
    (hF : F ≠ 0) : (intervalLinearFactor c a F).natDegree = F.natDegree + 1 := by
  have ht : (1 * (F.natDegree : ℝ) + c) * F.leadingCoeff ≠ 0 :=
    mul_ne_zero (by positivity) (leadingCoeff_ne_zero.mpr hF)
  have hd := natDegree_and_leadingCoeff_quadratic_derivative_add_linear_mul_add
    F (-F.derivative) 0 1 (-a) c
    (by rw [natDegree_neg]; exact (natDegree_derivative_le F).trans (Nat.sub_le _ _)) ht
  convert hd.1 using 1
  simp only [intervalLinearFactor, intervalOperator_apply, map_zero, map_one, map_neg,
    zero_mul, zero_add, one_mul]
  congr 1
  ring

/-- Positive-weight linear insertion cannot annihilate a nonzero polynomial. -/
theorem intervalLinearFactor_ne_zero (c a : ℝ) (F : ℝ[X]) (hc : 0 < c)
    (hF : F ≠ 0) : intervalLinearFactor c a F ≠ 0 := by
  intro hz
  have hd := intervalLinearFactor_natDegree c a F hc hF
  rw [hz, natDegree_zero] at hd
  lia

@[simp] theorem intervalLinearFactor_eval (c a x : ℝ) (F : ℝ[X]) :
    (intervalLinearFactor c a F).eval x =
      (x ^ 2 - 1) * F.derivative.eval x + (c * x - a) * F.eval x := by
  simp only [intervalLinearFactor, intervalOperator_apply, eval_sub, eval_add, eval_mul, eval_pow,
    eval_X, eval_one, eval_C]
  ring

/-- An interval-simple polynomial has nonzero values at both endpoints. -/
theorem eval_endpoints_ne_zero_of_roots_mem_Ioo {F : ℝ[X]} (hF : F ≠ 0)
    (hi : ∀ r ∈ F.roots, -1 < r ∧ r < 1) : F.eval (-1) ≠ 0 ∧ F.eval 1 ≠ 0 := by
  constructor <;> intro hz
  · have h := (hi (-1) ((mem_roots hF).mpr hz)).1
    exact (lt_irrefl _) h
  · have h := (hi 1 ((mem_roots hF).mpr hz)).2
    exact (lt_irrefl _) h

/-- Real spectral factors between the endpoint weights insert one simple root
in every gap, including the two endpoint gaps. -/
theorem intervalLinearFactor_roots (c a : ℝ) (F : ℝ[X]) (hc : 0 < c)
    (hF : F.Splits) (hF0 : F ≠ 0) (hnd : F.roots.Nodup)
    (hi : ∀ r ∈ F.roots, -1 < r ∧ r < 1) (ha : -c < a ∧ a < c) :
    (intervalLinearFactor c a F).Splits ∧
      (intervalLinearFactor c a F).roots.Nodup ∧
      ∀ r ∈ (intervalLinearFactor c a F).roots, -1 < r ∧ r < 1 := by
  apply splits_nodup_interval_of_root_derivative_signs hF hF0 hnd hi
    (intervalLinearFactor_natDegree c a F hc hF0)
  · intro r hr
    have hroot := (mem_roots hF0).mp hr
    have hd := (HasSimpleRoots.of_roots_nodup hF0 hnd).eval_derivative_ne_zero hroot
    rw [intervalLinearFactor_eval, hroot, mul_zero, add_zero]
    have hs : r ^ 2 - 1 < 0 := by nlinarith [(hi r hr).1, (hi r hr).2]
    nlinarith [sq_pos_of_ne_zero hd]
  · have he := (eval_endpoints_ne_zero_of_roots_mem_Ioo hF0 hi).1
    simp only [intervalLinearFactor_eval]
    norm_num only
    nlinarith [sq_pos_of_ne_zero he, ha.1]
  · have he := (eval_endpoints_ne_zero_of_roots_mem_Ioo hF0 hi).2
    simp only [intervalLinearFactor_eval]
    norm_num only
    nlinarith [sq_pos_of_ne_zero he, ha.2]

/-- A linear insertion has no old root when the old roots are simple and interior. -/
theorem intervalLinearFactor_eval_base_ne_zero (c a s : ℝ) (F : ℝ[X])
    (hF0 : F ≠ 0) (hnd : F.roots.Nodup)
    (hi : ∀ r ∈ F.roots, -1 < r ∧ r < 1)
    (hG : (intervalLinearFactor c a F).eval s = 0) : F.eval s ≠ 0 := by
  intro hz
  have hr := (mem_roots hF0).mpr hz
  have hd := (HasSimpleRoots.of_roots_nodup hF0 hnd).eval_derivative_ne_zero hz
  rw [intervalLinearFactor_eval, hz, mul_zero, add_zero] at hG
  have hs : s ^ 2 - 1 < 0 := by nlinarith [(hi s hr).1, (hi s hr).2]
  exact (mul_ne_zero hs.ne hd) hG

/-- The derivative at an inserted root has the sign of the old polynomial. -/
theorem intervalLinearFactor_eval_derivative_mul_pos (c a s : ℝ) (F : ℝ[X])
    (hc : 0 < c) (hF : F.Splits) (hi : ∀ r ∈ F.roots, -1 < r ∧ r < 1)
    (hFs : F.eval s ≠ 0) (hG : (intervalLinearFactor c a F).eval s = 0) :
    0 < F.eval s * (intervalLinearFactor c a F).derivative.eval s := by
  have heq : F * (intervalLinearFactor c a F).derivative =
      zigzagJ F.natDegree F + C ((F.natDegree : ℝ) + c) * F ^ 2 +
        intervalLinearFactor c a F * F.derivative := by
    simp only [intervalLinearFactor, intervalOperator_apply, derivative_sub,
      derivative_mul, derivative_X_pow_succ, Nat.cast_one, map_add, map_one, pow_one,
      derivative_one, sub_zero, derivative_C, zero_mul, derivative_X, mul_one, zero_add, zigzagJ,
      C_ofNat, map_natCast]
    ring
  have he := congrArg (fun p : ℝ[X] => p.eval s) heq
  simp only [eval_mul, eval_add, eval_C, eval_pow, hG, zero_mul, add_zero] at he
  by_cases hd : F.natDegree = 0
  · have hj : zigzagJ F.natDegree F = 0 := by
      simp [zigzagJ, hd, derivative_of_natDegree_zero hd]
    rw [hj, eval_zero, hd, Nat.cast_zero, zero_add, zero_add] at he
    rw [he]
    exact mul_pos hc (sq_pos_of_ne_zero hFs)
  · have hj := zigzagJ_eval_pos_of_splits F hF (by lia) hi s hFs
    have hn : 0 ≤ ((F.natDegree : ℝ) + c) * (F.eval s) ^ 2 := by positivity
    linarith

/-- Quadratic insertion raises degree by two. -/
theorem intervalQuadraticFactor_natDegree (c a b : ℝ) (F : ℝ[X]) (hc : 0 < c)
    (hF : F ≠ 0) : (intervalQuadraticFactor c a b F).natDegree = F.natDegree + 2 := by
  have hG := intervalLinearFactor_ne_zero c a F hc hF
  have hd := intervalLinearFactor_natDegree c a (intervalLinearFactor c a F) hc hG
  rw [intervalLinearFactor_natDegree c a F hc hF] at hd
  have hl : (C (b ^ 2) * F).natDegree <
      (intervalLinearFactor c a (intervalLinearFactor c a F)).natDegree := by
    rw [hd]
    exact (natDegree_C_mul_le _ _).trans_lt (by lia)
  rw [intervalQuadraticFactor, natDegree_add_eq_left_of_natDegree_lt hl, hd]

/-- Laguerre's inequality controls a conjugate pair at a linear-insertion root. -/
theorem intervalQuadraticFactor_eval_identity (c a b u s : ℝ) (F : ℝ[X])
    (hG : (intervalLinearFactor c u F).eval s = 0) :
    F.eval s * (intervalQuadraticFactor c a b F).eval s =
      -(1 - s ^ 2) ^ 2 *
        (F.derivative.eval s ^ 2 - F.eval s * F.derivative.derivative.eval s) -
      (c + c * s ^ 2 - 2 * u * s - ((a - u) ^ 2 + b ^ 2)) * F.eval s ^ 2 := by
  have hid : F * intervalQuadraticFactor c a b F +
      (1 - X ^ 2) ^ 2 * (F.derivative ^ 2 - F * F.derivative.derivative) +
      (C c + C c * X ^ 2 - C (2 * a) * X - C (b ^ 2)) * F ^ 2 =
      intervalLinearFactor c a F ^ 2 + C 2 * X * F * intervalLinearFactor c a F := by
    simp only [intervalQuadraticFactor, intervalLinearFactor, intervalOperator_apply,
      derivative_sub, derivative_mul, derivative_X_pow_succ, Nat.cast_one,
      map_add, map_one, pow_one, derivative_one, sub_zero, derivative_C, zero_mul, derivative_X,
      mul_one, zero_add, map_pow, map_mul, C_ofNat]
    ring
  have hGa : (intervalLinearFactor c a F).eval s = (u - a) * F.eval s := by
    rw [intervalLinearFactor_eval] at hG ⊢
    nlinarith
  have he := congrArg (fun p : ℝ[X] => p.eval s) hid
  simp only [eval_add, eval_mul, eval_sub, eval_pow, eval_C, eval_X, eval_one,
    hGa] at he
  nlinarith [he]

/-- The elliptic spectral region suffices at every input degree, including zero. -/
theorem intervalQuadraticFactor_eval_mul_neg (c a b s : ℝ) (F : ℝ[X])
    (hc : 0 < c) (hF : F.Splits) (hFs : F.eval s ≠ 0)
    (hpair : a ^ 2 + c * b ^ 2 < c ^ 2)
    (hG : (intervalLinearFactor c a F).eval s = 0) :
    F.eval s * (intervalQuadraticFactor c a b F).eval s < 0 := by
  have hg : 0 < c + c * s ^ 2 - 2 * a * s - b ^ 2 := by
    nlinarith [sq_nonneg (c * s - a)]
  rw [intervalQuadraticFactor_eval_identity c a b a s F hG, sub_self, zero_pow (by decide),
    zero_add]
  have hl := mul_nonneg (sq_nonneg (1 - s ^ 2)) (laguerre_form_nonneg hF s)
  have hp := mul_pos hg (sq_pos_of_ne_zero hFs)
  linarith

/-- A quadratic insertion is interval-simple whenever its values have the old
polynomial's opposite sign at the intermediate roots. -/
theorem intervalQuadraticFactor_roots_of_eval_mul_neg (c a b u : ℝ) (F : ℝ[X])
    (hc : 0 < c) (hF : F.Splits) (hF0 : F ≠ 0) (hnd : F.roots.Nodup)
    (hi : ∀ r ∈ F.roots, -1 < r ∧ r < 1) (hu : -c < u ∧ u < c)
    (hends : 0 < (c + a) ^ 2 + b ^ 2 ∧ 0 < (c - a) ^ 2 + b ^ 2)
    (hneg : ∀ s, -1 < s ∧ s < 1 → F.eval s ≠ 0 →
      (intervalLinearFactor c u F).eval s = 0 →
      F.eval s * (intervalQuadraticFactor c a b F).eval s < 0) :
    (intervalQuadraticFactor c a b F).Splits ∧
      (intervalQuadraticFactor c a b F).roots.Nodup ∧
      ∀ r ∈ (intervalQuadraticFactor c a b F).roots, -1 < r ∧ r < 1 := by
  obtain ⟨hG, hGnd, hGi⟩ := intervalLinearFactor_roots c u F hc hF hF0 hnd hi hu
  have hG0 := intervalLinearFactor_ne_zero c u F hc hF0
  apply splits_nodup_interval_of_root_derivative_signs hG hG0 hGnd hGi
  · rw [intervalQuadraticFactor_natDegree c a b F hc hF0,
      intervalLinearFactor_natDegree c u F hc hF0]
  · intro s hs
    have hg := (mem_roots hG0).mp hs
    have hf := intervalLinearFactor_eval_base_ne_zero c u s F hF0 hnd hi hg
    have hprod := mul_neg_of_neg_of_pos (hneg s (hGi s hs) hf hg)
      (intervalLinearFactor_eval_derivative_mul_pos c u s F hc hF hi hf hg)
    have hsq := sq_pos_of_ne_zero hf
    nlinarith [hprod]
  · have he := (eval_endpoints_ne_zero_of_roots_mem_Ioo hF0 hi).1
    have hp : 0 < c + u := by linarith [hu.1]
    have hpp := hends.1
    have hh := mul_pos (mul_pos hp hpp) (sq_pos_of_ne_zero he)
    simp only [intervalQuadraticFactor, eval_add, eval_mul, eval_C,
      intervalLinearFactor_eval]
    norm_num only
    nlinarith [hh]
  · have he := (eval_endpoints_ne_zero_of_roots_mem_Ioo hF0 hi).2
    have hp : 0 < c - u := by linarith [hu.2]
    have hpp := hends.2
    have hh := mul_pos (mul_pos hp hpp) (sq_pos_of_ne_zero he)
    simp only [intervalQuadraticFactor, eval_add, eval_mul, eval_C,
      intervalLinearFactor_eval]
    norm_num only
    nlinarith [hh]

/-- Conjugate pairs in the elliptic spectral region preserve simple interval roots. -/
theorem intervalQuadraticFactor_roots (c a b : ℝ) (F : ℝ[X]) (hc : 0 < c)
    (hF : F.Splits) (hF0 : F ≠ 0) (hnd : F.roots.Nodup)
    (hi : ∀ r ∈ F.roots, -1 < r ∧ r < 1)
    (hpair : a ^ 2 + c * b ^ 2 < c ^ 2) :
    (intervalQuadraticFactor c a b F).Splits ∧
      (intervalQuadraticFactor c a b F).roots.Nodup ∧
      ∀ r ∈ (intervalQuadraticFactor c a b F).roots, -1 < r ∧ r < 1 := by
  have ha : -c < a ∧ a < c := by
    constructor <;> nlinarith [mul_nonneg hc.le (sq_nonneg b)]
  apply intervalQuadraticFactor_roots_of_eval_mul_neg c a b a F hc hF hF0 hnd hi ha
  · constructor <;> nlinarith [sq_pos_of_pos (show 0 < c + a by linarith [ha.1]),
      sq_pos_of_pos (show 0 < c - a by linarith [ha.2]), sq_nonneg b]
  · intro s _ hs hg
    exact intervalQuadraticFactor_eval_mul_neg c a b s F hc hF hs hpair hg

end RealRooted.IntervalDifferential

open Polynomial

namespace RealRooted.IntervalDifferential

/-- Root distances in the unit interval give a degree-weighted lower bound
for the Laguerre expression. -/
theorem interval_laguerre_lower_bound (F : ℝ[X]) (hF : F.Splits)
    (hi : ∀ r ∈ F.roots, -1 < r ∧ r < 1) (s : ℝ) (hFs : F.eval s ≠ 0) :
    (F.natDegree : ℝ) * (1 - |s|) ^ 2 * F.eval s ^ 2 ≤
      (1 - s ^ 2) ^ 2 *
        (F.derivative.eval s ^ 2 - F.eval s * F.derivative.derivative.eval s) := by
  have hb (r : ℝ) (hr : r ∈ F.roots) :
      (1 - |s|) ^ 2 ≤ (1 - s ^ 2) ^ 2 * (s - r)⁻¹ ^ 2 := by
    have hd : s - r ≠ 0 := by
      intro hz
      have hF0 : F ≠ 0 := by intro hz; simp [hz] at hFs
      exact hFs (sub_eq_zero.mp hz ▸ (mem_roots hF0).mp hr)
    have ha : |s - r| ≤ 1 + |s| := by
      have hrabs : |r| < 1 := abs_lt.mpr (hi r hr)
      linarith [abs_sub s r]
    have hsq : (s - r) ^ 2 ≤ (1 + |s|) ^ 2 := by
      nlinarith [sq_abs (s - r), abs_nonneg (s - r), abs_nonneg s]
    have hmul := mul_le_mul_of_nonneg_left hsq (sq_nonneg (1 - |s|))
    have heq : (1 - |s|) ^ 2 * (1 + |s|) ^ 2 = (1 - s ^ 2) ^ 2 := by
      calc
        _ = (1 - |s| ^ 2) ^ 2 := by ring
        _ = _ := by rw [sq_abs]
    have hb := (le_div_iff₀ (sq_pos_of_ne_zero hd)).mpr (hmul.trans_eq heq)
    simpa only [div_eq_mul_inv, inv_pow] using hb
  have hs := Multiset.sum_map_le_sum_map (s := F.roots)
    (fun _ : ℝ => (1 - |s|) ^ 2)
    (fun r : ℝ => (1 - s ^ 2) ^ 2 * (s - r)⁻¹ ^ 2) hb
  simp only [Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul,
    Multiset.sum_map_mul_left] at hs
  rw [← hF.natDegree_eq_card_roots] at hs
  have he := laguerre_eval_eq_eval_sq_mul_rootSumSq_of_splits hF hFs
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_right hs (sq_nonneg (F.eval s))]

/-- The uniform threshold obtained by testing at a shifted linear insertion. -/
def intervalInsertionThreshold (c : ℝ) (d : ℕ) (u : ℝ) : ℝ :=
  d + c - ((d : ℝ) + |u|) ^ 2 / ((d : ℝ) + c)

/-- The root-distance bound and completion of the square give the shifted
quadratic sign criterion for every positive endpoint weight. -/
theorem intervalQuadraticFactor_shift_eval_mul_neg (c a b u s : ℝ) (F : ℝ[X])
    (hc : 0 < c) (hF : F.Splits) (hi : ∀ r ∈ F.roots, -1 < r ∧ r < 1)
    (hFs : F.eval s ≠ 0)
    (hpair : (a - u) ^ 2 + b ^ 2 < intervalInsertionThreshold c F.natDegree u)
    (hG : (intervalLinearFactor c u F).eval s = 0) :
    F.eval s * (intervalQuadraticFactor c a b F).eval s < 0 := by
  have hl := interval_laguerre_lower_bound F hF hi s hFs
  have hd : 0 < (F.natDegree : ℝ) + c := by positivity
  have he := intervalQuadraticFactor_eval_identity c a b u s F hG
  have ha : u * s ≤ |u| * |s| := by simpa only [abs_mul] using le_abs_self (u * s)
  have ham := mul_le_mul_of_nonneg_left ha hd.le
  have hdiv := div_mul_cancel₀ (((F.natDegree : ℝ) + |u|) ^ 2) hd.ne'
  unfold intervalInsertionThreshold at hpair
  have hgap := mul_pos hd (sub_pos.mpr hpair)
  have hcoef : 0 < (F.natDegree : ℝ) * (1 - |s|) ^ 2 +
      c + c * s ^ 2 - 2 * u * s - ((a - u) ^ 2 + b ^ 2) := by
    have hsq := sq_nonneg (((F.natDegree : ℝ) + c) * |s| - (F.natDegree + |u|))
    rw [← sq_abs s]
    by_contra hn
    have hmul := mul_nonpos_of_nonneg_of_nonpos hd.le (le_of_not_gt hn)
    nlinarith [hdiv, hgap, ham]
  have hp := mul_pos hcoef (sq_pos_of_ne_zero hFs)
  nlinarith [he, hl]

/-- Shifted linear test points give a reusable quadratic insertion criterion. -/
theorem intervalQuadraticFactor_shift_roots (c a b u : ℝ) (F : ℝ[X]) (hc : 0 < c)
    (hF : F.Splits) (hF0 : F ≠ 0) (hnd : F.roots.Nodup)
    (hi : ∀ r ∈ F.roots, -1 < r ∧ r < 1) (hu : |u| < c) (hb : b ≠ 0)
    (hpair : (a - u) ^ 2 + b ^ 2 < intervalInsertionThreshold c F.natDegree u) :
    (intervalQuadraticFactor c a b F).Splits ∧
      (intervalQuadraticFactor c a b F).roots.Nodup ∧
      ∀ r ∈ (intervalQuadraticFactor c a b F).roots, -1 < r ∧ r < 1 := by
  apply intervalQuadraticFactor_roots_of_eval_mul_neg c a b u F hc hF hF0 hnd hi
    (abs_lt.mp hu)
  · constructor <;> nlinarith [sq_pos_of_ne_zero hb, sq_nonneg (c + a), sq_nonneg (c - a)]
  · intro s _ hs hg
    exact intervalQuadraticFactor_shift_eval_mul_neg c a b u s F hc hF hi hs hpair hg

/-- Every pair in the squared-radius `25/4` disk is admissible after degree six. -/
theorem intervalInsertionThreshold_six {d : ℕ} (hd : 6 ≤ d) :
    (25 / 4 : ℝ) < intervalInsertionThreshold 4 d 0 := by
  have hdr : (6 : ℝ) ≤ d := by exact_mod_cast hd
  have hp : 0 < (d : ℝ) + 4 := by positivity
  unfold intervalInsertionThreshold
  rw [abs_zero, add_zero]
  have he := div_mul_cancel₀ ((d : ℝ) ^ 2) hp.ne'
  by_contra hn
  have hh := mul_le_mul_of_nonneg_right (le_of_not_gt hn) hp.le
  nlinarith

/-- The six rational starting inequalities from the revised structural note. -/
theorem intervalInsertionThreshold_small {d : ℕ} (hd : d < 6) (a b : ℝ)
    (hdisk : a ^ 2 + b ^ 2 ≤ 25 / 4)
    (hmoment : -(2 + (25 / 16 : ℝ) * d) / (15 - d) ≤ (a ^ 2 - b ^ 2) / 4) :
    ∃ u : ℝ, |u| < 4 ∧
      (a - u) ^ 2 + b ^ 2 < intervalInsertionThreshold 4 d u := by
  let v : ℝ := (6 - (d : ℝ)) / 4
  have hdR : (d : ℝ) < 6 := by exact_mod_cast hd
  have hv : 0 < v := by dsimp [v]; linarith
  have hv4 : v < 4 := by dsimp [v]; have h := Nat.cast_nonneg (α := ℝ) d; linarith
  have hmain : (|a| - v) ^ 2 + b ^ 2 < intervalInsertionThreshold 4 d v := by
    by_contra hnot
    have hfail := le_of_not_gt hnot
    have hA : |a| ≤ (25 / 4 + v ^ 2 - intervalInsertionThreshold 4 d v) / (2 * v) := by
      apply (le_div_iff₀ (by positivity : 0 < 2 * v)).mpr
      nlinarith [sq_abs a]
    have hconvex := mul_nonneg (abs_nonneg a) (sub_nonneg.mpr hA)
    dsimp only [v] at hA hconvex hfail
    interval_cases d <;> norm_num only [v, intervalInsertionThreshold] at * <;>
      nlinarith [sq_abs a]
  by_cases ha : 0 ≤ a
  · refine ⟨v, by simpa only [abs_of_pos hv] using hv4, ?_⟩
    simpa only [abs_of_nonneg ha] using hmain
  · refine ⟨-v, ?_, ?_⟩
    · simpa only [abs_neg, abs_of_pos hv] using hv4
    · have hab : |a| = -a := abs_of_neg (lt_of_not_ge ha)
      have hth : intervalInsertionThreshold 4 d (-v) = intervalInsertionThreshold 4 d v := by
        simp only [intervalInsertionThreshold, abs_neg]
      rw [hth]
      rw [hab] at hmain
      nlinarith

end RealRooted.IntervalDifferential
