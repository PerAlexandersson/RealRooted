module

public import Mathlib.Algebra.Polynomial.UnitTrinomial
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Algebraic restrictions on roots of trinomials

We use Mathlib's `Polynomial.trinomial`, with parameters `0, ℓ, k, 1, b, a`, rather
than defining a second polynomial API. The multiple-root equations are the algebraic
part of Section 3 of the unpublished manuscript *Dominant roots on the signed trinomial
curve* (2026-10-29), linked in RealRooted issue #2153. They apply over any field of
characteristic zero. The smallest-modulus assertion needs additional root-counting
arguments and does not follow from these equations alone.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted.Trinomial

variable {K : Type*} [Field K] [CharZero K]

private theorem mul_eval_derivative_monomial (m : ℕ) (c r : K) :
    r * (C c * X ^ m).derivative.eval r = (m : K) * c * r ^ m := by
  cases m with
  | zero => simp
  | succ m =>
    simp only [derivative_C_mul, derivative_X_pow, eval_mul, eval_C, eval_pow, eval_X,
      Nat.add_sub_cancel]
    rw [pow_succ]
    ring

/-- Multiplying a trinomial's derivative by its argument removes the shifted powers. -/
theorem mul_eval_derivative_trinomial (ℓ k : ℕ) (a b r : K) :
    r * (trinomial 0 ℓ k 1 b a).derivative.eval r =
      (ℓ : K) * b * r ^ ℓ + (k : K) * a * r ^ k := by
  simp only [trinomial_def, derivative_add, eval_add, mul_add,
    mul_eval_derivative_monomial, Nat.cast_zero, zero_mul, zero_add]

/-- A multiple root fixes both nonconstant monomials of a trinomial. This includes
possible multiple outer roots and does not assume a smallest-modulus condition. -/
theorem powers_of_isRoot_derivative {ℓ k : ℕ} (hℓk : ℓ < k) {a b r : K}
    (hr : (trinomial 0 ℓ k 1 b a).IsRoot r)
    (hd : (trinomial 0 ℓ k 1 b a).derivative.IsRoot r) :
    a * r ^ k = (ℓ : K) / ((k : K) - ℓ) ∧
      b * r ^ ℓ = -(k : K) / ((k : K) - ℓ) := by
  have hdiff : (k : K) - ℓ ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hℓk.ne')
  have hzero : 1 + b * r ^ ℓ + a * r ^ k = 0 := by
    simpa [IsRoot.def, trinomial_def] using hr
  have hder : (ℓ : K) * b * r ^ ℓ + (k : K) * a * r ^ k = 0 := by
    rw [← mul_eval_derivative_trinomial]
    exact mul_eq_zero.mpr (Or.inr hd)
  constructor
  · apply (eq_div_iff hdiff).mpr
    linear_combination hder - (ℓ : K) * hzero
  · apply (eq_div_iff hdiff).mpr
    linear_combination (k : K) * hzero - hder

omit [CharZero K] in
/-- Two nonzero numbers with the same powers at coprime exponents coincide. -/
theorem eq_of_pow_eq_of_coprime {ℓ k : ℕ} (hcop : ℓ.Coprime k) {u v : K}
    (hu : u ≠ 0) (hv : v ≠ 0) (hℓ : u ^ ℓ = v ^ ℓ) (hk : u ^ k = v ^ k) :
    u = v := by
  let q : Kˣ := Units.mk0 u hu / Units.mk0 v hv
  have hqℓ : q ^ ℓ = 1 := by
    apply Units.val_injective
    simp [q, div_pow, hv, hℓ]
  have hqk : q ^ k = 1 := by
    apply Units.val_injective
    simp [q, div_pow, hv, hk]
  have hq : q = 1 := (pow_eq_one_iff_of_coprime hcop).mp ⟨hqℓ, hqk⟩
  have hval := congrArg Units.val hq
  have hdiv : u / v = 1 := by simpa [q] using hval
  exact (div_eq_one_iff_eq hv).mp hdiv

private theorem eq_or_conj_of_norm_eq_of_re_eq {u v : ℂ}
    (hnorm : ‖u‖ = ‖v‖) (hre : u.re = v.re) : u = v ∨ u = star v := by
  have him : u.im ^ 2 = v.im ^ 2 := by
    have h := Complex.sq_norm_sub_sq_re u
    rw [hnorm, hre] at h
    exact h.symm.trans (Complex.sq_norm_sub_sq_re v)
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp him with hi | hi
  · exact Or.inl (Complex.ext hre hi)
  · exact Or.inr (Complex.ext (by simpa using hre) (by simpa using hi))

private theorem root_ne_zero {ℓ k : ℕ} (hℓ : ℓ ≠ 0) (hk : k ≠ 0) {a b z : ℂ}
    (hz : (trinomial 0 ℓ k 1 b a).IsRoot z) : z ≠ 0 := by
  intro h
  simp [IsRoot.def, trinomial_def, h, hℓ, hk] at hz

private theorem pow_eq_of_isRoot_of_pow_eq {ℓ k : ℕ} {b u v : ℂ} (hb : b ≠ 0)
    (hu : (trinomial 0 ℓ k 1 b 1).IsRoot u)
    (hv : (trinomial 0 ℓ k 1 b 1).IsRoot v) (hpow : u ^ k = v ^ k) :
    u ^ ℓ = v ^ ℓ := by
  have hu' : 1 + b * u ^ ℓ + u ^ k = 0 := by
    simpa [IsRoot.def, trinomial_def] using hu
  have hv' : 1 + b * v ^ ℓ + v ^ k = 0 := by
    simpa [IsRoot.def, trinomial_def] using hv
  apply mul_left_cancel₀ hb
  rw [hpow] at hu'
  linear_combination hu' - hv'

/-- A real normalized trinomial at coprime positive lags has at most a conjugate pair of
distinct roots on each circle centered at zero. This is a root-set statement, so it
continues to apply when roots outside the smallest circle are multiple. -/
theorem eq_or_conj_of_isRoot_of_norm_eq {ℓ k : ℕ} (hℓ : ℓ ≠ 0) (hk : k ≠ 0)
    (hcop : ℓ.Coprime k) {b : ℝ} (hb : b ≠ 0) {u v : ℂ}
    (hu : (trinomial 0 ℓ k 1 (b : ℂ) 1).IsRoot u)
    (hv : (trinomial 0 ℓ k 1 (b : ℂ) 1).IsRoot v) (hnorm : ‖u‖ = ‖v‖) :
    u = v ∨ u = star v := by
  have heq (z : ℂ) (hz : (trinomial 0 ℓ k 1 (b : ℂ) 1).IsRoot z) :
      (b : ℂ) * z ^ ℓ = -(1 + z ^ k) := by
    have h : 1 + (b : ℂ) * z ^ ℓ + z ^ k = 0 := by
      simpa [IsRoot.def, trinomial_def] using hz
    linear_combination h
  have hnorm' : ‖1 + u ^ k‖ = ‖1 + v ^ k‖ := by
    have h : ‖(b : ℂ) * u ^ ℓ‖ = ‖(b : ℂ) * v ^ ℓ‖ := by
      simp only [Complex.norm_mul, Complex.norm_pow, hnorm]
    simpa only [heq u hu, heq v hv, norm_neg] using h
  have hnormk : ‖u ^ k‖ = ‖v ^ k‖ := by simp only [Complex.norm_pow, hnorm]
  have hre : (u ^ k).re = (v ^ k).re := by
    have h := congrArg (fun r : ℝ ↦ r ^ 2) hnorm'
    simp only [Complex.sq_norm, Complex.normSq_add, map_one, one_mul, Complex.conj_re] at h
    simp only [← Complex.sq_norm, hnormk] at h
    linarith
  have hb' : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb
  have hu0 := root_ne_zero hℓ hk hu
  have hv0 := root_ne_zero hℓ hk hv
  rcases eq_or_conj_of_norm_eq_of_re_eq hnormk hre with he | he
  · exact Or.inl (eq_of_pow_eq_of_coprime hcop hu0 hv0
      (pow_eq_of_isRoot_of_pow_eq hb' hu hv he) he)
  · have hvstar : (trinomial 0 ℓ k 1 (b : ℂ) 1).IsRoot (star v) := by
      have h := congrArg (starRingEnd ℂ) hv
      simpa [IsRoot.def, trinomial_def] using h
    have hpow : u ^ k = (star v) ^ k := by simpa only [star_pow] using he
    exact Or.inr (eq_of_pow_eq_of_coprime hcop hu0 (star_ne_zero.mpr hv0)
      (pow_eq_of_isRoot_of_pow_eq hb' hu hvstar hpow) hpow)

private theorem sq_mul_eval_second_derivative_monomial (m : ℕ) (c r : K) :
    r ^ 2 * (C c * X ^ m).derivative.derivative.eval r =
      (m : K) * ((m : K) - 1) * c * r ^ m := by
  cases m with
  | zero => simp
  | succ m =>
    cases m with
    | zero => simp
    | succ m =>
      simp only [derivative_X_pow, derivative_mul, derivative_C,
        zero_mul, zero_add, eval_mul, eval_C, eval_pow, eval_X, Nat.add_sub_cancel]
      simp only [pow_succ, Nat.cast_add, Nat.cast_one]
      ring

/-- At a multiple root of a trinomial, the weighted second derivative is `k * ℓ`.
In particular, a multiple root is exactly double when `0 < ℓ < k`. -/
theorem sq_mul_eval_second_derivative_of_isRoot {ℓ k : ℕ} {a b r : K}
    (hr : (trinomial 0 ℓ k 1 b a).IsRoot r)
    (hd : (trinomial 0 ℓ k 1 b a).derivative.IsRoot r) :
    r ^ 2 * (trinomial 0 ℓ k 1 b a).derivative.derivative.eval r = (k : K) * ℓ := by
  have hzero : 1 + b * r ^ ℓ + a * r ^ k = 0 := by
    simpa [IsRoot.def, trinomial_def] using hr
  have hder : (ℓ : K) * b * r ^ ℓ + (k : K) * a * r ^ k = 0 := by
    rw [← mul_eval_derivative_trinomial]
    exact mul_eq_zero.mpr (Or.inr hd)
  have hsecond : r ^ 2 * (trinomial 0 ℓ k 1 b a).derivative.derivative.eval r =
      (ℓ : K) * ((ℓ : K) - 1) * b * r ^ ℓ +
        (k : K) * ((k : K) - 1) * a * r ^ k := by
    simp only [trinomial_def, derivative_add, eval_add, mul_add,
      sq_mul_eval_second_derivative_monomial, Nat.cast_zero, zero_mul, zero_add]
  linear_combination hsecond + ((k : K) + ℓ - 1) * hder - (k : K) * ℓ * hzero

/-- All multiple roots of a characteristic-zero trinomial with positive, distinct lags
are exactly double. This is independent of any dominance hypothesis. -/
theorem rootMultiplicity_eq_two_of_isRoot_derivative {ℓ k : ℕ}
    (hℓ : ℓ ≠ 0) (hℓk : ℓ < k) {a b r : K}
    (hr : (trinomial 0 ℓ k 1 b a).IsRoot r)
    (hd : (trinomial 0 ℓ k 1 b a).derivative.IsRoot r) :
    (trinomial 0 ℓ k 1 b a).rootMultiplicity r = 2 := by
  have hp : trinomial 0 ℓ k (1 : K) b a ≠ 0 := by
    intro h
    have hc := trinomial_trailing_coeff' (u := (1 : K)) (v := b) (w := a)
      (by lia : 0 < ℓ) hℓk
    simp [h] at hc
  have hlow := (one_lt_rootMultiplicity_iff_isRoot hp).mpr ⟨hr, hd⟩
  have hsecond : (trinomial 0 ℓ k 1 b a).derivative.derivative.eval r ≠ 0 := by
    intro h
    have heq := sq_mul_eval_second_derivative_of_isRoot hr hd
    rw [h, mul_zero] at heq
    have hk : (k : K) ≠ 0 := by exact_mod_cast (show k ≠ 0 by lia)
    have hℓ' : (ℓ : K) ≠ 0 := by exact_mod_cast hℓ
    exact mul_ne_zero hk hℓ' heq.symm
  have hupp : ¬ 2 < (trinomial 0 ℓ k 1 b a).rootMultiplicity r := by
    intro h
    have hroot := isRoot_iterate_derivative_of_lt_rootMultiplicity h
    exact hsecond (by simpa [Function.iterate_succ_apply] using hroot)
  lia

/-- A multiple root of a real normalized trinomial with coprime lags is real. -/
theorem im_eq_zero_of_isRoot_derivative {ℓ k : ℕ} (hℓ : ℓ ≠ 0) (hℓk : ℓ < k)
    (hcop : ℓ.Coprime k) {b : ℝ} (hb : b ≠ 0) {z : ℂ}
    (hz : (trinomial 0 ℓ k 1 (b : ℂ) 1).IsRoot z)
    (hd : (trinomial 0 ℓ k 1 (b : ℂ) 1).derivative.IsRoot z) : z.im = 0 := by
  have hzstar : (trinomial 0 ℓ k 1 (b : ℂ) 1).IsRoot (star z) := by
    have h := congrArg (starRingEnd ℂ) hz
    simpa [IsRoot.def, trinomial_def] using h
  have hdstar : (trinomial 0 ℓ k 1 (b : ℂ) 1).derivative.IsRoot (star z) := by
    have h := congrArg (starRingEnd ℂ) hd
    simpa [IsRoot.def, trinomial_def, derivative_C_mul, derivative_X_pow] using h
  have h₁ := powers_of_isRoot_derivative hℓk hz hd
  have h₂ := powers_of_isRoot_derivative hℓk hzstar hdstar
  have hzk : z ^ k = (star z) ^ k := by simpa using h₁.1.trans h₂.1.symm
  have hzℓ : z ^ ℓ = (star z) ^ ℓ := by
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hb) (h₁.2.trans h₂.2.symm)
  have hz0 := root_ne_zero hℓ (by lia : k ≠ 0) hz
  have heq := eq_of_pow_eq_of_coprime hcop hz0 (star_ne_zero.mpr hz0) hzℓ hzk
  have him := congrArg Complex.im heq
  simp only [Complex.star_def, Complex.conj_im] at him
  linarith

/-- Nonreal roots of a real normalized trinomial at coprime positive lags are simple. -/
theorem rootMultiplicity_eq_one_of_im_ne_zero {ℓ k : ℕ} (hℓ : ℓ ≠ 0) (hℓk : ℓ < k)
    (hcop : ℓ.Coprime k) {b : ℝ} (hb : b ≠ 0) {z : ℂ}
    (hz : (trinomial 0 ℓ k 1 (b : ℂ) 1).IsRoot z) (him : z.im ≠ 0) :
    (trinomial 0 ℓ k 1 (b : ℂ) 1).rootMultiplicity z = 1 := by
  have hp : trinomial 0 ℓ k (1 : ℂ) (b : ℂ) 1 ≠ 0 := by
    intro h
    have hc := trinomial_trailing_coeff' (u := (1 : ℂ)) (v := (b : ℂ)) (w := 1)
      (by lia : 0 < ℓ) hℓk
    simp [h] at hc
  have hlo := (rootMultiplicity_pos hp).mpr hz
  have hhi : ¬ 1 < (trinomial 0 ℓ k 1 (b : ℂ) 1).rootMultiplicity z := by
    intro h
    have hd := ((one_lt_rootMultiplicity_iff_isRoot hp).mp h).2
    exact him (im_eq_zero_of_isRoot_derivative hℓ hℓk hcop hb hz hd)
  lia

/-- For a lag-one trinomial, every multiple denominator root occurs at the critical
invariant value. The assertion holds for arbitrary complex coefficients. -/
theorem invariant_eq_of_isRoot_derivative {k : ℕ} (hk : 2 ≤ k) {a b r : ℂ}
    (hr : (trinomial 0 1 k 1 b a).IsRoot r)
    (hd : (trinomial 0 1 k 1 b a).derivative.IsRoot r) :
    (-1 : ℂ) ^ k * b ^ k / a = (k : ℂ) ^ k / (k - 1 : ℕ) ^ (k - 1) := by
  have hp := powers_of_isRoot_derivative (by lia : 1 < k) hr hd
  simp only [Nat.cast_one, pow_one] at hp
  have hr0 := root_ne_zero (by decide : 1 ≠ 0) (by lia : k ≠ 0) hr
  have hkcast : ((k - 1 : ℕ) : ℂ) = (k : ℂ) - 1 := by
    rw [Nat.cast_sub (by lia : 1 ≤ k), Nat.cast_one]
  have hden : (k : ℂ) - 1 ≠ 0 := by
    rw [← hkcast]
    exact_mod_cast (show k - 1 ≠ 0 by lia)
  have ha : a = (1 : ℂ) / ((k : ℂ) - 1) / r ^ k :=
    (eq_div_iff (pow_ne_zero k hr0)).mpr hp.1
  have hb : b = (-(k : ℂ) / ((k : ℂ) - 1)) / r := (eq_div_iff hr0).mpr hp.2
  have hpow : ((k : ℂ) - 1) ^ k = ((k : ℂ) - 1) ^ (k - 1) * ((k : ℂ) - 1) := by
    rw [← pow_succ, Nat.sub_add_cancel (by lia : 1 ≤ k)]
  rw [ha, hb, hkcast]
  have hsign : (-1 : ℂ) ^ k * (-(k : ℂ)) ^ k = (k : ℂ) ^ k := by
    rw [← mul_pow, neg_one_mul, neg_neg]
  simp only [div_pow]
  calc
    _ = ((-1 : ℂ) ^ k * (-(k : ℂ)) ^ k) * ((k : ℂ) - 1) /
        ((k : ℂ) - 1) ^ k := by field_simp
    _ = (k : ℂ) ^ k / ((k : ℂ) - 1) ^ (k - 1) := by
      rw [hsign, hpow]
      field_simp

end RealRooted.Trinomial
