/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Basic.Real.Basic

import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic
import RealRooted.Mathlib.Algebra.Polynomial.DifferentialEquation.SecondOrder

/-!
# Polynomial Sonin identities for second-order differential equations

Let `a b c y g h` be polynomials and put `R = a y'' + b y' + c y`.  We prove two
division-free identities, valid over any commutative ring, which express the derivative of a
Sonin-type envelope divided by a rational weight `g / h` in terms of `R` and a weight defect.
-/

@[expose] public section

namespace Polynomial

namespace Sonin

variable {R : Type*} [CommRing R]

/-- The residual `a y'' + b y' + c y` of the second-order operator. -/
noncomputable def residual (a b c y : R[X]) : R[X] :=
  a * y.derivative.derivative + b * y.derivative + c * y

/-- The discriminant `4ac - 2ab' + 2a'b - b²` of the normal form of the operator. -/
noncomputable def disc (a b c : R[X]) : R[X] :=
  4 * a * c - 2 * a * b.derivative + 2 * a.derivative * b - b ^ 2

/-- The first-order form `2ay' + by`. -/
noncomputable def lin (a b y : R[X]) : R[X] :=
  2 * a * y.derivative + b * y

/-- The Sonin envelope numerator `Δ y² + W²`. -/
noncomputable def envelope (a b c y : R[X]) : R[X] :=
  disc a b c * y ^ 2 + lin a b y ^ 2

/-- The sign polynomial `2a'Δ - aΔ'` of the envelope. -/
noncomputable def signPoly (a b c : R[X]) : R[X] :=
  2 * a.derivative * disc a b c - a * (disc a b c).derivative

/-- The cross product `y W`. -/
noncomputable def cross (a b y : R[X]) : R[X] :=
  y * lin a b y

/-- The weight defect `a (g'h - gh') - b g h` of the rational weight `g / h`. -/
noncomputable def weightDefect (a b g h : R[X]) : R[X] :=
  a * (g.derivative * h - g * h.derivative) - b * g * h

variable (a b c y g h : R[X])

/-- Sonin identity with the envelope `Δ y² + W²`: the derivative of `g F / (h Δ)` has numerator
`g h W² P / a`, up to the residual and the weight defect.  No hypothesis on `a` is needed. -/
theorem envelope_identity :
    a * ((g * envelope a b c y).derivative * h * disc a b c -
        g * envelope a b c y * (h * disc a b c).derivative) -
      g * h * lin a b y ^ 2 * signPoly a b c =
    disc a b c * envelope a b c y * weightDefect a b g h +
      4 * a * g * h * disc a b c * lin a b y * residual a b c y := by
  simp only [envelope, disc, lin, signPoly, weightDefect, residual, sq, derivative_mul,
    derivative_add, derivative_sub, derivative_ofNat]
  ring

/-- Sonin identity with the cross term `K = y W`. -/
theorem cross_identity :
    2 * a * ((g * cross a b y).derivative * h - g * cross a b y * h.derivative) -
      g * h * (lin a b y ^ 2 - disc a b c * y ^ 2) =
    2 * cross a b y * weightDefect a (b - a.derivative) g h +
      4 * a * g * h * y * residual a b c y := by
  simp only [cross, disc, lin, weightDefect, residual, sq, derivative_mul, derivative_add,
    derivative_ofNat]
  ring

/-- The envelope identity when the equation `R = 0` and the weight identity hold. -/
theorem envelope_identity_of_ode (hR : residual a b c y = 0) (hT : weightDefect a b g h = 0) :
    a * ((g * envelope a b c y).derivative * h * disc a b c -
        g * envelope a b c y * (h * disc a b c).derivative) =
      g * h * lin a b y ^ 2 * signPoly a b c := by
  have := envelope_identity a b c y g h
  rw [hR, hT] at this
  grind

/-- The cross identity when the equation `R = 0` and the weight identity hold. -/
theorem cross_identity_of_ode (hR : residual a b c y = 0)
    (hT : weightDefect a (b - a.derivative) g h = 0) :
    2 * a * ((g * cross a b y).derivative * h - g * cross a b y * h.derivative) =
      g * h * (lin a b y ^ 2 - disc a b c * y ^ 2) := by
  have := cross_identity a b c y g h
  rw [hR, hT] at this
  grind

variable {j : R[X]}

/-- Division-free envelope identity: cancel the nonzero polynomial `a` when `g h = a j`. -/
theorem envelope_derivative_eq_of_ode [IsDomain R] (ha : a ≠ 0) (hgh : g * h = a * j)
    (hR : residual a b c y = 0) (hT : weightDefect a b g h = 0) :
    (g * envelope a b c y).derivative * h * disc a b c -
        g * envelope a b c y * (h * disc a b c).derivative =
      j * lin a b y ^ 2 * signPoly a b c := by
  refine mul_left_cancel₀ ha ?_
  rw [envelope_identity_of_ode a b c y g h hR hT, hgh]
  ring

/-- Division-free cross identity: cancel `a` when `g h = a j`. -/
theorem cross_derivative_eq_of_ode [IsDomain R] (ha : a ≠ 0) (hgh : g * h = a * j)
    (hR : residual a b c y = 0) (hT : weightDefect a (b - a.derivative) g h = 0) :
    2 * ((g * cross a b y).derivative * h - g * cross a b y * h.derivative) =
      j * (lin a b y ^ 2 - disc a b c * y ^ 2) := by
  refine mul_left_cancel₀ ha ?_
  linear_combination cross_identity_of_ode a b c y g h hR hT +
    (lin a b y ^ 2 - disc a b c * y ^ 2) * hgh

end Sonin

section Real

/-- Quotient rule for the real functions defined by two polynomials. -/
theorem hasDerivAt_eval_div (p q : ℝ[X]) {x : ℝ} (hq : q.eval x ≠ 0) :
    HasDerivAt (fun t => p.eval t / q.eval t)
      ((p.derivative.eval x * q.eval x - p.eval x * q.derivative.eval x) / q.eval x ^ 2) x :=
  (p.hasDerivAt x).div (q.hasDerivAt x) hq

namespace Sonin

variable (a b c y g h j : ℝ[X]) {x : ℝ}

/-- Real quotient statement of the Sonin envelope identity: the derivative of `g F / (h Δ)`. -/
theorem hasDerivAt_envelope_div (ha : a ≠ 0) (hgh : g * h = a * j)
    (hR : residual a b c y = 0) (hT : weightDefect a b g h = 0)
    (hx : (h * disc a b c).eval x ≠ 0) :
    HasDerivAt (fun t => (g * envelope a b c y).eval t / (h * disc a b c).eval t)
      ((j * lin a b y ^ 2 * signPoly a b c).eval x / ((h * disc a b c).eval x) ^ 2) x := by
  have key : eval x (g * envelope a b c y).derivative * eval x (h * disc a b c) -
      eval x (g * envelope a b c y) * eval x (h * disc a b c).derivative =
      eval x (j * lin a b y ^ 2 * signPoly a b c) := by
    have h4 := congrArg (eval x) (envelope_derivative_eq_of_ode a b c y g h ha hgh hR hT)
    simp only [eval_sub, eval_mul] at h4 ⊢
    linear_combination h4
  simpa only [key] using hasDerivAt_eval_div (g * envelope a b c y) (h * disc a b c) hx

/-- Real quotient statement of the cross identity: the derivative of `g K / h`. -/
theorem hasDerivAt_cross_div (ha : a ≠ 0) (hgh : g * h = a * j)
    (hR : residual a b c y = 0) (hT : weightDefect a (b - a.derivative) g h = 0)
    (hx : h.eval x ≠ 0) :
    HasDerivAt (fun t => (g * cross a b y).eval t / h.eval t)
      ((j * (lin a b y ^ 2 - disc a b c * y ^ 2)).eval x / (2 * h.eval x ^ 2)) x := by
  have key : eval x (g * cross a b y).derivative * eval x h -
      eval x (g * cross a b y) * eval x h.derivative =
      eval x (j * (lin a b y ^ 2 - disc a b c * y ^ 2)) / 2 := by
    have h4 := congrArg (eval x) (cross_derivative_eq_of_ode a b c y g h ha hgh hR hT)
    simp only [eval_sub, eval_mul, eval_ofNat] at h4 ⊢
    linear_combination h4 / 2
  have := hasDerivAt_eval_div (g * cross a b y) h hx
  rw [key] at this
  convert this using 1
  ring

open Filter Topology Set

/-- A function with nonnegative derivative on a convex set is monotone there. -/
private theorem monotoneOn_of_hasDerivAt {D : Set ℝ} (hD : Convex ℝ D) {E d : ℝ → ℝ}
    (hE : ∀ x ∈ D, HasDerivAt E (d x) x) (hd : ∀ x ∈ D, 0 ≤ d x) : MonotoneOn E D :=
  monotoneOn_of_deriv_nonneg hD (fun x hx => (hE x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hE x (interior_subset hx)).differentiableAt.differentiableWithinAt)
    (fun x hx => by rw [(hE x (interior_subset hx)).deriv]; exact hd x (interior_subset hx))

/-- A function vanishing at `r` with positive derivative there is negative on some left
neighbourhood. -/
private theorem not_eventually_nonneg_nhdsLT {E : ℝ → ℝ} {d r : ℝ} (hE : HasDerivAt E d r)
    (hd : 0 < d) (h0 : E r = 0) : ¬ ∀ᶠ t in 𝓝[<] r, 0 ≤ E t := by
  intro hev
  have hs : Tendsto (slope E r) (𝓝[<] r) (𝓝 d) :=
    (hasDerivAt_iff_tendsto_slope.1 hE).mono_left
      (nhdsWithin_mono r (fun t (ht : t < r) => ne_of_lt ht))
  have : d ≤ 0 := le_of_tendsto hs (by
    filter_upwards [hev, self_mem_nhdsWithin] with t ht ht'
    rw [slope_def_field, h0, sub_zero]
    exact div_nonpos_of_nonneg_of_nonpos ht (by linarith [mem_Iio.1 ht']))
  linarith

/-- A function vanishing at `r` with positive derivative there is positive on some right
neighbourhood. -/
private theorem not_eventually_nonpos_nhdsGT {E : ℝ → ℝ} {d r : ℝ} (hE : HasDerivAt E d r)
    (hd : 0 < d) (h0 : E r = 0) : ¬ ∀ᶠ t in 𝓝[>] r, E t ≤ 0 := by
  intro hev
  have hs : Tendsto (slope E r) (𝓝[>] r) (𝓝 d) :=
    (hasDerivAt_iff_tendsto_slope.1 hE).mono_left
      (nhdsWithin_mono r (fun t (ht : r < t) => ne_of_gt ht))
  have : d ≤ 0 := le_of_tendsto hs (by
    filter_upwards [hev, self_mem_nhdsWithin] with t ht ht'
    rw [slope_def_field, h0, sub_zero]
    exact div_nonpos_of_nonpos_of_nonneg ht (by linarith [mem_Ioi.1 ht']))
  linarith

/-- At a root `r` of a nonzero solution `y` with `a r ≠ 0`, the function `g K / h` vanishes and
has a positive derivative. -/
private theorem exists_pos_hasDerivAt_of_eval_eq_zero (hy : y ≠ 0) (hgh : g * h = a * j)
    (hR : residual a b c y = 0) (hT : weightDefect a (b - a.derivative) g h = 0) {r : ℝ}
    (hr : y.eval r = 0) (har : a.eval r ≠ 0) (hhr : h.eval r ≠ 0) (hjr : 0 < j.eval r) :
    ∃ d, 0 < d ∧ HasDerivAt (fun t => (g * cross a b y).eval t / h.eval t) d r := by
  have ha : a ≠ 0 := by
    rintro rfl
    simp at har
  have hy' : y.derivative.eval r ≠ 0 :=
    eval_derivative_ne_zero_of_second_order_ode hy hR hr har
  refine ⟨_, ?_, hasDerivAt_cross_div a b c y g h j ha hgh hR hT hhr⟩
  have hW : (lin a b y).eval r = 2 * a.eval r * y.derivative.eval r := by simp [lin, hr]
  have hsq : 0 < (2 * a.eval r * y.derivative.eval r) ^ 2 := by positivity
  rw [eval_mul, eval_sub, eval_mul, eval_pow, eval_pow, hr, hW, zero_pow two_ne_zero, mul_zero,
    sub_zero]
  positivity

variable {a b c y g h j}

/-- Under the sign hypotheses on a convex set `D`, the function `g K / h` is monotone on `D`:
its derivative is `j (W² - Δ y²) / (2 h²)`, which is nonnegative when `Δ ≤ 0` and `j > 0`. -/
private theorem monotoneOn_cross_div {D : Set ℝ} (hD : Convex ℝ D) (ha0 : a ≠ 0)
    (hgh : g * h = a * j) (hR : residual a b c y = 0)
    (hT : weightDefect a (b - a.derivative) g h = 0) (hh : ∀ x ∈ D, h.eval x ≠ 0)
    (hj : ∀ x ∈ D, 0 < j.eval x) (hΔ : ∀ x ∈ D, (disc a b c).eval x ≤ 0) :
    MonotoneOn (fun t => (g * cross a b y).eval t / h.eval t) D := by
  refine monotoneOn_of_hasDerivAt hD
    (fun x hx => hasDerivAt_cross_div a b c y g h j ha0 hgh hR hT (hh x hx)) fun x hx => ?_
  have h1 := mul_nonneg (neg_nonneg.2 (hΔ x hx)) (sq_nonneg (y.eval x))
  rw [eval_mul, eval_sub, eval_mul, eval_pow, eval_pow]
  exact div_nonneg (mul_nonneg (hj x hx).le
    (by nlinarith [sq_nonneg ((lin a b y).eval x)])) (by positivity)

/-- If `y` solves the second-order equation, the weight identities hold and `Δ ≤ 0`, `j > 0`,
`a ≠ 0`, `h ≠ 0` on `(-∞, L]` while `g K / h → 0` at `-∞`, then `y` has no root in `(-∞, L]`. -/
theorem eval_ne_zero_of_tendsto_atBot (hy : y ≠ 0) (hgh : g * h = a * j)
    (hR : residual a b c y = 0) (hT : weightDefect a (b - a.derivative) g h = 0) {L : ℝ}
    (ha : ∀ x ≤ L, a.eval x ≠ 0) (hh : ∀ x ≤ L, h.eval x ≠ 0) (hj : ∀ x ≤ L, 0 < j.eval x)
    (hΔ : ∀ x ≤ L, (disc a b c).eval x ≤ 0)
    (hlim : Tendsto (fun t => (g * cross a b y).eval t / h.eval t) atBot (𝓝 0)) :
    ∀ x ≤ L, y.eval x ≠ 0 := by
  intro r hrL hr
  have ha0 : a ≠ 0 := by
    rintro rfl
    simpa using ha L le_rfl
  have hmono := monotoneOn_cross_div (D := Iic L) (convex_Iic L) ha0 hgh hR hT hh hj hΔ
  have hE0 : ∀ x ≤ L, 0 ≤ (g * cross a b y).eval x / h.eval x := fun x hx =>
    le_of_tendsto hlim (by
      filter_upwards [eventually_le_atBot x] with t ht
      exact hmono (ht.trans hx) hx ht)
  obtain ⟨d, hd, hdE⟩ := exists_pos_hasDerivAt_of_eval_eq_zero a b c y g h j hy hgh hR hT hr
    (ha r hrL) (hh r hrL) (hj r hrL)
  exact not_eventually_nonneg_nhdsLT hdE hd (by simp [cross, hr]) (by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hE0 t ((le_of_lt ht).trans hrL))

/-- Mirror image of `eval_ne_zero_of_tendsto_atBot` on the half-line `[L, ∞)`. -/
theorem eval_ne_zero_of_tendsto_atTop (hy : y ≠ 0) (hgh : g * h = a * j)
    (hR : residual a b c y = 0) (hT : weightDefect a (b - a.derivative) g h = 0) {L : ℝ}
    (ha : ∀ x ≥ L, a.eval x ≠ 0) (hh : ∀ x ≥ L, h.eval x ≠ 0) (hj : ∀ x ≥ L, 0 < j.eval x)
    (hΔ : ∀ x ≥ L, (disc a b c).eval x ≤ 0)
    (hlim : Tendsto (fun t => (g * cross a b y).eval t / h.eval t) atTop (𝓝 0)) :
    ∀ x ≥ L, y.eval x ≠ 0 := by
  intro r hrL hr
  have ha0 : a ≠ 0 := by
    rintro rfl
    simpa using ha L le_rfl
  have hmono := monotoneOn_cross_div (D := Ici L) (convex_Ici L) ha0 hgh hR hT hh hj hΔ
  have hE0 : ∀ x ≥ L, (g * cross a b y).eval x / h.eval x ≤ 0 := fun x hx =>
    ge_of_tendsto hlim (by
      filter_upwards [eventually_ge_atTop x] with t ht
      exact hmono hx (hx.trans ht) ht)
  obtain ⟨d, hd, hdE⟩ := exists_pos_hasDerivAt_of_eval_eq_zero a b c y g h j hy hgh hR hT hr
    (ha r hrL) (hh r hrL) (hj r hrL)
  exact not_eventually_nonpos_nhdsGT hdE hd (by simp [cross, hr]) (by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hE0 t (hrL.trans (le_of_lt ht)))

/-- Finite-interval variant: if `g K / h` is nonnegative at `L`, then `y` has no root in
`(L, U]` under the sign hypotheses on `[L, U]`. -/
theorem eval_ne_zero_of_mem_Ioc (hy : y ≠ 0) (hgh : g * h = a * j)
    (hR : residual a b c y = 0) (hT : weightDefect a (b - a.derivative) g h = 0) {L U : ℝ}
    (ha : ∀ x ∈ Icc L U, a.eval x ≠ 0) (hh : ∀ x ∈ Icc L U, h.eval x ≠ 0)
    (hj : ∀ x ∈ Icc L U, 0 < j.eval x) (hΔ : ∀ x ∈ Icc L U, (disc a b c).eval x ≤ 0)
    (hL : 0 ≤ (g * cross a b y).eval L / h.eval L) :
    ∀ x ∈ Ioc L U, y.eval x ≠ 0 := by
  intro r hr0 hr
  have hLU : L ≤ U := hr0.1.le.trans hr0.2
  have hmem : r ∈ Icc L U := ⟨hr0.1.le, hr0.2⟩
  have ha0 : a ≠ 0 := by
    rintro rfl
    simpa using ha L ⟨le_rfl, hLU⟩
  have hmono := monotoneOn_cross_div (D := Icc L U) (convex_Icc L U) ha0 hgh hR hT hh hj hΔ
  obtain ⟨d, hd, hdE⟩ := exists_pos_hasDerivAt_of_eval_eq_zero a b c y g h j hy hgh hR hT hr
    (ha r hmem) (hh r hmem) (hj r hmem)
  exact not_eventually_nonneg_nhdsLT hdE hd (by simp [cross, hr]) (by
    filter_upwards [Ioo_mem_nhdsLT hr0.1] with t ht
    exact hL.trans (hmono ⟨le_rfl, hLU⟩ ⟨ht.1.le, ht.2.le.trans hr0.2⟩ ht.1.le))

/-- Finite-interval variant: if `g K / h` is positive at `L`, then `y` has no root in `[L, U]`
under the sign hypotheses on `[L, U]`. -/
theorem eval_ne_zero_of_mem_Icc (hy : y ≠ 0) (hgh : g * h = a * j)
    (hR : residual a b c y = 0) (hT : weightDefect a (b - a.derivative) g h = 0) {L U : ℝ}
    (ha : ∀ x ∈ Icc L U, a.eval x ≠ 0) (hh : ∀ x ∈ Icc L U, h.eval x ≠ 0)
    (hj : ∀ x ∈ Icc L U, 0 < j.eval x) (hΔ : ∀ x ∈ Icc L U, (disc a b c).eval x ≤ 0)
    (hL : 0 < (g * cross a b y).eval L / h.eval L) :
    ∀ x ∈ Icc L U, y.eval x ≠ 0 := by
  intro r hr0 hr
  rcases hr0.1.eq_or_lt with rfl | hlt
  · simp [cross, hr] at hL
  · exact eval_ne_zero_of_mem_Ioc hy hgh hR hT ha hh hj hΔ hL.le r ⟨hlt, hr0.2⟩ hr

end Sonin

end Real

end Polynomial
