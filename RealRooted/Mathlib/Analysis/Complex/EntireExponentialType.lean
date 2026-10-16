/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/

module

public import Mathlib.Analysis.Complex.BorelCaratheodory
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Complex.Liouville

/-!
# Entire functions of exponential type

Classification of entire functions of at most exponential type without zeros, via the
Borel-Carathéodory inequality and Cauchy estimates for the second derivative. If the real part of
an entire function `g` grows at most linearly (or like `(1 + ‖z‖) ^ (3 / 2)`), then `g` is affine.
A zero-free entire function has an entire logarithm, so a zero-free entire function of at most
exponential type is the exponential of an affine function.

## Main statements

* `Differentiable.exists_affine_of_re_le`: if `(g z).re ≤ C * (1 + ‖z‖)` for all `z`, then
  `g z = a * z + b` for some `a b : ℂ`.
* `Differentiable.exists_affine_of_re_le_rpow`: the same under the bound
  `C * (1 + ‖z‖) ^ (3 / 2)`.
* `Differentiable.exists_log_of_ne_zero`: a zero-free entire `f` is `Complex.exp ∘ g` for an
  entire `g`.
* `Differentiable.exists_eq_exp_affine_of_norm_le_exp`: a zero-free entire `f` with
  `‖f z‖ ≤ Real.exp (C * (1 + ‖z‖))` satisfies `f z = Complex.exp (a * z + b)`.
* `Differentiable.exists_eq_exp_real_affine_of_norm_le_exp`: if moreover `f` is real on the real
  axis and `0 < (f 0).re`, then `a` and `b` can be taken real.
-/

public noncomputable section

namespace Complex

private theorem differentiable_deriv {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    Differentiable ℂ (deriv g) := fun z =>
  ((hg.analyticAt z).deriv).differentiableAt

private theorem norm_le_of_re_le {g : ℂ → ℂ} (hg : Differentiable ℂ g) {C : ℝ}
    (h : ∀ z, (g z).re ≤ C * (1 + ‖z‖)) {ρ : ℝ} (hρ : 0 < ρ) {z : ℂ}
    (hz : ‖z‖ ≤ ρ) :
    ‖g z‖ ≤ 2 * (|C| * (1 + 2 * ρ) + 1) + 3 * ‖g 0‖ := by
  set M := |C| * (1 + 2 * ρ) + 1
  have hM : 0 < M := by positivity
  have hzb : z ∈ Metric.ball (0 : ℂ) (2 * ρ) := by
    rw [mem_ball_zero_iff]
    linarith
  have key := Complex.borelCaratheodory (f := g) (M := M) (R := 2 * ρ) hM
    hg.differentiableOn ?_ (by linarith) hzb
  · have hd : 0 < 2 * ρ - ‖z‖ := by linarith
    have h1 : 2 * M * ‖z‖ / (2 * ρ - ‖z‖) ≤ 2 * M := by
      rw [div_le_iff₀ hd]
      nlinarith [norm_nonneg z]
    have h2 : ‖g 0‖ * (2 * ρ + ‖z‖) / (2 * ρ - ‖z‖) ≤ 3 * ‖g 0‖ := by
      rw [div_le_iff₀ hd]
      nlinarith [norm_nonneg z, norm_nonneg (g 0)]
    linarith
  · intro w hw
    rw [mem_ball_zero_iff] at hw
    change (g w).re ≤ M
    calc
      (g w).re ≤ C * (1 + ‖w‖) := h w
      _ ≤ |C| * (1 + ‖w‖) := by
        apply mul_le_mul_of_nonneg_right (le_abs_self C)
        positivity
      _ ≤ |C| * (1 + 2 * ρ) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg C)
        linarith
      _ ≤ M := by linarith

private theorem eq_zero_of_mul_sq_le {x A B : ℝ} (hx : 0 ≤ x) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ R : ℝ, 1 ≤ R → x * R ^ 2 ≤ A + B * R) : x = 0 := by
  by_contra hne
  have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hne)
  set R := (A + B + 1) / x + 1
  have hR1 : 1 ≤ R := by
    have : 0 ≤ (A + B + 1) / x := by positivity
    linarith
  have hh := h R hR1
  have hxR : x * R = A + B + 1 + x := by
    simp only [R]
    field_simp
  have hR : x * R ^ 2 = (A + B + 1 + x) * R := by
    rw [← hxR]
    ring
  nlinarith

private theorem eq_zero_of_mul_sq_le_rpow {x A B : ℝ} (hx : 0 ≤ x) (hA : 0 ≤ A)
    (hB : 0 ≤ B)
    (h : ∀ R : ℝ, 1 ≤ R → x * R ^ 2 ≤ A + B * R ^ (3 / 2 : ℝ)) : x = 0 := by
  by_contra hne
  have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hne)
  set t := (A + B) / x + 1 with ht
  have ht1 : 1 ≤ t := by
    have : 0 ≤ (A + B) / x := by positivity
    linarith
  have ht0 : 0 ≤ t := by linarith
  have hh := h (t ^ 2) (one_le_pow₀ ht1)
  have hpow : (t ^ 2) ^ (3 / 2 : ℝ) = t ^ 3 := by
    rw [← Real.rpow_natCast t 2, ← Real.rpow_mul ht0, ← Real.rpow_natCast t 3]
    norm_num
  rw [hpow] at hh
  have hxt : x * t = A + B + x := by
    rw [ht]
    field_simp
  have h3 : 1 ≤ t ^ 3 := one_le_pow₀ ht1
  have hAt : A ≤ A * t ^ 3 := le_mul_of_one_le_right hA h3
  have h4 : x * t * t ^ 3 ≤ (A + B) * t ^ 3 := by nlinarith
  have h5 : x * t ≤ A + B := le_of_mul_le_mul_right h4 (by positivity)
  linarith

private theorem norm_le_of_re_le_rpow {g : ℂ → ℂ} (hg : Differentiable ℂ g) {C : ℝ}
    (h : ∀ z, (g z).re ≤ C * (1 + ‖z‖) ^ (3 / 2 : ℝ)) {ρ : ℝ} (hρ : 0 < ρ) {z : ℂ}
    (hz : ‖z‖ ≤ ρ) :
    ‖g z‖ ≤ 2 * (|C| * (1 + 2 * ρ) ^ (3 / 2 : ℝ) + 1) + 3 * ‖g 0‖ := by
  set M := |C| * (1 + 2 * ρ) ^ (3 / 2 : ℝ) + 1
  have hM : 0 < M := by positivity
  have hzb : z ∈ Metric.ball (0 : ℂ) (2 * ρ) := by
    rw [mem_ball_zero_iff]
    linarith
  have key := Complex.borelCaratheodory (f := g) (M := M) (R := 2 * ρ) hM
    hg.differentiableOn ?_ (by linarith) hzb
  · have hd : 0 < 2 * ρ - ‖z‖ := by linarith
    have h1 : 2 * M * ‖z‖ / (2 * ρ - ‖z‖) ≤ 2 * M := by
      rw [div_le_iff₀ hd]
      nlinarith [norm_nonneg z]
    have h2 : ‖g 0‖ * (2 * ρ + ‖z‖) / (2 * ρ - ‖z‖) ≤ 3 * ‖g 0‖ := by
      rw [div_le_iff₀ hd]
      nlinarith [norm_nonneg z, norm_nonneg (g 0)]
    linarith
  · intro w hw
    rw [mem_ball_zero_iff] at hw
    change (g w).re ≤ M
    calc
      (g w).re ≤ C * (1 + ‖w‖) ^ (3 / 2 : ℝ) := h w
      _ ≤ |C| * (1 + ‖w‖) ^ (3 / 2 : ℝ) := by
        apply mul_le_mul_of_nonneg_right (le_abs_self C)
        positivity
      _ ≤ |C| * (1 + 2 * ρ) ^ (3 / 2 : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg C)
        apply Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
      _ ≤ M := by linarith

end Complex

namespace Differentiable

open Complex

/-- An entire complex function whose real part has at most linear growth is affine. -/
theorem exists_affine_of_re_le {g : ℂ → ℂ} (hg : Differentiable ℂ g) {C : ℝ}
    (h : ∀ z, (g z).re ≤ C * (1 + ‖z‖)) : ∃ a b : ℂ, ∀ z, g z = a * z + b := by
  have hd1 := differentiable_deriv hg
  have h2 : ∀ c, _root_.deriv (_root_.deriv g) c = 0 := by
    intro c
    have hdd : ∀ R : ℝ, 1 ≤ R → ‖_root_.deriv (_root_.deriv g) c‖ * R ^ 2 ≤
        2 * (2 * (|C| * (1 + 2 * ‖c‖) + 1) + 3 * ‖g 0‖) + (8 * |C|) * R := by
      intro R hR
      have hR0 : 0 < R := by linarith
      have hbound := norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (c := c) (f := g) 2 hR0
        hg.diffContOnCl (C := 2 * (|C| * (1 + 2 * (‖c‖ + R)) + 1) + 3 * ‖g 0‖) (by
          intro z hz
          apply norm_le_of_re_le hg h (by positivity)
          rw [mem_sphere_iff_norm] at hz
          calc
            ‖z‖ = ‖(z - c) + c‖ := by ring_nf
            _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
            _ = ‖c‖ + R := by rw [hz]; ring)
      rw [iteratedDeriv_succ, iteratedDeriv_one] at hbound
      rw [le_div_iff₀ (by positivity)] at hbound
      simp at hbound
      nlinarith [abs_nonneg C]
    exact norm_eq_zero.mp
      (eq_zero_of_mul_sq_le (norm_nonneg _) (by positivity) (by positivity) hdd)
  set a := _root_.deriv g 0
  have ha : ∀ z, _root_.deriv g z = a := fun z => is_const_of_deriv_eq_zero hd1 h2 z 0
  have hk : Differentiable ℂ (fun z => g z - a * z) := hg.sub (by fun_prop)
  have hk' : ∀ z, _root_.deriv (fun z => g z - a * z) z = 0 := by
    intro z
    have hderiv : HasDerivAt (fun z => g z - a * z) (_root_.deriv g z - a * 1) z :=
      (hg z).hasDerivAt.sub ((hasDerivAt_id z).const_mul a)
    rw [hderiv.deriv, ha]
    ring
  refine ⟨a, g 0, fun z => ?_⟩
  have hconst := is_const_of_deriv_eq_zero hk hk' z 0
  simp at hconst
  linear_combination hconst

/-- An entire complex function whose real part grows at most like
`(1 + ‖z‖) ^ (3 / 2)` is affine. -/
theorem exists_affine_of_re_le_rpow {g : ℂ → ℂ} (hg : Differentiable ℂ g) {C : ℝ}
    (h : ∀ z, (g z).re ≤ C * (1 + ‖z‖) ^ (3 / 2 : ℝ)) :
    ∃ a b : ℂ, ∀ z, g z = a * z + b := by
  have hd1 : Differentiable ℂ (_root_.deriv g) := fun z =>
    ((hg.analyticAt z).deriv).differentiableAt
  have h2 : ∀ c, _root_.deriv (_root_.deriv g) c = 0 := by
    intro c
    have hdd : ∀ R : ℝ, 1 ≤ R → ‖_root_.deriv (_root_.deriv g) c‖ * R ^ 2 ≤
        2 * (2 * 1 + 3 * ‖g 0‖) +
          (4 * |C| * (3 + 2 * ‖c‖) ^ (3 / 2 : ℝ)) * R ^ (3 / 2 : ℝ) := by
      intro R hR
      have hR0 : 0 < R := by linarith
      have hbound := norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
        (c := c) (f := g) 2 hR0 hg.diffContOnCl
        (C := 2 * (|C| * (1 + 2 * (‖c‖ + R)) ^ (3 / 2 : ℝ) + 1) + 3 * ‖g 0‖) (by
          intro z hz
          apply Complex.norm_le_of_re_le_rpow hg h (by positivity)
          rw [mem_sphere_iff_norm] at hz
          calc
            ‖z‖ = ‖(z - c) + c‖ := by ring_nf
            _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
            _ = ‖c‖ + R := by rw [hz]; ring)
      rw [iteratedDeriv_succ, iteratedDeriv_one] at hbound
      rw [le_div_iff₀ (by positivity)] at hbound
      have hp : (1 + 2 * (‖c‖ + R)) ^ (3 / 2 : ℝ) ≤
          (3 + 2 * ‖c‖) ^ (3 / 2 : ℝ) * R ^ (3 / 2 : ℝ) := by
        rw [← Real.mul_rpow (by positivity) hR0.le]
        apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
        nlinarith [norm_nonneg c]
      have hC : 0 ≤ |C| := abs_nonneg C
      simp only [Nat.factorial] at hbound
      norm_num at hbound
      nlinarith [mul_le_mul_of_nonneg_left hp hC]
    exact norm_eq_zero.mp
      (Complex.eq_zero_of_mul_sq_le_rpow (norm_nonneg _) (by positivity) (by positivity) hdd)
  set a := _root_.deriv g 0
  have ha : ∀ z, _root_.deriv g z = a := fun z =>
    is_const_of_deriv_eq_zero hd1 h2 z 0
  have hk : Differentiable ℂ (fun z => g z - a * z) := hg.sub (by fun_prop)
  have hk' : ∀ z, _root_.deriv (fun z => g z - a * z) z = 0 := by
    intro z
    have hderiv : HasDerivAt (fun z => g z - a * z) (_root_.deriv g z - a * 1) z :=
      (hg z).hasDerivAt.sub ((hasDerivAt_id z).const_mul a)
    rw [hderiv.deriv, ha]
    ring
  refine ⟨a, g 0, fun z => ?_⟩
  have hconst := is_const_of_deriv_eq_zero hk hk' z 0
  simp at hconst
  linear_combination hconst

/-- A zero-free entire complex function has an entire logarithm. -/
theorem exists_log_of_ne_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h0 : ∀ z, f z ≠ 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, Complex.exp (g z) = f z := by
  set q : ℂ → ℂ := fun z => _root_.deriv f z / f z
  have hq : Differentiable ℂ q := (differentiable_deriv hf).div hf h0
  set G : ℂ → ℂ := fun w => Complex.wedgeIntegral 0 w q
  have hG : ∀ z, HasDerivAt G (q z) z := by
    intro z
    have hz : z ∈ Metric.ball (0 : ℂ) (‖z‖ + 1) := by
      rw [mem_ball_zero_iff]
      linarith
    exact Complex.IsConservativeOn.hasDerivAt_wedgeIntegral hq.continuous.continuousOn hz
      hq.differentiableOn.isConservativeOn
  have hGd : Differentiable ℂ G := fun z => (hG z).differentiableAt
  set F : ℂ → ℂ := fun z => f z * Complex.exp (-G z)
  have hFd : ∀ z, HasDerivAt F (_root_.deriv f z * Complex.exp (-G z) +
      f z * (Complex.exp (-G z) * (-q z))) z := fun z =>
    (hf z).hasDerivAt.mul ((hG z).neg.cexp)
  have hF0 : ∀ z, _root_.deriv F z = 0 := by
    intro z
    rw [(hFd z).deriv]
    simp only [q]
    field_simp [h0 z]
    ring
  have hFc : ∀ z, F z = F 0 := fun z =>
    is_const_of_deriv_eq_zero (fun z => (hFd z).differentiableAt) hF0 z 0
  have hF0ne : F 0 ≠ 0 := mul_ne_zero (h0 0) (Complex.exp_ne_zero _)
  refine ⟨fun z => G z + Complex.log (F 0), hGd.add_const _, fun z => ?_⟩
  rw [Complex.exp_add, Complex.exp_log hF0ne, ← hFc z]
  simp only [F, Complex.exp_neg]
  field_simp [Complex.exp_ne_zero (G z)]

/-- A zero-free entire complex function of at most exponential type is the exponential of an
affine function. -/
theorem exists_eq_exp_affine_of_norm_le_exp {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h0 : ∀ z, f z ≠ 0) {C : ℝ} (h : ∀ z, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖))) :
    ∃ a b : ℂ, ∀ z, f z = Complex.exp (a * z + b) := by
  obtain ⟨g, hg, hgf⟩ := hf.exists_log_of_ne_zero h0
  have hre : ∀ z, (g z).re ≤ C * (1 + ‖z‖) := by
    intro z
    have hnorm := h z
    rw [← hgf z, Complex.norm_exp] at hnorm
    exact Real.exp_le_exp.mp hnorm
  obtain ⟨a, b, hab⟩ := hg.exists_affine_of_re_le hre
  exact ⟨a, b, fun z => by rw [← hgf z, hab z]⟩

/-- If a zero-free entire complex function of at most exponential type is real on the real axis
and positive at zero, then it is the exponential of an affine function with real coefficients. -/
theorem exists_eq_exp_real_affine_of_norm_le_exp {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h0 : ∀ z, f z ≠ 0) {C : ℝ} (h : ∀ z, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖)))
    (hreal : ∀ x : ℝ, (f x).im = 0) (hpos : 0 < (f 0).re) :
    ∃ a b : ℝ, ∀ z, f z = Complex.exp (a * z + b) := by
  obtain ⟨a, b, hab⟩ := hf.exists_eq_exp_affine_of_norm_le_exp h0 h
  have hsin : ∀ x : ℝ, Real.sin (x * a.im + b.im) = 0 := by
    intro x
    have him := hreal x
    rw [hab, Complex.exp_im] at him
    have hsin' := (mul_eq_zero.mp him).resolve_left (Real.exp_pos _).ne'
    simpa [mul_comm] using hsin'
  have haim : a.im = 0 := by
    by_contra hne
    have hsin' := hsin ((Real.pi / 2 - b.im) / a.im)
    rw [div_mul_cancel₀ _ hne, sub_add_cancel, Real.sin_pi_div_two] at hsin'
    norm_num at hsin'
  have hb0 := hsin 0
  simp only [zero_mul, zero_add] at hb0
  have hcos : 0 < Real.cos b.im := by
    have hpos' := hpos
    rw [hab, Complex.exp_re] at hpos'
    have hcos' := (pos_iff_pos_of_mul_pos hpos').mp (Real.exp_pos _)
    simpa only [mul_zero, zero_add] using hcos'
  have hcos1 : Real.cos b.im = 1 := by
    have htrig := Real.sin_sq_add_cos_sq b.im
    rw [hb0] at htrig
    nlinarith
  refine ⟨a.re, b.re, fun z => ?_⟩
  rw [hab z]
  have ha : a = (a.re : ℂ) := Complex.ext (by simp) (by simp [haim])
  have hb : Complex.exp b = Complex.exp (b.re : ℂ) := by
    conv_lhs => rw [← Complex.re_add_im b]
    rw [Complex.exp_add, Complex.exp_mul_I]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, hcos1, hb0]
    simp
  rw [Complex.exp_add, Complex.exp_add, hb, ← ha]

end Differentiable
