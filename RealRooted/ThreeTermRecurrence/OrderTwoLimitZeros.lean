/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
module

public import RealRooted.Mathlib.Analysis.Complex.Hurwitz

/-!
# Limits of zeros for order-two recurrences

The characteristic roots of an analytic order-two recurrence are analytic away from zeros of
the discriminant. The two-dominant theorem then supplies limits of zeros.
-/

public section

open Filter Topology Metric Polynomial

noncomputable section

namespace Complex

/-- A nonvanishing analytic discriminant has an analytic square-root branch on a ball.
This is the local branch construction for the order-two application of Sokal,
*Combinatorics, Probability and Computing* 13 (2004), Theorem 1.5(b). -/
theorem exists_ball_analytic_square_root {D : ℂ → ℂ} {z₀ : ℂ}
    (hD : AnalyticAt ℂ D z₀) (hD0 : D z₀ ≠ 0) :
    ∃ ρ > 0, ∃ d : ℂ → ℂ,
      (∀ z ∈ ball z₀ ρ, AnalyticAt ℂ d z) ∧
      (∀ z ∈ ball z₀ ρ, d z ^ 2 = D z) ∧ d z₀ ≠ 0 := by
  obtain ⟨ρ, hρ, hslit, han, hexp⟩ := exists_ball_analytic_log_ratio hD hD0
  let d₀ : ℂ := sqrt (D z₀)
  have hd₀sq : d₀ ^ 2 = D z₀ := by
    change (sqrt (D z₀)) ^ 2 = D z₀
    rw [sqrt_eq_exp hD0, ← exp_nat_mul]
    convert exp_log hD0 using 1
    ring_nf
  have hd₀ : d₀ ≠ 0 := by
    intro heq
    exact hD0 (by simpa [heq] using hd₀sq.symm)
  let d : ℂ → ℂ := fun z => d₀ * exp (log (D z / D z₀) / 2)
  refine ⟨ρ, hρ, d, ?_, ?_, ?_⟩
  · intro z hz
    exact analyticAt_const.mul (((han z hz).div_const).cexp')
  · intro z hz
    have hlog : (2 : ℂ) * (log (D z / D z₀) / 2) =
        log (D z / D z₀) := by ring
    calc
      d z ^ 2 = d₀ ^ 2 * exp (log (D z / D z₀) / 2) ^ 2 := by
        simp [d, mul_pow]
      _ = D z₀ * exp (log (D z / D z₀)) := by
        rw [hd₀sq, ← exp_nat_mul]
        simpa using congrArg (fun x : ℂ => D z₀ * exp x) hlog
      _ = D z := by
        rw [hexp z hz]
        exact mul_div_cancel₀ _ hD0
  · simp [d, d₀, hd₀]

end Complex

private theorem two_step_closed_form (w : ℕ → ℂ) (A B u v : ℂ)
    (hrec : ∀ n, w (n + 2) = A * w (n + 1) + B * w n)
    (hsum : u + v = A) (hprod : u * v = -B) (huv : u ≠ v) :
    ∀ n, w n = (w 1 - v * w 0) / (u - v) * u ^ n +
      (u * w 0 - w 1) / (u - v) * v ^ n := by
  have hden : u - v ≠ 0 := sub_ne_zero.mpr huv
  have hrootu : u ^ 2 = A * u + B := by
    rw [← hsum, ← neg_eq_iff_eq_neg.mpr hprod]
    ring
  have hrootv : v ^ 2 = A * v + B := by
    rw [← hsum, ← neg_eq_iff_eq_neg.mpr hprod]
    ring
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
      simp only [pow_zero, mul_one]
      field_simp [hden]
      ring
  | one =>
      simp only [pow_one]
      field_simp [hden]
      ring
  | more n ih0 ih1 =>
      rw [hrec, ih0, ih1]
      simp only [pow_succ]
      linear_combination
        -((w 1 - v * w 0) / (u - v) * u ^ n) * hrootu -
        ((u * w 0 - w 1) / (u - v) * v ^ n) * hrootv

private theorem two_step_chebyshev_form (w : ℕ → ℂ) (A B t : ℂ)
    (ht : t ≠ 0) (htsq : t ^ 2 = -B)
    (h0 : w 0 = 1) (h1 : w 1 = A)
    (hrec : ∀ n, w (n + 2) = A * w (n + 1) + B * w n) :
    ∀ n, w n = t ^ n * (Polynomial.Chebyshev.U ℂ (n : ℤ)).eval (A / (2 * t)) := by
  let x := A / (2 * t)
  have h2t : (2 : ℂ) * t ≠ 0 := mul_ne_zero (by norm_num) ht
  have hAx : 2 * t * x = A := by
    dsimp [x]
    rw [mul_comm, div_mul_cancel₀ _ h2t]
  have hB : B = -(t ^ 2) := by linear_combination htsq
  intro n
  induction n using Nat.twoStepInduction with
  | zero => simp [h0, Polynomial.Chebyshev.U_zero]
  | one =>
      simp [h1, Polynomial.Chebyshev.U_one]
      linear_combination -hAx
  | more n ih0 ih1 =>
      rw [hrec, ih0, ih1]
      have hU := Polynomial.Chebyshev.U_add_two ℂ (n : ℤ)
      norm_cast at hU
      rw [hU]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
        Polynomial.eval_X]
      change A * (t ^ (n + 1) * (Polynomial.Chebyshev.U ℂ ((n + 1 : ℕ) : ℤ)).eval x) +
          B * (t ^ n * (Polynomial.Chebyshev.U ℂ (n : ℤ)).eval x) =
          t ^ (n + 2) * (2 * x *
            (Polynomial.Chebyshev.U ℂ ((n + 1 : ℕ) : ℤ)).eval x -
            (Polynomial.Chebyshev.U ℂ (n : ℤ)).eval x)
      rw [← hAx, hB]
      simp only [pow_succ]
      ring

private theorem two_step_zero_of_chebyshev_parameter (w : ℕ → ℂ)
    (A B t c : ℂ) (n : ℕ) (ht : t ≠ 0) (htsq : t ^ 2 = -B)
    (h0 : w 0 = 1) (h1 : w 1 = A)
    (hrec : ∀ m, w (m + 2) = A * w (m + 1) + B * w m)
    (hq : A ^ 2 = -4 * B * c ^ 2)
    (hc : (Polynomial.Chebyshev.U ℂ (n : ℤ)).eval c = 0) :
    w n = 0 := by
  let x := A / (2 * t)
  have h2t : (2 : ℂ) * t ≠ 0 := mul_ne_zero (by norm_num) ht
  have hxsq : x ^ 2 = c ^ 2 := by
    dsimp [x]
    rw [div_pow]
    apply (div_eq_iff (pow_ne_zero _ h2t)).mpr
    rw [mul_pow]
    linear_combination hq - (4 * c ^ 2) * htsq
  have hUx : (Polynomial.Chebyshev.U ℂ (n : ℤ)).eval x = 0 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hxsq with hx | hx
    · simp [hx, hc]
    · simp [hx, Polynomial.Chebyshev.U_eval_neg, hc]
  rw [two_step_chebyshev_form w A B t ht htsq h0 h1 hrec n, hUx, mul_zero]

private theorem tendsto_chebyshev_grid (t : ℝ) (ht0 : 0 < t) :
    Tendsto (fun n : ℕ =>
      ((⌊(n : ℝ) * t⌋₊ + 1 : ℕ) : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 t) := by
  have hlo : Tendsto (fun n : ℕ => t * ((n : ℝ) / (n + 1))) atTop (𝓝 t) := by
    simpa using (tendsto_const_nhds (x := t)).mul
      (tendsto_natCast_div_add_atTop (1 : ℝ))
  have hhi : Tendsto (fun n : ℕ =>
      t * ((n : ℝ) / (n + 1)) + 1 / (n + 1)) atTop (𝓝 t) := by
    simpa using hlo.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi
  · intro n
    change t * ((n : ℝ) / (n + 1)) ≤
      ((⌊(n : ℝ) * t⌋₊ + 1 : ℕ) : ℝ) / ((n : ℝ) + 1)
    have hlt := Nat.lt_floor_add_one ((n : ℝ) * t)
    have hden : 0 < (n : ℝ) + 1 := by positivity
    have : (n : ℝ) * t ≤ ((⌊(n : ℝ) * t⌋₊ + 1 : ℕ) : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hlt.le
    calc
      t * ((n : ℝ) / (n + 1)) = ((n : ℝ) * t) / (n + 1) := by ring
      _ ≤ ((⌊(n : ℝ) * t⌋₊ + 1 : ℕ) : ℝ) / (n + 1) :=
        div_le_div_of_nonneg_right this hden.le
  · intro n
    change ((⌊(n : ℝ) * t⌋₊ + 1 : ℕ) : ℝ) / ((n : ℝ) + 1) ≤
      t * ((n : ℝ) / (n + 1)) + 1 / (n + 1)
    have hn : 0 ≤ (n : ℝ) * t := by positivity
    have hle := Nat.floor_le hn
    have hden : 0 < (n : ℝ) + 1 := by positivity
    have : ((⌊(n : ℝ) * t⌋₊ + 1 : ℕ) : ℝ) ≤ (n : ℝ) * t + 1 := by
      simp only [Nat.cast_add, Nat.cast_one]
      linarith
    calc
      ((⌊(n : ℝ) * t⌋₊ + 1 : ℕ) : ℝ) / (n + 1) ≤
          ((n : ℝ) * t + 1) / (n + 1) :=
        div_le_div_of_nonneg_right this hden.le
      _ = t * ((n : ℝ) / (n + 1)) + 1 / (n + 1) := by ring

private theorem chebyshev_grid_root (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    ∀ᶠ (n : ℕ) in atTop,
      (Polynomial.Chebyshev.U ℂ (n : ℤ)).eval
        (Real.cos (((⌊(n : ℝ) * t⌋₊ + 1 : ℕ) : ℝ) * Real.pi / (n + 1)) : ℂ) = 0 := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  let k := ⌊(n : ℝ) * t⌋₊ + 1
  have hkpos : 0 < k := by dsimp [k]; lia
  have hfloorle : ((⌊(n : ℝ) * t⌋₊ : ℕ) : ℝ) ≤ (n : ℝ) * t :=
    Nat.floor_le (by positivity)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hkn : k ≤ n := by
    have hlt : ((⌊(n : ℝ) * t⌋₊ : ℕ) : ℝ) < n := by
      nlinarith [mul_lt_mul_of_pos_left ht1 hnpos]
    have hlt' : ⌊(n : ℝ) * t⌋₊ < n := by exact_mod_cast hlt
    dsimp [k]
    lia
  let θ : ℝ := (k : ℝ) * Real.pi / (n + 1)
  have hθ0 : 0 < θ := by dsimp [θ]; positivity
  have hθπ : θ < Real.pi := by
    dsimp [θ]
    have hden : (0 : ℝ) < n + 1 := by positivity
    apply (div_lt_iff₀ hden).mpr
    have hkn' : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
    nlinarith [Real.pi_pos]
  have hsin : Real.sin θ ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ).ne'
  have hθmul : ((n : ℤ) + 1 : ℝ) * θ = (k : ℝ) * Real.pi := by
    dsimp [θ]
    simp only [Int.cast_natCast]
    have hden : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hden]
  have hsinmul : Real.sin (((n : ℤ) + 1 : ℝ) * θ) = 0 := by
    rw [hθmul]
    exact Real.sin_nat_mul_pi k
  have hreal := Polynomial.Chebyshev.U_real_cos θ (n : ℤ)
  rw [hsinmul] at hreal
  have hUreal : (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval (Real.cos θ) = 0 :=
    (mul_eq_zero.mp hreal).resolve_right hsin
  have hcomplex : (Polynomial.Chebyshev.U ℂ (n : ℤ)).eval
      (Real.cos θ : ℂ) = 0 := by
    rw [← Polynomial.Chebyshev.map_U Complex.ofRealHom]
    rw [Polynomial.eval_map, ← Complex.ofRealHom_eq_coe, Polynomial.eval₂_at_apply]
    simpa using congrArg (fun x : ℝ => (x : ℂ)) hUreal
  simpa [k, θ] using hcomplex

private theorem tendsto_chebyshev_grid_cos_sq (t : ℝ) (ht0 : 0 < t) :
    Tendsto (fun n : ℕ =>
      Real.cos (((⌊(n : ℝ) * t⌋₊ + 1 : ℕ) : ℝ) * Real.pi / (n + 1)) ^ 2)
      atTop (𝓝 (Real.cos (Real.pi * t) ^ 2)) := by
  have hangle : Tendsto (fun n : ℕ =>
      (((⌊(n : ℝ) * t⌋₊ + 1 : ℕ) : ℝ) * Real.pi / (n + 1)))
      atTop (𝓝 (Real.pi * t)) := by
    convert (tendsto_const_nhds (x := Real.pi)).mul (tendsto_chebyshev_grid t ht0)
      using 1
    funext n
    ring
  exact ((Real.continuous_cos.continuousAt.tendsto.comp hangle).pow 2)

private theorem norm_one_add_eq_norm_one_sub_of_sq_neg {w : ℂ} {t : ℝ}
    (ht : 0 < t) (hw : w ^ 2 = -(t : ℂ)) :
    ‖1 + w‖ = ‖1 - w‖ := by
  have hsqre : w.re ^ 2 - w.im ^ 2 = -t := by
    have h := congrArg Complex.re hw
    simpa [pow_two, Complex.mul_re, sq] using h
  have hsqim : w.re * w.im = 0 := by
    have h := congrArg Complex.im hw
    simp only [pow_two, Complex.mul_im, Complex.neg_im, Complex.ofReal_im] at h
    nlinarith
  have hre : w.re = 0 := by
    by_contra hne
    have him : w.im = 0 := (mul_eq_zero.mp hsqim).resolve_left hne
    rw [him] at hsqre
    nlinarith [sq_nonneg w.re]
  have hsq : ‖1 + w‖ ^ 2 = ‖1 - w‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, hre]
  nlinarith [norm_nonneg (1 + w), norm_nonneg (1 - w)]

/-- A positive interior Chebyshev parameter gives equimodular quadratic roots.
This supplies the order-two hypothesis in Sokal, CPC 13 (2004), Theorem 1.5(b). -/
theorem equimodular_quadratic_roots {A B d : ℂ} {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hd0 : d ≠ 0)
    (hA : A ^ 2 = -4 * (t : ℂ) * B)
    (hd : d ^ 2 = A ^ 2 + 4 * B) :
    ‖(A + d) / 2‖ = ‖(A - d) / 2‖ := by
  let w : ℂ := A / d
  let s : ℝ := t / (1 - t)
  have hs : 0 < s := div_pos ht0 (by linarith)
  have hdsq : d ^ 2 = 4 * (1 - (t : ℂ)) * B := by
    rw [hd, hA]
    ring
  have hwsq : w ^ 2 = -(s : ℂ) := by
    dsimp [w, s]
    rw [div_pow]
    apply (div_eq_iff (pow_ne_zero _ hd0)).mpr
    push_cast
    have htne : (1 - (t : ℂ)) ≠ 0 := by
      intro heq
      have : t = 1 := by exact_mod_cast (sub_eq_zero.mp heq).symm
      linarith
    field_simp [htne]
    linear_combination
      (1 - (t : ℂ)) * hA + (t : ℂ) * hdsq
  have hnorm := norm_one_add_eq_norm_one_sub_of_sq_neg hs hwsq
  have hplus : A + d = d * (1 + w) := by
    dsimp [w]
    field_simp [hd0]
    ring
  have hminus : A - d = d * (w - 1) := by
    dsimp [w]
    field_simp [hd0]
  rw [hplus, hminus, norm_div, norm_div, norm_mul, norm_mul]
  rw [show ‖w - 1‖ = ‖1 - w‖ by rw [norm_sub_rev]]
  rw [hnorm]

private theorem quadratic_q_eq_ratio_expr {A B d : ℂ}
    (hd : d ^ 2 = A ^ 2 + 4 * B)
    (hB : B ≠ 0) (hplus : A + d ≠ 0) (hminus : A - d ≠ 0) :
    A ^ 2 / (-4 * B) =
      (((A + d) / (A - d) + 1) ^ 2) / (4 * ((A + d) / (A - d))) := by
  field_simp [hB, hplus, hminus]
  have hprod := congrArg (fun x : ℂ => A ^ 2 * x) hd
  linear_combination hprod

/-- Nonconstancy of the quadratic parameter transfers to the ratio of characteristic
roots. This is the order-two nondegeneracy condition in Sokal, CPC 13 (2004), Theorem 1.5(b). -/
theorem quadratic_ratio_not_locally_constant {A B d : ℂ → ℂ}
    {z₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hd : ∀ z ∈ ball z₀ ρ, d z ^ 2 = A z ^ 2 + 4 * B z)
    (hB : ∀ z ∈ ball z₀ ρ, B z ≠ 0)
    (hplus : ∀ z ∈ ball z₀ ρ, A z + d z ≠ 0)
    (hminus : ∀ z ∈ ball z₀ ρ, A z - d z ≠ 0)
    (hnconst : ¬∀ᶠ z in 𝓝 z₀,
      A z ^ 2 / (-4 * B z) = A z₀ ^ 2 / (-4 * B z₀)) :
    ¬∀ᶠ z in 𝓝 z₀,
      ((A z + d z) / 2) / ((A z - d z) / 2) =
        ((A z₀ + d z₀) / 2) / ((A z₀ - d z₀) / 2) := by
  intro hratio
  apply hnconst
  have hqeq (z : ℂ) (hz : z ∈ ball z₀ ρ) :
      A z ^ 2 / (-4 * B z) =
        (((((A z + d z) / 2) / ((A z - d z) / 2)) + 1) ^ 2) /
          (4 * (((A z + d z) / 2) / ((A z - d z) / 2))) := by
    have hr : ((A z + d z) / 2) / ((A z - d z) / 2) =
        (A z + d z) / (A z - d z) := by
      field_simp [hminus z hz]
    rw [hr]
    exact quadratic_q_eq_ratio_expr (hd z hz) (hB z hz)
      (hplus z hz) (hminus z hz)
  filter_upwards [hratio, ball_mem_nhds z₀ hρ] with z hrz hz
  rw [hqeq z hz, hrz, ← hqeq z₀ (mem_ball_self hρ)]

namespace RealRooted

/-- For the Chebyshev initial data `W₀=1`, `W₁=A`, every nonconstant analytic interior
equimodular parameter `A²/(-4B)` is a liminf limit of zeros. The proof uses open mapping
and `Polynomial.Chebyshev.U_complex_cos`, independently of Hurwitz. Compare Sokal,
*Combinatorics, Probability and Computing* 13 (2004), Theorem 1.5(b). -/
theorem isLimitOfZeros_chebyshev_two_step {A B : ℂ → ℂ} {W : ℕ → ℂ → ℂ}
    {z₀ : ℂ} {q₀ : ℝ}
    (h0 : W 0 = fun _ => 1) (h1 : W 1 = A)
    (hrec : ∀ n z, W (n + 2) z = A z * W (n + 1) z + B z * W n z)
    (hA : AnalyticAt ℂ A z₀) (hB : AnalyticAt ℂ B z₀)
    (hB0 : B z₀ ≠ 0) (hqpos : 0 < q₀) (hqlt : q₀ < 1)
    (hq0 : A z₀ ^ 2 / (-4 * B z₀) = (q₀ : ℂ))
    (hnconst : ¬∀ᶠ z in 𝓝 z₀,
      A z ^ 2 / (-4 * B z) = A z₀ ^ 2 / (-4 * B z₀)) :
    Complex.IsLimitOfZeros W z₀ := by
  let q : ℂ → ℂ := fun z => A z ^ 2 / (-4 * B z)
  have hden0 : (-4 : ℂ) * B z₀ ≠ 0 := mul_ne_zero (by norm_num) hB0
  have hq : AnalyticAt ℂ q z₀ :=
    (hA.pow 2).div (analyticAt_const.mul hB) hden0
  have hBnear : ∀ᶠ z in 𝓝 z₀, B z ≠ 0 := hB.continuousAt.eventually_ne hB0
  obtain ⟨ρ, hρ, hBball⟩ := Metric.mem_nhds_iff.mp hBnear
  let t : ℝ := Real.arccos (Real.sqrt q₀) / Real.pi
  have hsqrt0 : 0 < Real.sqrt q₀ := Real.sqrt_pos.2 hqpos
  have hsqrt1 : Real.sqrt q₀ < 1 := by
    nlinarith [Real.sq_sqrt hqpos.le]
  have hθ0 : 0 < Real.arccos (Real.sqrt q₀) :=
    Real.arccos_pos.mpr hsqrt1
  have hθπ : Real.arccos (Real.sqrt q₀) < Real.pi :=
    Real.arccos_lt_pi.mpr (by linarith)
  have ht0 : 0 < t := div_pos hθ0 Real.pi_pos
  have ht1 : t < 1 := (div_lt_one Real.pi_pos).mpr hθπ
  have htarget : Real.cos (Real.pi * t) ^ 2 = q₀ := by
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    have heq : Real.pi * t = Real.arccos (Real.sqrt q₀) := by
      dsimp [t]
      exact mul_div_cancel₀ _ hπ
    rw [heq, Real.cos_arccos (by linarith) hsqrt1.le,
      Real.sq_sqrt hqpos.le]
  have hgridReal : Tendsto (fun n : ℕ =>
      Real.cos (((⌊(n : ℝ) * t⌋₊ + 1 : ℕ) : ℝ) * Real.pi / (n + 1)) ^ 2)
      atTop (𝓝 q₀) := by
    rw [← htarget]
    exact tendsto_chebyshev_grid_cos_sq t ht0
  have hgrid : Tendsto (fun n : ℕ =>
      ((Real.cos (((⌊(n : ℝ) * t⌋₊ + 1 : ℕ) : ℝ) * Real.pi / (n + 1)) ^ 2 : ℝ) : ℂ))
      atTop (𝓝 (q z₀)) := by
    rw [show q z₀ = (q₀ : ℂ) from hq0]
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp hgridReal
  intro ε hε
  let δ := min ε ρ / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδε : δ ≤ ε := by
    dsimp [δ]
    have := min_le_left ε ρ
    linarith
  have hδρ : δ ≤ ρ := by
    dsimp [δ]
    have := min_le_right ε ρ
    linarith
  have hmap : 𝓝 (q z₀) ≤ Filter.map q (𝓝 z₀) :=
    (hq.eventually_constant_or_nhds_le_map_nhds).resolve_left hnconst
  have himage : q '' ball z₀ δ ∈ 𝓝 (q z₀) := by
    apply hmap
    change q ⁻¹' (q '' ball z₀ δ) ∈ 𝓝 z₀
    exact mem_of_superset (ball_mem_nhds z₀ hδ)
      (fun z hz => ⟨z, hz, rfl⟩)
  obtain ⟨η, hη, hηim⟩ := Metric.mem_nhds_iff.mp himage
  have hgridnear : ∀ᶠ (n : ℕ) in atTop,
      ((Real.cos (((⌊(n : ℝ) * t⌋₊ + 1 : ℕ) : ℝ) * Real.pi / (n + 1)) ^ 2 : ℝ) : ℂ)
        ∈ ball (q z₀) η :=
    hgrid.eventually (isOpen_ball.mem_nhds (mem_ball_self hη))
  filter_upwards [hgridnear, chebyshev_grid_root t ht0 ht1] with n hn hUn
  obtain ⟨z, hzδ, hqz⟩ := hηim hn
  have hzρ : z ∈ ball z₀ ρ := ball_subset_ball hδρ hzδ
  have hBz : B z ≠ 0 := hBball hzρ
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (-B z) (by norm_num : 0 < 2)
  have hu0 : u ≠ 0 := by
    intro heq
    exact hBz (by simpa [heq] using hu.symm)
  let c : ℂ :=
    (Real.cos (((⌊(n : ℝ) * t⌋₊ + 1 : ℕ) : ℝ) * Real.pi / (n + 1)) : ℂ)
  have hqparam : A z ^ 2 = -4 * B z * c ^ 2 := by
    have hden : (-4 : ℂ) * B z ≠ 0 := mul_ne_zero (by norm_num) hBz
    dsimp [q] at hqz
    dsimp [c]
    field_simp [hden] at hqz
    push_cast at hqz
    push_cast
    linear_combination -hqz
  have hzero : W n z = 0 :=
    two_step_zero_of_chebyshev_parameter (fun m => W m z) (A z) (B z)
      u c n hu0 hu (by simpa using congrFun h0 z) (by simpa using congrFun h1 z)
      (fun m => hrec m z) hqparam hUn
  exact ⟨z, ball_subset_ball hδε hzδ, hzero⟩

/-- A general analytic order-two recurrence has zeros accumulating at a point with two
distinct equimodular characteristic roots and nonzero interpolation coefficients.
This is the order-two application of Sokal, *Combinatorics, Probability and Computing*
13 (2004), Theorem 1.5(b). -/
theorem isLimitOfZeros_two_step_of_roots {A B U V u v : ℂ → ℂ}
    {W : ℕ → ℂ → ℂ} {z₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (h0 : W 0 = U) (h1 : W 1 = V)
    (hrec : ∀ n z, W (n + 2) z = A z * W (n + 1) z + B z * W n z)
    (hroots : ∀ z ∈ ball z₀ ρ, u z + v z = A z ∧ u z * v z = -B z ∧ u z ≠ v z)
    (hU : AnalyticAt ℂ U z₀) (hV : AnalyticAt ℂ V z₀)
    (hu : AnalyticAt ℂ u z₀) (hv : AnalyticAt ℂ v z₀)
    (hunu : u z₀ ≠ v z₀) (hv0 : v z₀ ≠ 0)
    (hcoeffu : V z₀ - v z₀ * U z₀ ≠ 0)
    (hcoeffv : u z₀ * U z₀ - V z₀ ≠ 0)
    (heq : ‖u z₀‖ = ‖v z₀‖)
    (hnconst : ¬∀ᶠ z in 𝓝 z₀, u z / v z = u z₀ / v z₀) :
    Complex.IsLimitOfZeros W z₀ := by
  let αu : ℂ → ℂ := fun z => (V z - v z * U z) / (u z - v z)
  let αv : ℂ → ℂ := fun z => (u z * U z - V z) / (u z - v z)
  have hden : u z₀ - v z₀ ≠ 0 := sub_ne_zero.mpr hunu
  have hαu : AnalyticAt ℂ αu z₀ :=
    (hV.sub (hv.mul hU)).div (hu.sub hv) hden
  have hαv : AnalyticAt ℂ αv z₀ :=
    ((hu.mul hU).sub hV).div (hu.sub hv) hden
  have hαu0 : αu z₀ ≠ 0 := div_ne_zero hcoeffu hden
  have hαv0 : αv z₀ ≠ 0 := div_ne_zero hcoeffv hden
  have hform (n : ℕ) (z : ℂ) (hz : z ∈ ball z₀ ρ) :
      W n z = αu z * u z ^ n + αv z * v z ^ n := by
    have hrz := hroots z hz
    have h := two_step_closed_form (fun n => W n z) (A z) (B z) (u z) (v z)
      (fun n => hrec n z) hrz.1 hrz.2.1 hrz.2.2 n
    simpa [αu, αv, ← h0, ← h1] using h
  have htwo : Complex.IsLimitOfZeros
      (fun n z => αu z * u z ^ n + αv z * v z ^ n) z₀ :=
    Complex.isLimitOfZeros_two_terms hαu hαv hu hv hαu0 hαv0 hv0 heq hnconst
  apply Complex.isLimitOfZeros_of_eventually_zero_imp hρ htwo
  exact Eventually.of_forall fun n z hz hzero => by
    rw [hform n z hz]
    exact hzero

/-- The order-two two-dominant theorem when interpolation coefficients may vanish at the
equimodular point but are nonzero analytic germs. This is the coefficient-zero closure
extension of Sokal, *Combinatorics, Probability and Computing* 13 (2004), Theorem 1.5(b). -/
theorem isLimitOfZeros_two_step_of_roots_closure {A B U V u v : ℂ → ℂ}
    {W : ℕ → ℂ → ℂ} {z₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (h0 : W 0 = U) (h1 : W 1 = V)
    (hrec : ∀ n z, W (n + 2) z = A z * W (n + 1) z + B z * W n z)
    (hroots : ∀ z ∈ ball z₀ ρ, u z + v z = A z ∧ u z * v z = -B z ∧ u z ≠ v z)
    (hU : AnalyticAt ℂ U z₀) (hV : AnalyticAt ℂ V z₀)
    (hu : AnalyticAt ℂ u z₀) (hv : AnalyticAt ℂ v z₀)
    (hunu : u z₀ ≠ v z₀) (hv0 : v z₀ ≠ 0)
    (hcoeffu : ¬∀ᶠ z in 𝓝 z₀, V z - v z * U z = 0)
    (hcoeffv : ¬∀ᶠ z in 𝓝 z₀, u z * U z - V z = 0)
    (heq : ‖u z₀‖ = ‖v z₀‖)
    (hnconst : ¬∀ᶠ z in 𝓝 z₀, u z / v z = u z₀ / v z₀) :
    Complex.IsLimitOfZeros W z₀ := by
  let αu : ℂ → ℂ := fun z => (V z - v z * U z) / (u z - v z)
  let αv : ℂ → ℂ := fun z => (u z * U z - V z) / (u z - v z)
  have hden : u z₀ - v z₀ ≠ 0 := sub_ne_zero.mpr hunu
  have hαu : AnalyticAt ℂ αu z₀ :=
    (hV.sub (hv.mul hU)).div (hu.sub hv) hden
  have hαv : AnalyticAt ℂ αv z₀ :=
    ((hu.mul hU).sub hV).div (hu.sub hv) hden
  have hdenev : ∀ᶠ z in 𝓝 z₀, u z - v z ≠ 0 :=
    (hu.sub hv).continuousAt.eventually_ne hden
  have hαugerm : ¬∀ᶠ z in 𝓝 z₀, αu z = 0 := by
    intro h
    apply hcoeffu
    filter_upwards [h, hdenev] with z hz hzden
    rcases div_eq_zero_iff.mp hz with hnum | hdenz
    · exact hnum
    · exact (hzden hdenz).elim
  have hαvgerm : ¬∀ᶠ z in 𝓝 z₀, αv z = 0 := by
    intro h
    apply hcoeffv
    filter_upwards [h, hdenev] with z hz hzden
    rcases div_eq_zero_iff.mp hz with hnum | hdenz
    · exact hnum
    · exact (hzden hdenz).elim
  have hform (n : ℕ) (z : ℂ) (hz : z ∈ ball z₀ ρ) :
      W n z = αu z * u z ^ n + αv z * v z ^ n := by
    have hrz := hroots z hz
    have h := two_step_closed_form (fun n => W n z) (A z) (B z) (u z) (v z)
      (fun n => hrec n z) hrz.1 hrz.2.1 hrz.2.2 n
    simpa [αu, αv, ← h0, ← h1] using h
  let α : Bool → ℂ → ℂ := fun k => if k then αu else αv
  let β : Bool → ℂ → ℂ := fun k => if k then u else v
  have htwo : Complex.IsLimitOfZeros
      (fun n z => αu z * u z ^ n + αv z * v z ^ n) z₀ := by
    have h := Complex.isLimitOfZeros_finset_two_dominant_closure
      (Finset.univ : Finset Bool) α β true false
      (by simp) (by simp) (by decide)
      (by
        intro k _
        cases k with
        | false => simpa [α] using hαv
        | true => simpa [α] using hαu)
      (by
        intro k _
        cases k with
        | false => simpa [β] using hv
        | true => simpa [β] using hu)
      (by simpa [α] using hαugerm) (by simpa [α] using hαvgerm)
      (by simpa [β] using hv0) (by simpa [β] using heq)
      (by intro k _ hki hkj; cases k <;> simp_all)
      (by simpa [β] using hnconst)
    simpa [α, β, Fintype.sum_bool, add_comm] using h
  apply Complex.isLimitOfZeros_of_eventually_zero_imp hρ htwo
  exact Eventually.of_forall fun n z hz hzero => by
    rw [hform n z hz]
    exact hzero

/-- General initial data for an order-two recurrence, expressed through an analytic square-root
branch of `A²+4B`. This applies Sokal's two-dominant theorem; *Combinatorics, Probability and
Computing* 13 (2004), Theorem 1.5(b). -/
theorem isLimitOfZeros_two_step_of_analytic_sqrt
    {A B U V d : ℂ → ℂ} {W : ℕ → ℂ → ℂ} {z₀ : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (h0 : W 0 = U) (h1 : W 1 = V)
    (hrec : ∀ n z, W (n + 2) z = A z * W (n + 1) z + B z * W n z)
    (hA : AnalyticAt ℂ A z₀) (hU : AnalyticAt ℂ U z₀)
    (hV : AnalyticAt ℂ V z₀) (hd : AnalyticAt ℂ d z₀)
    (hdsq : ∀ z ∈ ball z₀ ρ, d z ^ 2 = A z ^ 2 + 4 * B z)
    (hd0 : d z₀ ≠ 0)
    (hv0 : (A z₀ - d z₀) / 2 ≠ 0)
    (hcoeffu : V z₀ - ((A z₀ - d z₀) / 2) * U z₀ ≠ 0)
    (hcoeffv : ((A z₀ + d z₀) / 2) * U z₀ - V z₀ ≠ 0)
    (heq : ‖(A z₀ + d z₀) / 2‖ = ‖(A z₀ - d z₀) / 2‖)
    (hnconst : ¬∀ᶠ z in 𝓝 z₀,
      ((A z + d z) / 2) / ((A z - d z) / 2) =
        ((A z₀ + d z₀) / 2) / ((A z₀ - d z₀) / 2)) :
    Complex.IsLimitOfZeros W z₀ := by
  let u : ℂ → ℂ := fun z => (A z + d z) / 2
  let v : ℂ → ℂ := fun z => (A z - d z) / 2
  have hdev : ∀ᶠ z in 𝓝 z₀, d z ≠ 0 := hd.continuousAt.eventually_ne hd0
  obtain ⟨δ, hδ, hdball⟩ := Metric.mem_nhds_iff.mp hdev
  let η := min ρ δ
  have hη : 0 < η := lt_min hρ hδ
  have hηρ : ball z₀ η ⊆ ball z₀ ρ := ball_subset_ball (min_le_left _ _)
  have hηδ : ball z₀ η ⊆ ball z₀ δ := ball_subset_ball (min_le_right _ _)
  have hroots : ∀ z ∈ ball z₀ η,
      u z + v z = A z ∧ u z * v z = -B z ∧ u z ≠ v z := by
    intro z hz
    have hdz : d z ≠ 0 := hdball (hηδ hz)
    have hsq := hdsq z (hηρ hz)
    refine ⟨?_, ?_, ?_⟩
    · dsimp [u, v]
      ring
    · dsimp [u, v]
      linear_combination (-1 / 4 : ℂ) * hsq
    · intro heqz
      apply hdz
      dsimp [u, v] at heqz
      linear_combination heqz
  have hu : AnalyticAt ℂ u z₀ := (hA.add hd).div_const
  have hv : AnalyticAt ℂ v z₀ := (hA.sub hd).div_const
  have hunu : u z₀ ≠ v z₀ := by
    intro heqz
    apply hd0
    dsimp [u, v] at heqz
    linear_combination heqz
  exact isLimitOfZeros_two_step_of_roots hη h0 h1 hrec hroots hU hV
    hu hv hunu hv0 hcoeffu hcoeffv heq hnconst

end RealRooted

namespace RealRooted

/-- Chebyshev-data rows have the expected degree when the `A W (n+1)` term strictly
dominates the `B W n` term in degree. This supplies nonvanishing for applications of
Sokal, *Combinatorics, Probability and Computing* 13 (2004), Theorem 1.5(b). -/
theorem chebyshev_two_step_natDegree_of_degree_lt {A B : ℝ[X]} {W : ℕ → ℝ[X]}
    (hA : A.natDegree ≠ 0) (hB : B.natDegree < 2 * A.natDegree)
    (h0 : W 0 = 1) (h1 : W 1 = A)
    (hrec : ∀ n, W (n + 2) = A * W (n + 1) + B * W n) (n : ℕ) :
    (W n).natDegree = A.natDegree * n := by
  have hAne : A ≠ 0 := by
    intro hzero
    apply hA
    simp [hzero]
  induction n using Nat.twoStepInduction with
  | zero => simp [h0]
  | one => simp [h1]
  | more n hn hn1 =>
      have hApos : 0 < A.natDegree := Nat.pos_of_ne_zero hA
      have hW1 : W (n + 1) ≠ 0 := by
        intro hzero
        rw [hzero, natDegree_zero] at hn1
        have hpos : 0 < A.natDegree * (n + 1) := Nat.mul_pos hApos (by lia)
        lia
      have hleft : (A * W (n + 1)).natDegree = A.natDegree * (n + 2) := by
        rw [natDegree_mul hAne hW1, hn1]
        ring
      have hright : (B * W n).natDegree < A.natDegree * (n + 2) := by
        calc
          (B * W n).natDegree ≤ B.natDegree + (W n).natDegree := natDegree_mul_le
          _ = B.natDegree + A.natDegree * n := by rw [hn]
          _ < 2 * A.natDegree + A.natDegree * n := Nat.add_lt_add_right hB _
          _ = A.natDegree * (n + 2) := by ring
      have hright' : (B * W n).natDegree < (A * W (n + 1)).natDegree := by
        rwa [hleft]
      rw [hrec, natDegree_add_eq_left_of_natDegree_lt hright', hleft]

/-- Under strict degree dominance, every Chebyshev-data row is nonzero (hence in
particular the rows are eventually nonzero). This is the nonvanishing input for Sokal,
*Combinatorics, Probability and Computing* 13 (2004), Theorem 1.5(b). -/
theorem chebyshev_two_step_ne_zero_of_degree_lt {A B : ℝ[X]} {W : ℕ → ℝ[X]}
    (hA : A.natDegree ≠ 0) (hB : B.natDegree < 2 * A.natDegree)
    (h0 : W 0 = 1) (h1 : W 1 = A)
    (hrec : ∀ n, W (n + 2) = A * W (n + 1) + B * W n) (n : ℕ) :
    W n ≠ 0 := by
  rcases n with _ | n
  · simp [h0]
  · intro hzero
    have hdeg := chebyshev_two_step_natDegree_of_degree_lt hA hB h0 h1 hrec (n + 1)
    rw [hzero, natDegree_zero] at hdeg
    have hpos : 0 < A.natDegree * (n + 1) :=
      Nat.mul_pos (Nat.pos_of_ne_zero hA) (by lia)
    lia

/-- A nonreal liminf limit of zeros forces every sufficiently late nonzero real polynomial
to fail to split over `ℝ`. This is the real-rootedness obstruction supplied by Sokal,
*Combinatorics, Probability and Computing* 13 (2004), Theorem 1.5(b). -/
theorem eventually_not_splits_of_nonreal_limit {W : ℕ → ℝ[X]} {z₀ : ℂ}
    (hz₀ : z₀.im ≠ 0)
    (hW : ∀ᶠ n in atTop, W n ≠ 0)
    (hlim : Complex.IsLimitOfZeros
      (fun n z => ((W n).map Complex.ofRealHom).eval z) z₀) :
    ∀ᶠ n in atTop, ¬(W n).Splits := by
  let ε := |z₀.im| / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  filter_upwards [hW, hlim ε hε] with n hn ⟨z, hz, hroot⟩ hsplit
  have hzim : z.im ≠ 0 := by
    intro heq
    have hbound := Complex.abs_im_le_norm (z - z₀)
    rw [Complex.sub_im, heq, zero_sub, abs_neg] at hbound
    rw [mem_ball, dist_eq_norm] at hz
    dsimp [ε] at hz
    have hpos : 0 < |z₀.im| := abs_pos.mpr hz₀
    linarith
  have hrange : z ∈ (Complex.ofRealHom).range :=
    hsplit.mem_range_of_isRoot hn (i := Complex.ofRealHom) hroot
  obtain ⟨x, rfl⟩ := hrange
  exact hzim (by simp)

/-- **Order-two BKW criterion.** Suppose the Chebyshev-data rows
`W₀ = 1`, `W₁ = A`, `W (n+2) = A W (n+1) + B W n` satisfy strict degree dominance.
If a nonreal point has nonzero `B`, the parameter `A²/(-4B)` lies in `(0,1)`, and that
parameter is not locally constant, then every sufficiently late row fails to split over
`ℝ`. This is Sokal, *Combinatorics, Probability and Computing* 13 (2004), Theorem 1.5(b). -/
theorem eventually_not_splits_chebyshev_two_step_of_ratio
    {A B : ℝ[X]} {W : ℕ → ℝ[X]} {z₀ : ℂ} {q₀ : ℝ}
    (hAdeg : A.natDegree ≠ 0) (hBdeg : B.natDegree < 2 * A.natDegree)
    (h0 : W 0 = 1) (h1 : W 1 = A)
    (hrec : ∀ n, W (n + 2) = A * W (n + 1) + B * W n)
    (hz₀ : z₀.im ≠ 0) (hB0 : aeval z₀ B ≠ 0)
    (hqpos : 0 < q₀) (hqlt : q₀ < 1)
    (hq0 : aeval z₀ A ^ 2 / (-4 * aeval z₀ B) = (q₀ : ℂ))
    (hnconst : ¬∀ᶠ z in 𝓝 z₀,
      aeval z A ^ 2 / (-4 * aeval z B) =
        aeval z₀ A ^ 2 / (-4 * aeval z₀ B)) :
    ∀ᶠ n in atTop, ¬(W n).Splits := by
  let Ac : ℂ → ℂ := fun z => aeval z A
  let Bc : ℂ → ℂ := fun z => aeval z B
  let F : ℕ → ℂ → ℂ := fun n z => aeval z (W n)
  have hF0 : F 0 = fun _ => 1 := by
    funext z
    simp [F, h0]
  have hF1 : F 1 = Ac := by
    funext z
    simp [F, Ac, h1]
  have hFrec (n : ℕ) (z : ℂ) :
      F (n + 2) z = Ac z * F (n + 1) z + Bc z * F n z := by
    simp [F, Ac, Bc, hrec]
  have hAc : AnalyticAt ℂ Ac z₀ := by
    dsimp [Ac]
    exact analyticAt_id.aeval_polynomial A
  have hBc : AnalyticAt ℂ Bc z₀ := by
    dsimp [Bc]
    exact analyticAt_id.aeval_polynomial B
  have hlim : Complex.IsLimitOfZeros F z₀ :=
    isLimitOfZeros_chebyshev_two_step hF0 hF1 hFrec hAc hBc hB0
      hqpos hqlt hq0 hnconst
  apply eventually_not_splits_of_nonreal_limit hz₀
    (Eventually.of_forall (chebyshev_two_step_ne_zero_of_degree_lt
      hAdeg hBdeg h0 h1 hrec))
  have hhom : Complex.ofRealHom = algebraMap ℝ ℂ := by
    ext x
    rfl
  rw [hhom]
  simpa only [F, aeval_def, eval₂_eq_eval_map] using hlim

/-- **Fibonacci/Pell-type BKW obstruction.** If `p ≠ 0` and `s > 0`, then the
Chebyshev-data recurrence `W₀ = 1`, `W₁ = pX`,
`W (n+2) = pX W (n+1) + s W n` eventually fails to split over `ℝ`.
This is a direct corollary of Sokal, *Combinatorics, Probability and Computing*
13 (2004), Theorem 1.5(b). -/
theorem eventually_not_splits_of_mul_X_const_two_step {p s : ℝ} (hp : p ≠ 0)
    (hs : 0 < s) {W : ℕ → ℝ[X]} (h0 : W 0 = 1) (h1 : W 1 = C p * X)
    (hrec : ∀ n, W (n + 2) = (C p * X) * W (n + 1) + C s * W n) :
    ∀ᶠ n in atTop, ¬(W n).Splits := by
  let z₀ : ℂ := (Real.sqrt s / p : ℝ) * Complex.I
  have hz₀ : z₀.im ≠ 0 := by
    dsimp [z₀]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
      Complex.ofReal_im, Complex.I_re, zero_mul, add_zero]
    exact div_ne_zero (Real.sqrt_ne_zero'.mpr hs) hp
  have hB0 : aeval z₀ (C s : ℝ[X]) ≠ 0 := by
    simp [hs.ne']
  have hq0 : aeval z₀ (C p * X : ℝ[X]) ^ 2 /
      (-4 * aeval z₀ (C s : ℝ[X])) = ((1 / 4 : ℝ) : ℂ) := by
    simp only [map_mul, aeval_C, aeval_X]
    have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp
    have hsqrt : ((Real.sqrt s : ℝ) : ℂ) ^ 2 = (s : ℂ) := by
      exact_mod_cast Real.sq_sqrt hs.le
    have hquot : (((Real.sqrt s / p : ℝ) : ℂ) ^ 2) =
        (s : ℂ) / (p : ℂ) ^ 2 := by
      push_cast
      rw [div_pow, hsqrt]
    dsimp [z₀]
    field_simp [hp0, hs0]
    rw [hquot, Complex.I_sq]
    field_simp [hp0]
    norm_num
  have hnconst : ¬∀ᶠ z in 𝓝 z₀,
      aeval z (C p * X : ℝ[X]) ^ 2 / (-4 * aeval z (C s : ℝ[X])) =
        aeval z₀ (C p * X : ℝ[X]) ^ 2 / (-4 * aeval z₀ (C s : ℝ[X])) := by
    intro hconst
    let P : ℂ → ℂ := fun z => ((p : ℂ) * z) ^ 2 + s
    have hP : AnalyticOnNhd ℂ P Set.univ := by
      intro z _
      dsimp [P]
      fun_prop
    have hzero : P =ᶠ[𝓝 z₀] 0 := by
      filter_upwards [hconst] with z hz
      rw [hq0] at hz
      simp only [map_mul, aeval_C, aeval_X] at hz
      have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
      change P z = 0
      dsimp [P]
      field_simp [hs0] at hz
      norm_num at hz
      linear_combination -hz
    have hglobal := hP.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ z₀) hzero
    have hs0 := hglobal (Set.mem_univ (0 : ℂ))
    have hsC : (s : ℂ) = 0 := by
      simpa only [P, mul_zero, pow_two, zero_mul, zero_add, Pi.zero_apply] using hs0
    exact hs.ne' (by exact_mod_cast hsC)
  apply eventually_not_splits_chebyshev_two_step_of_ratio
    (A := C p * X) (B := C s) (z₀ := z₀) (q₀ := 1 / 4)
    (by rw [natDegree_C_mul_X p hp]; norm_num)
    (by rw [natDegree_C_mul_X p hp]; simp)
    h0 h1 hrec hz₀ hB0 (by norm_num) (by norm_num) hq0 hnconst

end RealRooted
