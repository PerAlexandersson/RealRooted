import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecificLimits.Normed
import RealRooted.Mathlib.Algebra.LinearRecurrence.Quadratic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Asymptotics of linear recurrences with polynomial modes

Ratio limits for sequences of the form `(α n + β) λ^n + (γ n + δ) ν^n` and their quadratic
analogues, with `|ν| < λ`, and the scalar recurrences satisfied by `P n (1)`, `P n '(1)` and
`P n ''(1)` when `P (n + 2) = a * P (n + 1) + b * P n`.
-/

open Filter Topology
open scoped Polynomial

namespace LinearRecurrence

/-- The normalized linear root-mode ratio has a finite limit. -/
theorem linear_ratio_tendsto {A B α β γ δ r : ℝ} (hA : A ≠ 0)
    (hr : |r| < 1) :
    Tendsto (fun n : ℕ =>
      (((α * (n : ℝ) + β) + (γ * (n : ℝ) + δ) * r ^ n) /
        (A + B * r ^ n) - (α / A) * (n : ℝ))) atTop (𝓝 (β / A)) := by
  have hpow0 : Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one hr
  have hpow1 : Tendsto (fun n : ℕ => (n : ℝ) * r ^ n) atTop (𝓝 0) :=
    tendsto_self_mul_const_pow_of_abs_lt_one hr
  have hden : Tendsto (fun n : ℕ => A + B * r ^ n) atTop (𝓝 A) := by
    simpa only [mul_zero, add_zero] using
      (tendsto_const_nhds (f := atTop) (x := A)).add
        ((tendsto_const_nhds (f := atTop) (x := B)).mul hpow0)
  have hnum : Tendsto
      (fun n : ℕ => A * β + A * (γ * (n : ℝ) + δ) * r ^ n -
        α * (n : ℝ) * B * r ^ n) atTop (𝓝 (A * β)) := by
    have hγ : Tendsto (fun n : ℕ => γ * ((n : ℝ) * r ^ n)) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_const_nhds (f := atTop) (x := γ)).mul hpow1
    have hδ : Tendsto (fun n : ℕ => δ * r ^ n) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_const_nhds (f := atTop) (x := δ)).mul hpow0
    have hinner : Tendsto (fun n : ℕ =>
        γ * ((n : ℝ) * r ^ n) + δ * r ^ n) atTop (𝓝 0) := by
      simpa only [add_zero] using hγ.add hδ
    have hterm : Tendsto (fun n : ℕ =>
        A * (γ * (n : ℝ) + δ) * r ^ n) atTop (𝓝 0) := by
      convert (tendsto_const_nhds (f := atTop) (x := A)).mul hinner using 1
      · funext n
        ring
      · simp
    have hα : Tendsto (fun n : ℕ => α * ((n : ℝ) * r ^ n)) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_const_nhds (f := atTop) (x := α)).mul hpow1
    have hαB : Tendsto (fun n : ℕ =>
        α * (n : ℝ) * B * r ^ n) atTop (𝓝 0) := by
      convert hα.mul (tendsto_const_nhds (f := atTop) (x := B)) using 1
      · funext n
        ring
      · simp
    simpa only [sub_zero, add_zero] using
      (tendsto_const_nhds.add hterm).sub hαB
  have hquot := hnum.div (hden.const_mul A) (mul_ne_zero hA hA)
  have hquot' : Tendsto (fun n : ℕ =>
      (A * β + A * (γ * (n : ℝ) + δ) * r ^ n -
        α * (n : ℝ) * B * r ^ n) / (A * (A + B * r ^ n)))
      atTop (𝓝 (β / A)) := by
    convert hquot using 1
    field_simp [hA]
  have hden_ne : ∀ᶠ n : ℕ in atTop, A + B * r ^ n ≠ 0 := hden.eventually_ne hA
  have heq : ∀ᶠ n : ℕ in atTop,
      (((α * (n : ℝ) + β) + (γ * (n : ℝ) + δ) * r ^ n) /
        (A + B * r ^ n) - (α / A) * (n : ℝ)) =
      (A * β + A * (γ * (n : ℝ) + δ) * r ^ n -
        α * (n : ℝ) * B * r ^ n) / (A * (A + B * r ^ n)) := by
    filter_upwards [hden_ne] with n hn
    have hn' : r ^ n * B + A ≠ 0 := by
      intro h
      apply hn
      rw [← h]
      ring
    have hn'' : A + r ^ n * B ≠ 0 := by
      intro h
      apply hn
      simpa [mul_comm, add_comm] using h
    apply (eq_div_iff (mul_ne_zero hA hn)).2
    field_simp [hA, hn, hn', hn'']
    ring
  have heq' :
      (fun n : ℕ =>
        (A * β + A * (γ * (n : ℝ) + δ) * r ^ n -
          α * (n : ℝ) * B * r ^ n) / (A * (A + B * r ^ n))) =ᶠ[atTop]
      (fun n : ℕ =>
        ((α * (n : ℝ) + β) + (γ * (n : ℝ) + δ) * r ^ n) /
          (A + B * r ^ n) - (α / A) * (n : ℝ)) := heq.mono fun _ h => h.symm
  exact hquot'.congr' heq'

/-- The linear ratio remainder is exponentially small after one extra factor of
the index. -/
theorem linear_ratio_remainder_mul_tendsto {A B α β γ δ r : ℝ} (hA : A ≠ 0)
    (hr : |r| < 1) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      ((((α * (n : ℝ) + β) + (γ * (n : ℝ) + δ) * r ^ n) /
        (A + B * r ^ n) - (α / A) * (n : ℝ)) - β / A)) atTop (𝓝 0) := by
  have hpow0 : Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one hr
  have hpow1 : Tendsto (fun n : ℕ => (n : ℝ) * r ^ n) atTop (𝓝 0) :=
    tendsto_self_mul_const_pow_of_abs_lt_one hr
  have hpow2 : Tendsto (fun n : ℕ => (n : ℝ) ^ 2 * r ^ n) atTop (𝓝 0) :=
    tendsto_pow_const_mul_const_pow_of_abs_lt_one 2 hr
  have hden : Tendsto (fun n : ℕ => A + B * r ^ n) atTop (𝓝 A) := by
    simpa only [mul_zero, add_zero] using
      (tendsto_const_nhds (f := atTop) (x := A)).add
        ((tendsto_const_nhds (f := atTop) (x := B)).mul hpow0)
  have hnum : Tendsto (fun n : ℕ =>
      ((A * γ - α * B) * (n : ℝ) + (A * δ - β * B)) * r ^ n)
      atTop (𝓝 0) := by
    have hγ : Tendsto (fun n : ℕ =>
        (A * γ - α * B) * ((n : ℝ) * r ^ n)) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_const_nhds (f := atTop) (x := A * γ - α * B)).mul hpow1
    have hδ : Tendsto (fun n : ℕ =>
        (A * δ - β * B) * r ^ n) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_const_nhds (f := atTop) (x := A * δ - β * B)).mul hpow0
    have hsum : Tendsto (fun n : ℕ =>
        (A * γ - α * B) * ((n : ℝ) * r ^ n) +
          (A * δ - β * B) * r ^ n) atTop (𝓝 0) := by
      simpa only [add_zero] using hγ.add hδ
    convert hsum using 1
    · funext n
      ring
  have hnum' : Tendsto (fun n : ℕ =>
      ((A * γ - α * B) * (n : ℝ) + (A * δ - β * B)) *
        (n : ℝ) * r ^ n) atTop (𝓝 0) := by
    have hγ : Tendsto (fun n : ℕ =>
        (A * γ - α * B) * ((n : ℝ) ^ 2 * r ^ n)) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_const_nhds (f := atTop) (x := A * γ - α * B)).mul hpow2
    have hδ : Tendsto (fun n : ℕ =>
        (A * δ - β * B) * ((n : ℝ) * r ^ n)) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_const_nhds (f := atTop) (x := A * δ - β * B)).mul hpow1
    have hsum : Tendsto (fun n : ℕ =>
        (A * γ - α * B) * ((n : ℝ) ^ 2 * r ^ n) +
          (A * δ - β * B) * ((n : ℝ) * r ^ n)) atTop (𝓝 0) := by
      simpa only [add_zero] using hγ.add hδ
    convert hsum using 1
    · funext n
      ring
  have hquot := hnum'.div (hden.const_mul A) (mul_ne_zero hA hA)
  have hquot' : Tendsto (fun n : ℕ =>
      (((A * γ - α * B) * (n : ℝ) + (A * δ - β * B)) *
        (n : ℝ) * r ^ n) / (A * (A + B * r ^ n))) atTop (𝓝 0) := by
    convert hquot using 1
    simp only [zero_div]
  have hden_ne : ∀ᶠ n : ℕ in atTop, A + B * r ^ n ≠ 0 := hden.eventually_ne hA
  have heq : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) *
        ((((α * (n : ℝ) + β) + (γ * (n : ℝ) + δ) * r ^ n) /
          (A + B * r ^ n) - (α / A) * (n : ℝ)) - β / A) =
      (((A * γ - α * B) * (n : ℝ) + (A * δ - β * B)) *
        (n : ℝ) * r ^ n) / (A * (A + B * r ^ n)) := by
    filter_upwards [hden_ne] with n hn
    have hn' : r ^ n * B + A ≠ 0 := by
      intro h
      apply hn
      rw [← h]
      ring
    have hn'' : A + r ^ n * B ≠ 0 := by
      intro h
      apply hn
      simpa [mul_comm, add_comm] using h
    apply (eq_div_iff (mul_ne_zero hA hn)).2
    field_simp [hA, hn, hn', hn'']
    ring
  have heq' :
      (fun n : ℕ =>
        (((A * γ - α * B) * (n : ℝ) + (A * δ - β * B)) *
          (n : ℝ) * r ^ n) / (A * (A + B * r ^ n))) =ᶠ[atTop]
      (fun n : ℕ => (n : ℝ) *
        ((((α * (n : ℝ) + β) + (γ * (n : ℝ) + δ) * r ^ n) /
          (A + B * r ^ n) - (α / A) * (n : ℝ)) - β / A)) :=
    heq.mono fun _ h => h.symm
  exact hquot'.congr' heq'

/-- The normalized quadratic root-mode ratio has a finite limit after its
quadratic and linear terms are removed. -/
theorem quadratic_ratio_tendsto {A B η θ κ ζ ξ χ r : ℝ} (hA : A ≠ 0)
    (hr : |r| < 1) :
    Tendsto (fun n : ℕ =>
      (((η * (n : ℝ) ^ 2 + θ * (n : ℝ) + κ) +
          (ζ * (n : ℝ) ^ 2 + ξ * (n : ℝ) + χ) * r ^ n) /
        (A + B * r ^ n) - (η / A) * (n : ℝ) ^ 2 -
        (θ / A) * (n : ℝ))) atTop (𝓝 (κ / A)) := by
  have hpow0 : Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one hr
  have hpow1 : Tendsto (fun n : ℕ => (n : ℝ) * r ^ n) atTop (𝓝 0) :=
    tendsto_self_mul_const_pow_of_abs_lt_one hr
  have hpow2 : Tendsto (fun n : ℕ => (n : ℝ) ^ 2 * r ^ n) atTop (𝓝 0) :=
    tendsto_pow_const_mul_const_pow_of_abs_lt_one 2 hr
  have hden : Tendsto (fun n : ℕ => A + B * r ^ n) atTop (𝓝 A) := by
    simpa only [mul_zero, add_zero] using
      (tendsto_const_nhds (f := atTop) (x := A)).add
        ((tendsto_const_nhds (f := atTop) (x := B)).mul hpow0)
  have hnum : Tendsto (fun n : ℕ =>
      A * κ + A * (ζ * (n : ℝ) ^ 2 + ξ * (n : ℝ) + χ) * r ^ n -
        η * (n : ℝ) ^ 2 * B * r ^ n - θ * (n : ℝ) * B * r ^ n)
      atTop (𝓝 (A * κ)) := by
    have hζ : Tendsto (fun n : ℕ => ζ * ((n : ℝ) ^ 2 * r ^ n)) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_const_nhds (f := atTop) (x := ζ)).mul hpow2
    have hξ : Tendsto (fun n : ℕ => ξ * ((n : ℝ) * r ^ n)) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_const_nhds (f := atTop) (x := ξ)).mul hpow1
    have hχ : Tendsto (fun n : ℕ => χ * r ^ n) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_const_nhds (f := atTop) (x := χ)).mul hpow0
    have htail : Tendsto (fun n : ℕ =>
        A * (ζ * (n : ℝ) ^ 2 + ξ * (n : ℝ) + χ) * r ^ n)
        atTop (𝓝 0) := by
      have hsum : Tendsto (fun n : ℕ =>
          ζ * ((n : ℝ) ^ 2 * r ^ n) + ξ * ((n : ℝ) * r ^ n) +
            χ * r ^ n) atTop (𝓝 0) := by
        simpa only [add_zero] using (hζ.add hξ).add hχ
      convert (tendsto_const_nhds (f := atTop) (x := A)).mul hsum using 1
      · funext n
        ring
      · simp
    have hη : Tendsto (fun n : ℕ =>
        η * ((n : ℝ) ^ 2 * r ^ n)) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_const_nhds (f := atTop) (x := η)).mul hpow2
    have hηB : Tendsto (fun n : ℕ =>
        η * (n : ℝ) ^ 2 * B * r ^ n) atTop (𝓝 0) := by
      convert hη.mul (tendsto_const_nhds (f := atTop) (x := B)) using 1
      · funext n
        ring
      · simp
    have hθ : Tendsto (fun n : ℕ =>
        θ * ((n : ℝ) * r ^ n)) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_const_nhds (f := atTop) (x := θ)).mul hpow1
    have hθB : Tendsto (fun n : ℕ =>
        θ * (n : ℝ) * B * r ^ n) atTop (𝓝 0) := by
      convert hθ.mul (tendsto_const_nhds (f := atTop) (x := B)) using 1
      · funext n
        ring
      · simp
    simpa only [sub_zero, add_zero] using ((tendsto_const_nhds.add htail).sub hηB).sub hθB
  have hquot := hnum.div (hden.const_mul A) (mul_ne_zero hA hA)
  have hquot' : Tendsto (fun n : ℕ =>
      (A * κ + A * (ζ * (n : ℝ) ^ 2 + ξ * (n : ℝ) + χ) * r ^ n -
        η * (n : ℝ) ^ 2 * B * r ^ n - θ * (n : ℝ) * B * r ^ n) /
        (A * (A + B * r ^ n))) atTop (𝓝 (κ / A)) := by
    convert hquot using 1
    field_simp [hA]
  have hden_ne : ∀ᶠ n : ℕ in atTop, A + B * r ^ n ≠ 0 := hden.eventually_ne hA
  have heq : ∀ᶠ n : ℕ in atTop,
      (((η * (n : ℝ) ^ 2 + θ * (n : ℝ) + κ) +
          (ζ * (n : ℝ) ^ 2 + ξ * (n : ℝ) + χ) * r ^ n) /
        (A + B * r ^ n) - (η / A) * (n : ℝ) ^ 2 -
        (θ / A) * (n : ℝ)) =
      (A * κ + A * (ζ * (n : ℝ) ^ 2 + ξ * (n : ℝ) + χ) * r ^ n -
        η * (n : ℝ) ^ 2 * B * r ^ n - θ * (n : ℝ) * B * r ^ n) /
        (A * (A + B * r ^ n)) := by
    filter_upwards [hden_ne] with n hn
    have hn' : r ^ n * B + A ≠ 0 := by
      intro h
      apply hn
      rw [← h]
      ring
    have hn'' : A + r ^ n * B ≠ 0 := by
      intro h
      apply hn
      simpa [mul_comm, add_comm] using h
    apply (eq_div_iff (mul_ne_zero hA hn)).2
    field_simp [hA, hn, hn', hn'']
    ring
  have heq' :
      (fun n : ℕ =>
        (A * κ + A * (ζ * (n : ℝ) ^ 2 + ξ * (n : ℝ) + χ) * r ^ n -
          η * (n : ℝ) ^ 2 * B * r ^ n - θ * (n : ℝ) * B * r ^ n) /
          (A * (A + B * r ^ n))) =ᶠ[atTop]
      (fun n : ℕ =>
        (((η * (n : ℝ) ^ 2 + θ * (n : ℝ) + κ) +
            (ζ * (n : ℝ) ^ 2 + ξ * (n : ℝ) + χ) * r ^ n) /
          (A + B * r ^ n) - (η / A) * (n : ℝ) ^ 2 -
          (θ / A) * (n : ℝ))) := heq.mono fun _ h => h.symm
  exact hquot'.congr' heq'

/-- The mean correction is bounded in the algebraic two-mode model. -/
theorem linear_ratio_isBigO {A B α β γ δ r : ℝ} (hA : A ≠ 0)
    (hr : |r| < 1) :
    (fun n : ℕ =>
      (((α * (n : ℝ) + β) + (γ * (n : ℝ) + δ) * r ^ n) /
        (A + B * r ^ n) - (α / A) * (n : ℝ))) =O[atTop]
      (fun _ => (1 : ℝ)) := by
  exact (linear_ratio_tendsto hA hr).isBigO_one ℝ

/-- The quadratic ratio has bounded remainder after its two leading terms. -/
theorem quadratic_ratio_isBigO {A B η θ κ ζ ξ χ r : ℝ} (hA : A ≠ 0)
    (hr : |r| < 1) :
    (fun n : ℕ =>
      (((η * (n : ℝ) ^ 2 + θ * (n : ℝ) + κ) +
          (ζ * (n : ℝ) ^ 2 + ξ * (n : ℝ) + χ) * r ^ n) /
        (A + B * r ^ n) - (η / A) * (n : ℝ) ^ 2 -
        (θ / A) * (n : ℝ))) =O[atTop]
      (fun _ => (1 : ℝ)) := by
  exact (quadratic_ratio_tendsto hA hr).isBigO_one ℝ

/-- A quadratic second-mode ratio and a linear first-mode ratio give a bounded
variance remainder. -/
theorem variance_ratio_tendsto {A B α β γ δ η θ κ ζ ξ χ r m c σ : ℝ}
    (hA : A ≠ 0) (hr : |r| < 1) (hm : m = α / A) (hc : c = β / A)
    (hquad : η / A = m ^ 2)
    (hsigma : σ = θ / A + m - 2 * m * c) :
    Tendsto (fun n : ℕ =>
      (((η * (n : ℝ) ^ 2 + θ * (n : ℝ) + κ) +
          (ζ * (n : ℝ) ^ 2 + ξ * (n : ℝ) + χ) * r ^ n) /
        (A + B * r ^ n)) +
        (((α * (n : ℝ) + β) + (γ * (n : ℝ) + δ) * r ^ n) /
          (A + B * r ^ n)) -
        ((((α * (n : ℝ) + β) + (γ * (n : ℝ) + δ) * r ^ n) /
          (A + B * r ^ n)) ^ 2) - σ * (n : ℝ)) atTop
      (𝓝 (κ / A + c - c ^ 2)) := by
  let M : ℕ → ℝ := fun n =>
    ((α * (n : ℝ) + β) + (γ * (n : ℝ) + δ) * r ^ n) /
      (A + B * r ^ n)
  let Q : ℕ → ℝ := fun n =>
    ((η * (n : ℝ) ^ 2 + θ * (n : ℝ) + κ) +
        (ζ * (n : ℝ) ^ 2 + ξ * (n : ℝ) + χ) * r ^ n) /
      (A + B * r ^ n)
  let X : ℕ → ℝ := fun n => M n - m * (n : ℝ)
  let Y : ℕ → ℝ := fun n => Q n - (η / A) * (n : ℝ) ^ 2 -
    (θ / A) * (n : ℝ)
  have hX : Tendsto X atTop (𝓝 c) := by
    have h := linear_ratio_tendsto (A := A) (B := B) (α := α) (β := β)
      (γ := γ) (δ := δ) (r := r) hA hr
    simpa only [X, M, hm, hc] using h
  have hY : Tendsto Y atTop (𝓝 (κ / A)) := by
    have h := quadratic_ratio_tendsto (A := A) (B := B) (η := η) (θ := θ)
      (κ := κ) (ζ := ζ) (ξ := ξ) (χ := χ) (r := r) hA hr
    simpa only [Y, Q] using h
  have hrate : Tendsto (fun n : ℕ => (n : ℝ) * (X n - c)) atTop (𝓝 0) := by
    have h := linear_ratio_remainder_mul_tendsto (A := A) (B := B) (α := α)
      (β := β) (γ := γ) (δ := δ) (r := r) hA hr
    simpa only [X, M, hm, hc] using h
  have hXsq : Tendsto (fun n : ℕ => X n ^ 2) atTop (𝓝 (c ^ 2)) := by
    simpa only [pow_two] using hX.mul hX
  have hmc : Tendsto (fun n : ℕ =>
      (2 * m) * ((n : ℝ) * (X n - c))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds (f := atTop) (x := 2 * m)).mul hrate
  have hrest : Tendsto (fun n : ℕ =>
      Y n + X n - X n ^ 2 - (2 * m) * ((n : ℝ) * (X n - c)))
      atTop (𝓝 (κ / A + c - c ^ 2)) := by
    simpa only [sub_zero, add_zero] using ((hY.add hX).sub hXsq).sub hmc
  have halg : ∀ n : ℕ, Q n + M n - M n ^ 2 - σ * (n : ℝ) =
      Y n + X n - X n ^ 2 - (2 * m) * ((n : ℝ) * (X n - c)) := by
    intro n
    dsimp [X, Y]
    rw [hquad, hsigma]
    ring
  have heq :
      (fun n : ℕ =>
        Y n + X n - X n ^ 2 - (2 * m) * ((n : ℝ) * (X n - c))) =ᶠ[atTop]
      (fun n : ℕ => Q n + M n - M n ^ 2 - σ * (n : ℝ)) :=
    Filter.Eventually.of_forall fun n => (halg n).symm
  change Tendsto (fun n : ℕ => Q n + M n - M n ^ 2 - σ * (n : ℝ)) atTop
    (𝓝 (κ / A + c - c ^ 2))
  exact hrest.congr' heq


/-- Divide a sequence with a linear asymptotic by its index. -/
theorem tendsto_div_nat_of_tendsto_sub_linear {f : ℕ → ℝ} {m c : ℝ}
    (h : Tendsto (fun n => f n - m * (n : ℝ)) atTop (𝓝 c)) :
    Tendsto (fun n => f n / (n : ℝ)) atTop (𝓝 m) := by
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hprod : Tendsto (fun n : ℕ =>
      (f n - m * (n : ℝ)) * (n : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa only [mul_zero] using h.mul hinv
  have heq : ∀ᶠ n : ℕ in atTop,
      f n / (n : ℝ) = (f n - m * (n : ℝ)) * (n : ℝ)⁻¹ + m := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hn)
    field_simp [hn']
    ring
  have hsum : Tendsto (fun n : ℕ =>
      (f n - m * (n : ℝ)) * (n : ℝ)⁻¹ + m) atTop (𝓝 m) := by
    simpa only [zero_add] using
      hprod.add (tendsto_const_nhds (f := atTop) (x := m))
  have heq' :
      (fun n : ℕ => (f n - m * (n : ℝ)) * (n : ℝ)⁻¹ + m) =ᶠ[atTop]
      (fun n : ℕ => f n / (n : ℝ)) := heq.mono fun _ h => h.symm
  exact hsum.congr' heq'

private theorem mode_eq_of_quadratic_recurrence {p q : ℝ} {S T : ℕ → ℝ}
    (hS : ∀ n : ℕ, S (n + 2) = p * S (n + 1) + q * S n)
    (hT : ∀ n : ℕ, T (n + 2) = p * T (n + 1) + q * T n)
    (h0 : S 0 = T 0) (h1 : S 1 = T 1) :
    ∀ n, S n = T n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => exact h0
  | one => exact h1
  | more n ih0 ih1 =>
      rw [hS n, hT n, ih0, ih1]

/-- A solution of `S (n+2) = p S (n+1) + q S n` is `A rⁿ + B sⁿ` for the distinct roots `r, s`. -/
theorem two_mode_solution {p q r s A B : ℝ} {S : ℕ → ℝ}
    (hS : ∀ n : ℕ, S (n + 2) = p * S (n + 1) + q * S n)
    (hsum : r + s = p) (hprod : r * s = -q)
    (h0 : S 0 = A + B) (h1 : S 1 = A * r + B * s) :
    ∀ n, S n = A * r ^ n + B * s ^ n := by
  let T : ℕ → ℝ := fun n => A * r ^ n + B * s ^ n
  have hr : r ^ 2 = p * r + q := by
    linear_combination r * hsum - hprod
  have hs : s ^ 2 = p * s + q := by
    linear_combination s * hsum - hprod
  have hT : ∀ n : ℕ, T (n + 2) = p * T (n + 1) + q * T n := by
    intro n
    dsimp [T]
    simp only [pow_succ]
    linear_combination A * r ^ n * hr + B * s ^ n * hs
  exact mode_eq_of_quadratic_recurrence hS hT (by simpa [T] using h0)
    (by simpa [T] using h1)

/-- A recurrence forced by a two-mode sequence has a solution `(α n + β) rⁿ + (γ n + δ) sⁿ`. -/
theorem forced_linear_two_mode_solution {S T : ℕ → ℝ}
    {p q r s u v A B α β γ δ : ℝ}
    (hT : ∀ n : ℕ, T (n + 2) =
      p * T (n + 1) + q * T n + u * S (n + 1) + v * S n)
    (hsum : r + s = p) (hprod : r * s = -q)
    (hSform : ∀ n : ℕ, S n = A * r ^ n + B * s ^ n)
    (hα : α * r * (2 * r - p) = A * (u * r + v))
    (hγ : γ * s * (2 * s - p) = B * (u * s + v))
    (h0 : T 0 = β + δ)
    (h1 : T 1 = (α + β) * r + (γ + δ) * s) :
    ∀ n, T n = (α * (n : ℝ) + β) * r ^ n +
      (γ * (n : ℝ) + δ) * s ^ n := by
  have hr : r ^ 2 = p * r + q := by
    linear_combination r * hsum - hprod
  have hs : s ^ 2 = p * s + q := by
    linear_combination s * hsum - hprod
  let C : ℕ → ℝ := fun n =>
    (α * (n : ℝ) + β) * r ^ n + (γ * (n : ℝ) + δ) * s ^ n
  have hC : ∀ n : ℕ, C (n + 2) =
      p * C (n + 1) + q * C n + u * S (n + 1) + v * S n := by
    intro n
    dsimp [C]
    simp only [pow_succ]
    rw [hSform n, hSform (n + 1)]
    push_cast
    ring_nf
    linear_combination r ^ n * hα + s ^ n * hγ +
      α * (n : ℝ) * r ^ n * hr + β * r ^ n * hr +
      γ * (n : ℝ) * s ^ n * hs + δ * s ^ n * hs
  intro n
  induction n using Nat.twoStepInduction with
  | zero => change T 0 = C 0; simpa [C] using h0
  | one => change T 1 = C 1; simpa [C] using h1
  | more n ih0 ih1 =>
      change T (n + 2) = C (n + 2)
      rw [hT n, hC n, ih0, ih1]

/-- The doubly forced recurrence has a solution with quadratic-in-`n` mode coefficients. -/
theorem forced_quadratic_two_mode_solution {S T U : ℕ → ℝ}
    {p q r s u v u₂ v₂ A B α β γ δ η θ κ ζ ξ χ : ℝ}
    (hU : ∀ n : ℕ, U (n + 2) =
      p * U (n + 1) + q * U n + u₂ * S (n + 1) + 2 * u * T (n + 1) +
        v₂ * S n + 2 * v * T n)
    (hsum : r + s = p) (hprod : r * s = -q)
    (hSform : ∀ n : ℕ, S n = A * r ^ n + B * s ^ n)
    (hTform : ∀ n : ℕ, T n = (α * (n : ℝ) + β) * r ^ n +
      (γ * (n : ℝ) + δ) * s ^ n)
    (hη : η * r * (2 * r - p) = α * (u * r + v))
    (hθ : η * r * (4 * r - p) + θ * r * (2 * r - p) =
      A * (u₂ * r + v₂) + 2 * u * r * (α + β) + 2 * v * β)
    (hζ : ζ * s * (2 * s - p) = γ * (u * s + v))
    (hξ : ζ * s * (4 * s - p) + ξ * s * (2 * s - p) =
      B * (u₂ * s + v₂) + 2 * u * s * (γ + δ) + 2 * v * δ)
    (h0 : U 0 = κ + χ)
    (h1 : U 1 = (η + θ + κ) * r + (ζ + ξ + χ) * s) :
    ∀ n, U n = (η * (n : ℝ) ^ 2 + θ * (n : ℝ) + κ) * r ^ n +
      (ζ * (n : ℝ) ^ 2 + ξ * (n : ℝ) + χ) * s ^ n := by
  have hr : r ^ 2 = p * r + q := by
    linear_combination r * hsum - hprod
  have hs : s ^ 2 = p * s + q := by
    linear_combination s * hsum - hprod
  let C : ℕ → ℝ := fun n =>
    (η * (n : ℝ) ^ 2 + θ * (n : ℝ) + κ) * r ^ n +
      (ζ * (n : ℝ) ^ 2 + ξ * (n : ℝ) + χ) * s ^ n
  have hC : ∀ n : ℕ, C (n + 2) =
      p * C (n + 1) + q * C n + u₂ * S (n + 1) + 2 * u * T (n + 1) +
        v₂ * S n + 2 * v * T n := by
    intro n
    dsimp [C]
    simp only [pow_succ]
    rw [hSform n, hSform (n + 1), hTform n, hTform (n + 1)]
    push_cast
    ring_nf
    linear_combination
      r ^ n * ((η * (n : ℝ) ^ 2 + θ * (n : ℝ) + κ) * hr +
        2 * (n : ℝ) * hη + hθ) +
      s ^ n * ((ζ * (n : ℝ) ^ 2 + ξ * (n : ℝ) + χ) * hs +
        2 * (n : ℝ) * hζ + hξ)
  intro n
  induction n using Nat.twoStepInduction with
  | zero => change U 0 = C 0; simpa [C] using h0
  | one => change U 1 = C 1; simpa [C] using h1
  | more n ih0 ih1 =>
      change U (n + 2) = C (n + 2)
      rw [hU n, hC n, ih0, ih1]

/-- The constants `β, δ` of a linear two-mode form are fixed by the first two values. -/
theorem two_mode_linear_initial_values {r s α β γ δ T0 T1 : ℝ}
    (hβ : β = (T1 - α * r - γ * s - s * T0) / (r - s))
    (hδ : δ = T0 - β) (hrs : r ≠ s) :
    T0 = β + δ ∧ T1 = (α + β) * r + (γ + δ) * s := by
  constructor
  · rw [hδ]
    ring
  · rw [hδ, hβ]
    field_simp [hrs]
    ring

/-- The constants of a quadratic two-mode form are fixed by the first two values. -/
theorem two_mode_quadratic_initial_values
    {r s η θ ζ ξ κ χ U0 U1 : ℝ}
    (hκ : κ = (U1 - (η + θ) * r - (ζ + ξ) * s - s * U0) / (r - s))
    (hχ : χ = U0 - κ) (hrs : r ≠ s) :
    U0 = κ + χ ∧ U1 = (η + θ + κ) * r + (ζ + ξ + χ) * s := by
  constructor
  · rw [hχ]
    ring
  · rw [hχ, hκ]
    field_simp [hrs]
    ring

end LinearRecurrence

namespace Polynomial

/-- Evaluating a three-term polynomial recurrence at `1`. -/
theorem eval_one_recurrence
    {P : ℕ → ℝ[X]} {a b : ℝ[X]}
    (hP : ∀ n, P (n + 2) = a * P (n + 1) + b * P n) (n : ℕ) :
    (P (n + 2)).eval 1 = a.eval 1 * (P (n + 1)).eval 1 +
      b.eval 1 * (P n).eval 1 := by
  rw [hP, eval_add, eval_mul, eval_mul]

/-- The derivative at `1` of a three-term polynomial recurrence. -/
theorem derivative_eval_one_recurrence
    {P : ℕ → ℝ[X]} {a b : ℝ[X]}
    (hP : ∀ n, P (n + 2) = a * P (n + 1) + b * P n) (n : ℕ) :
    (P (n + 2)).derivative.eval 1 =
      (a.derivative.eval 1 * (P (n + 1)).eval 1 +
        a.eval 1 * (P (n + 1)).derivative.eval 1) +
      (b.derivative.eval 1 * (P n).eval 1 +
        b.eval 1 * (P n).derivative.eval 1) := by
  rw [hP]
  simp only [derivative_add, derivative_mul, eval_add, eval_mul]

/-- The second derivative at `1` of a three-term polynomial recurrence. -/
theorem derivative_derivative_eval_one_recurrence
    {P : ℕ → ℝ[X]} {a b : ℝ[X]}
    (hP : ∀ n, P (n + 2) = a * P (n + 1) + b * P n) (n : ℕ) :
    (P (n + 2)).derivative.derivative.eval 1 =
      (a.derivative.derivative.eval 1 * (P (n + 1)).eval 1 +
        2 * a.derivative.eval 1 * (P (n + 1)).derivative.eval 1 +
        a.eval 1 * (P (n + 1)).derivative.derivative.eval 1) +
      (b.derivative.derivative.eval 1 * (P n).eval 1 +
        2 * b.derivative.eval 1 * (P n).derivative.eval 1 +
        b.eval 1 * (P n).derivative.derivative.eval 1) := by
  rw [hP, derivative_add, derivative_mul, derivative_mul]
  simp only [derivative_add, derivative_mul, eval_add, eval_mul]
  ring

end Polynomial
