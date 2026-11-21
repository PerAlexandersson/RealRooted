module

public import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# A quadratic zero-location inequality

This is the quadratic step of the Grace-apolarity proof of Theorem A in the
unpublished manuscript associated with RealRooted issue #2415:
https://github.com/PerAlexandersson/RealRooted/issues/2415.
-/

public section

namespace RealRooted.ExponentialRows

/-- Two numbers in the open lower half-plane cannot have a nonnegative real product. -/
theorem re_mul_neg_of_im_neg {u v : ℂ} (hu : u.im < 0) (hv : v.im < 0)
    (h : (u * v).im = 0) : (u * v).re < 0 := by
  have hi : u.re * v.im + u.im * v.re = 0 := by simpa [Complex.mul_im] using h
  have he : (u * v).re * u.im = -(u.re ^ 2 + u.im ^ 2) * v.im := by
    simp only [Complex.mul_re]
    linear_combination u.re * hi
  have hs : 0 < u.re ^ 2 + u.im ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero (ne_of_lt hu))
  have hp : 0 < -(u.re ^ 2 + u.im ^ 2) * v.im := mul_pos_of_neg_of_neg (neg_neg_of_pos hs) hv
  by_contra hnot
  have hn := mul_nonpos_of_nonneg_of_nonpos (le_of_not_gt hnot) hu.le
  linarith

/-- Roots of `(1 + βη)² + ν(η - γω²)` lie strictly above the line `ωℝ`
when `β, γ, ν ≥ 0` and `ω` is in the open upper half-plane. This includes `β = 0`
and `γ = 0`, so the zero-location step requires no continuity argument. -/
theorem im_mul_conj_pos_of_quadratic_eq_zero {β γ ν : ℝ} {η ω : ℂ}
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hν : 0 ≤ ν)
    (hωi : 0 < ω.im)
    (heq : (1 + (β : ℂ) * η) ^ 2 + (ν : ℂ) * (η - (γ : ℂ) * ω ^ 2) = 0) :
    0 < (η * starRingEnd ℂ ω).im := by
  by_cases hβ0 : β = 0
  · subst β
    have hr := congrArg Complex.re heq
    have hi := congrArg Complex.im heq
    simp only [Complex.ofReal_zero, zero_mul, add_zero, pow_two, Complex.add_re,
      Complex.add_im, Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im,
      Complex.zero_re, Complex.zero_im, mul_zero, sub_zero, zero_add] at hr hi
    have hp : 0 < (ν * γ * (ω.re ^ 2 + ω.im ^ 2) + 1) * ω.im := by positivity
    have he : ν * (η.re * -ω.im + η.im * ω.re) =
        (ν * γ * (ω.re ^ 2 + ω.im ^ 2) + 1) * ω.im := by
      linear_combination ω.re * hi - ω.im * hr
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
    nlinarith
  · let κ : ℝ := ν / β
    have hκ : 0 ≤ κ := div_nonneg hν hβ
    let δ : ℝ := Real.sqrt (κ ^ 2 + 4 * κ)
    have hδ : δ ^ 2 = κ ^ 2 + 4 * κ := Real.sq_sqrt (by positivity)
    have hδ0 : 0 ≤ δ := Real.sqrt_nonneg _
    let r : ℝ := (-κ + δ) / 2
    let s : ℝ := (-κ - δ) / 2
    have hr : r < 1 := by dsimp [r]; nlinarith
    have hs : s < 1 := by dsimp [s]; nlinarith
    have hrs : r + s = -κ := by dsimp [r, s]; ring
    have hrsm : r * s = -κ := by dsimp [r, s]; nlinarith
    let ζ : ℂ := 1 + (β : ℂ) * η
    have hκβ : κ * β = ν := div_mul_cancel₀ ν hβ0
    have hz : ζ ^ 2 + (κ : ℂ) * ζ - (κ : ℂ) = (ν * γ : ℝ) * ω ^ 2 := by
      dsimp [ζ]
      have hk : (κ : ℂ) * (β : ℂ) = (ν : ℂ) := by exact_mod_cast hκβ
      push_cast
      linear_combination heq + η * hk
    let A := (ζ - (r : ℂ)) * starRingEnd ℂ ω
    let B := (ζ - (s : ℂ)) * starRingEnd ℂ ω
    have hab : A * B = ((ν * γ : ℝ) : ℂ) * (ω * starRingEnd ℂ ω) ^ 2 := by
      have ha : (r : ℂ) + (s : ℂ) = -(κ : ℂ) := by exact_mod_cast hrs
      have hb : (r : ℂ) * (s : ℂ) = -(κ : ℂ) := by exact_mod_cast hrsm
      dsimp [A, B]
      linear_combination (starRingEnd ℂ ω) ^ 2 * hz -
        ζ * (starRingEnd ℂ ω) ^ 2 * ha + (starRingEnd ℂ ω) ^ 2 * hb
    by_contra h
    have hy : (η * starRingEnd ℂ ω).im ≤ 0 := le_of_not_gt h
    have hA : A.im < 0 := by
      dsimp [A, ζ]
      simp only [Complex.mul_im, Complex.sub_im, Complex.add_im, Complex.one_im,
        Complex.ofReal_im, Complex.ofReal_re, Complex.mul_re, Complex.add_re,
        Complex.one_re, Complex.sub_re, Complex.conj_im, Complex.conj_re,
        zero_mul, sub_zero, zero_add] at hy ⊢
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hβ hy,
        mul_pos (sub_pos.mpr hr) hωi]
    have hB : B.im < 0 := by
      dsimp [B, ζ]
      simp only [Complex.mul_im, Complex.sub_im, Complex.add_im, Complex.one_im,
        Complex.ofReal_im, Complex.ofReal_re, Complex.mul_re, Complex.add_re,
        Complex.one_re, Complex.sub_re, Complex.conj_im, Complex.conj_re,
        zero_mul, sub_zero, zero_add] at hy ⊢
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hβ hy,
        mul_pos (sub_pos.mpr hs) hωi]
    have hi : (A * B).im = 0 := by
      rw [hab, Complex.mul_conj, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
        Complex.ofReal_im]
    have hp : 0 ≤ (A * B).re := by
      rw [hab, Complex.mul_conj, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
        Complex.ofReal_re]
      exact mul_nonneg (mul_nonneg hν hγ) (sq_nonneg _)
    exact (not_lt_of_ge hp) (re_mul_neg_of_im_neg hA hB hi)

end RealRooted.ExponentialRows
