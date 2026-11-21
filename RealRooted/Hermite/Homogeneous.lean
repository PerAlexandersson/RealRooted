module

public import RealRooted.Hermite.Basic
public import Mathlib.Basic.Complex.Basic
import RealRooted.Hermite.Roots
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

/-!
# Homogeneous Hermite polynomials

The normalization is `Hₙ(x,s) = n! [zⁿ] exp(xz + sz²)`. We use its three-term
recurrence over arbitrary commutative rings. The zero-location characterization is
used in the unpublished Grace-apolarity proof of RealRooted issue #2415:
https://github.com/PerAlexandersson/RealRooted/issues/2415.
-/

@[expose] public section

open Polynomial

namespace RealRooted

/-- The homogeneous Hermite polynomial, with quadratic exponential parameter `s`. -/
def hermiteHomogeneous {R : Type*} [CommRing R] (x s : R) : ℕ → R
  | 0 => 1
  | 1 => x
  | n + 2 => x * hermiteHomogeneous x s (n + 1) +
      2 * (n + 1 : ℕ) * s * hermiteHomogeneous x s n

/-- The zeroth homogeneous Hermite polynomial is one. -/
@[simp] theorem hermiteHomogeneous_zero {R : Type*} [CommRing R] (x s : R) :
    hermiteHomogeneous x s 0 = 1 := rfl

/-- The first homogeneous Hermite polynomial is the linear argument. -/
@[simp] theorem hermiteHomogeneous_one {R : Type*} [CommRing R] (x s : R) :
    hermiteHomogeneous x s 1 = x := rfl

/-- The homogeneous Hermite three-term recurrence. -/
theorem hermiteHomogeneous_add_two {R : Type*} [CommRing R] (x s : R) (n : ℕ) :
    hermiteHomogeneous x s (n + 2) = x * hermiteHomogeneous x s (n + 1) +
      2 * (n + 1 : ℕ) * s * hermiteHomogeneous x s n := rfl

/-- A ring homomorphism commutes with homogeneous Hermite polynomials. -/
theorem map_hermiteHomogeneous {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (x s : R) (n : ℕ) :
    f (hermiteHomogeneous x s n) = hermiteHomogeneous (f x) (f s) n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih ih' => simp [hermiteHomogeneous_add_two, ih, ih', map_ofNat]

/-- Setting the quadratic parameter to zero gives a power. -/
@[simp] theorem hermiteHomogeneous_zero_right {R : Type*} [CommRing R] (x : R) (n : ℕ) :
    hermiteHomogeneous x 0 n = x ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih ih' => simp [hermiteHomogeneous_add_two, ih', pow_succ, mul_comm]

/-- Evaluation in the linear variable commutes with homogeneous Hermite polynomials. -/
theorem eval_hermiteHomogeneous {R : Type*} [CommRing R] (x s : R) (n : ℕ) :
    (hermiteHomogeneous X (C s) n).eval x = hermiteHomogeneous x s n := by
  simpa using map_hermiteHomogeneous (evalRingHom x) X (C s) n

/-- Scaling the linear argument by a square root of `-2s` recovers the classical
probabilists' Hermite polynomial. The identity also holds when the scale is zero. -/
theorem hermiteHomogeneous_mul {w s : ℂ} (hw : w ^ 2 = -2 * s) (z : ℂ) (n : ℕ) :
    hermiteHomogeneous (w * z) s n =
      w ^ n * ((hermiteReal n).map Complex.ofRealHom).eval z := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih ih' =>
    rw [hermiteHomogeneous_add_two, ih, ih', hermiteReal_add_two]
    simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_X,
      Polynomial.map_C, eval_sub, eval_mul, eval_X, eval_C, Complex.ofRealHom_eq_coe]
    push_cast
    simp only [pow_succ]
    linear_combination (n + 1 : ℂ) * w ^ n *
      ((hermiteReal n).map Complex.ofRealHom).eval z * hw

/-- Every zero of a homogeneous Hermite polynomial satisfies `x² + νs = 0`
for some nonnegative real `ν`. This includes the degenerate parameter `s = 0`. -/
theorem exists_nonneg_sq_add_eq_zero_of_hermiteHomogeneous_eq_zero {x s : ℂ} {n : ℕ}
    (h : hermiteHomogeneous x s n = 0) :
    ∃ ν : ℝ, 0 ≤ ν ∧ x ^ 2 + (ν : ℂ) * s = 0 := by
  by_cases hs : s = 0
  · subst s
    rw [hermiteHomogeneous_zero_right] at h
    have hx : x = 0 := by
      by_cases hn : n = 0
      · simp [hn] at h
      · exact (pow_eq_zero_iff hn).mp h
    exact ⟨0, le_rfl, by simp [hx]⟩
  · obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (-2 * s) (by decide : 0 < 2)
    have hw0 : w ≠ 0 := by
      intro he
      have hws : -2 * s ≠ 0 := mul_ne_zero (by norm_num) hs
      apply hws
      rw [← hw, he]
      norm_num
    have hroot : ((hermiteReal n).map Complex.ofRealHom).IsRoot (x / w) := by
      have hh := hermiteHomogeneous_mul hw (x / w) n
      rw [mul_div_cancel₀ x hw0, h] at hh
      exact (mul_eq_zero.mp hh.symm).resolve_left (pow_ne_zero _ hw0)
    obtain ⟨r, hr⟩ := (hermiteReal_splits n).mem_range_of_isRoot (hermiteReal_ne_zero n) hroot
    have hr' : (r : ℂ) = x / w := hr
    have hx : x = w * (r : ℂ) := by rw [hr', mul_div_cancel₀ x hw0]
    refine ⟨2 * r ^ 2, by positivity, ?_⟩
    rw [hx, mul_pow, hw]
    push_cast
    ring

end RealRooted
