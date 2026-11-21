module

public import RealRooted.EffectiveBKW.PairExpansion
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Domination by exact residual amplitudes

The spectral bounds may be weak and depend on the parameter. Strict amplitude
comparison then gives cutoff zero, including near collisions of the dominant pair.
-/

public section

namespace RealRooted.EffectiveBKW

/-- Two symmetric squared bounds control the sum of absolute real amplitudes. -/
theorem abs_add_abs_lt_of_sq {a b M : ℝ} (hM : 0 ≤ M)
    (hp : (a + b) ^ 2 < M ^ 2) (hm : (a - b) ^ 2 < M ^ 2) : |a| + |b| < M := by
  rcases le_total 0 a with ha | ha
  · rcases le_total 0 b with hb | hb
    · rw [abs_of_nonneg ha, abs_of_nonneg hb]
      nlinarith
    · rw [abs_of_nonneg ha, abs_of_nonpos hb]
      nlinarith
  · rcases le_total 0 b with hb | hb
    · rw [abs_of_nonpos ha, abs_of_nonneg hb]
      nlinarith
    · rw [abs_of_nonpos ha, abs_of_nonpos hb]
      nlinarith

/-- A pointwise spectral bound controls two real exponential modes at every index. -/
theorem abs_add_mul_pow_le (a x b y R : ℝ) (hx : |x| ≤ R) (hy : |y| ≤ R) (n : ℕ) :
    |a * x ^ n + b * y ^ n| ≤ (|a| + |b|) * R ^ n := by
  calc
    _ ≤ |a * x ^ n| + |b * y ^ n| := abs_add_le _ _
    _ = |a| * |x| ^ n + |b| * |y| ^ n := by rw [abs_mul, abs_mul, abs_pow, abs_pow]
    _ ≤ |a| * R ^ n + |b| * R ^ n :=
      add_le_add (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (abs_nonneg _) hx n) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (abs_nonneg _) hy n) (abs_nonneg _))
    _ = _ := (add_mul _ _ _).symm

namespace PairExpansion

variable {P : ℕ → Polynomial ℝ} {J : Set ℝ} (h : PairExpansion P J)

/-- Two exact real modes are dominated at every index by a strictly larger pair amplitude. -/
theorem dom_of_two_real_modes {S : Set ℝ} (a x b y : ℝ → ℝ)
    (hr : ∀ n t, t ∈ S → h.rest n t = a t * x t ^ n + b t * y t ^ n)
    (hx : ∀ t ∈ S, |x t| ≤ ‖h.lam t‖)
    (hy : ∀ t ∈ S, |y t| ≤ ‖h.lam t‖)
    (ha : ∀ t ∈ S, |a t| + |b t| < 2 * ‖h.amplitude t‖)
    (hS : S ⊆ J) : h.Dom S 0 := by
  intro n _ t ht
  unfold Dominates
  rw [hr n t ht]
  exact (abs_add_mul_pow_le _ _ _ _ _ (hx t ht) (hy t ht) n).trans_lt
    (mul_lt_mul_of_pos_right (ha t ht)
      (pow_pos (norm_pos_iff.mpr (h.lam_ne_zero (hS ht))) n))

/-- Symmetric squared comparisons suffice for two real residual amplitudes.
This form avoids choosing the signs or ordering of the cofactor residues. -/
theorem dom_of_two_real_modes_of_sq {S : Set ℝ} (a x b y : ℝ → ℝ)
    (hr : ∀ n t, t ∈ S → h.rest n t = a t * x t ^ n + b t * y t ^ n)
    (hx : ∀ t ∈ S, |x t| ≤ ‖h.lam t‖)
    (hy : ∀ t ∈ S, |y t| ≤ ‖h.lam t‖)
    (hplus : ∀ t ∈ S, (a t + b t) ^ 2 < 4 * ‖h.amplitude t‖ ^ 2)
    (hminus : ∀ t ∈ S, (a t - b t) ^ 2 < 4 * ‖h.amplitude t‖ ^ 2)
    (hS : S ⊆ J) : h.Dom S 0 := by
  apply h.dom_of_two_real_modes a x b y hr hx hy ?_ hS
  intro t ht
  apply abs_add_abs_lt_of_sq (mul_nonneg (by norm_num) (norm_nonneg _))
  · nlinarith [hplus t ht]
  · nlinarith [hminus t ht]

/-- A residual conjugate pair is dominated at every index when its amplitude is smaller. -/
theorem dom_of_conjugate_modes {S : Set ℝ} (B μ : ℝ → ℂ)
    (hr : ∀ n t, t ∈ S → h.rest n t = 2 * (B t * μ t ^ n).re)
    (hμ : ∀ t ∈ S, ‖μ t‖ ≤ ‖h.lam t‖)
    (hB : ∀ t ∈ S, ‖B t‖ < ‖h.amplitude t‖)
    (hS : S ⊆ J) : h.Dom S 0 := by
  intro n _ t ht
  unfold Dominates
  rw [hr n t ht, abs_mul, Nat.abs_ofNat]
  calc
    _ ≤ 2 * (‖B t‖ * ‖μ t‖ ^ n) := by
      simpa only [norm_mul, norm_pow] using
        mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm (B t * μ t ^ n)) (by norm_num)
    _ ≤ 2 * (‖B t‖ * ‖h.lam t‖ ^ n) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hμ t ht) n) (norm_nonneg _)) (by norm_num)
    _ < _ := by
      have hp := pow_pos (norm_pos_iff.mpr (h.lam_ne_zero (hS ht))) n
      have := mul_lt_mul_of_pos_right (hB t ht) hp
      linarith

end PairExpansion
end RealRooted.EffectiveBKW
