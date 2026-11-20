module

public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Algebraic identities for the Möbius flow

The parameter `s` is independent here. Substituting `s = tanh t` gives the
algebraic part of Shi's flow and paired-root identities (arXiv:2610.35783v2,
Section 2). No assertion about analytic Taylor coefficients is made here.
-/

public section

namespace RealRooted.TuranHurwitz

/-- The rational flow in the variable `s = tanh t`. -/
@[expose] noncomputable def mobiusFlow (s u : ℂ) : ℂ := (u - s) / (1 - u * s)

/-- The flow starts at `u`. -/
@[simp] theorem mobiusFlow_zero (u : ℂ) : mobiusFlow 0 u = u := by
  simp [mobiusFlow]

/-- The quadratic identity underlying the flow differential equation. -/
theorem mobiusFlow_sq_sub_one (s u : ℂ) (hne : 1 - u * s ≠ 0) :
    mobiusFlow s u ^ 2 - 1 = (u ^ 2 - 1) * (1 - s ^ 2) / (1 - u * s) ^ 2 := by
  dsimp [mobiusFlow]
  field_simp
  ring

/-- A root factor under the rational flow. -/
theorem mobiusFlow_sub (s u r : ℂ) (hne : 1 - u * s ≠ 0) :
    mobiusFlow s u - r = ((u - r) - (1 - r * u) * s) / (1 - u * s) := by
  dsimp [mobiusFlow]
  field_simp
  ring

/-- Pairing opposite flow parameters gives the kernel's quadratic factor. -/
theorem mobiusFlow_pair (s u r : ℂ) (hm : 1 - u * s ≠ 0) (hp : 1 + u * s ≠ 0) :
    (mobiusFlow s u - r) * (mobiusFlow (-s) u - r) =
      ((u - r) ^ 2 - (1 - r * u) ^ 2 * s ^ 2) / (1 - u ^ 2 * s ^ 2) := by
  have hden : 1 - u ^ 2 * s ^ 2 ≠ 0 := by
    have heq : 1 - u ^ 2 * s ^ 2 = (1 - u * s) * (1 + u * s) := by ring
    rw [heq]
    exact mul_ne_zero hm hp
  dsimp [mobiusFlow]
  simp only [mul_neg, sub_neg_eq_add]
  field_simp [hm, hp, hden]
  ring

/-- The norm-square identity controlling the paired-root parameter. -/
theorem normSq_sub_real_sub_normSq_one_sub_mul (u : ℂ) (r : ℝ) :
    Complex.normSq (u - (r : ℂ)) - Complex.normSq (1 - (r : ℂ) * u) =
      (1 - r ^ 2) * (Complex.normSq u - 1) := by
  simp [Complex.normSq_apply]
  ring

/-- A real root in `[-1, 1]` gives a paired-root parameter in the closed unit disk. -/
theorem norm_pairedRoot_le_one {u : ℂ} (hu : 1 < ‖u‖) {r : ℝ}
    (hlo : -1 ≤ r) (hhi : r ≤ 1) :
    ‖((1 - (r : ℂ) * u) / (u - (r : ℂ))) ^ 2‖ ≤ 1 := by
  have hr : ‖(r : ℂ)‖ ≤ 1 := by simpa using (abs_le.mpr ⟨hlo, hhi⟩)
  have hden : u - (r : ℂ) ≠ 0 := by
    intro heq
    have hnorm := congrArg norm (sub_eq_zero.mp heq)
    linarith
  have hid := normSq_sub_real_sub_normSq_one_sub_mul u r
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_norm_sq] at hid
  have hrr : 0 ≤ 1 - r ^ 2 := by nlinarith
  have huu : 0 ≤ ‖u‖ ^ 2 - 1 := by nlinarith
  have hle : ‖1 - (r : ℂ) * u‖ ≤ ‖u - (r : ℂ)‖ := by
    nlinarith [mul_nonneg hrr huu, norm_nonneg (1 - (r : ℂ) * u),
      norm_nonneg (u - (r : ℂ))]
  have hratio : ‖(1 - (r : ℂ) * u) / (u - (r : ℂ))‖ ≤ 1 := by
    rw [norm_div]
    exact (div_le_one (norm_pos_iff.mpr hden)).mpr hle
  rw [norm_pow]
  nlinarith [norm_nonneg ((1 - (r : ℂ) * u) / (u - (r : ℂ)))]

end RealRooted.TuranHurwitz
