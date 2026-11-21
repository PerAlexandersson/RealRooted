module

public import RealRooted.EffectiveBKW.PairExpansion
public import RealRooted.EffectiveBKW.QuadraticInverse
public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Splits
import RealRooted.EffectiveBKW.ZeroCount
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The Chebyshev test of effective BKW

We construct the exact zero-remainder pair for `Uₙ` on `(-1,1)` and obtain splitting,
simple roots, and root localization through the general phase theorem. The generating
function identity identifies this family with `1 / (1 - 2tz + z²)`.
-/

@[expose] public section

open Set

namespace RealRooted.EffectiveBKW.Examples.Chebyshev

open Polynomial

/-- The second-kind Chebyshev family, using Mathlib's canonical generator. -/
noncomputable def row (n : ℕ) : Polynomial ℝ := Polynomial.Chebyshev.U ℝ n

/-- Positive scalar in the dominant amplitude. -/
noncomputable def scale (t : ℝ) : ℝ := (2 * Real.sin (Real.arccos t))⁻¹

/-- The upper-half-plane eigenvalue on `(-1,1)`. -/
noncomputable def lam (t : ℝ) : ℂ :=
  Complex.exp ((Real.arccos t : ℂ) * Complex.I)

/-- Exact dominant amplitude for the second-kind family. -/
noncomputable def amplitude (t : ℝ) : ℂ :=
  (scale t : ℂ) * Complex.exp (((Real.arccos t - Real.pi / 2 : ℝ) : ℂ) * Complex.I)

private theorem sin_pos {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    0 < Real.sin (Real.arccos t) :=
  Real.sin_pos_of_pos_of_lt_pi (Real.arccos_pos.mpr ht.2) (Real.arccos_lt_pi.mpr ht.1)

private theorem scale_pos {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) : 0 < scale t :=
  inv_pos.mpr (mul_pos (by norm_num) (sin_pos ht))

private theorem norm_lam (t : ℝ) : ‖lam t‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

private theorem norm_amplitude {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    ‖amplitude t‖ = scale t := by
  simp only [amplitude, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_exp_ofReal_mul_I, mul_one, abs_of_pos (scale_pos ht)]

private theorem term_eq (n : ℕ) (t : ℝ) :
    amplitude t * lam t ^ n = (scale t : ℂ) *
      Complex.exp (((((n : ℝ) + 1) * Real.arccos t - Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
  simp only [amplitude, lam]
  rw [mul_assoc, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 2
  push_cast
  ring

private theorem term_re (n : ℕ) (t : ℝ) :
    (amplitude t * lam t ^ n).re =
      scale t * Real.cos (((n : ℝ) + 1) * Real.arccos t - Real.pi / 2) := by
  rw [term_eq]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.exp_ofReal_mul_I_re]

private theorem continuous_lam : Continuous lam := by
  unfold lam
  fun_prop

private theorem continuousOn_amplitude : ContinuousOn amplitude (Ioo (-1 : ℝ) 1) := by
  have hs : ContinuousOn scale (Ioo (-1 : ℝ) 1) := by
    apply ContinuousOn.inv₀
      ((continuous_const.mul (Real.continuous_sin.comp Real.continuous_arccos)).continuousOn)
    intro t ht
    exact ne_of_gt (mul_pos (by norm_num) (sin_pos ht))
  unfold amplitude
  exact (Complex.continuous_ofReal.comp_continuousOn hs).mul
    (by fun_prop)

private theorem row_eval (n : ℕ) {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    (row n).eval t = 2 * (amplitude t * lam t ^ n).re := by
  have hu := Polynomial.Chebyshev.U_real_cos (Real.arccos t) (n : ℤ)
  rw [Real.cos_arccos ht.1.le ht.2.le] at hu
  rw [term_re, Real.cos_sub_pi_div_two]
  dsimp [row, scale]
  push_cast at hu
  have hs : Real.sin (Real.arccos t) ≠ 0 := (sin_pos ht).ne'
  field_simp
  nlinarith [hu]

/-- Exact order-two expansion with no remainder and starting index zero. -/
noncomputable def expansion : PairExpansion row (Ioo (-1 : ℝ) 1) where
  first := 0
  lam := lam
  amplitude := amplitude
  rest := fun _ _ ↦ 0
  continuousOn_lam := by exact continuous_lam.continuousOn
  continuousOn_amplitude := by exact continuousOn_amplitude
  im_pos := by
    intro t ht
    simpa [lam] using sin_pos ht
  amplitude_ne_zero := by
    intro t ht
    exact norm_pos_iff.mp (by rw [norm_amplitude ht]; exact scale_pos ht)
  expand := by
    intro n _ t ht
    simpa using row_eval n ht

/-- The exact order-two pair is dominated at every index, including zero. -/
theorem dom : expansion.Dom (Ioo (-1 : ℝ) 1) 0 :=
  expansion.dom_of_rest_eq_zero (fun _ ht ↦ ht) (by intros; rfl)

private theorem cos_mem {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) Real.pi) :
    Real.cos θ ∈ Ioo (-1 : ℝ) 1 := by
  constructor
  · simpa using Real.cos_lt_cos_of_nonneg_of_le_pi hθ.1.le le_rfl hθ.2
  · simpa using Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hθ.2.le hθ.1

/-- The general effective BKW theorem proves all Chebyshev rows split, have no repeated
roots, and have every root in `(-1,1)`. No Chebyshev root theorem is used. -/
theorem splits_nodup (n : ℕ) :
    (row n).Splits ∧ (row n).roots.Nodup ∧ ∀ z ∈ (row n).roots, z ∈ Ioo (-1 : ℝ) 1 := by
  let ε : ℝ := Real.pi / (4 * ((n : ℝ) + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have heq : ((n : ℝ) + 1) * ε = Real.pi / 4 := by
    dsimp [ε]
    field_simp
  have hεlt : ε < Real.pi / 2 := by
    have := mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hε.le
    nlinarith [Real.pi_pos]
  have hθa : Real.pi - ε ∈ Ioo (0 : ℝ) Real.pi := by constructor <;> linarith
  have hθb : ε ∈ Ioo (0 : ℝ) Real.pi := by constructor <;> linarith
  let φ : ℝ → ℝ := fun t ↦ ((n : ℝ) + 1) * Real.arccos t - Real.pi / 2
  have hφ : ContinuousOn φ (Ioo (-1 : ℝ) 1) := by dsimp [φ]; fun_prop
  have hp : ∀ t ∈ Ioo (-1 : ℝ) 1,
      (expansion.amplitude t * expansion.lam t ^ n).re =
        (‖expansion.amplitude t‖ * ‖expansion.lam t‖ ^ n) * Real.cos (φ t) := by
    intro t ht
    change (amplitude t * lam t ^ n).re =
      (‖amplitude t‖ * ‖lam t‖ ^ n) * Real.cos (φ t)
    rw [norm_amplitude ht, norm_lam, one_pow, mul_one]
    exact term_re n t
  have hab : Real.cos (Real.pi - ε) < Real.cos ε :=
    Real.cos_lt_cos_of_nonneg_of_le_pi hε.le hθa.2.le (by linarith)
  have hlo : φ (Real.cos ε) < (0 : ℝ) * Real.pi := by
    dsimp [φ]
    rw [Real.arccos_cos hθb.1.le hθb.2.le]
    nlinarith [Real.pi_pos]
  have hhi : ((0 : ℝ) + n) * Real.pi < φ (Real.cos (Real.pi - ε)) := by
    dsimp [φ]
    rw [Real.arccos_cos hθa.1.le hθa.2.le]
    nlinarith [Real.pi_pos]
  have hdegree : (row n).natDegree ≤ n := by
    exact (Polynomial.Chebyshev.natDegree_U_natCast (R := ℝ) n).le
  exact (expansion.splits_nodup (L := 0) (K := n) (N := 0) inferInstance
    (Nat.zero_le n) dom (Nat.zero_le n) hφ hp (cos_mem hθa) (cos_mem hθb)
    hab (by simpa only [Int.cast_zero] using hlo)
    (by simpa only [Int.cast_zero] using hhi) hdegree).2

/-- The rows agree with the coefficients of the inverse dominant quadratic. -/
theorem eval_eq_coeff_quadraticInverse (n : ℕ) (t : ℝ) :
    (row n).eval t = PowerSeries.coeff n (quadraticInverse t 1) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [row]
  | one => simp [row, Polynomial.Chebyshev.U_one]
  | more n ih₀ ih₁ =>
      have hU := Polynomial.Chebyshev.U_add_two ℝ (n : ℤ)
      have hr : row (n + 2) = 2 * Polynomial.X * row (n + 1) - row n := by
        simpa only [row, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using hU
      rw [hr, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul]
      simp only [Polynomial.eval_ofNat, Polynomial.eval_X, ih₀, ih₁]
      rw [coeff_quadraticInverse_add_two]
      ring

/-- Formal generating-function identity `Σ Uₙ(t)zⁿ = 1/(1 - 2tz + z²)`. -/
theorem generating_function (t : ℝ) :
    quadratic t 1 * PowerSeries.mk (fun n ↦ (row n).eval t) = 1 := by
  have hseries : PowerSeries.mk (fun n ↦ (row n).eval t) = quadraticInverse t 1 := by
    ext n
    simpa using eval_eq_coeff_quadraticInverse n t
  rw [hseries, quadratic_mul_quadraticInverse]

end RealRooted.EffectiveBKW.Examples.Chebyshev
