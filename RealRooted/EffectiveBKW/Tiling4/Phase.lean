module

public import RealRooted.EffectiveBKW.Tiling4.Branch
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import RealRooted.EffectiveBKW.Tiling4.Domination
import RealRooted.EffectiveBKW.Phase
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!+# The continuous tiling phase and its sample signs

The upper-half-plane eigenvalue and the positive real part of the amplitude
keep both arguments continuous on the whole ray. `EdgePhase` supplies the
endpoint bounds used to construct the finite phase witnesses below.
-/

@[expose] public section

open Set

namespace RealRooted.EffectiveBKW.Tiling4

/-- The unwrapped phase of the dominant term at index `n`. -/
noncomputable def phase (n : ℕ) (t : ℝ) : ℝ :=
  (n : ℝ) * Complex.arg (eigenvalue t (realRoot t)) +
    Complex.arg (amplitude t (realRoot t))

/-- The dominant amplitude lies in the open right half-plane on the pair ray. -/
theorem amplitude_re_pos {t : ℝ} (ht : t < rightEdge) :
    0 < (amplitude t (realRoot t)).re := by
  have h := thirdAmplitude_lt_one (pairImagSq_realRoot_pos ht)
    (realCondition_realRoot_pos (ht.trans rightEdge_neg))
  change 0 < (1 - thirdAmplitude t (realRoot t)) / 2
  linarith

/-- The chosen phase is continuous throughout the entire pair ray. -/
theorem continuousOn_phase (n : ℕ) : ContinuousOn (phase n) (Iio rightEdge) := by
  have hl := expansion.continuousOn_lam
  have hA := expansion.continuousOn_amplitude
  have hθ : ContinuousOn (fun t ↦ Complex.arg (eigenvalue t (realRoot t))) (Iio rightEdge) := by
    intro t ht
    apply (Complex.continuousAt_arg (Or.inr ?_)).comp_continuousWithinAt (hl t ht)
    exact (pairImag_pos (pairImagSq_realRoot_pos ht)).ne'
  have hδ : ContinuousOn (fun t ↦ Complex.arg (amplitude t (realRoot t))) (Iio rightEdge) := by
    intro t ht
    have hc : ContinuousWithinAt (fun u ↦ amplitude u (realRoot u)) (Iio rightEdge) t :=
      hA t ht
    exact (Complex.continuousAt_arg (Or.inl (amplitude_re_pos ht))).comp_continuousWithinAt
      (f := fun u ↦ amplitude u (realRoot u)) hc
  exact hθ.const_mul (n : ℝ) |>.add hδ

private theorem term_polar (n : ℕ) (t : ℝ) :
    amplitude t (realRoot t) * eigenvalue t (realRoot t) ^ n =
      (‖amplitude t (realRoot t)‖ * ‖eigenvalue t (realRoot t)‖ ^ n : ℝ) *
        Complex.exp ((phase n t : ℂ) * Complex.I) := by
  let A := amplitude t (realRoot t)
  let z := eigenvalue t (realRoot t)
  change A * z ^ n = (‖A‖ * ‖z‖ ^ n : ℝ) * Complex.exp ((phase n t : ℂ) * Complex.I)
  calc
    A * z ^ n = (‖A‖ * Complex.exp ((Complex.arg A : ℂ) * Complex.I)) *
        (‖z‖ * Complex.exp ((Complex.arg z : ℂ) * Complex.I)) ^ n := by
      rw [Complex.norm_mul_exp_arg_mul_I, Complex.norm_mul_exp_arg_mul_I]
    _ = (‖A‖ * ‖z‖ ^ n : ℝ) *
        (Complex.exp ((Complex.arg A : ℂ) * Complex.I) *
          Complex.exp ((Complex.arg z : ℂ) * Complex.I) ^ n) := by
      push_cast
      rw [mul_pow]
      ring
    _ = _ := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 2
      dsimp [phase, A, z]
      push_cast
      ring

/-- The phase gives the real cosine identity consumed by effective BKW. -/
theorem term_re_eq_norm_mul_cos (n : ℕ) (t : ℝ) :
    (amplitude t (realRoot t) * eigenvalue t (realRoot t) ^ n).re =
      (‖amplitude t (realRoot t)‖ * ‖eigenvalue t (realRoot t)‖ ^ n) *
        Real.cos (phase n t) := by
  apply expansion.re_eq_norm_mul_cos_of_polar
  simpa only [expansion, pairExpansion, norm_mul, norm_pow] using term_polar n t

/-- Finite phase witnesses give the ordered alternating samples at every positive index. -/
theorem exists_alternating (k : ℕ) {a b : ℝ} (ha : a < rightEdge) (hb : b < rightEdge)
    (hab : a < b) (hlo : phase (k + 1) b < 0)
    (hhi : (k : ℝ) * Real.pi < phase (k + 1) a) :
    ∃ s : Fin (k + 1) → ℝ, StrictAnti s ∧ (∀ j, s j < rightEdge) ∧
      ∀ j, 0 < (-1 : ℝ) ^ j.val * (polynomial (k + 1)).eval (s j) := by
  have h := expansion.exists_alternating (L := 0) (K := k) (N := 1) inferInstance
    (by simp [expansion, pairExpansion]) expansion_dom (by lia) (continuousOn_phase (k + 1))
    (fun t _ ↦ term_re_eq_norm_mul_cos (k + 1) t) ha hb hab
    (by simpa using hlo) (by simpa using hhi)
  simpa using h

end RealRooted.EffectiveBKW.Tiling4
