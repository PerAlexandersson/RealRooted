module

public import RealRooted.EffectiveBKW.PathCube.ConjugateModes
public import RealRooted.EffectiveBKW.PathCube.PhaseGeometry
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The normalized sine formula from the rational residues
-/

@[expose] public section

namespace RealRooted.EffectiveBKW.PathCube.RationalSeries

/-- The rational amplitude of the conjugate pair, before the sine normalization. -/
noncomputable def rationalAmplitude (a c x y u v w : ℝ) : ℂ :=
  (cubicPolynomial u v w).eval ((a : ℂ) + c * Complex.I)⁻¹ /
    ((1 - (x : ℂ) * ((a : ℂ) + c * Complex.I)⁻¹) *
      (1 - (y : ℂ) * ((a : ℂ) + c * Complex.I)⁻¹))

/-- The interpolation residue equals the rational amplitude divided by the pair factor. -/
theorem residue_zero_eq {a c x y u v w : ℝ}
    (hz : (a : ℂ) + c * Complex.I ≠ 0) :
    residue (normalizedRoots a c x y) (cubicPolynomial u v w) 0 =
      rationalAmplitude a c x y u v w * ((a : ℂ) + c * Complex.I) /
        (((a : ℂ) + c * Complex.I) - ((a : ℂ) - c * Complex.I)) := by
  have hpair : 1 - ((a : ℂ) - c * Complex.I) * ((a : ℂ) + c * Complex.I)⁻¹ =
      (((a : ℂ) + c * Complex.I) - ((a : ℂ) - c * Complex.I)) /
        ((a : ℂ) + c * Complex.I) := by
    field_simp
  have hcof : (cofactorPolynomial (normalizedRoots a c x y) 0).eval
      ((a : ℂ) + c * Complex.I)⁻¹ =
      (1 - ((a : ℂ) - c * Complex.I) * ((a : ℂ) + c * Complex.I)⁻¹) *
        ((1 - (x : ℂ) * ((a : ℂ) + c * Complex.I)⁻¹) *
          (1 - (y : ℂ) * ((a : ℂ) + c * Complex.I)⁻¹)) := by
    simp [cofactorPolynomial, normalizedRoots, linearPolynomial, Fin.prod_univ_succ]
  unfold residue
  change (cubicPolynomial u v w).eval ((a : ℂ) + c * Complex.I)⁻¹ /
    (cofactorPolynomial (normalizedRoots a c x y) 0).eval
      ((a : ℂ) + c * Complex.I)⁻¹ = _
  rw [hcof, mul_comm (1 - ((a : ℂ) - c * Complex.I) *
    ((a : ℂ) + c * Complex.I)⁻¹), div_mul_eq_div_div, hpair, div_div_eq_mul_div]
  rfl

private theorem unit_root_polar {a c : ℝ} (hu : a ^ 2 + c ^ 2 = 1) (hc : 0 < c) :
    Complex.exp ((Real.arccos a : ℂ) * Complex.I) = (a : ℂ) + c * Complex.I := by
  let z : ℂ := (a : ℂ) + c * Complex.I
  have hn : ‖z‖ = 1 := by
    rw [Complex.norm_def]
    have hs : Complex.normSq z = 1 := by
      simp only [z, Complex.normSq_apply, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_im, Complex.mul_im]
      nlinarith
    rw [hs, Real.sqrt_one]
  have hi : 0 < z.im := by simpa [z] using hc
  have harg := Complex.arg_of_im_pos hi
  have he := Complex.norm_mul_exp_arg_mul_I z
  rw [hn] at he
  simp only [Complex.ofReal_one, one_mul] at he
  simpa [harg, hn, z] using he

/-- Multiplying the paired residue contribution by the normalized sine gives its exact phase. -/
theorem pair_sine_identity {a c x y u v w : ℝ}
    (hu : a ^ 2 + c ^ 2 = 1) (hc : 0 < c)
    (hne : rationalAmplitude a c x y u v w ≠ 0)
    (him : (rationalAmplitude a c x y u v w).im ≤ 0) (n : ℕ) :
    2 * c * (residue (normalizedRoots a c x y) (cubicPolynomial u v w) 0 *
      ((a : ℂ) + c * Complex.I) ^ n).re =
    ‖rationalAmplitude a c x y u v w‖ *
      Real.sin (((n : ℝ) + 1) * Real.arccos a +
        lowerPhase (rationalAmplitude a c x y u v w)) := by
  let z : ℂ := (a : ℂ) + c * Complex.I
  let F := rationalAmplitude a c x y u v w
  have hz : z ≠ 0 := by
    intro he
    have hi := congrArg Complex.im he
    simp [z] at hi
    linarith
  have hden : z - ((a : ℂ) - c * Complex.I) = (2 * c : ℝ) * Complex.I := by
    dsimp [z]
    push_cast
    ring
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hcomplex : (2 * c : ℝ) *
      (residue (normalizedRoots a c x y) (cubicPolynomial u v w) 0 * z ^ n) =
      -Complex.I * (F * z ^ (n + 1)) := by
    rw [residue_zero_eq hz]
    change (2 * c : ℝ) * (F * z / (z - ((a : ℂ) - c * Complex.I)) * z ^ n) = _
    rw [hden, pow_succ]
    field_simp
    ring_nf
    simp
  have hp : F * z ^ (n + 1) = (‖F‖ : ℂ) * Complex.exp
      (((((n : ℝ) + 1) * Real.arccos a + lowerPhase F : ℝ) : ℂ) * Complex.I) := by
    calc
      _ = (‖F‖ : ℂ) * Complex.exp ((lowerPhase F : ℂ) * Complex.I) *
          Complex.exp ((Real.arccos a : ℂ) * Complex.I) ^ (n + 1) :=
        congrArg₂ (fun p q : ℂ ↦ p * q) (lowerPhase_polar hne him).symm
          (congrArg (fun q : ℂ ↦ q ^ (n + 1)) (unit_root_polar hu hc).symm)
      _ = _ := by
        rw [← Complex.exp_nat_mul, mul_assoc, ← Complex.exp_add]
        apply congrArg (fun q : ℂ ↦ (‖F‖ : ℂ) * Complex.exp q)
        push_cast
        ring
  have hr := congrArg Complex.re hcomplex
  rw [hp] at hr
  simpa only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero,
    one_mul, neg_one_mul, sub_zero, zero_sub, neg_neg, neg_zero, add_zero,
    Complex.exp_ofReal_mul_I_im,
    z, F] using hr

end RealRooted.EffectiveBKW.PathCube.RationalSeries
