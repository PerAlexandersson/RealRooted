module

public import RealRooted.EffectiveBKW.Tiling4.Phase
import RealRooted.EffectiveBKW.Tiling4.Domination
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!+# Phase bounds at the two ends of the tiling ray

At the finite collision we scale the amplitude by the positive imaginary part
of the eigenvalue. At infinity we normalize the eigenvalue by `-t` and use the
fixed lower bound on the amplitude argument coming from its positive real part.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace RealRooted.EffectiveBKW.Tiling4

private theorem characteristicDeriv_rightEdge_pos :
    0 < characteristicDeriv rightEdge (realRoot rightEdge) := by
  have hm := realRoot_mem rightEdge_neg
  have hb := rightEdge_mem
  by_cases hr : 0 ≤ realRoot rightEdge
  · have hp : 0 ≤ realRoot rightEdge * (realRoot rightEdge - rightEdge) :=
      mul_nonneg hr (sub_nonneg.mpr hm.1.le)
    have hR := realCondition_realRoot_pos rightEdge_neg
    dsimp [realCondition] at hR
    linarith
  · have hr0 : realRoot rightEdge ≤ 0 := le_of_not_ge hr
    have hp : (1 + rightEdge) * realRoot rightEdge ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith [hb.1]) hr0
    have ht : rightEdge * (2 + rightEdge) < 0 :=
      mul_neg_of_neg_of_pos rightEdge_neg (by linarith [hb.1])
    dsimp [characteristicDeriv]
    nlinarith [sq_nonneg (realRoot rightEdge)]

private theorem pairImagSq_rightEdge : pairImagSq rightEdge (realRoot rightEdge) = 0 := by
  have h := characteristicDeriv_sq_mul_pairImagSq (characteristic_realRoot rightEdge_neg)
  change characteristicDeriv rightEdge (realRoot rightEdge) ^ 2 *
    pairImagSq rightEdge (realRoot rightEdge) = -(rightEdge ^ 2 * edgeFunction rightEdge) at h
  rw [edgeFunction_rightEdge, mul_zero, neg_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 2 characteristicDeriv_rightEdge_pos.ne')

private theorem pairReal_rightEdge_gt :
    realRoot rightEdge < pairReal rightEdge (realRoot rightEdge) := by
  have hm := realRoot_mem rightEdge_neg
  have hb := rightEdge_mem
  dsimp [pairReal]
  linarith [hm.2, hb.1]

/-- The selected real root has a finite one-sided limit at the pair collision. -/
theorem tendsto_realRoot_rightEdge :
    Tendsto realRoot (𝓝[<] rightEdge) (𝓝 (realRoot rightEdge)) := by
  have hr := characteristic_realRoot rightEdge_neg
  have hx := pairReal_rightEdge_gt
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hs : characteristic rightEdge a < 0 := by
      rw [characteristic_eq_mul hr, pairImagSq_rightEdge, add_zero]
      exact mul_neg_of_neg_of_pos (sub_neg.mpr ha)
        (sq_pos_of_ne_zero (by linarith))
    have hc : Continuous (fun t ↦ characteristic t a) := by unfold characteristic; fun_prop
    have he : ∀ᶠ t in 𝓝 rightEdge, characteristic t a < 0 :=
      hc.continuousAt.eventually (eventually_lt_nhds hs)
    filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht hmem
    exact (characteristic_neg_iff (characteristic_realRoot (hmem.trans rightEdge_neg))
      (pairImagSq_realRoot_pos hmem) a).mp ht
  · intro b hb
    let c := min b ((realRoot rightEdge + pairReal rightEdge (realRoot rightEdge)) / 2)
    have hc0 : realRoot rightEdge < c := lt_min hb (by linarith)
    have hcx : c < pairReal rightEdge (realRoot rightEdge) :=
      (min_le_right _ _).trans_lt (by linarith)
    have hs : 0 < characteristic rightEdge c := by
      rw [characteristic_eq_mul hr, pairImagSq_rightEdge, add_zero]
      exact mul_pos (sub_pos.mpr hc0) (sq_pos_of_ne_zero (by linarith))
    have hc : Continuous (fun t ↦ characteristic t c) := by unfold characteristic; fun_prop
    have he : ∀ᶠ t in 𝓝 rightEdge, 0 < characteristic t c :=
      hc.continuousAt.eventually (eventually_gt_nhds hs)
    filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht hmem
    exact ((characteristic_pos_iff (characteristic_realRoot (hmem.trans rightEdge_neg))
      (pairImagSq_realRoot_pos hmem) c).mp ht).trans_le (min_le_left _ _)

/-- The amplitude multiplied by `2y`, which has a finite nonzero limit at the collision. -/
noncomputable def scaledAmplitude (t r : ℝ) : ℂ :=
  ⟨(1 - thirdAmplitude t r) * pairImag t r,
    (1 - thirdAmplitude t r) * pairReal t r - 1 + thirdAmplitude t r * r⟩

private theorem scaledAmplitude_im_neg :
    (scaledAmplitude rightEdge (realRoot rightEdge)).im < 0 := by
  have hI := imagCondition_realRoot_neg rightEdge_neg
  have hd := characteristicDeriv_rightEdge_pos
  have heq : imagCondition rightEdge (realRoot rightEdge) =
      2 * characteristicDeriv rightEdge (realRoot rightEdge) *
        (scaledAmplitude rightEdge (realRoot rightEdge)).im := by
    have hne := hd.ne'
    dsimp [imagCondition, realCondition, scaledAmplitude, thirdAmplitude, pairReal]
    field_simp
  rw [heq] at hI
  nlinarith

private theorem tendsto_spectral_rightEdge :
    Tendsto (fun t ↦ eigenvalue t (realRoot t)) (𝓝[<] rightEdge)
      (𝓝 (eigenvalue rightEdge (realRoot rightEdge))) := by
  have ht : Tendsto (fun t : ℝ ↦ t) (𝓝[<] rightEdge) (𝓝 rightEdge) :=
    continuousWithinAt_id
  have hp := ht.prodMk_nhds tendsto_realRoot_rightEdge
  have hx : Continuous (fun p : ℝ × ℝ ↦ pairReal p.1 p.2) := by
    dsimp [pairReal]; fun_prop
  have hy : Continuous (fun p : ℝ × ℝ ↦ pairImag p.1 p.2) := by
    dsimp [pairImag, pairImagSq, pairNormSq, pairReal]; fun_prop
  have hl := (hx.continuousAt.tendsto.comp hp).ofReal.add
    ((hy.continuousAt.tendsto.comp hp).ofReal.mul_const Complex.I)
  simpa only [Function.comp_def, eigenvalue, Complex.mk_eq_add_mul_I] using hl

private theorem tendsto_scaledAmplitude_rightEdge :
    Tendsto (fun t ↦ scaledAmplitude t (realRoot t)) (𝓝[<] rightEdge)
      (𝓝 (scaledAmplitude rightEdge (realRoot rightEdge))) := by
  have ht : Tendsto (fun t : ℝ ↦ t) (𝓝[<] rightEdge) (𝓝 rightEdge) :=
    continuousWithinAt_id
  have hp := ht.prodMk_nhds tendsto_realRoot_rightEdge
  have hd : Continuous (fun p : ℝ × ℝ ↦ characteristicDeriv p.1 p.2) := by
    dsimp [characteristicDeriv]; fun_prop
  have hnum : Continuous (fun p : ℝ × ℝ ↦ p.2 * (p.2 - p.1)) := by fun_prop
  have hC : Tendsto (fun t ↦ thirdAmplitude t (realRoot t)) (𝓝[<] rightEdge)
      (𝓝 (thirdAmplitude rightEdge (realRoot rightEdge))) :=
    (hnum.continuousAt.div hd.continuousAt characteristicDeriv_rightEdge_pos.ne').tendsto.comp hp
  have hx : Continuous (fun p : ℝ × ℝ ↦ pairReal p.1 p.2) := by
    dsimp [pairReal]; fun_prop
  have hy : Continuous (fun p : ℝ × ℝ ↦ pairImag p.1 p.2) := by
    dsimp [pairImag, pairImagSq, pairNormSq, pairReal]; fun_prop
  have hOne : Tendsto (fun _ : ℝ ↦ (1 : ℝ)) (𝓝[<] rightEdge) (𝓝 1) := tendsto_const_nhds
  have hRe := (hOne.sub hC).mul (hy.continuousAt.tendsto.comp hp)
  have hIm := (((hOne.sub hC).mul
    (hx.continuousAt.tendsto.comp hp)).sub_const 1).add (hC.mul tendsto_realRoot_rightEdge)
  have h := hRe.ofReal.add (hIm.ofReal.mul_const Complex.I)
  simpa only [Function.comp_def, scaledAmplitude, Complex.mk_eq_add_mul_I] using h

private theorem arg_scaledAmplitude {t : ℝ} (ht : t < rightEdge) :
    Complex.arg (scaledAmplitude t (realRoot t)) = Complex.arg (amplitude t (realRoot t)) := by
  have hy := pairImag_pos (pairImagSq_realRoot_pos ht)
  have hne := hy.ne'
  have heq : scaledAmplitude t (realRoot t) =
      (2 * pairImag t (realRoot t) : ℝ) * amplitude t (realRoot t) := by
    apply Complex.ext
    · simp [scaledAmplitude, amplitude, Complex.mul_re]
      ring
    · simp [scaledAmplitude, amplitude, Complex.mul_im]
      field_simp
  rw [heq]
  exact Complex.arg_real_mul _ (by positivity)

/-- The total phase tends to `-π/2` from inside the pair ray at the finite endpoint. -/
theorem tendsto_phase_rightEdge (n : ℕ) :
    Tendsto (phase n) (𝓝[<] rightEdge) (𝓝 (-(Real.pi / 2))) := by
  have hx0 : 0 < pairReal rightEdge (realRoot rightEdge) := by
    have hm := realRoot_mem rightEdge_neg
    have hb := rightEdge_mem
    dsimp [pairReal]
    linarith [hm.2, hb.1]
  have hy0 : pairImag rightEdge (realRoot rightEdge) = 0 := by
    simp [pairImag, pairImagSq_rightEdge]
  have hArgEigen := (Complex.continuousAt_arg
    (x := eigenvalue rightEdge (realRoot rightEdge)) (Or.inl hx0)).tendsto.comp
      tendsto_spectral_rightEdge
  have hArgZero : Complex.arg (eigenvalue rightEdge (realRoot rightEdge)) = 0 := by
    rw [eigenvalue, hy0]
    change Complex.arg (pairReal rightEdge (realRoot rightEdge) : ℂ) = 0
    exact Complex.arg_ofReal_of_nonneg hx0.le
  have hWarg := (Complex.continuousAt_arg
    (x := scaledAmplitude rightEdge (realRoot rightEdge))
    (Or.inr scaledAmplitude_im_neg.ne)).tendsto.comp tendsto_scaledAmplitude_rightEdge
  have hWzero : Complex.arg (scaledAmplitude rightEdge (realRoot rightEdge)) = -(Real.pi / 2) :=
    Complex.arg_eq_neg_pi_div_two_iff.mpr
      ⟨by simp [scaledAmplitude, hy0], scaledAmplitude_im_neg⟩
  rw [hArgZero] at hArgEigen
  rw [hWzero] at hWarg
  have hmem : ∀ᶠ t in 𝓝[<] rightEdge, t < rightEdge := self_mem_nhdsWithin
  have hAarg : Tendsto (fun t ↦ Complex.arg (amplitude t (realRoot t)))
      (𝓝[<] rightEdge) (𝓝 (-(Real.pi / 2))) :=
    hWarg.congr' (hmem.mono fun _ ht ↦ arg_scaledAmplitude ht)
  change Tendsto (fun t ↦ (n : ℝ) * Complex.arg (eigenvalue t (realRoot t)) +
    Complex.arg (amplitude t (realRoot t))) (𝓝[<] rightEdge) (𝓝 (-(Real.pi / 2)))
  simpa only [Function.comp_def, mul_zero, zero_add] using
    (hArgEigen.const_mul (n : ℝ)).add hAarg

private noncomputable def normalizedImagSq (s u : ℝ) : ℝ :=
  u ^ 2 - (1 + s) * u - 1 - 2 * s - ((s + 1 - u) / 2) ^ 2

private theorem normalizedImagSq_eq {t : ℝ} (ht : t ≠ 0) :
    normalizedImagSq t⁻¹ (scaledRoot t) = pairImagSq t (realRoot t) / t ^ 2 := by
  dsimp [normalizedImagSq, scaledRoot, pairImagSq, pairNormSq, pairReal]
  field_simp
  ring

private theorem normalizedReal_eq {t : ℝ} (ht : t ≠ 0) :
    pairReal t (realRoot t) / (-t) = -(t⁻¹ + 1 - scaledRoot t) / 2 := by
  dsimp [pairReal, scaledRoot]
  field_simp

private noncomputable def normalizedEigenvalue (t : ℝ) : ℂ :=
  ⟨pairReal t (realRoot t) / (-t), pairImag t (realRoot t) / (-t)⟩

private theorem tendsto_normalizedEigenvalue :
    Tendsto normalizedEigenvalue atBot (𝓝 (-1 : ℂ)) := by
  have hi : Tendsto (fun t : ℝ ↦ t⁻¹) atBot (𝓝 0) := tendsto_inv_atBot_zero
  have hu := tendsto_scaledRoot_atBot
  have hR : Tendsto (fun t ↦ -(t⁻¹ + 1 - scaledRoot t) / 2) atBot (𝓝 (-1 : ℝ)) := by
    convert (((hi.add_const 1).sub hu).neg.div_const 2) using 1
    norm_num
  have hRe : Tendsto (fun t ↦ pairReal t (realRoot t) / (-t)) atBot (𝓝 (-1 : ℝ)) :=
    hR.congr' ((eventually_lt_atBot (0 : ℝ)).mono fun _ ht ↦ (normalizedReal_eq ht.ne).symm)
  have hc : Continuous (fun p : ℝ × ℝ ↦ normalizedImagSq p.1 p.2) := by
    dsimp [normalizedImagSq]; fun_prop
  have hS : Tendsto (fun t ↦ normalizedImagSq t⁻¹ (scaledRoot t)) atBot (𝓝 (0 : ℝ)) := by
    convert hc.continuousAt.tendsto.comp (hi.prodMk_nhds hu) using 1 <;>
      norm_num [normalizedImagSq, Function.comp_def]
  have hIm : Tendsto (fun t ↦ pairImag t (realRoot t) / (-t)) atBot (𝓝 (0 : ℝ)) := by
    have hs : Tendsto (fun t ↦ Real.sqrt (normalizedImagSq t⁻¹ (scaledRoot t)))
        atBot (𝓝 (0 : ℝ)) := by simpa only [Real.sqrt_zero] using hS.sqrt
    apply hs.congr'
    filter_upwards [eventually_lt_atBot (0 : ℝ)] with t ht
    rw [normalizedImagSq_eq ht.ne, Real.sqrt_div' _ (sq_nonneg t),
      Real.sqrt_sq_eq_abs, abs_of_neg ht]
    rfl
  have hz := hRe.ofReal.add (hIm.ofReal.mul_const Complex.I)
  change Tendsto (fun t ↦ Complex.mk (pairReal t (realRoot t) / (-t))
    (pairImag t (realRoot t) / (-t))) atBot (𝓝 (-1 : ℂ))
  simpa only [Complex.mk_eq_add_mul_I, Complex.ofReal_neg,
    Complex.ofReal_one, Complex.ofReal_zero, zero_mul, add_zero] using hz

private theorem arg_normalizedEigenvalue {t : ℝ} (ht : t < 0) :
    Complex.arg (normalizedEigenvalue t) = Complex.arg (eigenvalue t (realRoot t)) := by
  have hne := ht.ne
  have heq : normalizedEigenvalue t = ((-t)⁻¹ : ℝ) * eigenvalue t (realRoot t) := by
    apply Complex.ext
    · simp [normalizedEigenvalue, eigenvalue, Complex.mul_re, div_eq_mul_inv]
      field_simp
    · simp [normalizedEigenvalue, eigenvalue, Complex.mul_im, div_eq_mul_inv]
      field_simp
  rw [heq]
  exact Complex.arg_real_mul _ (inv_pos.mpr (neg_pos.mpr ht))

/-- The eigenvalue angle tends to `π` at the unbounded left edge, from the upper half-plane. -/
theorem tendsto_eigenvalue_arg_atBot :
    Tendsto (fun t ↦ Complex.arg (eigenvalue t (realRoot t))) atBot (𝓝 Real.pi) := by
  have hw : Tendsto normalizedEigenvalue atBot (𝓝[{z : ℂ | 0 ≤ z.im}] (-1 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_normalizedEigenvalue, ?_⟩
    filter_upwards [eventually_lt_atBot (0 : ℝ)] with t ht
    exact div_nonneg (Real.sqrt_nonneg _) (neg_pos.mpr ht).le
  have harg := (Complex.tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero
    (z := (-1 : ℂ)) (by norm_num) (by norm_num)).comp hw
  exact harg.congr' ((eventually_lt_atBot (0 : ℝ)).mono fun _ ht ↦ arg_normalizedEigenvalue ht)

/-- At every positive index the phase eventually exceeds its last required sample level. -/
theorem eventually_phase_gt (k : ℕ) :
    ∀ᶠ t in atBot, (k : ℝ) * Real.pi < phase (k + 1) t := by
  have hlim := (tendsto_eigenvalue_arg_atBot.const_mul ((k + 1 : ℕ) : ℝ)).sub_const
    (Real.pi / 2)
  have hbound : (k : ℝ) * Real.pi < ((k + 1 : ℕ) : ℝ) * Real.pi - Real.pi / 2 := by
    push_cast
    nlinarith [Real.pi_pos]
  have he := hlim.eventually (eventually_gt_nhds hbound)
  filter_upwards [he, eventually_lt_atBot rightEdge] with t ht hmem
  have hδ := Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl (amplitude_re_pos hmem))
  dsimp [phase]
  linarith

/-- The two edge bounds supply ordered finite witnesses at every positive index. -/
theorem exists_phase_bounds (k : ℕ) :
    ∃ a b : ℝ, a < b ∧ b < rightEdge ∧ phase (k + 1) b < 0 ∧
      (k : ℝ) * Real.pi < phase (k + 1) a := by
  have hneg := (tendsto_phase_rightEdge (k + 1)).eventually
    (eventually_lt_nhds (show -(Real.pi / 2) < 0 by nlinarith [Real.pi_pos]))
  have hmem : ∀ᶠ t in 𝓝[<] rightEdge, t < rightEdge := self_mem_nhdsWithin
  obtain ⟨b, hb, hlo⟩ := (hmem.and hneg).exists
  obtain ⟨a, hhi, hab⟩ := ((eventually_phase_gt k).and (eventually_lt_atBot b)).exists
  exact ⟨a, b, hab, hb, hlo, hhi⟩

end RealRooted.EffectiveBKW.Tiling4
