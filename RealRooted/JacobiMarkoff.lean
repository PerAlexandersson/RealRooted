import RealRooted.JacobiOrthogonality

/-!
# Markoff monotonicity for shifted Jacobi roots

This file develops the parameter derivative and strict sign argument for the
first parameter of beta-one shifted Jacobi polynomials.
-/

open Filter Polynomial Topology

noncomputable section

namespace RealRooted

/-- The logarithmic beta-one moment, obtained by differentiating the ordinary
moment with respect to the exponent. -/
def jacobiBetaOneLogMoment (α : ℝ) (k : ℕ) : ℝ :=
  -1 / (α + k + 1) ^ 2 + 1 / (α + k + 2) ^ 2

/-- The logarithmic beta-one moment functional on real polynomials. -/
def jacobiBetaOneLogFunctional (α : ℝ) (p : ℝ[X]) : ℝ :=
  p.sum fun k c => c * jacobiBetaOneLogMoment α k

@[simp]
theorem jacobiBetaOneLogFunctional_zero (α : ℝ) :
    jacobiBetaOneLogFunctional α 0 = 0 := by
  simp [jacobiBetaOneLogFunctional]

@[simp]
theorem jacobiBetaOneLogFunctional_add (α : ℝ) (p q : ℝ[X]) :
    jacobiBetaOneLogFunctional α (p + q) =
      jacobiBetaOneLogFunctional α p +
        jacobiBetaOneLogFunctional α q := by
  simp only [jacobiBetaOneLogFunctional]
  apply Polynomial.sum_add_index <;> simp [add_mul]

@[simp]
theorem jacobiBetaOneLogFunctional_C_mul (α c : ℝ) (p : ℝ[X]) :
    jacobiBetaOneLogFunctional α (C c * p) =
      c * jacobiBetaOneLogFunctional α p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [mul_add, hp, hq, mul_add]
  | monomial n a =>
      simp [jacobiBetaOneLogFunctional, C_mul_monomial, mul_assoc]

@[simp]
theorem jacobiBetaOneLogFunctional_monomial (α c : ℝ) (k : ℕ) :
    jacobiBetaOneLogFunctional α (monomial k c) =
      c * jacobiBetaOneLogMoment α k := by
  simp [jacobiBetaOneLogFunctional]

/-- The logarithmic moment is the derivative of the ordinary beta-one moment. -/
theorem deriv_jacobiBetaOneMoment {α : ℝ} (hα : -1 < α) (k : ℕ) :
    deriv (fun a => jacobiBetaOneMoment a k) α =
      jacobiBetaOneLogMoment α k := by
  have hu : α + (k : ℝ) + 1 ≠ 0 := by
    have hk : 0 ≤ (k : ℝ) := by positivity
    linarith
  have hv : α + (k : ℝ) + 2 ≠ 0 := by
    have hk : 0 ≤ (k : ℝ) := by positivity
    linarith
  have hfirst : HasDerivAt (fun a : ℝ => a + k + 1) 1 α := by
    simpa only [add_assoc] using
      (hasDerivAt_id' α).add_const ((k : ℝ) + 1)
  have hsecond : HasDerivAt (fun a : ℝ => a + k + 2) 1 α := by
    simpa only [add_assoc] using
      (hasDerivAt_id' α).add_const ((k : ℝ) + 2)
  have hinv := (hfirst.mul hsecond).inv (mul_ne_zero hu hv)
  have hvalue :
      -(1 * (α + k + 2) + (α + k + 1) * 1) /
          ((α + k + 1) * (α + k + 2)) ^ 2 =
        jacobiBetaOneLogMoment α k := by
    simp only [jacobiBetaOneLogMoment]
    field_simp [hu, hv]
    ring
  have hfun :
      ((fun a : ℝ => a + k + 1) * (fun a : ℝ => a + k + 2))⁻¹ =
        fun a => jacobiBetaOneMoment a k := by
    funext a
    rfl
  rw [← hfun]
  exact (hinv.congr_deriv hvalue).deriv

/-- Integral representation of the logarithmic beta-one moment. -/
theorem integral_rpow_mul_one_sub_mul_log_zero_one {α : ℝ}
    (hα : -1 < α) (k : ℕ) :
    (∫ x : ℝ in 0..1,
        x ^ (α + k) * (1 - x) * Real.log x) =
      jacobiBetaOneLogMoment α k := by
  have hk : 0 ≤ (k : ℝ) := by positivity
  have h₀ : -1 < α + (k : ℝ) := by linarith
  have h₁ : -1 < α + (k : ℝ) + 1 := by linarith
  have hint₀ := intervalIntegral.intervalIntegrable_rpow_mul_log h₀
  have hint₁ := intervalIntegral.intervalIntegrable_rpow_mul_log h₁
  calc
    (∫ x : ℝ in 0..1, x ^ (α + k) * (1 - x) * Real.log x) =
        ∫ x : ℝ in 0..1,
          (x ^ (α + k) * Real.log x -
            x ^ (α + k + 1) * Real.log x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      simp only [Set.uIcc_of_le zero_le_one] at hx
      rcases hx.1.eq_or_lt with hzero | hxpos
      · subst x
        simp
      · rw [Real.rpow_add_one hxpos.ne']
        ring
    _ = (∫ x : ℝ in 0..1, x ^ (α + k) * Real.log x) -
        ∫ x : ℝ in 0..1, x ^ (α + k + 1) * Real.log x := by
      rw [intervalIntegral.integral_sub hint₀ hint₁]
    _ = jacobiBetaOneLogMoment α k := by
      rw [intervalIntegral.integral_rpow_mul_log_zero_one h₀,
        intervalIntegral.integral_rpow_mul_log_zero_one h₁]
      simp only [jacobiBetaOneLogMoment]
      ring

theorem intervalIntegrable_jacobiBetaOneLogIntegrand {α : ℝ}
    (hα : -1 < α) (p : ℝ[X]) :
    IntervalIntegrable
      (fun x : ℝ => p.eval x * x ^ α * (1 - x) * Real.log x)
      MeasureTheory.volume 0 1 := by
  have hlog := intervalIntegral.intervalIntegrable_rpow_mul_log hα
  have hone : Continuous (fun x : ℝ => 1 - x) :=
    continuous_const.sub continuous_id
  have hbase := hlog.mul_continuousOn hone.continuousOn
  have hproduct := hbase.continuousOn_mul p.continuousOn
  convert hproduct using 1
  ext x
  ring

/-- The logarithmic moment functional is integration against
`x ^ α * (1 - x) * log x` on the unit interval. -/
theorem jacobiBetaOneLogFunctional_eq_integral {α : ℝ} (hα : -1 < α)
    (p : ℝ[X]) :
    jacobiBetaOneLogFunctional α p =
      ∫ x : ℝ in 0..1,
        p.eval x * x ^ α * (1 - x) * Real.log x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [jacobiBetaOneLogFunctional_add, hp, hq]
      rw [← intervalIntegral.integral_add
        (intervalIntegrable_jacobiBetaOneLogIntegrand hα p)
        (intervalIntegrable_jacobiBetaOneLogIntegrand hα q)]
      apply intervalIntegral.integral_congr
      intro x hx
      simp only [eval_add]
      ring
  | monomial n c =>
      rw [jacobiBetaOneLogFunctional_monomial,
        ← integral_rpow_mul_one_sub_mul_log_zero_one hα n,
        ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      rw [eval_monomial]
      simp only [Set.uIcc_of_le zero_le_one] at hx
      rcases hx.1.eq_or_lt with hzero | hxpos
      · subst x
        simp
      · rw [Real.rpow_add hxpos, Real.rpow_natCast]
        ring

theorem integral_rpow_mul_one_sub_zero_one {α : ℝ}
    (hα : -1 < α) (k : ℕ) :
    (∫ x : ℝ in 0..1, x ^ (α + k) * (1 - x)) =
      jacobiBetaOneMoment α k := by
  have hk : 0 ≤ (k : ℝ) := by positivity
  have h₀ : -1 < α + (k : ℝ) := by linarith
  have h₁ : -1 < α + (k : ℝ) + 1 := by linarith
  have hint₀ := intervalIntegral.intervalIntegrable_rpow'
    (a := 0) (b := 1) h₀
  have hint₁ := intervalIntegral.intervalIntegrable_rpow'
    (a := 0) (b := 1) h₁
  calc
    (∫ x : ℝ in 0..1, x ^ (α + k) * (1 - x)) =
        ∫ x : ℝ in 0..1,
          (x ^ (α + k) - x ^ (α + k + 1)) := by
      apply intervalIntegral.integral_congr_uIoo
      intro x hx
      dsimp only
      have hxpos : 0 < x := by simpa using hx.1
      rw [Real.rpow_add_one hxpos.ne']
      ring
    _ = (∫ x : ℝ in 0..1, x ^ (α + k)) -
        ∫ x : ℝ in 0..1, x ^ (α + k + 1) := by
      rw [intervalIntegral.integral_sub hint₀ hint₁]
    _ = jacobiBetaOneMoment α k := by
      have hu : α + (k : ℝ) + 1 ≠ 0 := by linarith
      have hv : α + (k : ℝ) + 2 ≠ 0 := by linarith
      have hmoment : (α + (k : ℝ) + 1)⁻¹ -
          (α + k + 2)⁻¹ = jacobiBetaOneMoment α k := by
        rw [inv_sub_inv hu hv]
        rw [show α + (k : ℝ) + 2 - (α + k + 1) = 1 by ring]
        simp only [one_div, jacobiBetaOneMoment]
      rw [integral_rpow (Or.inl h₀), integral_rpow (Or.inl h₁)]
      simp only [Real.one_rpow, Real.zero_rpow hu,
        Real.zero_rpow (by linarith : α + k + 1 + 1 ≠ 0),
        sub_zero, one_div]
      convert hmoment using 1
      ring

theorem intervalIntegrable_jacobiBetaOneIntegrand {α : ℝ}
    (hα : -1 < α) (p : ℝ[X]) :
    IntervalIntegrable
      (fun x : ℝ => p.eval x * x ^ α * (1 - x))
      MeasureTheory.volume 0 1 := by
  have hpow := intervalIntegral.intervalIntegrable_rpow'
    (a := 0) (b := 1) hα
  have hone : Continuous (fun x : ℝ => 1 - x) :=
    continuous_const.sub continuous_id
  have hbase := hpow.mul_continuousOn hone.continuousOn
  have hproduct := hbase.continuousOn_mul p.continuousOn
  convert hproduct using 1
  ext x
  ring

/-- The beta-one moment functional is integration against
`x ^ α * (1 - x)` on the unit interval. -/
theorem jacobiBetaOneFunctional_eq_integral {α : ℝ} (hα : -1 < α)
    (p : ℝ[X]) :
    jacobiBetaOneFunctional α p =
      ∫ x : ℝ in 0..1, p.eval x * x ^ α * (1 - x) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [jacobiBetaOneFunctional_add, hp, hq]
      rw [← intervalIntegral.integral_add
        (intervalIntegrable_jacobiBetaOneIntegrand hα p)
        (intervalIntegrable_jacobiBetaOneIntegrand hα q)]
      apply intervalIntegral.integral_congr
      intro x hx
      simp only [eval_add]
      ring
  | monomial n c =>
      rw [jacobiBetaOneFunctional_monomial,
        ← integral_rpow_mul_one_sub_zero_one hα n,
        ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr_uIoo
      intro x hx
      dsimp only
      rw [eval_monomial]
      have hxpos : 0 < x := by simpa using hx.1
      rw [Real.rpow_add hxpos, Real.rpow_natCast]
      ring

private theorem sub_mul_log_sub_nonneg {r x : ℝ} (hr : 0 < r)
    (hx : 0 < x) :
    0 ≤ (x - r) * (Real.log x - Real.log r) := by
  rcases le_total x r with hxr | hrx
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hxr)
      (sub_nonpos.mpr
        (Real.strictMonoOn_log.monotoneOn hx hr hxr))
  · exact mul_nonneg (sub_nonneg.mpr hrx)
      (sub_nonneg.mpr
        (Real.strictMonoOn_log.monotoneOn hr hx hrx))

private theorem sub_mul_log_sub_pos {r x : ℝ} (hr : 0 < r)
    (hx : 0 < x) (hxr : x ≠ r) :
    0 < (x - r) * (Real.log x - Real.log r) := by
  rcases lt_or_gt_of_ne hxr with hxr' | hrx
  · exact mul_pos_of_neg_of_neg (sub_neg.mpr hxr')
      (sub_neg.mpr (Real.log_lt_log hx hxr'))
  · exact mul_pos (sub_pos.mpr hrx)
      (sub_pos.mpr (Real.log_lt_log hr hrx))

/-- Strict Markoff sign for a root factor and a nonzero quotient polynomial. -/
theorem jacobiBetaOneLogFunctional_X_sub_C_mul_sq_pos {α r : ℝ}
    (hα : -1 < α) (hr : r ∈ Set.Ioo (0 : ℝ) 1) {q : ℝ[X]}
    (hq : q ≠ 0)
    (horth : jacobiBetaOneFunctional α ((X - C r) * q ^ 2) = 0) :
    0 < jacobiBetaOneLogFunctional α ((X - C r) * q ^ 2) := by
  let p : ℝ[X] := (X - C r) * q ^ 2
  let f : ℝ → ℝ := fun x =>
    (x - r) * (Real.log x - Real.log r) * (q.eval x) ^ 2 *
      x ^ α * (1 - x)
  have hreg : (∫ x : ℝ in 0..1, p.eval x * x ^ α * (1 - x)) = 0 := by
    rw [← jacobiBetaOneFunctional_eq_integral hα]
    exact horth
  have hlogInt := intervalIntegrable_jacobiBetaOneLogIntegrand hα p
  have hregInt := intervalIntegrable_jacobiBetaOneIntegrand hα p
  have hfInt : IntervalIntegrable f MeasureTheory.volume 0 1 := by
    have hsub := hlogInt.sub (hregInt.const_mul (Real.log r))
    convert hsub using 1
    ext x
    simp only [f, p, eval_mul, eval_sub, eval_X, eval_C, eval_pow]
    ring
  have hIntegral : jacobiBetaOneLogFunctional α p =
      ∫ x : ℝ in 0..1, f x := by
    rw [jacobiBetaOneLogFunctional_eq_integral hα]
    calc
      (∫ x : ℝ in 0..1,
          p.eval x * x ^ α * (1 - x) * Real.log x) =
          (∫ x : ℝ in 0..1,
            p.eval x * x ^ α * (1 - x) * Real.log x) -
            Real.log r *
              ∫ x : ℝ in 0..1, p.eval x * x ^ α * (1 - x) := by
        rw [hreg, mul_zero, sub_zero]
      _ = ∫ x : ℝ in 0..1,
          (p.eval x * x ^ α * (1 - x) * Real.log x -
            Real.log r * (p.eval x * x ^ α * (1 - x))) := by
        rw [intervalIntegral.integral_sub hlogInt
          (hregInt.const_mul (Real.log r)),
          intervalIntegral.integral_const_mul]
      _ = ∫ x : ℝ in 0..1, f x := by
        apply intervalIntegral.integral_congr
        intro x hx
        simp only [f, p, eval_mul, eval_sub, eval_X, eval_C, eval_pow]
        ring
  have hf_nonneg : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.uIoc 0 1)] f := by
    rw [Set.uIoc_of_le zero_le_one]
    rw [Filter.EventuallyLE]
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with x hx
    have hfirst := sub_mul_log_sub_nonneg hr.1 hx.1
    have hpow : 0 < x ^ α := Real.rpow_pos_of_pos hx.1 α
    have hone : 0 ≤ 1 - x := sub_nonneg.mpr hx.2
    dsimp only [f]
    exact mul_nonneg (mul_nonneg (mul_nonneg hfirst (sq_nonneg _)) hpow.le) hone
  let forbidden : Finset ℝ := q.roots.toFinset ∪ {r}
  obtain ⟨x, hx, havoid⟩ :=
    (Set.Ioo_infinite (show (0 : ℝ) < 1 by norm_num)).exists_notMem_finset forbidden
  have hxr : x ≠ r := by
    intro h
    apply havoid
    simp [forbidden, h]
  have hqx : q.eval x ≠ 0 := by
    intro heval
    apply havoid
    have hroot : q.IsRoot x := by simpa [Polynomial.IsRoot.def]
    have hmem : x ∈ q.roots := (Polynomial.mem_roots hq).mpr hroot
    simp [forbidden, hmem]
  have hfx : 0 < f x := by
    have hfirst := sub_mul_log_sub_pos hr.1 hx.1 hxr
    have hpow : 0 < x ^ α := Real.rpow_pos_of_pos hx.1 α
    have hqpos : 0 < (q.eval x) ^ 2 := sq_pos_of_ne_zero hqx
    have hone : 0 < 1 - x := sub_pos.mpr hx.2
    dsimp only [f]
    positivity
  have hfcont : ContinuousAt f x := by
    have hx0 : x ≠ 0 := hx.1.ne'
    dsimp only [f]
    exact (((((continuousAt_id.sub continuousAt_const).mul
      ((Real.continuousAt_log hx0).sub continuousAt_const)).mul
        (q.continuousAt.pow 2)).mul
          (continuousAt_id.rpow_const (Or.inl hx0))).mul
            (continuousAt_const.sub continuousAt_id))
  have hevent : ∀ᶠ y in 𝓝 x, f y ≠ 0 :=
    hfcont.eventually_ne hfx.ne'
  obtain ⟨a, b, hxab, hab⟩ := hevent.exists_Ioo_subset
  let a' := max a 0
  let b' := min b 1
  have ha'x : a' < x := max_lt hxab.1 hx.1
  have hxb' : x < b' := lt_min hxab.2 hx.2
  have ha'b' : a' < b' := ha'x.trans hxb'
  have hsubset : Set.Ioo a' b' ⊆ Function.support f ∩ Set.Ioc 0 1 := by
    intro y hy
    have hay : a < y := (le_max_left a 0).trans_lt hy.1
    have hyb : y < b := hy.2.trans_le (min_le_left b 1)
    have hfy : f y ≠ 0 := hab ⟨hay, hyb⟩
    refine ⟨Function.mem_support.mpr hfy, ?_⟩
    exact ⟨(le_max_right a 0).trans_lt hy.1,
      (hy.2.trans_le (min_le_right b 1)).le⟩
  have hmeasure : 0 < MeasureTheory.volume
      (Function.support f ∩ Set.Ioc 0 1) :=
    ((MeasureTheory.Measure.measure_Ioo_pos _).mpr ha'b').trans_le
      (MeasureTheory.measure_mono hsubset)
  have hfpos : 0 < ∫ x : ℝ in 0..1, f x :=
    (intervalIntegral.integral_pos_iff_support_of_nonneg_ae'
      hf_nonneg hfInt).mpr ⟨zero_lt_one, hmeasure⟩
  rw [hIntegral]
  exact hfpos

end RealRooted
