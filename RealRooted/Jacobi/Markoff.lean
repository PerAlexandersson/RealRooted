module

public import RealRooted.JacobiOrthogonality
public import RealRooted.Jacobi
public import RealRooted.Bezoutian.WronskianConverse
public import RealRooted.Mathlib.Analysis.SpecialFunctions.Integrals.RpowLog
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Data.List.GetD
public import RealRooted.Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Markoff monotonicity for shifted Jacobi roots

This file develops the parameter derivative and strict sign argument for the
first parameter of beta-one shifted Jacobi polynomials.
-/

@[expose] public section

open Filter Polynomial Topology
open scoped ContDiff

noncomputable section

namespace RealRooted

/-- The logarithmic beta-one moment, obtained by differentiating the ordinary
moment with respect to the exponent. -/
def jacobiBetaOneLogMoment (α : ℝ) (k : ℕ) : ℝ :=
  -1 / (α + k + 1) ^ 2 + 1 / (α + k + 2) ^ 2

/-- The logarithmic beta-one moment functional on real polynomials. -/
def jacobiBetaOneLogFunctional (α : ℝ) (p : ℝ[X]) : ℝ :=
  Polynomial.momentFunctional (jacobiBetaOneLogMoment α) p

@[simp]
theorem jacobiBetaOneLogFunctional_zero (α : ℝ) :
    jacobiBetaOneLogFunctional α 0 = 0 := by
  simpa only [jacobiBetaOneLogFunctional] using
    Polynomial.momentFunctional_zero (jacobiBetaOneLogMoment α)

@[simp]
theorem jacobiBetaOneLogFunctional_add (α : ℝ) (p q : ℝ[X]) :
    jacobiBetaOneLogFunctional α (p + q) =
      jacobiBetaOneLogFunctional α p +
        jacobiBetaOneLogFunctional α q := by
  simpa only [jacobiBetaOneLogFunctional] using
    Polynomial.momentFunctional_add (jacobiBetaOneLogMoment α) p q

@[simp]
theorem jacobiBetaOneLogFunctional_C_mul (α c : ℝ) (p : ℝ[X]) :
    jacobiBetaOneLogFunctional α (C c * p) =
      c * jacobiBetaOneLogFunctional α p := by
  simpa only [jacobiBetaOneLogFunctional] using
    Polynomial.momentFunctional_C_mul (jacobiBetaOneLogMoment α) c p

@[simp]
theorem jacobiBetaOneLogFunctional_monomial (α c : ℝ) (k : ℕ) :
    jacobiBetaOneLogFunctional α (monomial k c) =
      c * jacobiBetaOneLogMoment α k := by
  simpa only [jacobiBetaOneLogFunctional] using
    Polynomial.momentFunctional_monomial (jacobiBetaOneLogMoment α) c k

/-- The logarithmic moment is the derivative of the ordinary beta-one moment. -/
theorem hasDerivAt_jacobiBetaOneMoment {α : ℝ} (hα : -1 < α) (k : ℕ) :
    HasDerivAt (fun a => jacobiBetaOneMoment a k)
      (jacobiBetaOneLogMoment α k) α := by
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
  convert hinv using 1
  · funext a
    rfl
  · change jacobiBetaOneLogMoment α k =
      -(1 * (α + k + 2) + (α + k + 1) * 1) /
        ((α + k + 1) * (α + k + 2)) ^ 2
    simp only [jacobiBetaOneLogMoment]
    field_simp [hu, hv]
    ring

theorem deriv_jacobiBetaOneMoment {α : ℝ} (hα : -1 < α) (k : ℕ) :
    deriv (fun a => jacobiBetaOneMoment a k) α =
      jacobiBetaOneLogMoment α k :=
  (hasDerivAt_jacobiBetaOneMoment hα k).deriv

/-- Differentiating the beta-one moment functional at a fixed polynomial
gives its logarithmic moment functional. -/
theorem hasDerivAt_jacobiBetaOneFunctional {α : ℝ} (hα : -1 < α)
    (p : ℝ[X]) :
    HasDerivAt (fun a => jacobiBetaOneFunctional a p)
      (jacobiBetaOneLogFunctional α p) α := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [jacobiBetaOneFunctional_add,
        jacobiBetaOneLogFunctional_add]
      change HasDerivAt
        ((fun a => jacobiBetaOneFunctional a p) +
          fun a => jacobiBetaOneFunctional a q)
        (jacobiBetaOneLogFunctional α p +
          jacobiBetaOneLogFunctional α q) α
      exact hp.add hq
  | monomial n c =>
      simpa using (hasDerivAt_jacobiBetaOneMoment hα n).const_mul c

@[simp]
theorem jacobiBetaOneLogFunctional_sum {ι : Type*} (α : ℝ)
    (s : Finset ι) (p : ι → ℝ[X]) :
    jacobiBetaOneLogFunctional α (∑ i ∈ s, p i) =
      ∑ i ∈ s, jacobiBetaOneLogFunctional α (p i) := by
  simpa only [jacobiBetaOneLogFunctional] using
    Polynomial.momentFunctional_sum (jacobiBetaOneLogMoment α) s p

@[simp]
theorem jacobiBetaOneInner_sum_left {ι : Type*} (α : ℝ)
    (s : Finset ι) (p : ι → ℝ[X]) (q : ℝ[X]) :
    jacobiBetaOneInner α (∑ i ∈ s, p i) q =
      ∑ i ∈ s, jacobiBetaOneInner α (p i) q := by
  rw [jacobiBetaOneInner_comm, jacobiBetaOneInner_sum_right]
  apply Finset.sum_congr rfl
  intro i hi
  rw [jacobiBetaOneInner_comm]

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
      apply intervalIntegral.integral_congr_uIoo
      intro x hx
      dsimp only
      rw [Real.rpow_add_one (show 0 < x by simpa using hx.1).ne']
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
  have hone : Continuous fun x : ℝ => 1 - x := by fun_prop
  convert ((intervalIntegral.intervalIntegrable_rpow_mul_log hα).mul_continuousOn
    hone.continuousOn).continuousOn_mul p.continuousOn using 1
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
      apply intervalIntegral.integral_congr_uIoo
      intro x hx
      dsimp only
      rw [eval_monomial]
      rw [Real.rpow_add (by simpa using hx.1), Real.rpow_natCast]
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
  have hone : Continuous fun x : ℝ => 1 - x := by fun_prop
  convert ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) hα).mul_continuousOn
    hone.continuousOn).continuousOn_mul p.continuousOn using 1
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

private theorem intervalIntegral_pos_of_continuousAt_pos {f : ℝ → ℝ}
    (hfInt : IntervalIntegrable f MeasureTheory.volume 0 1)
    (hf_nonneg : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.uIoc 0 1)] f)
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) (hfx : 0 < f x)
    (hfcont : ContinuousAt f x) :
    0 < ∫ y : ℝ in 0..1, f y := by
  obtain ⟨a, b, hxab, hab⟩ := (hfcont.eventually_ne hfx.ne').exists_Ioo_subset
  let a' := max a 0
  let b' := min b 1
  have ha'x : a' < x := max_lt hxab.1 hx.1
  have hxb' : x < b' := lt_min hxab.2 hx.2
  have hsubset : Set.Ioo a' b' ⊆ Function.support f ∩ Set.Ioc 0 1 := by
    intro y hy
    refine ⟨Function.mem_support.mpr (hab ⟨?_, ?_⟩), ?_⟩
    · exact (le_max_left a 0).trans_lt hy.1
    · exact hy.2.trans_le (min_le_left b 1)
    · exact ⟨(le_max_right a 0).trans_lt hy.1,
        (hy.2.trans_le (min_le_right b 1)).le⟩
  apply (intervalIntegral.integral_pos_iff_support_of_nonneg_ae'
    hf_nonneg hfInt).mpr
  refine ⟨zero_lt_one, ((MeasureTheory.Measure.measure_Ioo_pos _).mpr ?_).trans_le
    (MeasureTheory.measure_mono hsubset)⟩
  exact ha'x.trans hxb'

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
    rw [show (∫ x : ℝ in 0..1,
        p.eval x * x ^ α * (1 - x) * Real.log x) =
      (∫ x : ℝ in 0..1, p.eval x * x ^ α * (1 - x) * Real.log x) -
        Real.log r * ∫ x : ℝ in 0..1, p.eval x * x ^ α * (1 - x) by
          rw [hreg, mul_zero, sub_zero]]
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub hlogInt (hregInt.const_mul (Real.log r))]
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [f, p, eval_mul, eval_sub, eval_X, eval_C, eval_pow]
    ring
  have hf_nonneg : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.uIoc 0 1)] f := by
    rw [Set.uIoc_of_le zero_le_one, Filter.EventuallyLE,
      MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
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
    simp [forbidden, (Polynomial.mem_roots hq).mpr (by
      simpa [Polynomial.IsRoot.def])]
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
  rw [hIntegral]
  exact intervalIntegral_pos_of_continuousAt_pos hfInt hf_nonneg hx hfx hfcont

@[fun_prop]
theorem differentiable_ring_choose (n : ℕ) :
    Differentiable ℝ (fun x : ℝ => Ring.choose x n) := by
  simp_rw [Ring.choose_eq_smul, smul_eq_mul,
    ← eval₂_smulOneHom_eq_smeval, ← eval_map]
  fun_prop

@[fun_prop]
theorem contDiff_ring_choose (n : ℕ) :
    ContDiff ℝ ∞ (fun x : ℝ => Ring.choose x n) := by
  simp_rw [Ring.choose_eq_smul, smul_eq_mul,
    ← eval₂_smulOneHom_eq_smeval, ← eval_map]
  simpa [aeval_def] using
    (contDiff_const.mul
      (Polynomial.contDiff_aeval (descPochhammer ℝ n) ∞))

theorem natDegree_shiftedJacobiMonic_le (n : ℕ) (α β : ℝ) :
    (shiftedJacobiMonic n α β).natDegree ≤ n := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro k hk
  rw [coeff_shiftedJacobiMonic]
  simp [Nat.not_le_of_lt hk]

theorem differentiableAt_shiftedJacobiMonic_coeff_alpha (n k : ℕ)
    {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    DifferentiableAt ℝ
      (fun a => (shiftedJacobiMonic n a β).coeff k) α := by
  have hchoose : Ring.choose (n + α + β + n) n ≠ 0 := by
    cases n with
    | zero => simp
    | succ n =>
        exact (Polynomial.ring_choose_pos (by
          push_cast
          linarith)).ne'
  have hscale :
      (-1 : ℝ) ^ n * Ring.choose (n + α + β + n) n ≠ 0 :=
    mul_ne_zero (pow_ne_zero n (by norm_num)) hchoose
  rw [show (fun a => (shiftedJacobiMonic n a β).coeff k) =
      fun a =>
        (((-1 : ℝ) ^ n * Ring.choose (n + a + β + n) n)⁻¹) *
          (if k ≤ n then
            (-1 : ℝ) ^ k * Ring.choose (n + a) (n - k) *
              Ring.choose (n + a + β + k) k
          else 0) by
    funext a
    exact coeff_shiftedJacobiMonic n k a β]
  split_ifs
  · fun_prop (disch := assumption)
  · fun_prop

theorem hasDerivAt_shiftedJacobiMonic_coeff_natDegree_alpha (n : ℕ)
    {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    HasDerivAt (fun a => (shiftedJacobiMonic n a β).coeff n) 0 α := by
  have hevent :
      Filter.EventuallyEq (nhds α)
        (fun a => (shiftedJacobiMonic n a β).coeff n) (fun _ => 1) := by
    filter_upwards [Ioi_mem_nhds hα] with a ha
    simpa only [natDegree_shiftedJacobiMonic n ha hβ] using
      (monic_shiftedJacobiMonic n ha hβ).coeff_natDegree
  exact (hasDerivAt_const α 1).congr_of_eventuallyEq hevent

/-- Coefficientwise derivative of the monic shifted Jacobi polynomial with
respect to its first parameter. -/
def shiftedJacobiMonicAlphaDeriv (n : ℕ) (α β : ℝ) : ℝ[X] :=
  ∑ k ∈ Finset.range n,
    C (deriv (fun a => (shiftedJacobiMonic n a β).coeff k) α) * X ^ k

theorem natDegree_shiftedJacobiMonicAlphaDeriv_lt (n : ℕ) (α β : ℝ)
    (hn : 1 ≤ n) :
    (shiftedJacobiMonicAlphaDeriv n α β).natDegree < n := by
  rw [Nat.lt_iff_le_pred hn, natDegree_le_iff_coeff_eq_zero]
  intro k hk
  have hkn : n ≤ k := by lia
  simp [shiftedJacobiMonicAlphaDeriv, hkn]

/-- The evaluation of the monic shifted Jacobi family is smooth jointly in
the first parameter and the polynomial variable away from the normalization
poles. -/
theorem contDiffAt_shiftedJacobiMonic_eval_alpha_prod (n : ℕ)
    {α β x : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    ContDiffAt ℝ ∞
      (fun z : ℝ × ℝ => (shiftedJacobiMonic n z.1 β).eval z.2) (α, x) := by
  have hchoose : Ring.choose (n + α + β + n) n ≠ 0 := by
    cases n with
    | zero => simp
    | succ n =>
        exact (Polynomial.ring_choose_pos (by
          push_cast
          linarith)).ne'
  have hscale :
      (-1 : ℝ) ^ n * Ring.choose (n + α + β + n) n ≠ 0 :=
    mul_ne_zero (pow_ne_zero n (by norm_num)) hchoose
  rw [show (fun z : ℝ × ℝ =>
      (shiftedJacobiMonic n z.1 β).eval z.2) =
        fun z => ∑ k ∈ Finset.range (n + 1),
          (((-1 : ℝ) ^ n *
              Ring.choose ((n : ℝ) + z.1 + β + n) n)⁻¹ *
              ((-1 : ℝ) ^ k * Ring.choose ((n : ℝ) + z.1) (n - k) *
                Ring.choose ((n : ℝ) + z.1 + β + k) k)) * z.2 ^ k by
    funext z
    rw [Polynomial.eval_eq_sum_range'
      (Nat.lt_succ_of_le (natDegree_shiftedJacobiMonic_le n z.1 β))]
    apply Finset.sum_congr rfl
    intro k hk
    rw [coeff_shiftedJacobiMonic]
    simp only [Finset.mem_range] at hk
    simp [Nat.le_of_lt_succ hk]]
  fun_prop (disch := assumption)

theorem hasDerivAt_shiftedJacobiMonic_eval_alpha (n : ℕ) {α β x : ℝ}
    (hα : -1 < α) (hβ : -1 < β) :
    HasDerivAt (fun a => (shiftedJacobiMonic n a β).eval x)
      ((shiftedJacobiMonicAlphaDeriv n α β).eval x) α := by
  have hsum :=
    HasDerivAt.fun_sum (u := Finset.range n) fun k hk =>
      (differentiableAt_shiftedJacobiMonic_coeff_alpha n k hα hβ).hasDerivAt.mul_const
        (x ^ k)
  have htop : HasDerivAt
      (fun a => (shiftedJacobiMonic n a β).coeff n * x ^ n) 0 α := by
    simpa using
      (hasDerivAt_shiftedJacobiMonic_coeff_natDegree_alpha n hα hβ).mul_const
        (x ^ n)
  have hall := hsum.add htop
  have heval : (fun a => (shiftedJacobiMonic n a β).eval x) =
      fun a =>
        (∑ k ∈ Finset.range n,
          (shiftedJacobiMonic n a β).coeff k * x ^ k) +
            (shiftedJacobiMonic n a β).coeff n * x ^ n := by
    funext a
    rw [← Finset.sum_range_succ]
    exact Polynomial.eval_eq_sum_range'
      (Nat.lt_succ_of_le (natDegree_shiftedJacobiMonic_le n a β)) x
  rw [heval]
  change HasDerivAt
    ((fun a => ∑ k ∈ Finset.range n,
      (shiftedJacobiMonic n a β).coeff k * x ^ k) +
        fun a => (shiftedJacobiMonic n a β).coeff n * x ^ n)
      ((shiftedJacobiMonicAlphaDeriv n α β).eval x) α
  simpa [shiftedJacobiMonicAlphaDeriv, eval_finsetSum] using hall

/-- The monic normalization preserves beta-one Jacobi orthogonality. -/
theorem shiftedJacobiMonic_betaOneInner_eq_zero {α : ℝ} (hα : -1 < α)
    {n : ℕ} (q : ℝ[X]) (hq : q.natDegree < n) :
    jacobiBetaOneInner α (shiftedJacobiMonic n α 1) q = 0 := by
  rw [shiftedJacobiMonic, jacobiBetaOneInner_C_mul_left,
    shiftedJacobi_betaOneInner_eq_zero hα q hq, mul_zero]

/-- Parameter derivative of the beta-one orthogonality pairing for the moving
monic shifted Jacobi polynomial. -/
theorem hasDerivAt_jacobiBetaOneInner_shiftedJacobiMonic_alpha (n : ℕ)
    {α : ℝ} (hα : -1 < α) (q : ℝ[X]) :
    HasDerivAt
      (fun a => jacobiBetaOneInner a (shiftedJacobiMonic n a 1) q)
      (jacobiBetaOneInner α (shiftedJacobiMonicAlphaDeriv n α 1) q +
        jacobiBetaOneLogFunctional α
          (shiftedJacobiMonic n α 1 * q)) α := by
  have hp_repr : ∀ a : ℝ,
      shiftedJacobiMonic n a 1 =
        ∑ k ∈ Finset.range (n + 1),
          C ((shiftedJacobiMonic n a 1).coeff k) * X ^ k :=
    fun a => (shiftedJacobiMonic n a 1).as_sum_range_C_mul_X_pow'
      (Nat.lt_succ_of_le (natDegree_shiftedJacobiMonic_le n a 1))
  have hfun :
      (fun a => jacobiBetaOneInner a (shiftedJacobiMonic n a 1) q) =
        fun a => ∑ k ∈ Finset.range (n + 1),
          (shiftedJacobiMonic n a 1).coeff k *
            jacobiBetaOneInner a (X ^ k) q := by
    funext a
    nth_rewrite 1 [hp_repr a]
    rw [jacobiBetaOneInner_sum_left]
    simp only [jacobiBetaOneInner_C_mul_left]
  have hterm : ∀ k ∈ Finset.range (n + 1),
      HasDerivAt
        (fun a => (shiftedJacobiMonic n a 1).coeff k *
          jacobiBetaOneInner a (X ^ k) q)
        (deriv (fun a => (shiftedJacobiMonic n a 1).coeff k) α *
            jacobiBetaOneInner α (X ^ k) q +
          (shiftedJacobiMonic n α 1).coeff k *
            jacobiBetaOneLogFunctional α (X ^ k * q)) α := by
    intro k hk
    have hc :=
      (differentiableAt_shiftedJacobiMonic_coeff_alpha n k
        (α := α) (β := 1) hα (by norm_num)).hasDerivAt
    exact hc.mul (by
      simpa only [jacobiBetaOneInner, Polynomial.momentPairing, jacobiBetaOneFunctional] using
        hasDerivAt_jacobiBetaOneFunctional hα (X ^ k * q))
  have hsum := HasDerivAt.fun_sum hterm
  have hfirst :
      (∑ k ∈ Finset.range (n + 1),
        deriv (fun a => (shiftedJacobiMonic n a 1).coeff k) α *
          jacobiBetaOneInner α (X ^ k) q) =
        jacobiBetaOneInner α (shiftedJacobiMonicAlphaDeriv n α 1) q := by
    rw [Finset.sum_range_succ,
      (hasDerivAt_shiftedJacobiMonic_coeff_natDegree_alpha n hα
        (by norm_num)).deriv,
      zero_mul, add_zero, shiftedJacobiMonicAlphaDeriv,
      jacobiBetaOneInner_sum_left]
    simp only [jacobiBetaOneInner_C_mul_left]
  have hsecond :
      (∑ k ∈ Finset.range (n + 1),
        (shiftedJacobiMonic n α 1).coeff k *
          jacobiBetaOneLogFunctional α (X ^ k * q)) =
        jacobiBetaOneLogFunctional α
          (shiftedJacobiMonic n α 1 * q) := by
    conv_rhs => rw [hp_repr α]
    rw [Finset.sum_mul, jacobiBetaOneLogFunctional_sum]
    simp only [mul_assoc, jacobiBetaOneLogFunctional_C_mul]
  rw [hfun]
  convert hsum using 1
  rw [Finset.sum_add_distrib, hfirst, hsecond]

/-- Differentiating the identically zero lower-degree orthogonality pairing
gives the Markoff derivative identity. -/
theorem jacobiBetaOneInner_alphaDeriv_add_logFunctional_eq_zero (n : ℕ)
    {α : ℝ} (hα : -1 < α) (q : ℝ[X]) (hq : q.natDegree < n) :
    jacobiBetaOneInner α (shiftedJacobiMonicAlphaDeriv n α 1) q +
        jacobiBetaOneLogFunctional α
          (shiftedJacobiMonic n α 1 * q) = 0 := by
  have hevent : Filter.EventuallyEq (nhds α)
      (fun a => jacobiBetaOneInner a (shiftedJacobiMonic n a 1) q)
      (fun _ => 0) := by
    filter_upwards [Ioi_mem_nhds hα] with a ha
    exact shiftedJacobiMonic_betaOneInner_eq_zero ha q hq
  have hzero : HasDerivAt
      (fun a => jacobiBetaOneInner a (shiftedJacobiMonic n a 1) q) 0 α :=
    (hasDerivAt_const α 0).congr_of_eventuallyEq hevent
  exact HasDerivAt.unique
    (hasDerivAt_jacobiBetaOneInner_shiftedJacobiMonic_alpha n hα q) hzero

/-- The beta-one moment functional is strictly positive on the square of a
nonzero real polynomial. -/
theorem jacobiBetaOneFunctional_sq_pos {α : ℝ} (hα : -1 < α)
    {q : ℝ[X]} (hq : q ≠ 0) :
    0 < jacobiBetaOneFunctional α (q ^ 2) := by
  let f : ℝ → ℝ := fun x => (q.eval x) ^ 2 * x ^ α * (1 - x)
  have hfInt : IntervalIntegrable f MeasureTheory.volume 0 1 := by
    convert intervalIntegrable_jacobiBetaOneIntegrand hα (q ^ 2) using 1
    ext x
    simp only [f, eval_pow]
  have hf_nonneg : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.uIoc 0 1)] f := by
    rw [Set.uIoc_of_le zero_le_one, Filter.EventuallyLE,
      MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with x hx
    have hpow : 0 < x ^ α := Real.rpow_pos_of_pos hx.1 α
    have hone : 0 ≤ 1 - x := sub_nonneg.mpr hx.2
    dsimp only [f]
    positivity
  obtain ⟨x, hx, havoid⟩ :=
    (Set.Ioo_infinite (show (0 : ℝ) < 1 by norm_num)).exists_notMem_finset
      q.roots.toFinset
  have hqx : q.eval x ≠ 0 := by
    intro heval
    apply havoid
    have hroot : q.IsRoot x := by simpa [Polynomial.IsRoot.def]
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hq).mpr hroot)
  have hfx : 0 < f x := by
    have hpow : 0 < x ^ α := Real.rpow_pos_of_pos hx.1 α
    have hone : 0 < 1 - x := sub_pos.mpr hx.2
    dsimp only [f]
    positivity
  have hfcont : ContinuousAt f x := by
    have hx0 : x ≠ 0 := hx.1.ne'
    dsimp only [f]
    exact (((q.continuousAt.pow 2).mul
      (continuousAt_id.rpow_const (Or.inl hx0))).mul
        (continuousAt_const.sub continuousAt_id))
  rw [jacobiBetaOneFunctional_eq_integral hα]
  convert intervalIntegral_pos_of_continuousAt_pos hfInt hf_nonneg hx hfx hfcont using 1
  simp only [f, eval_pow]

/-- Every root of a monic shifted Jacobi polynomial is simple. -/
theorem shiftedJacobiMonic_derivative_eval_ne_zero (n : ℕ) {α β r : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (hr : (shiftedJacobiMonic n α β).IsRoot r) :
    (shiftedJacobiMonic n α β).derivative.eval r ≠ 0 := by
  intro hder
  let p := shiftedJacobiMonic n α β
  have hp_ne : p ≠ 0 := shiftedJacobiMonic_ne_zero n hα hβ
  have hmult : 1 < p.rootMultiplicity r :=
    (Polynomial.one_lt_rootMultiplicity_iff_isRoot hp_ne).mpr ⟨hr, by
      simpa only [Polynomial.IsRoot.def, p] using hder⟩
  have hcount := (Multiset.nodup_iff_count_le_one.mp
    (shiftedJacobiMonic_roots_nodup n hα hβ)) r
  rw [Polynomial.count_roots] at hcount
  lia

/-- Every root of a monic shifted Jacobi polynomial lies in the open unit
interval. -/
theorem shiftedJacobiMonic_isRoot_mem_Ioo (n : ℕ) {α β r : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (hr : (shiftedJacobiMonic n α β).IsRoot r) :
    r ∈ Set.Ioo (0 : ℝ) 1 := by
  have hraw : (shiftedJacobi n α β).IsRoot r := by
    rw [Polynomial.IsRoot.def] at hr ⊢
    rw [shiftedJacobi_eq_leading_mul_monic n hα hβ]
    simp [hr]
  exact shiftedJacobi_isRoot_mem_Ioo n hα hβ hraw

/-- Evaluation at a Jacobi root is represented, on lower-degree polynomials,
by pairing with the corresponding root quotient. -/
theorem jacobiBetaOneInner_rootQuotient_eq_eval_mul {n : ℕ} {α r : ℝ}
    (hα : -1 < α) (hr : (shiftedJacobiMonic n α 1).IsRoot r)
    (h : ℝ[X]) (hh : h.natDegree < n) :
    jacobiBetaOneInner α h
        (shiftedJacobiMonic n α 1 /ₘ (X - C r)) =
      h.eval r * jacobiBetaOneInner α 1
        (shiftedJacobiMonic n α 1 /ₘ (X - C r)) := by
  let p := shiftedJacobiMonic n α 1
  let q := p /ₘ (X - C r)
  let s := (h - C (h.eval r)) /ₘ (X - C r)
  have hp_factor : (X - C r) * q = p :=
    Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hr
  have ht_root : (h - C (h.eval r)).IsRoot r := by
    simp [Polynomial.IsRoot.def]
  have ht_factor : (X - C r) * s = h - C (h.eval r) :=
    Polynomial.mul_divByMonic_eq_iff_isRoot.mpr ht_root
  have hn : 1 ≤ n := by lia
  have htdeg : (h - C (h.eval r)).natDegree < n :=
    (natDegree_sub_le h (C (h.eval r))).trans_lt
      (max_lt hh (by rw [natDegree_C]; exact hn))
  have hsdeg : s.natDegree < n := by
    rw [show s.natDegree = (h - C (h.eval r)).natDegree -
      (X - C r).natDegree by
        simpa [natDegree_X_sub_C] using
          natDegree_divByMonic_X_sub_C (h - C (h.eval r)) r]
    exact (Nat.sub_le _ _).trans_lt htdeg
  have horth : jacobiBetaOneInner α p s = 0 :=
    shiftedJacobiMonic_betaOneInner_eq_zero hα s hsdeg
  have hcross : jacobiBetaOneInner α ((X - C r) * s) q =
      jacobiBetaOneInner α p s := by
    simp only [jacobiBetaOneInner]
    apply congrArg (jacobiBetaOneFunctional α)
    rw [← hp_factor]
    ring
  have hdecomp : h = C (h.eval r) * 1 + (X - C r) * s := by
    rw [ht_factor]
    ring
  change jacobiBetaOneInner α h q =
    h.eval r * jacobiBetaOneInner α 1 q
  calc
    jacobiBetaOneInner α h q =
        jacobiBetaOneInner α
          (C (h.eval r) * 1 + (X - C r) * s) q :=
      congrArg (fun u => jacobiBetaOneInner α u q) hdecomp
    _ = h.eval r * jacobiBetaOneInner α 1 q := by
      rw [jacobiBetaOneInner_add_left,
        jacobiBetaOneInner_C_mul_left, hcross, horth, add_zero]

/-- At every root, the first-parameter derivative and the spatial derivative
of the monic beta-one shifted Jacobi family have opposite signs. -/
theorem shiftedJacobiMonicAlphaDeriv_eval_mul_derivative_eval_neg
    (n : ℕ) {α r : ℝ} (hα : -1 < α) (hn : 1 ≤ n)
    (hr : (shiftedJacobiMonic n α 1).IsRoot r) :
    (shiftedJacobiMonicAlphaDeriv n α 1).eval r *
        (shiftedJacobiMonic n α 1).derivative.eval r < 0 := by
  let p := shiftedJacobiMonic n α 1
  let d := shiftedJacobiMonicAlphaDeriv n α 1
  let q := p /ₘ (X - C r)
  have hp_factor : (X - C r) * q = p :=
    Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hr
  have hq_ne : q ≠ 0 := by
    intro hqzero
    have hp_ne : p ≠ 0 :=
      shiftedJacobiMonic_ne_zero n (α := α) (β := 1) hα (by norm_num)
    apply hp_ne
    rw [← hp_factor, hqzero, mul_zero]
  have hqdeg : q.natDegree < n := by
    dsimp only [q, p]
    rw [natDegree_divByMonic_X_sub_C,
      natDegree_shiftedJacobiMonic n hα (by norm_num)]
    lia
  have hrIoo : r ∈ Set.Ioo (0 : ℝ) 1 :=
    shiftedJacobiMonic_isRoot_mem_Ioo n hα (by norm_num) hr
  have hpoly : (X - C r) * q ^ 2 = p * q := by
    rw [← hp_factor]
    ring
  have horth :
      jacobiBetaOneFunctional α ((X - C r) * q ^ 2) = 0 := by
    rw [hpoly]
    exact shiftedJacobiMonic_betaOneInner_eq_zero hα q hqdeg
  have hlogpos :
      0 < jacobiBetaOneLogFunctional α ((X - C r) * q ^ 2) :=
    jacobiBetaOneLogFunctional_X_sub_C_mul_sq_pos hα hrIoo hq_ne horth
  have hmarkoff :=
    jacobiBetaOneInner_alphaDeriv_add_logFunctional_eq_zero n hα q hqdeg
  change jacobiBetaOneInner α d q +
    jacobiBetaOneLogFunctional α (p * q) = 0 at hmarkoff
  rw [← hpoly] at hmarkoff
  have hinner_neg : jacobiBetaOneInner α d q < 0 := by linarith
  have hqeval : q.eval r = p.derivative.eval r := by
    have hid := congrArg (Polynomial.eval r)
      (Polynomial.divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative
        p r)
    simpa only [q, eval_add, eval_mul, eval_sub, eval_X, eval_C,
      sub_self, zero_mul, add_zero] using hid
  have hqeval_ne : q.eval r ≠ 0 := by
    rw [hqeval]
    exact shiftedJacobiMonic_derivative_eval_ne_zero n hα (by norm_num) hr
  have hddeg : d.natDegree < n :=
    natDegree_shiftedJacobiMonicAlphaDeriv_lt n α 1 hn
  have hdrep : jacobiBetaOneInner α d q =
      d.eval r * jacobiBetaOneInner α 1 q :=
    jacobiBetaOneInner_rootQuotient_eq_eval_mul hα hr d hddeg
  have hqrep : jacobiBetaOneInner α q q =
      q.eval r * jacobiBetaOneInner α 1 q :=
    jacobiBetaOneInner_rootQuotient_eq_eval_mul hα hr q hqdeg
  have hqq_pos : 0 < jacobiBetaOneInner α q q := by
    simpa only [jacobiBetaOneInner, Polynomial.momentPairing,
      jacobiBetaOneFunctional, pow_two] using
      jacobiBetaOneFunctional_sq_pos hα hq_ne
  have hidentity :
      jacobiBetaOneInner α d q * (q.eval r) ^ 2 =
        (d.eval r * q.eval r) * jacobiBetaOneInner α q q := by
    rw [hdrep, hqrep]
    ring
  have hneg :
      (d.eval r * q.eval r) * jacobiBetaOneInner α q q < 0 := by
    rw [← hidentity]
    exact mul_neg_of_neg_of_pos hinner_neg (sq_pos_of_ne_zero hqeval_ne)
  have hdq_neg : d.eval r * q.eval r < 0 :=
    neg_of_mul_neg_left hneg hqq_pos.le
  change d.eval r * p.derivative.eval r < 0
  rwa [← hqeval]

/-- The `i`th root, in increasing order, of a monic shifted Jacobi
polynomial. The default value is irrelevant in the admissible parameter
range, where the root list has length `n`. -/
noncomputable def shiftedJacobiMonicRoot (n : ℕ) (i : Fin n)
    (α β : ℝ) : ℝ :=
  ((shiftedJacobiMonic n α β).roots.sort (· ≤ ·)).getD i 0

theorem shiftedJacobiMonic_roots_sort_length (n : ℕ) {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) :
    ((shiftedJacobiMonic n α β).roots.sort (· ≤ ·)).length = n := by
  rw [Multiset.length_sort,
    Polynomial.splits_iff_card_roots.mp (shiftedJacobiMonic_splits n hα hβ),
    natDegree_shiftedJacobiMonic n hα hβ]

theorem shiftedJacobiMonicRoot_isRoot (n : ℕ) (i : Fin n)
    {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    (shiftedJacobiMonic n α β).IsRoot
      (shiftedJacobiMonicRoot n i α β) := by
  have hlen := shiftedJacobiMonic_roots_sort_length n hα hβ
  rw [shiftedJacobiMonicRoot,
    List.getD_eq_getElem _ _ (by simp [hlen])]
  apply Polynomial.isRoot_of_mem_roots
  exact (Multiset.mem_sort _).mp (List.getElem_mem ..)

theorem strictMono_shiftedJacobiMonicRoot (n : ℕ) {α β : ℝ}
    (hα : -1 < α) (hβ : -1 < β) :
    StrictMono (fun i : Fin n => shiftedJacobiMonicRoot n i α β) := by
  have hlen := shiftedJacobiMonic_roots_sort_length n hα hβ
  have hstrict := (Multiset.pairwise_sort
    (s := (shiftedJacobiMonic n α β).roots) (r := (· ≤ ·))).sortedLE.sortedLT_of_nodup
      (Multiset.coe_nodup.mp (by
        simpa using shiftedJacobiMonic_roots_nodup n hα hβ))
  intro i j hij
  change ((shiftedJacobiMonic n α β).roots.sort (· ≤ ·)).getD i 0 <
    ((shiftedJacobiMonic n α β).roots.sort (· ≤ ·)).getD j 0
  rw [List.getD_eq_getElem _ _ (by simp [hlen]),
    List.getD_eq_getElem _ _ (by simp [hlen])]
  exact hstrict.getElem_lt_getElem_of_lt hij

theorem exists_shiftedJacobiMonicRoot_eq (n : ℕ) {α β r : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (hr : (shiftedJacobiMonic n α β).IsRoot r) :
    ∃ i : Fin n, shiftedJacobiMonicRoot n i α β = r := by
  have hp_ne := shiftedJacobiMonic_ne_zero n hα hβ
  apply exists_index_eq_of_mem_roots
    (fun i : Fin n => shiftedJacobiMonicRoot n i α β)
    (strictMono_shiftedJacobiMonicRoot n hα hβ)
    (fun i => shiftedJacobiMonicRoot_isRoot n i hα hβ) hp_ne
  · rw [natDegree_shiftedJacobiMonic n hα hβ]
  · exact (Polynomial.mem_roots hp_ne).mpr hr

/-- A simple root of the beta-one monic shifted Jacobi family admits a local
smooth parameter branch. Its derivative is the usual implicit quotient. -/
theorem exists_hasDerivAt_shiftedJacobiMonic_root_alpha
    (n : ℕ) {α r : ℝ} (hα : -1 < α)
    (hr : (shiftedJacobiMonic n α 1).IsRoot r) :
    ∃ ρ : ℝ → ℝ,
      HasDerivAt ρ
        (-((shiftedJacobiMonicAlphaDeriv n α 1).eval r) /
          (shiftedJacobiMonic n α 1).derivative.eval r) α ∧
      ρ α = r ∧
      ∀ᶠ a in 𝓝 α, (shiftedJacobiMonic n a 1).IsRoot (ρ a) := by
  let F : ℝ × ℝ → ℝ := fun z =>
    (shiftedJacobiMonic n z.1 1).eval z.2
  have hcont : ContDiffAt ℝ ∞ F (α, r) :=
    contDiffAt_shiftedJacobiMonic_eval_alpha_prod n hα (by norm_num)
  let A : ℝ →L[ℝ] ℝ :=
    fderiv ℝ F (α, r) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ
  let B : ℝ →L[ℝ] ℝ :=
    fderiv ℝ F (α, r) ∘L ContinuousLinearMap.inl ℝ ℝ ℝ
  have hfull : HasFDerivAt F (fderiv ℝ F (α, r)) (α, r) :=
    (hcont.differentiableAt (by simp)).hasFDerivAt
  have hA : A = ContinuousLinearMap.toSpanSingleton ℝ
      ((shiftedJacobiMonic n α 1).derivative.eval r) := by
    apply HasFDerivAt.unique
    · exact hfull.comp r (hasFDerivAt_prodMk_right α r)
    · exact (shiftedJacobiMonic n α 1).hasFDerivAt r
  have hB : B = ContinuousLinearMap.toSpanSingleton ℝ
      ((shiftedJacobiMonicAlphaDeriv n α 1).eval r) := by
    apply HasFDerivAt.unique
    · exact hfull.comp α (hasFDerivAt_prodMk_left α r)
    · exact (hasDerivAt_shiftedJacobiMonic_eval_alpha n hα
        (by norm_num : (-1 : ℝ) < 1)).hasFDerivAt
  have hspatial : (shiftedJacobiMonic n α 1).derivative.eval r ≠ 0 :=
    shiftedJacobiMonic_derivative_eval_ne_zero n hα (by norm_num) hr
  have hAinv : A.IsInvertible := by
    rw [hA]
    exact ContinuousLinearMap.toSpanSingleton_isInvertible hspatial
  let ρ : ℝ → ℝ := hcont.implicitFunction (by simp) hAinv
  have hρbase : ρ α = r :=
    hcont.implicitFunction_apply_self (by simp) hAinv
  have hρroot : ∀ᶠ a in 𝓝 α,
      (shiftedJacobiMonic n a 1).IsRoot (ρ a) := by
    have heq := hcont.eventually_apply_implicitFunction (by simp) hAinv
    filter_upwards [heq] with a ha
    rw [Polynomial.IsRoot.def]
    change F (a, ρ a) = 0
    simpa only [F, Polynomial.IsRoot.def] using ha.trans (by simpa using hr)
  have hρstrict := hcont.hasStrictFDerivAt_implicitFunction (by simp) hAinv
  have hρderiv : HasDerivAt ρ
      ((-(A.inverse ∘L B)) 1) α := by
    simpa only [ρ, A, B] using hρstrict.hasFDerivAt.hasDerivAt
  have hquotient : (-(A.inverse ∘L B)) 1 =
      -((shiftedJacobiMonicAlphaDeriv n α 1).eval r) /
        (shiftedJacobiMonic n α 1).derivative.eval r := by
    rw [neg_apply, ContinuousLinearMap.comp_apply,
      hB, ContinuousLinearMap.toSpanSingleton_apply, one_smul, hA]
    rw [ContinuousLinearMap.inverse_toSpanSingleton_apply hspatial]
    ring
  refine ⟨ρ, ?_, hρbase, hρroot⟩
  rwa [hquotient] at hρderiv

/-- The ordered beta-one shifted Jacobi roots are differentiable in the first
parameter throughout the orthogonality range. -/
theorem hasDerivAt_shiftedJacobiMonicRoot_alpha
    (n : ℕ) (i : Fin n) {α : ℝ} (hα : -1 < α) :
    HasDerivAt (fun a => shiftedJacobiMonicRoot n i a 1)
      (-((shiftedJacobiMonicAlphaDeriv n α 1).eval
          (shiftedJacobiMonicRoot n i α 1)) /
        (shiftedJacobiMonic n α 1).derivative.eval
          (shiftedJacobiMonicRoot n i α 1)) α := by
  let r : Fin n → ℝ := fun j => shiftedJacobiMonicRoot n j α 1
  have hr_root : ∀ j, (shiftedJacobiMonic n α 1).IsRoot (r j) :=
    fun j => shiftedJacobiMonicRoot_isRoot n j hα (by norm_num)
  have hbranch : ∀ j : Fin n, ∃ ρ : ℝ → ℝ,
      HasDerivAt ρ
        (-((shiftedJacobiMonicAlphaDeriv n α 1).eval (r j)) /
          (shiftedJacobiMonic n α 1).derivative.eval (r j)) α ∧
      ρ α = r j ∧
      ∀ᶠ a in 𝓝 α, (shiftedJacobiMonic n a 1).IsRoot (ρ a) :=
    fun j => exists_hasDerivAt_shiftedJacobiMonic_root_alpha n hα (hr_root j)
  choose ρ hρderiv hρbase hρroot using hbranch
  have hall_roots : ∀ᶠ a in 𝓝 α, ∀ j : Fin n,
      (shiftedJacobiMonic n a 1).IsRoot (ρ j a) := by
    rw [Filter.eventually_all]
    exact hρroot
  have hall_order : ∀ᶠ a in 𝓝 α, StrictMono (fun j : Fin n => ρ j a) := by
    change ∀ᶠ a in 𝓝 α, ∀ ⦃j k : Fin n⦄, j < k → ρ j a < ρ k a
    rw [Filter.eventually_all]
    intro j
    rw [Filter.eventually_all]
    intro k
    by_cases hjk : j < k
    · have hbase : ρ j α < ρ k α := by
        rw [hρbase j, hρbase k]
        exact strictMono_shiftedJacobiMonicRoot n hα (by norm_num) hjk
      exact ((hρderiv j).continuousAt.eventually_lt
        (hρderiv k).continuousAt hbase).mono fun _ h _ => h
    · exact Filter.Eventually.of_forall fun _ h => (hjk h).elim
  have hparam : ∀ᶠ a in 𝓝 α, -1 < a := Ioi_mem_nhds hα
  have hall_eq : ∀ᶠ a in 𝓝 α, ∀ j : Fin n,
      shiftedJacobiMonicRoot n j a 1 = ρ j a := by
    filter_upwards [hall_roots, hall_order, hparam] with a ha_roots ha_order ha
    intro j
    have hsort := Polynomial.roots_sort_eq_of_isRoot
      (shiftedJacobiMonic_ne_zero n ha (by norm_num))
      (natDegree_shiftedJacobiMonic n ha (by norm_num))
      (fun k : Fin n => ρ k a) ha_roots ha_order
    rw [shiftedJacobiMonicRoot, hsort,
      List.getD_eq_getElem _ _ (by simp : j.val < (List.map (fun k : Fin n => ρ k a)
        (List.finRange n)).length)]
    simp
  apply (hρderiv i).congr_of_eventuallyEq
  exact hall_eq.mono fun _ h => h i

theorem shiftedJacobiMonicRoot_alpha_deriv_pos
    (n : ℕ) (i : Fin n) {α : ℝ} (hα : -1 < α) :
    0 < -((shiftedJacobiMonicAlphaDeriv n α 1).eval
          (shiftedJacobiMonicRoot n i α 1)) /
        (shiftedJacobiMonic n α 1).derivative.eval
          (shiftedJacobiMonicRoot n i α 1) := by
  have hroot := shiftedJacobiMonicRoot_isRoot n i
    (α := α) (β := 1) hα (by norm_num)
  have hneg :=
    shiftedJacobiMonicAlphaDeriv_eval_mul_derivative_eval_neg n
      (α := α) (r := shiftedJacobiMonicRoot n i α 1) hα
      (by have := i.isLt; lia) hroot
  rcases mul_neg_iff.mp hneg with h | h
  · exact div_pos_of_neg_of_neg (by linarith) h.2
  · exact div_pos (by linarith) h.2

/-- Every ordered beta-one shifted Jacobi root moves strictly to the right as
the first parameter increases. -/
theorem strictMonoOn_shiftedJacobiMonicRoot_alpha
    (n : ℕ) (i : Fin n) :
    StrictMonoOn (fun a => shiftedJacobiMonicRoot n i a 1)
      (Set.Ioi (-1 : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi (-1 : ℝ))
  · intro a ha
    exact (hasDerivAt_shiftedJacobiMonicRoot_alpha n i
      (by simpa using ha)).continuousAt.continuousWithinAt
  · intro a ha
    have ha' : -1 < a := by simpa using ha
    rw [(hasDerivAt_shiftedJacobiMonicRoot_alpha n i ha').deriv]
    exact shiftedJacobiMonicRoot_alpha_deriv_pos n i ha'

end RealRooted
