import RealRooted.BinaryRunTransformation.Anchor
import RealRooted.BinaryRunTransformation.PointingPencil
import RealRooted.CriticalValueContinuation
import RealRooted.Interlacing.NegativeRoots
import RealRooted.IteratedDerivativeShift
import RealRooted.Hadamard.Newton
import RealRooted.Mathlib.Topology.Algebra.Polynomial
import RealRooted.QuadraticRoot
import Mathlib.Topology.Order.ProjIcc

/-!
# Continuation for the binary-run deformation

This file connects the smooth binary-run family to the generic local root
continuation API.  It is the analytic layer used to prevent collisions while
the scaling parameter increases.
-/

open Filter Polynomial Topology
open scoped ContDiff

namespace RealRooted

noncomputable section

/-- A nondegenerate critical point of the shifted binary-run deformation has
a local `C¹` branch of critical points. -/
theorem exists_contDiffAt_shiftedBinaryRunDeformation_criticalPoint
    {n : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ n) {t x : ℝ}
    (hcritical :
      (shiftedBinaryRunDeformation n p t).derivative.IsRoot x)
    (hregular :
      (shiftedBinaryRunDeformation n p t).derivative.derivative.eval x ≠ 0) :
    ∃ ξ : ℝ → ℝ,
      ContDiffAt ℝ 1 ξ t ∧
        ξ t = x ∧
          ∀ᶠ u in 𝓝 t,
            (shiftedBinaryRunDeformation n p u).derivative.IsRoot (ξ u) := by
  apply exists_contDiffAt_polynomial_root
    (fun u => (shiftedBinaryRunDeformation n p u).derivative)
  · exact (contDiff_derivative_shiftedBinaryRunDeformation_eval_prod hp).contDiffAt.of_le
      (by simp)
  · exact hcritical
  · exact hregular

/-- Along a differentiable branch of critical points, the critical value has
the same parameter derivative as evaluation at a fixed point. -/
theorem hasDerivAt_shiftedBinaryRunDeformation_criticalValue
    {n : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ n) {t x ξ' : ℝ}
    (ht : t ≠ 0) {ξ : ℝ → ℝ} (hξ : HasDerivAt ξ ξ' t)
    (hξbase : ξ t = x)
    (hcritical :
      (shiftedBinaryRunDeformation n p t).derivative.eval x = 0) :
    HasDerivAt
      (fun u => (shiftedBinaryRunDeformation n p u).eval (ξ u))
      ((shiftedBinaryRunPointing n p t).eval x / t) t := by
  let B : ℕ → ℝ[X] := fun m =>
    (binaryRunPolynomial n m).comp (X + 1)
  have hsum : HasDerivAt
      (fun u => ∑ m ∈ Finset.range (n + 1),
        (p.coeff m * u ^ m) * (B m).eval (ξ u))
      (∑ m ∈ Finset.range (n + 1),
        ((p.coeff m * ((m : ℝ) * t ^ (m - 1))) * (B m).eval x +
          (p.coeff m * t ^ m) * ((B m).derivative.eval x * ξ'))) t := by
    apply HasDerivAt.fun_sum
    intro m hm
    convert
      ((hasDerivAt_pow m t).const_mul (p.coeff m)).mul
        (((B m).hasDerivAt (ξ t)).comp t hξ) using 1
    all_goals first
      | rfl
      | simp [Function.comp_apply, hξbase]
  have hfixed : HasDerivAt
      (fun u => ∑ m ∈ Finset.range (n + 1),
        (p.coeff m * u ^ m) * (B m).eval x)
      (∑ m ∈ Finset.range (n + 1),
        (p.coeff m * ((m : ℝ) * t ^ (m - 1))) * (B m).eval x) t := by
    apply HasDerivAt.fun_sum
    intro m hm
    exact ((hasDerivAt_pow m t).const_mul (p.coeff m)).mul_const _
  have hfixed_eq :
      (∑ m ∈ Finset.range (n + 1),
        (p.coeff m * ((m : ℝ) * t ^ (m - 1))) * (B m).eval x) =
        (shiftedBinaryRunPointing n p t).eval x / t := by
    apply HasDerivAt.unique hfixed
    convert hasDerivAt_shiftedBinaryRunDeformation_eval hp ht x using 1
    funext u
    rw [shiftedBinaryRunDeformation_eq_sum_range hp,
      Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, B]
  have hspace_eq :
      (∑ m ∈ Finset.range (n + 1),
        (p.coeff m * t ^ m) * ((B m).derivative.eval x * ξ')) = 0 := by
    have hderiv :
        (shiftedBinaryRunDeformation n p t).derivative.eval x =
          ∑ m ∈ Finset.range (n + 1),
            (p.coeff m * t ^ m) * (B m).derivative.eval x := by
      rw [shiftedBinaryRunDeformation_eq_sum_range hp]
      simp only [Polynomial.derivative_sum, Polynomial.derivative_C_mul,
        Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, B]
    calc
      _ = (∑ m ∈ Finset.range (n + 1),
          (p.coeff m * t ^ m) * (B m).derivative.eval x) * ξ' := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro m hm
        ring
      _ = 0 := by rw [← hderiv, hcritical, zero_mul]
  convert hsum using 1
  · funext u
    rw [shiftedBinaryRunDeformation_eq_sum_range hp,
      Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, B]
  · rw [Finset.sum_add_distrib, hfixed_eq, hspace_eq, add_zero]

/-- The squared critical value has derivative `2 Q Qₜ` along any
differentiable critical-point branch. -/
theorem hasDerivAt_sq_shiftedBinaryRunDeformation_criticalValue
    {n : ℕ} {p : ℝ[X]} (hp : p.natDegree ≤ n) {t x ξ' : ℝ}
    (ht : t ≠ 0) {ξ : ℝ → ℝ} (hξ : HasDerivAt ξ ξ' t)
    (hξbase : ξ t = x)
    (hcritical :
      (shiftedBinaryRunDeformation n p t).derivative.eval x = 0) :
    HasDerivAt
      (fun u =>
        ((shiftedBinaryRunDeformation n p u).eval (ξ u)) ^ 2)
      (2 * (shiftedBinaryRunDeformation n p t).eval x *
        ((shiftedBinaryRunPointing n p t).eval x / t)) t := by
  have hvalue := hasDerivAt_shiftedBinaryRunDeformation_criticalValue
    hp ht hξ hξbase hcritical
  convert hvalue.pow 2 using 1
  rw [hξbase]
  ring

/-- The pointing-pencil sign makes every squared critical value move
nondecreasingly while the shifted deformation is split and the critical value
is nonzero. -/
theorem shiftedBinaryRunDeformation_sqCriticalValue_deriv_nonneg
    {n : ℕ} (hn : 4 ≤ n) {p : ℝ[X]} (hp : IsPFPolynomial p)
    (hp0 : p ≠ 0) (hdegree : p.natDegree ≤ n) {t x : ℝ}
    (ht : 0 < t) (hx : x < 0)
    (hcritical :
      (shiftedBinaryRunDeformation n p t).derivative.eval x = 0)
    (hsplits : (shiftedBinaryRunDeformation n p t).Splits)
    (hpositiveDegree :
      1 ≤ (shiftedBinaryRunDeformation n p t).natDegree)
    (hvalue : (shiftedBinaryRunDeformation n p t).eval x ≠ 0) :
    0 ≤ 2 * (shiftedBinaryRunDeformation n p t).eval x *
      ((shiftedBinaryRunPointing n p t).eval x / t) := by
  let Q := shiftedBinaryRunDeformation n p t
  let A := (shiftedBinaryRunPointing n p t).eval x
  let B := Q.derivative.derivative.eval x
  let C := Q.eval x
  have hBC : B * C < 0 := by
    have hstrict := deriv2_mul_lt_deriv_sq_at_non_root
      hsplits hpositiveDegree hvalue
    rw [hcritical] at hstrict
    norm_num [Q, B, C] at hstrict ⊢
    exact hstrict
  have hAB : A * B ≤ 0 :=
    binaryRunDeformation_critical_sign_of_neg
      hn hp hp0 hdegree ht hx hcritical
  have hAC : 0 ≤ A * C := by
    rcases mul_neg_iff.mp hBC with ⟨hBpos, hCneg⟩ | ⟨hBneg, hCpos⟩
    · have hAnonpos : A ≤ 0 := by
        by_contra h
        exact (not_le_of_gt (mul_pos (lt_of_not_ge h) hBpos)) hAB
      exact mul_nonneg_of_nonpos_of_nonpos hAnonpos hCneg.le
    · have hAnonneg : 0 ≤ A := by
        by_contra h
        exact (not_le_of_gt (mul_pos_of_neg_of_neg (lt_of_not_ge h) hBneg)) hAB
      exact mul_nonneg hAnonneg hCpos.le
  have hdiv : 0 ≤ (C * A) / t :=
    div_nonneg (by simpa [mul_comm] using hAC) ht.le
  change 0 ≤ 2 * C * (A / t)
  calc
    0 ≤ 2 * ((C * A) / t) := mul_nonneg (by norm_num) hdiv
    _ = 2 * C * (A / t) := by field_simp

/-- At a positive parameter where the shifted deformation has maximal degree,
is PF, and has a positive critical-value margin, the same PF and margin
conditions persist in a right neighborhood. -/
theorem shiftedBinaryRunDeformation_pf_criticalValueMargin_eventually_right
    {n : ℕ} (hn : 4 ≤ n) {p : ℝ[X]} (hp : IsPFPolynomial p)
    (hp0 : p ≠ 0) (hdegree : p.natDegree ≤ n) {t δ : ℝ}
    (ht : 0 < t) (hδ : 0 < δ)
    (hQdegree :
      (shiftedBinaryRunDeformation n p t).natDegree = (n + 1) / 2)
    (hQpf : IsPFPolynomial (shiftedBinaryRunDeformation n p t))
    (hmargin : ∀ x,
      (shiftedBinaryRunDeformation n p t).derivative.IsRoot x →
        δ ≤ (shiftedBinaryRunDeformation n p t).eval x ^ 2) :
    ∀ᶠ u in 𝓝[>] t,
      IsPFPolynomial (shiftedBinaryRunDeformation n p u) ∧
        ∀ x, (shiftedBinaryRunDeformation n p u).derivative.IsRoot x →
          δ ≤ (shiftedBinaryRunDeformation n p u).eval x ^ 2 := by
  let D := (n + 1) / 2
  let Q : ℝ → ℝ[X] := fun u => shiftedBinaryRunDeformation n p u
  let R : ℝ → ℝ[X] := fun u => (Q u).derivative
  have hDpos : 0 < D := by
    dsimp [D]
    lia
  have hQ0 : Q t ≠ 0 := by
    intro hzero
    have hzeroDegree : (Q t).natDegree = 0 := by simp [hzero]
    rw [hQdegree] at hzeroDegree
    lia
  have hQsplit : (Q t).Splits :=
    (hQpf.ne_zero_and_splits hQ0).2
  have hQcoeff0 : (Q t).coeff 0 ≠ 0 := by
    change (shiftedBinaryRunDeformation n p t).coeff 0 ≠ 0
    rw [coeff_zero_shiftedBinaryRunDeformation hdegree]
    exact (eval_pos_of_hasNonnegCoeffs hp.hasNonnegCoeffs hp0 ht).ne'
  have hQrootsNeg : ∀ x, (Q t).IsRoot x → x < 0 := by
    intro x hx
    have hxmem : x ∈ (Q t).roots :=
      (Polynomial.mem_roots hQ0).mpr hx
    apply lt_of_le_of_ne (hQpf.roots_nonpos x hxmem)
    intro hxzero
    subst x
    exact hQcoeff0 <| by
      simpa [Polynomial.IsRoot.def,
        Polynomial.coeff_zero_eq_eval_zero] using hx
  have hcriticalNeg : ∀ x, (Q t).derivative.IsRoot x → x < 0 := by
    apply roots_neg_of_interlaces_of_right_roots_neg
      (derivative_interlaces hQsplit <| by
        rw [hQdegree]
        lia)
    exact hQrootsNeg
  have hQsimple : HasSimpleRoots (Q t) :=
    hasSimpleRoots_of_criticalValueMargin hQ0 hδ hmargin
  have hQdegree' : (Q t).natDegree = D := hQdegree
  have hQdegreeEvent : ∀ᶠ u in 𝓝 t, (Q u).natDegree = D := by
    apply Polynomial.eventually_natDegree_eq_of_le_of_continuous_coeff
      Q hQdegree' hQ0
    · intro u
      exact natDegree_shiftedBinaryRunDeformation_le hdegree u
    · intro k
      exact (contDiff_coeff_shiftedBinaryRunDeformation hdegree k).continuous
  obtain ⟨ζ, hζbase, hζlocal⟩ :=
    exists_eventually_polynomial_root_branches Q hDpos.ne'
      hQdegreeEvent hQsplit hQsimple fun x _ =>
        by simpa only [Q] using
          (contDiff_shiftedBinaryRunDeformation_eval_prod
            hdegree).contDiffAt.of_le (by norm_num)
  have hRdegreeEvent : ∀ᶠ u in 𝓝 t, (R u).natDegree = D - 1 := by
    filter_upwards [hQdegreeEvent] with u hu
    change (Q u).derivative.natDegree = D - 1
    rw [Polynomial.natDegree_derivative, hu]
  have hR0 : R t ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr <| by
      rw [hQdegree']
      exact hDpos.ne'
  have hRsplit : (R t).Splits :=
    (hQpf.derivative.ne_zero_and_splits hR0).2
  have hRsimple : HasSimpleRoots (R t) :=
    hQsimple.derivative_of_splits hQsplit <| by
      rw [hQdegree']
      exact hDpos.ne'
  have hDsub : D - 1 ≠ 0 := by
    dsimp [D]
    lia
  obtain ⟨ξ, hξbase, hξlocal⟩ :=
    exists_eventually_polynomial_root_branches R hDsub
      hRdegreeEvent hRsplit hRsimple fun x _ =>
        by simpa only [R, Q] using
          (contDiff_derivative_shiftedBinaryRunDeformation_eval_prod
            hdegree).contDiffAt.of_le (by norm_num)
  have hξlocal_t := hξlocal.self_of_nhds
  have hξroot_t (i) : R t |>.IsRoot (ξ i t) :=
    (hξlocal_t.2.2.2 (ξ i t)).2 ⟨i, rfl⟩
  have hξneg : ∀ᶠ u in 𝓝 t, ∀ i, ξ i u < 0 := by
    rw [Filter.eventually_all]
    intro i
    apply (hξlocal_t.2.2.1 i).continuousAt.eventually_lt continuousAt_const
    exact hcriticalNeg (ξ i t) (hξroot_t i)
  have hξvalue0 (i) : (Q t).eval (ξ i t) ≠ 0 := by
    intro hzero
    have hbound := hmargin (ξ i t) (hξroot_t i)
    rw [hzero] at hbound
    norm_num at hbound
    linarith
  have hξvalue : ∀ᶠ u in 𝓝 t, ∀ i, (Q u).eval (ξ i u) ≠ 0 := by
    rw [Filter.eventually_all]
    intro i
    have hcont : ContinuousAt (fun u => (Q u).eval (ξ i u)) t :=
      (contDiff_shiftedBinaryRunDeformation_eval_prod
        hdegree).continuous.continuousAt.comp
          (continuousAt_id.prodMk (hξlocal_t.2.2.1 i).continuousAt)
    exact hcont.eventually_ne (hξvalue0 i)
  have hpos : ∀ᶠ u in 𝓝 t, 0 < u :=
    continuousAt_const.eventually_lt continuousAt_id ht
  have hlocal : ∀ᶠ u in 𝓝 t,
      (∀ x, (Q u).derivative.IsRoot x → ∃ i, ξ i u = x) ∧
        ∀ i, ∃ v,
          HasDerivAt (fun s => (Q s).eval (ξ i s) ^ 2) v u ∧
            0 ≤ v := by
    filter_upwards [hζlocal, hξlocal, hQdegreeEvent, hξneg,
      hξvalue, hpos] with u hQu hRu hQdegreeu hξnegu hξvalueu hupos
    constructor
    · intro x hx
      exact (hRu.2.2.2 x).1 hx
    · intro i
      have hcritical : (Q u).derivative.eval (ξ i u) = 0 :=
        (hRu.2.2.2 (ξ i u)).2 ⟨i, rfl⟩
      have hξderiv : HasDerivAt (ξ i) (deriv (ξ i) u) u :=
        (hRu.2.2.1 i).differentiableAt (by norm_num) |>.hasDerivAt
      let v := 2 * (Q u).eval (ξ i u) *
        ((shiftedBinaryRunPointing n p u).eval (ξ i u) / u)
      refine ⟨v, ?_, ?_⟩
      · exact hasDerivAt_sq_shiftedBinaryRunDeformation_criticalValue
          hdegree hupos.ne' hξderiv rfl hcritical
      · exact shiftedBinaryRunDeformation_sqCriticalValue_deriv_nonneg
          hn hp hp0 hdegree hupos (hξnegu i) hcritical hQu.1
          (by rw [hQdegreeu]; exact hDpos) (hξvalueu i)
  have hbase : ∀ i, δ ≤ (Q t).eval (ξ i t) ^ 2 :=
    fun i => hmargin (ξ i t) (hξroot_t i)
  have hmarginRight :=
    criticalValueMargin_eventually_right_of_branches Q ξ hbase hlocal
  have hQright : ∀ᶠ u in 𝓝[>] t,
      (Q u).Splits ∧ HasSimpleRoots (Q u) :=
    hζlocal.filter_mono inf_le_left |>.mono fun _ hu => ⟨hu.1, hu.2.1⟩
  filter_upwards [hmarginRight, hQright,
    (self_mem_nhdsWithin : ∀ᶠ u : ℝ in 𝓝[>] t, u ∈ Set.Ioi t)]
    with u humargin hQu hut
  refine ⟨IsPFPolynomial.of_realRooted_nonneg
    (hp.hasNonnegCoeffs.shiftedBinaryRunDeformation hdegree <| by
      exact ht.le.trans (le_of_lt hut)) hQu.1, humargin⟩

/-- A positive critical-value margin propagates across a compact positive
parameter interval.  The closedness step uses a clamped family so that the
fixed-degree hypothesis holds globally. -/
theorem shiftedBinaryRunDeformation_pf_criticalValueMargin_Icc
    {n : ℕ} (hn : 4 ≤ n) {p : ℝ[X]} (hp : IsPFPolynomial p)
    (hp0 : p ≠ 0) (hdegree : p.natDegree ≤ n) {a b δ : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hδ : 0 < δ)
    (hQdegree : ∀ u ∈ Set.Icc a b,
      (shiftedBinaryRunDeformation n p u).natDegree = (n + 1) / 2)
    (haPF : IsPFPolynomial (shiftedBinaryRunDeformation n p a))
    (haMargin : ∀ x,
      (shiftedBinaryRunDeformation n p a).derivative.IsRoot x →
        δ ≤ (shiftedBinaryRunDeformation n p a).eval x ^ 2) :
    ∀ u ∈ Set.Icc a b,
      IsPFPolynomial (shiftedBinaryRunDeformation n p u) ∧
        ∀ x, (shiftedBinaryRunDeformation n p u).derivative.IsRoot x →
          δ ≤ (shiftedBinaryRunDeformation n p u).eval x ^ 2 := by
  let Q : ℝ → ℝ[X] := fun u => shiftedBinaryRunDeformation n p u
  let S : Set ℝ := {u |
    IsPFPolynomial (Q u) ∧
      ∀ x, (Q u).derivative.IsRoot x → δ ≤ (Q u).eval x ^ 2}
  let c : ℝ → ℝ := fun u => (Set.projIcc a b hab u : ℝ)
  let P : ℝ → ℝ[X] := fun u => Q (c u)
  have hc : Continuous c :=
    continuous_subtype_val.comp continuous_projIcc
  have hPdegree : ∀ u, (P u).natDegree = (n + 1) / 2 := by
    intro u
    apply hQdegree (c u)
    exact (Set.projIcc a b hab u).2
  have hPcoeff : ∀ k : ℕ, Continuous fun u => (P u).coeff k :=
    fun k => (contDiff_coeff_shiftedBinaryRunDeformation
      hdegree k).continuous.comp hc
  have hD : 2 ≤ (n + 1) / 2 := by lia
  have hPclosed := isClosed_isPFPolynomial_and_criticalValueMargin
    P hD hPdegree hPcoeff δ
  have hclosed : IsClosed (S ∩ Set.Icc a b) := by
    have heq : S ∩ Set.Icc a b =
        {u | IsPFPolynomial (P u) ∧
          ∀ x, (P u).derivative.IsRoot x → δ ≤ (P u).eval x ^ 2} ∩
            Set.Icc a b := by
      ext u
      constructor
      · rintro ⟨hu, huIcc⟩
        refine ⟨?_, huIcc⟩
        simpa [S, P, Q, c, Set.projIcc_of_mem hab huIcc] using hu
      · rintro ⟨hu, huIcc⟩
        refine ⟨?_, huIcc⟩
        simpa [S, P, Q, c, Set.projIcc_of_mem hab huIcc] using hu
    rw [heq]
    exact hPclosed.inter isClosed_Icc
  have haS : a ∈ S :=
    ⟨haPF, haMargin⟩
  have hforward : ∀ u ∈ S ∩ Set.Ico a b, S ∈ 𝓝[>] u := by
    intro u hu
    have huIcc : u ∈ Set.Icc a b := ⟨hu.2.1, hu.2.2.le⟩
    have hupos : 0 < u := ha.trans_le hu.2.1
    change ∀ᶠ v in 𝓝[>] u,
      IsPFPolynomial (shiftedBinaryRunDeformation n p v) ∧
        ∀ x, (shiftedBinaryRunDeformation n p v).derivative.IsRoot x →
          δ ≤ (shiftedBinaryRunDeformation n p v).eval x ^ 2
    exact shiftedBinaryRunDeformation_pf_criticalValueMargin_eventually_right
      hn hp hp0 hdegree hupos hδ (hQdegree u huIcc) hu.1.1 hu.1.2
  have hsub : Set.Icc a b ⊆ S :=
    hclosed.Icc_subset_of_forall_mem_nhdsWithin haS hforward
  intro u hu
  exact hsub hu

/-- A regular PF input admits a positive starting scale carrying a uniform
critical-value margin.  Regularity here means that the coefficient at the
maximal possible output degree is positive. -/
theorem exists_pos_shiftedBinaryRunDeformation_anchor
    {n : ℕ} (hn : 4 ≤ n) {p : ℝ[X]} (hp : IsPFPolynomial p)
    (hpdeg : p.natDegree ≤ n) (hp0 : 0 < p.coeff 0)
    (hpTop : 0 < p.coeff ((n + 1) / 2)) :
    ∃ a δ : ℝ, 0 < a ∧ a ≤ 1 ∧ 0 < δ ∧
      (shiftedBinaryRunDeformation n p a).natDegree = (n + 1) / 2 ∧
      IsPFPolynomial (shiftedBinaryRunDeformation n p a) ∧
      ∀ x, (shiftedBinaryRunDeformation n p a).derivative.IsRoot x →
        δ ≤ (shiftedBinaryRunDeformation n p a).eval x ^ 2 := by
  let D := (n + 1) / 2
  let P : ℝ → ℝ[X] := fun t ↦ rescaledBinaryRunDeformation n p t
  have hPdegree0 : (P 0).natDegree = D :=
    natDegree_rescaledBinaryRunDeformation_eq (by lia)
      hp.hasNonnegCoeffs hpTop le_rfl
  have hPanchor : P 0 = binaryRunAnchor n p :=
    rescaledBinaryRunDeformation_zero n p
  have hPsimple : HasSimpleRoots (P 0) := by
    rw [hPanchor]
    exact binaryRunAnchor_hasSimpleRoots (by lia) hp hpdeg hp0
  have hPsplit : (P 0).Splits := by
    rw [hPanchor]
    exact ((isPFPolynomial_binaryRunAnchor hp hpdeg).ne_zero_and_splits
      (by rw [← hPanchor]; exact hPsimple.ne_zero)).2
  have hPdegree : ∀ᶠ t in nhds (0 : ℝ), (P t).natDegree = D := by
    apply Polynomial.eventually_natDegree_eq_of_le_of_continuous_coeff
      P hPdegree0 hPsimple.ne_zero
    · intro t
      exact natDegree_rescaledBinaryRunDeformation_le n p t
    · intro k
      exact (contDiff_coeff_rescaledBinaryRunDeformation n p k).continuous
  obtain ⟨ξ, _hξbase, hlocal⟩ :=
    exists_eventually_polynomial_root_branches P (by dsimp [D]; lia)
      hPdegree hPsplit hPsimple fun x _ ↦ by
        simpa only [P] using
          (contDiff_rescaledBinaryRunDeformation_eval_prod n p).contDiffAt.of_le
            (by norm_num)
  have hgood : ∀ᶠ t in nhds (0 : ℝ),
      (P t).Splits ∧ HasSimpleRoots (P t) :=
    hlocal.mono fun t ht ↦ ⟨ht.1, ht.2.1⟩
  rcases Metric.mem_nhds_iff.mp hgood with ⟨ρ, hρ, hball⟩
  let a : ℝ := min (ρ / 2) (1 / 2)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have haρ : a < ρ :=
    (min_le_left (ρ / 2) (1 / 2 : ℝ)).trans_lt (half_lt_self hρ)
  have ha1 : a ≤ 1 := by
    dsimp [a]
    linarith [min_le_right (ρ / 2) (1 / 2 : ℝ)]
  have hPa : (P a).Splits ∧ HasSimpleRoots (P a) := by
    apply hball
    simpa [Real.dist_eq, abs_of_pos ha] using haρ
  have hPaPF : IsPFPolynomial (P a) :=
    IsPFPolynomial.of_realRooted_nonneg
      (hp.hasNonnegCoeffs.rescaledBinaryRunDeformation ha.le) hPa.1
  have hordPF :
      IsPFPolynomial (binaryRunTransform n (scalePolynomial a p)) := by
    rw [← rescaledBinaryRunDeformation_comp_scale hpdeg a]
    simpa using hPaPF.comp_C_mul_X_add_C
      (a := a) (d := 0) ha (by norm_num)
  have hordSimple :
      HasSimpleRoots (binaryRunTransform n (scalePolynomial a p)) := by
    rw [← rescaledBinaryRunDeformation_comp_scale hpdeg a]
    simpa using hPa.2.comp_C_mul_X_add_C
      (a := a) (b := 0) ha.ne'
  have hshiftPF :
      IsPFPolynomial (shiftedBinaryRunDeformation n p a) := by
    simpa [shiftedBinaryRunDeformation] using
      hordPF.comp_C_mul_X_add_C (a := 1) (d := 1) (by norm_num) (by norm_num)
  have hshiftSimple :
      HasSimpleRoots (shiftedBinaryRunDeformation n p a) := by
    simpa [shiftedBinaryRunDeformation] using
      hordSimple.comp_C_mul_X_add_C (a := 1) (b := 1) (by norm_num)
  obtain ⟨δ, hδ, hmargin⟩ := hshiftSimple.exists_pos_criticalValueMargin
    (by rw [natDegree_shiftedBinaryRunDeformation_eq (by lia)
      hp.hasNonnegCoeffs hpdeg hpTop ha]; dsimp [D]; lia)
  refine ⟨a, δ, ha, ha1, hδ,
    natDegree_shiftedBinaryRunDeformation_eq (by lia)
      hp.hasNonnegCoeffs hpdeg hpTop ha, hshiftPF, hmargin⟩

/-- The binary-run transform preserves PF polynomials satisfying the two
strict coefficient conditions needed by the constant-degree continuation. -/
theorem isPFPolynomial_binaryRunTransform_of_regular
    {n : ℕ} (hn : 4 ≤ n) {p : ℝ[X]} (hp : IsPFPolynomial p)
    (hpdeg : p.natDegree ≤ n) (hp0 : 0 < p.coeff 0)
    (hpTop : 0 < p.coeff ((n + 1) / 2)) :
    IsPFPolynomial (binaryRunTransform n p) := by
  obtain ⟨a, δ, ha, ha1, hδ, haDegree, haPF, haMargin⟩ :=
    exists_pos_shiftedBinaryRunDeformation_anchor hn hp hpdeg hp0 hpTop
  have hdegree : ∀ u ∈ Set.Icc a 1,
      (shiftedBinaryRunDeformation n p u).natDegree = (n + 1) / 2 :=
    fun _ hu => natDegree_shiftedBinaryRunDeformation_eq (by lia)
      hp.hasNonnegCoeffs hpdeg hpTop (ha.trans_le hu.1)
  have hall := shiftedBinaryRunDeformation_pf_criticalValueMargin_Icc
    hn hp (by
      intro hpzero
      rw [hpzero] at hp0
      simp at hp0) hpdeg ha ha1 hδ hdegree haPF haMargin
  have hone := hall 1 (Set.right_mem_Icc.mpr ha1)
  have honeDegree := hdegree 1 (Set.right_mem_Icc.mpr ha1)
  have hshiftNe : shiftedBinaryRunDeformation n p 1 ≠ 0 := by
    intro hzero
    rw [hzero] at honeDegree
    simp at honeDegree
    lia
  have hshiftSplit : (shiftedBinaryRunDeformation n p 1).Splits :=
    (hone.1.ne_zero_and_splits hshiftNe).2
  have hback := isRealRooted_comp_X_add_C hshiftNe hshiftSplit (-1)
  have houtSplit : (binaryRunTransform n p).Splits := by
    simpa [shiftedBinaryRunDeformation, scalePolynomial,
      Polynomial.comp_assoc, add_assoc] using hback.2
  exact IsPFPolynomial.of_realRooted_nonneg
    hp.hasNonnegCoeffs.binaryRunTransform houtSplit

/-- Reflection and a small positive translation regularize every PF input
with positive constant coefficient while staying inside the degree box. -/
theorem isPFPolynomial_binaryRunTransform_of_coeff_zero_pos
    {n : ℕ} (hn : 4 ≤ n) {p : ℝ[X]} (hp : IsPFPolynomial p)
    (hpdeg : p.natDegree ≤ n) (hp0 : 0 < p.coeff 0) :
    IsPFPolynomial (binaryRunTransform n p) := by
  let q : ℝ[X] := p.reflect n
  let r : ℝ → ℝ[X] := fun u ↦ (q.comp (X + C u)).reflect n
  have hqPF : IsPFPolynomial q := isPFPolynomial_reflect hp hpdeg
  have hqdegree : q.natDegree = n :=
    DegreeDropReversal.natDegree_reflect_eq_of_coeff_zero_ne hpdeg hp0.ne'
  have hq0 : q ≠ 0 := by
    intro hzero
    rw [hzero] at hqdegree
    simp at hqdegree
    lia
  have htranslatedDegree (u : ℝ) :
      (q.comp (X + C u)).natDegree = n := by
    rw [Polynomial.natDegree_comp, hqdegree]
    simp
  have hrdegree (u : ℝ) : (r u).natDegree ≤ n := by
    dsimp [r]
    calc
      _ ≤ max n (q.comp (X + C u)).natDegree :=
        Polynomial.natDegree_reflect_le
      _ = n := by rw [htranslatedDegree]; simp
  have hrPF {u : ℝ} (hu : 0 < u) : IsPFPolynomial (r u) := by
    apply isPFPolynomial_reflect
    · simpa using hqPF.comp_C_mul_X_add_C
        (a := 1) (d := u) (by norm_num) hu.le
    · rw [htranslatedDegree]
  have hrCoeffPos {u : ℝ} (hu : 0 < u) {k : ℕ} (hk : k ≤ n) :
      0 < (r u).coeff k := by
    change 0 < ((q.comp (X + C u)).reflect n).coeff k
    rw [Polynomial.coeff_reflect, Polynomial.revAt_le hk]
    apply hqPF.hasNonnegCoeffs.coeff_comp_X_add_C_pos
      hq0 hu
    rw [hqdegree]
    exact Nat.sub_le n k
  have hregular {u : ℝ} (hu : 0 < u) :
      IsPFPolynomial (binaryRunTransform n (r u)) := by
    apply isPFPolynomial_binaryRunTransform_of_regular hn (hrPF hu)
      (hrdegree u)
    · exact hrCoeffPos hu (Nat.zero_le n)
    · exact hrCoeffPos hu (by lia)
  have hrCoeffContinuous (m : ℕ) : Continuous fun u ↦ (r u).coeff m := by
    rw [show (fun u ↦ (r u).coeff m) = fun u ↦
        (q.comp (X + C u)).coeff (Polynomial.revAt n m) by
      funext u
      simp only [r, Polynomial.coeff_reflect]]
    exact q.continuous_coeff_comp_X_add_C _
  have houtCoeffContinuous (k : ℕ) :
      Continuous fun u ↦ (binaryRunTransform n (r u)).coeff k := by
    simp_rw [coeff_binaryRunTransform_eq_sum_range (hrdegree _) k]
    apply continuous_finsetSum
    intro m hm
    exact (hrCoeffContinuous m).mul_const _
  have hlimit : IsPFPolynomial (binaryRunTransform n (r 0)) := by
    apply IsPFPolynomial.of_coeff_tendsto
      (p := fun j ↦ binaryRunTransform n (r (1 / (j + 1 : ℝ))))
    · intro j
      apply hregular
      positivity
    · intro k
      exact (houtCoeffContinuous k).tendsto 0 |>.comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa [r, q, Polynomial.reflect_reflect] using hlimit

/-- For `n ≥ 4`, the binary-run transform preserves every PF polynomial in
the degree-`n` box. -/
theorem isPFPolynomial_binaryRunTransform_of_four_le
    {n : ℕ} (hn : 4 ≤ n) {p : ℝ[X]} (hp : IsPFPolynomial p)
    (hpdeg : p.natDegree ≤ n) :
    IsPFPolynomial (binaryRunTransform n p) := by
  by_cases hpzero : p = 0
  · subst p
    simp [IsPFPolynomial.zero]
  let r : ℝ → ℝ[X] := fun u ↦ p.comp (X + C u)
  have hrdegree (u : ℝ) : (r u).natDegree ≤ n := by
    dsimp [r]
    rw [Polynomial.natDegree_comp]
    simpa using hpdeg
  have hregular {u : ℝ} (hu : 0 < u) :
      IsPFPolynomial (binaryRunTransform n (r u)) := by
    apply isPFPolynomial_binaryRunTransform_of_coeff_zero_pos hn
      (by
        dsimp [r]
        simpa using hp.comp_C_mul_X_add_C
          (a := 1) (d := u) (by norm_num) hu.le)
      (hrdegree u)
    change 0 < (p.comp (X + C u)).coeff 0
    simpa [Polynomial.coeff_zero_eq_eval_zero] using
      eval_pos_of_hasNonnegCoeffs hp.hasNonnegCoeffs hpzero hu
  have hrCoeffContinuous (m : ℕ) : Continuous fun u ↦ (r u).coeff m :=
    p.continuous_coeff_comp_X_add_C m
  have houtCoeffContinuous (k : ℕ) :
      Continuous fun u ↦ (binaryRunTransform n (r u)).coeff k := by
    simp_rw [coeff_binaryRunTransform_eq_sum_range (hrdegree _) k]
    apply continuous_finsetSum
    intro m hm
    exact (hrCoeffContinuous m).mul_const _
  have hlimit : IsPFPolynomial (binaryRunTransform n (r 0)) := by
    apply IsPFPolynomial.of_coeff_tendsto
      (p := fun j ↦ binaryRunTransform n (r (1 / (j + 1 : ℝ))))
    · intro j
      apply hregular
      positivity
    · intro k
      exact (houtCoeffContinuous k).tendsto 0 |>.comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa [r] using hlimit

private theorem coeff_zero_binaryRunTransform_three {p : ℝ[X]}
    (hpdeg : p.natDegree ≤ 3) :
    (binaryRunTransform 3 p).coeff 0 = p.coeff 0 := by
  rw [coeff_binaryRunTransform_eq_sum_range hpdeg]
  norm_num [Finset.sum_range_succ, binaryRunPolynomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial, Polynomial.coeff_one]

private theorem coeff_one_binaryRunTransform_three {p : ℝ[X]}
    (hpdeg : p.natDegree ≤ 3) :
    (binaryRunTransform 3 p).coeff 1 =
      p.coeff 1 + 2 * p.coeff 2 / 3 + p.coeff 3 := by
  rw [coeff_binaryRunTransform_eq_sum_range hpdeg]
  norm_num [Finset.sum_range_succ, binaryRunPolynomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial, Polynomial.coeff_one]
  ring_nf

private theorem coeff_two_binaryRunTransform_three {p : ℝ[X]}
    (hpdeg : p.natDegree ≤ 3) :
    (binaryRunTransform 3 p).coeff 2 = p.coeff 2 / 3 := by
  rw [coeff_binaryRunTransform_eq_sum_range hpdeg]
  norm_num [Finset.sum_range_succ, binaryRunPolynomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial, Polynomial.coeff_one]
  ring

private theorem isPFPolynomial_binaryRunTransform_of_le_three
    {n : ℕ} (hn : n ≤ 3) {p : ℝ[X]} (hp : IsPFPolynomial p)
    (hpdeg : p.natDegree ≤ n) :
    IsPFPolynomial (binaryRunTransform n p) := by
  let q := binaryRunTransform n p
  have hqnn : HasNonnegCoeffs q := hp.hasNonnegCoeffs.binaryRunTransform
  by_cases hn3 : n = 3
  · subst n
    have hqdeg : q.natDegree ≤ 2 :=
      natDegree_binaryRunTransform_le hpdeg
    have hpSplit : p.Splits := by
      rcases hp.eq_zero_or_splits with hpzero | hsplit
      · simp [hpzero]
      · exact hsplit
    have hnewton :=
      two_mul_coeff_zero_mul_coeff_two_le_coeff_one_sq_of_splits_of_natDegree_le
        (n := 3) (by norm_num) hpdeg hpSplit
    have hq0 : q.coeff 0 = p.coeff 0 :=
      coeff_zero_binaryRunTransform_three hpdeg
    have hq1 : q.coeff 1 =
        p.coeff 1 + 2 * p.coeff 2 / 3 + p.coeff 3 :=
      coeff_one_binaryRunTransform_three hpdeg
    have hq2 : q.coeff 2 = p.coeff 2 / 3 :=
      coeff_two_binaryRunTransform_three hpdeg
    have hdisc : 4 * q.coeff 2 * q.coeff 0 ≤ q.coeff 1 ^ 2 := by
      rw [hq0, hq1, hq2]
      have hp0 := hp.hasNonnegCoeffs 0
      have hp1 := hp.hasNonnegCoeffs 1
      have hp2 := hp.hasNonnegCoeffs 2
      have hp3 := hp.hasNonnegCoeffs 3
      have htail : 0 ≤ 2 * p.coeff 2 / 3 + p.coeff 3 := by positivity
      have hsquare : p.coeff 1 ^ 2 ≤
          (p.coeff 1 + 2 * p.coeff 2 / 3 + p.coeff 3) ^ 2 := by
        nlinarith [mul_nonneg hp1 htail,
          sq_nonneg (2 * p.coeff 2 / 3 + p.coeff 3)]
      norm_num at hnewton
      nlinarith [mul_nonneg hp0 hp2]
    have hqSplit : q.Splits := by
      by_cases hq2zero : q.coeff 2 = 0
      · apply Polynomial.Splits.of_natDegree_le_one
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro k hk
        rcases eq_or_lt_of_le (show 2 ≤ k by lia) with rfl | hk2
        · exact hq2zero
        · exact Polynomial.coeff_eq_zero_of_natDegree_lt
            (lt_of_le_of_lt hqdeg hk2)
      · rw [Polynomial.eq_quadratic_of_degree_le_two
          (Polynomial.degree_le_of_natDegree_le hqdeg)]
        exact quadraticPoly_splits_of_le (lt_of_le_of_ne (hqnn 2) <|
          Ne.symm hq2zero) hdisc
    exact IsPFPolynomial.of_realRooted_nonneg hqnn hqSplit
  · have hn2 : n ≤ 2 := by lia
    apply IsPFPolynomial.of_realRooted_nonneg hqnn
    apply Polynomial.Splits.of_natDegree_le_one
    exact (natDegree_binaryRunTransform_le hpdeg).trans <| by
      have : (n + 1) / 2 ≤ 1 := by lia
      exact this

/-- The normalized binary-run basis transformation preserves PF polynomials,
equivalently real-rooted polynomials with nonnegative coefficients and
nonpositive zeros, in every finite degree box. -/
theorem IsPFPolynomial.binaryRunTransform
    {n : ℕ} {p : ℝ[X]} (hp : IsPFPolynomial p)
    (hpdeg : p.natDegree ≤ n) :
    IsPFPolynomial (binaryRunTransform n p) := by
  by_cases hn : 4 ≤ n
  · exact isPFPolynomial_binaryRunTransform_of_four_le hn hp hpdeg
  · exact isPFPolynomial_binaryRunTransform_of_le_three (by lia) hp hpdeg

end

end RealRooted
