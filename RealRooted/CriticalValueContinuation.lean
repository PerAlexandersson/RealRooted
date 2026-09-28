import RealRooted.PFPolynomial.Closure
import RealRooted.SimpleRoots
import RealRooted.Mathlib.Analysis.Normed.Field.Approximation
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Continuation of simple polynomial roots

This file packages the local implicit-function input used by critical-value
continuation arguments.  It deliberately records only a smooth local root
branch; formulas for the branch derivative belong in downstream applications.
-/

open Filter Polynomial Topology
open scoped ContDiff

noncomputable section

namespace RealRooted

/-- A uniform degree bound and coefficientwise continuity give continuity of
evaluation along a continuous parameter-dependent point. -/
theorem Polynomial.continuous_eval_of_continuous_coeff
    {T : Type*} [TopologicalSpace T]
    (p : T → ℝ[X]) {N : ℕ}
    (hdegree : ∀ t, (p t).natDegree ≤ N)
    (hcoeff : ∀ i : ℕ, Continuous fun t => (p t).coeff i)
    {x : T → ℝ} (hx : Continuous x) :
    Continuous fun t => (p t).eval (x t) := by
  rw [show (fun t => (p t).eval (x t)) =
      fun t => ∑ i ∈ Finset.range (N + 1),
        (p t).coeff i * x t ^ i by
    funext t
    exact Polynomial.eval_eq_sum_range'
      (Nat.lt_succ_of_le (hdegree t)) (x t)]
  exact continuous_finsetSum _ fun i _ =>
    (hcoeff i).mul (hx.pow i)

/-- The monic normalization of the derivative of a real polynomial. -/
def monicDerivative (p : ℝ[X]) : ℝ[X] :=
  C p.derivative.leadingCoeff⁻¹ * p.derivative

theorem monicDerivative_monic {p : ℝ[X]} (hp : p.natDegree ≠ 0) :
    (monicDerivative p).Monic := by
  apply Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
  exact inv_mul_cancel₀ <| leadingCoeff_ne_zero.mpr <|
    (Polynomial.derivative_ne_zero.mpr hp)

theorem natDegree_monicDerivative {p : ℝ[X]} (hp : p.natDegree ≠ 0) :
    (monicDerivative p).natDegree = p.natDegree - 1 := by
  rw [monicDerivative, Polynomial.natDegree_C_mul
    (inv_ne_zero (leadingCoeff_ne_zero.mpr
      (Polynomial.derivative_ne_zero.mpr hp))),
    p.natDegree_derivative]

theorem isRoot_monicDerivative_iff {p : ℝ[X]} (hp : p.natDegree ≠ 0)
    (x : ℝ) :
    (monicDerivative p).IsRoot x ↔ p.derivative.IsRoot x := by
  have hscale : p.derivative.leadingCoeff⁻¹ ≠ 0 :=
    inv_ne_zero <| leadingCoeff_ne_zero.mpr <|
      Polynomial.derivative_ne_zero.mpr hp
  rw [Polynomial.IsRoot.def, Polynomial.IsRoot.def, monicDerivative,
    Polynomial.eval_mul, Polynomial.eval_C, mul_eq_zero]
  simp only [hscale, false_or]

/-- Fixed degree and coefficientwise continuity are inherited by the monic
derivative normalization. -/
theorem continuous_coeff_monicDerivative
    {T : Type*} [TopologicalSpace T] (p : T → ℝ[X]) {D : ℕ}
    (hdegree : ∀ t, (p t).natDegree = D) (hD : D ≠ 0)
    (hcoeff : ∀ i : ℕ, Continuous fun t => (p t).coeff i)
    (i : ℕ) :
    Continuous fun t => (monicDerivative (p t)).coeff i := by
  have hlc : Continuous fun t => (p t).derivative.leadingCoeff := by
    rw [show (fun t => (p t).derivative.leadingCoeff) =
        fun t => (p t).coeff D * (D : ℝ) by
      funext t
      rw [Polynomial.leadingCoeff_derivative, Polynomial.leadingCoeff,
        hdegree t]]
    exact (hcoeff D).mul_const D
  have hlc0 : ∀ t, (p t).derivative.leadingCoeff ≠ 0 := by
    intro t
    exact leadingCoeff_ne_zero.mpr <|
      Polynomial.derivative_ne_zero.mpr (by simpa [hdegree t] using hD)
  simp only [monicDerivative, Polynomial.coeff_C_mul,
    Polynomial.coeff_derivative]
  exact (hlc.inv₀ hlc0).mul
    ((hcoeff (i + 1)).mul_const (i + 1))

/-- For a fixed-degree coefficientwise-continuous family, the locus where the
polynomial is PF and every critical value has squared magnitude at least `δ`
is closed. -/
theorem isClosed_isPFPolynomial_and_criticalValueMargin
    (p : ℝ → ℝ[X]) {D : ℕ} (hD : 2 ≤ D)
    (hdegree : ∀ t, (p t).natDegree = D)
    (hcoeff : ∀ i : ℕ, Continuous fun t => (p t).coeff i)
    (δ : ℝ) :
    IsClosed {t |
      IsPFPolynomial (p t) ∧
        ∀ x, (p t).derivative.IsRoot x → δ ≤ (p t).eval x ^ 2} := by
  let q : ℝ → ℝ[X] := fun t => monicDerivative (p t)
  have hD0 : D ≠ 0 := by lia
  have hqmonic : ∀ t, (q t).Monic := by
    intro t
    exact monicDerivative_monic (by simpa [hdegree t] using hD0)
  have hqdegree : ∀ t, (q t).natDegree = D - 1 := by
    intro t
    change (monicDerivative (p t)).natDegree = D - 1
    rw [natDegree_monicDerivative (by simpa [hdegree t] using hD0),
      hdegree t]
  have hqcoeff : ∀ i : ℕ, Continuous fun t => (q t).coeff i := by
    intro i
    exact continuous_coeff_monicDerivative p hdegree hD0 hcoeff i
  have heval : Continuous fun z : ℝ × ℝ => (p z.1).eval z.2 := by
    apply Polynomial.continuous_eval_of_continuous_coeff
      (fun z : ℝ × ℝ => p z.1) (N := D)
    · intro z
      exact (hdegree z.1).le
    · intro i
      exact (hcoeff i).comp continuous_fst
    · exact continuous_snd
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro t ht
  change ¬(IsPFPolynomial (p t) ∧
    ∀ x, (p t).derivative.IsRoot x → δ ≤ (p t).eval x ^ 2) at ht
  change {u | ¬(IsPFPolynomial (p u) ∧
    ∀ x, (p u).derivative.IsRoot x → δ ≤ (p u).eval x ^ 2)} ∈ 𝓝 t
  by_cases htpf : IsPFPolynomial (p t)
  · have hmargin : ¬∀ x,
        (p t).derivative.IsRoot x → δ ≤ (p t).eval x ^ 2 := by
      exact fun h => ht ⟨htpf, h⟩
    push Not at hmargin
    obtain ⟨x, hxroot, hxvalue⟩ := hmargin
    have hxvalue' : (p t).eval x ^ 2 < δ := hxvalue
    have hevent : ∀ᶠ z in 𝓝 (t, x), (p z.1).eval z.2 ^ 2 < δ :=
      (heval.pow 2).continuousAt.eventually_lt continuousAt_const hxvalue'
    rw [nhds_prod_eq] at hevent
    obtain ⟨A, hA, η, hη, hsmall⟩ :=
      Metric.eventually_prod_nhds_iff.mp hevent
    obtain ⟨ε, hε, hnear⟩ :=
      Polynomial.exists_coeff_radius_root_near (hqmonic t)
        (by rw [hqdegree t]; lia)
        ((isRoot_monicDerivative_iff
          (by simpa [hdegree t] using hD0) x).2 hxroot) hη
    have hclose := Polynomial.eventually_forall_norm_coeff_sub_lt
      q hqdegree hqcoeff t hε
    filter_upwards [hA, hclose] with u huA huclose
    intro hu
    rcases hu with ⟨hupf, humargin⟩
    have huderiv0 : (p u).derivative ≠ 0 :=
      Polynomial.derivative_ne_zero.mpr (by simpa [hdegree u] using hD0)
    have hqsplit : (q u).Splits := by
      exact ((hupf.derivative.ne_zero_and_splits huderiv0).2).C_mul _
    obtain ⟨y, hyroot, hxy⟩ := hnear (q u) (hqmonic u)
      ((hqdegree u).trans (hqdegree t).symm) huclose hqsplit
    have hycritical : (p u).derivative.IsRoot y := by
      exact (isRoot_monicDerivative_iff
        (by simpa [hdegree u] using hD0) y).1 hyroot
    have hyvalue : (p u).eval y ^ 2 < δ := by
      apply hsmall huA
      simpa [dist_eq_norm, norm_sub_rev] using hxy
    exact (not_lt_of_ge (humargin y hycritical)) hyvalue
  · have hopen : IsOpen {u | ¬IsPFPolynomial (p u)} :=
      (isClosed_isPFPolynomial p hcoeff).isOpen_compl
    apply Filter.mem_of_superset (hopen.mem_nhds htpf)
    intro u hupf hu
    exact hupf hu.1

/-- A positive lower bound on all squared critical values excludes repeated
roots. -/
theorem hasSimpleRoots_of_criticalValueMargin
    {p : ℝ[X]} (hp0 : p ≠ 0) {δ : ℝ} (hδ : 0 < δ)
    (hmargin : ∀ x, p.derivative.IsRoot x → δ ≤ p.eval x ^ 2) :
    HasSimpleRoots p := by
  intro x hx
  have hxderiv : ¬p.derivative.IsRoot x := by
    intro hxderiv
    have hbound := hmargin x hxderiv
    rw [Polynomial.IsRoot.def] at hx
    rw [hx] at hbound
    norm_num at hbound
    exact (not_lt_of_ge hbound) hδ
  have hpos : 0 < p.rootMultiplicity x :=
    (Polynomial.rootMultiplicity_pos hp0).2 hx
  have hle : p.rootMultiplicity x ≤ 1 := by
    by_contra h
    have htwo : 1 < p.rootMultiplicity x := by lia
    exact hxderiv ((Polynomial.one_lt_rootMultiplicity_iff_isRoot hp0).1 htwo).2
  lia

/-- The derivative of a positive-degree split polynomial with simple roots
also has simple roots. -/
theorem HasSimpleRoots.derivative_of_splits
    {p : ℝ[X]} (hsimple : HasSimpleRoots p) (hsplits : p.Splits)
    (hdegree : p.natDegree ≠ 0) :
    HasSimpleRoots p.derivative := by
  by_cases hone : p.natDegree = 1
  · apply hasSimpleRoots_of_natDegree_le_one
    · exact Polynomial.derivative_ne_zero.mpr hdegree
    · rw [p.natDegree_derivative, hone]
      norm_num
  · have htwo : 2 ≤ p.natDegree := by lia
    have hinterl : StrictInterl p.derivative p :=
      (derivative_interlaces hsplits htwo).toStrictInterl
    exact (hinterl.hasSimpleRoots_of_no_common_root fun _ hx =>
      hsimple.eval_derivative_ne_zero hx.2 hx.1).1

private theorem toSpanSingleton_isInvertible {c : ℝ} (hc : c ≠ 0) :
    (ContinuousLinearMap.toSpanSingleton ℝ c).IsInvertible := by
  let e : ℝ ≃L[ℝ] ℝ :=
    ContinuousLinearEquiv.smulLeft (Units.mk0 c hc)
  refine ⟨e, ?_⟩
  ext
  simp [e, ContinuousLinearMap.toSpanSingleton_apply, mul_comm]

/-- A regular real root of a jointly `C¹` polynomial family admits a local
`C¹` parameter branch. -/
theorem exists_contDiffAt_polynomial_root
    (p : ℝ → ℝ[X]) {t r : ℝ}
    (hF : ContDiffAt ℝ 1
      (fun z : ℝ × ℝ => (p z.1).eval z.2) (t, r))
    (hr : (p t).IsRoot r)
    (hregular : (p t).derivative.eval r ≠ 0) :
    ∃ ρ : ℝ → ℝ,
      ContDiffAt ℝ 1 ρ t ∧
        ρ t = r ∧
          ∀ᶠ s in 𝓝 t, (p s).IsRoot (ρ s) := by
  let F : ℝ × ℝ → ℝ := fun z => (p z.1).eval z.2
  let A : ℝ →L[ℝ] ℝ :=
    fderiv ℝ F (t, r) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ
  have hfull : HasFDerivAt F (fderiv ℝ F (t, r)) (t, r) :=
    (hF.differentiableAt (by simp)).hasFDerivAt
  have hA : A = ContinuousLinearMap.toSpanSingleton ℝ
      ((p t).derivative.eval r) := by
    apply HasFDerivAt.unique
    · exact hfull.comp r (hasFDerivAt_prodMk_right t r)
    · exact (p t).hasFDerivAt r
  have hAinv : A.IsInvertible := by
    rw [hA]
    exact toSpanSingleton_isInvertible hregular
  let ρ : ℝ → ℝ := hF.implicitFunction (by simp) hAinv
  have hρbase : ρ t = r :=
    hF.implicitFunction_apply_self (by simp) hAinv
  have hρroot : ∀ᶠ s in 𝓝 t, (p s).IsRoot (ρ s) := by
    have heq := hF.eventually_apply_implicitFunction (by simp) hAinv
    filter_upwards [heq] with s hs
    rw [Polynomial.IsRoot.def]
    change F (s, ρ s) = 0
    simpa only [F, Polynomial.IsRoot.def] using hs.trans (by simpa using hr)
  exact ⟨ρ, hF.contDiffAt_implicitFunction (by simp) hAinv,
    hρbase, hρroot⟩

end RealRooted
