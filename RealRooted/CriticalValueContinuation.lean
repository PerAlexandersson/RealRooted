import RealRooted.PFPolynomial.Closure
import RealRooted.RootCounting.Finite
import RealRooted.SimpleRoots
import RealRooted.Mathlib.Analysis.Normed.Field.Approximation
import Mathlib.Analysis.Calculus.Deriv.MeanValue
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

/-- A continuous polynomial family with a uniform degree bound retains its
maximal degree locally when the top coefficient is initially nonzero. -/
theorem Polynomial.eventually_natDegree_eq_of_le_of_continuous_coeff
    {T : Type*} [TopologicalSpace T] (p : T → ℝ[X]) {t : T} {D : ℕ}
    (hdegree : (p t).natDegree = D) (hp0 : p t ≠ 0)
    (hle : ∀ u, (p u).natDegree ≤ D)
    (hcoeff : ∀ i : ℕ, Continuous fun u => (p u).coeff i) :
    ∀ᶠ u in 𝓝 t, (p u).natDegree = D := by
  have htop : (p t).coeff D ≠ 0 := by
    rw [← hdegree]
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp0
  filter_upwards [(hcoeff D).continuousAt.eventually_ne htop] with u hu
  apply le_antisymm (hle u)
  exact Polynomial.le_natDegree_of_ne_zero hu

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

/-- A positive-degree polynomial with simple roots has a uniform positive
lower bound on the squares of all its critical values. -/
theorem HasSimpleRoots.exists_pos_criticalValueMargin
    {p : ℝ[X]} (hsimple : HasSimpleRoots p) (hdegree : p.natDegree ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ x, p.derivative.IsRoot x → δ ≤ p.eval x ^ 2 := by
  classical
  have hderivative : p.derivative ≠ 0 :=
    Polynomial.derivative_ne_zero.mpr hdegree
  let S := p.derivative.roots.toFinset
  have hpositive : ∀ x ∈ S, 0 < p.eval x ^ 2 := by
    intro x hx
    have hxcritical : p.derivative.IsRoot x := by
      apply (Polynomial.mem_roots hderivative).mp
      exact Multiset.mem_toFinset.mp hx
    apply sq_pos_of_ne_zero
    intro hxzero
    exact hsimple.eval_derivative_ne_zero
      (by simpa [Polynomial.IsRoot.def] using hxzero) <| by
        simpa [Polynomial.IsRoot.def] using hxcritical
  have hfinite : ∀ T : Finset ℝ,
      (∀ x ∈ T, 0 < p.eval x ^ 2) →
        ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ T, δ ≤ p.eval x ^ 2 := by
    intro T hT
    induction T using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert a T ha ih =>
        obtain ⟨δ, hδ, hbound⟩ := ih fun x hx ↦ hT x (by simp [hx])
        refine ⟨min δ (p.eval a ^ 2), lt_min hδ (hT a (by simp)), ?_⟩
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact min_le_right _ _
        · exact (min_le_left _ _).trans (hbound x hx)
  obtain ⟨δ, hδ, hbound⟩ := hfinite S hpositive
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  apply hbound x
  apply Multiset.mem_toFinset.mpr
  exact (Polynomial.mem_roots hderivative).mpr hx

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

/-- The simple roots of a smooth fixed-degree split polynomial admit local
smooth branches that exhaust all nearby roots. -/
theorem exists_eventually_polynomial_root_branches
    (p : ℝ → ℝ[X]) {t : ℝ} {D : ℕ} (hD : D ≠ 0)
    (hdegree : ∀ᶠ u in 𝓝 t, (p u).natDegree = D)
    (hsplits : (p t).Splits) (hsimple : HasSimpleRoots (p t))
    (hsmooth : ∀ x, (p t).IsRoot x →
      ContDiffAt ℝ 1 (fun z : ℝ × ℝ => (p z.1).eval z.2) (t, x)) :
    ∃ ξ : {x // x ∈ (p t).roots.toFinset} → ℝ → ℝ,
      (∀ i, ξ i t = i) ∧
        ∀ᶠ u in 𝓝 t,
          (p u).Splits ∧ HasSimpleRoots (p u) ∧
            (∀ i, ContDiffAt ℝ 1 (ξ i) u) ∧
              ∀ x, (p u).IsRoot x ↔ ∃ i, ξ i u = x := by
  classical
  let I := (p t).roots.toFinset
  have hdegree_t : (p t).natDegree = D := hdegree.self_of_nhds
  have hroot (i : ↥I) : (p t).IsRoot i := by
    apply (Polynomial.mem_roots hsimple.ne_zero).mp
    apply Multiset.mem_toFinset.mp
    simpa only [I] using i.2
  let ξ (i : ↥I) : ℝ → ℝ :=
    (exists_contDiffAt_polynomial_root p (hsmooth i (hroot i))
      (hroot i) (hsimple.eval_derivative_ne_zero (hroot i))).choose
  have hξsmooth (i : ↥I) : ContDiffAt ℝ 1 (ξ i) t :=
    (exists_contDiffAt_polynomial_root p (hsmooth i (hroot i))
      (hroot i) (hsimple.eval_derivative_ne_zero (hroot i))).choose_spec.1
  have hξbase (i : ↥I) : ξ i t = i :=
    (exists_contDiffAt_polynomial_root p (hsmooth i (hroot i))
      (hroot i) (hsimple.eval_derivative_ne_zero (hroot i))).choose_spec.2.1
  have hξroot (i : ↥I) :
      ∀ᶠ u in 𝓝 t, (p u).IsRoot (ξ i u) :=
    (exists_contDiffAt_polynomial_root p (hsmooth i (hroot i))
      (hroot i) (hsimple.eval_derivative_ne_zero (hroot i))).choose_spec.2.2
  refine ⟨ξ, hξbase, ?_⟩
  have hroots : ∀ᶠ u in 𝓝 t, ∀ i : ↥I,
      (p u).IsRoot (ξ i u) :=
    Filter.eventually_all.mpr hξroot
  have hsmooths : ∀ᶠ u in 𝓝 t, ∀ i : ↥I,
      ContDiffAt ℝ 1 (ξ i) u :=
    Filter.eventually_all.mpr fun i =>
      (hξsmooth i).eventually (by norm_num)
  have hdistinct : ∀ᶠ u in 𝓝 t, ∀ i j : ↥I,
      i ≠ j → ξ i u ≠ ξ j u := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    by_cases hij : i = j
    · subst j
      simp
    · have hne : ξ i t - ξ j t ≠ 0 := by
        rw [hξbase i, hξbase j, sub_ne_zero]
        exact fun h => hij (Subtype.ext h)
      filter_upwards [((hξsmooth i).continuousAt.sub
        (hξsmooth j).continuousAt).eventually_ne hne]
        with u hu
      intro _
      exact sub_ne_zero.mp hu
  have hIcard : I.card = D := by
    dsimp [I]
    rw [Multiset.toFinset_card_of_nodup hsimple.roots_nodup,
      ← hsplits.natDegree_eq_card_roots, hdegree_t]
  filter_upwards [hdegree, hroots, hsmooths, hdistinct]
    with u hudegree huroots husmooth hudistinct
  let s : Finset ℝ := Finset.univ.image fun i : ↥I => ξ i u
  have hξinj : Function.Injective fun i : ↥I => ξ i u := by
    intro i j hij
    by_contra hne
    exact hudistinct i j hne hij
  have hscard : s.card = D := by
    change (Finset.univ.image fun i : ↥I => ξ i u).card = D
    rw [Finset.card_image_of_injective _ hξinj, Finset.card_univ,
      Fintype.card_coe, hIcard]
  have hsroot : ∀ x ∈ s, (p u).IsRoot x := by
    intro x hx
    change x ∈ Finset.univ.image (fun i : ↥I => ξ i u) at hx
    rw [Finset.mem_image] at hx
    obtain ⟨i, _, rfl⟩ := hx
    exact huroots i
  have husplits : (p u).Splits :=
    Polynomial.splits_of_finset_roots_of_natDegree_le_card hsroot <| by
      rw [hudegree, hscard]
  have hu0 : p u ≠ 0 := by
    intro hu
    have : D = 0 := by simpa [hu] using hudegree.symm
    exact hD this
  have hunodup : (p u).roots.Nodup := by
    apply RootCounting.roots_nodup_of_card_roots
      husplits.natDegree_eq_card_roots.symm hsroot hu0
    rw [hudegree, hscard]
  have hssub : s ⊆ (p u).roots.toFinset := by
    intro x hx
    apply Multiset.mem_toFinset.mpr
    exact (Polynomial.mem_roots hu0).mpr (hsroot x hx)
  have hseq : s = (p u).roots.toFinset := by
    apply Finset.eq_of_subset_of_card_le hssub
    calc
      (p u).roots.toFinset.card ≤ (p u).roots.card :=
        Multiset.toFinset_card_le _
      _ = (p u).natDegree := husplits.natDegree_eq_card_roots.symm
      _ = D := hudegree
      _ = s.card := hscard.symm
  refine ⟨husplits, HasSimpleRoots.of_roots_nodup hu0 hunodup,
    husmooth, ?_⟩
  intro x
  constructor
  · intro hx
    have hxmem : x ∈ s := by
      rw [hseq]
      exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hu0).mpr hx)
    change x ∈ Finset.univ.image (fun i : ↥I => ξ i u) at hxmem
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hxmem
    exact ⟨i, hi⟩
  · rintro ⟨i, rfl⟩
    exact huroots i

/-- Simple roots in a smooth fixed-degree split family persist locally with
their (unit) multiplicity.

This packages `exists_eventually_polynomial_root_branches` in the per-root
lower-count form used by root-count local-constancy arguments. Unlike the
older affine-pencil continuity theorem, the polynomial family `p` is
arbitrary.
-/
theorem exists_eventually_forall_root_count_le_card_filter_near_of_simple
    (p : ℝ → ℝ[X]) {t : ℝ} {D : ℕ} (hD : D ≠ 0)
    (hdegree : ∀ᶠ u in 𝓝 t, (p u).natDegree = D)
    (hsplits : (p t).Splits) (hsimple : HasSimpleRoots (p t))
    (hsmooth : ∀ x, (p t).IsRoot x →
      ContDiffAt ℝ 1 (fun z : ℝ × ℝ => (p z.1).eval z.2) (t, x))
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᶠ u in 𝓝 t, ∀ a ∈ (p t).roots.toFinset,
      (p t).roots.count a ≤
        ((p u).roots.filter (fun q => |q - a| < ρ)).card := by
  classical
  obtain ⟨ξ, hξbase, hbranches⟩ :=
    exists_eventually_polynomial_root_branches p hD hdegree hsplits
      hsimple hsmooth
  have hbranches_t := hbranches.self_of_nhds
  have hnear : ∀ᶠ u in 𝓝 t,
      ∀ i : {x // x ∈ (p t).roots.toFinset}, |ξ i u - i| < ρ := by
    rw [Filter.eventually_all]
    intro i
    have hcontinuous : ContinuousAt (ξ i) t :=
      (hbranches_t.2.2.1 i).continuousAt
    simpa [Real.dist_eq, hξbase i] using
      (Metric.tendsto_nhds.mp hcontinuous.tendsto ρ hρ)
  filter_upwards [hbranches, hnear] with u hu hnear_u
  intro a ha
  let i : {x // x ∈ (p t).roots.toFinset} := ⟨a, ha⟩
  have ha_root : (p t).IsRoot a :=
    Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp ha)
  have hcount : (p t).roots.count a = 1 :=
    hsimple.roots_count_eq_one ha_root
  have hbranch_root : (p u).IsRoot (ξ i u) :=
    (hu.2.2.2 (ξ i u)).2 ⟨i, rfl⟩
  have hbranch_mem : ξ i u ∈ (p u).roots :=
    (Polynomial.mem_roots hu.2.1.ne_zero).2 hbranch_root
  rw [hcount]
  apply Multiset.card_pos.mpr
  intro hzero
  have hmem : ξ i u ∈
      (p u).roots.filter (fun q => |q - a| < ρ) :=
    Multiset.mem_filter.mpr ⟨hbranch_mem, hnear_u i⟩
  simp [hzero] at hmem

/-- Metric-neighborhood form of
`exists_eventually_forall_root_count_le_card_filter_near_of_simple`. -/
theorem exists_eps_forall_root_count_le_card_filter_near_of_simple
    (p : ℝ → ℝ[X]) {t : ℝ} {D : ℕ} (hD : D ≠ 0)
    (hdegree : ∀ᶠ u in 𝓝 t, (p u).natDegree = D)
    (hsplits : (p t).Splits) (hsimple : HasSimpleRoots (p t))
    (hsmooth : ∀ x, (p t).IsRoot x →
      ContDiffAt ℝ 1 (fun z : ℝ × ℝ => (p z.1).eval z.2) (t, x))
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ ε > 0, ∀ u : ℝ, |u - t| < ε →
      ∀ a ∈ (p t).roots.toFinset,
        (p t).roots.count a ≤
          ((p u).roots.filter (fun q => |q - a| < ρ)).card := by
  have hlocal :=
    exists_eventually_forall_root_count_le_card_filter_near_of_simple
      p hD hdegree hsplits hsimple hsmooth hρ
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hlocal
  refine ⟨ε, hε, fun u hu ↦ hball ?_⟩
  simpa [Metric.mem_ball, Real.dist_eq] using hu

/-- If finitely many critical-point branches exhaust all nearby critical
points and their squared critical values have nonnegative derivatives, then a
critical-value margin persists to the right. -/
theorem criticalValueMargin_eventually_right_of_branches
    {ι : Type*} (p : ℝ → ℝ[X]) (ξ : ι → ℝ → ℝ) {t δ : ℝ}
    (hbase : ∀ i, δ ≤ (p t).eval (ξ i t) ^ 2)
    (hlocal : ∀ᶠ s in 𝓝 t,
      (∀ x, (p s).derivative.IsRoot x → ∃ i, ξ i s = x) ∧
        ∀ i, ∃ v,
          HasDerivAt (fun u => (p u).eval (ξ i u) ^ 2) v s ∧ 0 ≤ v) :
    ∀ᶠ s in 𝓝[>] t,
      ∀ x, (p s).derivative.IsRoot x → δ ≤ (p s).eval x ^ 2 := by
  obtain ⟨l, r, ht, hgood⟩ := hlocal.exists_Ioo_subset
  have hmono (i : ι) :
      MonotoneOn (fun u => (p u).eval (ξ i u) ^ 2) (Set.Ioo l r) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioo l r)
    · intro s hs
      exact ((hgood hs).2 i).choose_spec.1.continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Ioo] at hs
      exact ((hgood hs).2 i).choose_spec.1.differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Ioo] at hs
      obtain ⟨v, hv, hvnonneg⟩ := (hgood hs).2 i
      rw [hv.deriv]
      exact hvnonneg
  apply mem_nhdsGT_iff_exists_Ioo_subset.mpr
  refine ⟨r, ht.2, ?_⟩
  intro s hs x hx
  have hs' : s ∈ Set.Ioo l r := ⟨ht.1.trans hs.1, hs.2⟩
  obtain ⟨i, hi⟩ := (hgood hs').1 x hx
  rw [← hi]
  exact (hbase i).trans (hmono i ht hs' hs.1.le)

end RealRooted
