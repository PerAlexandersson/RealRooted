module

public import RealRooted.OperatorPreservesInterlacing
public import RealRooted.BorceaBranden.Transcendental.RealOperatorBasics
import RealRooted.BorceaBranden.Transcendental.RealClassification
public import RealRooted.HermiteBiehler.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Complex.Polynomial.Basic
import RealRooted.Mathlib.Analysis.Complex.Hurwitz
import RealRooted.Mathlib.Analysis.Complex.LimitsOfZeros
import RealRooted.MultivariateStability.Specialization
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Classical hyperbolicity of finite-difference operators

We formalize Lemma 8 in Brändén, Krasikov, and Shapiro,
*Elements of Pólya--Schur theory in the finite difference setting*, Proc. AMS 144 (2016).

In `PolyFiniteDifferenceOp.support_subsingleton_of_preserves` we prove the hard direction
unconditionally, using the two-dominant-term limit-of-zeros theorem on the images of `X ^ m`.
The full criterion is `PolyFiniteDifferenceOp.preserves_iff`: at most one coefficient is
nonzero, and every surviving coefficient splits over the reals.

We also provide the univariate real Borcea--Brändén bridge, real boundary slices of stable
limits, and the exponential-polynomial zero argument suggested by the paper's proof.
The earlier conditional criteria and the pointwise-to-global support lemma are retained.
-/

public section

open Polynomial

noncomputable section

namespace RealRooted

/-- The finite-difference operator with polynomial coefficients
`p(x) ↦ ∑ j, q j (x) p(x - j)` from BKS (2016), equation (1) and Lemma 8.  Compare
`finiteDifferenceOp`, the constant-coefficient operator with an arbitrary step. -/
@[expose]
def polyFiniteDifferenceOp {n : ℕ} (q : Fin n → ℝ[X]) : ℝ[X] →ₗ[ℝ] ℝ[X] where
  toFun p := ∑ j, q j * p.comp (X - C (j : ℝ))
  map_add' p r := by
    simp [add_comp, mul_add, Finset.sum_add_distrib]
  map_smul' a p := by
    simp only [Polynomial.smul_eq_C_mul, mul_comp, C_comp]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [RingHom.id_apply]
    ring

namespace PolyFiniteDifferenceOp

@[simp]
theorem apply {n : ℕ} (q : Fin n → ℝ[X]) (p : ℝ[X]) :
    polyFiniteDifferenceOp q p = ∑ j, q j * p.comp (X - C (j : ℝ)) :=
  rfl

/-- If only coefficient `i` can be nonzero, the finite-difference sum is its `i`th term. -/
theorem eq_single {n : ℕ} (q : Fin n → ℝ[X]) (i : Fin n)
    (h : ∀ j, j ≠ i → q j = 0) (p : ℝ[X]) :
    polyFiniteDifferenceOp q p = q i * p.comp (X - C (i : ℝ)) := by
  classical
  rw [apply, Finset.sum_eq_single i]
  · intro j _ hji
    simp [h j hji]
  · simp

/-- The image of `1` recovers the unique nonzero coefficient. -/
theorem one_eq {n : ℕ} {q : Fin n → ℝ[X]} {i : Fin n}
    (hi : q i ≠ 0) (hsupport : Set.Subsingleton {j | q j ≠ 0}) :
    polyFiniteDifferenceOp q 1 = q i := by
  rw [eq_single q i (fun j hji ↦ by
    by_contra hj
    exact hji (hsupport hj hi))]
  simp

/-- The easy direction of BKS (2016), Lemma 8: a single polynomial coefficient times a
translation preserves real-rootedness when that coefficient is real-rooted. -/
theorem preserves_of_support_subsingleton
    {n : ℕ} {q : Fin n → ℝ[X]} (hsupport : Set.Subsingleton {j | q j ≠ 0})
    (hsplits : ∀ j, q j ≠ 0 → (q j).Splits) :
    PreservesRealRootedOrZero (polyFiniteDifferenceOp q) := by
  intro p hp
  classical
  by_cases hq : ∃ i, q i ≠ 0
  · obtain ⟨i, hi⟩ := hq
    right
    rw [eq_single q i (fun j hji ↦ by
      by_contra hj
      exact hji (hsupport hj hi))]
    exact (hsplits i hi).mul (hp.2.comp_X_sub_C (i : ℝ))
  · left
    simp only [apply]
    apply Finset.sum_eq_zero
    intro i _
    have hi : q i = 0 := not_ne_iff.mp (not_exists.mp hq i)
    simp [hi]

/-- The polynomial-identity step in the converse of BKS (2016), Lemma 8: if at each real
point at most one coefficient is nonzero, then at most one coefficient polynomial is nonzero. -/
theorem support_subsingleton_of_eval {n : ℕ} {q : Fin n → ℝ[X]}
    (hpoint : ∀ x : ℝ, Set.Subsingleton {j | (q j).eval x ≠ 0}) :
    Set.Subsingleton {j | q j ≠ 0} := by
  intro i hi j hj
  by_contra hij
  have hprod : q i * q j = 0 := by
    apply Polynomial.funext
    intro x
    rw [eval_mul, eval_zero]
    by_contra hne
    have hiEval : (q i).eval x ≠ 0 := fun h ↦ hne (by simp [h])
    have hjEval : (q j).eval x ≠ 0 := fun h ↦ hne (by simp [h])
    exact hij (hpoint x hiEval hjEval)
  exact (mul_ne_zero hi hj) hprod

/-- With globally subsingleton coefficient support, the finite-difference operator preserves
real-rootedness exactly when its unique possible nonzero coefficient is real-rooted. -/
theorem preserves_iff_of_support_subsingleton
    {n : ℕ} {q : Fin n → ℝ[X]} (hsupport : Set.Subsingleton {j | q j ≠ 0}) :
    PreservesRealRootedOrZero (polyFiniteDifferenceOp q) ↔
      ∀ j, q j ≠ 0 → (q j).Splits := by
  constructor
  · intro hpres j hj
    have hone := hpres 1 ⟨one_ne_zero, Splits.one⟩
    rw [one_eq hj hsupport] at hone
    exact hone.resolve_left hj
  · exact preserves_of_support_subsingleton hsupport

/-- BKS (2016), Lemma 8 after the analytic pointwise-support step: preservation is equivalent
to having at most one nonzero coefficient, which must itself be real-rooted. -/
theorem preserves_iff_of_eval
    {n : ℕ} {q : Fin n → ℝ[X]}
    (hpoint : ∀ x : ℝ, Set.Subsingleton {j | (q j).eval x ≠ 0}) :
    PreservesRealRootedOrZero (polyFiniteDifferenceOp q) ↔
      Set.Subsingleton {j | q j ≠ 0} ∧ ∀ j, q j ≠ 0 → (q j).Splits := by
  have hsupport := support_subsingleton_of_eval hpoint
  constructor
  · intro hpres
    exact ⟨hsupport, (preserves_iff_of_support_subsingleton hsupport).1 hpres⟩
  · rintro ⟨_, hsplits⟩
    exact preserves_of_support_subsingleton hsupport hsplits

/-- A family supported at one shift satisfies the BKS criterion. -/
theorem preserves_single
    {n : ℕ} (i : Fin n) {q : ℝ[X]} (hq : q.Splits) :
    PreservesRealRootedOrZero
      (polyFiniteDifferenceOp fun j ↦ if j = i then q else 0) := by
  apply preserves_of_support_subsingleton
  · intro j hj k hk
    have hji : j = i := by
      by_contra h
      simp [h] at hj
    have hki : k = i := by
      by_contra h
      simp [h] at hk
    exact hji.trans hki.symm
  · intro j hj
    by_cases hji : j = i
    · simpa [hji] using hq
    · simp [hji] at hj

/-- A concrete quadratic example: multiplication by `(x - 2)(x + 3)` after shifting by one
preserves real-rootedness. -/
theorem preserves_example :
    PreservesRealRootedOrZero
      (polyFiniteDifferenceOp (n := 3) fun j ↦
        if j = 1 then (X - C 2) * (X + C 3) else 0) := by
  exact preserves_single 1
    ((Splits.X_sub_C 2).mul (Splits.X_add_C 3))

end PolyFiniteDifferenceOp

namespace BorceaBranden

/-- Transport a univariate operator to a singleton variable set for the real
Borcea--Brändén classification used in BKS (2016), Lemma 8. -/
@[expose]
def univariateOperator (T : ℝ[X] →ₗ[ℝ] ℝ[X]) :
    MvPolynomial (Fin 1) ℝ →ₗ[ℝ] MvPolynomial (Fin 1) ℝ where
  toFun p := (MvPolynomial.uniqueAlgEquiv ℝ (Fin 1)).symm
    (T (MvPolynomial.uniqueAlgEquiv ℝ (Fin 1) p))
  map_add' p q := by simp
  map_smul' r p := by simp

private theorem eval_complexify_singleton (p : ℝ[X]) (z : Fin 1 → ℂ) :
    MvPolynomial.eval z
      (complexifyMv ((MvPolynomial.uniqueAlgEquiv ℝ (Fin 1)).symm p)) =
      (complexify p).eval (z 0) := by
  simp only [complexifyMv, complexify, MvPolynomial.eval_map, Polynomial.eval_map]
  exact MvPolynomial.eval₂_uniqueAlgEquiv_symm

/-- Real stability in one variable is precisely nonzero real-rootedness;
this identifies the conventions in BKS Lemma 8 and the real classification. -/
theorem mvRealStable_singleton_iff (p : ℝ[X]) :
    MvRealStable ((MvPolynomial.uniqueAlgEquiv ℝ (Fin 1)).symm p) ↔
      p ≠ 0 ∧ p.Splits := by
  constructor
  · intro h
    refine ⟨fun hp => h.ne_zero (by simp [hp]), ?_⟩
    apply IsUpperHalfPlaneStable.splits_complexify
    intro z hz
    have hh := h (fun _ => z) (fun _ => hz)
    rwa [eval_complexify_singleton] at hh
  · rintro ⟨hp, hs⟩ z hz
    rw [eval_complexify_singleton]
    exact eval_complexify_ne_zero_of_splits_of_im_pos hs hp (hz 0)

/-- Global univariate real-rootedness preservation transports to real stability
preservation on one multivariate variable, as needed in BKS (2016), Lemma 8. -/
theorem preservesRealStability_univariateOperator_iff (T : ℝ[X] →ₗ[ℝ] ℝ[X]) :
    PreservesRealStability (univariateOperator T) ↔ PreservesRealRootedOrZero T := by
  constructor
  · intro h p hp
    have hh := h ((MvPolynomial.uniqueAlgEquiv ℝ (Fin 1)).symm p)
      ((mvRealStable_singleton_iff p).2 hp)
    change MvRealStableOrZero ((MvPolynomial.uniqueAlgEquiv ℝ (Fin 1)).symm
      (T ((MvPolynomial.uniqueAlgEquiv ℝ (Fin 1))
        ((MvPolynomial.uniqueAlgEquiv ℝ (Fin 1)).symm p)))) at hh
    rw [AlgEquiv.apply_symm_apply] at hh
    rcases hh with hh | hh
    · left
      exact (MvPolynomial.uniqueAlgEquiv ℝ (Fin 1)).symm.injective
        (hh.trans (map_zero _).symm)
    · exact Or.inr ((mvRealStable_singleton_iff _).1 hh).2
  · intro h p hp
    let r := MvPolynomial.uniqueAlgEquiv ℝ (Fin 1) p
    have hr : r ≠ 0 ∧ r.Splits := (mvRealStable_singleton_iff r).1
      (by simpa only [r, AlgEquiv.symm_apply_apply] using hp)
    rcases h r hr with hz | hs
    · left
      change (MvPolynomial.uniqueAlgEquiv ℝ (Fin 1)).symm (T r) = 0
      simp [hz]
    · by_cases hz : T r = 0
      · left
        change (MvPolynomial.uniqueAlgEquiv ℝ (Fin 1)).symm (T r) = 0
        simp [hz]
      · exact Or.inr ((mvRealStable_singleton_iff (T r)).2 ⟨hz, hs⟩)

/-- Univariate real Borcea--Brändén classification, expressed using the library's
multivariate symbol family on a singleton type.  This is the classification invoked
in the proof of BKS (2016), Lemma 8. -/
theorem preserves_iff_rankTwo_or_signedSymbol (T : ℝ[X] →ₗ[ℝ] ℝ[X]) :
    PreservesRealRootedOrZero T ↔
      HasGlobalStableRankTwoRepresentation (univariateOperator T) ∨
        IsRealStableLimit (realTranscendentalSymbolPolynomial (univariateOperator T)) ∨
        IsRealStableLimit
          (negRightFamily (realTranscendentalSymbolPolynomial (univariateOperator T))) := by
  rw [← preservesRealStability_univariateOperator_iff]
  exact preservesRealStability_iff_rankTwo_or_signedTranscendentalSymbol_stableLimit _

end BorceaBranden

namespace PolyFiniteDifferenceOp

private theorem eq_monomial_of_roots_eq_zero (p : ℂ[X])
    (h : ∀ z : ℂ, p.eval z = 0 → z = 0) :
    p = monomial p.roots.card p.leadingCoeff := by
  have hm : p.roots.map (fun z => X - C z) =
      p.roots.map (fun _ => (X : ℂ[X])) := by
    apply Multiset.map_congr rfl
    intro z hz
    rw [h z ((mem_roots (ne_zero_of_mem_roots hz)).1 hz)]
    simp
  calc
    p = C p.leadingCoeff * (p.roots.map (fun z => X - C z)).prod :=
      (IsAlgClosed.splits p).eq_prod_roots
    _ = monomial p.roots.card p.leadingCoeff := by
      rw [hm]
      simp [C_mul_X_pow_eq_monomial]

/-- The exponential obstruction in BKS (2016), Lemma 8: a polynomial with two
nonzero coefficients gives a non-real zero after substitution of the exponential. -/
theorem exists_nonreal_zero_eval_exp {p : ℂ[X]}
    (hp : ¬Set.Subsingleton {j : ℕ | p.coeff j ≠ 0}) :
    ∃ y : ℂ, y.im ≠ 0 ∧ p.eval (Complex.exp y) = 0 := by
  have hz : ∃ z : ℂ, p.eval z = 0 ∧ z ≠ 0 := by
    by_contra h
    have hroot : ∀ z : ℂ, p.eval z = 0 → z = 0 := by
      intro z hz
      by_contra hne
      exact h ⟨z, hz, hne⟩
    apply hp
    rw [eq_monomial_of_roots_eq_zero p hroot]
    intro i hi j hj
    have hi' : p.roots.card = i := by
      by_contra hne
      simp [coeff_monomial, hne] at hi
    have hj' : p.roots.card = j := by
      by_contra hne
      simp [coeff_monomial, hne] at hj
    exact hi'.symm.trans hj'
  obtain ⟨z, hz, hne⟩ := hz
  refine ⟨Complex.log z + 2 * Real.pi * Complex.I, ?_, ?_⟩
  · have hbound := Complex.neg_pi_lt_log_im z
    have hpi := Real.pi_pos
    norm_num [Complex.add_im, Complex.mul_im, Complex.mul_re]
    linarith
  · rw [Complex.exp_periodic, Complex.exp_log hne, hz]

/-- If all zeros of a polynomial composed with the exponential are real, its
coefficient support is subsingleton.  This is the exponential step of BKS Lemma 8. -/
theorem coeff_support_subsingleton_of_eval_exp {p : ℂ[X]}
    (h : ∀ y : ℂ, p.eval (Complex.exp y) = 0 → y.im = 0) :
    Set.Subsingleton {j : ℕ | p.coeff j ≠ 0} := by
  by_contra hp
  obtain ⟨y, hy, hz⟩ := exists_nonreal_zero_eval_exp hp
  exact hy (h y hz)

private theorem exists_eval_exp_ne_zero {p : ℂ[X]} (hp : p ≠ 0) :
    ∃ y : ℂ, p.eval (Complex.exp y) ≠ 0 := by
  by_contra h
  apply hp
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply Set.Infinite.mono _ (Set.finite_singleton (0 : ℂ)).infinite_compl
  intro z hz
  have hne : z ≠ 0 := hz
  have hy : p.eval (Complex.exp (Complex.log z)) = 0 :=
    not_ne_iff.mp (not_exists.mp h (Complex.log z))
  change p.eval z = 0
  simpa only [Complex.exp_log hne] using hy

open Filter Topology

private theorem eval_ne_zero_of_splits_im_ne {p : ℝ[X]} (hp : p.Splits) (hp0 : p ≠ 0)
    {z : ℂ} (hz : z.im ≠ 0) : (complexify p).eval z ≠ 0 := by
  rw [eval_complexify_eq_prod hp]
  refine mul_ne_zero (by simp [hp0]) ?_
  apply Multiset.prod_ne_zero
  simp only [Multiset.mem_map, not_exists, not_and]
  rintro r _ heq
  exact hz (by simpa using congrArg Complex.im heq)

/-- Hurwitz step in BKS (2016), Lemma 8: a nonzero entire locally uniform limit
of real-rooted polynomials has only real zeros. Zero approximants are allowed. -/
theorem im_eq_zero_of_split_limit {p : ℕ → ℝ[X]} {g : ℂ → ℂ}
    (hp : ∀ k, (p k).Splits)
    (hconv : TendstoLocallyUniformly (fun k z => (complexify (p k)).eval z) g atTop)
    (hg : Differentiable ℂ g) (hne : ∃ a, g a ≠ 0) {z : ℂ} (hz : g z = 0) :
    z.im = 0 := by
  obtain ⟨a, ha⟩ := hne
  have hev := (hconv.tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ a)).eventually_ne ha
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have hp0 : ∀ k, p (k + N) ≠ 0 := by
    intro k hk
    have hh := hN (k + N) (Nat.le_add_left N k)
    simp [hk] at hh
  have hconv' : TendstoLocallyUniformly
      (fun k w => (complexify (p (k + N))).eval w) g atTop := by
    intro u hu w
    obtain ⟨t, ht, he⟩ := hconv u hu w
    exact ⟨t, ht, (tendsto_add_atTop_nat N) he⟩
  by_contra him
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1
    (isOpen_ne_fun Complex.continuous_im continuous_const) z him
  have hzero : ∀ w ∈ Metric.ball z r, g w = 0 := by
    rcases Complex.forall_ne_or_forall_eq_of_tendstoLocallyUniformlyOn_ball
      (fun k => (Polynomial.differentiable (complexify (p (k + N)))).differentiableOn)
      hconv'.tendstoLocallyUniformlyOn
      (fun k w hw => eval_ne_zero_of_splits_im_ne (hp _) (hp0 k) (hball hw)) with hh | hh
    · exact (hh z (Metric.mem_ball_self hr) hz).elim
    · exact hh
  have hlocal : g =ᶠ[𝓝 z] 0 := by
    filter_upwards [Metric.ball_mem_nhds z hr] with w hw
    exact hzero w hw
  have han := hg.differentiableOn.analyticOnNhd isOpen_univ
  exact ha (han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ z) hlocal (Set.mem_univ a))

end PolyFiniteDifferenceOp

namespace BorceaBranden

private def slicePolynomial (P : MvPolynomial (Fin 1 ⊕ Fin 1) ℝ) (x : ℝ) : ℝ[X] :=
  MvPolynomial.eval₂ C (Sum.elim (fun _ => C x) (fun _ => X)) P

private theorem eval_slicePolynomial (P : MvPolynomial (Fin 1 ⊕ Fin 1) ℝ)
    (x : ℝ) (y : ℂ) :
    (complexify (slicePolynomial P x)).eval y =
      MvPolynomial.eval (Sum.elim (fun _ => (x : ℂ)) (fun _ => y)) (complexifyMv P) := by
  simp only [complexify, complexifyMv, Polynomial.eval_map, MvPolynomial.eval_map]
  induction P using MvPolynomial.induction_on with
  | C r => simp [slicePolynomial]
  | add P Q hP hQ => simpa [slicePolynomial] using congrArg₂ (· + ·) hP hQ
  | mul_X P i hP =>
    cases i with
    | inl i => simpa [slicePolynomial] using congrArg (· * (x : ℂ)) hP
    | inr i => simpa [slicePolynomial] using congrArg (· * y) hP

private theorem slicePolynomial_splits {P : MvPolynomial (Fin 1 ⊕ Fin 1) ℝ}
    (hP : MvRealStable P) (x : ℝ) : (slicePolynomial P x).Splits := by
  let Q := MvPolynomial.specializeAt (Sum.inl (0 : Fin 1)) x P
  have hQ := hP.specializeAt_zero_or_general (Sum.inl (0 : Fin 1)) x
  have heval (y : ℂ) : MvPolynomial.eval (fun _ => y) (complexifyMv Q) =
      (complexify (slicePolynomial P x)).eval y := by
    rw [eval_slicePolynomial]
    simp only [Q, complexifyMv_specializeAt, MvPolynomial.eval_specializeAt]
    apply congrArg (fun z => MvPolynomial.eval z (complexifyMv P))
    funext i
    rcases i with i | i
    · have hi : i = 0 := Subsingleton.elim _ _
      simp [hi]
    · simp
  rcases hQ with hz | hs
  · have hzero : complexify (slicePolynomial P x) = 0 := by
      apply Polynomial.funext
      intro y
      rw [← heval]
      change MvPolynomial.eval (fun _ => y)
        (complexifyMv (MvPolynomial.specializeAt (Sum.inl (0 : Fin 1)) x P)) = _
      simp [hz, complexifyMv]
    have hpzero : slicePolynomial P x = 0 := by
      exact Polynomial.map_injective Complex.ofRealHom Complex.ofRealHom.injective
        (hzero.trans (Polynomial.map_zero _).symm)
    simp [hpzero]
  · apply IsUpperHalfPlaneStable.splits_complexify
    intro y hy
    rw [← heval]
    exact hs (fun _ => y) (fun _ => hy)

/-- The real-boundary slice of the entire series in a real stable-limit family.
This is the slice used in BKS (2016), Lemma 8. -/
@[expose]
def realSeriesSlice (P : (Fin 1 →₀ ℕ) → MvPolynomial (Fin 1) ℝ)
    (x : ℝ) (y : ℂ) : ℂ :=
  ∑' e : Fin 1 ⊕ Fin 1 →₀ ℕ, (realSeriesCoeff P e : ℂ) *
    ∏ i, (Sum.elim (fun _ => (x : ℂ)) (fun _ => y) i) ^ e i

open Filter Topology

/-- The real-boundary slice of a real stable-limit family is a locally uniform
limit of real-rooted univariate polynomials (BKS 2016, Lemma 8). -/
theorem IsRealStableLimit.exists_split_limit_slice
    {P : (Fin 1 →₀ ℕ) → MvPolynomial (Fin 1) ℝ} (hP : IsRealStableLimit P) (x : ℝ) :
    ∃ p : ℕ → ℝ[X], (∀ k, (p k).Splits) ∧
      TendstoLocallyUniformly (fun k y => (complexify (p k)).eval y)
        (realSeriesSlice P x) atTop := by
  obtain ⟨F, hF, _, hconv⟩ := hP
  refine ⟨fun k => slicePolynomial (F k) x, fun k => slicePolynomial_splits (hF k) x, ?_⟩
  have hh := hconv.comp (fun y : ℂ => Sum.elim (fun _ : Fin 1 => (x : ℂ))
      (fun _ : Fin 1 => y)) (by
        apply continuous_pi
        intro i
        cases i with
        | inl i => exact continuous_const
        | inr i => exact continuous_id)
  unfold realSeriesSlice
  simpa only [Function.comp_def, eval_slicePolynomial, complexifyMv] using hh

/-- Hurwitz applied to the real-boundary slice of a real stable-limit family:
unless the whole slice vanishes, each of its zeros is real (BKS 2016, Lemma 8). -/
theorem IsRealStableLimit.im_eq_zero_of_slice_eq_zero
    {P : (Fin 1 →₀ ℕ) → MvPolynomial (Fin 1) ℝ} (hP : IsRealStableLimit P) (x : ℝ)
    (hne : ∃ a, realSeriesSlice P x a ≠ 0) {y : ℂ}
    (hy : realSeriesSlice P x y = 0) : y.im = 0 := by
  obtain ⟨p, hp, hconv⟩ := hP.exists_split_limit_slice x
  have hg : Differentiable ℂ (realSeriesSlice P x) := by
    rw [← differentiableOn_univ]
    exact hconv.tendstoLocallyUniformlyOn.differentiableOn
      (Filter.Eventually.of_forall fun k =>
        (Polynomial.differentiable (complexify (p k))).differentiableOn) isOpen_univ
  exact PolyFiniteDifferenceOp.im_eq_zero_of_split_limit hp hconv hg hne hy

/-- The exponential-polynomial obstruction for a real stable-limit slice.
Both signs of the transcendental symbol are covered by the real nonzero scale `s`.
This is the analytic implication in BKS (2016), Lemma 8, with an explicit series identity. -/
theorem IsRealStableLimit.coeff_support_subsingleton_of_slice
    {P : (Fin 1 →₀ ℕ) → MvPolynomial (Fin 1) ℝ} (hP : IsRealStableLimit P)
    (x : ℝ) (a : ℂ) {s : ℝ} (hs : s ≠ 0) (p : ℂ[X])
    (heq : ∀ y : ℂ, realSeriesSlice P x y =
      Complex.exp (a * y) * p.eval (Complex.exp ((s : ℂ) * y))) :
    Set.Subsingleton {j : ℕ | p.coeff j ≠ 0} := by
  by_cases hp : p = 0
  · simp [hp]
  have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
  obtain ⟨w, hw⟩ := PolyFiniteDifferenceOp.exists_eval_exp_ne_zero hp
  have hne : ∃ y, realSeriesSlice P x y ≠ 0 := by
    refine ⟨w / (s : ℂ), ?_⟩
    rw [heq, mul_div_cancel₀ _ hsC]
    exact mul_ne_zero (Complex.exp_ne_zero _) hw
  apply PolyFiniteDifferenceOp.coeff_support_subsingleton_of_eval_exp
  intro y hy
  have hz : realSeriesSlice P x (y / (s : ℂ)) = 0 := by
    rw [heq, mul_div_cancel₀ _ hsC, hy, mul_zero]
  have him := hP.im_eq_zero_of_slice_eq_zero x hne hz
  rw [Complex.div_ofReal_im] at him
  exact (div_eq_zero_iff).1 him |>.resolve_right hs

end BorceaBranden

namespace PolyFiniteDifferenceOp

open Filter Topology

private theorem polynomial_not_zero_germ {p : ℂ[X]} (hp : p ≠ 0) (z : ℂ) :
    ¬∀ᶠ w in 𝓝 z, p.eval w = 0 := by
  intro h
  apply hp
  apply Polynomial.funext
  intro w
  rw [eval_zero]
  have han := (Polynomial.differentiable p).differentiableOn.analyticOnNhd isOpen_univ
  exact han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ z) h (Set.mem_univ w)

private theorem shift_ratio_not_constant {a b : ℂ} (hab : a ≠ b) {z : ℂ}
    (hzb : z - b ≠ 0) :
    ¬∀ᶠ w in 𝓝 z, (w - a) / (w - b) = (z - a) / (z - b) := by
  let p : ℂ[X] := (X - C a) * C (z - b) - (X - C b) * C (z - a)
  have hp : p ≠ 0 := by
    intro hp
    have hh := congrArg (fun f : ℂ[X] => f.coeff 1) hp
    simp only [p, coeff_sub, coeff_mul_C] at hh
    norm_num at hh
    exact hab (by linear_combination hh)
  intro h
  apply polynomial_not_zero_germ hp z
  have hev : ∀ᶠ w in 𝓝 z, w - b ≠ 0 :=
    (continuousAt_id.sub continuousAt_const).eventually_ne hzb
  filter_upwards [h, hev] with w hw hwb
  have hh := (div_eq_div_iff hwb hzb).1 hw
  simpa [p, sub_eq_zero, mul_comm] using hh

private theorem norm_shift_sq (z : ℂ) (a : ℝ) :
    ‖z - (a : ℂ)‖ ^ 2 = (z.re - a) ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [pow_two]

private theorem norm_shift_lt_of_re_neg {z : ℂ} (hz : z.re < 0)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ‖z - (a : ℂ)‖ < ‖z - (b : ℂ)‖ := by
  have hpos : 0 < (b - a) * (a + b - 2 * z.re) := mul_pos (by linarith) (by linarith)
  have h1 := norm_shift_sq z a
  have h2 := norm_shift_sq z b
  nlinarith [norm_nonneg (z - (a : ℂ)), norm_nonneg (z - (b : ℂ))]

private theorem midpoint_norm_eq (a b : ℝ) :
    ‖((a + b) / 2 : ℂ) + Complex.I - (a : ℂ)‖ =
      ‖((a + b) / 2 : ℂ) + Complex.I - (b : ℂ)‖ := by
  have h1 := norm_shift_sq (((a + b) / 2 : ℂ) + Complex.I) a
  have h2 := norm_shift_sq (((a + b) / 2 : ℂ) + Complex.I) b
  norm_num at h1 h2
  nlinarith [norm_nonneg (((a + b) / 2 : ℂ) + Complex.I - (a : ℂ)),
    norm_nonneg (((a + b) / 2 : ℂ) + Complex.I - (b : ℂ))]

private theorem midpoint_norm_lt {a b c : ℝ} (hac : a < c) (hcb : c < b) :
    ‖((a + b) / 2 : ℂ) + Complex.I - (c : ℂ)‖ <
      ‖((a + b) / 2 : ℂ) + Complex.I - (b : ℂ)‖ := by
  have h1 := norm_shift_sq (((a + b) / 2 : ℂ) + Complex.I) c
  have h2 := norm_shift_sq (((a + b) / 2 : ℂ) + Complex.I) b
  norm_num at h1 h2
  have hh : 0 < (c - a) * (b - c) := mul_pos (by linarith) (by linarith)
  nlinarith [norm_nonneg (((a + b) / 2 : ℂ) + Complex.I - (c : ℂ)),
    norm_nonneg (((a + b) / 2 : ℂ) + Complex.I - (b : ℂ))]

private theorem eval_operator_pow {n : ℕ} (q : Fin n → ℝ[X]) (m : ℕ) (z : ℂ) :
    (complexify (polyFiniteDifferenceOp q (X ^ m))).eval z =
      ∑ k, (complexify (q k)).eval z * (z - (k : ℂ)) ^ m := by
  simp [apply, complexify, Polynomial.eval_map, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_pow, Polynomial.eval₂_sub]

private theorem sum_support {n : ℕ} (q : Fin n → ℝ[X]) (m : ℕ) (z : ℂ) :
    ∑ k ∈ Finset.univ.filter (fun k => q k ≠ 0),
        (complexify (q k)).eval z * (z - (k : ℂ)) ^ m =
      (complexify (polyFiniteDifferenceOp q (X ^ m))).eval z := by
  classical
  rw [eval_operator_pow]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro k _ hk
  have hk0 : q k = 0 := by simpa using hk
  simp [hk0]

private theorem exists_left_eval_ne_zero {p : ℂ[X]} (hp : p ≠ 0) :
    ∃ z : ℂ, z.re < 0 ∧ p.eval z ≠ 0 := by
  by_contra h
  apply polynomial_not_zero_germ hp (-1)
  have hev : ∀ᶠ z : ℂ in 𝓝 (-1), z.re < 0 :=
    Complex.continuous_re.continuousAt.eventually (eventually_lt_nhds (by norm_num))
  filter_upwards [hev] with z hz
  by_contra hn
  exact h ⟨z, hz, hn⟩

private theorem eventually_operator_pow_ne_zero {n : ℕ} (q : Fin n → ℝ[X])
    (s : Finset (Fin n)) (hs : s = Finset.univ.filter (fun k => q k ≠ 0))
    (j : Fin n) (hj : j ∈ s) (hmax : ∀ k ∈ s, k ≤ j) :
    ∀ᶠ m in atTop, polyFiniteDifferenceOp q (X ^ m) ≠ 0 := by
  have hq : q j ≠ 0 := by simpa [hs] using hj
  have hqc : complexify (q j) ≠ 0 := Polynomial.map_ne_zero hq
  obtain ⟨w, hw, hqw⟩ := exists_left_eval_ne_zero hqc
  have hbj : w - (j : ℂ) ≠ 0 := by
    intro he
    have hh := congrArg Complex.re he
    simp only [Complex.sub_re, Complex.natCast_re, Complex.zero_re] at hh
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
    linarith
  obtain ⟨r, hr, hev⟩ := Complex.eventually_forall_ne_zero_of_unique_dominant s
    (fun k z => (complexify (q k)).eval z) (fun k z => z - (k : ℂ)) j hj
    (fun k _ => (Polynomial.differentiable _).continuous.continuousAt)
    (fun _ _ => continuousAt_id.sub continuousAt_const) hbj
    (fun k hk hkj => norm_shift_lt_of_re_neg hw (Nat.cast_nonneg k.val)
      (by exact_mod_cast lt_of_le_of_ne (hmax k hk) hkj)) hqw
  filter_upwards [hev] with m hm
  intro hm0
  have hh := hm w (Metric.mem_ball_self hr)
  rw [hs, sum_support, hm0] at hh
  simp at hh

private theorem limitZeros_extreme_shifts {n : ℕ} (q : Fin n → ℝ[X])
    (s : Finset (Fin n)) (hs : s = Finset.univ.filter (fun k => q k ≠ 0))
    (i j : Fin n) (hi : i ∈ s) (hj : j ∈ s) (hij : i < j)
    (hmin : ∀ k ∈ s, i ≤ k) (hmax : ∀ k ∈ s, k ≤ j) :
    Complex.IsLimitOfZeros
      (fun m z => (complexify (polyFiniteDifferenceOp q (X ^ m))).eval z)
      (((i : ℂ) + (j : ℂ)) / 2 + Complex.I) := by
  have hqi : q i ≠ 0 := by simpa [hs] using hi
  have hqj : q j ≠ 0 := by simpa [hs] using hj
  have hbj : ((i : ℂ) + (j : ℂ)) / 2 + Complex.I - (j : ℂ) ≠ 0 := by
    intro h
    have hh := congrArg Complex.im h
    norm_num at hh
  have hh := Complex.isLimitOfZeros_finset_two_dominant_closure s
    (fun k z => (complexify (q k)).eval z) (fun k z => z - (k : ℂ)) i j hi hj
    (ne_of_lt hij)
    (fun k _ => (Polynomial.differentiable _).analyticAt _)
    (fun _ _ => analyticAt_id.sub analyticAt_const)
    (polynomial_not_zero_germ (Polynomial.map_ne_zero hqi) _)
    (polynomial_not_zero_germ (Polynomial.map_ne_zero hqj) _) hbj
    (midpoint_norm_eq (i : ℝ) (j : ℝ))
    (fun k hk hki hkj => midpoint_norm_lt
      (by exact_mod_cast lt_of_le_of_ne (hmin k hk) (Ne.symm hki))
      (by exact_mod_cast lt_of_le_of_ne (hmax k hk) hkj))
    (shift_ratio_not_constant (by
      intro he
      exact (ne_of_lt hij) (Fin.ext (Nat.cast_injective he))) hbj)
  simpa only [hs, sum_support] using hh

/-- The hard direction of BKS (2016), Lemma 8. Two surviving shifts force nonreal
zeros in images of powers, by the two-dominant-term limit-of-zeros theorem. -/
theorem support_subsingleton_of_preserves {n : ℕ} {q : Fin n → ℝ[X]}
    (hT : PreservesRealRootedOrZero (polyFiniteDifferenceOp q)) :
    Set.Subsingleton {j | q j ≠ 0} := by
  classical
  by_contra h
  obtain ⟨a, ha, b, hb, hab⟩ := Set.not_subsingleton_iff.mp h
  let s := Finset.univ.filter (fun k => q k ≠ 0)
  have ha' : a ∈ s := by simpa [s] using ha
  have hb' : b ∈ s := by simpa [s] using hb
  have hs : s.Nonempty := ⟨a, ha'⟩
  let i := s.min' hs
  let j := s.max' hs
  have hi : i ∈ s := Finset.min'_mem s hs
  have hj : j ∈ s := Finset.max'_mem s hs
  have hmin : ∀ k ∈ s, i ≤ k := fun k hk => s.min'_le k hk
  have hmax : ∀ k ∈ s, k ≤ j := fun k hk => s.le_max' k hk
  have hij : i < j := by
    apply lt_of_le_of_ne (hmin j hj)
    intro he
    have hai : a = i := le_antisymm (he ▸ hmax a ha') (hmin a ha')
    have hbi : b = i := le_antisymm (he ▸ hmax b hb') (hmin b hb')
    exact hab (hai.trans hbi.symm)
  let z : ℂ := ((i : ℂ) + (j : ℂ)) / 2 + Complex.I
  have hz : z.im ≠ 0 := by norm_num [z]
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp
    (isOpen_ne_fun Complex.continuous_im continuous_const) z hz
  have hlim := limitZeros_extreme_shifts q s rfl i j hi hj hij hmin hmax
  obtain ⟨m, hm, w, hw, hzero⟩ :=
    ((eventually_operator_pow_ne_zero q s rfl j hj hmax).and (hlim r hr)).exists
  have hsplit := (hT (X ^ m) ⟨pow_ne_zero _ X_ne_zero, Splits.X.pow m⟩).resolve_left hm
  exact eval_ne_zero_of_splits_im_ne hsplit hm (hball hw) hzero

/-- BKS (2016), Lemma 8: exactly one split coefficient may survive; the zero
operator is included by allowing empty support. -/
theorem preserves_iff {n : ℕ} {q : Fin n → ℝ[X]} :
    PreservesRealRootedOrZero (polyFiniteDifferenceOp q) ↔
      Set.Subsingleton {j | q j ≠ 0} ∧ ∀ j, q j ≠ 0 → (q j).Splits := by
  constructor
  · intro h
    have hs := support_subsingleton_of_preserves h
    exact ⟨hs, (preserves_iff_of_support_subsingleton hs).mp h⟩
  · rintro ⟨hs, hsplit⟩
    exact preserves_of_support_subsingleton hs hsplit

end PolyFiniteDifferenceOp

end RealRooted
