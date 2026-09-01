import RealRooted.Basic
import RealRooted.BorceaBranden.Applications.GeneralDegreeBoxPolarization
import RealRooted.Mathlib.Algebra.MvPolynomial.Stability.Symbol
import RealRooted.MultivariateStability

/-!
# Borcea--Branden finite-symbol classification

Human statement:
https://www.symmetricfunctions.com/stablePolynomials.htm#borceaBrandenFiniteSymbol

Original reference: J. Borcea and P. Branden, "The Lee-Yang and Polya-Schur
programs. I. Linear operators preserving stability", Invent. Math. 177 (2009),
541--569.

This file proves the finite-degree complex algebraic-symbol theorem. The
classification includes the rank-at-most-one
alternative from Theorem 1.1; outside that alternative, preservation is
equivalent to stability of the algebraic symbol. The real-univariate interface
lives in `RealRooted.BorceaBranden.UnivariateFiniteSymbol`.
-/

open Polynomial BigOperators

namespace RealRooted
namespace BorceaBranden

noncomputable section

/-- A complex linear operator on a coordinate-wise degree box preserves
upper-half-plane stability, allowing the zero output. -/
def PreservesComplexStabilityOnDegreeBox
    {σ : Type*} [Fintype σ] (κ : σ → ℕ)
    (T : MvPolynomial.degreeOfLE σ ℂ κ →ₗ[ℂ] MvPolynomial σ ℂ) : Prop :=
  ∀ f, MvUpperHalfPlaneStable f.1 →
    MvUpperHalfPlaneStableOrZero (T f)

/-- The bounded polynomial given in binomial-expansion form by
`∏ i, (X i + C (W i)) ^ κ i`.

These shifted boxes are the test polynomials used in the necessity proof of
Borcea--Brändén Theorem 1.1. -/
def shiftedBoxPolynomial {σ : Type*} [Fintype σ]
    (κ : σ → ℕ) (W : σ → ℂ) :
    MvPolynomial.degreeOfLE σ ℂ κ :=
  ∑ m : {m : σ →₀ ℕ // ∀ i, m i ≤ κ i},
    ((MvPolynomial.boxChoose κ m.1 : ℂ) *
      ∏ i, W i ^ (κ i - m.1 i)) •
        MvPolynomial.basisDegreeOfLE κ m

/-- The bounded-basis definition of `shiftedBoxPolynomial` is the expected
product of shifted powers. -/
theorem shiftedBoxPolynomial_eq_prod {σ : Type*} [Fintype σ]
    (κ : σ → ℕ) (W : σ → ℂ) :
    (shiftedBoxPolynomial κ W).1 =
      ∏ i, (MvPolynomial.X i + MvPolynomial.C (W i)) ^ κ i := by
  classical
  have hfactor (i : σ) :
      (MvPolynomial.X i + MvPolynomial.C (W i) :
        MvPolynomial σ ℂ) ^ κ i =
        ∑ k : Fin (κ i + 1),
          MvPolynomial.X i ^ (k : ℕ) *
            MvPolynomial.C (W i) ^ (κ i - (k : ℕ)) *
              MvPolynomial.C ((κ i).choose (k : ℕ) : ℂ) := by
    rw [add_pow]
    rw [Fin.sum_univ_eq_sum_range
      (fun k : ℕ => (MvPolynomial.X i : MvPolynomial σ ℂ) ^ k *
        MvPolynomial.C (W i) ^ (κ i - k) *
          MvPolynomial.C ((κ i).choose k : ℂ))
      (κ i + 1)]
    simp
  simp only [shiftedBoxPolynomial, Submodule.coe_sum,
    Submodule.coe_smul, MvPolynomial.coe_basisDegreeOfLE,
    MvPolynomial.smul_eq_C_mul]
  simp_rw [hfactor]
  rw [Fintype.prod_sum]
  apply Fintype.sum_equiv (MvPolynomial.degreeOfLEIndexEquiv κ)
  intro m
  change MvPolynomial.C ((MvPolynomial.boxChoose κ m.1 : ℂ) *
      ∏ i, W i ^ (κ i - m.1 i)) * MvPolynomial.monomial m.1 1 =
    ∏ i, MvPolynomial.X i ^ m.1 i *
      MvPolynomial.C (W i) ^ (κ i - m.1 i) *
        MvPolynomial.C ((κ i).choose (m.1 i) : ℂ)
  rw [show (∏ i, MvPolynomial.X i ^ m.1 i *
        MvPolynomial.C (W i) ^ (κ i - m.1 i) *
          MvPolynomial.C ((κ i).choose (m.1 i) : ℂ)) =
      (∏ i, MvPolynomial.X i ^ m.1 i) *
        (∏ i, MvPolynomial.C (W i) ^ (κ i - m.1 i)) *
          ∏ i, MvPolynomial.C ((κ i).choose (m.1 i) : ℂ) by
    simp_rw [Finset.prod_mul_distrib]]
  simp_rw [← map_pow]
  rw [← map_prod, ← map_prod, MvPolynomial.prod_X_pow]
  have hind : Finsupp.indicator (Finset.univ : Finset σ)
      (fun i _ => m.1 i) = m.1 := by
    ext i
    rw [Finsupp.indicator_of_mem (Finset.mem_univ i)]
  rw [hind]
  simp only [MvPolynomial.boxChoose, Nat.cast_prod, map_mul]
  ring

/-- A shifted box is stable when every shift lies in the open upper half-plane. -/
theorem mvUpperHalfPlaneStable_shiftedBoxPolynomial
    {σ : Type*} [Fintype σ] (κ : σ → ℕ) (W : σ → ℂ)
    (hW : ∀ i, 0 < (W i).im) :
    MvUpperHalfPlaneStable (shiftedBoxPolynomial κ W).1 := by
  rw [shiftedBoxPolynomial_eq_prod]
  intro z hz
  simp only [MvPolynomial.eval_prod, Finset.prod_ne_zero_iff,
    MvPolynomial.eval_pow, MvPolynomial.eval_add, MvPolynomial.eval_X,
    MvPolynomial.eval_C, ne_eq]
  intro i _hi
  apply pow_ne_zero
  intro hzero
  have him := congrArg Complex.im hzero
  have hzi : 0 < (z i).im := hz i
  simp only [Complex.add_im, Complex.zero_im] at him
  linarith [hzi, hW i]

/-- The robust perturbation property for a shifted box: every polynomial in
the same degree box can be added with some nonzero scalar while preserving
upper-half-plane stability.

Borcea--Brändén Lemma 3.1 proves this property whenever every coordinate of
`W` lies in the open upper half-plane. Isolating it here gives the precise
analytic input needed by the remaining zero-fiber necessity branch. -/
def HasShiftedBoxPerturbations
    {σ : Type*} [Fintype σ] (κ : σ → ℕ) (W : σ → ℂ) : Prop :=
  ∀ f : MvPolynomial.degreeOfLE σ ℂ κ,
    ∃ ε : ℂ, ε ≠ 0 ∧
      MvUpperHalfPlaneStable (shiftedBoxPolynomial κ W + ε • f).1

/-- A polynomial is uniformly dominated by a shifted box on the open
upper half-plane. This is the quantitative estimate used in the proof of
Borcea--Brändén Lemma 3.1. -/
def IsUniformlyDominatedByShiftedBox
    {σ : Type*} [Fintype σ] {κ : σ → ℕ}
    (W : σ → ℂ) (f : MvPolynomial.degreeOfLE σ ℂ κ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ z, (∀ i, 0 < (z i).im) →
    ‖MvPolynomial.eval z f.1‖ ≤
      C * ‖MvPolynomial.eval z (shiftedBoxPolynomial κ W).1‖

/-- Uniform domination by a stable shifted box gives the nonzero perturbation
required by the zero-fiber necessity argument. -/
theorem hasShiftedBoxPerturbations_of_uniformlyDominated
    {σ : Type*} [Fintype σ] {κ : σ → ℕ} {W : σ → ℂ}
    (hW : ∀ i, 0 < (W i).im)
    (hdom : ∀ f : MvPolynomial.degreeOfLE σ ℂ κ,
      IsUniformlyDominatedByShiftedBox W f) :
    HasShiftedBoxPerturbations κ W := by
  intro f
  obtain ⟨C, hC, hbound⟩ := hdom f
  let ε : ℂ := ((C + 1)⁻¹ : ℝ)
  have hC1 : 0 < C + 1 := by linarith
  have hε : ε ≠ 0 := by
    change (↑((C + 1)⁻¹ : ℝ) : ℂ) ≠ 0
    exact_mod_cast inv_ne_zero (ne_of_gt hC1)
  refine ⟨ε, hε, ?_⟩
  intro z hz
  have hS := mvUpperHalfPlaneStable_shiftedBoxPolynomial κ W hW z hz
  have hSnorm : 0 < ‖MvPolynomial.eval z (shiftedBoxPolynomial κ W).1‖ :=
    norm_pos_iff.mpr hS
  have hεnorm : ‖ε‖ = (C + 1)⁻¹ := by
    change ‖(↑((C + 1)⁻¹ : ℝ) : ℂ)‖ = (C + 1)⁻¹
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hC1)]
  have hεC : ‖ε‖ * C < 1 := by
    rw [hεnorm, inv_mul_eq_div]
    exact (div_lt_one hC1).mpr (by linarith)
  have hsmall : ‖ε * MvPolynomial.eval z f.1‖ <
      ‖MvPolynomial.eval z (shiftedBoxPolynomial κ W).1‖ := by
    calc
      ‖ε * MvPolynomial.eval z f.1‖ =
          ‖ε‖ * ‖MvPolynomial.eval z f.1‖ := norm_mul _ _
      _ ≤ ‖ε‖ *
          (C * ‖MvPolynomial.eval z (shiftedBoxPolynomial κ W).1‖) :=
        mul_le_mul_of_nonneg_left (hbound z hz) (norm_nonneg _)
      _ = (‖ε‖ * C) *
          ‖MvPolynomial.eval z (shiftedBoxPolynomial κ W).1‖ := by ring
      _ < 1 * ‖MvPolynomial.eval z (shiftedBoxPolynomial κ W).1‖ :=
        mul_lt_mul_of_pos_right hεC hSnorm
      _ = ‖MvPolynomial.eval z (shiftedBoxPolynomial κ W).1‖ := one_mul _
  change MvPolynomial.eval z
      ((shiftedBoxPolynomial κ W).1 + ε • f.1) ≠ 0
  rw [MvPolynomial.smul_eq_C_mul]
  simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul,
    MvPolynomial.eval_C]
  intro hzero
  have heq : MvPolynomial.eval z (shiftedBoxPolynomial κ W).1 =
      -(ε * MvPolynomial.eval z f.1) := by
    linear_combination hzero
  have hnormeq := congrArg norm heq
  rw [norm_neg] at hnormeq
  exact (ne_of_lt hsmall) hnormeq.symm

/-- A single upper-half-plane coordinate and its shifted factor admit a
uniform majorant. The loose constant is also large enough to raise exponents
from a monomial degree to the ambient degree-box bound. -/
private theorem norm_le_shift_majorant
    (z W : ℂ) (hz : 0 ≤ z.im) (hW : 0 < W.im) :
    let B : ℝ := 1 + ‖W‖ / W.im + 1 / W.im
    ‖z‖ ≤ B * ‖z + W‖ ∧ 1 ≤ B * ‖z + W‖ := by
  dsimp only
  have hshift : W.im ≤ ‖z + W‖ := by
    have him : W.im ≤ (z + W).im := by
      simp only [Complex.add_im]
      linarith
    exact him.trans (Complex.im_le_norm (z + W))
  have hinv : 1 ≤ W.im⁻¹ * ‖z + W‖ := by
    rw [inv_mul_eq_div]
    exact (le_div_iff₀ hW).2 (by simpa using hshift)
  have hWnorm : ‖W‖ ≤ (‖W‖ / W.im) * ‖z + W‖ := by
    calc
      ‖W‖ = ‖W‖ * 1 := by ring
      _ ≤ ‖W‖ * (W.im⁻¹ * ‖z + W‖) := by gcongr
      _ = (‖W‖ / W.im) * ‖z + W‖ := by
        rw [div_eq_mul_inv]
        ring
  have hztri : ‖z‖ ≤ ‖z + W‖ + ‖W‖ := by
    have hzsub : z = (z + W) - W := by ring
    calc
      ‖z‖ = ‖(z + W) - W‖ := congrArg norm hzsub
      _ ≤ ‖z + W‖ + ‖W‖ := norm_sub_le (z + W) W
  constructor
  · calc
      ‖z‖ ≤ ‖z + W‖ + ‖W‖ := hztri
      _ ≤ (1 + ‖W‖ / W.im + 1 / W.im) * ‖z + W‖ := by
        rw [add_mul, add_mul, one_mul]
        have hlast : 0 ≤ (1 / W.im) * ‖z + W‖ := by positivity
        linarith
  · calc
      1 ≤ W.im⁻¹ * ‖z + W‖ := hinv
      _ ≤ (1 + ‖W‖ / W.im + 1 / W.im) * ‖z + W‖ := by
        rw [add_mul, add_mul, one_mul, one_div]
        have hnormterm : 0 ≤ (‖W‖ / W.im) * ‖z + W‖ := by positivity
        linarith

/-- Coordinatewise majorization, raised to the ambient degree-box exponent. -/
private theorem norm_pow_le_shift_majorant_pow
    (z W : ℂ) (m κ : ℕ) (hz : 0 ≤ z.im) (hW : 0 < W.im)
    (hm : m ≤ κ) :
    ‖z‖ ^ m ≤
      (1 + ‖W‖ / W.im + 1 / W.im) ^ κ * ‖z + W‖ ^ κ := by
  obtain ⟨hzle, hone⟩ := norm_le_shift_majorant z W hz hW
  calc
    ‖z‖ ^ m ≤
        ((1 + ‖W‖ / W.im + 1 / W.im) * ‖z + W‖) ^ m :=
      pow_le_pow_left₀ (norm_nonneg z) hzle m
    _ ≤ ((1 + ‖W‖ / W.im + 1 / W.im) * ‖z + W‖) ^ κ :=
      pow_le_pow_right₀ hone hm
    _ = (1 + ‖W‖ / W.im + 1 / W.im) ^ κ *
        ‖z + W‖ ^ κ := by rw [mul_pow]

/-- Evaluation of one bounded monomial is uniformly dominated by the shifted
box product. -/
private theorem norm_eval_monomial_le_shiftedBox
    {σ : Type*} [Fintype σ] (κ : σ → ℕ) (W z : σ → ℂ)
    (hW : ∀ i, 0 < (W i).im) (hz : ∀ i, 0 ≤ (z i).im)
    (m : σ →₀ ℕ) (hm : ∀ i, m i ≤ κ i) (c : ℂ) :
    ‖MvPolynomial.eval z (MvPolynomial.monomial m c)‖ ≤
      (‖c‖ * ∏ i,
        (1 + ‖W i‖ / (W i).im + 1 / (W i).im) ^ κ i) *
          ∏ i, ‖z i + W i‖ ^ κ i := by
  have hprod : (∏ i, ‖z i‖ ^ m i) ≤
      ∏ i, (1 + ‖W i‖ / (W i).im + 1 / (W i).im) ^ κ i *
        ‖z i + W i‖ ^ κ i := by
    apply Finset.prod_le_prod
    · intro i _hi
      positivity
    · intro i _hi
      exact norm_pow_le_shift_majorant_pow
        (z i) (W i) (m i) (κ i) (hz i) (hW i) (hm i)
  rw [MvPolynomial.eval_monomial,
    m.prod_fintype (fun i e => z i ^ e) (fun i => pow_zero (z i))]
  simp only [norm_mul, norm_prod, norm_pow]
  rw [Finset.prod_mul_distrib] at hprod
  calc
    ‖c‖ * ∏ i, ‖z i‖ ^ m i ≤
        ‖c‖ * ((∏ i,
          (1 + ‖W i‖ / (W i).im + 1 / (W i).im) ^ κ i) *
            ∏ i, ‖z i + W i‖ ^ κ i) :=
      mul_le_mul_of_nonneg_left hprod (norm_nonneg c)
    _ = (‖c‖ * ∏ i,
        (1 + ‖W i‖ / (W i).im + 1 / (W i).im) ^ κ i) *
          ∏ i, ‖z i + W i‖ ^ κ i := by ring

/-- The uniform relative evaluation estimate in Borcea--Brändén Lemma 3.1. -/
theorem uniformlyDominatedByShiftedBox
    {σ : Type*} [Fintype σ] (κ : σ → ℕ) (W : σ → ℂ)
    (hW : ∀ i, 0 < (W i).im)
    (f : MvPolynomial.degreeOfLE σ ℂ κ) :
    IsUniformlyDominatedByShiftedBox W f := by
  classical
  let A : ℝ :=
    ∏ i, (1 + ‖W i‖ / (W i).im + 1 / (W i).im) ^ κ i
  let M : ℝ := (∑ m ∈ f.1.support, ‖MvPolynomial.coeff m f.1‖) * A
  have hA : 0 ≤ A := by
    dsimp only [A]
    apply Finset.prod_nonneg
    intro i _hi
    have hiW := hW i
    positivity
  refine ⟨M, by dsimp only [M]; positivity, ?_⟩
  intro z hz
  have hm (m : σ →₀ ℕ) (hm : m ∈ f.1.support) :
      ∀ i, m i ≤ κ i :=
    (MvPolynomial.mem_degreeOfLE f.1).mp f.2 m hm
  have hshiftNorm :
      ‖MvPolynomial.eval z (shiftedBoxPolynomial κ W).1‖ =
        ∏ i, ‖z i + W i‖ ^ κ i := by
    rw [shiftedBoxPolynomial_eq_prod]
    simp only [MvPolynomial.eval_prod, MvPolynomial.eval_pow,
      MvPolynomial.eval_add, MvPolynomial.eval_X, MvPolynomial.eval_C,
      norm_prod, norm_pow]
  rw [f.1.as_sum, map_sum]
  calc
    ‖∑ m ∈ f.1.support,
        MvPolynomial.eval z
          (MvPolynomial.monomial m (MvPolynomial.coeff m f.1))‖ ≤
        ∑ m ∈ f.1.support,
          ‖MvPolynomial.eval z
            (MvPolynomial.monomial m (MvPolynomial.coeff m f.1))‖ := by
      exact norm_sum_le _ _
    _ ≤ ∑ m ∈ f.1.support,
        ((‖MvPolynomial.coeff m f.1‖ * A) *
          ∏ i, ‖z i + W i‖ ^ κ i) := by
      apply Finset.sum_le_sum
      intro m hm_support
      exact norm_eval_monomial_le_shiftedBox κ W z hW
        (fun i => (hz i).le) m (hm m hm_support)
          (MvPolynomial.coeff m f.1)
    _ = M * ‖MvPolynomial.eval z (shiftedBoxPolynomial κ W).1‖ := by
      rw [hshiftNorm]
      simp only [A, M, Finset.sum_mul]

/-- Borcea--Brändén Lemma 3.1 in the exact weak form needed for the
zero-fiber necessity branch. -/
theorem hasShiftedBoxPerturbations
    {σ : Type*} [Fintype σ] (κ : σ → ℕ) (W : σ → ℂ)
    (hW : ∀ i, 0 < (W i).im) :
    HasShiftedBoxPerturbations κ W := by
  apply hasShiftedBoxPerturbations_of_uniformlyDominated hW
  intro f
  exact uniformlyDominatedByShiftedBox κ W hW f

/-- Specializing the right variables of the finite algebraic symbol gives the
operator applied to the corresponding shifted-box polynomial. This is the
identity `G_T(z, W) = T((z + W)^κ)` used in the necessity proof of
Borcea--Brändén Theorem 1.1. -/
theorem specializeRight_algebraicSymbol
    {σ τ : Type*} [Fintype σ] (κ : σ → ℕ) (W : σ → ℂ)
    (T : MvPolynomial.degreeOfLE σ ℂ κ →ₗ[ℂ] MvPolynomial τ ℂ) :
    specializeRight W (MvPolynomial.algebraicSymbol κ T) =
      T (shiftedBoxPolynomial κ W) := by
  classical
  rw [MvPolynomial.algebraicSymbol_eq_sum]
  unfold shiftedBoxPolynomial specializeRight
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro m _
  unfold MvPolynomial.rightComplementMonomial
  simp only [map_mul]
  rw [MvPolynomial.aeval_rename]
  have hleft :
      Sum.elim MvPolynomial.X (MvPolynomial.C ∘ W) ∘ Sum.inl =
        (MvPolynomial.X : τ → MvPolynomial τ ℂ) := by
    funext i
    rfl
  rw [hleft]
  simp [MvPolynomial.smul_eq_C_mul]
  ring

/-- Evaluation form of `specializeRight_algebraicSymbol`. -/
theorem eval_algebraicSymbol_eq_eval_shiftedBoxPolynomial
    {σ τ : Type*} [Fintype σ] (κ : σ → ℕ) (W : σ → ℂ)
    (T : MvPolynomial.degreeOfLE σ ℂ κ →ₗ[ℂ] MvPolynomial τ ℂ)
    (x : τ → ℂ) :
    MvPolynomial.eval (Sum.elim x W) (MvPolynomial.algebraicSymbol κ T) =
      MvPolynomial.eval x (T (shiftedBoxPolynomial κ W)) := by
  rw [← eval_specializeRight, specializeRight_algebraicSymbol]

/-- The no-zero-fiber case of the necessity direction in Borcea--Brändén
Theorem 1.1: if a stability preserver never kills an upper-half-plane shifted
box, then its algebraic symbol is stable. -/
theorem algebraicSymbol_stable_of_preserves_of_shiftedBox_ne_zero
    {σ τ : Type*} [Fintype σ] (κ : σ → ℕ)
    (T : MvPolynomial.degreeOfLE σ ℂ κ →ₗ[ℂ] MvPolynomial τ ℂ)
    (hT : ∀ f, MvUpperHalfPlaneStable f.1 →
      MvUpperHalfPlaneStableOrZero (T f))
    (hne : ∀ W, (∀ i, 0 < (W i).im) →
      T (shiftedBoxPolynomial κ W) ≠ 0) :
    MvUpperHalfPlaneStable (MvPolynomial.algebraicSymbol κ T) := by
  intro u hu
  let z : τ → ℂ := fun i => u (Sum.inl i)
  let W : σ → ℂ := fun i => u (Sum.inr i)
  have hz : ∀ i, 0 < (z i).im := fun i => hu (Sum.inl i)
  have hW : ∀ i, 0 < (W i).im := fun i => hu (Sum.inr i)
  have hout := hT (shiftedBoxPolynomial κ W)
    (mvUpperHalfPlaneStable_shiftedBoxPolynomial κ W hW)
  have houtStable : MvUpperHalfPlaneStable
      (T (shiftedBoxPolynomial κ W)) :=
    hout.resolve_left (hne W hW)
  have heval := houtStable z hz
  rw [← specializeRight_algebraicSymbol κ W T,
    eval_specializeRight] at heval
  have hu_eq : Sum.elim z W = u := by
    funext i
    cases i <;> rfl
  simpa only [hu_eq] using heval

/-- The exceptional branch in Borcea--Brändén Theorem 1.1: the operator has a
one-dimensional representation with a stable spanning polynomial. This also
includes the zero operator by taking the functional to be zero. -/
def HasStableRankOneRepresentation
    {σ : Type*} [Fintype σ] (κ : σ → ℕ)
    (T : MvPolynomial.degreeOfLE σ ℂ κ →ₗ[ℂ] MvPolynomial σ ℂ) : Prop :=
  ∃ (α : MvPolynomial.degreeOfLE σ ℂ κ →ₗ[ℂ] ℂ)
      (P : MvPolynomial σ ℂ),
    MvUpperHalfPlaneStable P ∧ ∀ f, T f = (α f) • P

/-- If every polynomial in the range of a complex linear map is stable or zero,
then the map has the stable rank-at-most-one representation from
Borcea--Brändén Theorem 1.1(a).

This is the complex stable-subspace rigidity step used in the necessity proof.
Fixing one nonzero stable output `P`, evaluation at an upper-half-plane point
expresses every other output as a scalar multiple of `P`. -/
theorem hasStableRankOneRepresentation_of_range_stableOrZero
    {σ : Type*} [Fintype σ] {κ : σ → ℕ}
    {T : MvPolynomial.degreeOfLE σ ℂ κ →ₗ[ℂ] MvPolynomial σ ℂ}
    (hT : ∀ f, MvUpperHalfPlaneStableOrZero (T f)) :
    HasStableRankOneRepresentation κ T := by
  by_cases hzero : T = 0
  · refine ⟨0, 1, MvUpperHalfPlaneStable.one, ?_⟩
    intro f
    simp [hzero]
  · have hex : ∃ f, T f ≠ 0 := by
      by_contra h
      push Not at h
      apply hzero
      apply LinearMap.ext
      intro f
      exact h f
    obtain ⟨f₀, hf₀⟩ := hex
    let P := T f₀
    have hP : MvUpperHalfPlaneStable P := (hT f₀).resolve_left hf₀
    let z : σ → ℂ := fun _ => Complex.I
    have hz : ∀ i, 0 < (z i).im := by
      intro i
      simp [z]
    have hPz : MvPolynomial.eval z P ≠ 0 := hP z hz
    let α : MvPolynomial.degreeOfLE σ ℂ κ →ₗ[ℂ] ℂ :=
      { toFun := fun f => MvPolynomial.eval z (T f) / MvPolynomial.eval z P
        map_add' := by
          intro f g
          simp [map_add, add_div]
        map_smul' := by
          intro c f
          simp [map_smul, mul_div_assoc] }
    refine ⟨α, P, hP, ?_⟩
    intro f
    let q := T (f - (α f) • f₀)
    have hq : q = T f - (α f) • P := by simp [q, P]
    have hqeval : MvPolynomial.eval z q = 0 := by
      rw [hq]
      simp [α]
      field_simp
      ring
    have hqzero : q = 0 := by
      rcases hT (f - (α f) • f₀) with hzeroq | hstableq
      · exact hzeroq
      · exact (hstableq z hz hqeval).elim
    rw [hq] at hqzero
    exact sub_eq_zero.mp hqzero

/-- Cancellation of a nonzero scalar in the weak stability predicate. -/
private theorem mvUpperHalfPlaneStableOrZero_of_smul
    {σ : Type*} {c : ℂ} (hc : c ≠ 0) {P : MvPolynomial σ ℂ}
    (hP : MvUpperHalfPlaneStableOrZero (c • P)) :
    MvUpperHalfPlaneStableOrZero P := by
  rw [MvPolynomial.smul_eq_C_mul] at hP
  have hscaled := hP.C_mul c⁻¹
  simpa only [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one,
    one_mul] using hscaled

/-- The zero-fiber case of Borcea--Brändén necessity, conditional only on the
robust shifted-box perturbation property supplied by their Lemma 3.1. -/
theorem hasStableRankOneRepresentation_of_preserves_of_shiftedBox_eq_zero
    {σ : Type*} [Fintype σ] {κ : σ → ℕ}
    {T : MvPolynomial.degreeOfLE σ ℂ κ →ₗ[ℂ] MvPolynomial σ ℂ}
    (hT : PreservesComplexStabilityOnDegreeBox κ T)
    {W : σ → ℂ} (hperturb : HasShiftedBoxPerturbations κ W)
    (hzero : T (shiftedBoxPolynomial κ W) = 0) :
    HasStableRankOneRepresentation κ T := by
  apply hasStableRankOneRepresentation_of_range_stableOrZero
  intro f
  obtain ⟨ε, hε, hstable⟩ := hperturb f
  have hout := hT (shiftedBoxPolynomial κ W + ε • f) hstable
  have hscaled : MvUpperHalfPlaneStableOrZero (ε • T f) := by
    simpa [map_add, map_smul, hzero] using hout
  exact mvUpperHalfPlaneStableOrZero_of_smul hε hscaled

/-- The complete necessity implication, reduced to the robust perturbation
lemma for upper-half-plane shifted boxes. -/
theorem rankOne_or_algebraicSymbol_stable_of_preserves_of_perturbations
    {σ : Type*} [Fintype σ] {κ : σ → ℕ}
    {T : MvPolynomial.degreeOfLE σ ℂ κ →ₗ[ℂ] MvPolynomial σ ℂ}
    (hT : PreservesComplexStabilityOnDegreeBox κ T)
    (hperturb : ∀ W, (∀ i, 0 < (W i).im) →
      HasShiftedBoxPerturbations κ W) :
    HasStableRankOneRepresentation κ T ∨
      MvUpperHalfPlaneStable (MvPolynomial.algebraicSymbol κ T) := by
  by_cases hne : ∀ W, (∀ i, 0 < (W i).im) →
      T (shiftedBoxPolynomial κ W) ≠ 0
  · exact Or.inr
      (algebraicSymbol_stable_of_preserves_of_shiftedBox_ne_zero κ T hT hne)
  · push Not at hne
    obtain ⟨W, hW, hzero⟩ := hne
    exact Or.inl
      (hasStableRankOneRepresentation_of_preserves_of_shiftedBox_eq_zero
        hT (hperturb W hW) hzero)

/-- Source-faithful necessity wrapper for the literal “all sufficiently small
positive perturbations” conclusion of Borcea--Brändén Lemma 3.1. -/
theorem rankOne_or_algebraicSymbol_stable_of_preserves_of_robust_perturbations
    {σ : Type*} [Fintype σ] {κ : σ → ℕ}
    {T : MvPolynomial.degreeOfLE σ ℂ κ →ₗ[ℂ] MvPolynomial σ ℂ}
    (hT : PreservesComplexStabilityOnDegreeBox κ T)
    (hrobust : ∀ W, (∀ i, 0 < (W i).im) → ∀ f,
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        MvUpperHalfPlaneStable
          (shiftedBoxPolynomial κ W + (ε : ℂ) • f).1) :
    HasStableRankOneRepresentation κ T ∨
      MvUpperHalfPlaneStable (MvPolynomial.algebraicSymbol κ T) := by
  apply rankOne_or_algebraicSymbol_stable_of_preserves_of_perturbations hT
  intro W hW f
  obtain ⟨ε₀, hε₀, hstable⟩ := hrobust W hW f
  refine ⟨(ε₀ / 2 : ℝ), ?_, ?_⟩
  · exact_mod_cast (half_pos hε₀).ne'
  · exact hstable (ε₀ / 2) (half_pos hε₀) (half_lt_self hε₀)

/-- Necessity in the complex finite-symbol classification: every stability
preserver either has stable rank at most one or has a stable algebraic symbol.

The proof combines the no-zero-fiber symbol argument with the robust
perturbation estimate and stable-range rigidity in the zero-fiber case. -/
theorem rankOne_or_algebraicSymbol_stable_of_preserves
    {σ : Type*} [Fintype σ] {κ : σ → ℕ}
    {T : MvPolynomial.degreeOfLE σ ℂ κ →ₗ[ℂ] MvPolynomial σ ℂ}
    (hT : PreservesComplexStabilityOnDegreeBox κ T) :
    HasStableRankOneRepresentation κ T ∨
      MvUpperHalfPlaneStable (MvPolynomial.algebraicSymbol κ T) := by
  apply rankOne_or_algebraicSymbol_stable_of_preserves_of_perturbations hT
  intro W hW
  exact hasShiftedBoxPerturbations κ W hW

/-- The stable rank-at-most-one alternative in Borcea--Brändén Theorem 1.1
preserves stability, with the zero scalar giving the allowed zero output. -/
theorem HasStableRankOneRepresentation.preservesComplexStabilityOnDegreeBox
    {σ : Type*} [Fintype σ] {κ : σ → ℕ}
    {T : MvPolynomial.degreeOfLE σ ℂ κ →ₗ[ℂ] MvPolynomial σ ℂ}
    (h : HasStableRankOneRepresentation κ T) :
    PreservesComplexStabilityOnDegreeBox κ T := by
  intro f _hf
  obtain ⟨α, P, hP, hT⟩ := h
  rw [hT, MvPolynomial.smul_eq_C_mul]
  exact hP.orZero.C_mul (α f)

/-- Borcea--Brändén, Theorem 1.1: a complex linear operator on a finite degree
box preserves upper-half-plane stability if and only if it has a stable
rank-at-most-one representation or its finite algebraic symbol is stable.

This proposition packages the checked classification theorem below. -/
def finiteComplexSymbolClassificationStatement : Prop :=
  ∀ (σ : Type) [Fintype σ] (κ : σ → ℕ)
      (T : MvPolynomial.degreeOfLE σ ℂ κ →ₗ[ℂ] MvPolynomial σ ℂ),
    PreservesComplexStabilityOnDegreeBox κ T ↔
      HasStableRankOneRepresentation κ T ∨
        MvUpperHalfPlaneStable (MvPolynomial.algebraicSymbol κ T)

/-- Borcea--Brändén finite complex-symbol classification. -/
theorem finiteComplexSymbolClassification :
    finiteComplexSymbolClassificationStatement := by
  intro σ _ κ T
  constructor
  · exact rankOne_or_algebraicSymbol_stable_of_preserves
  · rintro (hrank | hSymbol)
    · exact hrank.preservesComplexStabilityOnDegreeBox
    · intro p hp
      exact RealRooted.BorceaBranden.finiteSymbol_preserves_stability_general
        κ T hSymbol p hp

/-- Outside the rank-at-most-one alternative, the main classification has the
familiar form: an operator preserves stability if and only if its algebraic
symbol is stable. -/
def finiteComplexSymbolIffStatement : Prop :=
  ∀ (σ : Type) [Fintype σ] (κ : σ → ℕ)
      (T : MvPolynomial.degreeOfLE σ ℂ κ →ₗ[ℂ] MvPolynomial σ ℂ),
    ¬HasStableRankOneRepresentation κ T →
      (PreservesComplexStabilityOnDegreeBox κ T ↔
        MvUpperHalfPlaneStable (MvPolynomial.algebraicSymbol κ T))

/-- Non-rank-one form of the complex finite-symbol classification. -/
theorem finiteComplexSymbolIff :
    finiteComplexSymbolIffStatement := by
  intro σ _ κ T hrank
  rw [finiteComplexSymbolClassification σ κ T]
  simp only [hrank, false_or]

end

end BorceaBranden
end RealRooted
