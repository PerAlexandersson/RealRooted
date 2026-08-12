import RealRooted.Basic
import RealRooted.Mathlib.Algebra.MvPolynomial.Stability.Symbol
import RealRooted.MultivariateStability

/-!
# Borcea--Branden finite-symbol challenge entry point

Human statement:
https://www.symmetricfunctions.com/stablePolynomials.htm#borceaBrandenFiniteSymbol

Original reference: J. Borcea and P. Branden, "The Lee-Yang and Polya-Schur
programs. I. Linear operators preserving stability", Invent. Math. 177 (2009),
541--569.

This file records Lean-facing interfaces for the finite-degree algebraic
symbol theorem. The complex classification includes the rank-at-most-one
alternative from Theorem 1.1; outside that alternative, preservation is
equivalent to stability of the algebraic symbol. These are statement
interfaces, not proofs of the classification. Tactic-specific
coefficient-bidiagonal specializations live in `RealRooted.Tactic.FiniteSymbolPF`.
-/

open Polynomial BigOperators

namespace RealRooted
namespace Challenges
namespace BorceaBranden

noncomputable section

/-! ## Complex finite-symbol classification -/

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
    have hq : q = T f - (α f) • P := by
      simp [q, P]
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

This is the main classification challenge. It is an explicit proposition, not
a proved theorem. -/
def finiteComplexSymbolClassificationStatement : Prop :=
  ∀ (σ : Type) [Fintype σ] (κ : σ → ℕ)
      (T : MvPolynomial.degreeOfLE σ ℂ κ →ₗ[ℂ] MvPolynomial σ ℂ),
    PreservesComplexStabilityOnDegreeBox κ T ↔
      HasStableRankOneRepresentation κ T ∨
        MvUpperHalfPlaneStable (MvPolynomial.algebraicSymbol κ T)

/-- Admitted Borcea--Brändén finite complex-symbol classification.

This is the single explicit admission for the classification challenge tracked
in issue #372. It is not a checked proof. -/
theorem finiteComplexSymbolClassification :
    finiteComplexSymbolClassificationStatement := by
  sorry

/-- Outside the rank-at-most-one alternative, the main classification has the
familiar form: an operator preserves stability if and only if its algebraic
symbol is stable. This remains an explicit challenge proposition. -/
def finiteComplexSymbolIffStatement : Prop :=
  ∀ (σ : Type) [Fintype σ] (κ : σ → ℕ)
      (T : MvPolynomial.degreeOfLE σ ℂ κ →ₗ[ℂ] MvPolynomial σ ℂ),
    ¬HasStableRankOneRepresentation κ T →
      (PreservesComplexStabilityOnDegreeBox κ T ↔
        MvUpperHalfPlaneStable (MvPolynomial.algebraicSymbol κ T))

/-- Admitted non-rank-one form of the complex finite-symbol classification.

This is a formal consequence of the single admitted classification theorem,
not an additional admission. -/
theorem finiteComplexSymbolIff :
    finiteComplexSymbolIffStatement := by
  intro σ _ κ T hrank
  rw [finiteComplexSymbolClassification σ κ T]
  simp only [hrank, false_or]

/-! ## Real univariate application interface -/

/-- Regard a univariate polynomial as a bivariate polynomial in the first
variable. -/
def polynomialInFirstMv (p : ℝ[X]) : MvPolynomial (Fin 2) ℝ :=
  p.eval₂ (MvPolynomial.C : ℝ →+* MvPolynomial (Fin 2) ℝ)
    (MvPolynomial.X (0 : Fin 2))

/-- The finite algebraic symbol `T((x + y)^d)` of a real linear operator on
univariate polynomials, expanded through the monomial basis in degree `d`. -/
def finiteAlgebraicSymbol (d : ℕ) (T : ℝ[X] →ₗ[ℝ] ℝ[X]) :
    MvPolynomial (Fin 2) ℝ :=
  ∑ k ∈ Finset.range (d + 1),
    MvPolynomial.C (Nat.choose d k : ℝ) *
      polynomialInFirstMv (T ((X : ℝ[X]) ^ k)) *
        (MvPolynomial.X (1 : Fin 2)) ^ (d - k)

/-- Degree-bounded preservation of real-rootedness, allowing the zero output. -/
def PreservesRealRootedUpTo
    (d : ℕ) (T : ℝ[X] →ₗ[ℝ] ℝ[X]) : Prop :=
  ∀ {p : ℝ[X]}, p.natDegree ≤ d → p.Splits → T p = 0 ∨ (T p).Splits

/-- The positive-symbol sufficiency direction of Borcea--Branden,
Theorem 1.2(b), specialized to one real source variable of degree at most `d`.

The paper's symbol is `T((z + w)^d)`, which is `finiteAlgebraicSymbol d T`
after expanding in the monomial basis. The complex counterpart is
Theorem 1.1(b). The statement below records only the application-facing
implication to real-rooted inputs and zero-aware outputs, not the converse,
the signed-symbol branch, or the low-rank alternative. -/
def finiteSymbolTheoremStatement : Prop :=
  ∀ {d : ℕ} {T : ℝ[X] →ₗ[ℝ] ℝ[X]},
    MvUpperHalfPlaneStable (complexifyMv (finiteAlgebraicSymbol d T)) →
      PreservesRealRootedUpTo d T

/- The checked witness lives in
`RealRooted.BorceaBranden.Applications.RealUnivariateSymbol`; importing it here
would create an application/core cycle. -/

/-- Direct use of the finite-symbol theorem interface. -/
theorem preservesRealRootedUpTo_of_finiteSymbol
    (hBB : finiteSymbolTheoremStatement)
    {d : ℕ} {T : ℝ[X] →ₗ[ℝ] ℝ[X]}
    (hstable :
      MvUpperHalfPlaneStable (complexifyMv (finiteAlgebraicSymbol d T))) :
    PreservesRealRootedUpTo d T :=
  hBB hstable

end

end BorceaBranden
end Challenges
end RealRooted
