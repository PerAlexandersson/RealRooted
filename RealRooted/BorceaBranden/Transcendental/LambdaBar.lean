import RealRooted.BorceaBranden.Transcendental.TranscendentalSymbol
import RealRooted.BorceaBranden.Transcendental.JensenMultiplier

open scoped BigOperators

noncomputable section

namespace RealRooted.BorceaBranden

variable {τ σ : Type*} [Finite τ] [Fintype σ]

/-- The right-block falling-factorial operator
`z^γ w^α ↦ (β)_α z^γ w^α`. -/
def lambdaBar (β : σ →₀ ℕ) (p : MvPolynomial (τ ⊕ σ) ℂ) :
    MvPolynomial (τ ⊕ σ) ℂ :=
  p.coeff.sum fun e a =>
    MvPolynomial.monomial e
      (((fall (Finsupp.sumFinsuppEquivProdFinsupp e).2 β : ℝ) : ℂ) * a)

omit [Finite τ] in
/-- Coefficients of the right-block falling-factorial operator. -/
@[simp]
theorem coeff_lambdaBar (β : σ →₀ ℕ) (p : MvPolynomial (τ ⊕ σ) ℂ)
    (e : τ ⊕ σ →₀ ℕ) :
    (lambdaBar β p).coeff e =
      (fall (Finsupp.sumFinsuppEquivProdFinsupp e).2 β : ℂ) * p.coeff e := by
  classical
  rw [lambdaBar, MvPolynomial.sum_def, MvPolynomial.coeff_sum]
  by_cases he : e ∈ p.support
  · simp [he, MvPolynomial.coeff_monomial]
  · have hcoeff : p.coeff e = 0 := Finsupp.notMem_support_iff.mp he
    simp [he, hcoeff, MvPolynomial.coeff_monomial]

omit [Finite τ] [Fintype σ] in
private theorem exists_coordinateFallingFactorialTransform_stableOrZero
    {τ σ : Type*} [Finite τ] [Finite σ]
    (β : σ →₀ ℕ) (f : MvPolynomial (τ ⊕ σ) ℂ)
    (hf : MvUpperHalfPlaneStable f) (s : Finset σ) :
    ∃ g : MvPolynomial (τ ⊕ σ) ℂ,
      MvUpperHalfPlaneStableOrZero g ∧
        ∀ e : τ ⊕ σ →₀ ℕ,
          g.coeff e =
            ((∏ i ∈ s,
              ((β i).descFactorial (e (Sum.inr i)) : ℝ) : ℝ) : ℂ) * f.coeff e := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨f, hf.orZero, ?_⟩
      intro e
      simp
  | @insert q s hqs ih =>
      obtain ⟨g, hg, hcoeff⟩ := ih
      rcases hg with hzero | hg
      · subst g
        refine ⟨0, Or.inl rfl, ?_⟩
        intro e
        have hz :
            ((∏ i ∈ s,
              ((β i).descFactorial (e (Sum.inr i)) : ℝ) : ℝ) : ℂ) * f.coeff e = 0 :=
          (hcoeff e).symm
        push_cast at hz
        rw [Finset.prod_insert hqs]
        push_cast
        rw [mul_assoc, hz, mul_zero]
        simp only [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
      · let gamma : ℕ → ℝ := fun k => ((β q).descFactorial k : ℝ)
        let g' := coordinateDiagonalOperator gamma (Sum.inr q) g
        have hg' : MvUpperHalfPlaneStableOrZero g' :=
          IsPFMultiplierSequence.coordinateDiagonalOperator_preserves_stability
            (isPFMultiplierSequence_descFactorial (β q))
              (g.degreeOf (Sum.inr q)) (Sum.inr q) le_rfl hg
        refine ⟨g', hg', ?_⟩
        intro e
        rw [show g' = coordinateDiagonalOperator gamma (Sum.inr q) g from rfl,
          coeff_coordinateDiagonalOperator, hcoeff]
        simp only [gamma]
        rw [Finset.prod_insert hqs]
        push_cast
        ring

/-- The operator `Λbar_β : z^γ w^α ↦ (β)_α z^γ w^α` preserves
upper-half-plane stability, with zero output allowed.  This is the spectator-variable form of
Borcea--Brändén, arXiv:0809.0401, Lemma 5.2. -/
theorem lambdaBar_stableOrZero (β : σ →₀ ℕ) {p : MvPolynomial (τ ⊕ σ) ℂ}
    (hp : MvUpperHalfPlaneStableOrZero p) :
    MvUpperHalfPlaneStableOrZero (lambdaBar β p) := by
  rcases hp with hp | hp
  · subst p
    left
    ext e
    simp
  · obtain ⟨g, hg, hcoeff⟩ :=
      exists_coordinateFallingFactorialTransform_stableOrZero β p hp Finset.univ
    have heq : g = lambdaBar β p := by
      ext e
      rw [hcoeff, coeff_lambdaBar]
      simp only [fall]
      congr 2
    rw [← heq]
    exact hg

/-- Restrict a global linear operator to the coordinate degree box `β`. -/
def degreeBoxRestriction (β : σ → ℕ)
    (T : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial τ ℂ) :
    MvPolynomial.degreeOfLE σ ℂ β →ₗ[ℂ] MvPolynomial τ ℂ :=
  T.comp (MvPolynomial.degreeOfLE σ ℂ β).subtype

/-- The finite Jensen truncation `J_β T = Λbar_β G_T`. -/
def jensenTruncation (β : σ →₀ ℕ)
    (T : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial τ ℂ) :
    MvPolynomial (τ ⊕ σ) ℂ := by
  classical
  exact glue (transcendentalSymbolPolynomial T) (fun α => fall α β) β

omit [Finite τ] in
/-- The coefficient of the Jensen truncation is
`(β)_α (-1)^|α| / α!` times the corresponding coefficient of `T(z^α)`, and is zero outside
the box. -/
theorem coeff_jensenTruncation (β : σ →₀ ℕ)
    (T : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial τ ℂ) (e : τ ⊕ σ →₀ ℕ) :
    (jensenTruncation β T).coeff e =
      (if (Finsupp.sumFinsuppEquivProdFinsupp e).2 ≤ β then
        (fall (Finsupp.sumFinsuppEquivProdFinsupp e).2 β : ℂ) else 0) *
        transcendentalSymbolCoeff T e := by
  classical
  rw [jensenTruncation, coeff_glue]
  rfl

end RealRooted.BorceaBranden
