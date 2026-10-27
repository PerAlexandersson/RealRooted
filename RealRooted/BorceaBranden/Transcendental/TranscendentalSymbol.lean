module

import Mathlib.RingTheory.MvPolynomial.Basic
public import RealRooted.BorceaBranden.Transcendental.PivotConverse

@[expose] public section

open Filter Topology
open scoped BigOperators

noncomputable section

namespace RealRooted.BorceaBranden

variable {τ σ : Type*} [Fintype τ] [Fintype σ]

/-- The complex multivariate Laguerre--Pólya class in split variables `(z, w)`.

Membership means that the explicit entire series `∑_α P_α(z) w^α` converges absolutely
everywhere and is a locally uniform limit of upper-half-plane-stable-or-zero polynomials.
This is the limit class used in Borcea--Brändén, arXiv:0809.0401, Theorem 5.1. -/
def IsComplexStableLimit (P : (σ →₀ ℕ) → MvPolynomial τ ℂ) : Prop :=
  ∃ F : ℕ → MvPolynomial (τ ⊕ σ) ℂ,
    (∀ k, MvUpperHalfPlaneStableOrZero (F k)) ∧
    (∀ x : τ ⊕ σ → ℂ,
      Summable fun e : τ ⊕ σ →₀ ℕ => ‖seriesCoeff P e * ∏ i, x i ^ e i‖) ∧
    TendstoLocallyUniformly (fun k (x : τ ⊕ σ → ℂ) => MvPolynomial.eval x (F k))
      (fun x => ∑' e : τ ⊕ σ →₀ ℕ, seriesCoeff P e * ∏ i, x i ^ e i) atTop

/-- The coefficient of the real formal series `∑_α P_α(z) w^α`. -/
def realSeriesCoeff (P : (σ →₀ ℕ) → MvPolynomial τ ℝ)
    (e : τ ⊕ σ →₀ ℕ) : ℝ :=
  (P (Finsupp.sumFinsuppEquivProdFinsupp e).2).coeff
    (Finsupp.sumFinsuppEquivProdFinsupp e).1

/-- The real multivariate Laguerre--Pólya class in split variables `(z, w)`.

The approximating polynomials have real coefficients and are real stable.  The limit is the
explicit complex evaluation of the real-coefficient series.  This is the real limit class used
in Borcea--Brändén, arXiv:0809.0401, Theorem 5.1. -/
def IsRealStableLimit (P : (σ →₀ ℕ) → MvPolynomial τ ℝ) : Prop :=
  ∃ F : ℕ → MvPolynomial (τ ⊕ σ) ℝ,
    (∀ k, MvRealStable (F k)) ∧
    (∀ x : τ ⊕ σ → ℂ,
      Summable fun e : τ ⊕ σ →₀ ℕ =>
        ‖(realSeriesCoeff P e : ℂ) * ∏ i, x i ^ e i‖) ∧
    TendstoLocallyUniformly
      (fun k (x : τ ⊕ σ → ℂ) =>
        MvPolynomial.eval x (MvPolynomial.map Complex.ofRealHom (F k)))
      (fun x => ∑' e : τ ⊕ σ →₀ ℕ,
        (realSeriesCoeff P e : ℂ) * ∏ i, x i ^ e i) atTop

/-- The multivariate factorial `α! = ∏ i, (α i)!`. -/
def multiFactorial (α : σ →₀ ℕ) : ℕ :=
  ∏ i, (α i).factorial

/-- The signed reciprocal factorial `(-1)^|α| / α!`. -/
def signedInvFactorial (α : σ →₀ ℕ) : ℂ :=
  (-1 : ℂ) ^ (∑ i, α i) / (multiFactorial α : ℂ)

/-- The coefficient polynomial of the transcendental symbol of `T` at `w^α`.

Thus `G_T(z,w) = ∑_α transcendentalSymbolPolynomial T α (z) w^α`.  This is the symbol
normalization in Borcea--Brändén, arXiv:0809.0401, Theorem 1.3. -/
def transcendentalSymbolPolynomial
    (T : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial τ ℂ) (α : σ →₀ ℕ) :
    MvPolynomial τ ℂ :=
  MvPolynomial.C (signedInvFactorial α) * T (MvPolynomial.monomial α 1)

/-- The coefficient of `z^γ w^α` in the transcendental symbol of `T`. -/
def transcendentalSymbolCoeff
    (T : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial τ ℂ) (e : τ ⊕ σ →₀ ℕ) : ℂ :=
  seriesCoeff (transcendentalSymbolPolynomial T) e

/-- The explicit entire-series expression for the transcendental symbol `G_T`. -/
def transcendentalSymbol
    (T : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial τ ℂ) (x : τ ⊕ σ → ℂ) : ℂ :=
  ∑' e : τ ⊕ σ →₀ ℕ, transcendentalSymbolCoeff T e * ∏ i, x i ^ e i

omit [Fintype τ] in
/-- Coefficient identification for the transcendental symbol. -/
theorem coeff_transcendentalSymbolPolynomial
    (T : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial τ ℂ)
    (α : σ →₀ ℕ) (γ : τ →₀ ℕ) :
    (transcendentalSymbolPolynomial T α).coeff γ =
      signedInvFactorial α * (T (MvPolynomial.monomial α 1)).coeff γ := by
  simp only [transcendentalSymbolPolynomial, MvPolynomial.coeff_C_mul]

private theorem signedInvFactorial_ne_zero (α : σ →₀ ℕ) :
    signedInvFactorial α ≠ 0 := by
  have hfactorial : multiFactorial α ≠ 0 := by
    unfold multiFactorial
    exact Finset.prod_ne_zero_iff.mpr fun i _ => Nat.factorial_ne_zero (α i)
  unfold signedInvFactorial multiFactorial
  exact div_ne_zero (pow_ne_zero _ (by norm_num)) (Nat.cast_ne_zero.mpr hfactorial)

omit [Fintype τ] in
/-- A complex linear operator is determined by its transcendental-symbol coefficient
polynomials. -/
theorem transcendentalSymbolPolynomial_injective :
    Function.Injective
      (transcendentalSymbolPolynomial :
        (MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial τ ℂ) →
          (σ →₀ ℕ) → MvPolynomial τ ℂ) := by
  intro T U hTU
  apply (MvPolynomial.basisMonomials σ ℂ).ext
  intro α
  simp only [MvPolynomial.coe_basisMonomials]
  apply MvPolynomial.ext
  intro γ
  have h := congrArg (fun p : MvPolynomial τ ℂ => p.coeff γ)
    (congrFun hTU α)
  simp only [coeff_transcendentalSymbolPolynomial] at h
  exact mul_left_cancel₀ (signedInvFactorial_ne_zero α) h

omit [Fintype τ] in
/-- A complex linear operator is determined by every scalar coefficient of its transcendental
symbol. -/
theorem transcendentalSymbolCoeff_injective :
    Function.Injective
      (transcendentalSymbolCoeff :
        (MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial τ ℂ) →
          (τ ⊕ σ →₀ ℕ) → ℂ) := by
  intro T U hTU
  apply transcendentalSymbolPolynomial_injective
  funext α
  apply MvPolynomial.ext
  intro γ
  have h := congrFun hTU (Finsupp.sumFinsuppEquivProdFinsupp.symm (γ, α))
  simpa only [transcendentalSymbolCoeff, seriesCoeff,
    Equiv.apply_symm_apply] using h

/-- The zero coefficient family belongs to the complex stable limit class. -/
theorem isComplexStableLimit_zero :
    IsComplexStableLimit (fun _ : σ →₀ ℕ => (0 : MvPolynomial τ ℂ)) := by
  refine ⟨fun _ => 0, fun _ => Or.inl rfl, ?_, ?_⟩
  · intro x
    exact (summable_zero : Summable (fun _ : τ ⊕ σ →₀ ℕ => (0 : ℝ))).congr
      (fun e => by simp [seriesCoeff])
  · simp only [seriesCoeff, AddMonoidAlgebra.coeff_zero]
    intro u hu x
    refine ⟨Set.univ, Filter.univ_mem, Filter.Eventually.of_forall ?_⟩
    intro k y hy
    simpa using (refl_mem_uniformity hu : ((0 : ℂ), 0) ∈ u)

/-- Scale the right-block coordinates of a point. -/
def rightScaledPoint (r : σ → ℝ) (x : τ ⊕ σ → ℂ) : τ ⊕ σ → ℂ :=
  Sum.elim (fun i => x (Sum.inl i)) (fun i => (r i : ℂ) * x (Sum.inr i))

/-- Substitute `w_i ↦ r_i w_i`, leaving the left-block variables fixed. -/
def rightScaledPolynomial (r : σ → ℝ) (p : MvPolynomial (τ ⊕ σ) ℂ) :
    MvPolynomial (τ ⊕ σ) ℂ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (Sum.elim (fun i => MvPolynomial.X (Sum.inl i))
      (fun i => MvPolynomial.C (r i : ℂ) * MvPolynomial.X (Sum.inr i))) p

omit [Fintype τ] [Fintype σ] in
/-- Evaluation commutes with positive right-coordinate scaling. -/
theorem eval_rightScaledPolynomial (r : σ → ℝ) (x : τ ⊕ σ → ℂ)
    (p : MvPolynomial (τ ⊕ σ) ℂ) :
    MvPolynomial.eval x (rightScaledPolynomial r p) =
      MvPolynomial.eval (rightScaledPoint r x) p := by
  unfold rightScaledPolynomial
  change MvPolynomial.eval x (MvPolynomial.eval₂ MvPolynomial.C _ p) = _
  rw [MvPolynomial.eval_eval₂]
  rw [show (MvPolynomial.eval x).comp MvPolynomial.C = RingHom.id ℂ by ext; simp]
  congr 1
  funext i
  cases i with
  | inl i => simp [rightScaledPoint]
  | inr i => simp [rightScaledPoint]

/-- Scale the `w^α` coefficient polynomial by `∏ i, r_i^(α_i)`. -/
def rightScaledFamily (r : σ → ℝ) (P : (σ →₀ ℕ) → MvPolynomial τ ℂ)
    (α : σ →₀ ℕ) : MvPolynomial τ ℂ :=
  MvPolynomial.C (∏ i, (r i : ℂ) ^ α i) * P α

private theorem seriesTerm_rightScaledFamily (r : σ → ℝ)
    (P : (σ →₀ ℕ) → MvPolynomial τ ℂ) (x : τ ⊕ σ → ℂ)
    (e : τ ⊕ σ →₀ ℕ) :
    seriesCoeff (rightScaledFamily r P) e * ∏ i, x i ^ e i =
      seriesCoeff P e * ∏ i, rightScaledPoint r x i ^ e i := by
  classical
  unfold seriesCoeff rightScaledFamily rightScaledPoint
  rw [MvPolynomial.coeff_C_mul, Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, mul_pow, Finset.prod_mul_distrib,
    Finsupp.snd_sumFinsuppEquivProdFinsupp]
  ring

private theorem series_rightScaledFamily (r : σ → ℝ)
    (P : (σ →₀ ℕ) → MvPolynomial τ ℂ) (x : τ ⊕ σ → ℂ) :
    (∑' e : τ ⊕ σ →₀ ℕ, seriesCoeff (rightScaledFamily r P) e * ∏ i, x i ^ e i) =
      ∑' e : τ ⊕ σ →₀ ℕ,
        seriesCoeff P e * ∏ i, rightScaledPoint r x i ^ e i := by
  apply tsum_congr
  exact seriesTerm_rightScaledFamily r P x

omit [Fintype τ] [Fintype σ] in
private theorem rightScaledPolynomial_stableOrZero (r : σ → ℝ) (hr : ∀ i, 0 < r i)
    {p : MvPolynomial (τ ⊕ σ) ℂ} (hp : MvUpperHalfPlaneStableOrZero p) :
    MvUpperHalfPlaneStableOrZero (rightScaledPolynomial r p) := by
  rcases hp with hp | hp
  · left
    subst p
    simp [rightScaledPolynomial]
  · right
    intro x hx
    rw [eval_rightScaledPolynomial]
    apply hp
    rintro (i | i)
    · simpa [rightScaledPoint] using hx (Sum.inl i)
    · change 0 < ((r i : ℂ) * x (Sum.inr i)).im
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      exact mul_pos (hr i) (hx (Sum.inr i))

/-- The complex stable limit class is closed under positive scaling of the `w` coordinates.
This is the scaling step used in Borcea--Brändén, arXiv:0809.0401, Theorem 5.1. -/
theorem IsComplexStableLimit.rightScaledFamily (r : σ → ℝ) (hr : ∀ i, 0 < r i)
    {P : (σ →₀ ℕ) → MvPolynomial τ ℂ} (hP : IsComplexStableLimit P) :
    IsComplexStableLimit (rightScaledFamily r P) := by
  obtain ⟨F, hFstable, hsum, hconv⟩ := hP
  refine ⟨fun k => rightScaledPolynomial r (F k),
    fun k => rightScaledPolynomial_stableOrZero r hr (hFstable k), ?_, ?_⟩
  · intro x
    exact (hsum (rightScaledPoint r x)).congr fun e => by
      rw [seriesTerm_rightScaledFamily]
  · have hcontinuous : Continuous (rightScaledPoint (τ := τ) r) := by
      apply continuous_pi
      rintro (i | i)
      · exact continuous_apply (Sum.inl i)
      · exact continuous_const.mul (continuous_apply (Sum.inr i))
    have hc := hconv.comp (rightScaledPoint r) hcontinuous
    simpa only [Function.comp_def, eval_rightScaledPolynomial,
      series_rightScaledFamily] using hc

end RealRooted.BorceaBranden
