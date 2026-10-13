import RealRooted.BorceaBranden.Transcendental.UniformSzasz
import RealRooted.Mathlib.Analysis.Complex.Polynomial.CoeffEstimates

open Filter Topology

noncomputable section

namespace RealRooted.BorceaBranden

variable {τ σ : Type*} [Fintype τ] [Fintype σ] [DecidableEq σ]

/-- The falling factorial `(β)_α = ∏ i, (β i)! / (β i - α i)!` (`0` when `α ≰ β`). -/
def fall (α β : σ →₀ ℕ) : ℝ :=
  ∏ i, ((β i).descFactorial (α i) : ℝ)

/-- The constant exponent vector `(m, …, m)`. -/
def constExp (σ : Type*) [Fintype σ] (m : ℕ) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun _ => m)

/-- Given coefficients `P α ∈ ℂ[z]` (`α ∈ ℕ^σ`) and multipliers `κ α`, the polynomial
`∑_{α ≤ β} κ α · P α (z) w^α` in the variables `z = (inl _)`, `w = (inr _)`. -/
def glue (P : (σ →₀ ℕ) → MvPolynomial τ ℂ)
    (κ : (σ →₀ ℕ) → ℝ) (β : σ →₀ ℕ) :
    MvPolynomial (τ ⊕ σ) ℂ :=
  ∑ α ∈ Finset.Iic β, ∑ γ ∈ (P α).support,
    MvPolynomial.monomial (Finsupp.sumFinsuppEquivProdFinsupp.symm (γ, α))
      ((κ α : ℂ) * (P α).coeff γ)

/-- The coefficient of the formal series `∑_α P_α(z) w^α` at the monomial `z^γ w^α`. -/
def seriesCoeff (P : (σ →₀ ℕ) → MvPolynomial τ ℂ) (e : τ ⊕ σ →₀ ℕ) : ℂ :=
  (P (Finsupp.sumFinsuppEquivProdFinsupp e).2).coeff (Finsupp.sumFinsuppEquivProdFinsupp e).1

/-! ## Auxiliary lemmas for `pivot_converse` -/

omit [Fintype τ] [Fintype σ] in
private theorem coeff_glue (P : (σ →₀ ℕ) → MvPolynomial τ ℂ)
    (κ : (σ →₀ ℕ) → ℝ) (β : σ →₀ ℕ)
    (e : τ ⊕ σ →₀ ℕ) :
    (glue P κ β).coeff e =
      (if (Finsupp.sumFinsuppEquivProdFinsupp e).2 ≤ β then
        (κ (Finsupp.sumFinsuppEquivProdFinsupp e).2 : ℂ) else 0) * seriesCoeff P e := by
  classical
  set E :=
    (Finsupp.sumFinsuppEquivProdFinsupp :
      (τ ⊕ σ →₀ ℕ) ≃ (τ →₀ ℕ) × (σ →₀ ℕ)) with hE
  have inner : ∀ α, (∑ γ ∈ (P α).support,
      MvPolynomial.monomial (E.symm (γ, α)) ((κ α : ℂ) * (P α).coeff γ)).coeff e =
      if (E e).2 = α then (κ α : ℂ) * (P α).coeff (E e).1 else 0 := by
    intro α
    rw [MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial]
    have key : ∀ γ, (E.symm (γ, α) = e) ↔ (γ = (E e).1 ∧ α = (E e).2) := by
      intro γ
      rw [Equiv.symm_apply_eq, Prod.ext_iff]
    simp only [key]
    by_cases hα : (E e).2 = α
    · subst hα
      simp only [and_true, ite_true]
      rw [Finset.sum_ite_eq']
      split_ifs with hm
      · rfl
      · rw [MvPolynomial.notMem_support_iff.mp hm, mul_zero]
    · have : ∀ γ, ¬ (γ = (E e).1 ∧ α = (E e).2) := fun γ h => hα h.2.symm
      simp [this, hα]
  unfold glue
  rw [MvPolynomial.coeff_sum, ← hE]
  simp only [inner]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_Iic, seriesCoeff]
  split_ifs <;> simp_all [E]

omit [DecidableEq σ] in
private theorem jensen_eq_zero_of_not_le {α β : σ →₀ ℕ} (h : ¬ α ≤ β) :
    MvPolynomial.jensen α β = 0 := by
  rw [Finsupp.le_def] at h
  push Not at h
  obtain ⟨i, hi⟩ := h
  unfold MvPolynomial.jensen
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rw [(Nat.descFactorial_eq_zero_iff_lt).mpr hi]
  simp

private theorem tendsto_descFactorial_div_pow (a : ℕ) :
    Tendsto (fun n : ℕ => (n.descFactorial a : ℝ) / (n : ℝ) ^ a) atTop (𝓝 1) := by
  induction a with
  | zero => simp
  | succ a ih =>
    have h1 : Tendsto (fun n : ℕ => (((n - a : ℕ) : ℝ) / n)) atTop (𝓝 1) := by
      have h2 : Tendsto (fun n : ℕ => (1 : ℝ) - (a : ℝ) * (1 / (n : ℝ)))
          atTop (𝓝 1) := by
        have := (tendsto_one_div_atTop_nhds_zero_nat).const_mul (a : ℝ)
        simpa using (tendsto_const_nhds (x := (1:ℝ))).sub this
      refine h2.congr' ?_
      filter_upwards [eventually_ge_atTop (a + 1)] with n hn
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by lia)
      rw [Nat.cast_sub (by lia)]
      field_simp
    have := h1.mul ih
    rw [mul_one] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [Nat.descFactorial_succ, Nat.cast_mul, pow_succ]
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by lia)
    field_simp

omit [DecidableEq σ] in
private theorem constExp_apply (m : ℕ) (i : σ) : constExp σ m i = m := rfl

omit [DecidableEq σ] in
private theorem tendsto_jensen_constExp (α : σ →₀ ℕ) :
    Tendsto (fun m : ℕ => MvPolynomial.jensen α (constExp σ (m + 1)))
      atTop (𝓝 1) := by
  unfold MvPolynomial.jensen
  simp only [constExp_apply]
  have key := tendsto_finsetProd (Finset.univ : Finset σ) (fun i _ =>
    (tendsto_descFactorial_div_pow (α i)).comp (tendsto_add_atTop_nat 1))
  simpa [Function.comp] using key

omit [Fintype τ] in
/-- Evaluating the Jensen-glued polynomial equals evaluating the falling-factorial-glued one with
the `w`-variables divided by `m + 1`. -/
private theorem eval_glue_jensen [Finite τ]
    (P : (σ →₀ ℕ) → MvPolynomial τ ℂ) (m : ℕ) (x : τ ⊕ σ → ℂ) :
    MvPolynomial.eval x
        (glue P (fun α => MvPolynomial.jensen α (constExp σ (m + 1)))
          (constExp σ (m + 1))) =
      MvPolynomial.eval
        (Sum.elim (fun t => x (Sum.inl t)) (fun j => x (Sum.inr j) / ((m + 1 : ℕ) : ℂ)))
        (glue P (fun α => fall α (constExp σ (m + 1))) (constExp σ (m + 1))) := by
  let := Fintype.ofFinite τ
  unfold glue
  simp only [map_sum, MvPolynomial.eval_monomial]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun γ _ => ?_
  rw [Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp),
    Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Finsupp.sumFinsuppEquivProdFinsupp_symm_inl,
    Finsupp.sumFinsuppEquivProdFinsupp_symm_inr, Sum.elim_inl, Sum.elim_inr,
    MvPolynomial.jensen, fall, constExp_apply]
  push_cast
  simp only [div_pow, Finset.prod_div_distrib]
  ring

omit [Fintype τ] in
private theorem stable_or_zero_glue_jensen [Finite τ]
    (P : (σ →₀ ℕ) → MvPolynomial τ ℂ)
    (h : ∀ β : σ →₀ ℕ,
      MvUpperHalfPlaneStable (glue P (fun α => fall α β) β) ∨
        glue P (fun α => fall α β) β = 0)
    (m : ℕ) :
    MvUpperHalfPlaneStable
      (glue P (fun α => MvPolynomial.jensen α (constExp σ (m + 1)))
        (constExp σ (m + 1))) ∨
      glue P (fun α => MvPolynomial.jensen α (constExp σ (m + 1)))
        (constExp σ (m + 1)) = 0 := by
  rcases h (constExp σ (m + 1)) with hs | hz
  · left
    intro x hx
    rw [eval_glue_jensen]
    apply hs
    rintro (t | j)
    · simpa using hx (Sum.inl t)
    · simp only [Sum.elim_inr, Set.mem_ofPred_eq]
      rw [Complex.div_natCast_im]
      exact div_pos (hx (Sum.inr j)) (by positivity)
  · right
    apply MvPolynomial.funext
    intro x
    rw [eval_glue_jensen, hz]
    simp

/-! ## Target -/

/-- **Borcea--Brändén, arXiv:0809.0401, Theorem 5.1, sufficiency (⇐).**
Let `P α ∈ ℂ[z]` (`α ∈ ℕ^σ`) be
such that for every `β ∈ ℕ^σ` the polynomial
`∑_{α ≤ β} (β)_α P_α(z) w^α` is stable or zero.
Then the formal series
`∑_α P_α(z) w^α` is a locally uniform limit of stable-or-zero polynomials
in the variables `(z, w)`:
there are polynomials `F k`, stable or zero, such that the series `∑ c_e x^e` converges absolutely
everywhere and `F k → ∑ c_e x^e` locally uniformly, where `c_e` is the coefficient of
`z^γ w^α` in the series.

Proof (paper §5.3): with `β_m = (m,…,m)` put
`F_m = ∑_{α ≤ β_m} J(α,β_m) P_α w^α`.  Since
`J(α, β_m) = (β_m)_α / m^{|α|}`, we have `F_m(z,w) = G_m(z, w/m)`, where
`G_m = ∑_{α ≤ β_m} (β_m)_α P_α w^α`.  This is stable or zero by hypothesis.  Positive
rescaling preserves the upper half-plane, so `F_m` is stable or zero for `m ≥ 1`.  Its
coefficients are `κ_m(e) * c e`, where `κ_m(e) = J(α(e), β_m) → 1`.
Hence `exists_norm_eval_le_exp_sq` applies and gives `B`, `C`, and `m₀`;
consequently `F_{m₀+k}`
is bounded on every polydisc uniformly in `k`, and
`MvPolynomial.tendstoLocallyUniformly_of_bounded_of_coeff_tendsto` gives the conclusion for
`F k := F_{m₀+k}`. -/
theorem exists_stableOrZero_tendstoLocallyUniformly_of_fallingFactorial_glue
    (P : (σ →₀ ℕ) → MvPolynomial τ ℂ)
    (h : ∀ β : σ →₀ ℕ,
      MvUpperHalfPlaneStable (glue P (fun α => fall α β) β) ∨
        glue P (fun α => fall α β) β = 0) :
    ∃ F : ℕ → MvPolynomial (τ ⊕ σ) ℂ,
      (∀ k, MvUpperHalfPlaneStable (F k) ∨ F k = 0) ∧
      (∀ x : τ ⊕ σ → ℂ,
        Summable fun e : τ ⊕ σ →₀ ℕ => ‖seriesCoeff P e * ∏ i, x i ^ (e i)‖) ∧
      TendstoLocallyUniformly (fun k (x : τ ⊕ σ → ℂ) => MvPolynomial.eval x (F k))
        (fun x => ∑' e : τ ⊕ σ →₀ ℕ, seriesCoeff P e * ∏ i, x i ^ (e i)) atTop := by
  set f : ℕ → MvPolynomial (τ ⊕ σ) ℂ := fun m =>
    glue P (fun α => MvPolynomial.jensen α (constExp σ (m + 1)))
      (constExp σ (m + 1)) with hf
  set κ : ℕ → (τ ⊕ σ →₀ ℕ) → ℝ := fun m e =>
    MvPolynomial.jensen (Finsupp.sumFinsuppEquivProdFinsupp e).2
      (constExp σ (m + 1)) with hκ
  have hcoef : ∀ m e, (f m).coeff e = (κ m e : ℂ) * seriesCoeff P e := by
    intro m e
    simp only [hf, hκ, coeff_glue]
    split_ifs with hle
    · rfl
    · rw [jensen_eq_zero_of_not_le hle, Complex.ofReal_zero]
  have hκt : ∀ e, Tendsto (fun m => κ m e) atTop (𝓝 1) := fun e =>
    tendsto_jensen_constExp _
  have hst : ∀ m, MvUpperHalfPlaneStable (f m) ∨ f m = 0 := fun m =>
    stable_or_zero_glue_jensen P h m
  obtain ⟨B, C, m₀, hB⟩ :=
    exists_norm_eval_le_exp_sq (seriesCoeff P) κ f hcoef hκt hst
  obtain ⟨h1, h2⟩ := MvPolynomial.tendstoLocallyUniformly_of_bounded_of_coeff_tendsto
    (fun k => f (k + m₀)) (seriesCoeff P)
    (fun r hr => ⟨B * Real.exp (C * r ^ 2), fun k z hz => hB (k + m₀) (by lia) r hr.le z hz⟩)
    (fun e => by
      simp only [hcoef]
      have := ((hκt e).comp (tendsto_add_atTop_nat m₀))
      have h' := (Complex.continuous_ofReal.tendsto 1).comp this
      simpa [Function.comp] using h'.mul_const (seriesCoeff P e))
  exact ⟨fun k => f (k + m₀), fun k => hst _, h1, h2⟩

end RealRooted.BorceaBranden
