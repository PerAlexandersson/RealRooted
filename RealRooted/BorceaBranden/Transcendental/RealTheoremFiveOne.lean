import RealRooted.BorceaBranden.RealFiniteClassificationIff
import RealRooted.BorceaBranden.Transcendental.PivotForward

open Filter Topology
open scoped BigOperators

noncomputable section

namespace RealRooted.BorceaBranden

variable {τ σ : Type*} [Fintype τ] [Fintype σ] [DecidableEq σ]

/-- Coefficientwise complexification of a real formal polynomial family. -/
def complexifyFamily (P : (σ →₀ ℕ) → MvPolynomial τ ℝ)
    (α : σ →₀ ℕ) : MvPolynomial τ ℂ :=
  complexifyMv (P α)

/-- The signed reciprocal factorial over the reals. -/
def realSignedInvFactorial (α : σ →₀ ℕ) : ℝ :=
  (-1 : ℝ) ^ (∑ i, α i) / (multiFactorial α : ℝ)

/-- The real coefficient family of the transcendental symbol. -/
def realTranscendentalSymbolPolynomial
    (T : MvPolynomial σ ℝ →ₗ[ℝ] MvPolynomial τ ℝ)
    (α : σ →₀ ℕ) : MvPolynomial τ ℝ :=
  MvPolynomial.C (realSignedInvFactorial α) *
    T (MvPolynomial.monomial α 1)

/-- Negate the right formal variables in a real coefficient family. -/
def negRightFamily (P : (σ →₀ ℕ) → MvPolynomial τ ℝ)
    (α : σ →₀ ℕ) : MvPolynomial τ ℝ :=
  MvPolynomial.C ((-1 : ℝ) ^ (∑ i, α i)) * P α

/-- The finite real falling-factorial truncation of a coefficient family. -/
def realGlue (P : (σ →₀ ℕ) → MvPolynomial τ ℝ)
    (κ : (σ →₀ ℕ) → ℝ) (β : σ →₀ ℕ) :
    MvPolynomial (τ ⊕ σ) ℝ :=
  ∑ α ∈ Finset.Iic β, ∑ γ ∈ (P α).support,
    MvPolynomial.monomial
      (Finsupp.sumFinsuppEquivProdFinsupp.symm (γ, α))
      (κ α * (P α).coeff γ)

omit [Fintype τ] [Fintype σ] [DecidableEq σ] in
/-- The complex coefficient of a complexified real family is the cast of its
real series coefficient. -/
theorem seriesCoeff_complexifyFamily
    (P : (σ →₀ ℕ) → MvPolynomial τ ℝ) (e : τ ⊕ σ →₀ ℕ) :
    seriesCoeff (complexifyFamily P) e = (realSeriesCoeff P e : ℂ) := by
  unfold seriesCoeff complexifyFamily realSeriesCoeff complexifyMv
  rw [MvPolynomial.coeff_map]
  rfl

omit [Fintype τ] [Fintype σ] in
/-- Complexification commutes with finite real gluing. -/
theorem complexifyMv_realGlue
    (P : (σ →₀ ℕ) → MvPolynomial τ ℝ)
    (κ : (σ →₀ ℕ) → ℝ) (β : σ →₀ ℕ) :
    complexifyMv (realGlue P κ β) = glue (complexifyFamily P) κ β := by
  classical
  unfold realGlue glue complexifyFamily complexifyMv
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro α _hα
  rw [map_sum]
  rw [MvPolynomial.support_map_of_injective _ Complex.ofRealHom.injective]
  apply Finset.sum_congr rfl
  intro γ _hγ
  rw [MvPolynomial.map_monomial]
  congr 1
  simp only [map_mul]
  rfl

omit [DecidableEq σ] in
/-- A real stable-limit witness is also a complex stable-limit witness after
coefficientwise complexification. -/
theorem IsRealStableLimit.isComplexStableLimit
    {P : (σ →₀ ℕ) → MvPolynomial τ ℝ} (hP : IsRealStableLimit P) :
    IsComplexStableLimit (complexifyFamily P) := by
  obtain ⟨F, hF, hsum, hconv⟩ := hP
  refine ⟨fun k => complexifyMv (F k), fun k => Or.inr (hF k), ?_, ?_⟩
  · intro x
    exact (hsum x).congr fun e => by rw [seriesCoeff_complexifyFamily]
  · change TendstoLocallyUniformly
      (fun k (x : τ ⊕ σ → ℂ) =>
        MvPolynomial.eval x (MvPolynomial.map Complex.ofRealHom (F k)))
      (fun x => ∑' e : τ ⊕ σ →₀ ℕ,
        (realSeriesCoeff P e : ℂ) * ∏ i, x i ^ e i) atTop
    exact hconv

/-- Borcea--Brändén, arXiv:0809.0401, Theorem 5.1, forward real
implication: every falling-factorial truncation of a real stable limit is real
stable or zero. -/
theorem realGlue_stableOrZero_of_isRealStableLimit
    (P : (σ →₀ ℕ) → MvPolynomial τ ℝ) (hP : IsRealStableLimit P)
    (β : σ →₀ ℕ) :
    MvRealStableOrZero (realGlue P (fun α => fall α β) β) := by
  rw [mvRealStableOrZero_iff_complexifyMv, complexifyMv_realGlue]
  exact fallingFactorial_glue_stableOrZero_of_isComplexStableLimit
    (complexifyFamily P) hP.isComplexStableLimit β

omit [DecidableEq σ] in
private theorem real_jensen_eq_zero_of_not_le {α β : σ →₀ ℕ} (h : ¬ α ≤ β) :
    MvPolynomial.jensen α β = 0 := by
  rw [Finsupp.le_def] at h
  obtain ⟨i, hi⟩ := not_forall.mp h
  unfold MvPolynomial.jensen
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rw [(Nat.descFactorial_eq_zero_iff_lt).mpr (Nat.lt_of_not_ge hi)]
  simp

private theorem real_tendsto_descFactorial_div_pow (a : ℕ) :
    Tendsto (fun n : ℕ => (n.descFactorial a : ℝ) / (n : ℝ) ^ a) atTop (𝓝 1) := by
  induction a with
  | zero => simp
  | succ a ih =>
    have h1 : Tendsto (fun n : ℕ => (((n - a : ℕ) : ℝ) / n)) atTop (𝓝 1) := by
      have h2 : Tendsto (fun n : ℕ => (1 : ℝ) - (a : ℝ) * (1 / (n : ℝ)))
          atTop (𝓝 1) := by
        have ht := (tendsto_one_div_atTop_nhds_zero_nat).const_mul (a : ℝ)
        simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub ht
      refine h2.congr' ?_
      filter_upwards [eventually_ge_atTop (a + 1)] with n hn
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by lia)
      rw [Nat.cast_sub (by lia)]
      field_simp
    have ht := h1.mul ih
    rw [mul_one] at ht
    refine ht.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [Nat.descFactorial_succ, Nat.cast_mul, pow_succ]
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by lia)
    field_simp

omit [DecidableEq σ] in
private theorem real_constExp_apply (m : ℕ) (i : σ) : constExp σ m i = m := rfl

omit [DecidableEq σ] in
private theorem real_tendsto_jensen_constExp (α : σ →₀ ℕ) :
    Tendsto (fun m : ℕ => MvPolynomial.jensen α (constExp σ (m + 1)))
      atTop (𝓝 1) := by
  unfold MvPolynomial.jensen
  simp only [real_constExp_apply]
  have ht := tendsto_finsetProd (Finset.univ : Finset σ) (fun i _ =>
    (real_tendsto_descFactorial_div_pow (α i)).comp (tendsto_add_atTop_nat 1))
  simpa [Function.comp] using ht

omit [Fintype τ] in
private theorem eval_realGlue_jensen [Finite τ]
    (P : (σ →₀ ℕ) → MvPolynomial τ ℂ) (m : ℕ) (x : τ ⊕ σ → ℂ) :
    MvPolynomial.eval x
        (glue P (fun α => MvPolynomial.jensen α (constExp σ (m + 1)))
          (constExp σ (m + 1))) =
      MvPolynomial.eval
        (Sum.elim (fun t => x (Sum.inl t))
          (fun j => x (Sum.inr j) / ((m + 1 : ℕ) : ℂ)))
        (glue P (fun α => fall α (constExp σ (m + 1)))
          (constExp σ (m + 1))) := by
  let := Fintype.ofFinite τ
  unfold glue
  simp only [map_sum, MvPolynomial.eval_monomial]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun γ _ => ?_
  rw [Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp),
    Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Finsupp.sumFinsuppEquivProdFinsupp_symm_inl,
    Finsupp.sumFinsuppEquivProdFinsupp_symm_inr, Sum.elim_inl, Sum.elim_inr,
    MvPolynomial.jensen, fall, real_constExp_apply]
  push_cast
  simp only [div_pow, Finset.prod_div_distrib]
  ring

omit [Fintype τ] in
private theorem stableOrZero_realGlue_jensen [Finite τ]
    (P : (σ →₀ ℕ) → MvPolynomial τ ℂ)
    (h : ∀ β : σ →₀ ℕ,
      MvUpperHalfPlaneStableOrZero (glue P (fun α => fall α β) β))
    (m : ℕ) :
    MvUpperHalfPlaneStableOrZero
      (glue P (fun α => MvPolynomial.jensen α (constExp σ (m + 1)))
        (constExp σ (m + 1))) := by
  rcases h (constExp σ (m + 1)) with hz | hs
  · left
    apply MvPolynomial.funext
    intro x
    rw [eval_realGlue_jensen, hz]
    simp
  · right
    intro x hx
    rw [eval_realGlue_jensen]
    apply hs
    rintro (t | j)
    · simpa using hx (Sum.inl t)
    · simp only [Sum.elim_inr, Set.mem_ofPred_eq]
      rw [Complex.div_natCast_im]
      exact div_pos (hx (Sum.inr j)) (by positivity)

omit [DecidableEq σ] in
private theorem isRealStableLimit_of_forall_eq_zero
    (P : (σ →₀ ℕ) → MvPolynomial τ ℝ) (hP : ∀ α, P α = 0) :
    IsRealStableLimit P := by
  classical
  let q : ℕ → MvPolynomial (τ ⊕ σ) ℝ := fun k =>
    MvPolynomial.C (((k + 1 : ℕ) : ℝ)⁻¹)
  let qc : ℕ → MvPolynomial (τ ⊕ σ) ℂ := fun k => complexifyMv (q k)
  have hqc : ∀ k, qc k = MvPolynomial.C
      (((((k + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ)) := by
    intro k
    simp [qc, q, complexifyMv]
  have hq : ∀ k, MvRealStable (q k) := by
    intro k z _hz
    simp only [q, complexifyMv, MvPolynomial.map_C, MvPolynomial.eval_C]
    exact Complex.ofReal_ne_zero.mpr
      (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)))
  have hbound : ∀ r : ℝ, 0 < r → ∃ K : ℝ, ∀ k z, (∀ i, ‖z i‖ ≤ r) →
      ‖MvPolynomial.eval z (qc k)‖ ≤ K := by
    intro r _hr
    refine ⟨1, fun k z _hz => ?_⟩
    rw [hqc, MvPolynomial.eval_C]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact (inv_le_one₀ (by positivity)).2 (by norm_num)
  have hcoeff : ∀ e : τ ⊕ σ →₀ ℕ,
      Tendsto (fun k => (qc k).coeff e) atTop (𝓝 0) := by
    intro e
    by_cases he : e = 0
    · subst e
      simp only [hqc, MvPolynomial.coeff_C, eq_self, ite_true]
      have ht := Complex.continuous_ofReal.continuousAt.tendsto.comp
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa [Function.comp_def] using ht
    · have hz : ∀ k, (qc k).coeff e = 0 := by
        intro k
        rw [hqc, MvPolynomial.coeff_C, ite_eq_right (Ne.symm he)]
      simpa only [hz] using (tendsto_const_nhds (x := (0 : ℂ)))
  obtain ⟨_hsum, hconv⟩ :=
    MvPolynomial.tendstoLocallyUniformly_of_bounded_of_coeff_tendsto
      qc (fun _ => 0) hbound hcoeff
  have hreal : ∀ e, realSeriesCoeff P e = 0 := by
    intro e
    simp [realSeriesCoeff, hP]
  refine ⟨q, hq, ?_, ?_⟩
  · intro x
    simp only [hreal, Complex.ofReal_zero, zero_mul, norm_zero]
    exact summable_zero
  · change TendstoLocallyUniformly
      (fun k x => MvPolynomial.eval x (qc k))
      (fun x => ∑' e : τ ⊕ σ →₀ ℕ,
        (realSeriesCoeff P e : ℂ) * ∏ i, x i ^ e i) atTop
    simpa only [hreal, Complex.ofReal_zero, zero_mul, tsum_zero] using hconv

/-- Borcea--Brändén, arXiv:0809.0401, Theorem 5.1, reverse real
implication: real stable-or-zero falling-factorial truncations produce a
locally uniform limit of real stable polynomials. -/
theorem isRealStableLimit_of_forall_realGlue_stableOrZero
    (P : (σ →₀ ℕ) → MvPolynomial τ ℝ)
    (h : ∀ β : σ →₀ ℕ,
      MvRealStableOrZero (realGlue P (fun α => fall α β) β)) :
    IsRealStableLimit P := by
  classical
  by_cases hzero : ∀ α, P α = 0
  · exact isRealStableLimit_of_forall_eq_zero P hzero
  · obtain ⟨α₀, hα₀⟩ := not_forall.mp hzero
    have hexists : ∃ γ₀, (P α₀).coeff γ₀ ≠ 0 := by
      by_contra hall
      apply hα₀
      ext γ
      rw [AddMonoidAlgebra.coeff_zero]
      exact not_ne_iff.mp (not_exists.mp hall γ)
    obtain ⟨γ₀, hγ₀⟩ := hexists
    let e₀ : τ ⊕ σ →₀ ℕ :=
      Finsupp.sumFinsuppEquivProdFinsupp.symm (γ₀, α₀)
    let f : ℕ → MvPolynomial (τ ⊕ σ) ℝ := fun m =>
      realGlue P (fun α => MvPolynomial.jensen α (constExp σ (m + 1)))
        (constExp σ (m + 1))
    let fc : ℕ → MvPolynomial (τ ⊕ σ) ℂ := fun m => complexifyMv (f m)
    let κ : ℕ → (τ ⊕ σ →₀ ℕ) → ℝ := fun m e =>
      MvPolynomial.jensen (Finsupp.sumFinsuppEquivProdFinsupp e).2
        (constExp σ (m + 1))
    have hcoef : ∀ m e,
        (fc m).coeff e = (κ m e : ℂ) * (realSeriesCoeff P e : ℂ) := by
      intro m e
      rw [show fc m = glue (complexifyFamily P)
        (fun α => MvPolynomial.jensen α (constExp σ (m + 1)))
        (constExp σ (m + 1)) by simp [fc, f, complexifyMv_realGlue], coeff_glue]
      rw [seriesCoeff_complexifyFamily]
      split_ifs with hle
      · rfl
      · have hkzero : κ m e = 0 := real_jensen_eq_zero_of_not_le hle
        rw [hkzero, Complex.ofReal_zero, zero_mul]
    have hκt : ∀ e, Tendsto (fun m => κ m e) atTop (𝓝 1) := fun e =>
      real_tendsto_jensen_constExp _
    have hst : ∀ m, MvRealStableOrZero (f m) := by
      intro m
      rw [mvRealStableOrZero_iff_complexifyMv]
      rw [show complexifyMv (f m) = glue (complexifyFamily P)
        (fun α => MvPolynomial.jensen α (constExp σ (m + 1)))
        (constExp σ (m + 1)) by simp [f, complexifyMv_realGlue]]
      apply stableOrZero_realGlue_jensen
      intro β
      rw [← complexifyMv_realGlue, ← mvRealStableOrZero_iff_complexifyMv]
      exact h β
    have hcst : ∀ m, MvUpperHalfPlaneStable (fc m) ∨ fc m = 0 := by
      intro m
      rcases hst m with hz | hs
      · exact Or.inr (by simp [fc, hz, complexifyMv])
      · exact Or.inl hs
    obtain ⟨B, C, m₀, hB⟩ :=
      exists_norm_eval_le_exp_sq (fun e => (realSeriesCoeff P e : ℂ)) κ fc
        hcoef hκt hcst
    have he₀ : realSeriesCoeff P e₀ ≠ 0 := by
      simpa [e₀, realSeriesCoeff] using hγ₀
    have hev : ∀ᶠ m in atTop, κ m e₀ ∈ Set.Ioo (1 / 2 : ℝ) 2 :=
      (hκt e₀).eventually (Ioo_mem_nhds (by norm_num) (by norm_num))
    obtain ⟨m₁, hm₁⟩ := eventually_atTop.mp hev
    let M := max m₀ m₁
    obtain ⟨hsum, hconv⟩ :=
      MvPolynomial.tendstoLocallyUniformly_of_bounded_of_coeff_tendsto
        (fun k => fc (k + M)) (fun e => (realSeriesCoeff P e : ℂ))
        (fun r hr => ⟨B * Real.exp (C * r ^ 2), fun k z hz =>
          hB (k + M) (le_trans (le_max_left _ _) (Nat.le_add_left _ _))
            r hr.le z hz⟩)
        (fun e => by
          simp only [hcoef]
          have ht := (hκt e).comp (tendsto_add_atTop_nat M)
          have ht' := (Complex.continuous_ofReal.tendsto 1).comp ht
          simpa [Function.comp] using ht'.mul_const (realSeriesCoeff P e : ℂ))
    refine ⟨fun k => f (k + M), ?_, hsum, ?_⟩
    · intro k
      rcases hst (k + M) with hz | hs
      · exfalso
        have hc : (fc (k + M)).coeff e₀ ≠ 0 := by
          rw [hcoef]
          exact mul_ne_zero
            (Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_trans (by norm_num)
              (hm₁ (k + M) (by
                exact le_trans (le_max_right _ _) (Nat.le_add_left _ _))).1)))
            (Complex.ofReal_ne_zero.mpr he₀)
        apply hc
        simp [fc, hz, complexifyMv]
      · exact hs
    · exact hconv

/-- Cofinal-subsequence form of Borcea--Brändén, arXiv:0809.0401,
Theorem 5.1 (real reverse implication). -/
theorem isRealStableLimit_of_cofinal_constExp_realGlue_stableOrZero
    (P : (σ →₀ ℕ) → MvPolynomial τ ℝ) (b : ℕ → ℕ)
    (hb : Tendsto b atTop atTop)
    (h : ∀ m,
      MvRealStableOrZero
        (realGlue P (fun α => fall α (constExp σ (b m + 1)))
          (constExp σ (b m + 1)))) :
    IsRealStableLimit P := by
  classical
  by_cases hzero : ∀ α, P α = 0
  · exact isRealStableLimit_of_forall_eq_zero P hzero
  · obtain ⟨α₀, hα₀⟩ := not_forall.mp hzero
    have hexists : ∃ γ₀, (P α₀).coeff γ₀ ≠ 0 := by
      by_contra hall
      apply hα₀
      ext γ
      rw [AddMonoidAlgebra.coeff_zero]
      exact not_ne_iff.mp (not_exists.mp hall γ)
    obtain ⟨γ₀, hγ₀⟩ := hexists
    let e₀ : τ ⊕ σ →₀ ℕ :=
      Finsupp.sumFinsuppEquivProdFinsupp.symm (γ₀, α₀)
    let f : ℕ → MvPolynomial (τ ⊕ σ) ℝ := fun m =>
      realGlue P (fun α => MvPolynomial.jensen α (constExp σ (b m + 1)))
        (constExp σ (b m + 1))
    let fc : ℕ → MvPolynomial (τ ⊕ σ) ℂ := fun m => complexifyMv (f m)
    let κ : ℕ → (τ ⊕ σ →₀ ℕ) → ℝ := fun m e =>
      MvPolynomial.jensen (Finsupp.sumFinsuppEquivProdFinsupp e).2
        (constExp σ (b m + 1))
    have hcoef : ∀ m e,
        (fc m).coeff e = (κ m e : ℂ) * (realSeriesCoeff P e : ℂ) := by
      intro m e
      rw [show fc m = glue (complexifyFamily P)
        (fun α => MvPolynomial.jensen α (constExp σ (b m + 1)))
        (constExp σ (b m + 1)) by simp [fc, f, complexifyMv_realGlue], coeff_glue]
      rw [seriesCoeff_complexifyFamily]
      split_ifs with hle
      · rfl
      · have hkzero : κ m e = 0 := real_jensen_eq_zero_of_not_le hle
        rw [hkzero, Complex.ofReal_zero, zero_mul]
    have hκt : ∀ e, Tendsto (fun m => κ m e) atTop (𝓝 1) := by
      intro e
      have ht := (real_tendsto_jensen_constExp
        (Finsupp.sumFinsuppEquivProdFinsupp e).2).comp hb
      simpa [κ, Function.comp_def] using ht
    have hst : ∀ m, MvRealStableOrZero (f m) := by
      intro m
      rw [mvRealStableOrZero_iff_complexifyMv]
      rw [show complexifyMv (f m) = glue (complexifyFamily P)
        (fun α => MvPolynomial.jensen α (constExp σ (b m + 1)))
        (constExp σ (b m + 1)) by simp [f, complexifyMv_realGlue]]
      have hg : MvUpperHalfPlaneStableOrZero
          (glue (complexifyFamily P)
            (fun α => fall α (constExp σ (b m + 1)))
            (constExp σ (b m + 1))) := by
        rw [← complexifyMv_realGlue, ← mvRealStableOrZero_iff_complexifyMv]
        exact h m
      rcases hg with hz | hs
      · left
        apply MvPolynomial.funext
        intro x
        rw [eval_realGlue_jensen, hz]
        simp
      · right
        intro x hx
        rw [eval_realGlue_jensen]
        apply hs
        rintro (t | j)
        · simpa using hx (Sum.inl t)
        · simp only [Sum.elim_inr, Set.mem_ofPred_eq]
          rw [Complex.div_natCast_im]
          exact div_pos (hx (Sum.inr j)) (by positivity)
    have hcst : ∀ m, MvUpperHalfPlaneStable (fc m) ∨ fc m = 0 := by
      intro m
      rcases hst m with hz | hs
      · exact Or.inr (by simp [fc, hz, complexifyMv])
      · exact Or.inl hs
    obtain ⟨B, C, m₀, hB⟩ :=
      exists_norm_eval_le_exp_sq (fun e => (realSeriesCoeff P e : ℂ)) κ fc
        hcoef hκt hcst
    have he₀ : realSeriesCoeff P e₀ ≠ 0 := by
      simpa [e₀, realSeriesCoeff] using hγ₀
    have hev : ∀ᶠ m in atTop, κ m e₀ ∈ Set.Ioo (1 / 2 : ℝ) 2 :=
      (hκt e₀).eventually (Ioo_mem_nhds (by norm_num) (by norm_num))
    obtain ⟨m₁, hm₁⟩ := eventually_atTop.mp hev
    let M := max m₀ m₁
    obtain ⟨hsum, hconv⟩ :=
      MvPolynomial.tendstoLocallyUniformly_of_bounded_of_coeff_tendsto
        (fun k => fc (k + M)) (fun e => (realSeriesCoeff P e : ℂ))
        (fun r hr => ⟨B * Real.exp (C * r ^ 2), fun k z hz =>
          hB (k + M) (le_trans (le_max_left _ _) (Nat.le_add_left _ _))
            r hr.le z hz⟩)
        (fun e => by
          simp only [hcoef]
          have ht := (hκt e).comp (tendsto_add_atTop_nat M)
          have ht' := (Complex.continuous_ofReal.tendsto 1).comp ht
          simpa [Function.comp] using ht'.mul_const (realSeriesCoeff P e : ℂ))
    refine ⟨fun k => f (k + M), ?_, hsum, ?_⟩
    · intro k
      rcases hst (k + M) with hz | hs
      · exfalso
        have hc : (fc (k + M)).coeff e₀ ≠ 0 := by
          rw [hcoef]
          exact mul_ne_zero
            (Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_trans (by norm_num)
              (hm₁ (k + M) (by
                exact le_trans (le_max_right _ _) (Nat.le_add_left _ _))).1)))
            (Complex.ofReal_ne_zero.mpr he₀)
        apply hc
        simp [fc, hz, complexifyMv]
      · exact hs
    · exact hconv

/-- **Borcea--Brändén, arXiv:0809.0401, Theorem 5.1 (real case).**
A real formal series is a locally uniform limit of real stable polynomials if
and only if all its falling-factorial truncations are real stable or zero. -/
theorem isRealStableLimit_iff_forall_realGlue_stableOrZero
    (P : (σ →₀ ℕ) → MvPolynomial τ ℝ) :
    IsRealStableLimit P ↔
      ∀ β : σ →₀ ℕ,
        MvRealStableOrZero (realGlue P (fun α => fall α β) β) := by
  constructor
  · exact fun hP β => realGlue_stableOrZero_of_isRealStableLimit P hP β
  · exact isRealStableLimit_of_forall_realGlue_stableOrZero P

end RealRooted.BorceaBranden
