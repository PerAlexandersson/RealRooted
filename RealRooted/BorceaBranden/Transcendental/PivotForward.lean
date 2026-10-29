module

public import RealRooted.BorceaBranden.Transcendental.LambdaBar
import RealRooted.Mathlib.Analysis.Complex.Polynomial.CoeffExtraction
import RealRooted.Mathlib.Analysis.Complex.Hurwitz
import Mathlib.Algebra.MvPolynomial.Funext

public section

open Filter Topology

noncomputable section

namespace RealRooted.BorceaBranden

variable {τ σ : Type*} [Fintype τ] [Fintype σ] [DecidableEq σ]

omit [DecidableEq σ] in
private theorem fall_eq_zero_of_not_le {α β : σ →₀ ℕ} (hαβ : ¬α ≤ β) :
    fall α β = 0 := by
  rw [Finsupp.le_def] at hαβ
  push Not at hαβ
  obtain ⟨i, hi⟩ := hαβ
  unfold fall
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rw [(Nat.descFactorial_eq_zero_iff_lt).mpr hi]
  simp

omit [Fintype τ] in
private theorem eval_glue [Finite τ]
    (P : (σ →₀ ℕ) → MvPolynomial τ ℂ) (κ : (σ →₀ ℕ) → ℝ)
    (β : σ →₀ ℕ) (x : τ ⊕ σ → ℂ) :
    MvPolynomial.eval x (glue P κ β) =
      ∑ α ∈ Finset.Iic β, (κ α : ℂ) *
        MvPolynomial.eval (fun i => x (Sum.inl i)) (P α) *
          ∏ i, x (Sum.inr i) ^ α i := by
  classical
  let _ := Fintype.ofFinite τ
  unfold glue
  simp only [map_sum, MvPolynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro α hα
  rw [MvPolynomial.eval_eq', Finset.mul_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro γ hγ
  rw [Finsupp.prod_fintype _ _ (fun i => pow_zero (x i)), Fintype.prod_sum_type]
  simp only [Finsupp.sumFinsuppEquivProdFinsupp_symm_inl,
    Finsupp.sumFinsuppEquivProdFinsupp_symm_inr]
  ring

omit [Fintype τ] in
private theorem lambdaBar_eq_glue_coeffPoly (β : σ →₀ ℕ)
    (p : MvPolynomial (τ ⊕ σ) ℂ) :
    lambdaBar β p = glue (fun α => MvPolynomial.coeffPoly α p) (fun α => fall α β) β := by
  ext e
  rw [coeff_lambdaBar, coeff_glue]
  let E : (τ ⊕ σ →₀ ℕ) ≃ (τ →₀ ℕ) × (σ →₀ ℕ) :=
    Finsupp.sumFinsuppEquivProdFinsupp
  have he : (E e).1.sumElim (E e).2 = e := by
    change E.symm (E e) = e
    exact E.symm_apply_apply e
  unfold seriesCoeff
  rw [MvPolynomial.coeff_coeffPoly, he]
  by_cases hle : (E e).2 ≤ β
  · simp only [hle, ite_true, E]
  · have hle' : ¬(Finsupp.sumFinsuppEquivProdFinsupp e).2 ≤ β := by
      simpa only [E] using hle
    have hfall : fall (Finsupp.sumFinsuppEquivProdFinsupp e).2 β = 0 := by
      apply fall_eq_zero_of_not_le
      exact hle'
    simp only [hle', ite_false, hfall, Complex.ofReal_zero, zero_mul]

omit [DecidableEq σ] in
private theorem tendstoLocallyUniformly_const_function
    {ι X : Type*} [TopologicalSpace X] (g : X → ℂ) (l : Filter ι) :
    TendstoLocallyUniformly (fun _ : ι => g) g l := by
  intro u hu x
  exact ⟨Set.univ, Filter.univ_mem, Filter.Eventually.of_forall fun _ y _ =>
    refl_mem_uniformity hu⟩

omit [DecidableEq σ] in
private theorem tendstoLocallyUniformly_finset_sum
    {ι X A : Type*} [TopologicalSpace X]
    (s : Finset A) (f : A → ι → X → ℂ) (g : A → X → ℂ) (l : Filter ι)
    (h : ∀ a ∈ s, TendstoLocallyUniformly (f a) (g a) l) :
    TendstoLocallyUniformly (fun n x => ∑ a ∈ s, f a n x)
      (fun x => ∑ a ∈ s, g a x) l := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using tendstoLocallyUniformly_const_function (fun _ : X => 0) l
  | @insert a s has ih =>
      have ha := h a (Finset.mem_insert_self a s)
      have hs := ih fun b hb => h b (Finset.mem_insert_of_mem hb)
      simp only [Finset.sum_insert has]
      change TendstoLocallyUniformly
        ((f a) + fun n x => ∑ b ∈ s, f b n x)
        ((g a) + fun x => ∑ b ∈ s, g b x) l
      exact ha.add hs

/-- Applying `Λbar_β` to approximating polynomials commutes with the explicit locally uniform
series limit.  This is the coefficient-extraction step in Borcea--Brändén,
arXiv:0809.0401, Theorem 5.1. -/
theorem tendstoLocallyUniformly_eval_lambdaBar
    (P : (σ →₀ ℕ) → MvPolynomial τ ℂ) (β : σ →₀ ℕ)
    (F : ℕ → MvPolynomial (τ ⊕ σ) ℂ)
    (hsum : ∀ x : τ ⊕ σ → ℂ,
      Summable fun e : τ ⊕ σ →₀ ℕ => ‖seriesCoeff P e * ∏ i, x i ^ e i‖)
    (hconv : TendstoLocallyUniformly
      (fun k (x : τ ⊕ σ → ℂ) => MvPolynomial.eval x (F k))
      (fun x => ∑' e : τ ⊕ σ →₀ ℕ, seriesCoeff P e * ∏ i, x i ^ e i) atTop) :
    TendstoLocallyUniformly
      (fun k x => MvPolynomial.eval x (lambdaBar β (F k)))
      (fun x => MvPolynomial.eval x (glue P (fun α => fall α β) β)) atTop := by
  let f : (σ →₀ ℕ) → ℕ → (τ ⊕ σ → ℂ) → ℂ := fun α k x =>
    (fall α β : ℂ) *
      MvPolynomial.eval (fun i => x (Sum.inl i)) (MvPolynomial.coeffPoly α (F k)) *
        ∏ i, x (Sum.inr i) ^ α i
  let g : (σ →₀ ℕ) → (τ ⊕ σ → ℂ) → ℂ := fun α x =>
    (fall α β : ℂ) * MvPolynomial.eval (fun i => x (Sum.inl i)) (P α) *
      ∏ i, x (Sum.inr i) ^ α i
  have hterm : ∀ α ∈ Finset.Iic β, TendstoLocallyUniformly (f α) (g α) atTop := by
    intro α hα
    have hc := MvPolynomial.tendstoLocallyUniformly_eval_coeffPoly F P hsum hconv α
    have hleft := hc.comp (fun x : τ ⊕ σ → ℂ => fun i => x (Sum.inl i)) (by fun_prop)
    let q : (τ ⊕ σ → ℂ) → ℂ := fun x =>
      (fall α β : ℂ) * ∏ i, x (Sum.inr i) ^ α i
    have hq := tendstoLocallyUniformly_const_function q (atTop : Filter ℕ)
    have hcontinuousEval : Continuous fun z : τ → ℂ => MvPolynomial.eval z (P α) := by
      simp only [MvPolynomial.eval_eq']
      fun_prop
    have hmul := hq.mul₀ hleft (by fun_prop) (hcontinuousEval.comp (by fun_prop))
    convert hmul using 1
    · funext k x
      simp only [f, q, Pi.mul_apply, Function.comp_apply]
      ring_nf
    · funext x
      simp only [g, q, Pi.mul_apply, Function.comp_apply]
      ring_nf
  have hsumconv := tendstoLocallyUniformly_finset_sum
    (Finset.Iic β) f g atTop hterm
  convert hsumconv using 1
  · funext k x
    rw [lambdaBar_eq_glue_coeffPoly, eval_glue]
  · funext x
    rw [eval_glue]

omit [Fintype τ] [Fintype σ] [DecidableEq σ] in
/-- A locally uniform limit of stable-or-zero multivariate polynomials that is itself a
polynomial is stable or zero.  This packages the stable-or-zero approximation convention with
the Hurwitz theorem in `RealRooted.Mathlib.Analysis.Complex.Hurwitz`. -/
theorem mvUpperHalfPlaneStableOrZero_of_tendstoLocallyUniformly
    {τ σ : Type*} [Finite τ] [Finite σ]
    (p : ℕ → MvPolynomial (τ ⊕ σ) ℂ) (q : MvPolynomial (τ ⊕ σ) ℂ)
    (hp : ∀ k, MvUpperHalfPlaneStableOrZero (p k))
    (hconv : TendstoLocallyUniformly
      (fun k (x : τ ⊕ σ → ℂ) => MvPolynomial.eval x (p k))
      (fun x => MvPolynomial.eval x q) atTop) :
    MvUpperHalfPlaneStableOrZero q := by
  by_cases hzero : ∃ᶠ k in atTop, p k = 0
  · left
    apply MvPolynomial.funext
    intro x
    have heval := hconv.tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ x)
    have hfrequent : ∃ᶠ k in atTop, MvPolynomial.eval x (p k) = 0 :=
      hzero.mono fun k hk => by simp only [hk, map_zero]
    exact tendsto_nhds_unique_of_frequently_eq heval tendsto_const_nhds hfrequent
  · have hnonzero : ∀ᶠ k in atTop, p k ≠ 0 := by
      simpa only [not_frequently] using hzero
    have hstable : ∀ᶠ k in atTop, MvUpperHalfPlaneStable (p k) := by
      filter_upwards [hnonzero] with k hk
      rcases hp k with hkzero | hkstable
      · exact (hk hkzero).elim
      · exact hkstable
    rw [eventually_atTop] at hstable
    obtain ⟨N, hN⟩ := hstable
    have hconvTail : TendstoLocallyUniformly
        (fun k (x : τ ⊕ σ → ℂ) => MvPolynomial.eval x (p (k + N)))
        (fun x => MvPolynomial.eval x q) atTop := by
      intro u hu x
      obtain ⟨s, hs, hlast⟩ := hconv u hu x
      exact ⟨s, hs, (tendsto_add_atTop_nat N).eventually hlast⟩
    have hhurwitz := MvPolynomial.eval_ne_zero_or_eq_zero_of_tendstoLocallyUniformlyOn
      (fun k => p (k + N)) q
      (fun k z hz => hN (k + N) (Nat.le_add_left N k) z hz)
      hconvTail.tendstoLocallyUniformlyOn
    rcases hhurwitz with hstableq | hzeroq
    · right
      intro z hz
      exact hstableq z hz
    · exact Or.inl hzeroq

omit [Fintype τ] in
/-- If the falling-factorial transforms of a stable-limit witness converge locally uniformly to
the corresponding truncation, then that truncation is stable or zero.  Together with coefficient
extraction for locally uniform entire limits, this is the forward implication of
Borcea--Brändén, arXiv:0809.0401, Theorem 5.1. -/
theorem fallingFactorial_glue_stableOrZero_of_lambdaBar_tendstoLocallyUniformly
    {τ : Type*} [Finite τ]
    (P : (σ →₀ ℕ) → MvPolynomial τ ℂ) (β : σ →₀ ℕ)
    (F : ℕ → MvPolynomial (τ ⊕ σ) ℂ)
    (hF : ∀ k, MvUpperHalfPlaneStableOrZero (F k))
    (htransform : TendstoLocallyUniformly
      (fun k (x : τ ⊕ σ → ℂ) => MvPolynomial.eval x (lambdaBar β (F k)))
      (fun x => MvPolynomial.eval x (glue P (fun α => fall α β) β)) atTop) :
    MvUpperHalfPlaneStableOrZero (glue P (fun α => fall α β) β) := by
  apply mvUpperHalfPlaneStableOrZero_of_tendstoLocallyUniformly
    (fun k => lambdaBar β (F k))
  · exact fun k => lambdaBar_stableOrZero β (hF k)
  · exact htransform

/-- Borcea--Brändén, arXiv:0809.0401, Theorem 5.1, reverse implication: stable-or-zero
falling-factorial truncations put the explicit series in the complex stable limit class. -/
theorem isComplexStableLimit_of_forall_fallingFactorial_glue_stableOrZero
    (P : (σ →₀ ℕ) → MvPolynomial τ ℂ)
    (h : ∀ β : σ →₀ ℕ,
      MvUpperHalfPlaneStableOrZero (glue P (fun α => fall α β) β)) :
    IsComplexStableLimit P := by
  obtain ⟨F, hF, hsum, hconv⟩ :=
    exists_stableOrZero_tendstoLocallyUniformly_of_fallingFactorial_glue P fun β => by
      rcases h β with hzero | hstable
      · exact Or.inr hzero
      · exact Or.inl hstable
  exact ⟨F, fun k => (hF k).symm, hsum, hconv⟩

/-- Borcea--Brändén, arXiv:0809.0401, Theorem 5.1, forward implication: every
falling-factorial truncation of a complex stable limit is stable or zero. -/
theorem fallingFactorial_glue_stableOrZero_of_isComplexStableLimit
    (P : (σ →₀ ℕ) → MvPolynomial τ ℂ) (hP : IsComplexStableLimit P)
    (β : σ →₀ ℕ) :
    MvUpperHalfPlaneStableOrZero (glue P (fun α => fall α β) β) := by
  obtain ⟨F, hF, hsum, hconv⟩ := hP
  apply fallingFactorial_glue_stableOrZero_of_lambdaBar_tendstoLocallyUniformly
    P β F hF
  exact tendstoLocallyUniformly_eval_lambdaBar P β F hsum hconv

/-- **Borcea--Brändén, arXiv:0809.0401, Theorem 5.1 (complex case).**
The explicit series belongs to the complex stable-limit class if and only if every
falling-factorial truncation is upper-half-plane stable or zero. -/
theorem isComplexStableLimit_iff_forall_fallingFactorial_glue_stableOrZero
    (P : (σ →₀ ℕ) → MvPolynomial τ ℂ) :
    IsComplexStableLimit P ↔
      ∀ β : σ →₀ ℕ,
        MvUpperHalfPlaneStableOrZero (glue P (fun α => fall α β) β) := by
  constructor
  · exact fun hP β => fallingFactorial_glue_stableOrZero_of_isComplexStableLimit P hP β
  · exact isComplexStableLimit_of_forall_fallingFactorial_glue_stableOrZero P

end RealRooted.BorceaBranden
