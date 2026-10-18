/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/
import RealRooted.Mathlib.Analysis.Complex.Polynomial.CoeffEstimates

/-!
# Coefficient extraction under locally uniform convergence of polynomials

If multivariate complex polynomials `p k` converge locally uniformly to an everywhere absolutely
convergent power series, then each coefficient `(p k).coeff m` converges to the corresponding
series coefficient. We apply this to polynomials in split variables `(z, w)`: extracting the
coefficient of `w ^ α` commutes with the limit, so the resulting polynomials in `z` converge
locally uniformly to the corresponding coefficient polynomial of the limit. This is the
coefficient-extraction step in Borcea-Brändén, arXiv:0809.0401, Theorem 5.1.

## Main definitions

* `MvPolynomial.coeffPoly`: the polynomial in the left variables `z` obtained by extracting the
  coefficient of `w ^ α` from a polynomial in `MvPolynomial (τ ⊕ σ) ℂ`.
* `MvPolynomial.rightSlice`: a split polynomial viewed as a polynomial in the right variables
  after fixing the left variables.

## Main statements

* `MvPolynomial.tendsto_coeff_of_tendstoLocallyUniformly_tsum`: locally uniform convergence to a
  power series with coefficients `c` gives `(p k).coeff m → c m` for every `m`.
* `MvPolynomial.coeff_coeffPoly`: `(coeffPoly α p).coeff γ = p.coeff (γ.sumElim α)`.
* `MvPolynomial.eval_rightSlice`: evaluating `rightSlice z p` at `w` is evaluating `p` at
  `Sum.elim z w`.
* `MvPolynomial.tendstoLocallyUniformly_eval_coeffPoly`: if split polynomials `p k` converge
  locally uniformly to `∑ P_α(z) w ^ α`, then `coeffPoly α (p k)` converges locally uniformly
  to `P α`.
-/

open Filter Topology
open scoped BigOperators

noncomputable section

namespace MvPolynomial

variable {τ σ : Type*} [Fintype τ] [Fintype σ]

/-- Locally uniform convergence to an everywhere absolutely convergent multivariate power
series identifies every polynomial coefficient. -/
theorem tendsto_coeff_of_tendstoLocallyUniformly_tsum
    (p : ℕ → MvPolynomial τ ℂ) (c : (τ →₀ ℕ) → ℂ)
    (hsum : ∀ x : τ → ℂ,
      Summable fun e : τ →₀ ℕ => ‖c e * ∏ i, x i ^ e i‖)
    (hconv : TendstoLocallyUniformly
      (fun k (x : τ → ℂ) => MvPolynomial.eval x (p k))
      (fun x => ∑' e : τ →₀ ℕ, c e * ∏ i, x i ^ e i) atTop)
    (m : τ →₀ ℕ) :
    Tendsto (fun k => (p k).coeff m) atTop (𝓝 (c m)) := by
  classical
  rw [Metric.tendsto_atTop]
  intro ε hε
  let K : Set (τ → ℂ) := Metric.closedBall 0 1
  have hK : IsCompact K := isCompact_closedBall 0 1
  have hc : Summable fun e : τ →₀ ℕ => ‖c e‖ := by
    simpa using hsum (fun _ => 1)
  have hterm : ∀ e (x : τ → ℂ), x ∈ K →
      ‖c e * ∏ i, x i ^ e i‖ ≤ ‖c e‖ := by
    intro e x hx
    have hxnorm : ‖x‖ ≤ 1 := by
      simpa only [K, Metric.mem_closedBall, dist_zero_right] using hx
    have hxi : ∀ i, ‖x i‖ ≤ 1 := fun i => (norm_le_pi_norm x i).trans hxnorm
    rw [norm_mul, norm_prod]
    have hp : ∏ i, ‖x i ^ e i‖ ≤ 1 := by
      calc
        ∏ i, ‖x i ^ e i‖ ≤ ∏ _i : τ, (1 : ℝ) := by
          gcongr with i
          rw [norm_pow]
          exact pow_le_one₀ (norm_nonneg _) (hxi i)
        _ = 1 := by simp
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (norm_nonneg (c e))
  have hseries : TendstoUniformlyOn
      (fun s : Finset (τ →₀ ℕ) => fun x =>
        ∑ e ∈ s, c e * ∏ i, x i ^ e i)
      (fun x => ∑' e : τ →₀ ℕ, c e * ∏ i, x i ^ e i) atTop K :=
    tendstoUniformlyOn_tsum hc hterm
  have hpconv :=
    (tendstoLocallyUniformly_iff_forall_isCompact.mp hconv K hK)
  have hpε := (Metric.tendstoUniformlyOn_iff.mp hpconv (ε / 4) (by positivity))
  have hsε := (Metric.tendstoUniformlyOn_iff.mp hseries (ε / 4) (by positivity))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hpε
  obtain ⟨s, hs⟩ := eventually_atTop.1 hsε
  refine ⟨N, fun k hkN => ?_⟩
  have hk := hN k hkN
  let q : MvPolynomial τ ℂ := ∑ e ∈ s ∪ {m}, MvPolynomial.monomial e (c e)
  have hqeval : ∀ x : τ → ℂ,
      MvPolynomial.eval x q = ∑ e ∈ s ∪ {m}, c e * ∏ i, x i ^ e i := by
    intro x
    simp only [q, map_sum, MvPolynomial.eval_monomial]
    simp_rw [Finsupp.prod_fintype _ _ (fun i => pow_zero (x i))]
  have hqcoeff : q.coeff m = c m := by
    simp only [q, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    simp
  have hbound : ∀ x : τ → ℂ, (∀ i, ‖x i‖ = 1) →
      ‖MvPolynomial.eval x (p k - q)‖ ≤ ε / 2 := by
    intro x hx
    have hxK : x ∈ K := by
      change x ∈ Metric.closedBall 0 1
      rw [Metric.mem_closedBall, dist_zero_right]
      rw [pi_norm_le_iff_of_nonneg (by norm_num)]
      exact fun i => (hx i).le
    have hkx := hk x hxK
    have hsx := hs (s ∪ {m}) (Finset.subset_union_left) x hxK
    rw [dist_eq_norm] at hkx
    have hsx' : ‖(∑' e : τ →₀ ℕ, c e * ∏ i, x i ^ e i) -
        MvPolynomial.eval x q‖ < ε / 4 := by
      rw [hqeval]
      simpa only [dist_eq_norm] using hsx
    rw [MvPolynomial.eval_sub]
    exact (calc
      ‖MvPolynomial.eval x (p k) - MvPolynomial.eval x q‖ =
          ‖(MvPolynomial.eval x (p k) -
              ∑' e : τ →₀ ℕ, c e * ∏ i, x i ^ e i) +
            ((∑' e : τ →₀ ℕ, c e * ∏ i, x i ^ e i) -
              MvPolynomial.eval x q)‖ := by abel_nf
      _ ≤
          ‖MvPolynomial.eval x (p k) -
            ∑' e : τ →₀ ℕ, c e * ∏ i, x i ^ e i‖ +
          ‖(∑' e : τ →₀ ℕ, c e * ∏ i, x i ^ e i) -
            MvPolynomial.eval x q‖ := norm_add_le _ _
      _ < ε / 4 + ε / 4 := add_lt_add (by simpa [norm_sub_rev] using hkx) hsx'
      _ = ε / 2 := by ring).le
  have hcoeff := norm_coeff_mul_pow_le_of_forall_norm_eval_le
    (p k - q) (by norm_num : (0 : ℝ) < 1) hbound m
  rw [MvPolynomial.coeff_sub, hqcoeff, one_pow, mul_one] at hcoeff
  simpa only [dist_eq_norm] using lt_of_le_of_lt hcoeff (half_lt_self hε)

private theorem sumAlgEquiv_monomial
    {S₁ S₂ R : Type*} [CommSemiring R]
    (a : S₁ →₀ ℕ) (b : S₂ →₀ ℕ) (r : R) :
    MvPolynomial.sumAlgEquiv R S₁ S₂
        (MvPolynomial.monomial (a.sumElim b) r) =
      MvPolynomial.monomial a (MvPolynomial.monomial b r) := by
  classical
  rw [MvPolynomial.monomial_eq, MvPolynomial.monomial_eq,
    MvPolynomial.monomial_eq, Finsupp.prod_sumElim]
  simp only [map_mul, MvPolynomial.sumAlgEquiv_C_inl]
  simp [Finsupp.prod]
  simp only [← map_pow, ← map_prod]
  simp only [MvPolynomial.prod_X_pow_eq_monomial]
  ring

private theorem coeff_coeff_sumAlgEquiv
    {S₁ S₂ R : Type*} [CommSemiring R]
    (p : MvPolynomial (S₁ ⊕ S₂) R)
    (a : S₁ →₀ ℕ) (b : S₂ →₀ ℕ) :
    ((MvPolynomial.sumAlgEquiv R S₁ S₂ p).coeff a).coeff b =
      p.coeff (a.sumElim b) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
      simp [hp, hq]
  | monomial d r =>
      let d₁ : S₁ →₀ ℕ :=
        Finsupp.comapDomain Sum.inl d Sum.inl_injective.injOn
      let d₂ : S₂ →₀ ℕ :=
        Finsupp.comapDomain Sum.inr d Sum.inr_injective.injOn
      have hd : d₁.sumElim d₂ = d :=
        Finsupp.comapDomain_sumElim_comapDomain d
      rw [← hd, sumAlgEquiv_monomial]
      have hsum : d₁.sumElim d₂ = a.sumElim b ↔ d₁ = a ∧ d₂ = b := by
        constructor
        · intro h
          constructor
          · ext i
            exact DFunLike.congr_fun h (Sum.inl i)
          · ext i
            exact DFunLike.congr_fun h (Sum.inr i)
        · rintro ⟨rfl, rfl⟩
          rfl
      by_cases hda : d₁ = a
      · have hright : a.sumElim d₂ = a.sumElim b ↔ d₂ = b := by
          constructor
          · intro h
            ext i
            exact DFunLike.congr_fun h (Sum.inr i)
          · rintro rfl
            rfl
        simp [MvPolynomial.coeff_monomial, hda, hright]
      · simp [MvPolynomial.coeff_monomial, hsum, hda]

/-- The polynomial in the left variables obtained by extracting the coefficient of `w^α`
from a polynomial in split variables `(z, w)`. -/
def coeffPoly (α : σ →₀ ℕ) (p : MvPolynomial (τ ⊕ σ) ℂ) : MvPolynomial τ ℂ :=
  (MvPolynomial.sumAlgEquiv ℂ σ τ
    (MvPolynomial.rename (Equiv.sumComm τ σ) p)).coeff α

omit [Fintype τ] [Fintype σ] in
/-- Coefficients of `coeffPoly` are the corresponding split coefficients. -/
theorem coeff_coeffPoly (α : σ →₀ ℕ) (p : MvPolynomial (τ ⊕ σ) ℂ)
    (γ : τ →₀ ℕ) :
    (coeffPoly α p).coeff γ = p.coeff (γ.sumElim α) := by
  classical
  unfold coeffPoly
  rw [coeff_coeff_sumAlgEquiv]
  have hmap :
      (γ.sumElim α).mapDomain (Equiv.sumComm τ σ) = α.sumElim γ := by
    ext i
    rcases i with i | i
    · simp
    · simp
  rw [← hmap, MvPolynomial.coeff_rename_mapDomain
    (Equiv.sumComm τ σ) (Equiv.sumComm τ σ).injective]

/-- Regard a split polynomial as a polynomial in its right variables after fixing the left
variables. -/
def rightSlice (z : τ → ℂ) (p : MvPolynomial (τ ⊕ σ) ℂ) : MvPolynomial σ ℂ :=
  MvPolynomial.map (MvPolynomial.eval z)
    (MvPolynomial.sumAlgEquiv ℂ σ τ
      (MvPolynomial.rename (Equiv.sumComm τ σ) p))

omit [Fintype τ] [Fintype σ] in
/-- Extracting a right coefficient after fixing the left variables evaluates `coeffPoly`. -/
theorem coeff_rightSlice (z : τ → ℂ) (p : MvPolynomial (τ ⊕ σ) ℂ)
    (α : σ →₀ ℕ) :
    (rightSlice z p).coeff α = MvPolynomial.eval z (coeffPoly α p) := by
  unfold rightSlice coeffPoly
  rw [MvPolynomial.coeff_map]

omit [Fintype τ] [Fintype σ] in
/-- Evaluation of a right slice is evaluation at the combined point. -/
theorem eval_rightSlice (z : τ → ℂ) (w : σ → ℂ)
    (p : MvPolynomial (τ ⊕ σ) ℂ) :
    MvPolynomial.eval w (rightSlice z p) =
      MvPolynomial.eval (Sum.elim z w) p := by
  classical
  unfold rightSlice
  rw [MvPolynomial.eval_map]
  change
    (((MvPolynomial.eval₂Hom (MvPolynomial.eval z) w).comp
      ((MvPolynomial.sumAlgEquiv ℂ σ τ).toRingEquiv.toRingHom.comp
        (MvPolynomial.rename (Equiv.sumComm τ σ)).toRingHom)) p) =
      MvPolynomial.eval (Sum.elim z w) p
  congr 1
  ext i
  case hC => simp
  case hX =>
    rcases i with i | i
    · simp [Equiv.sumComm_apply]
    · simp [Equiv.sumComm_apply]

private theorem exists_eval_bound_of_tendstoLocallyUniformly_tsum
    (p : ℕ → MvPolynomial τ ℂ) (c : (τ →₀ ℕ) → ℂ)
    (hsum : ∀ x : τ → ℂ,
      Summable fun e : τ →₀ ℕ => ‖c e * ∏ i, x i ^ e i‖)
    (hconv : TendstoLocallyUniformly
      (fun k (x : τ → ℂ) => MvPolynomial.eval x (p k))
      (fun x => ∑' e : τ →₀ ℕ, c e * ∏ i, x i ^ e i) atTop)
    (r : ℝ) (hr : 0 < r) :
    ∃ K : ℝ, ∀ k (x : τ → ℂ), (∀ i, ‖x i‖ ≤ r) →
      ‖MvPolynomial.eval x (p k)‖ ≤ K := by
  classical
  let D : Set (τ → ℂ) := Metric.closedBall 0 r
  have hD : IsCompact D := isCompact_closedBall 0 r
  have hconvD := tendstoLocallyUniformly_iff_forall_isCompact.mp hconv D hD
  have hevent := Metric.tendstoUniformlyOn_iff.mp hconvD 1 (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  let u : (τ →₀ ℕ) → ℝ := fun e => ‖c e * ∏ _i : τ, (r : ℂ) ^ e _i‖
  have hu : Summable u := hsum (fun _ => r)
  let M : ℝ := ∑' e, u e
  let A : ℝ := ∑ k ∈ Finset.range N, ∑ e ∈ (p k).support,
    ‖(p k).coeff e‖ * r ^ (∑ i, e i)
  refine ⟨A + M + 1, fun k x hx => ?_⟩
  have hxD : x ∈ D := by
    change x ∈ Metric.closedBall 0 r
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hr.le]
    exact hx
  have hmono : ∀ e : τ →₀ ℕ,
      ‖c e * ∏ i, x i ^ e i‖ ≤ u e := by
    intro e
    rw [norm_mul, norm_prod]
    change ‖c e‖ * ∏ i, ‖x i ^ e i‖ ≤
      ‖c e * ∏ _i : τ, (r : ℂ) ^ e _i‖
    rw [norm_mul, norm_prod]
    gcongr with i
    rw [norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    exact pow_le_pow_left₀ (norm_nonneg _) (hx i) _
  have hlimit :
      ‖∑' e : τ →₀ ℕ, c e * ∏ i, x i ^ e i‖ ≤ M := by
    have hnorm := norm_tsum_le_tsum_norm (hsum x)
    have hle := Summable.tsum_le_tsum hmono (hsum x) hu
    exact hnorm.trans hle
  by_cases hk : N ≤ k
  · have hclose := hN k hk x hxD
    rw [dist_eq_norm] at hclose
    calc
      ‖MvPolynomial.eval x (p k)‖ ≤
          ‖∑' e : τ →₀ ℕ, c e * ∏ i, x i ^ e i‖ +
            ‖(∑' e : τ →₀ ℕ, c e * ∏ i, x i ^ e i) -
              MvPolynomial.eval x (p k)‖ := by
        have hadd := norm_add_le
          (∑' e : τ →₀ ℕ, c e * ∏ i, x i ^ e i)
          (MvPolynomial.eval x (p k) -
            ∑' e : τ →₀ ℕ, c e * ∏ i, x i ^ e i)
        have heq :
            (∑' e : τ →₀ ℕ, c e * ∏ i, x i ^ e i) +
                (MvPolynomial.eval x (p k) -
                  ∑' e : τ →₀ ℕ, c e * ∏ i, x i ^ e i) =
              MvPolynomial.eval x (p k) := by abel_nf
        rw [heq, norm_sub_rev] at hadd
        exact hadd
      _ ≤ M + 1 := add_le_add hlimit hclose.le
      _ ≤ A + M + 1 := by
        have hA : 0 ≤ A := Finset.sum_nonneg fun j _ =>
          Finset.sum_nonneg fun e _ => mul_nonneg (norm_nonneg _) (pow_nonneg hr.le _)
        linarith
  · have hkN : k ∈ Finset.range N := Finset.mem_range.mpr (by lia)
    rw [MvPolynomial.eval_eq']
    calc
      ‖∑ e ∈ (p k).support, (p k).coeff e * ∏ i, x i ^ e i‖ ≤
          ∑ e ∈ (p k).support, ‖(p k).coeff e‖ * r ^ (∑ i, e i) := by
        calc
          _ ≤ ∑ e ∈ (p k).support,
              ‖(p k).coeff e * ∏ i, x i ^ e i‖ := norm_sum_le _ _
          _ ≤ _ := Finset.sum_le_sum fun e _ => by
            rw [norm_mul, norm_prod, ← Finset.prod_pow_eq_pow_sum]
            gcongr with i
            rw [norm_pow]
            exact pow_le_pow_left₀ (norm_nonneg _) (hx i) _
      _ ≤ A := by
        dsimp only [A]
        exact Finset.single_le_sum
          (s := Finset.range N)
          (f := fun j => ∑ e ∈ (p j).support,
            ‖(p j).coeff e‖ * r ^ (∑ i, e i))
          (fun j _ => Finset.sum_nonneg fun e _ =>
            mul_nonneg (norm_nonneg ((p j).coeff e))
              (pow_nonneg hr.le (∑ i, e i))) hkN
      _ ≤ A + M + 1 := by
        have hM : 0 ≤ M := by
          dsimp only [M, u]
          exact tsum_nonneg fun e => norm_nonneg _
        linarith

/-- If split polynomials converge locally uniformly to the explicit series
`∑_α P_α(z)w^α`, then their `w^α` coefficient polynomials converge locally uniformly to
`P_α`.  This is the coefficient-extraction step in Borcea--Brändén,
arXiv:0809.0401, Theorem 5.1. -/
theorem tendstoLocallyUniformly_eval_coeffPoly
    (p : ℕ → MvPolynomial (τ ⊕ σ) ℂ)
    (P : (σ →₀ ℕ) → MvPolynomial τ ℂ)
    (hsum : ∀ x : τ ⊕ σ → ℂ, Summable fun e : τ ⊕ σ →₀ ℕ =>
      ‖(P (Finsupp.sumFinsuppEquivProdFinsupp e).2).coeff
          (Finsupp.sumFinsuppEquivProdFinsupp e).1 * ∏ i, x i ^ e i‖)
    (hconv : TendstoLocallyUniformly
      (fun k (x : τ ⊕ σ → ℂ) => MvPolynomial.eval x (p k))
      (fun x => ∑' e : τ ⊕ σ →₀ ℕ,
        (P (Finsupp.sumFinsuppEquivProdFinsupp e).2).coeff
          (Finsupp.sumFinsuppEquivProdFinsupp e).1 * ∏ i, x i ^ e i) atTop)
    (α : σ →₀ ℕ) :
    TendstoLocallyUniformly
      (fun k z => MvPolynomial.eval z (coeffPoly α (p k)))
      (fun z => MvPolynomial.eval z (P α)) atTop := by
  let c : (τ ⊕ σ →₀ ℕ) → ℂ := fun e =>
    (P (Finsupp.sumFinsuppEquivProdFinsupp e).2).coeff
      (Finsupp.sumFinsuppEquivProdFinsupp e).1
  have hcoef : ∀ γ : τ →₀ ℕ,
      Tendsto (fun k => (coeffPoly α (p k)).coeff γ) atTop
        (𝓝 ((P α).coeff γ)) := by
    intro γ
    have hc : c (γ.sumElim α) = (P α).coeff γ := by
      change
        (P (Finsupp.sumFinsuppEquivProdFinsupp (γ.sumElim α)).2).coeff
          (Finsupp.sumFinsuppEquivProdFinsupp (γ.sumElim α)).1 = _
      rw [show γ.sumElim α =
        Finsupp.sumFinsuppEquivProdFinsupp.symm (γ, α) from rfl,
        Equiv.apply_symm_apply]
    rw [← hc]
    simpa only [coeff_coeffPoly] using
      tendsto_coeff_of_tendstoLocallyUniformly_tsum p c hsum hconv (γ.sumElim α)
  have hbound : ∀ r : ℝ, 0 < r → ∃ K : ℝ, ∀ k (z : τ → ℂ),
      (∀ i, ‖z i‖ ≤ r) → ‖MvPolynomial.eval z (coeffPoly α (p k))‖ ≤ K := by
    intro r hr
    obtain ⟨K, hK⟩ := exists_eval_bound_of_tendstoLocallyUniformly_tsum p c hsum hconv
      (max r 1) (lt_of_lt_of_le zero_lt_one (le_max_right r 1))
    refine ⟨K, fun k z hz => ?_⟩
    have hs : ∀ w : σ → ℂ, (∀ i, ‖w i‖ = 1) →
        ‖MvPolynomial.eval w (rightSlice z (p k))‖ ≤ K := by
      intro w hw
      rw [eval_rightSlice]
      apply hK
      rintro (i | i)
      · exact (hz i).trans (le_max_left r 1)
      · exact (hw i).le.trans (le_max_right r 1)
    have hcauchy := norm_coeff_mul_pow_le_of_forall_norm_eval_le
      (rightSlice z (p k)) (by norm_num : (0 : ℝ) < 1) hs α
    rw [coeff_rightSlice, one_pow, mul_one] at hcauchy
    exact hcauchy
  obtain ⟨_, hlocal⟩ := tendstoLocallyUniformly_of_bounded_of_coeff_tendsto
    (fun k => coeffPoly α (p k)) (fun γ => (P α).coeff γ) hbound hcoef
  have heval : ∀ z : τ → ℂ,
      HasSum (fun γ : τ →₀ ℕ => (P α).coeff γ * ∏ i, z i ^ γ i)
        (MvPolynomial.eval z (P α)) := by
    intro z
    rw [MvPolynomial.eval_eq']
    apply hasSum_sum_of_ne_finset_zero
    intro γ hγ
    rw [MvPolynomial.notMem_support_iff.mp hγ, zero_mul]
  convert hlocal using 1
  funext z
  exact (heval z).tsum_eq.symm

end MvPolynomial
