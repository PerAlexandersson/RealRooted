module

public import Mathlib

public section

open Complex Filter Topology

noncomputable section

namespace MvPolynomial

private lemma exp_eq_pow (k N : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) / N) =
      Complex.exp (2 * Real.pi * Complex.I / N) ^ k := by
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

private lemma geom_char_sum {ω r : ℂ} {N : ℕ} (hω : IsPrimitiveRoot ω N) (hr : r ≠ 0)
    {a b : ℕ} (ha : a < N) (hb : b < N) :
    ∑ j : Fin N, (r * ω ^ (j : ℕ)) ^ a * ((r * ω ^ (j : ℕ)) ^ b)⁻¹ =
      if a = b then (N : ℂ) else 0 := by
  have hN : N ≠ 0 := by lia
  have hω0 : ω ≠ 0 := hω.ne_zero hN
  split_ifs with hab
  · subst hab
    have h : ∀ j : Fin N,
        (r * ω ^ (j : ℕ)) ^ a * ((r * ω ^ (j : ℕ)) ^ a)⁻¹ = 1 := fun j =>
      mul_inv_cancel₀ (pow_ne_zero _ (mul_ne_zero hr (pow_ne_zero _ hω0)))
    simp [h]
  · set u := ω ^ a * (ω ^ b)⁻¹ with hu
    have hterm : ∀ j : ℕ, (r * ω ^ j) ^ a * ((r * ω ^ j) ^ b)⁻¹ =
        r ^ a * (r ^ b)⁻¹ * u ^ j := by
      intro j
      rw [hu, mul_pow, mul_pow, mul_pow, mul_inv, inv_pow, ← pow_mul, ← pow_mul, ← pow_mul,
        ← pow_mul, mul_comm j a, mul_comm j b]
      ring
    rw [Fin.sum_univ_eq_sum_range (fun j => (r * ω ^ j) ^ a * ((r * ω ^ j) ^ b)⁻¹) N]
    simp_rw [hterm, ← Finset.mul_sum]
    have hu1 : u ≠ 1 := by
      intro h
      rw [hu, mul_inv_eq_one₀ (pow_ne_zero _ hω0)] at h
      exact hab (hω.pow_inj ha hb h)
    rw [geom_sum_eq hu1, hu, mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm a N,
      mul_comm b N, pow_mul, pow_mul, hω.pow_eq_one]
    simp

private lemma char_sum {τ : Type*} [Fintype τ] [DecidableEq τ] {ω r : ℂ} {N : ℕ}
    (hω : IsPrimitiveRoot ω N) (hr : r ≠ 0) (α m : τ →₀ ℕ) (hα : ∀ i, α i < N)
    (hm : ∀ i, m i < N) :
    ∑ f : τ → Fin N, (∏ i, (r * ω ^ (f i : ℕ)) ^ α i) *
        (∏ i, (r * ω ^ (f i : ℕ)) ^ m i)⁻¹ =
      if α = m then (N : ℂ) ^ Fintype.card τ else 0 := by
  simp_rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (j : Fin N) =>
    (r * ω ^ (j : ℕ)) ^ α i * ((r * ω ^ (j : ℕ)) ^ m i)⁻¹)]
  simp_rw [geom_char_sum hω hr (hα _) (hm _)]
  split_ifs with h
  · subst h
    simp
  · obtain ⟨i, hi⟩ : ∃ i, α i ≠ m i := by
      by_contra hc
      push Not at hc
      exact h (Finsupp.ext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- A multivariate polynomial coefficient is its average on a product of sufficiently many
roots of unity, after the usual monomial correction. -/
theorem coeff_eq_rootOfUnity_avg {τ : Type*} [Fintype τ] [DecidableEq τ]
    (P : MvPolynomial τ ℂ)
    {r : ℝ} (hr : 0 < r) {N : ℕ} (hN : P.totalDegree < N) (m : τ →₀ ℕ)
    (hm : ∀ i, m i < N) :
    P.coeff m = ((N : ℂ) ^ Fintype.card τ)⁻¹ *
      ∑ f : τ → Fin N,
        MvPolynomial.eval (fun i => (r : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * (f i : ℕ) / N)) P *
          (∏ i, ((r : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (f i : ℕ) / N)) ^
            (m i))⁻¹ := by
  have hN0 : N ≠ 0 := by lia
  have hω := Complex.isPrimitiveRoot_exp N hN0
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  simp_rw [exp_eq_pow]
  set ω := Complex.exp (2 * Real.pi * Complex.I / N) with hωdef
  simp_rw [MvPolynomial.eval_eq', Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun α hα => by
    rw [char_sum hω hr0 α m (fun i => lt_of_le_of_lt
      ((MvPolynomial.monomial_le_degreeOf i hα).trans
        (MvPolynomial.degreeOf_le_totalDegree _ _)) hN) hm])]
  simp_rw [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  have hc : (N : ℂ) ^ Fintype.card τ ≠ 0 := pow_ne_zero _ (by exact_mod_cast hN0)
  split_ifs with h
  · field_simp
  · simpa using h

/-- A polynomial coefficient times the corresponding power of a torus radius is at most the
supremum norm of the polynomial on that torus. -/
theorem norm_coeff_mul_pow_le_of_forall_norm_eval_le {τ : Type*} [Fintype τ]
    (P : MvPolynomial τ ℂ) {r : ℝ} (hr : 0 < r) {M : ℝ}
    (hM : ∀ z : τ → ℂ, (∀ i, ‖z i‖ = r) → ‖MvPolynomial.eval z P‖ ≤ M)
    (m : τ →₀ ℕ) : ‖P.coeff m‖ * r ^ (∑ i, m i) ≤ M := by
  classical
  by_cases hmem : m ∈ P.support
  · set N := P.totalDegree + 1 with hNdef
    have hN : P.totalDegree < N := Nat.lt_succ_self _
    have hN0 : N ≠ 0 := by lia
    have hω := Complex.isPrimitiveRoot_exp N hN0
    have hmN : ∀ i, m i < N := fun i => lt_of_le_of_lt
      ((MvPolynomial.monomial_le_degreeOf i hmem).trans
        (MvPolynomial.degreeOf_le_totalDegree _ _)) hN
    have hz : ∀ (f : τ → Fin N) i,
        ‖(r : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((f i : ℕ) : ℂ) / N)‖ = r := by
      intro f i
      rw [exp_eq_pow, norm_mul, norm_pow, hω.norm'_eq_one hN0]
      simp [abs_of_pos hr]
    have hs : 0 < r ^ (∑ i, m i) := pow_pos hr _
    have hterm : ∀ f : τ → Fin N,
        ‖MvPolynomial.eval (fun i => (r : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * (f i : ℕ) / N)) P *
          (∏ i, ((r : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (f i : ℕ) / N)) ^
            (m i))⁻¹‖ ≤ M * (r ^ (∑ i, m i))⁻¹ := by
      intro f
      rw [norm_mul, norm_inv, norm_prod]
      simp_rw [norm_pow, hz f]
      rw [Finset.prod_pow_eq_pow_sum]
      exact mul_le_mul_of_nonneg_right (hM _ (hz f)) (inv_nonneg.mpr hs.le)
    rw [coeff_eq_rootOfUnity_avg P hr hN m hmN, norm_mul, norm_inv, norm_pow,
      Complex.norm_natCast]
    have hc : (0 : ℝ) < (N : ℝ) ^ Fintype.card τ :=
      pow_pos (by exact_mod_cast Nat.pos_of_ne_zero hN0) _
    calc
      ((N : ℝ) ^ Fintype.card τ)⁻¹ * ‖∑ f : τ → Fin N, _‖ * r ^ (∑ i, m i) ≤
          ((N : ℝ) ^ Fintype.card τ)⁻¹ *
              (∑ f : τ → Fin N, M * (r ^ (∑ i, m i))⁻¹) * r ^ (∑ i, m i) := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun f _ => hterm f)
      _ = M := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          nsmul_eq_mul]
        push_cast
        field_simp
  · rw [MvPolynomial.notMem_support_iff.mp hmem, norm_zero, zero_mul]
    exact (norm_nonneg _).trans (hM (fun _ => r) (by simp [abs_of_pos hr]))

private lemma summable_half_pi {τ : Type*} [Fintype τ] :
    Summable fun x : τ → ℕ => ∏ i, (1 / 2 : ℝ) ^ (x i) := by
  classical
  refine summable_of_sum_le (c := 2 ^ Fintype.card τ)
    (fun x => Finset.prod_nonneg fun i _ => by positivity) ?_
  intro S
  set N := S.sup (fun x => Finset.univ.sup x) + 1
  have hsub : S ⊆ Fintype.piFinset (fun _ : τ => Finset.range N) := by
    intro x hx
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range]
    have h1 : x i ≤ Finset.univ.sup x := Finset.le_sup (Finset.mem_univ i)
    have h2 : Finset.univ.sup x ≤ S.sup (fun x => Finset.univ.sup x) :=
      Finset.le_sup (f := fun x => Finset.univ.sup x) hx
    lia
  calc
    ∑ x ∈ S, ∏ i, (1 / 2 : ℝ) ^ (x i) ≤
        ∑ x ∈ Fintype.piFinset (fun _ : τ => Finset.range N), ∏ i, (1 / 2 : ℝ) ^ (x i) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun x _ _ => Finset.prod_nonneg fun i _ => by positivity)
    _ = ∏ _i : τ, ∑ j ∈ Finset.range N, (1 / 2 : ℝ) ^ j := (Finset.prod_univ_sum _ _).symm
    _ ≤ ∏ _i : τ, (2 : ℝ) :=
      Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun j _ => by positivity)
        (fun i _ => sum_geometric_two_le N)
    _ = 2 ^ Fintype.card τ := by simp

private lemma summable_half {τ : Type*} [Fintype τ] :
    Summable fun m : τ →₀ ℕ => (1 / 2 : ℝ) ^ (∑ i, m i) := by
  have h := (Finsupp.equivFunOnFinite (α := τ) (M := ℕ)).summable_iff.mpr
    (summable_half_pi (τ := τ))
  refine h.congr fun m => ?_
  simp [Finset.prod_pow_eq_pow_sum]

private lemma norm_mono_le {τ : Type*} [Fintype τ] (z : τ → ℂ) {R : ℝ}
    (hz : ∀ i, ‖z i‖ ≤ R) (m : τ →₀ ℕ) :
    ‖∏ i, z i ^ m i‖ ≤ R ^ (∑ i, m i) := by
  rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
    (fun i _ => by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hz i) _)

private lemma coeff_bound {τ : Type*} [Fintype τ] (p : ℕ → MvPolynomial τ ℂ)
    (c : (τ →₀ ℕ) → ℂ)
    (hcoef : ∀ m, Tendsto (fun k => (p k).coeff m) atTop (𝓝 (c m)))
    {r K : ℝ} (hr : 0 < r)
    (hK : ∀ k (z : τ → ℂ), (∀ i, ‖z i‖ ≤ r) →
      ‖MvPolynomial.eval z (p k)‖ ≤ K)
    (m : τ →₀ ℕ) :
    (∀ k, ‖(p k).coeff m‖ * r ^ (∑ i, m i) ≤ K) ∧
      ‖c m‖ * r ^ (∑ i, m i) ≤ K := by
  have h1 : ∀ k, ‖(p k).coeff m‖ * r ^ (∑ i, m i) ≤ K := fun k =>
    norm_coeff_mul_pow_le_of_forall_norm_eval_le (p k) hr
      (fun z hz => hK k z (fun i => (hz i).le)) m
  refine ⟨h1, ?_⟩
  have ht : Tendsto (fun k => ‖(p k).coeff m‖ * r ^ (∑ i, m i)) atTop
      (𝓝 (‖c m‖ * r ^ (∑ i, m i))) := ((hcoef m).norm).mul_const _
  exact le_of_tendsto' ht h1

private lemma term_bound {τ : Type*} [Fintype τ] {a : ℂ} {R K : ℝ} (z : τ → ℂ)
    (hz : ∀ i, ‖z i‖ ≤ R) (m : τ →₀ ℕ)
    (ha : ‖a‖ * (2 * R) ^ (∑ i, m i) ≤ K) :
    ‖a * ∏ i, z i ^ m i‖ ≤ K * (1 / 2) ^ (∑ i, m i) := by
  rw [norm_mul]
  calc
    ‖a‖ * ‖∏ i, z i ^ m i‖ ≤ ‖a‖ * R ^ (∑ i, m i) :=
      mul_le_mul_of_nonneg_left (norm_mono_le z hz m) (norm_nonneg _)
    _ = ‖a‖ * (2 * R) ^ (∑ i, m i) * (1 / 2) ^ (∑ i, m i) := by
      rw [mul_assoc, ← mul_pow]
      congr 2
      ring
    _ ≤ K * (1 / 2) ^ (∑ i, m i) :=
      mul_le_mul_of_nonneg_right ha (by positivity)

/-- Uniformly bounded multivariate polynomials whose coefficients converge converge locally
uniformly to their coefficientwise power series. -/
theorem tendstoLocallyUniformly_of_bounded_of_coeff_tendsto {τ : Type*} [Fintype τ]
    (p : ℕ → MvPolynomial τ ℂ) (c : (τ →₀ ℕ) → ℂ)
    (hbound : ∀ r : ℝ, 0 < r → ∃ K : ℝ, ∀ k (z : τ → ℂ),
      (∀ i, ‖z i‖ ≤ r) →
      ‖MvPolynomial.eval z (p k)‖ ≤ K)
    (hcoef : ∀ m, Tendsto (fun k => (p k).coeff m) atTop (𝓝 (c m))) :
    (∀ z : τ → ℂ, Summable fun m : τ →₀ ℕ => ‖c m * ∏ i, z i ^ (m i)‖) ∧
      TendstoLocallyUniformly (fun k (z : τ → ℂ) => MvPolynomial.eval z (p k))
        (fun z => ∑' m : τ →₀ ℕ, c m * ∏ i, z i ^ (m i)) atTop := by
  have hG : ∀ z : τ → ℂ,
      Summable fun m : τ →₀ ℕ => ‖c m * ∏ i, z i ^ (m i)‖ := by
    intro z
    have hR : 0 < ‖z‖ + 1 := by positivity
    have hz : ∀ i, ‖z i‖ ≤ ‖z‖ + 1 := fun i =>
      (norm_le_pi_norm z i).trans (by linarith)
    obtain ⟨K, hK⟩ := hbound (2 * (‖z‖ + 1)) (by positivity)
    exact Summable.of_nonneg_of_le (fun m => norm_nonneg _)
      (fun m => term_bound z hz m ((coeff_bound p c hcoef (by positivity) hK m).2))
      (summable_half.mul_left K)
  refine ⟨hG, ?_⟩
  have heval : ∀ k (z : τ → ℂ),
      HasSum (fun m => (p k).coeff m * ∏ i, z i ^ m i) (MvPolynomial.eval z (p k)) := by
    intro k z
    rw [MvPolynomial.eval_eq']
    apply hasSum_sum_of_ne_finset_zero
    intro m hm
    rw [MvPolynomial.notMem_support_iff.mp hm, zero_mul]
  rw [tendstoLocallyUniformly_iff_filter]
  intro x
  rw [tendstoUniformlyOnFilter_iff_tendsto]
  set R := ‖x‖ + 1
  have hR : 0 < R := by positivity
  obtain ⟨K, hK⟩ := hbound (2 * R) (by positivity)
  have hnear : ∀ᶠ z in 𝓝 x, ∀ i, ‖z i‖ ≤ R := by
    have h : ∀ᶠ z in 𝓝 x, ‖z‖ < R :=
      (continuous_norm.tendsto x).eventually (gt_mem_nhds (by linarith))
    filter_upwards [h] with z hz i using (norm_le_pi_norm z i).trans hz.le
  have key : Tendsto (fun q : ℕ × (τ → ℂ) => ∑' m : τ →₀ ℕ,
      ((p q.1).coeff m * ∏ i, q.2 i ^ m i - c m * ∏ i, q.2 i ^ m i))
      (atTop ×ˢ 𝓝 x) (𝓝 0) := by
    have ht := tendsto_tsum_of_dominated_convergence (𝓕 := (atTop : Filter ℕ) ×ˢ 𝓝 x)
      (f := fun (q : ℕ × (τ → ℂ)) (m : τ →₀ ℕ) =>
        (p q.1).coeff m * ∏ i, q.2 i ^ m i - c m * ∏ i, q.2 i ^ m i)
      (g := fun _ => (0 : ℂ))
      (bound := fun m : τ →₀ ℕ => 2 * K * (1 / 2 : ℝ) ^ (∑ i, m i))
      (summable_half.mul_left _) ?_ ?_
    · simpa using ht
    · intro m
      have h1 : Tendsto (fun q : ℕ × (τ → ℂ) => (p q.1).coeff m - c m)
          (atTop ×ˢ 𝓝 x) (𝓝 0) := by
        have h := ((hcoef m).sub_const (c m)).comp (tendsto_fst (g := 𝓝 x))
        simpa [Function.comp_def] using h
      have h2 : Tendsto (fun q : ℕ × (τ → ℂ) => ∏ i, q.2 i ^ m i) (atTop ×ˢ 𝓝 x)
          (𝓝 (∏ i, x i ^ m i)) := by
        have hc : Continuous fun z : τ → ℂ => ∏ i, z i ^ m i := by fun_prop
        exact (hc.tendsto x).comp tendsto_snd
      have hmul := h1.mul h2
      simp only [zero_mul] at hmul
      refine hmul.congr (fun q => ?_)
      ring
    · have h : ∀ᶠ q : ℕ × (τ → ℂ) in atTop ×ˢ 𝓝 x, ∀ i, ‖q.2 i‖ ≤ R :=
        tendsto_snd.eventually hnear
      filter_upwards [h] with q hq m
      have b1 := term_bound q.2 hq m ((coeff_bound p c hcoef (by positivity) hK m).1 q.1)
      have b2 := term_bound q.2 hq m ((coeff_bound p c hcoef (by positivity) hK m).2)
      calc
        _ ≤ _ := norm_sub_le _ _
        _ ≤ _ := add_le_add b1 b2
        _ = _ := by ring
  rw [tendsto_uniformity_iff_dist_tendsto_zero]
  have hnorm := key.norm
  rw [norm_zero] at hnorm
  refine hnorm.congr (fun q => ?_)
  dsimp only
  rw [Summable.tsum_sub (heval q.1 q.2).summable (hG q.2).of_norm,
    (heval q.1 q.2).tsum_eq, dist_comm, dist_eq_norm]

end MvPolynomial
