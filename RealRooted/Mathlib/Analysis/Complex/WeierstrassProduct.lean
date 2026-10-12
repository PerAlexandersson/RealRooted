import Mathlib

open Complex Filter Topology

noncomputable section

namespace Complex

/-- The Weierstrass elementary factor of genus `1`: `E₁(w) = (1 - w) e^w`. -/
def weierstrassFactorOne (w : ℂ) : ℂ := (1 - w) * Complex.exp w

/-- Elementary factor estimate: `‖E₁(w) - 1‖ ≤ ‖w‖²` for `‖w‖ ≤ 1`. -/
theorem norm_weierstrassFactorOne_sub_one_le {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖weierstrassFactorOne w - 1‖ ≤ ‖w‖ ^ 2 := by
  have hexp : HasSum (fun n => w^n / n.factorial) (Complex.exp w) := by
    have := NormedSpace.expSeries_div_hasSum_exp w
    rwa [← Complex.exp_eq_exp_ℂ] at this
  have h1 : HasSum (fun n => w^(n+1) / (n+1).factorial) (Complex.exp w - 1) := by
    have := (hasSum_nat_add_iff' 1).mpr hexp
    simpa using this
  have h2 := (h1.sub (hexp.mul_left w))
  have hE : Complex.exp w - 1 - w * Complex.exp w = weierstrassFactorOne w - 1 := by
    unfold weierstrassFactorOne
    ring
  rw [hE] at h2
  have rexp : HasSum (fun n : ℕ => (1:ℝ) / n.factorial) (Real.exp 1) := by
    have := NormedSpace.expSeries_div_hasSum_exp (1:ℝ)
    rw [← Real.exp_eq_exp_ℝ] at this
    simpa using this
  have rexp1 : HasSum (fun n : ℕ => (1:ℝ) / (n+1).factorial) (Real.exp 1 - 1) := by
    have := (hasSum_nat_add_iff' 1).mpr rexp
    simpa using this
  have hc : HasSum
      (fun n : ℕ =>
        ‖w‖ ^ 2 * ((1 : ℝ) / n.factorial - 1 / (n + 1).factorial)) (‖w‖ ^ 2) := by
    have := (rexp.sub rexp1).mul_left (‖w‖ ^ 2)
    simpa using this
  refine h2.norm_le_of_bounded hc ?_
  intro n
  have hfac : (n+1).factorial = (n+1) * n.factorial := Nat.factorial_succ n
  have hnf : (0:ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have eq1 : w^(n+1) / ((n+1).factorial : ℂ) - w * (w^n / n.factorial) =
      - (w^(n+1) * (((1:ℝ) / (n.factorial) - 1 / ((n+1).factorial) : ℝ) : ℂ)) := by
    rw [hfac]
    push_cast
    have : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
    field_simp
    ring
  rw [eq1, norm_neg, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have hcoef : 0 ≤ (1:ℝ) / (n.factorial) - 1 / ((n+1).factorial) := by
    rw [sub_nonneg]
    apply one_div_le_one_div_of_le hnf
    exact_mod_cast Nat.factorial_le (Nat.le_succ n)
  rw [abs_of_nonneg hcoef]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · apply mul_le_mul_of_nonneg_right _ hcoef
    exact pow_le_pow_of_le_one (norm_nonneg _) hw (by lia)


private lemma hasProd_aux (f : ℕ → ℂ → ℂ) (hf : ∀ k, Differentiable ℂ (f k))
    (hbd : ∀ R : ℝ, ∃ u : ℕ → ℝ, Summable u ∧
      ∀ᶠ k in atTop, ∀ x ∈ Metric.ball (0:ℂ) R, ‖f k x - 1‖ ≤ u k) :
    HasProdLocallyUniformlyOn f (fun x => ∏' k, f k x) Set.univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball 0
  obtain ⟨u, hu, hev⟩ := hbd R
  have := Summable.hasProdUniformlyOn_nat_one_add (f := fun k x => f k x - 1) hK hu ?_ ?_
  · simpa using this
  · filter_upwards [hev] with k hk x hx using hk x (hR hx)
  · intro k; exact ((hf k).continuous.sub continuous_const).continuousOn

private lemma differentiable_aux (f : ℕ → ℂ → ℂ) (F : ℂ → ℂ)
    (hf : ∀ k, Differentiable ℂ (f k))
    (h : HasProdLocallyUniformlyOn f F Set.univ) : Differentiable ℂ F := by
  have := TendstoLocallyUniformlyOn.differentiableOn h ?_ isOpen_univ
  · exact fun x => (this x trivial).differentiableAt (isOpen_univ.mem_nhds trivial)
  · filter_upwards with s
    simpa [Finset.prod_fn] using DifferentiableOn.finsetProd (fun k _ => (hf k).differentiableOn)

private theorem main_aux (g : ℂ → ℂ) (hg : Differentiable ℂ g) (hg0 : g 0 = 1)
    (hgne : ∀ y, g y = 0 → y = 1)
    (hgord : ∀ c : ℂ, c ≠ 0 → analyticOrderAt (fun x => g (x / c)) c = 1)
    {z : ℕ → ℂ} (hz : ∀ k, z k ≠ 0) (hfin : ∀ w, {k | z k = w}.Finite)
    (hbd : ∀ R : ℝ, ∃ u : ℕ → ℝ, Summable u ∧
      ∀ᶠ k in atTop, ∀ x ∈ Metric.ball (0:ℂ) R, ‖g (x / z k) - 1‖ ≤ u k) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      HasProdLocallyUniformlyOn (fun k w => g (w / z k)) F Set.univ ∧ F 0 = 1 ∧
      ∀ w : ℂ, analyticOrderAt F w = Set.encard {k | z k = w} := by
  have hfd : ∀ k, Differentiable ℂ (fun w => g (w / z k)) :=
    fun k => hg.comp (differentiable_id.div_const _)
  have hP := hasProd_aux (fun k w => g (w / z k)) hfd hbd
  have hFd := differentiable_aux _ _ hfd hP
  refine ⟨_, hFd, hP, by simp [hg0], ?_⟩
  intro w
  rw [(hfin w).encard_eq_coe_toFinset_card]
  by_cases hw : w = 0
  · subst hw
    have : (hfin 0).toFinset = ∅ := by
      ext k; simp [hz k]
    rw [this, Finset.card_empty, Nat.cast_zero]
    exact (hFd.analyticAt 0).analyticOrderAt_eq_zero.mpr (by simp [hg0])
  set S := (hfin w).toFinset with hS
  have hmem : ∀ k, k ∈ S ↔ z k = w := fun k => by simp [hS]
  let h : ℕ → ℂ → ℂ := fun k x => if k ∈ S then 1 else g (x / z k)
  have hhd : ∀ k, Differentiable ℂ (h k) := by
    intro k
    by_cases hk : k ∈ S
    · simpa only [h, hk, ite_true] using (differentiable_const (c := (1 : ℂ)))
    · simpa only [h, hk, ite_false] using hfd k
  have hhb : ∀ R : ℝ, ∃ u : ℕ → ℝ, Summable u ∧
      ∀ᶠ k in atTop, ∀ x ∈ Metric.ball (0:ℂ) R, ‖h k x - 1‖ ≤ u k := by
    intro R
    obtain ⟨u, hu, hev⟩ := hbd R
    refine ⟨u, hu, ?_⟩
    have hS' : ∀ᶠ k in atTop, k ∉ S := by
      rw [← Nat.cofinite_eq_atTop]
      exact S.finite_toSet.eventually_cofinite_notMem
    filter_upwards [hev, hS'] with k hk hk' x hx
    simpa [h, hk'] using hk x hx
  have hh := hasProd_aux h hhd hhb
  have hGd := differentiable_aux _ _ hhd hh
  have hsplit : (fun x => ∏' k, g (x / z k)) =
      (fun x => g (x / w)) ^ S.card * (fun x => ∏' k, h k x) := by
    ext x
    have h1 : HasProd (fun k => if k ∈ S then g (x / z k) else 1) (g (x / w) ^ S.card) := by
      have := hasProd_prod_of_ne_finset_one (f := fun k => if k ∈ S then g (x / z k) else 1)
        (s := S) (L := SummationFilter.unconditional ℕ) (fun k hk => by simp [hk])
      convert this using 1
      rw [Finset.prod_congr rfl (g := fun _ => g (x / w))
        (fun k hk => by simp [hk, (hmem k).1 hk]), Finset.prod_const]
    have h2 := hh.hasProd (Set.mem_univ x)
    have h3 := h1.mul h2
    have e : (fun k => (if k ∈ S then g (x / z k) else 1) * h k x) = fun k => g (x / z k) := by
      ext k; by_cases hk : k ∈ S <;> simp [h, hk]
    rw [e] at h3
    simpa using h3.tprod_eq
  have hGw : ∏' k, h k w ≠ 0 := by
    obtain ⟨u, hu, hev⟩ := hbd (‖w‖ + 1)
    have hsum : Summable fun k => ‖h k w - 1‖ := by
      refine Summable.of_norm_bounded_eventually hu ?_
      have hS' : ∀ᶠ k in cofinite, k ∉ S := S.finite_toSet.eventually_cofinite_notMem
      rw [Nat.cofinite_eq_atTop] at hS' ⊢
      filter_upwards [hev, hS'] with k hk hk'
      simpa [h, hk'] using hk w (by simp)
    have := tprod_one_add_ne_zero_of_summable (f := fun k => h k w - 1) ?_ hsum
    · simpa using this
    · intro k
      simp only [add_sub_cancel]
      by_cases hk : k ∈ S
      · simp [h, hk]
      · simp only [h, hk, ite_false]
        intro h0
        have := hgne _ h0
        rw [div_eq_one_iff_eq (hz k)] at this
        exact hk ((hmem k).2 this.symm)
  have hga : AnalyticAt ℂ (fun x => g (x / w)) w :=
    (hg.comp (differentiable_id.div_const w)).analyticAt w
  change analyticOrderAt (fun x => ∏' k, g (x / z k)) w = _
  rw [hsplit, analyticOrderAt_mul (hga.pow _) (hGd.analyticAt w), analyticOrderAt_pow hga,
    hgord w hw, (hGd.analyticAt w).analyticOrderAt_eq_zero.mpr hGw]
  simp


private lemma finite_aux {z : ℕ → ℂ} (hz : ∀ k, z k ≠ 0) {p : ℕ}
    (ht : Tendsto (fun k => ‖z k‖⁻¹ ^ p) atTop (𝓝 0)) (w : ℂ) :
    {k | z k = w}.Finite := by
  by_cases hw : w = 0
  · subst hw; simp [hz]
  have hpos : 0 < ‖w‖⁻¹ ^ p := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ht.eventually (gt_mem_nhds hpos))
  refine (Set.finite_Iio N).subset ?_
  intro k hk
  simp only [Set.mem_ofPred_eq] at hk
  simp only [Set.mem_Iio]
  by_contra h
  have := hN k (not_lt.1 h)
  rw [hk] at this
  exact lt_irrefl _ this

private lemma order_one_aux {f q : ℂ → ℂ} {c : ℂ} (hq : AnalyticAt ℂ q c)
    (hqc : q c ≠ 0)
    (hf : ∀ x, f x = (x - c) * q x) : analyticOrderAt f c = 1 := by
  have hfa : AnalyticAt ℂ f c := by
    rw [funext hf]; exact (analyticAt_id.sub analyticAt_const).mul hq
  have := (hfa.analyticOrderAt_eq_natCast (n := 1)).2
    ⟨q, hq, hqc, Eventually.of_forall fun x => by simp [hf]⟩
  exact_mod_cast this

/-- **Genus-0 Weierstrass product.** If `z k ≠ 0` and `∑ 1/‖z k‖ < ∞`,
the partial products
`∏_{k<n} (1 - w / z k)` converge locally uniformly on `ℂ` to an entire function `F`, with
`F 0 = 1`, whose zeros are exactly the `z k`, with multiplicity `#{k | z k = w}`. -/
theorem exists_entire_prod_genus_zero {z : ℕ → ℂ} (hz : ∀ k, z k ≠ 0)
    (hs : Summable fun k => ‖z k‖⁻¹) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      HasProdLocallyUniformlyOn (fun k w => 1 - w / z k) F Set.univ ∧ F 0 = 1 ∧
      ∀ w : ℂ, analyticOrderAt F w = Set.encard {k | z k = w} := by
  refine main_aux (fun y => 1 - y) (by fun_prop) (by simp) (fun y hy => by linear_combination -hy)
    (fun c hc => order_one_aux (q := fun _ => -c⁻¹) analyticAt_const (by simpa using hc)
      (fun x => by field_simp; ring)) hz
    (finite_aux hz (p := 1) (by simpa using hs.tendsto_atTop_zero)) ?_
  intro R
  refine ⟨fun k => |R| * ‖z k‖⁻¹, hs.mul_left _, Eventually.of_forall fun k x hx => ?_⟩
  rw [Metric.mem_ball, dist_zero_right] at hx
  simp only [sub_sub_cancel_left, norm_neg, norm_div]
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (hx.le.trans (le_abs_self R)) (by positivity)

/-- **Genus-1 Weierstrass product.** If `z k ≠ 0` and `∑ 1/‖z k‖² < ∞`,
the partial products
`∏_{k<n} E₁(w / z k)` converge locally uniformly on `ℂ` to an entire function `F`, with
`F 0 = 1`, whose zeros are exactly the `z k`, with multiplicity `#{k | z k = w}`. -/
theorem exists_entire_prod_genus_one {z : ℕ → ℂ} (hz : ∀ k, z k ≠ 0)
    (hs : Summable fun k => ‖z k‖⁻¹ ^ 2) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      HasProdLocallyUniformlyOn (fun k w => weierstrassFactorOne (w / z k)) F Set.univ ∧
        F 0 = 1 ∧
      ∀ w : ℂ, analyticOrderAt F w = Set.encard {k | z k = w} := by
  refine main_aux weierstrassFactorOne (by unfold weierstrassFactorOne; fun_prop)
    (by simp [weierstrassFactorOne]) ?_
    (fun c hc => order_one_aux (q := fun x => -c⁻¹ * Complex.exp (x / c)) (by fun_prop)
      (by simp [hc, Complex.exp_ne_zero])
      (fun x => by unfold weierstrassFactorOne; field_simp; ring)) hz
    (finite_aux hz (p := 2) hs.tendsto_atTop_zero) ?_
  · intro y hy
    unfold weierstrassFactorOne at hy
    rcases mul_eq_zero.1 hy with h | h
    · linear_combination -h
    · exact absurd h (Complex.exp_ne_zero y)
  intro R
  refine ⟨fun k => R ^ 2 * ‖z k‖⁻¹ ^ 2, hs.mul_left _, ?_⟩
  have ht : Tendsto (fun k => ‖z k‖⁻¹ ^ 2 * R ^ 2) atTop (𝓝 0) := by
    simpa using hs.tendsto_atTop_zero.mul_const (R ^ 2)
  filter_upwards [ht.eventually (gt_mem_nhds one_pos)] with k hk x hx
  rw [Metric.mem_ball, dist_zero_right] at hx
  have hx2 : ‖x‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx.le 2
  have hn : ‖x / z k‖ = ‖x‖ * ‖z k‖⁻¹ := by rw [norm_div, div_eq_mul_inv]
  have hsq : ‖x / z k‖ ^ 2 ≤ R ^ 2 * ‖z k‖⁻¹ ^ 2 := by
    rw [hn, mul_pow]; exact mul_le_mul_of_nonneg_right hx2 (by positivity)
  have h1 : ‖x / z k‖ ≤ 1 := by nlinarith [norm_nonneg (x / z k)]
  exact (norm_weierstrassFactorOne_sub_one_le h1).trans hsq

end Complex
