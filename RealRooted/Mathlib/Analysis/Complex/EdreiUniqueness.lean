import Mathlib

/-!
# Uniqueness of Edrei–Thoma parameters

This file proves that the parameters in the analytic Edrei–Thoma canonical product are unique.
-/

open Complex Filter Topology

noncomputable section

namespace Complex.EdreiThoma

/-- The Edrei–Thoma canonical function `C z^k e^{γ z} ∏(1 + α_i z) / ∏(1 - β_i z)`
(defined by `tprod`; it is the genuine product for `|z|` small when `∑ α_i, ∑ β_i < ∞`). -/
def edreiFunction (C γ : ℝ) (k : ℕ) (α β : ℕ → ℝ) (z : ℂ) : ℂ :=
  (C : ℂ) * z ^ k * Complex.exp (γ * z) * (∏' i, (1 + (α i : ℂ) * z)) /
    ∏' i, (1 - (β i : ℂ) * z)

/-! ### Auxiliary material -/

/-- Number of indices at which `u` takes the value `t`. -/
private def cnt (u : ℕ → ℝ) (t : ℝ) : ℕ := Nat.card ({i | u i = t} : Set ℕ)

/-- Power sums. -/
private def psum (u : ℕ → ℝ) (m : ℕ) : ℝ := ∑' i, u i ^ m

private lemma summable_pow_of_nonneg {u : ℕ → ℝ} (hu : ∀ i, 0 ≤ u i) (su : Summable u) {m : ℕ}
    (hm : 1 ≤ m) : Summable (fun i => u i ^ m) := by
  refine Summable.of_nonneg_of_le (fun i => pow_nonneg (hu i) _) (fun i => ?_)
    (su.mul_right ((∑' j, u j) ^ (m - 1)))
  have h1 : u i ≤ ∑' j, u j := su.le_tsum i (fun j _ => hu j)
  calc u i ^ m = u i * u i ^ (m - 1) := by rw [← pow_succ']; congr 1; lia
    _ ≤ u i * (∑' j, u j) ^ (m - 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hu i) h1 _) (hu i)

private lemma finite_ge {u : ℕ → ℝ} (su : Summable u) {ε : ℝ} (hε : 0 < ε) :
    {i | ε ≤ u i}.Finite := by
  have := su.tendsto_cofinite_zero.eventually (gt_mem_nhds hε)
  simpa [Filter.eventually_cofinite] using this

private lemma cnt_neg {u : ℕ → ℝ} (hu : ∀ i, 0 ≤ u i) {t : ℝ} (ht : t < 0) : cnt u t = 0 := by
  have : {i | u i = t} = (∅ : Set ℕ) := by
    ext i
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro h; linarith [hu i]
  simp [cnt, this]

private lemma encard_eq_cnt {u : ℕ → ℝ} (su : Summable u) {t : ℝ} (ht : 0 < t) :
    Set.encard {i | u i = t} = cnt u t := by
  have hfin : {i | u i = t}.Finite := (finite_ge su ht).subset (fun i hi => le_of_eq hi.symm)
  rw [cnt, Nat.card_coe_set_eq, hfin.cast_ncard_eq]

/-- Fiberwise regrouping of a sum. -/
private lemma hasSum_cnt {u : ℕ → ℝ} (g : ℝ → ℝ) (hs : Summable (fun i => g (u i))) :
    HasSum (fun t => (cnt u t : ℝ) * g t) (∑' i, g (u i)) := by
  set e := Equiv.sigmaFiberEquiv u
  have hF : Summable (fun x : (Σ t, {i // u i = t}) => g (u (e x))) :=
    (e.summable_iff (f := fun i => g (u i))).mpr hs
  have hF' : HasSum (fun x : (Σ t, {i // u i = t}) => g (u (e x))) (∑' i, g (u i)) := by
    rw [← e.tsum_eq (fun i => g (u i))]; exact hF.hasSum
  refine hF'.sigma (fun t => ?_)
  have h1 := (hF.sigma_factor t).hasSum
  convert h1 using 1
  have : ∀ c : {i // u i = t}, g (u (e ⟨t, c⟩)) = g t := by
    intro c; simp [e, Equiv.sigmaFiberEquiv, c.2]
  simp only [this, tsum_const, nsmul_eq_mul, cnt]
  rfl

private lemma cnt_ne_zero {u : ℕ → ℝ} {s : ℝ} (h : cnt u s ≠ 0) : ∃ i, u i = s := by
  by_contra hc
  push Not at hc
  apply h
  have : {i | u i = s} = (∅ : Set ℕ) := by
    ext i; simp [hc i]
  simp [cnt, this]

/-- Moment uniqueness. -/
private lemma moment_unique {u₁ u₂ v₁ v₂ : ℕ → ℝ}
    (hu₁ : ∀ i, 0 ≤ u₁ i) (hu₂ : ∀ i, 0 ≤ u₂ i) (hv₁ : ∀ i, 0 ≤ v₁ i) (hv₂ : ∀ i, 0 ≤ v₂ i)
    (su₁ : Summable u₁) (su₂ : Summable u₂) (sv₁ : Summable v₁) (sv₂ : Summable v₂)
    (e : ℕ → ℕ) (he : StrictMono e) (he1 : ∀ j, 1 ≤ e j)
    (h : ∀ j, psum u₁ (e j) + psum u₂ (e j) = psum v₁ (e j) + psum v₂ (e j)) :
    ∀ t, 0 < t → cnt u₁ t + cnt u₂ t = cnt v₁ t + cnt v₂ t := by
  intro t ht
  by_contra hne
  set D : ℝ → ℝ := fun s => ((cnt u₁ s + cnt u₂ s : ℕ) : ℝ) - ((cnt v₁ s + cnt v₂ s : ℕ) : ℝ)
    with hDdef
  have hD : ∀ s, D s ≠ 0 ↔ cnt u₁ s + cnt u₂ s ≠ cnt v₁ s + cnt v₂ s := by
    intro s
    rw [hDdef, Ne, sub_eq_zero, Nat.cast_inj]
  have hsumD : ∀ j, HasSum (fun s => D s * s ^ (e j)) 0 := by
    intro j
    have A1 := hasSum_cnt (u := u₁) (fun s => s ^ (e j)) (summable_pow_of_nonneg hu₁ su₁ (he1 j))
    have A2 := hasSum_cnt (u := u₂) (fun s => s ^ (e j)) (summable_pow_of_nonneg hu₂ su₂ (he1 j))
    have B1 := hasSum_cnt (u := v₁) (fun s => s ^ (e j)) (summable_pow_of_nonneg hv₁ sv₁ (he1 j))
    have B2 := hasSum_cnt (u := v₂) (fun s => s ^ (e j)) (summable_pow_of_nonneg hv₂ sv₂ (he1 j))
    have := (A1.add A2).sub (B1.add B2)
    convert this using 1
    · funext s; simp only [hDdef]; push_cast; ring
    · have hj := h j
      simp only [psum] at hj
      linarith
  have hsupp : ∀ s, D s ≠ 0 →
      (cnt u₁ s ≠ 0 ∨ cnt u₂ s ≠ 0 ∨ cnt v₁ s ≠ 0 ∨ cnt v₂ s ≠ 0) := by
    intro s hs
    rw [hD] at hs
    lia
  have hpos : ∀ s, D s ≠ 0 → 0 ≤ s := by
    intro s hs
    rcases hsupp s hs with h1 | h1 | h1 | h1 <;>
    · obtain ⟨i, hi⟩ := cnt_ne_zero h1
      rw [← hi]; first | exact hu₁ i | exact hu₂ i | exact hv₁ i | exact hv₂ i
  have hfin : {s | t ≤ s ∧ D s ≠ 0}.Finite := by
    refine (((((finite_ge su₁ ht).image u₁).union ((finite_ge su₂ ht).image u₂)).union
      ((finite_ge sv₁ ht).image v₁)).union ((finite_ge sv₂ ht).image v₂)).subset ?_
    rintro s ⟨hts, hs⟩
    rcases hsupp s hs with h1 | h1 | h1 | h1 <;> obtain ⟨i, hi⟩ := cnt_ne_zero h1 <;>
      subst hi <;> simp only [Set.mem_union, Set.mem_image, Set.mem_ofPred_eq]
    · exact Or.inl (Or.inl (Or.inl ⟨i, hts, rfl⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨i, hts, rfl⟩))
    · exact Or.inl (Or.inr ⟨i, hts, rfl⟩)
    · exact Or.inr ⟨i, hts, rfl⟩
  obtain ⟨t₀, ⟨htt₀, hDt₀⟩, hmax⟩ :=
    Set.exists_max_image _ id hfin ⟨t, le_rfl, (hD t).mpr hne⟩
  have hbig : ∀ s, t₀ < s → D s = 0 := by
    intro s hs
    by_contra hc
    have := hmax s ⟨by simp only [id] at *; linarith, hc⟩
    simp only [id] at this
    linarith
  have ht₀ : 0 < t₀ := lt_of_lt_of_le ht htt₀
  set R : ℕ → ℝ → ℝ := fun j s => if s = t₀ then 0 else D s * (s / t₀) ^ (e j) with hRdef
  have hR : ∀ j, ∑' s, R j s = - D t₀ := by
    intro j
    have h1 := (hsumD j).div_const (t₀ ^ (e j))
    have h2 := h1.sub (hasSum_ite_eq t₀ (D t₀))
    refine HasSum.tsum_eq ?_
    convert h2 using 1
    · funext s
      simp only [hRdef]
      split_ifs with hs
      · subst hs; field_simp; ring
      · rw [div_pow]; ring
    · simp
  have hcntsum : ∀ {u : ℕ → ℝ}, (∀ i, 0 ≤ u i) → Summable u →
      Summable (fun s => (cnt u s : ℝ) * |s|) := by
    intro u hu su
    have := (hasSum_cnt (u := u) (fun s => s ^ 1)
      (summable_pow_of_nonneg (m := 1) hu su le_rfl)).summable.abs
    refine this.congr (fun s => ?_)
    simp [abs_mul]
  set bound : ℝ → ℝ := fun s =>
    ((cnt u₁ s : ℝ) * |s| + (cnt u₂ s : ℝ) * |s| + (cnt v₁ s : ℝ) * |s| + (cnt v₂ s : ℝ) * |s|)
      / t₀ with hbdef
  have hbsum : Summable bound :=
    ((((hcntsum hu₁ su₁).add (hcntsum hu₂ su₂)).add (hcntsum hv₁ sv₁)).add
      (hcntsum hv₂ sv₂)).div_const t₀
  have hbnn : ∀ s, 0 ≤ bound s := fun s => by
    simp only [hbdef]; positivity
  have hlim : ∀ s, Tendsto (fun j => R j s) atTop (𝓝 0) := by
    intro s
    simp only [hRdef]
    by_cases hs : s = t₀
    · simp [hs]
    by_cases hDs : D s = 0
    · simp [hs, hDs]
    simp only [hs, ite_false]
    have h0 := hpos s hDs
    have hle : s ≤ t₀ := by
      by_contra hc; exact hDs (hbig s (lt_of_not_ge hc))
    have hlt : s / t₀ < 1 := (div_lt_one ht₀).mpr (lt_of_le_of_ne hle hs)
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg h0 ht₀.le) hlt).comp
      he.tendsto_atTop
    simpa using this.const_mul (D s)
  have hdom : ∀ᶠ j in atTop, ∀ s, ‖R j s‖ ≤ bound s := by
    refine Eventually.of_forall (fun j s => ?_)
    simp only [hRdef]
    by_cases hs : s = t₀
    · simp [hs, hbnn]
    by_cases hDs : D s = 0
    · simp [hs, hDs, hbnn]
    simp only [hs, ite_false, Real.norm_eq_abs]
    have h0 := hpos s hDs
    have hle : s ≤ t₀ := by
      by_contra hc; exact hDs (hbig s (lt_of_not_ge hc))
    have hq0 : 0 ≤ s / t₀ := div_nonneg h0 ht₀.le
    have hq1 : s / t₀ ≤ 1 := (div_le_one ht₀).mpr hle
    have hpow : (s / t₀) ^ (e j) ≤ s / t₀ := pow_le_of_le_one hq0 hq1 (by have := he1 j; lia)
    have habsD : |D s| ≤ (cnt u₁ s : ℝ) + cnt u₂ s + cnt v₁ s + cnt v₂ s := by
      simp only [hDdef]; push_cast
      rw [abs_le]; constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) (cnt u₁ s),
        Nat.cast_nonneg (α := ℝ) (cnt u₂ s), Nat.cast_nonneg (α := ℝ) (cnt v₁ s),
        Nat.cast_nonneg (α := ℝ) (cnt v₂ s)]
    rw [abs_mul, abs_of_nonneg (pow_nonneg hq0 _)]
    calc |D s| * (s / t₀) ^ (e j) ≤ ((cnt u₁ s : ℝ) + cnt u₂ s + cnt v₁ s + cnt v₂ s) * (s / t₀) :=
          mul_le_mul habsD hpow (pow_nonneg hq0 _) (by positivity)
      _ = bound s := by simp only [hbdef, abs_of_nonneg h0]; ring
  have hT := tendsto_tsum_of_dominated_convergence hbsum hlim hdom
  simp only [hR, tsum_zero] at hT
  have := tendsto_nhds_unique tendsto_const_nhds hT
  exact hDt₀ (by linarith)

/-- Sum of logarithms. -/
private def logSum (α : ℕ → ℝ) (x : ℝ) : ℝ := ∑' i, Real.log (1 + α i * x)

private lemma logSum_series {α : ℕ → ℝ} (hα : ∀ i, 0 ≤ α i) (sα : Summable α) {A : ℝ}
    (hA : ∀ i, α i ≤ A) {x : ℝ} (hx : |x| * A ≤ 1 / 2) :
    HasSum (fun i => Real.log (1 + α i * x)) (logSum α x) ∧
    HasSum (fun n : ℕ => (-1) ^ n * psum α (n + 1) / (n + 1) * x ^ (n + 1)) (logSum α x) := by
  set f : ℕ × ℕ → ℝ := fun p => (-1) ^ p.2 * (α p.1 * x) ^ (p.2 + 1) / (p.2 + 1) with hf
  have hsmall : ∀ i, |α i * x| ≤ 1 / 2 := by
    intro i
    rw [abs_mul, abs_of_nonneg (hα i)]
    nlinarith [abs_nonneg x, hA i, hα i]
  have hlog : ∀ i, HasSum (fun n => f (i, n)) (Real.log (1 + α i * x)) := by
    intro i
    have h := (Real.hasSum_pow_div_log_of_abs_lt_one
      (x := -(α i * x)) (by rw [abs_neg]; linarith [hsmall i])).neg
    rw [sub_neg_eq_add, neg_neg] at h
    convert h using 1
    funext n
    simp only [hf]
    rw [neg_pow (α i * x) (n + 1), pow_succ (-1 : ℝ) n]
    ring
  have hsum : Summable f := by
    refine Summable.of_norm_bounded (g := fun p : ℕ × ℕ => (α p.1 * |x|) * (1 / 2 : ℝ) ^ p.2)
      (Summable.mul_of_nonneg (sα.mul_right |x|) summable_geometric_two
        (fun i => mul_nonneg (hα i) (abs_nonneg x)) (fun n => by positivity)) ?_
    rintro ⟨i, n⟩
    simp only [hf, Real.norm_eq_abs]
    have hai : |α i * x| = α i * |x| := by rw [abs_mul, abs_of_nonneg (hα i)]
    rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_pow, hai,
      abs_of_pos (by positivity : (0:ℝ) < n + 1)]
    have h1 : α i * |x| ≤ 1 / 2 := hai ▸ hsmall i
    have h0 : 0 ≤ α i * |x| := mul_nonneg (hα i) (abs_nonneg x)
    calc (α i * |x|) ^ (n + 1) / (n + 1) ≤ (α i * |x|) ^ (n + 1) :=
          div_le_self (pow_nonneg h0 _) (by linarith [(n.cast_nonneg : (0:ℝ) ≤ n)])
      _ = α i * |x| * (α i * |x|) ^ n := by ring
      _ ≤ α i * |x| * (1 / 2) ^ n :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h1 n) h0
  have part1 := hsum.hasSum.prod_fiberwise hlog
  have heq : logSum α x = ∑' p, f p := part1.tsum_eq
  refine ⟨heq ▸ part1, ?_⟩
  rw [heq]
  have hsw : HasSum (f ∘ Prod.swap) (∑' p, f p) :=
    (Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hsum.hasSum
  refine hsw.prod_fiberwise (fun n => ?_)
  have := (hsw.summable.prod_factor n).hasSum
  convert this using 1
  simp only [Function.comp, Prod.swap, hf, psum]
  rw [← tsum_mul_left, ← tsum_div_const, ← tsum_mul_right]
  congr 1; funext i; ring

/-- The exponent `γ x + Σ log(1 + α_i x) - Σ log(1 - β_i x)`. -/
private def expo (γ : ℝ) (α β : ℕ → ℝ) (x : ℝ) : ℝ := γ * x + logSum α x - logSum β (-x)

/-- Taylor coefficients of `expo`. -/
private def coef (γ : ℝ) (α β : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => ((-1) ^ n * psum α (n + 1) + psum β (n + 1)) / (n + 1) + if n = 0 then γ else 0

private lemma psum_nonneg {α : ℕ → ℝ} (hα : ∀ i, 0 ≤ α i) (m : ℕ) : 0 ≤ psum α m :=
  tsum_nonneg (fun i => pow_nonneg (hα i) m)

private lemma psum_bound {α : ℕ → ℝ} (hα : ∀ i, 0 ≤ α i) (sα : Summable α) {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r ≤ 1) (hαr : ∀ i, α i * r ≤ 1) (n : ℕ) :
    psum α (n + 1) * r ^ (n + 1) ≤ ∑' i, α i := by
  rw [psum, ← tsum_mul_right]
  refine Summable.tsum_le_tsum (fun i => ?_)
    ((summable_pow_of_nonneg hα sα (Nat.le_add_left 1 n)).mul_right _) sα
  rw [← mul_pow]
  calc (α i * r) ^ (n + 1) ≤ α i * r :=
        pow_le_of_le_one (mul_nonneg (hα i) hr0) (hαr i) (Nat.succ_ne_zero n)
    _ ≤ α i := mul_le_of_le_one_right (hα i) hr1

private lemma expo_hasSum {γ : ℝ} {α β : ℕ → ℝ}
    (hα : ∀ i, 0 ≤ α i) (hβ : ∀ i, 0 ≤ β i) (sα : Summable α) (sβ : Summable β) {A : ℝ}
    (hAα : ∀ i, α i ≤ A) (hAβ : ∀ i, β i ≤ A) {x : ℝ} (hx : |x| * A ≤ 1 / 2) :
    HasSum (fun n => coef γ α β n * x ^ n) (expo γ α β x) := by
  have L1 := (logSum_series hα sα hAα hx).2
  have L2 := (logSum_series hβ sβ hAβ (x := -x) (by rwa [abs_neg])).2
  have G := hasSum_ite_eq 0 (γ * x)
  have S := (G.add L1).sub L2
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.sum_range_one, coef, pow_zero, mul_one, sub_zero]
  convert S using 1
  · funext n
    have hs : ((-1 : ℝ) ^ n) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [neg_pow x (n + 1), pow_succ (-1 : ℝ) n]
    split_ifs with hn
    · subst hn
      simp
      ring
    · linear_combination (-(psum β (n + 1)) * x ^ (n + 1) / (n + 1)) * hs
  · rfl

private lemma expo_hasFPowerSeriesAt {γ : ℝ} {α β : ℕ → ℝ}
    (hα : ∀ i, 0 ≤ α i) (hβ : ∀ i, 0 ≤ β i) (sα : Summable α) (sβ : Summable β) :
    HasFPowerSeriesAt (expo γ α β) (FormalMultilinearSeries.ofScalars ℝ (coef γ α β)) 0 := by
  set A : ℝ := 1 + ∑' i, α i + ∑' i, β i with hAdef
  have hSα : 0 ≤ ∑' i, α i := tsum_nonneg hα
  have hSβ : 0 ≤ ∑' i, β i := tsum_nonneg hβ
  have hA1 : 1 ≤ A := by linarith
  have hAα : ∀ i, α i ≤ A := fun i => by linarith [sα.le_tsum i (fun j _ => hα j)]
  have hAβ : ∀ i, β i ≤ A := fun i => by linarith [sβ.le_tsum i (fun j _ => hβ j)]
  set r : ℝ := 1 / (2 * A) with hrdef
  have hr0 : 0 < r := by positivity
  have hrA : r * A = 1 / 2 := by rw [hrdef]; field_simp
  have hr1 : r ≤ 1 := by nlinarith
  set R : NNReal := ⟨r, hr0.le⟩
  refine ⟨R, ?_, ?_, ?_⟩
  · refine FormalMultilinearSeries.le_radius_of_bound _ (∑' i, α i + ∑' i, β i + |γ|) (fun n => ?_)
    rw [FormalMultilinearSeries.ofScalars_norm, Real.norm_eq_abs]
    change |coef γ α β n| * r ^ n ≤ _
    rcases n with _ | n
    · simp only [coef, abs_zero, pow_zero, mul_one]
      positivity
    have hαr : ∀ i, α i * r ≤ 1 := fun i => by nlinarith [hAα i, hα i]
    have hβr : ∀ i, β i * r ≤ 1 := fun i => by nlinarith [hAβ i, hβ i]
    have b1 := psum_bound hα sα hr0.le hr1 hαr n
    have b2 := psum_bound hβ sβ hr0.le hr1 hβr n
    have p1 := psum_nonneg hα (n + 1)
    have p2 := psum_nonneg hβ (n + 1)
    have hrn : r ^ (n + 1) ≤ 1 := pow_le_one₀ hr0.le hr1
    have hrn0 : 0 ≤ r ^ (n + 1) := by positivity
    have hn1 : (1 : ℝ) ≤ n + 1 := by linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
    have habs : |(-1) ^ n * psum α (n + 1) + psum β (n + 1)| ≤ psum α (n + 1) + psum β (n + 1) := by
      rcases neg_one_pow_eq_or ℝ n with h | h <;> rw [h] <;> rw [abs_le] <;> constructor <;>
        linarith
    simp only [coef]
    have h1 : |((-1) ^ n * psum α (n + 1) + psum β (n + 1)) / (n + 1)| ≤
        psum α (n + 1) + psum β (n + 1) := by
      rw [abs_div, abs_of_pos (by linarith : (0:ℝ) < n + 1)]
      exact (div_le_self (by positivity) hn1).trans' (div_le_div_of_nonneg_right habs (by linarith))
    have h2 : |(if n = 0 then γ else 0 : ℝ)| ≤ |γ| := by split_ifs <;> simp
    calc |((-1) ^ n * psum α (n + 1) + psum β (n + 1)) / (n + 1) + if n = 0 then γ else 0| *
          r ^ (n + 1) ≤ (psum α (n + 1) + psum β (n + 1) + |γ|) * r ^ (n + 1) :=
          mul_le_mul_of_nonneg_right ((abs_add_le _ _).trans (add_le_add h1 h2)) hrn0
      _ = psum α (n + 1) * r ^ (n + 1) + psum β (n + 1) * r ^ (n + 1) + |γ| * r ^ (n + 1) := by
          ring
      _ ≤ _ := by nlinarith [abs_nonneg γ]
  · exact ENNReal.coe_pos.2 (NNReal.coe_pos.1 (show (0 : ℝ) < (R : ℝ) from hr0))
  · intro y hy
    have hy' : |y| < r := by
      have h := hy
      rw [Metric.mem_eball, edist_zero_right, enorm_lt_coe] at h
      have h2 : ((‖y‖₊ : NNReal) : ℝ) < (R : ℝ) := NNReal.coe_lt_coe.2 h
      exact h2
    have hx : |y| * A ≤ 1 / 2 := by nlinarith
    simpa [FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using
      expo_hasSum (γ := γ) hα hβ sα sβ hAα hAβ hx

private lemma tprod_eq_exp_logSum {α : ℕ → ℝ} (hα : ∀ i, 0 ≤ α i) (sα : Summable α) {A : ℝ}
    (hA : ∀ i, α i ≤ A) {x : ℝ} (hx : |x| * A ≤ 1 / 2) :
    ∏' i, (1 + (α i : ℂ) * (x : ℂ)) = ((Real.exp (logSum α x) : ℝ) : ℂ) := by
  have P := (logSum_series hα sα hA hx).1.rexp
  have hpos : ∀ i, 0 < 1 + α i * x := by
    intro i
    have : |α i * x| ≤ 1 / 2 := by
      rw [abs_mul, abs_of_nonneg (hα i)]; nlinarith [abs_nonneg x, hA i, hα i]
    linarith [neg_abs_le (α i * x)]
  have P' : HasProd (fun i => 1 + α i * x) (Real.exp (logSum α x)) := by
    convert P using 1
    funext i; simp [Real.exp_log (hpos i)]
  have Q := P'.map Complex.ofRealHom Complex.continuous_ofReal
  convert Q.tprod_eq using 2
  funext i; simp

private lemma edreiFunction_real {C γ : ℝ} {k : ℕ} {α β : ℕ → ℝ}
    (hα : ∀ i, 0 ≤ α i) (hβ : ∀ i, 0 ≤ β i) (sα : Summable α) (sβ : Summable β) :
    ∀ᶠ x : ℝ in 𝓝 0,
      edreiFunction C γ k α β (x : ℂ) =
        ((C * x ^ k * Real.exp (expo γ α β x) : ℝ) : ℂ) := by
  set A : ℝ := 1 + ∑' i, α i + ∑' i, β i with hAdef
  have hSα : 0 ≤ ∑' i, α i := tsum_nonneg hα
  have hSβ : 0 ≤ ∑' i, β i := tsum_nonneg hβ
  have hA1 : 1 ≤ A := by linarith
  have hAα : ∀ i, α i ≤ A := fun i => by linarith [sα.le_tsum i (fun j _ => hα j)]
  have hAβ : ∀ i, β i ≤ A := fun i => by linarith [sβ.le_tsum i (fun j _ => hβ j)]
  have hr0 : (0 : ℝ) < 1 / (2 * A) := by positivity
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hr0] with x hx
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hx
  have hxA : |x| * A ≤ 1 / 2 := by
    have := (lt_div_iff₀ (by positivity : (0:ℝ) < 2 * A)).mp hx
    linarith
  have h1 := tprod_eq_exp_logSum hα sα hAα hxA
  have h2 := tprod_eq_exp_logSum hβ sβ hAβ (x := -x) (by rwa [abs_neg])
  have h2' : ∏' i, (1 - (β i : ℂ) * (x : ℂ)) = ((Real.exp (logSum β (-x)) : ℝ) : ℂ) := by
    rw [← h2]; congr 1; funext i; push_cast; ring
  rw [edreiFunction, h1, h2', expo, Real.exp_sub, Real.exp_add]
  push_cast
  ring

private lemma step1_klt {C₁ C₂ : ℝ} {k₁ k₂ : ℕ} {H₁ H₂ : ℝ → ℝ} (hC₁ : 0 < C₁)
    (c₁ : ContinuousAt H₁ 0) (c₂ : ContinuousAt H₂ 0) (h₀₁ : H₁ 0 = 0)
    (h : ∀ᶠ x in 𝓝 0, C₁ * x ^ k₁ * Real.exp (H₁ x) = C₂ * x ^ k₂ * Real.exp (H₂ x)) :
    ¬ k₁ < k₂ := by
  intro hk
  have hev : ∀ᶠ x in 𝓝[≠] (0:ℝ), C₁ * Real.exp (H₁ x) = C₂ * x ^ (k₂ - k₁) * Real.exp (H₂ x) := by
    filter_upwards [nhdsWithin_le_nhds h, self_mem_nhdsWithin] with x hx hx0
    have hxk : x ^ k₁ ≠ 0 := pow_ne_zero _ hx0
    have : x ^ k₂ = x ^ k₁ * x ^ (k₂ - k₁) := by rw [← pow_add]; congr 1; lia
    rw [this] at hx
    apply mul_left_cancel₀ hxk
    linear_combination hx
  have t1 : Tendsto (fun x => C₁ * Real.exp (H₁ x)) (𝓝[≠] 0) (𝓝 (C₁ * Real.exp (H₁ 0))) :=
    ((Real.continuous_exp.continuousAt.comp c₁).const_mul C₁).mono_left nhdsWithin_le_nhds
  have t2 : Tendsto (fun x => C₂ * x ^ (k₂ - k₁) * Real.exp (H₂ x)) (𝓝[≠] 0)
      (𝓝 (C₂ * 0 ^ (k₂ - k₁) * Real.exp (H₂ 0))) := by
    refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
    exact ((continuousAt_const.mul (continuousAt_id.pow _)).mul
      (Real.continuous_exp.continuousAt.comp c₂)).tendsto
  have := tendsto_nhds_unique (t1.congr' hev) t2
  rw [zero_pow (by lia), h₀₁] at this
  simp at this
  linarith

private lemma step1 {C₁ C₂ : ℝ} {k₁ k₂ : ℕ} {H₁ H₂ : ℝ → ℝ} (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (c₁ : ContinuousAt H₁ 0) (c₂ : ContinuousAt H₂ 0) (h₀₁ : H₁ 0 = 0) (h₀₂ : H₂ 0 = 0)
    (h : ∀ᶠ x in 𝓝 0, C₁ * x ^ k₁ * Real.exp (H₁ x) = C₂ * x ^ k₂ * Real.exp (H₂ x)) :
    C₁ = C₂ ∧ k₁ = k₂ ∧ H₁ =ᶠ[𝓝 0] H₂ := by
  have hk : k₁ = k₂ := by
    have a := step1_klt hC₁ c₁ c₂ h₀₁ h
    have b := step1_klt hC₂ c₂ c₁ h₀₂ (h.mono fun x hx => hx.symm)
    lia
  subst hk
  have hev : ∀ᶠ x in 𝓝[≠] (0:ℝ), C₁ * Real.exp (H₁ x) = C₂ * Real.exp (H₂ x) := by
    filter_upwards [nhdsWithin_le_nhds h, self_mem_nhdsWithin] with x hx hx0
    have hxk : x ^ k₁ ≠ 0 := pow_ne_zero _ hx0
    apply mul_left_cancel₀ hxk
    linear_combination hx
  have t1 : Tendsto (fun x => C₁ * Real.exp (H₁ x)) (𝓝[≠] 0) (𝓝 (C₁ * Real.exp (H₁ 0))) :=
    ((Real.continuous_exp.continuousAt.comp c₁).const_mul C₁).mono_left nhdsWithin_le_nhds
  have t2 : Tendsto (fun x => C₂ * Real.exp (H₂ x)) (𝓝[≠] 0) (𝓝 (C₂ * Real.exp (H₂ 0))) :=
    ((Real.continuous_exp.continuousAt.comp c₂).const_mul C₂).mono_left nhdsWithin_le_nhds
  have hC : C₁ = C₂ := by
    simpa only [h₀₁, h₀₂, Real.exp_zero, mul_one] using
      tendsto_nhds_unique (t1.congr' hev) t2
  subst C₂
  refine ⟨rfl, rfl, ?_⟩
  have hev' := eventually_nhdsWithin_iff.mp hev
  filter_upwards [hev'] with x hx
  by_cases hx0 : x = 0
  · rw [hx0, h₀₁, h₀₂]
  · have := hx hx0
    exact Real.exp_injective (mul_left_cancel₀ hC₁.ne' this)

/-- **Uniqueness of the Edrei parameters.** If two canonical functions with nonnegative
`α, β`, positive `C`, and summable `α, β` agree on a neighbourhood of `0`, then `C`,
`k`, and `γ` agree. The multisets of nonzero `α`'s and of nonzero `β`'s also agree. -/
theorem params_eq_of_edreiFunction_eq {C₁ C₂ γ₁ γ₂ : ℝ} {k₁ k₂ : ℕ}
    {α₁ β₁ α₂ β₂ : ℕ → ℝ}
    (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (hα₁ : ∀ i, 0 ≤ α₁ i) (hβ₁ : ∀ i, 0 ≤ β₁ i)
    (hα₂ : ∀ i, 0 ≤ α₂ i) (hβ₂ : ∀ i, 0 ≤ β₂ i)
    (sα₁ : Summable α₁) (sβ₁ : Summable β₁)
    (sα₂ : Summable α₂) (sβ₂ : Summable β₂)
    (h : ∀ᶠ z in 𝓝 (0 : ℂ),
      edreiFunction C₁ γ₁ k₁ α₁ β₁ z = edreiFunction C₂ γ₂ k₂ α₂ β₂ z) :
    C₁ = C₂ ∧ k₁ = k₂ ∧ γ₁ = γ₂ ∧
      (∀ t : ℝ, 0 < t → Set.encard {i | α₁ i = t} = Set.encard {i | α₂ i = t}) ∧
      (∀ t : ℝ, 0 < t → Set.encard {i | β₁ i = t} = Set.encard {i | β₂ i = t}) := by
  have hR1 := edreiFunction_real (C := C₁) (γ := γ₁) (k := k₁) hα₁ hβ₁ sα₁ sβ₁
  have hR2 := edreiFunction_real (C := C₂) (γ := γ₂) (k := k₂) hα₂ hβ₂ sα₂ sβ₂
  have hc : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝 0) (𝓝 0) := by
    simpa using Complex.continuous_ofReal.tendsto 0
  have hreal : ∀ᶠ x : ℝ in 𝓝 0, C₁ * x ^ k₁ * Real.exp (expo γ₁ α₁ β₁ x) =
      C₂ * x ^ k₂ * Real.exp (expo γ₂ α₂ β₂ x) := by
    filter_upwards [hc.eventually h, hR1, hR2] with x hx h1 h2
    rw [h1, h2] at hx
    exact_mod_cast hx
  have P1 := expo_hasFPowerSeriesAt (γ := γ₁) hα₁ hβ₁ sα₁ sβ₁
  have P2 := expo_hasFPowerSeriesAt (γ := γ₂) hα₂ hβ₂ sα₂ sβ₂
  have z1 : expo γ₁ α₁ β₁ 0 = 0 := by simp [expo, logSum]
  have z2 : expo γ₂ α₂ β₂ 0 = 0 := by simp [expo, logSum]
  obtain ⟨hC, hk, hE⟩ := step1 hC₁ hC₂ P1.continuousAt P2.continuousAt z1 z2 hreal
  have hp := P1.eq_formalMultilinearSeries (P2.congr hE.symm)
  have hcoef : ∀ n, coef γ₁ α₁ β₁ n = coef γ₂ α₂ β₂ n := by
    intro n
    have := congrArg (fun p => p n (fun _ => (1 : ℝ))) hp
    simpa [FormalMultilinearSeries.ofScalars_apply_eq] using this
  have heven : ∀ j, psum β₁ (2 * j + 2) + psum α₂ (2 * j + 2) =
      psum β₂ (2 * j + 2) + psum α₁ (2 * j + 2) := by
    intro j
    have := hcoef (2 * j + 1 + 1)
    simp only [coef] at this
    rw [ite_eq_right (by lia), ite_eq_right (by lia)] at this
    have hpow : (-1 : ℝ) ^ (2 * j + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    rw [hpow] at this
    have hne : ((2 * j + 1 : ℕ) : ℝ) + 1 ≠ 0 := by positivity
    rw [add_zero, add_zero, div_left_inj' hne, show 2 * j + 1 + 1 = 2 * j + 2 by ring] at this
    linarith
  have hodd : ∀ j, psum α₁ (2 * j + 3) + psum β₁ (2 * j + 3) =
      psum α₂ (2 * j + 3) + psum β₂ (2 * j + 3) := by
    intro j
    have := hcoef (2 * j + 2 + 1)
    simp only [coef] at this
    rw [ite_eq_right (by lia), ite_eq_right (by lia)] at this
    have hpow : (-1 : ℝ) ^ (2 * j + 2) = 1 := by rw [pow_add, pow_mul]; norm_num
    rw [hpow] at this
    have hne : ((2 * j + 2 : ℕ) : ℝ) + 1 ≠ 0 := by positivity
    rw [add_zero, add_zero, div_left_inj' hne, show 2 * j + 2 + 1 = 2 * j + 3 by ring] at this
    linarith
  have ME := moment_unique hβ₁ hα₂ hβ₂ hα₁ sβ₁ sα₂ sβ₂ sα₁ (fun j => 2 * j + 2)
    (fun a b hab => by simp only; lia) (fun j => by lia) heven
  have MO := moment_unique hα₁ hβ₁ hα₂ hβ₂ sα₁ sβ₁ sα₂ sβ₂ (fun j => 2 * j + 3)
    (fun a b hab => by simp only; lia) (fun j => by lia) hodd
  have hcnt : ∀ t, 0 < t → cnt α₁ t = cnt α₂ t ∧ cnt β₁ t = cnt β₂ t := by
    intro t ht
    have h1 := ME t ht
    have h2 := MO t ht
    lia
  have hsum : ∀ {u v : ℕ → ℝ}, (∀ i, 0 ≤ u i) → (∀ i, 0 ≤ v i) → Summable u → Summable v →
      (∀ t, 0 < t → cnt u t = cnt v t) → psum u 1 = psum v 1 := by
    intro u v hu hv su sv huv
    have A : HasSum (fun t => (cnt u t : ℝ) * t ^ 1) (psum u 1) :=
      hasSum_cnt (u := u) (fun t => t ^ 1) (summable_pow_of_nonneg (m := 1) hu su le_rfl)
    have B : HasSum (fun t => (cnt v t : ℝ) * t ^ 1) (psum v 1) :=
      hasSum_cnt (u := v) (fun t => t ^ 1) (summable_pow_of_nonneg (m := 1) hv sv le_rfl)
    have hfun : (fun t => (cnt u t : ℝ) * t ^ 1) = (fun t => (cnt v t : ℝ) * t ^ 1) := by
      funext t
      rcases lt_trichotomy t 0 with ht | ht | ht
      · rw [cnt_neg hu ht, cnt_neg hv ht]
      · simp [ht]
      · rw [huv t ht]
    rw [hfun] at A
    exact A.unique B
  have hγ : γ₁ = γ₂ := by
    have := hcoef 1
    simp only [coef] at this
    rw [hsum hα₁ hα₂ sα₁ sα₂ (fun t ht => (hcnt t ht).1),
      hsum hβ₁ hβ₂ sβ₁ sβ₂ (fun t ht => (hcnt t ht).2)] at this
    simpa using this
  refine ⟨hC, hk, hγ, fun t ht => ?_, fun t ht => ?_⟩
  · rw [encard_eq_cnt sα₁ ht, encard_eq_cnt sα₂ ht, (hcnt t ht).1]
  · rw [encard_eq_cnt sβ₁ ht, encard_eq_cnt sβ₂ ht, (hcnt t ht).2]

end Complex.EdreiThoma

