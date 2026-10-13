import RealRooted.Mathlib.Analysis.Complex.Polynomial.Szasz

open Complex

noncomputable section

namespace MvPolynomial

/-! Definitions. -/

variable {σ : Type*} [Fintype σ]

/-- Generalized Jensen multiplier
`J(α, β) = (β)_α β^{-α} = ∏ i, (β i)! / (β i - α i)! / (β i)^(α i)`
(it is `0` when `α ≰ β`, and `1` for `β i = α i = 0`). -/
def jensen (α β : σ →₀ ℕ) : ℝ :=
  ∏ i, ((β i).descFactorial (α i) : ℝ) / (β i : ℝ) ^ (α i)

/-- The Jensen-multiplier operator `z^α ↦ J(α, β) z^α`. -/
def jensenOp (β : σ →₀ ℕ) (f : MvPolynomial σ ℂ) : MvPolynomial σ ℂ :=
  ∑ α ∈ f.support, MvPolynomial.monomial α ((jensen α β : ℂ) * f.coeff α)

/-- The constant `A` of Borcea–Brändén, Invent. Math. 177 (2009), Lemma 5.4. -/
def szaszA (f : MvPolynomial σ ℂ) : ℝ :=
  Real.sqrt (3 * (∑ i, ‖f.coeff (Finsupp.single i 1)‖) ^ 2 +
    2 * ∑ i, ∑ j, ‖f.coeff (Finsupp.single i 1 + Finsupp.single j 1)‖)

/-- The constant `C` of Borcea–Brändén, Theorem 5.5. -/
def szaszC (f : MvPolynomial σ ℂ) : ℝ :=
  6 * Real.exp 1 ^ 2 * (∑ i, ‖f.coeff (Finsupp.single i 1)‖) ^ 2 +
    4 * Real.exp 1 ^ 2 * ∑ i, ∑ j, ‖f.coeff (Finsupp.single i 1 + Finsupp.single j 1)‖

/-! Auxiliary lemmas. -/

open Polynomial in
/-- AM–GM in the form `(∏ x_j)` ≤ `(∑ x_j / k)^k`. -/
private lemma amgm_fin {k : ℕ} (x : Fin k → ℝ) (hx : ∀ j, 0 ≤ x j) :
    ∏ j, x j ≤ ((∑ j, x j) / k) ^ k := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have h := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ => (1 / k : ℝ)) x
    (fun _ _ => by positivity) (by simp [Finset.card_univ]; field_simp) (fun j _ => hx j)
  have h2 : ∏ j, x j = (∏ j, x j ^ (1 / k : ℝ)) ^ k := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hx j)]
    field_simp; simp
  rw [h2]
  have h3 : ∑ j, (1 / k : ℝ) * x j = (∑ j, x j) / k := by
    rw [← Finset.mul_sum]; ring
  rw [← h3]
  exact pow_le_pow_left₀ (Finset.prod_nonneg fun j _ => by have := hx j; positivity) h k

open Polynomial in
/-- Coefficients of `∏ (1 + ξ_j X)`. -/
private lemma coeff_prod_one_add {k : ℕ} (ξ : Fin k → ℂ) (d : ℕ) :
    (∏ j, (1 + Polynomial.C (ξ j) * Polynomial.X)).coeff d =
      ∑ t ∈ Finset.powersetCard d (Finset.univ : Finset (Fin k)), ∏ j ∈ t, ξ j := by
  rw [Finset.prod_one_add, Polynomial.finsetSum_coeff]
  have : ∀ t : Finset (Fin k),
      (∏ j ∈ t, Polynomial.C (ξ j) * Polynomial.X).coeff d =
      if t.card = d then ∏ j ∈ t, ξ j else 0 := by
    intro t
    rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_const, Polynomial.coeff_C_mul_X_pow]
    simp only [eq_comm]
  simp_rw [this]
  rw [Finset.powersetCard_eq_filter, Finset.sum_filter]

private lemma sum_powersetCard_two {k : ℕ} (ξ : Fin k → ℂ) :
    ∑ t ∈ Finset.powersetCard 2 (Finset.univ : Finset (Fin k)), ∏ j ∈ t, ξ j =
      ∑ i, ∑ j ∈ Finset.Ioi i, ξ i * ξ j := by
  rw [Finset.sum_sigma']
  symm
  apply Finset.sum_bij (fun x _ => ({x.1, x.2} : Finset (Fin k)))
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_Ioi] at hx
    rw [Finset.mem_powersetCard]; exact ⟨Finset.subset_univ _, Finset.card_pair hx.2.ne⟩
  · rintro ⟨a, b⟩ hx ⟨c, d⟩ hy hxy
    simp only [Finset.mem_sigma, Finset.mem_Ioi, Finset.mem_univ, true_and] at hx hy hxy
    have h1 : a ∈ ({c, d} : Finset (Fin k)) := hxy ▸ by simp
    have h2 : b ∈ ({c, d} : Finset (Fin k)) := hxy ▸ by simp
    have h3 : c ∈ ({a, b} : Finset (Fin k)) := hxy.symm ▸ by simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2 h3
    have hac : a = c := by
      rcases h1 with h1 | h1
      · exact h1
      · rcases h3 with h3 | h3
        · exact h3.symm
        · subst h1 h3; exact absurd (hx.trans hy) (lt_irrefl _)
    subst hac
    have hbd : b = d := by
      rcases h2 with h2 | h2
      · subst h2; exact absurd hx (lt_irrefl _)
      · exact h2
    subst hbd
    rfl
  · intro t ht
    rw [Finset.mem_powersetCard] at ht
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 ht.2
    rcases lt_or_gt_of_ne hxy with h | h
    · exact ⟨⟨x, y⟩, by simp [h], rfl⟩
    · exact ⟨⟨y, x⟩, by simp [h], Finset.pair_comm _ _⟩
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_Ioi] at hx
    rw [Finset.prod_pair hx.2.ne]

open Polynomial in
/-- Factorization of a polynomial with constant term `1`. -/
private lemma exists_prod_one_add (g : ℂ[X]) (h0 : g.coeff 0 = 1) :
    ∃ ξ : Fin g.natDegree → ℂ,
      g = ∏ j, (1 + Polynomial.C (ξ j) * Polynomial.X) := by
  have hg0 : g ≠ 0 := by rintro rfl; simp at h0
  have hcard : g.roots.card = g.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hfac := C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  have hroots_ne : ∀ r ∈ g.roots, r ≠ 0 := by
    intro r hr h; subst h
    rw [mem_roots hg0, IsRoot, ← coeff_zero_eq_eval_zero, h0] at hr; exact one_ne_zero hr
  set s := g.roots with hs
  set Q := (s.map (fun r => 1 + Polynomial.C (-r⁻¹) * Polynomial.X)).prod with hQ
  have h1 : (s.map (fun r => Polynomial.X - Polynomial.C r)).prod =
      Polynomial.C (s.map (fun r => -r)).prod * Q := by
    rw [hQ, map_multiset_prod, Multiset.map_map, ← Multiset.prod_map_mul]
    congr 1
    apply Multiset.map_congr rfl
    intro r hr
    simp only [Function.comp_apply]
    rw [mul_add, mul_one, ← mul_assoc, ← Polynomial.C_mul]
    have : -r * -r⁻¹ = 1 := by rw [neg_mul_neg, mul_inv_cancel₀ (hroots_ne r hr)]
    rw [this, Polynomial.C_1, one_mul, Polynomial.C_neg]
    ring
  have hQ0 : Q.coeff 0 = 1 := by
    rw [coeff_zero_eq_eval_zero, hQ, eval_multiset_prod, Multiset.map_map]
    simp
  have hgQ : g = Polynomial.C (g.leadingCoeff * (s.map (fun r => -r)).prod) * Q := by
    conv_lhs => rw [← hfac]
    rw [h1, Polynomial.C_mul, mul_assoc]
  have hc : g.leadingCoeff * (s.map (fun r => -r)).prod = 1 := by
    have := congrArg (fun p => p.coeff 0) hgQ
    simp only [Polynomial.coeff_C_mul, hQ0, mul_one, h0] at this
    exact this.symm
  rw [hc, Polynomial.C_1, one_mul] at hgQ
  obtain ⟨n, hn⟩ : ∃ n, g.natDegree = n := ⟨_, rfl⟩
  rw [hn]
  set l := s.toList with hl
  have hlen : l.length = n := by rw [hl, Multiset.length_toList, hcard, hn]
  subst hlen
  refine ⟨fun j => -(l[(j : ℕ)]'j.2)⁻¹, ?_⟩
  have := Fin.prod_univ_fun_getElem l
    (fun r => 1 + Polynomial.C (-r⁻¹) * Polynomial.X)
  refine hgQ.trans (Eq.trans ?_ this.symm)
  rw [hQ]
  conv_lhs => rw [← Multiset.coe_toList s]
  rw [Multiset.map_coe, Multiset.prod_coe]

open Polynomial in
/-- Univariate coefficient bound. -/
private lemma univ_coeff_bound (g : ℂ[X]) (h0 : g.coeff 0 = 1)
    (hs : ∀ z : ℂ, 0 < z.im → g.eval z ≠ 0) {A : ℝ} (hA : 0 ≤ A)
    (hc : 3 * ‖g.coeff 1‖ ^ 2 + 2 * ‖g.coeff 2‖ ≤ A ^ 2) :
    ‖g.coeff g.natDegree‖ ≤
      (Real.sqrt (g.natDegree : ℝ))⁻¹ ^ g.natDegree * A ^ g.natDegree := by
  obtain ⟨ξ, hξ⟩ := exists_prod_one_add g h0
  have key : ∀ d, g.coeff d =
      ∑ t ∈ Finset.powersetCard d (Finset.univ : Finset (Fin g.natDegree)), ∏ j ∈ t, ξ j :=
    fun d => by rw [← coeff_prod_one_add ξ d, ← hξ]
  have him : ∀ j, (ξ j).im ≤ 0 :=
    Complex.im_nonpos_of_prod_one_add_ne_zero ξ (fun z hz => by
    have := hs z hz
    rw [hξ, Polynomial.eval_prod] at this
    simpa using this)
  have hsq := Complex.sum_norm_sq_le_of_im_nonpos ξ him
  have hc1 : g.coeff 1 = ∑ j, ξ j := by
    rw [key, Finset.powersetCard_one, Finset.sum_map]; simp
  have hc2 : g.coeff 2 = ∑ i, ∑ j ∈ Finset.Ioi i, ξ i * ξ j := by
    rw [key, sum_powersetCard_two]
  have hck : g.coeff g.natDegree = ∏ j, ξ j := by
    have h := Finset.powersetCard_self (Finset.univ : Finset (Fin g.natDegree))
    rw [Finset.card_univ, Fintype.card_fin] at h
    rw [key, h, Finset.sum_singleton]
  rw [← hc1, ← hc2] at hsq
  have hS : ∑ j, ‖ξ j‖ ^ 2 ≤ A ^ 2 := hsq.trans hc
  have hP : (∏ j, ‖ξ j‖) ^ 2 ≤ (A ^ 2 / g.natDegree) ^ g.natDegree := by
    rw [← Finset.prod_pow]
    refine (amgm_fin (fun j => ‖ξ j‖ ^ 2) (fun j => by positivity)).trans ?_
    gcongr
  rw [hck, norm_prod, ← mul_pow]
  refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 ?_
  refine hP.trans (le_of_eq ?_)
  rw [← pow_mul, mul_comm g.natDegree 2, pow_mul, mul_pow, inv_pow, Real.sq_sqrt (by positivity)]
  ring

/-- The diagonal substitution `z_i = t`. -/
private def diag (p : MvPolynomial σ ℂ) : Polynomial ℂ :=
  MvPolynomial.aeval (fun _ => Polynomial.X) p

omit [Fintype σ] in
private lemma eval_diag (p : MvPolynomial σ ℂ) (t : ℂ) :
    (diag p).eval t = MvPolynomial.eval (fun _ => t) p := by
  rw [diag]
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

private lemma coeff_diag (p : MvPolynomial σ ℂ) (s : Finset (σ →₀ ℕ))
    (hs : p.support ⊆ s) (d : ℕ) :
    (diag p).coeff d = ∑ α ∈ s with ∑ i, α i = d, p.coeff α := by
  classical
  conv_lhs => rw [diag, MvPolynomial.as_sum p, map_sum]
  rw [Polynomial.finsetSum_coeff]
  have : ∀ α : σ →₀ ℕ,
      (MvPolynomial.aeval (fun _ => (Polynomial.X : Polynomial ℂ))
        (MvPolynomial.monomial α (p.coeff α))).coeff d =
          if ∑ i, α i = d then p.coeff α else 0 := by
    intro α
    rw [MvPolynomial.aeval_monomial, Finsupp.prod_pow, Finset.prod_pow_eq_pow_sum]
    rw [Polynomial.algebraMap_eq, Polynomial.coeff_C_mul_X_pow]
    simp only [eq_comm]
  simp_rw [this]
  rw [← Finset.sum_filter]
  apply Finset.sum_subset
  · intro α; simp only [Finset.mem_filter]; exact fun h => ⟨hs h.1, h.2⟩
  · intro α h1 h2
    simp only [Finset.mem_filter, not_and] at h1 h2
    by_contra hc
    exact h2 (MvPolynomial.mem_support_iff.2 hc) h1.2

lemma coeff_jensenOp (β α : σ →₀ ℕ) (f : MvPolynomial σ ℂ) :
    (jensenOp β f).coeff α = (jensen α β : ℂ) * f.coeff α := by
  classical
  rw [jensenOp, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.1 h, mul_zero]

private lemma support_jensenOp (β : σ →₀ ℕ) (f : MvPolynomial σ ℂ) :
    (jensenOp β f).support ⊆ f.support := by
  intro α hα
  rw [MvPolynomial.mem_support_iff, coeff_jensenOp] at hα
  rw [MvPolynomial.mem_support_iff]
  intro h; exact hα (by rw [h, mul_zero])

private lemma jensen_nonneg (α β : σ →₀ ℕ) : 0 ≤ jensen α β := by
  exact Finset.prod_nonneg fun i _ => by positivity

private lemma jensen_le_one (α β : σ →₀ ℕ) : jensen α β ≤ 1 := by
  apply Finset.prod_le_one₀ (fun i _ => by positivity)
  intro i _
  rcases Nat.eq_zero_or_pos (β i) with h | h
  · rcases Nat.eq_zero_or_pos (α i) with h' | h'
    · simp [h, h']
    · simp [h, Nat.descFactorial_of_lt h']
  · rw [div_le_one (by positivity)]
    exact_mod_cast Nat.descFactorial_le_pow _ _

private lemma le_of_jensen_ne_zero {α β : σ →₀ ℕ}
    (h : jensen α β ≠ 0) : α ≤ β := by
  intro i
  by_contra hi
  push Not at hi
  apply h
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [Nat.descFactorial_of_lt hi]

private lemma jensen_self_mul (β : σ →₀ ℕ) :
    jensen β β * ∏ i, ((β i : ℝ) ^ (β i) / ((β i).factorial : ℝ)) = 1 := by
  rw [jensen, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro i _
  rw [Nat.descFactorial_self]
  have h1 : ((β i).factorial : ℝ) ≠ 0 := by positivity
  rcases Nat.eq_zero_or_pos (β i) with h | h
  · simp [h]
  · have h2 : (β i : ℝ) ^ (β i) ≠ 0 := by positivity
    field_simp

private lemma eq_of_le_of_sum_eq {α β : σ →₀ ℕ} (h : α ≤ β)
    (hs : ∑ i, α i = ∑ i, β i) : α = β := by
  ext i
  by_contra hne
  have hlt : α i < β i := lt_of_le_of_ne (h i) hne
  have : ∑ j, α j < ∑ j, β j :=
    Finset.sum_lt_sum (fun j _ => h j) ⟨i, Finset.mem_univ _, hlt⟩
  lia

private lemma exists_single_of_sum_eq_succ {α : σ →₀ ℕ} {n : ℕ}
    (h : ∑ i, α i = n + 1) :
    ∃ i, ∃ α' : σ →₀ ℕ, α = Finsupp.single i 1 + α' ∧ ∑ i, α' i = n := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
    by_contra hc; push Not at hc; simp [hc] at h
  refine ⟨i, α - Finsupp.single i 1, ?_, ?_⟩
  · rw [add_tsub_cancel_of_le]
    rw [Finsupp.single_le_iff]; lia
  · have : ∀ j,
        (α - Finsupp.single i 1 : σ →₀ ℕ) j +
          (Finsupp.single i 1 : σ →₀ ℕ) j = α j := by
      intro j
      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply]
      split_ifs with hj <;> subst_vars <;> lia
    have h2 := Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => this j)
    have h3 : ∑ j, (Finsupp.single i 1 : σ →₀ ℕ) j = 1 := by simp [Finsupp.single_apply]
    rw [Finset.sum_add_distrib, h, h3] at h2
    lia

private lemma exists_single_of_sum_eq_one {α : σ →₀ ℕ} (h : ∑ i, α i = 1) :
    ∃ i, α = Finsupp.single i 1 := by
  obtain ⟨i, α', rfl, h'⟩ := exists_single_of_sum_eq_succ (n := 0) h
  have : α' = 0 := by
    ext j
    have := Finset.single_le_sum (fun j _ => Nat.zero_le (α' j)) (Finset.mem_univ j)
    simp only [Finsupp.coe_zero, Pi.zero_apply]; lia
  exact ⟨i, by rw [this, add_zero]⟩

private lemma exists_pair_of_sum_eq_two {α : σ →₀ ℕ} (h : ∑ i, α i = 2) :
    ∃ i j, α = Finsupp.single i 1 + Finsupp.single j 1 := by
  obtain ⟨i, α', rfl, h'⟩ := exists_single_of_sum_eq_succ (n := 1) h
  obtain ⟨j, rfl⟩ := exists_single_of_sum_eq_one h'
  exact ⟨i, j, rfl⟩

private lemma sum_half_pow_le (S : Finset (σ →₀ ℕ)) :
    ∑ α ∈ S, (1 / 2 : ℝ) ^ (∑ i, α i) ≤ 2 ^ Fintype.card σ := by
  classical
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ α ∈ S, ∀ i, α i < N := by
    refine ⟨∑ α ∈ S, ∑ i, α i + 1, fun α hα i => ?_⟩
    have h1 : α i ≤ ∑ j, α j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    have h2 : ∑ j, α j ≤ ∑ α ∈ S, ∑ i, α i :=
      Finset.single_le_sum (f := fun α : σ →₀ ℕ => ∑ i, α i)
        (fun _ _ => Nat.zero_le _) hα
    lia
  let e : (σ →₀ ℕ) → (σ → ℕ) := fun α => ⇑α
  have he : Set.InjOn e S := fun a _ b _ h => DFunLike.coe_injective h
  calc
    ∑ α ∈ S, (1 / 2 : ℝ) ^ (∑ i, α i) =
        ∑ x ∈ S.image e, ∏ i, (1 / 2 : ℝ) ^ (x i) := by
        rw [Finset.sum_image he]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [Finset.prod_pow_eq_pow_sum]
    _ ≤ ∑ x ∈ Fintype.piFinset (fun _ : σ => Finset.range N),
        ∏ i, (1 / 2 : ℝ) ^ (x i) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx
          obtain ⟨α, hα, rfl⟩ := Finset.mem_image.1 hx
          simp only [Fintype.mem_piFinset, Finset.mem_range]
          exact hN α hα
        · intros; positivity
    _ = ∏ _i : σ, ∑ m ∈ Finset.range N, (1 / 2 : ℝ) ^ m := by
        rw [Finset.prod_univ_sum]
    _ ≤ ∏ _i : σ, (2 : ℝ) := Finset.prod_le_prod₀ (fun _ _ => by positivity)
          (fun _ _ => sum_geometric_two_le N)
    _ = 2 ^ Fintype.card σ := by simp

private lemma pow_le_exp_sq (k : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    ((Real.sqrt (k : ℝ))⁻¹ * R) ^ k ≤ Real.exp (R ^ 2 / 2) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp only [CharP.cast_eq_zero, Real.sqrt_zero, inv_zero, zero_mul, pow_zero,
      Real.one_le_exp_iff]
    positivity
  set t := (Real.sqrt (k : ℝ))⁻¹ * R with ht
  have ht0 : 0 ≤ t := by positivity
  have h1 : t ≤ Real.exp (t ^ 2 / 2) := by
    have := Real.add_one_le_exp (t ^ 2 / 2)
    nlinarith [sq_nonneg (t - 1)]
  have hkt : (k : ℝ) * t ^ 2 = R ^ 2 := by
    rw [ht, mul_pow, inv_pow, Real.sq_sqrt (by positivity)]
    field_simp
  calc t ^ k ≤ Real.exp (t ^ 2 / 2) ^ k := by gcongr
    _ = Real.exp (R ^ 2 / 2) := by
      rw [← Real.exp_nat_mul, ← hkt]; ring_nf

private lemma prod_pow_div_factorial_le (β : σ →₀ ℕ) :
    ∏ i, ((β i : ℝ) ^ (β i) / ((β i).factorial : ℝ)) ≤ Real.exp 1 ^ (∑ i, β i) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod₀ (fun i _ => by positivity)
  intro i _
  rw [Real.exp_one_pow]
  exact Real.pow_div_factorial_le_exp _ (by positivity) _

omit [Fintype σ] in
private lemma sum_le_sum_of_forall_exists {ι : Type*} (T : Finset (σ →₀ ℕ))
    (e : ι → σ →₀ ℕ)
    (s : Finset ι) (h : ∀ α ∈ T, ∃ i ∈ s, e i = α)
    (w : (σ →₀ ℕ) → ℝ) (hw : ∀ α, 0 ≤ w α) :
    ∑ α ∈ T, w α ≤ ∑ i ∈ s, w (e i) := by
  classical
  calc ∑ α ∈ T, w α ≤ ∑ α ∈ s.image e, w α := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro α hα
          obtain ⟨i, hi, rfl⟩ := h α hα
          exact Finset.mem_image_of_mem _ hi
        · intros; exact hw _
    _ ≤ _ := Finset.sum_image_le_of_nonneg (fun _ _ => hw _)

private lemma szaszA_nonneg (f : MvPolynomial σ ℂ) : 0 ≤ szaszA f := Real.sqrt_nonneg _

private lemma szaszC_eq (f : MvPolynomial σ ℂ) :
    szaszC f = 2 * Real.exp 1 ^ 2 * szaszA f ^ 2 := by
  rw [szaszA, Real.sq_sqrt (by positivity), szaszC]; ring

/-- **Coefficient bound (Borcea–Brändén, arXiv:0809.0401, Lemma 5.4).**
Let `f = 1 + ∑ a(β) z^β` be such that every
Jensen-multiplier image `J_β f` is stable (in the paper `f` is stable and this is its
Lemma 5.2).  Then
`|a(β)| ≤ |β|^{-|β|/2} (β^β / β!) A^{|β|}`.

Proof: if `a(β) ≠ 0`, `β ≠ 0`, put all variables equal to `t` in `J_β f`:
the univariate polynomial
`g(t) = ∑_{α ≤ β} J(α,β) a(α) t^{|α|}` is stable, has constant term `1`,
degree `k = |β|` and leading
coefficient `(β!/β^β) a(β)`.  Its linear coefficient is
`∑_{i : β_i ≥ 1} a(e_i)` and its quadratic coefficient is
`∑_{i<j, β_iβ_j ≥ 1} a(e_i+e_j) + ∑_{β_i ≥ 2} (1 - 1/β_i) a(2e_i)`
(as `J(e_i,β)=1`,
`J(e_i+e_j,β)=1`, `J(2e_i,β) = 1 - 1/β_i`).  Factor `g = ∏ (1 + ξ_j t)`;
the `ξ_j` lie in the closed lower
half plane, so Szász gives `∑ ‖ξ_j‖² ≤ 3|a₁|² + 2|a₂| ≤ A²`, and AM–GM gives
`‖(β!/β^β) a(β)‖ = ∏ ‖ξ_j‖ ≤ (∑‖ξ_j‖²/k)^{k/2} ≤ A^k k^{-k/2}`. -/
theorem norm_coeff_le_of_forall_jensenOp_stable (f : MvPolynomial σ ℂ)
    (h0 : f.coeff 0 = 1)
    (hJ : ∀ (β : σ →₀ ℕ) (z : σ → ℂ),
      (∀ i, 0 < (z i).im) → MvPolynomial.eval z (jensenOp β f) ≠ 0)
    (β : σ →₀ ℕ) :
    ‖f.coeff β‖ ≤ (Real.sqrt ((∑ i, β i : ℕ) : ℝ))⁻¹ ^ (∑ i, β i) *
      (∏ i, ((β i : ℝ) ^ (β i) / ((β i).factorial : ℝ))) * szaszA f ^ (∑ i, β i) := by
  classical
  set k := ∑ i, β i with hk
  set P := ∏ i, ((β i : ℝ) ^ (β i) / ((β i).factorial : ℝ)) with hP
  have hPpos : 0 ≤ P := Finset.prod_nonneg fun i _ => by positivity
  by_cases ha : f.coeff β = 0
  · rw [ha, norm_zero]; have := szaszA_nonneg f; positivity
  set p := jensenOp β f with hp
  set g := diag p with hg
  have hcoeff : ∀ d, g.coeff d =
      ∑ α ∈ f.support with ∑ i, α i = d, (jensen α β : ℂ) * f.coeff α := by
    intro d
    rw [hg, coeff_diag p f.support (support_jensenOp β f) d]
    exact Finset.sum_congr rfl fun α _ => coeff_jensenOp β α f
  have hterm : ∀ α, (jensen α β : ℂ) * f.coeff α ≠ 0 → α ≤ β := by
    intro α h; apply le_of_jensen_ne_zero; intro h'; apply h; simp [h']
  have hsum_le : ∀ α : σ →₀ ℕ, α ≤ β → ∑ i, α i ≤ k := fun α h =>
    Finset.sum_le_sum fun i _ => h i
  have hJpos : 0 < jensen β β := by
    have h1 := jensen_self_mul β
    have h2 := jensen_nonneg β β
    rcases h2.lt_or_eq with h2 | h2
    · exact h2
    · rw [← h2, zero_mul] at h1; exact absurd h1 zero_ne_one
  have hgk : g.coeff k = (jensen β β : ℂ) * f.coeff β := by
    rw [hcoeff, Finset.sum_eq_single β]
    · intro α hα hne
      by_contra h
      exact hne (eq_of_le_of_sum_eq (hterm α h) (Finset.mem_filter.1 hα).2)
    · intro hβ
      exfalso; apply hβ
      simp only [Finset.mem_filter, MvPolynomial.mem_support_iff]
      exact ⟨ha, rfl⟩
  have hdeg : g.natDegree = k := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro d hd
      rw [hcoeff]
      apply Finset.sum_eq_zero
      intro α hα
      by_contra h
      have h1 := hsum_le α (hterm α h)
      have h2 := (Finset.mem_filter.1 hα).2
      have h3 : k < d := by exact_mod_cast hd
      lia
    · rw [hgk]; exact mul_ne_zero (by exact_mod_cast hJpos.ne') ha
  have h0g : g.coeff 0 = 1 := by
    rw [hcoeff, Finset.sum_eq_single 0]
    · simp [jensen, h0]
    · intro α hα hne
      exfalso; apply hne
      have h2 := (Finset.mem_filter.1 hα).2
      ext i
      have : α i ≤ ∑ j, α j :=
        Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
      simp only [Finsupp.coe_zero, Pi.zero_apply]
      lia
    · intro h
      exfalso; apply h
      simp [h0]
  have hs : ∀ z : ℂ, 0 < z.im → g.eval z ≠ 0 := fun z hz => by
    rw [hg, eval_diag]
    exact hJ β _ (fun _ => hz)
  have hnorm : ∀ d,
      ‖g.coeff d‖ ≤ ∑ α ∈ f.support with ∑ i, α i = d, ‖f.coeff α‖ := by
    intro d
    rw [hcoeff]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (jensen_nonneg α β)]
    exact mul_le_of_le_one_left (norm_nonneg _) (jensen_le_one α β)
  have hc1 : ‖g.coeff 1‖ ≤ ∑ i, ‖f.coeff (Finsupp.single i 1)‖ := by
    refine (hnorm 1).trans ?_
    refine (sum_le_sum_of_forall_exists _ (fun i => Finsupp.single i 1) Finset.univ ?_
      (fun α => ‖f.coeff α‖) (fun _ => norm_nonneg _))
    intro α hα
    obtain ⟨i, hi⟩ := exists_single_of_sum_eq_one (Finset.mem_filter.1 hα).2
    exact ⟨i, Finset.mem_univ _, hi.symm⟩
  have hc2 : ‖g.coeff 2‖ ≤
      ∑ i, ∑ j, ‖f.coeff (Finsupp.single i 1 + Finsupp.single j 1)‖ := by
    refine (hnorm 2).trans ?_
    rw [← Fintype.sum_prod_type']
    refine (sum_le_sum_of_forall_exists _
      (fun x : σ × σ => Finsupp.single x.1 1 + Finsupp.single x.2 1) Finset.univ ?_
      (fun α => ‖f.coeff α‖) (fun _ => norm_nonneg _))
    intro α hα
    obtain ⟨i, j, hij⟩ := exists_pair_of_sum_eq_two (Finset.mem_filter.1 hα).2
    exact ⟨(i, j), Finset.mem_univ _, hij.symm⟩
  have hc : 3 * ‖g.coeff 1‖ ^ 2 + 2 * ‖g.coeff 2‖ ≤ szaszA f ^ 2 := by
    rw [szaszA, Real.sq_sqrt (by positivity)]
    gcongr
  have key := univ_coeff_bound g h0g hs (szaszA_nonneg f) hc
  rw [hdeg, hgk, norm_mul, Complex.norm_real, Real.norm_of_nonneg hJpos.le] at key
  have hPJ : P * jensen β β = 1 := by rw [mul_comm]; exact jensen_self_mul β
  calc ‖f.coeff β‖ = P * (jensen β β * ‖f.coeff β‖) := by
        rw [← mul_assoc, hPJ, one_mul]
    _ ≤ P * ((Real.sqrt (k : ℝ))⁻¹ ^ k * szaszA f ^ k) := mul_le_mul_of_nonneg_left key hPpos
    _ = _ := by ring

/-- **Multivariate Szász growth bound (Borcea–Brändén, arXiv:0809.0401, Theorem 5.5).**
Under the same hypotheses,
`max {|f(z)| : |z_i| ≤ r} ≤ B e^{C r²}` with
`B = 2^{n-1} √(2e²-e)/(e-1)` (here we state the weaker
`2^n` to avoid the case `n = 0`) and `C = 6e²(∑|a(e_i)|)² + 4e² ∑_{i,j}|a(e_i+e_j)|`.

Proof: `|f(z)| ≤ ∑_β |a(β)| r^{|β|} ≤ ∑_k d(n,k) k^{-k/2} (A r)^k` with
`d(n,k) = ∑_{|β|=k} β^β/β! ≤ C(n+k-1,k) e^k ≤ 2^{n-1+k} e^k`
(use `β^β/β! ≤ e^{|β|}`, i.e.
`m^m/m! ≤ e^m`, and the number of `β` with `|β|=k` is `C(n+k-1,k)`).  With `R = 2eAr` and
`k^{-k/2} ≤ √((ek+1)e^{-k}) √(1/k!)`
(from `e^{-k} ≤ k!/k^k ≤ (ek+1)e^{-k}`) Cauchy–Schwarz gives
`∑_k k^{-k/2} R^k ≤ √(∑ (ek+1)e^{-k}) √(∑ R^{2k}/k!)`
`= (√(2e²-e)/(e-1)) e^{R²/2}`, and
`R²/2 = 2e²A²r² = C r²`. -/
theorem norm_eval_le_of_forall_jensenOp_stable (f : MvPolynomial σ ℂ)
    (h0 : f.coeff 0 = 1)
    (hJ : ∀ (β : σ →₀ ℕ) (z : σ → ℂ),
      (∀ i, 0 < (z i).im) → MvPolynomial.eval z (jensenOp β f) ≠ 0)
    {r : ℝ} (hr : 0 ≤ r)
    (z : σ → ℂ) (hz : ∀ i, ‖z i‖ ≤ r) :
    ‖MvPolynomial.eval z f‖ ≤
      (2 : ℝ) ^ (Fintype.card σ) *
        (Real.sqrt (2 * Real.exp 1 ^ 2 - Real.exp 1) / (Real.exp 1 - 1)) *
        Real.exp (szaszC f * r ^ 2) := by
  classical
  set A := szaszA f with hAdef
  have hA : 0 ≤ A := szaszA_nonneg f
  set R := 2 * Real.exp 1 * A * r with hRdef
  have hR : 0 ≤ R := by positivity
  have key : ∀ α : σ →₀ ℕ, ‖f.coeff α‖ * r ^ (∑ i, α i) ≤
      (1 / 2 : ℝ) ^ (∑ i, α i) * Real.exp (R ^ 2 / 2) := by
    intro α
    set k := ∑ i, α i with hk
    have h1 := norm_coeff_le_of_forall_jensenOp_stable f h0 hJ α
    have h2 := prod_pow_div_factorial_le α
    calc ‖f.coeff α‖ * r ^ k
        ≤ ((Real.sqrt (k : ℝ))⁻¹ ^ k *
            (∏ i, ((α i : ℝ) ^ (α i) / ((α i).factorial : ℝ))) * A ^ k) *
            r ^ k := by
          gcongr
      _ ≤ ((Real.sqrt (k : ℝ))⁻¹ ^ k * Real.exp 1 ^ k * A ^ k) * r ^ k := by gcongr
      _ = (1 / 2 : ℝ) ^ k * ((Real.sqrt (k : ℝ))⁻¹ * R) ^ k := by
        rw [hRdef, mul_pow, mul_pow, mul_pow, mul_pow]
        have : (1 / 2 : ℝ) ^ k * 2 ^ k = 1 := by rw [← mul_pow]; norm_num
        linear_combination (-(Real.sqrt (k : ℝ))⁻¹ ^ k * Real.exp 1 ^ k * A ^ k * r ^ k) * this
      _ ≤ (1 / 2 : ℝ) ^ k * Real.exp (R ^ 2 / 2) := by
        gcongr; exact pow_le_exp_sq k hR
  have hconst : 1 ≤ Real.sqrt (2 * Real.exp 1 ^ 2 - Real.exp 1) / (Real.exp 1 - 1) := by
    have he : 1 < Real.exp 1 := by
      have := Real.add_one_lt_exp (x := 1) one_ne_zero; linarith
    rw [le_div_iff₀ (by linarith), one_mul]
    apply Real.le_sqrt_of_sq_le
    nlinarith
  calc
    ‖MvPolynomial.eval z f‖ ≤
        ∑ α ∈ f.support, ‖f.coeff α‖ * r ^ (∑ i, α i) := by
        rw [MvPolynomial.eval_eq']
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ => ?_)
        rw [norm_mul, norm_prod]
        gcongr
        rw [← Finset.prod_pow_eq_pow_sum]
        gcongr with i
        rw [norm_pow]
        gcongr
        exact hz i
    _ ≤ ∑ α ∈ f.support, (1 / 2 : ℝ) ^ (∑ i, α i) * Real.exp (R ^ 2 / 2) :=
        Finset.sum_le_sum fun α _ => key α
    _ = (∑ α ∈ f.support, (1 / 2 : ℝ) ^ (∑ i, α i)) * Real.exp (R ^ 2 / 2) := by
        rw [Finset.sum_mul]
    _ ≤ 2 ^ Fintype.card σ * Real.exp (R ^ 2 / 2) := by
        gcongr; exact sum_half_pow_le _
    _ = 2 ^ Fintype.card σ * 1 * Real.exp (szaszC f * r ^ 2) := by
        rw [szaszC_eq, mul_one]
        congr 2
        rw [hRdef]; ring
    _ ≤ _ := by gcongr

end MvPolynomial
