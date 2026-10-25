module

public import RealRooted.Hadamard.Kostov.Eigen
public import RealRooted.Bezoutian.WronskianConverse
public import RealRooted.Wronskian.Successor.Interlacing

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted
namespace Kostov

/-- The polynomial `Q` is monic of degree `j` and `X * (X + 1) ^ (n - j - 2) * Q` equals
`monicPolynomial n v - monicPolynomial n 0` for a nonzero eigenvector `v` of `linearPart n` with
eigenvalue `eigenvalue n (j + 1)`. -/
def IsEigenpoly (n j : ℕ) (Q : ℝ[X]) : Prop :=
  Q.Monic ∧ Q.natDegree = j ∧
    ∃ v : Fin (n - 1) → ℝ, v ≠ 0 ∧
      monicPolynomial n v - monicPolynomial n 0 = X * (X + 1) ^ (n - j - 2) * Q ∧
      linearPart n v = eigenvalue n (j + 1) • v

/-! ### Real-rootedness of the Bernstein eigenpolynomials -/

/-- Pointwise convergence of the pre-images `F_r` towards `G_m`. -/
lemma tendsto_eval_eigen_combo (n m : ℕ) (hm : 2 ≤ m) (hmn : m ≤ n)
    (a : ℕ → ℝ) (ham1 : a m = 1)
    (y : ℝ) :
    Filter.Tendsto (fun r : ℕ => (∑ d ∈ Finset.Icc 2 m,
      (a d * (mu n m / mu n d) ^ r) • eigPoly n d).eval y) Filter.atTop
      (nhds ((eigPoly n m).eval y)) := by
  simp_rw [eval_finsetSum, eval_smul, smul_eq_mul]
  have hlim : (eigPoly n m).eval y = ∑ d ∈ Finset.Icc 2 m,
      (if d = m then a d * (eigPoly n d).eval y else 0) := by
    rw [Finset.sum_ite_eq', ite_eq_left (by simp; lia), ham1, one_mul]
  rw [hlim]
  refine tendsto_finsetSum _ fun d hd => ?_
  by_cases hdm : d = m
  · subst hdm
    simp only [ite_true, div_self (mu_pos n d hmn).ne', one_pow, mul_one]
    exact tendsto_const_nhds
  · rw [ite_eq_right hdm]
    have hd' : d < m := by simp at hd; lia
    have hq0 : 0 ≤ mu n m / mu n d :=
      div_nonneg (mu_pos n m hmn).le (mu_pos n d (by lia)).le
    have hq1 : mu n m / mu n d < 1 := by
      rw [div_lt_one (mu_pos n d (by lia))]
      exact mu_lt_of_lt n d m (by simp at hd; lia) hd' hmn
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul (a d)).mul_const
      ((eigPoly n d).eval y)
    simpa using this

/-- **All zeros of `G_m` are real.**  `G_m = X (X - 1) ∏ (X - z_i)` with `m - 2` (possibly
repeated) zeros `z_i ∈ [1/n, (n-1)/n]`.  Proved by a compactness argument from the
variation-diminishing property. -/
lemma eigPoly_eq_prod_closed (n m : ℕ) (hm : 2 ≤ m) (hmn : m ≤ n) :
    ∃ z : Fin (m - 2) → ℝ,
      (∀ i, z i ∈ Set.Icc (1 / (n : ℝ)) (((n - 1 : ℕ) : ℝ) / n)) ∧
      eigPoly n m = X * (X - C 1) * ∏ i, (X - C (z i)) := by
  have hn : 2 ≤ n := by lia
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by lia)
  set z : ℕ → ℝ := fun i => ((i : ℝ) + 3 / 2) / n with hz
  set F : ℝ[X] := X * (X - C 1) * ∏ i ∈ Finset.range (m - 2), (X - C (z i)) with hF
  have hFmon : F.Monic :=
    (monic_X.mul (monic_X_sub_C 1)).mul (monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _)
  have hFdeg : F.natDegree = m := by
    rw [hF, (monic_X.mul (monic_X_sub_C 1)).natDegree_mul
      (monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _), monic_X.natDegree_mul
      (monic_X_sub_C 1), natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]
    simp only [natDegree_X, natDegree_X_sub_C, Finset.sum_const, Finset.card_range, smul_eq_mul,
      mul_one]
    lia
  have hF0 : F.eval 0 = 0 := by simp [hF]
  have hF1 : F.eval 1 = 0 := by simp [hF]
  obtain ⟨a, hFa, ham⟩ := eig_expand n m hmn F hFdeg.le hF0 hF1
  have ham1 : a m = 1 := by
    rw [ham, ← hFdeg]; exact hFmon.leadingCoeff
  have hmud : ∀ d ∈ Finset.Icc 2 m, mu n d ≠ 0 := fun d hd =>
    (mu_pos n d (by simp at hd; lia)).ne'
  set Fr : ℕ → ℝ[X] := fun r =>
    ∑ d ∈ Finset.Icc 2 m, (a d * (mu n m / mu n d) ^ r) • eigPoly n d with hFr
  have hBFr : ∀ r, ((bernOp n) ^ r) (Fr r) = (mu n m) ^ r • F := by
    intro r
    rw [hFr, map_sum, hFa, Finset.smul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [map_smul, bernOp_pow_eigPoly n d (by simp at hd; lia) (by simp at hd; lia),
      smul_smul, smul_smul, div_pow]
    congr 1
    field_simp [pow_ne_zero r (hmud d hd)]
  have hFr0 : ∀ r, (Fr r).eval 0 = 0 := by
    intro r
    rw [hFr, eval_finsetSum]
    refine Finset.sum_eq_zero fun d hd => ?_
    rw [eval_smul, eigPoly_eval_zero n d (by simp at hd; lia) (by simp at hd; lia)]
    simp
  have hFr1 : ∀ r, (Fr r).eval 1 = 0 := by
    intro r
    rw [hFr, eval_finsetSum]
    refine Finset.sum_eq_zero fun d hd => ?_
    rw [eval_smul, eigPoly_eval_one n d (by simp at hd; lia) (by simp at hd; lia)]
    simp
  have hFrc : ∀ r k, (Fr r).coeff k =
      ∑ d ∈ Finset.Icc 2 m, a d * (mu n m / mu n d) ^ r * (eigPoly n d).coeff k := by
    intro r k
    simp [hFr, finsetSum_coeff, coeff_smul]
  have hFrdeg : ∀ r, (Fr r).natDegree ≤ m := by
    intro r
    refine natDegree_sum_le_of_forall_le _ _ fun d hd => ?_
    refine (natDegree_smul_le _ _).trans ?_
    rw [(eigPoly_spec n d (by simp at hd; lia) (by simp at hd; lia)).2.1]
    simp at hd; lia
  have hFrm : ∀ r, (Fr r).coeff m = 1 := by
    intro r
    rw [hFrc, Finset.sum_eq_single m]
    · rw [div_self (mu_pos n m hmn).ne', one_pow, eigPoly_coeff_self n m hm hmn, ham1]; ring
    · intro d hd hdm
      rw [coeff_eq_zero_of_natDegree_lt]
      · ring
      rw [(eigPoly_spec n d (by simp at hd; lia) (by simp at hd; lia)).2.1]
      simp at hd; lia
    · intro h; simp at h; lia
  have hFrd : ∀ r, (Fr r).natDegree = m := fun r =>
    natDegree_eq_of_le_of_coeff_ne_zero (hFrdeg r) (by rw [hFrm r]; exact one_ne_zero)
  have hFrmon : ∀ r, (Fr r).Monic := fun r => by
    rw [Monic, leadingCoeff, hFrd r, hFrm r]
  set s₀ := (Finset.range (m - 2)).image z with hs₀
  have hzinj : Set.InjOn z (Finset.range (m - 2)) := by
    intro i _ j _ h
    simp only [hz] at h
    field_simp at h
    exact_mod_cast (show (i : ℝ) = j by linarith)
  have hs₀c : s₀.card = m - 2 := by
    rw [hs₀, Finset.card_image_of_injOn hzinj, Finset.card_range]
  have hlt1 : ((n - 1 : ℕ) : ℝ) / n < 1 := by
    rw [div_lt_one hn0, Nat.cast_sub (by lia)]; simp
  -- each `F_r` has all its zeros real, in `[1/n, (n-1)/n]`
  have happrox : ∀ r, ∃ w : Fin (m - 2) → ℝ,
      (∀ i, w i ∈ Set.Icc (1 / (n : ℝ)) (((n - 1 : ℕ) : ℝ) / n)) ∧
      Fr r = X * (X - C 1) * ∏ i, (X - C (w i)) := by
    intro r
    have hne : ((bernOp n) ^ r) (Fr r) ≠ 0 := by
      rw [hBFr r]
      exact smul_ne_zero (pow_ne_zero _ (mu_pos n m hmn).ne') hFmon.ne_zero
    obtain ⟨s, hs, hs'⟩ := bernOp_pow_roots_le n hn r (Fr r) (hFr0 r) (hFr1 r) hne s₀ (by
      intro y hy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
      rw [Finset.mem_range] at hi
      refine ⟨?_, ?_, ?_⟩
      · rw [hBFr r, eval_smul, hF, eval_mul, eval_prod,
          Finset.prod_eq_zero (Finset.mem_range.mpr hi) (by simp)]
        simp
      · simp only [hz]
        exact div_lt_div_of_pos_right (by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]) hn0
      · simp only [hz]
        refine div_lt_div_of_pos_right ?_ hn0
        have : (i : ℝ) + 3 ≤ n := by exact_mod_cast (show i + 3 ≤ n by lia)
        rw [Nat.cast_sub (by lia)]
        push_cast
        linarith)
    obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq (show m - 2 ≤ s.card by lia)
    have h1t : (1 : ℝ) ∉ t := fun h => by linarith [(hs' 1 (hts h)).2.2]
    have h0t : (0 : ℝ) ∉ insert 1 t := by
      intro h
      rcases Finset.mem_insert.mp h with h | h
      · norm_num at h
      · have := (hs' 0 (hts h)).2.1
        have : (0 : ℝ) < 1 / n := by positivity
        linarith
    have hcard : (insert (0 : ℝ) (insert 1 t)).card = (Fr r).natDegree := by
      rw [Finset.card_insert_of_notMem h0t, Finset.card_insert_of_notMem h1t, htc, hFrd r]
      lia
    have hprod := monic_eq_prod_of_roots (Fr r) (hFrmon r) _ (by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hFr0 r
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hFr1 r
      · exact (hs' y (hts hy)).1) hcard
    rw [Finset.prod_insert h0t, Finset.prod_insert h1t, map_zero, sub_zero] at hprod
    set e := t.orderIsoOfFin htc
    refine ⟨fun i => (e i : ℝ), fun i => ?_, ?_⟩
    · obtain ⟨-, h2, h3⟩ := hs' _ (hts (e i).2)
      exact ⟨h2.le, h3.le⟩
    · rw [hprod, mul_assoc]
      congr 2
      rw [← Finset.prod_coe_sort t]
      exact (Fintype.prod_equiv e.toEquiv _ _ (fun _ => rfl)).symm
  choose zr hzr using happrox
  have hK : IsCompact (Set.pi Set.univ
      fun _ : Fin (m - 2) => Set.Icc (1 / (n : ℝ)) (((n - 1 : ℕ) : ℝ) / n)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨zs, hzs, φ, hφ, hlim⟩ := hK.tendsto_subseq (x := zr)
    (fun r => Set.mem_univ_pi.mpr (hzr r).1)
  refine ⟨zs, fun i => Set.mem_univ_pi.mp hzs i, ?_⟩
  refine Polynomial.funext fun y => ?_
  have h1 : Filter.Tendsto (fun r => (Fr (φ r)).eval y) Filter.atTop
      (nhds ((eigPoly n m).eval y)) :=
    (tendsto_eval_eigen_combo n m hm hmn a ham1 y).comp hφ.tendsto_atTop
  have h2 : Filter.Tendsto (fun r => (Fr (φ r)).eval y) Filter.atTop
      (nhds ((X * (X - C 1) * ∏ i, (X - C (zs i))).eval y)) := by
    have e : (fun r => (Fr (φ r)).eval y) =
        fun r => (X * (X - C 1) * ∏ i, (X - C (zr (φ r) i))).eval y :=
      funext fun r => by rw [(hzr (φ r)).2]
    rw [e]
    simp only [eval_mul, eval_X, eval_sub, eval_C, eval_prod]
    refine tendsto_const_nhds.mul (tendsto_finsetProd _ fun i _ => tendsto_const_nhds.sub ?_)
    exact ((continuous_apply i).tendsto zs).comp hlim
  exact tendsto_nhds_unique h1 h2

/-- Sign variations of the Bernstein coefficients of `B_n G` are bounded by zeros of `G` in
`(0,1)`. -/
lemma signVariations_coeffPoly_le (n : ℕ) (hn : 2 ≤ n) (G : ℝ[X]) (h0 : G.eval 0 = 0)
    (h1 : G.eval 1 = 0) :
    ∃ s : Finset ℝ, (coeffPoly n G).signVariations ≤ s.card ∧
      ∀ z ∈ s, G.eval z = 0 ∧ 0 < z ∧ z < 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by lia)
  set p := coeffPoly n G with hp_def
  have hx : StrictMono (fun k : ℕ => (k : ℝ) / n) := by
    intro a b hab
    exact div_lt_div_of_pos_right (by exact_mod_cast hab) hn0
  obtain ⟨s', hs'1, hs'2⟩ := signVariations_le_roots (fun z => G.eval z)
    (Polynomial.continuous G) _ hx 1 p.support.card p (n - 1) rfl (by
      intro k hk
      rw [hp_def, coeffPoly_coeff] at hk ⊢
      by_cases hkn : k ≤ n
      · rw [ite_eq_left hkn] at hk ⊢
        have hk0 : k ≠ 0 := by
          rintro rfl; simp [h0] at hk
        have hkn' : k ≠ n := by
          rintro rfl; simp [div_self hn0.ne', h1] at hk
        refine ⟨by lia, by lia, ?_⟩
        rw [sign_mul, sign_pos (show (0 : ℝ) < n.choose k by
          exact_mod_cast Nat.choose_pos hkn), mul_one]
      · rw [ite_eq_right hkn] at hk; exact absurd rfl hk)
  refine ⟨s', hs'1, fun z hz => ?_⟩
  obtain ⟨e1, e2, e3⟩ := hs'2 z hz
  refine ⟨e1, lt_trans (by positivity) e2, e3.trans ?_⟩
  rw [div_lt_one hn0, Nat.cast_sub (by lia)]; simp

lemma coeffPoly_eval_eq (n : ℕ) (G : ℝ[X]) (t : ℝ) (ht : t ≠ -1) :
    (coeffPoly n G).eval t = (1 + t) ^ n * (bernOp n G).eval (t / (1 + t)) := by
  have ht' : 1 + t ≠ 0 := by intro h; apply ht; linarith
  have hy : t / (1 + t) ≠ 1 := by
    intro h; rw [div_eq_one_iff_eq ht'] at h; linarith
  rw [bernOp_eval_eq n G _ hy]
  have e1 : 1 - t / (1 + t) = 1 / (1 + t) := by field_simp; ring
  have e2 : t / (1 + t) / (1 / (1 + t)) = t := by field_simp
  rw [e1, e2, ← mul_assoc, ← mul_pow, mul_one_div_cancel ht', one_pow, one_mul]

/-- The Möbius change of variables `y = t/(1+t)` applied to `y (y - 1) ∏ (y - z_i)`. -/
lemma prod_moebius (n m : ℕ) (hm : 2 ≤ m) (hmn : m ≤ n) (z : Fin (m - 2) → ℝ)
    (hz : ∀ i, z i ≠ 1) (t : ℝ) (ht : t ≠ -1) :
    (1 + t) ^ n * (t / (1 + t) * (t / (1 + t) - 1) * ∏ i, (t / (1 + t) - z i)) =
      -(∏ i, (1 - z i)) * (t * (1 + t) ^ (n - m) * ∏ i, (t - z i / (1 - z i))) := by
  have ht' : 1 + t ≠ 0 := by intro h; apply ht; linarith
  have hpow : (1 + t) ^ n =
      (1 + t) ^ (n - m) * (1 + t) * (1 + t) * ∏ _i : Fin (m - 2), (1 + t) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_succ, ← pow_succ,
      ← pow_add]
    congr 1; lia
  have hfac : ∀ i, (1 + t) * (t / (1 + t) - z i) = (1 - z i) * (t - z i / (1 - z i)) := by
    intro i
    have : 1 - z i ≠ 0 := sub_ne_zero.mpr (Ne.symm (hz i))
    field_simp
    ring
  have key : (∏ _i : Fin (m - 2), (1 + t)) * ∏ i, (t / (1 + t) - z i) =
      (∏ i, (1 - z i)) * ∏ i, (t - z i / (1 - z i)) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => hfac i
  rw [hpow]
  have e1 : (1 + t) * (t / (1 + t)) = t := by field_simp
  have e2 : (1 + t) * (t / (1 + t) - 1) = -1 := by field_simp; ring
  calc (1 + t) ^ (n - m) * (1 + t) * (1 + t) * (∏ _i : Fin (m - 2), (1 + t)) *
        (t / (1 + t) * (t / (1 + t) - 1) * ∏ i, (t / (1 + t) - z i))
      = (1 + t) ^ (n - m) * ((1 + t) * (t / (1 + t))) * ((1 + t) * (t / (1 + t) - 1)) *
        ((∏ _i : Fin (m - 2), (1 + t)) * ∏ i, (t / (1 + t) - z i)) := by ring
    _ = _ := by rw [e1, e2, key]; ring

lemma roots_prod_fin_X_sub_C {k : ℕ} (w : Fin k → ℝ) :
    (∏ i, (X - C (w i))).roots = Finset.univ.val.map w := by
  rw [Finset.prod_eq_multiset_prod]
  have : Finset.univ.val.map (fun i => X - C (w i)) =
      (Finset.univ.val.map w).map (fun a => X - C a) := by rw [Multiset.map_map]; rfl
  rw [this, roots_multiset_prod_X_sub_C]

/-- **Simple real zeros of `G_m`.**  `G_m = X (X - 1) ∏ (X - z_i)` with `m - 2` distinct zeros
`z_i ∈ (0,1)`.  Simplicity comes from Descartes' rule of signs (which counts multiplicities)
applied to the Bernstein coefficients of `B_n G_m = μ_m G_m`. -/
lemma eigPoly_eq_prod (n m : ℕ) (hm : 2 ≤ m) (hmn : m ≤ n) :
    ∃ z : Fin (m - 2) → ℝ, Function.Injective z ∧ (∀ i, 0 < z i ∧ z i < 1) ∧
      eigPoly n m = X * (X - C 1) * ∏ i, (X - C (z i)) := by
  have hn : 2 ≤ n := by lia
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by lia)
  obtain ⟨z, hzI, hG⟩ := eigPoly_eq_prod_closed n m hm hmn
  have hz01 : ∀ i, 0 < z i ∧ z i < 1 := by
    intro i
    obtain ⟨h1, h2⟩ := hzI i
    refine ⟨lt_of_lt_of_le (by positivity) h1, lt_of_le_of_lt h2 ?_⟩
    rw [div_lt_one hn0, Nat.cast_sub (by lia)]; simp
  refine ⟨z, ?_, hz01, hG⟩
  have heig := (eigPoly_spec n m hm hmn).2.2
  have hμ : mu n m ≠ 0 := (mu_pos n m hmn).ne'
  set w : Fin (m - 2) → ℝ := fun i => z i / (1 - z i) with hw
  have hwpos : ∀ i, 0 < w i := fun i => div_pos (hz01 i).1 (by linarith [(hz01 i).2])
  set κ : ℝ := -mu n m * ∏ i, (1 - z i) with hκ
  have hκ0 : κ ≠ 0 := by
    refine mul_ne_zero (neg_ne_zero.mpr hμ) (Finset.prod_ne_zero_iff.mpr fun i _ => ?_)
    exact (sub_pos.mpr (hz01 i).2).ne'
  set P : ℝ[X] := X * (X + 1) ^ (n - m) * ∏ i, (X - C (w i)) with hP
  have hp : coeffPoly n (eigPoly n m) = C κ * P := by
    refine eq_of_eval_eq_off _ _ {-1} fun t ht => ?_
    have ht' : t ≠ -1 := by simpa using ht
    rw [coeffPoly_eval_eq n _ t ht', heig, eval_smul, smul_eq_mul, hG]
    have := prod_moebius n m hm hmn z (fun i => (hz01 i).2.ne) t ht'
    simp only [eval_mul, eval_X, eval_sub, eval_C, eval_prod, eval_pow, eval_add, eval_one, hP]
    rw [mul_left_comm, this, hκ, add_comm t 1]
    ring
  have hX1 : (X + 1 : ℝ[X]).Monic := by simpa using monic_X_add_C (1 : ℝ)
  have hPmon : P.Monic :=
    (monic_X.mul (hX1.pow _)).mul (monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _)
  have hle : Finset.univ.val.map w ≤ P.roots := by
    rw [hP, roots_mul (by rw [← hP]; exact hPmon.ne_zero), roots_prod_fin_X_sub_C]
    exact Multiset.le_add_left _ _
  have hc1 : m - 2 ≤ (coeffPoly n (eigPoly n m)).roots.countP (0 < ·) := by
    rw [hp, roots_C_mul _ hκ0]
    calc m - 2 = (Finset.univ.val.map w).card := by simp
      _ = (Finset.univ.val.map w).countP (0 < ·) :=
          (Multiset.countP_eq_card.mpr (by simp [hwpos])).symm
      _ ≤ P.roots.countP (0 < ·) := Multiset.countP_le_of_le _ hle
  have hc2 := roots_countP_pos_le_signVariations (coeffPoly n (eigPoly n m))
  obtain ⟨s, hs1, hs2⟩ := signVariations_coeffPoly_le n hn _ (eigPoly_eval_zero n m hm hmn)
    (eigPoly_eval_one n m hm hmn)
  have hsub : s ⊆ Finset.univ.image z := by
    intro x hx
    obtain ⟨e1, e2, e3⟩ := hs2 x hx
    rw [hG] at e1
    simp only [eval_mul, eval_X, eval_sub, eval_C, eval_prod] at e1
    have hx1 : x - 1 ≠ 0 := sub_ne_zero.mpr e3.ne
    obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp
      ((mul_eq_zero.mp e1).resolve_left (mul_ne_zero e2.ne' hx1))
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, (sub_eq_zero.mp hi).symm⟩
  have hcard := Finset.card_le_card hsub
  have himg : (Finset.univ.image z).card = (Finset.univ : Finset (Fin (m - 2))).card :=
    le_antisymm Finset.card_image_le (by simp; lia)
  have := Finset.card_image_iff.mp himg
  intro a b hab
  exact this (Finset.mem_coe.mpr (Finset.mem_univ a)) (Finset.mem_coe.mpr (Finset.mem_univ b)) hab

/-- Given any factorisation `G_{j+2} = X (X - 1) ∏ (X - z_i)` with `z_i ∈ (0,1)`, the
eigenpolynomial `Q_{n,j}` is `∏ (X - z_i / (1 - z_i))`. -/
lemma isEigenpoly_eq_prod_of {n j : ℕ} (hj : j + 3 ≤ n) {Q : ℝ[X]} (hQ : IsEigenpoly n j Q)
    (z : Fin (j + 2 - 2) → ℝ) (hz01 : ∀ i, 0 < z i ∧ z i < 1)
    (hG : eigPoly n (j + 2) = X * (X - C 1) * ∏ i, (X - C (z i))) :
    Q = ∏ i, (X - C (z i / (1 - z i))) := by
  have hn : 2 ≤ n := by lia
  obtain ⟨hmon, -, v, -, hT, heig⟩ := hQ
  obtain ⟨hGmon, hGdeg, hGeig⟩ := eigPoly_spec n (j + 2) (by lia) (by lia)
  have e := eigenvalue_spec n (j + 1) (by lia)
  have hB := bern_of_linearPart_eigen n hn v _ e.1 heig
  rw [e.2] at hB
  obtain ⟨c, hc⟩ := eigen_unique n (j + 2) (by lia) (by lia) (eigPoly n (j + 2)) (Gv n v)
    hGmon.ne_zero (by rw [hGdeg]; lia) ((Gv_natDegree n hn v).trans (by lia)) hGeig hB
  set w : Fin (j + 2 - 2) → ℝ := fun i => z i / (1 - z i) with hw
  set k : ℝ := -c * ∏ i, (1 - z i) with hk
  have hQk : Q = C k * ∏ i, (X - C (w i)) := by
    refine eq_of_eval_eq_off _ _ {0, -1} fun x hx => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    obtain ⟨hx0, hx1⟩ := hx
    have hx1' : 1 + x ≠ 0 := by intro h; apply hx1; linarith
    have hy : x / (1 + x) ≠ 1 := by
      intro h; rw [div_eq_one_iff_eq hx1'] at h; linarith
    have h1 := congrArg (eval (x / (1 + x))) hc
    rw [Gv_eq_Psi n hn, Psi_eval n _ ((Tv_natDegree n hn v).trans (by lia)) _ hy,
      ← monicPolynomial_sub, hT, eval_smul, hG, smul_eq_mul] at h1
    have e1 : 1 - x / (1 + x) = 1 / (1 + x) := by field_simp; ring
    have e2 : x / (1 + x) / (1 / (1 + x)) = x := by field_simp
    rw [e1, e2] at h1
    simp only [eval_mul, eval_X, eval_pow, eval_add, eval_one, eval_sub, eval_C,
      eval_prod] at h1
    have hm := prod_moebius n (j + 2) (by lia) (by lia) z (fun i => (hz01 i).2.ne) x hx1
    have h2 : x * (x + 1) ^ (n - j - 2) * Q.eval x =
        x * (x + 1) ^ (n - j - 2) * (k * ∏ i, (x - w i)) := by
      have hpow : (1 / (1 + x)) ^ n * (1 + x) ^ n = 1 := by
        rw [← mul_pow, one_div_mul_cancel hx1', one_pow]
      calc x * (x + 1) ^ (n - j - 2) * Q.eval x
          = (1 / (1 + x)) ^ n * (x * (x + 1) ^ (n - j - 2) * Q.eval x) * (1 + x) ^ n := by
            rw [mul_comm ((1 / (1 + x)) ^ n) _, mul_assoc _ ((1 / (1 + x)) ^ n), hpow, mul_one]
        _ = c * ((1 + x) ^ n * (x / (1 + x) * (x / (1 + x) - 1) *
              ∏ i, (x / (1 + x) - z i))) := by rw [h1]; ring
        _ = _ := by
            rw [hm, hk, Nat.sub_sub, add_comm x 1]
            ring
    have hne : x * (x + 1) ^ (n - j - 2) ≠ 0 :=
      mul_ne_zero hx0 (pow_ne_zero _ (by rwa [add_comm]))
    rw [mul_right_inj' hne] at h2
    rw [h2]
    simp [eval_prod]
  have hpm : (∏ i, (X - C (w i))).Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
  have hk1 : k = 1 := by
    have := hmon.leadingCoeff
    rwa [hQk, leadingCoeff_mul, leadingCoeff_C, hpm.leadingCoeff, mul_one] at this
  rw [hQk, hk1, map_one, one_mul]

/-- The eigenpolynomial `Q_{n,j}` is `∏ (X - w_i)` with `j` distinct positive `w_i`
(`w_i = z_i / (1 - z_i)` for the interior zeros `z_i` of `G_{j+2}`). -/
lemma isEigenpoly_eq_prod {n j : ℕ} (hj : j + 3 ≤ n) {Q : ℝ[X]} (hQ : IsEigenpoly n j Q) :
    ∃ w : Fin (j + 2 - 2) → ℝ, Function.Injective w ∧ (∀ i, 0 < w i) ∧
      Q = ∏ i, (X - C (w i)) := by
  obtain ⟨z, hzinj, hz01, hG⟩ := eigPoly_eq_prod n (j + 2) (by lia) (by lia)
  have hz1 : ∀ i, 1 - z i ≠ 0 := fun i => (sub_pos.mpr (hz01 i).2).ne'
  refine ⟨fun i => z i / (1 - z i), ?_, fun i => div_pos (hz01 i).1 (sub_pos.mpr (hz01 i).2),
    isEigenpoly_eq_prod_of hj hQ z hz01 hG⟩
  intro a b hab
  have h1 := hz1 a
  have h2 := hz1 b
  simp only at hab
  field_simp at hab
  exact hzinj (by linarith)

end Kostov
end RealRooted
