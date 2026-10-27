module

import RealRooted.Hadamard.Kostov.Roots
public import RealRooted.Hadamard.Kostov.Interlacing
public import RealRooted.Hadamard.Kostov.Eigen

public section

open Polynomial

noncomputable section

namespace RealRooted
namespace Kostov

/-! ### Auxiliary lemmas: Wronskian of `G_m` and `G_{m+2}` on `(0, 1/2)` -/

/-- Generalisation of `alt_comb`: for `m < d ≤ n`, every combination `G_d - c G_m` has at least
`m - 2` strict sign changes in `(0,1)`. -/
lemma alt_comb_gen (n m d : ℕ) (hm : 2 ≤ m) (hmd : m < d) (hdn : d ≤ n) (c : ℝ) :
    Alt (eigPoly n d - c • eigPoly n m) (m - 2) := by
  have hn : 2 ≤ n := by lia
  by_cases hc : c = 0
  · simpa [hc] using (eigPoly_alt n d (by lia) hdn).mono (by lia)
  rcases Nat.eq_zero_or_pos (m - 2) with hk | hk
  · simpa [hk] using alt_zero (eigPoly n d - c • eigPoly n m)
  set k := m - 2 with hkdef
  set f := eigPoly n m with hf
  set g := eigPoly n d with hg
  set H := g - c • f with hH
  have hH0 : H.eval 0 = 0 := by
    simp [hH, hf, hg, eigPoly_eval_zero n m hm (by lia), eigPoly_eval_zero n d (by lia) hdn]
  have hH1 : H.eval 1 = 0 := by
    simp [hH, hf, hg, eigPoly_eval_one n m hm (by lia), eigPoly_eval_one n d (by lia) hdn]
  obtain ⟨q, hq0, hq1, hqinc, hqalt⟩ := eigPoly_alt n m hm (by lia)
  have hfq : ∀ i ≤ k, f.eval (q i) ≠ 0 := by
    intro i hi
    rcases lt_or_eq_of_le hi with h | h
    · exact left_ne_zero_of_mul (hqalt i h).ne
    · have := hqalt (k - 1) (by lia)
      rw [show k - 1 + 1 = k by lia] at this; rw [h]; exact right_ne_zero_of_mul this.ne
  have hμ : 0 < mu n m := mu_pos n m (by lia)
  have hratio0 : 0 ≤ mu n d / mu n m := div_nonneg (mu_pos n d hdn).le hμ.le
  have hratio1 : mu n d / mu n m < 1 := (div_lt_one hμ).2 (mu_lt_of_lt n m d (by lia) hmd hdn)
  have hBr : ∀ r : ℕ, ((bernOp n) ^ r) H =
      (mu n d) ^ r • g - (c * (mu n m) ^ r) • f := by
    intro r; rw [hH, map_sub, map_smul, hg, hf, bernOp_pow_eigPoly n m hm (by lia),
      bernOp_pow_eigPoly n d (by lia) hdn, smul_smul]
  set D : ℕ → ℝ := fun r => -(c * (mu n m) ^ r) with hD
  have hD0 : ∀ r, D r ≠ 0 := fun r => neg_ne_zero.mpr (mul_ne_zero hc (pow_ne_zero _ hμ.ne'))
  have hS : ∀ (r : ℕ) (y : ℝ), (((bernOp n) ^ r) H).eval y / D r =
      f.eval y - (mu n d / mu n m) ^ r * (g.eval y / c) := by
    intro r y; rw [hBr]
    simp only [eval_sub, eval_smul, smul_eq_mul, hD, div_pow]
    field_simp; ring
  have hT : ∀ y : ℝ, Filter.Tendsto (fun r : ℕ => (((bernOp n) ^ r) H).eval y / D r)
      Filter.atTop (nhds (f.eval y)) := by
    intro y; simp_rw [hS]
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hratio0 hratio1).mul_const
      (g.eval y / c)).const_sub (f.eval y)
  have hev : ∀ i ∈ Finset.range (k + 1), ∀ᶠ r in Filter.atTop,
      0 < (((bernOp n) ^ r) H).eval (q i) / D r * f.eval (q i) := by
    intro i hi; rw [Finset.mem_range] at hi
    have hpos : 0 < f.eval (q i) * f.eval (q i) := mul_self_pos.mpr (hfq i (by lia))
    exact ((hT (q i)).mul_const (f.eval (q i))).eventually_const_lt hpos
  obtain ⟨r, hr⟩ := ((Filter.eventually_all_finset _).mpr hev).exists
  refine Alt.of_bernOp_pow hn r H hH0 hH1 k ⟨q, hq0, hq1, hqinc, fun i hi => ?_⟩
  have e1 := hr i (Finset.mem_range.mpr (by lia))
  have e2 := hr (i + 1) (Finset.mem_range.mpr (by lia))
  have e3 := hqalt i hi
  set a := (((bernOp n) ^ r) H).eval (q i)
  set b := (((bernOp n) ^ r) H).eval (q (i + 1))
  have hab : a / D r * (b / D r) < 0 := by
    have : 0 < (a / D r * (b / D r)) * (f.eval (q i) * f.eval (q (i + 1))) := by
      calc (0 : ℝ) < _ := mul_pos e1 e2
        _ = _ := by ring
    exact neg_of_mul_pos_left this e3.le
  have : a * b = (a / D r * (b / D r)) * (D r) ^ 2 := by field_simp [hD0 r]
  rw [this]; exact mul_neg_of_neg_of_pos hab (sq_pos_of_ne_zero (hD0 r))

/-- If `p(s) = p'(s) = 0` then `(X - s)^2 ∣ p`. -/
lemma sq_dvd_of_eval_deriv (p : ℝ[X]) (s : ℝ) (h : p.eval s = 0)
    (h' : (derivative p).eval s = 0) : (X - C s) ^ 2 ∣ p := by
  by_cases hp : p = 0
  · simp [hp]
  rw [← le_rootMultiplicity_iff hp]
  lia [(one_lt_rootMultiplicity_iff_isRoot hp).mpr ⟨h, h'⟩]

/-- A polynomial vanishing at `0`, `1` and doubly at two distinct interior points, with `k`
strict sign changes in `(0,1)`, has degree at least `k + 6`. -/
lemma two_double_root_degree (F : ℝ[X]) (hF : F ≠ 0) (h0 : F.eval 0 = 0) (h1 : F.eval 1 = 0)
    (t s : ℝ) (hts : t ≠ s) (ht0 : 0 < t) (ht1 : t < 1) (hs0 : 0 < s) (hs1 : s < 1)
    (hFt : F.eval t = 0) (hF't : (derivative F).eval t = 0)
    (hFs : F.eval s = 0) (hF's : (derivative F).eval s = 0)
    (k : ℕ) (halt : Alt F k) : k + 6 ≤ F.natDegree := by
  have hcop : ∀ a b : ℝ, a ≠ b → IsCoprime (X - C a) (X - C b) := fun a b hab =>
    isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hab).isUnit
  have d0 : X - C 0 ∣ F := dvd_iff_isRoot.mpr h0
  have d1 : X - C 1 ∣ F := dvd_iff_isRoot.mpr h1
  have dt := sq_dvd_of_eval_deriv F t hFt hF't
  have ds := sq_dvd_of_eval_deriv F s hFs hF's
  have c01 := hcop 0 1 (by norm_num)
  have c0t := (hcop 0 t ht0.ne).pow_right (n := 2)
  have c0s := (hcop 0 s hs0.ne).pow_right (n := 2)
  have c1t := (hcop 1 t ht1.ne').pow_right (n := 2)
  have c1s := (hcop 1 s hs1.ne').pow_right (n := 2)
  have cts := (hcop t s hts).pow (m := 2) (n := 2)
  have hdvd : (X - C 0) * (X - C 1) * (X - C t) ^ 2 * (X - C s) ^ 2 ∣ F := by
    exact IsCoprime.mul_dvd ((c0s.mul_left c1s).mul_left cts)
      (IsCoprime.mul_dvd (c0t.mul_left c1t) (IsCoprime.mul_dvd c01 d0 d1) dt) ds
  obtain ⟨F4, hFeq'⟩ := hdvd
  have hF4ne : F4 ≠ 0 := by rintro rfl; simp_all
  have hmon : ((X - C 0) * (X - C 1) * (X - C t) ^ 2 * (X - C s) ^ 2 : ℝ[X]).Monic :=
    (((monic_X_sub_C 0).mul (monic_X_sub_C 1)).mul ((monic_X_sub_C t).pow 2)).mul
      ((monic_X_sub_C s).pow 2)
  have hdeg6 : ((X - C 0) * (X - C 1) * (X - C t) ^ 2 * (X - C s) ^ 2 : ℝ[X]).natDegree = 6 := by
    rw [natDegree_mul (by exact (((monic_X_sub_C 0).mul (monic_X_sub_C 1)).mul
        ((monic_X_sub_C t).pow 2)).ne_zero) ((monic_X_sub_C s).pow 2).ne_zero,
      natDegree_mul (by exact ((monic_X_sub_C 0).mul (monic_X_sub_C 1)).ne_zero)
        ((monic_X_sub_C t).pow 2).ne_zero,
      natDegree_mul (monic_X_sub_C 0).ne_zero (monic_X_sub_C 1).ne_zero, natDegree_pow,
      natDegree_pow, natDegree_X_sub_C, natDegree_X_sub_C, natDegree_X_sub_C, natDegree_X_sub_C]
  have hdeg : F.natDegree = 6 + F4.natDegree := by rw [hFeq', hmon.natDegree_mul' hF4ne, hdeg6]
  obtain ⟨p, hp0, hp1, hinc, halt⟩ := halt
  have hpin : ∀ i ≤ k, 0 < p i ∧ p i < 1 := fun i hi =>
    ⟨lt_of_lt_of_le hp0 (chain_le hinc 0 i (Nat.zero_le _) hi),
      lt_of_le_of_lt (chain_le hinc i k hi le_rfl) hp1⟩
  have hw : ∀ i ≤ k, (p i - 0) * (p i - 1) * (p i - t) ^ 2 * (p i - s) ^ 2 ≤ 0 := by
    intro i hi; obtain ⟨a1, a2⟩ := hpin i hi
    have : (p i - 0) * (p i - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg this (sq_nonneg _))
      (sq_nonneg _)
  have hk := le_natDegree_of_alt F4 hF4ne p k hinc (fun i hi => by
    have := halt i hi
    rw [hFeq'] at this
    simp only [eval_mul, eval_X, eval_sub, eval_C, eval_pow] at this
    by_contra hge; push Not at hge
    have : 0 ≤ ((p i - 0) * (p i - 1) * (p i - t) ^ 2 * (p i - s) ^ 2) *
        ((p (i + 1) - 0) * (p (i + 1) - 1) * (p (i + 1) - t) ^ 2 * (p (i + 1) - s) ^ 2) *
        (F4.eval (p i) * F4.eval (p (i + 1))) :=
      mul_nonneg (mul_nonneg_of_nonpos_of_nonpos (hw i hi.le) (hw (i + 1) hi)) hge
    linarith)
  lia

/-- Reflection of double roots: if `P(1 - y) = e P(y)` and `P` has a double zero at `t`, it has a
double zero at `1 - t`. -/
lemma reflect_double_root (P : ℝ[X]) (e : ℝ) (hP : P.comp (1 - X) = C e * P) (t : ℝ)
    (h : P.eval t = 0) (h' : (derivative P).eval t = 0) :
    P.eval (1 - t) = 0 ∧ (derivative P).eval (1 - t) = 0 := by
  have h1 := congrArg (eval t) hP
  have h2 := congrArg (fun Q => (derivative Q).eval t) hP
  simp only [eval_comp, eval_sub, eval_one, eval_X, eval_mul, eval_C] at h1
  simp only [derivative_comp, derivative_mul, derivative_C, zero_mul, zero_add, derivative_sub,
    derivative_one, derivative_X, eval_mul, eval_comp, eval_sub, eval_one, eval_X, eval_C,
    eval_zero] at h2
  refine ⟨by rw [h1, h, mul_zero], ?_⟩
  rw [h', mul_zero] at h2; linarith

lemma eigPoly_comb_reflect (n m : ℕ) (hm : 2 ≤ m) (hmn : m + 2 ≤ n) (c : ℝ) :
    (eigPoly n (m + 2) - c • eigPoly n m).comp (1 - X) =
      C ((-1 : ℝ) ^ m) * (eigPoly n (m + 2) - c • eigPoly n m) := by
  rw [sub_comp, smul_comp, eigPoly_reflect n (m + 2) (by lia) hmn,
    eigPoly_reflect n m hm (by lia), pow_add]
  simp only [smul_eq_C_mul]
  norm_num; ring

/-- The Wronskian of `G_m` and `G_{m+2}` has no zero in `(0, 1/2)`. -/
lemma wronskian2_ne_zero (n m : ℕ) (hm : 2 ≤ m) (hmn : m + 2 ≤ n) (t : ℝ) (ht0 : 0 < t)
    (ht1 : t < 1 / 2) :
    (eigPoly n m * derivative (eigPoly n (m + 2)) -
      derivative (eigPoly n m) * eigPoly n (m + 2)).eval t ≠ 0 := by
  set f := eigPoly n m with hf
  set g := eigPoly n (m + 2) with hg
  obtain ⟨hfmon, hfdeg, -⟩ := eigPoly_spec n m hm (by lia)
  obtain ⟨hgmon, hgdeg, -⟩ := eigPoly_spec n (m + 2) (by lia) hmn
  have hf0 := eigPoly_eval_zero n m hm (by lia)
  have hf1 := eigPoly_eval_one n m hm (by lia)
  have hg0 := eigPoly_eval_zero n (m + 2) (by lia) hmn
  have hg1 := eigPoly_eval_one n (m + 2) (by lia) hmn
  have hsimple : f.eval t = 0 → (derivative f).eval t ≠ 0 := by
    intro h h'; have :=
      double_root_degree f hfmon.ne_zero hf0 hf1 t ht0 (by linarith) h h' (m - 2)
      (eigPoly_alt n m hm (by lia)); lia
  have hH : ∀ c : ℝ, (g - c • f).eval t = 0 →
      (derivative (g - c • f)).eval t = 0 → False := by
    intro c h h'
    have hdeg : (g - c • f).natDegree ≤ m + 2 :=
      (natDegree_sub_le _ _).trans (max_le hgdeg.le ((natDegree_smul_le _ _).trans (by lia)))
    have hne : g - c • f ≠ 0 := by
      intro h0; have := congrArg (fun P => P.coeff (m + 2)) h0
      simp only [coeff_sub, coeff_smul, smul_eq_mul, coeff_zero] at this
      rw [coeff_eq_zero_of_natDegree_lt (by lia : f.natDegree < m + 2), ← hgdeg,
        hgmon.coeff_natDegree] at this
      norm_num at this
    obtain ⟨r1, r2⟩ := reflect_double_root _ _ (eigPoly_comb_reflect n m hm hmn c) t h h'
    have := two_double_root_degree (g - c • f) hne (by simp [hf, hg, hg0, hf0])
      (by simp [hf, hg, hg1, hf1]) t (1 - t) (by intro h; linarith) ht0 (by linarith)
      (by linarith) (by linarith) h h' r1 r2 (m - 2) (alt_comb_gen n m (m + 2) hm (by lia) hmn c)
    lia
  intro hW
  simp only [eval_sub, eval_mul] at hW
  by_cases hft : f.eval t = 0
  · have hf't := hsimple hft
    rw [hft, zero_mul, zero_sub, neg_eq_zero] at hW
    have hgt : g.eval t = 0 := (mul_eq_zero.mp hW).resolve_left hf't
    apply hH ((derivative g).eval t / (derivative f).eval t)
    · simp [hgt, hft]
    · simp only [derivative_sub, derivative_smul, eval_sub, eval_smul, smul_eq_mul]
      field_simp; ring
  · apply hH (g.eval t / f.eval t)
    · simp only [eval_sub, eval_smul, smul_eq_mul]
      field_simp; ring
    · simp only [derivative_sub, derivative_smul, eval_sub, eval_smul, smul_eq_mul]
      field_simp
      linear_combination hW

/-- Between two zeros of `G_{m+2}` in `(0,1/2)` there is a zero of `G_m`. -/
lemma zero_between2 (n m : ℕ) (hm : 2 ≤ m) (hmn : m + 2 ≤ n) (a b : ℝ) (ha0 : 0 < a)
    (hab : a < b) (hb1 : b < 1 / 2) (hga : (eigPoly n (m + 2)).eval a = 0)
    (hgb : (eigPoly n (m + 2)).eval b = 0) :
    ∃ t, a < t ∧ t < b ∧ (eigPoly n m).eval t = 0 := by
  set f := eigPoly n m with hf
  set g := eigPoly n (m + 2) with hg
  have hW := wronskian2_ne_zero n m hm hmn
  by_contra hno; push Not at hno
  have hfa : f.eval a ≠ 0 := by
    intro h; apply hW a ha0 (by linarith); simp [← hf, ← hg, h, hga]
  have hfb : f.eval b ≠ 0 := by
    intro h; apply hW b (by linarith) hb1; simp [← hf, ← hg, h, hgb]
  have hfne : ∀ x ∈ Set.Icc a b, f.eval x ≠ 0 := by
    intro x ⟨h1, h2⟩
    rcases eq_or_lt_of_le h1 with rfl | h1
    · exact hfa
    rcases eq_or_lt_of_le h2 with rfl | h2
    · exact hfb
    exact hno x h1 h2
  obtain ⟨c, ⟨hc1, hc2⟩, hc⟩ := exists_deriv_eq_zero hab
    ((Polynomial.continuous g).continuousOn.div (Polynomial.continuous f).continuousOn hfne)
    (by simp [hga, hgb])
  have hfc := hfne c ⟨hc1.le, hc2.le⟩
  rw [deriv_div (Polynomial.differentiableAt g) (Polynomial.differentiableAt f) hfc,
    Polynomial.deriv, Polynomial.deriv] at hc
  apply hW c (by linarith) (by linarith)
  simp only [eval_sub, eval_mul]
  linear_combination (div_eq_zero_iff.mp hc).resolve_right (pow_ne_zero 2 hfc)

/-- A zero in `(0,1)` of `X (X - 1) ∏ (X - z_i)` is one of the `z_i`. -/
lemma root_index_of_prod {k : ℕ} (z : Fin k → ℝ) (y : ℝ) (hy0 : 0 < y) (hy1 : y < 1)
    (h : (X * (X - C 1) * ∏ i, (X - C (z i))).eval y = 0) : ∃ l, z l = y := by
  simp only [eval_mul, eval_X, eval_sub, eval_C, eval_prod] at h
  have hyy : y * (y - 1) ≠ 0 := mul_ne_zero hy0.ne' (sub_ne_zero.mpr hy1.ne)
  obtain ⟨l, -, hl⟩ := Finset.prod_eq_zero_iff.mp ((mul_eq_zero.mp h).resolve_left hyy)
  exact ⟨l, (sub_eq_zero.mp hl).symm⟩

/-- A strictly monotone self-map of `Fin k` is the identity. -/
lemma fin_strictMono_eq_id {k : ℕ} (σ : Fin k → Fin k) (hσ : StrictMono σ) : σ = id := by
  have hs : Function.Surjective σ := Finite.surjective_of_injective hσ.injective
  have := Subsingleton.elim (StrictMono.orderIsoOfSurjective σ hσ hs) (OrderIso.refl _)
  funext i; exact congrArg (fun e : Fin k ≃o Fin k => e i) this

/-- The sorted interior zeros of `G_m` are symmetric about `1/2`. -/
lemma eigPoly_roots_symm (n m : ℕ) (hm : 2 ≤ m) (hmn : m ≤ n) (z : Fin (m - 2) → ℝ)
    (hz : StrictMono z) (hz01 : ∀ i, 0 < z i ∧ z i < 1)
    (hG : eigPoly n m = X * (X - C 1) * ∏ i, (X - C (z i))) :
    ∀ i, z (Fin.rev i) = 1 - z i := by
  have hroot : ∀ i, ∃ l, z l = 1 - z i := by
    intro i
    refine root_index_of_prod z _ (by linarith [(hz01 i).2]) (by linarith [(hz01 i).1]) ?_
    rw [← hG]
    have h1 := congrArg (eval (z i)) (eigPoly_reflect n m hm hmn)
    simp only [eval_comp, eval_sub, eval_one, eval_X, eval_mul, eval_C] at h1
    rw [h1, hG]; simp [eval_prod, Finset.prod_eq_zero (Finset.mem_univ i)]
  choose τ hτ using hroot
  have hστ : StrictMono (fun i => Fin.rev (τ i)) := by
    intro i i' hii'
    have h := hz hii'
    rw [Fin.rev_lt_rev]
    have : z (τ i') < z (τ i) := by rw [hτ, hτ]; linarith
    exact hz.lt_iff_lt.mp this
  have hid := fin_strictMono_eq_id _ hστ
  intro i
  have h2 : τ i = i.rev := by rw [← Fin.rev_rev (τ i), congrFun hid i]; rfl
  rw [← h2]; exact hτ i

/-- Combinatorial core of the lower-half comparison. -/
lemma lower_interlace {j : ℕ} (a : Fin j → ℝ) (b : Fin (j + 2) → ℝ) (ha : StrictMono a)
    (hb : StrictMono b) (has : ∀ i, a (Fin.rev i) = 1 - a i)
    (hbs : ∀ i, b (Fin.rev i) = 1 - b i)
    (hbet : ∀ l l' : Fin (j + 2), b l < b l' → b l' < 1 / 2 →
      ∃ r, b l < a r ∧ a r < b l') :
    ∀ (i : ℕ) (hi : i < j / 2),
      b ⟨i, by lia⟩ < a ⟨i, by lia⟩ ∧ a ⟨i, by lia⟩ < b ⟨i + 1, by lia⟩ := by
  set K := j / 2 with hK
  have hbhalf : ∀ l : Fin (j + 2), l.1 ≤ K → b l < 1 / 2 := by
    intro l hl
    have : b l < b (Fin.rev l) := hb (by rw [Fin.lt_def, Fin.val_rev]; lia)
    rw [hbs] at this; linarith
  have hahalf : ∀ l : Fin j, a l < 1 / 2 → l.1 < K := by
    intro l hl
    by_contra hc
    have : a (Fin.rev l) ≤ a l := ha.monotone (by rw [Fin.le_def, Fin.val_rev]; lia)
    rw [has] at this; linarith
  have hum : StrictMono (fun l : Fin (K + 1) => b ⟨l.1, by lia⟩) := fun l l' h =>
    hb (by rw [Fin.lt_def] at h ⊢; exact h)
  have hwm : StrictMono (fun l : Fin K => a ⟨l.1, by lia⟩) := fun l l' h =>
    ha (by rw [Fin.lt_def] at h ⊢; exact h)
  have hbet' : ∀ i : Fin K, ∃ l, (fun l : Fin (K + 1) => b ⟨l.1, by lia⟩) i.castSucc <
      (fun l : Fin K => a ⟨l.1, by lia⟩) l ∧
      (fun l : Fin K => a ⟨l.1, by lia⟩) l <
        (fun l : Fin (K + 1) => b ⟨l.1, by lia⟩) i.succ := by
    intro i
    have hi2 := i.2
    obtain ⟨r, hr1, hr2⟩ := hbet ⟨i.1, by lia⟩ ⟨i.1 + 1, by lia⟩
      (hb (by rw [Fin.lt_def]; exact Nat.lt_succ_self _)) (hbhalf _ (by change i.1 + 1 ≤ K; lia))
    have hrK := hahalf r (by linarith [hbhalf ⟨i.1 + 1, by lia⟩ (by change i.1 + 1 ≤ K; lia)])
    exact ⟨⟨r.1, hrK⟩, hr1, hr2⟩
  exact fun i hi => interlace_of_between _ _ hwm hum hbet' ⟨i, hi⟩
/-- Kostov's Theorem 4 compares roots two degrees apart.  For odd `j`, the central root is one.
(Zero-based form below: `i` ranges over `0 ≤ i < j/2`, with `x i` the `(i+1)`-st root.)
Checked exactly (rational isolating intervals) for `6 ≤ n ≤ 11`, all admissible `j`. -/
private theorem eigenpoly_two_step_aux {n j : ℕ} (_hj1 : 1 ≤ j) (hj : j + 5 ≤ n)
    {Q R : ℝ[X]} (hQ : IsEigenpoly n j Q) (hR : IsEigenpoly n (j + 2) R) :
    ∃ (x : Fin j → ℝ) (z : Fin (j + 2) → ℝ), StrictMono x ∧ StrictMono z ∧
      (∀ i, Q.IsRoot (x i)) ∧ (∀ i, R.IsRoot (z i)) ∧
      (∀ (i : ℕ) (hi : i < j / 2),
        z ⟨i, by lia⟩ < x ⟨i, by lia⟩ ∧ x ⟨i, by lia⟩ < z ⟨i + 1, by lia⟩ ∧
        z ⟨j - i, by lia⟩ < x ⟨j - 1 - i, by lia⟩ ∧
          x ⟨j - 1 - i, by lia⟩ < z ⟨j + 1 - i, by lia⟩) ∧
      (Odd j → x ⟨(j - 1) / 2, by lia⟩ = 1 ∧ z ⟨(j + 1) / 2, by lia⟩ = 1) := by
  obtain ⟨a, ha, ha01, hGa⟩ := eigPoly_eq_prod_sorted n (j + 2) (by lia) (by lia)
  obtain ⟨b, hb, hb01, hGb⟩ := eigPoly_eq_prod_sorted n (j + 2 + 2) (by lia) (by lia)
  have hQe := isEigenpoly_eq_prod_of (by lia) hQ a ha01 hGa
  have hRe := isEigenpoly_eq_prod_of (by lia) hR b hb01 hGb
  have has := eigPoly_roots_symm n (j + 2) (by lia) (by lia) a ha ha01 hGa
  have hbs := eigPoly_roots_symm n (j + 2 + 2) (by lia) (by lia) b hb hb01 hGb
  have hbet : ∀ l l' : Fin (j + 2), b l < b l' → b l' < 1 / 2 →
      ∃ r, b l < a r ∧ a r < b l' := by
    intro l l' hll' hl'
    have hgroot : ∀ l, (eigPoly n (j + 2 + 2)).eval (b l) = 0 := by
      intro l; rw [hGb, eval_mul, eval_prod,
        Finset.prod_eq_zero (Finset.mem_univ l) (by simp), mul_zero]
    obtain ⟨t, ht1, ht2, hft⟩ := zero_between2 n (j + 2) (by lia) (by lia) (b l) (b l')
      (hb01 l).1 hll' hl' (hgroot l) (hgroot l')
    rw [hGa] at hft
    obtain ⟨r, hr⟩ := root_index_of_prod a t (by linarith [(hb01 l).1])
      (by linarith [(hb01 l').2]) hft
    exact ⟨r, hr ▸ ht1, hr ▸ ht2⟩
  refine ⟨fun i => a i / (1 - a i), fun i => b i / (1 - b i), fun i i' h => moebius_lt (ha h)
    (ha01 i').2, fun i i' h => moebius_lt (hb h) (hb01 i').2, fun i => ?_, fun i => ?_,
    fun i hi => ?_, fun hodd => ?_⟩
  · rw [hQe, IsRoot, eval_prod]; exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  · rw [hRe, IsRoot, eval_prod]; exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  · obtain ⟨h1, h2⟩ := lower_interlace a b ha hb has hbs hbet i hi
    have e1 : a ⟨j - 1 - i, by lia⟩ = 1 - a ⟨i, by lia⟩ := by
      rw [← has]; congr 1; ext; simp; lia
    have e2 : b ⟨j - i, by lia⟩ = 1 - b ⟨i + 1, by lia⟩ := by
      rw [← hbs]; congr 1; ext; simp
    have e3 : b ⟨j + 1 - i, by lia⟩ = 1 - b ⟨i, by lia⟩ := by
      rw [← hbs]; congr 1; ext; simp
    refine ⟨moebius_lt h1 (ha01 _).2, moebius_lt h2 (hb01 _).2, ?_, ?_⟩
    · change b _ / (1 - b _) < a _ / (1 - a _)
      exact moebius_lt (by rw [e1, e2]; linarith) (ha01 _).2
    · change a _ / (1 - a _) < b _ / (1 - b _)
      exact moebius_lt (by rw [e1, e3]; linarith) (hb01 _).2
  · obtain ⟨k, rfl⟩ := hodd
    have e1 : a ⟨(2 * k + 1 - 1) / 2, by lia⟩ = 1 - a ⟨(2 * k + 1 - 1) / 2, by lia⟩ := by
      rw [← has]; congr 1; ext; simp; lia
    have e2 : b ⟨(2 * k + 1 + 1) / 2, by lia⟩ = 1 - b ⟨(2 * k + 1 + 1) / 2, by lia⟩ := by
      rw [← hbs]; congr 1; ext; simp; lia
    have ea : a ⟨(2 * k + 1 - 1) / 2, by lia⟩ = 1 / 2 := by linarith
    have eb : b ⟨(2 * k + 1 + 1) / 2, by lia⟩ = 1 / 2 := by linarith
    refine ⟨?_, ?_⟩
    · change a _ / (1 - a _) = 1; rw [ea]; norm_num
    · change b _ / (1 - b _) = 1; rw [eb]; norm_num

/-- **Kostov, Theorem 4 (#1320), index form.**  Let `1 ≤ j` and `j + 5 ≤ n` (that is
`j + 2 ≤ n - 3`).  Let `x_0 < ... < x_{j-1}` be the roots of `Q_{n,j}` and `z_0 < ... < z_{j+1}`
those of `Q_{n,j+2}` (zero-based).  Then for `0 ≤ i < ⌊j/2⌋`: `x_i ∈ (z_i, z_{i+1})` and
`x_{j-1-i} ∈ (z_{j-i}, z_{j+1-i})`, and for odd `j` the central roots
`x_{(j-1)/2} = z_{(j+1)/2} = 1`.  (This is not ordinary interlacing.)  Checked exactly for
`6 ≤ n ≤ 11`. -/
private theorem eigenpoly_two_step {n j : ℕ} (hj1 : 1 ≤ j) (hj : j + 5 ≤ n)
    {Q R : ℝ[X]} (hQ : IsEigenpoly n j Q) (hR : IsEigenpoly n (j + 2) R) :
    ∃ x z : ℕ → ℝ, StrictMonoOn x (Set.Iio j) ∧ StrictMonoOn z (Set.Iio (j + 2)) ∧
      (∀ i, i < j → Q.IsRoot (x i)) ∧ (∀ i, i < j + 2 → R.IsRoot (z i)) ∧
      (∀ i, i < j / 2 →
        z i < x i ∧ x i < z (i + 1) ∧ z (j - i) < x (j - 1 - i) ∧
          x (j - 1 - i) < z (j + 1 - i)) ∧
      (Odd j → x ((j - 1) / 2) = 1 ∧ z ((j + 1) / 2) = 1) := by
  obtain ⟨x, z, hx, hz, hQx, hRz, hmain, hodd⟩ := eigenpoly_two_step_aux hj1 hj hQ hR
  refine ⟨fun i => if h : i < j then x ⟨i, h⟩ else 0,
    fun i => if h : i < j + 2 then z ⟨i, h⟩ else 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    simp only [Set.mem_Iio] at ha hb
    simp only [ha, hb, dite_true]
    exact hx (by simpa [Fin.lt_def] using hab)
  · intro a ha b hb hab
    simp only [Set.mem_Iio] at ha hb
    simp only [ha, hb, dite_true]
    exact hz (by simpa [Fin.lt_def] using hab)
  · intro i hi
    simp only [hi, dite_true]
    exact hQx _
  · intro i hi
    simp only [hi, dite_true]
    exact hRz _
  · intro i hi
    have h := hmain i hi
    have hs : i < j ∧ i < j + 2 ∧ i + 1 < j + 2 ∧ j - i < j + 2 ∧
        j - 1 - i < j ∧ j + 1 - i < j + 2 := by lia
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hs
    simpa only [e1, e2, e3, e4, e5, e6, dite_true] using h
  · intro ho
    have h := hodd ho
    have hs : (j - 1) / 2 < j ∧ (j + 1) / 2 < j + 2 := by lia
    simpa only [hs.1, hs.2, dite_true] using h

/-- The canonical reduced eigenpolynomials satisfy Kostov's two-step comparison. -/
theorem eigenpolynomial_two_step (n j : ℕ) (hj1 : 1 ≤ j) (hj : j + 5 ≤ n) :
    ∃ x z : ℕ → ℝ, StrictMonoOn x (Set.Iio j) ∧ StrictMonoOn z (Set.Iio (j + 2)) ∧
      (∀ i, i < j → (eigenpolynomial n j).IsRoot (x i)) ∧
      (∀ i, i < j + 2 → (eigenpolynomial n (j + 2)).IsRoot (z i)) ∧
      (∀ i, i < j / 2 →
        z i < x i ∧ x i < z (i + 1) ∧ z (j - i) < x (j - 1 - i) ∧
          x (j - 1 - i) < z (j + 1 - i)) ∧
      (Odd j → x ((j - 1) / 2) = 1 ∧ z ((j + 1) / 2) = 1) :=
  eigenpoly_two_step hj1 hj (eigenpolynomial_isEigenpoly n j (by lia))
    (eigenpolynomial_isEigenpoly n (j + 2) (by lia))

end Kostov
end RealRooted
