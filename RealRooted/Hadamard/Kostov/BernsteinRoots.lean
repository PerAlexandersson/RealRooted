module

public import RealRooted.Hadamard.Kostov.Bernstein

@[expose] public noncomputable section

open Polynomial

namespace RealRooted
namespace Kostov

lemma opp_sign_cases {a b : ℝ} (h : SignType.sign a = -SignType.sign b) (ha : a ≠ 0) :
    (a < 0 ∧ 0 < b) ∨ (0 < a ∧ b < 0) := by
  rcases lt_or_gt_of_ne ha with ha | ha
  · left
    rw [sign_neg ha] at h
    refine ⟨ha, sign_eq_one_iff.mp ?_⟩
    rcases (SignType.sign b).trichotomy with h' | h' | h' <;> simp_all
  · right
    rw [sign_pos ha] at h
    refine ⟨ha, sign_eq_neg_one_iff.mp ?_⟩
    rcases (SignType.sign b).trichotomy with h' | h' | h' <;> simp_all

/-- **Sign variations of the coefficients are bounded by roots.** If the signs of the
coefficients of `P` agree with the signs of `f` at increasing nodes `x k`, then `f` has at least
`signVariations P` distinct zeros between the nodes. -/
lemma signVariations_le_roots (f : ℝ → ℝ) (hf : Continuous f) (x : ℕ → ℝ)
    (hx : StrictMono x)
    (lo : ℕ) : ∀ (N : ℕ) (P : ℝ[X]) (hi : ℕ), P.support.card = N →
    (∀ k, P.coeff k ≠ 0 → lo ≤ k ∧ k ≤ hi ∧
      SignType.sign (P.coeff k) = SignType.sign (f (x k))) →
    ∃ s : Finset ℝ, P.signVariations ≤ s.card ∧
      ∀ z ∈ s, f z = 0 ∧ x lo < z ∧ z < x hi := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro P hi hN hP
  by_cases hP0 : P = 0
  · exact ⟨∅, by simp [hP0], by simp⟩
  have hsv := signVariations_eq_eraseLead_add_ite hP0
  set d := P.natDegree with hd
  have hld : P.coeff d ≠ 0 := leadingCoeff_ne_zero.mpr hP0
  obtain ⟨hlo_d, hd_hi, hsd⟩ := hP d hld
  by_cases hE : P.eraseLead = 0
  · have := sign_ne_zero.mpr (leadingCoeff_ne_zero.mpr hP0)
    exact ⟨∅, by simp_all, by simp⟩
  set E := P.eraseLead with hE_def
  have hEd : E.natDegree < d := by
    rcases eraseLead_natDegree_lt_or_eraseLead_eq_zero P with h | h <;> simp_all
  have hEcoeff : ∀ k, E.coeff k ≠ 0 → k ≠ d ∧ E.coeff k = P.coeff k := by
    intro k hk
    rw [hE_def, eraseLead_coeff] at hk ⊢
    by_cases hkd : k = d <;> simp_all
  have hNpos : 0 < N := by
    rw [← hN]
    exact Finset.card_pos.mpr (support_nonempty.mpr hP0)
  obtain ⟨s, hs1, hs2⟩ := ih (N - 1) (by lia) E E.natDegree
    (by rw [hE_def, card_support_eraseLead, hN]) (by
      intro k hk
      obtain ⟨-, hk'⟩ := hEcoeff k hk
      obtain ⟨h1, -, h3⟩ := hP k (by rwa [← hk'])
      exact ⟨h1, le_natDegree_of_ne_zero hk, by rw [hk']; exact h3⟩)
  set e := E.natDegree with he
  have hle : E.coeff e ≠ 0 := leadingCoeff_ne_zero.mpr hE
  obtain ⟨-, hEe⟩ := hEcoeff e hle
  obtain ⟨hlo_e, -, hse⟩ := hP e (by rw [← hEe]; exact hle)
  have hxe : x e < x d := hx hEd
  by_cases hcond : SignType.sign P.leadingCoeff = -SignType.sign E.leadingCoeff
  · -- a genuine sign change: produce a new root between `x e` and `x d`
    have hcond' : SignType.sign (f (x d)) = -SignType.sign (f (x e)) := by
      rw [← hsd, ← hse, ← hEe]
      exact hcond
    have hfd : f (x d) ≠ 0 := by
      intro h0; rw [h0, sign_zero] at hsd; exact hld (sign_eq_zero_iff.mp hsd)
    have hz : ∃ z, x e < z ∧ z < x d ∧ f z = 0 := by
      rcases opp_sign_cases hcond' hfd with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · obtain ⟨z, ⟨hz1, hz2⟩, hz3⟩ :=
          intermediate_value_Ioo' hxe.le hf.continuousOn ⟨h1, h2⟩
        exact ⟨z, hz1, hz2, hz3⟩
      · obtain ⟨z, ⟨hz1, hz2⟩, hz3⟩ :=
          intermediate_value_Ioo hxe.le hf.continuousOn ⟨h2, h1⟩
        exact ⟨z, hz1, hz2, hz3⟩
    obtain ⟨z, hz1, hz2, hz3⟩ := hz
    have hzs : z ∉ s := fun h => by linarith [(hs2 z h).2.2]
    refine ⟨insert z s, ?_, ?_⟩
    · rw [hsv, ite_eq_left hcond, Finset.card_insert_of_notMem hzs]
      lia
    · intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact ⟨hz3, lt_of_le_of_lt (hx.monotone hlo_e) hz1,
          lt_of_lt_of_le hz2 (hx.monotone hd_hi)⟩
      · obtain ⟨h1, h2, h3⟩ := hs2 w hw
        exact ⟨h1, h2, h3.trans (hxe.trans_le (hx.monotone hd_hi))⟩
  · refine ⟨s, ?_, ?_⟩
    · rw [hsv, ite_eq_right hcond]; simpa using hs1
    · intro w hw
      obtain ⟨h1, h2, h3⟩ := hs2 w hw
      exact ⟨h1, h2, h3.trans (hxe.trans_le (hx.monotone hd_hi))⟩

/-- The polynomial `∑_k G(k/n) C(n,k) t^k`, so that `B_n G (y) = (1-y)^n p(y/(1-y))`. -/
def coeffPoly (n : ℕ) (G : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (G.eval ((k : ℝ) / n) * n.choose k) * X ^ k

lemma coeffPoly_coeff (n : ℕ) (G : ℝ[X]) (k : ℕ) :
    (coeffPoly n G).coeff k = if k ≤ n then G.eval ((k : ℝ) / n) * n.choose k else 0 := by
  simp only [coeffPoly, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp

private lemma sum_bb_eval (n : ℕ) (c : ℕ → ℝ) (y : ℝ) (hy : y ≠ 1) :
    (∑ k ∈ Finset.range (n + 1), C (c k) * bb n k).eval y =
      (1 - y) ^ n * ∑ k ∈ Finset.range (n + 1), c k * (y / (1 - y)) ^ k := by
  have hy' : 1 - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
  rw [eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [bb, eval_mul, eval_C, eval_pow, eval_X, eval_sub, eval_one]
  rw [show (1 - y) ^ n = (1 - y) ^ (n - k) * (1 - y) ^ k by
    rw [← pow_add, Nat.sub_add_cancel (by simpa using Finset.mem_range.mp hk)], div_pow]
  field_simp

lemma bernOp_eval_eq (n : ℕ) (G : ℝ[X]) (y : ℝ) (hy : y ≠ 1) :
    (bernOp n G).eval y = (1 - y) ^ n * (coeffPoly n G).eval (y / (1 - y)) := by
  rw [bernOp_apply, sum_bb_eval n _ y hy, coeffPoly, eval_finsetSum]
  simp

lemma card_le_countP_roots (p : ℝ[X]) (hp : p ≠ 0) (s : Finset ℝ)
    (hs : ∀ t ∈ s, p.IsRoot t ∧ 0 < t) : s.card ≤ p.roots.countP (0 < ·) := by
  rw [Multiset.countP_eq_card_filter]
  have : s.val ≤ p.roots.filter (0 < ·) := by
    rw [Multiset.le_iff_subset s.nodup]
    intro t ht
    obtain ⟨h1, h2⟩ := hs t ht
    exact Multiset.mem_filter.mpr ⟨(mem_roots hp).mpr h1, h2⟩
  exact Multiset.card_le_card this

/-- **Variation diminishing.** Zeros of `B_n G` in `(0,1)` are fewer than zeros of `G` in
`(1/n, (n-1)/n)`, for `G` vanishing at `0` and `1`. -/
lemma bernOp_roots_le (n : ℕ) (hn : 2 ≤ n) (G : ℝ[X]) (h0 : G.eval 0 = 0) (h1 : G.eval 1 = 0)
    (hB : bernOp n G ≠ 0) (s : Finset ℝ)
    (hs : ∀ y ∈ s, (bernOp n G).eval y = 0 ∧ 0 < y ∧ y < 1) :
    ∃ s' : Finset ℝ, s.card ≤ s'.card ∧
      ∀ z ∈ s', G.eval z = 0 ∧ (1 : ℝ) / n < z ∧ z < ((n - 1 : ℕ) : ℝ) / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by lia)
  set p := coeffPoly n G with hp_def
  have hp0 : p ≠ 0 := by
    intro hp
    apply hB
    rw [bernOp_apply]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [Finset.mem_range] at hk
    have := coeffPoly_coeff n G k
    rw [← hp_def, hp, coeff_zero, ite_eq_left (by lia)] at this
    rw [← this]; simp
  set s₁ := s.image (fun y => y / (1 - y)) with hs₁
  have hinj : Set.InjOn (fun y : ℝ => y / (1 - y)) s := by
    intro y hy y' hy' h
    simp only at h
    field_simp [show 1 - y ≠ 0 by linarith [(hs y hy).2.2],
      show 1 - y' ≠ 0 by linarith [(hs y' hy').2.2]] at h
    linarith
  have hcard : s₁.card = s.card := Finset.card_image_of_injOn hinj
  have hroots : ∀ t ∈ s₁, p.IsRoot t ∧ 0 < t := by
    intro t ht
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨e1, e2, e3⟩ := hs y hy
    have a1 : 0 < 1 - y := by linarith
    refine ⟨?_, div_pos e2 a1⟩
    rw [bernOp_eval_eq n G y (by linarith)] at e1
    exact (mul_eq_zero.mp e1).resolve_left (pow_ne_zero _ a1.ne')
  have hc1 := card_le_countP_roots p hp0 s₁ hroots
  have hc2 := roots_countP_pos_le_signVariations p
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
  refine ⟨s', by lia, fun z hz => ?_⟩
  obtain ⟨e1, e2, e3⟩ := hs'2 z hz
  exact ⟨e1, by simpa using e2, e3⟩

lemma bernOp_pow_eval_zero (n r : ℕ) (G : ℝ[X]) :
    (((bernOp n) ^ r) G).eval 0 = G.eval 0 := by
  induction r generalizing G <;> simp_all [pow_succ, Module.End.mul_apply, bernOp_eval_zero]

/-- Iterating the variation diminishing property. -/
lemma bernOp_pow_roots_le (n : ℕ) (hn : 2 ≤ n) : ∀ (r : ℕ) (G : ℝ[X]), G.eval 0 = 0 →
    G.eval 1 = 0 → ((bernOp n) ^ r) G ≠ 0 → ∀ s : Finset ℝ,
    (∀ y ∈ s, (((bernOp n) ^ r) G).eval y = 0 ∧ (1 : ℝ) / n < y ∧
      y < ((n - 1 : ℕ) : ℝ) / n) →
    ∃ s' : Finset ℝ, s.card ≤ s'.card ∧
      ∀ z ∈ s', G.eval z = 0 ∧ (1 : ℝ) / n < z ∧ z < ((n - 1 : ℕ) : ℝ) / n := by
  have hn0 : n ≠ 0 := by lia
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by lia)
  have hlt1 : ((n - 1 : ℕ) : ℝ) / n < 1 := by
    rw [div_lt_one hn', Nat.cast_sub (by lia)]; simp
  intro r
  induction r with
  | zero => intro G _ _ _ s hs; exact ⟨s, le_rfl, by simpa using hs⟩
  | succ r ih =>
    intro G h0 h1 hG s hs
    rw [pow_succ, Module.End.mul_apply] at hG hs
    obtain ⟨s₁, hs₁, hs₁'⟩ := ih (bernOp n G) (by rw [bernOp_eval_zero, h0])
      (by rw [bernOp_eval_one n hn0, h1]) hG s hs
    have hBG : bernOp n G ≠ 0 := fun h => hG (by simp [h])
    obtain ⟨s', hs', hs''⟩ := bernOp_roots_le n hn G h0 h1 hBG s₁ (by
      intro y hy
      obtain ⟨e1, e2, e3⟩ := hs₁' y hy
      exact ⟨e1, lt_trans (by positivity) e2, e3.trans hlt1⟩)
    exact ⟨s', hs₁.trans hs', hs''⟩

lemma eigPoly_eval_zero (n m : ℕ) (hm : 2 ≤ m) (hmn : m ≤ n) : (eigPoly n m).eval 0 = 0 :=
  eigen_eval_zero n _ _ (mu_lt_one n m hm hmn).ne (eigPoly_spec n m hm hmn).2.2

lemma eigPoly_eval_one (n m : ℕ) (hm : 2 ≤ m) (hmn : m ≤ n) : (eigPoly n m).eval 1 = 0 :=
  eigen_eval_one n (by lia) _ _ (mu_lt_one n m hm hmn).ne (eigPoly_spec n m hm hmn).2.2

lemma eigPoly_coeff_self (n m : ℕ) (hm : 2 ≤ m) (hmn : m ≤ n) :
    (eigPoly n m).coeff m = 1 := by
  obtain ⟨h1, h2, -⟩ := eigPoly_spec n m hm hmn
  simpa [leadingCoeff, h2] using h1.leadingCoeff

lemma eq_zero_of_natDegree_le_one_of_eval (F : ℝ[X]) (hF : F.natDegree ≤ 1) (h0 : F.eval 0 = 0)
    (h1 : F.eval 1 = 0) : F = 0 := by
  have hform := eq_X_add_C_of_natDegree_le_one hF
  rw [hform] at h0 h1 ⊢
  simp at h0 h1 ⊢
  simp [h0, show F.coeff 1 = 0 by linarith]

/-- Expansion in the eigenbasis of the polynomials vanishing at `0` and `1`. -/
lemma eig_expand (n : ℕ) : ∀ m : ℕ, m ≤ n → ∀ F : ℝ[X], F.natDegree ≤ m →
    F.eval 0 = 0 → F.eval 1 = 0 → ∃ a : ℕ → ℝ,
      F = ∑ d ∈ Finset.Icc 2 m, a d • eigPoly n d ∧ a m = F.coeff m := by
  intro m
  induction m with
  | zero =>
    intro _ F hF h0 h1
    have : F = 0 := eq_zero_of_natDegree_le_one_of_eval F (by lia) h0 h1
    exact ⟨0, by simp [this], by simp [this]⟩
  | succ m ih =>
    intro hmn F hF h0 h1
    by_cases hm : m = 0
    · subst hm
      have : F = 0 := eq_zero_of_natDegree_le_one_of_eval F hF h0 h1
      exact ⟨0, by simp [this], by simp [this]⟩
    obtain ⟨hmon, hdeg, -⟩ := eigPoly_spec n (m + 1) (by lia) hmn
    set c := F.coeff (m + 1) with hc
    set F' := F - c • eigPoly n (m + 1) with hF'
    have hF'd : F'.natDegree ≤ m := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro k hk
      rw [hF', coeff_sub, coeff_smul, smul_eq_mul]
      rcases Nat.lt_or_ge (m + 1) k with h | h
      · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hF h),
          coeff_eq_zero_of_natDegree_lt (by lia)]
        simp
      · obtain rfl : k = m + 1 := by lia
        rw [eigPoly_coeff_self n (m + 1) (by lia) hmn]
        ring
    have hF'0 : F'.eval 0 = 0 := by
      simp [hF', h0, eigPoly_eval_zero n (m + 1) (by lia) hmn]
    have hF'1 : F'.eval 1 = 0 := by
      simp [hF', h1, eigPoly_eval_one n (m + 1) (by lia) hmn]
    obtain ⟨a', ha', -⟩ := ih (by lia) F' hF'd hF'0 hF'1
    refine ⟨Function.update a' (m + 1) c, ?_, by simp⟩
    rw [Finset.sum_Icc_succ_top (by lia), Function.update_self]
    have : ∑ d ∈ Finset.Icc 2 m, Function.update a' (m + 1) c d • eigPoly n d =
        ∑ d ∈ Finset.Icc 2 m, a' d • eigPoly n d := by
      refine Finset.sum_congr rfl fun d hd => ?_
      rw [Function.update_of_ne (by simp at hd; lia)]
    rw [this, ← ha', hF']
    abel

/-- A monic polynomial with as many distinct roots as its degree is the product of the
corresponding linear factors. -/
lemma monic_eq_prod_of_roots (P : ℝ[X]) (hP : P.Monic) (S : Finset ℝ)
    (hS : ∀ z ∈ S, P.eval z = 0) (hcard : S.card = P.natDegree) :
    P = ∏ z ∈ S, (X - C z) := by
  have hP0 : P ≠ 0 := hP.ne_zero
  have hle : S.val ≤ P.roots :=
    (Multiset.le_iff_subset S.nodup).mpr fun z hz => (mem_roots hP0).mpr (hS z hz)
  have heq : S.val = P.roots :=
    Multiset.eq_of_le_of_card_le hle (by rw [← Finset.card_def, hcard]; exact card_roots' P)
  have := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hP
    (by rw [← heq, ← Finset.card_def, hcard])
  rw [Finset.prod_eq_multiset_prod, heq, this]

/-- Lower bound for the linear coefficient of a monic polynomial of degree `m` with roots `0`,
`1` and `m - 2` further roots in `(c, 1)`. -/
lemma coeff_one_bound (P : ℝ[X]) (m : ℕ) (hm : 2 ≤ m) (hP : P.Monic) (hd : P.natDegree = m)
    (h0 : P.eval 0 = 0) (h1 : P.eval 1 = 0) (c : ℝ) (hc : 0 < c) (s : Finset ℝ)
    (hs : m - 2 ≤ s.card) (hroots : ∀ z ∈ s, P.eval z = 0 ∧ c < z ∧ z < 1) :
    c ^ (m - 2) ≤ |P.coeff 1| := by
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq hs
  have h1t : (1 : ℝ) ∉ t := fun h => by linarith [(hroots 1 (hts h)).2.2]
  have h0t : (0 : ℝ) ∉ insert 1 t := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · norm_num at h
    · linarith [(hroots 0 (hts h)).2.1]
  have hcard : (insert (0 : ℝ) (insert 1 t)).card = P.natDegree := by
    rw [Finset.card_insert_of_notMem h0t, Finset.card_insert_of_notMem h1t, htc, hd]
    lia
  have hprod := monic_eq_prod_of_roots P hP _ (by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact h0
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact h1
    · exact (hroots z (hts hz)).1) hcard
  rw [Finset.prod_insert h0t, Finset.prod_insert h1t, map_zero, sub_zero] at hprod
  rw [hprod, show (1 : ℕ) = 0 + 1 from rfl, coeff_X_mul, coeff_zero_eq_eval_zero]
  simp only [eval_mul, eval_sub, eval_X, eval_C, eval_prod, zero_sub, neg_mul, one_mul, abs_neg,
    Finset.abs_prod, abs_neg]
  rw [← htc, ← Finset.prod_const]
  refine Finset.prod_le_prod₀ (fun _ _ => hc.le) fun z hz => ?_
  have := (hroots z (hts hz)).2.1
  rw [abs_of_pos (by linarith)]
  exact this.le

lemma bernOp_pow_eigPoly (n d : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) (r : ℕ) :
    ((bernOp n) ^ r) (eigPoly n d) = (mu n d) ^ r • eigPoly n d := by
  induction r <;> simp_all [pow_succ, Module.End.mul_apply, (eigPoly_spec n d hd hdn).2.2,
    map_smul, smul_smul, mul_comm]

/-- **Simple root at `0`.** The eigenpolynomial `G_m` (`2 ≤ m ≤ n`) has a simple zero at `0`:
its linear coefficient does not vanish.  (Proved by a variation-diminishing argument.) -/
theorem eigPoly_coeff_one_ne_zero (n m : ℕ) (hm : 2 ≤ m) (hmn : m ≤ n) :
    (eigPoly n m).coeff 1 ≠ 0 := by
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
    exact Finset.sum_eq_zero fun d hd => by
      simp [eigPoly_eval_zero n d (by simp at hd; lia) (by simp at hd; lia)]
  have hFr1 : ∀ r, (Fr r).eval 1 = 0 := by
    intro r
    rw [hFr, eval_finsetSum]
    exact Finset.sum_eq_zero fun d hd => by
      simp [eigPoly_eval_one n d (by simp at hd; lia) (by simp at hd; lia)]
  have hFrc : ∀ r k, (Fr r).coeff k =
      ∑ d ∈ Finset.Icc 2 m, a d * (mu n m / mu n d) ^ r * (eigPoly n d).coeff k := by
    intro r k
    simp [hFr, coeff_smul]
  have hFrdeg : ∀ r, (Fr r).natDegree ≤ m := by
    intro r
    refine natDegree_sum_le_of_forall_le _ _ fun d hd => ?_
    exact (natDegree_smul_le _ _).trans <| by
      rw [(eigPoly_spec n d (by simp at hd; lia) (by simp at hd; lia)).2.1]
      simp at hd
      lia
  have hFrm : ∀ r, (Fr r).coeff m = 1 := by
    intro r
    rw [hFrc, Finset.sum_eq_single m]
    · simp [div_self (mu_pos n m hmn).ne', eigPoly_coeff_self n m hm hmn, ham1]
    · intro d hd hdm
      rw [coeff_eq_zero_of_natDegree_lt]
      · ring
      simpa [(eigPoly_spec n d (by simp at hd; lia) (by simp at hd; lia)).2.1] using
        (show d < m by simp at hd; lia)
    · intro h; simp at h; lia
  have hFrd : ∀ r, (Fr r).natDegree = m := fun r =>
    natDegree_eq_of_le_of_coeff_ne_zero (hFrdeg r) (by rw [hFrm r]; exact one_ne_zero)
  have hFrmon : ∀ r, (Fr r).Monic := fun r => by simp [Monic, leadingCoeff, hFrd r, hFrm r]
  -- the roots of `F` between the interior nodes
  set s₀ := (Finset.range (m - 2)).image z with hs₀
  have hzinj : Set.InjOn z (Finset.range (m - 2)) := by
    intro i _ j _ h
    simp only [hz] at h
    field_simp at h
    exact_mod_cast (show (i : ℝ) = j by linarith)
  have hs₀c : s₀.card = m - 2 := by
    rw [hs₀, Finset.card_image_of_injOn hzinj, Finset.card_range]
  have hbound : ∀ r, (1 / (n : ℝ)) ^ (m - 2) ≤ |(Fr r).coeff 1| := by
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
    refine coeff_one_bound (Fr r) m hm (hFrmon r) (hFrd r) (hFr0 r) (hFr1 r) (1 / n)
      (by positivity) s (by lia) fun y hy => ?_
    obtain ⟨e1, e2, e3⟩ := hs' y hy
    refine ⟨e1, e2, e3.trans ?_⟩
    rw [div_lt_one hn0, Nat.cast_sub (by lia)]
    simp
  -- the limit
  have hT : Filter.Tendsto (fun r => (Fr r).coeff 1) Filter.atTop
      (nhds ((eigPoly n m).coeff 1)) := by
    simp_rw [hFrc]
    have hlim : (eigPoly n m).coeff 1 = ∑ d ∈ Finset.Icc 2 m,
        (if d = m then a d * (eigPoly n d).coeff 1 else 0) := by
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
        ((eigPoly n d).coeff 1)
      simpa using this
  have := ge_of_tendsto hT.abs (Filter.Eventually.of_forall hbound)
  intro h0
  rw [h0, abs_zero] at this
  have : 0 < (1 / (n : ℝ)) ^ (m - 2) := by positivity
  linarith

lemma natDegree_one_sub_X : (1 - X : ℝ[X]).natDegree = 1 := by
  rw [natDegree_sub_eq_right_of_natDegree_lt] <;> simp

lemma leadingCoeff_one_sub_X : (1 - X : ℝ[X]).leadingCoeff = -1 := by
  rw [show (1 - X : ℝ[X]) = -(X - C 1) by simp, leadingCoeff_neg, leadingCoeff_X_sub_C]

/-- The Bernstein operator commutes with the reflection `y ↦ 1 - y`. -/
lemma bernOp_comp_reflect (n : ℕ) (hn : n ≠ 0) (G : ℝ[X]) :
    bernOp n (G.comp (1 - X)) = (bernOp n G).comp (1 - X) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  refine Polynomial.funext fun y => ?_
  rw [eval_comp, bernOp_apply, bernOp_apply, eval_finsetSum, eval_finsetSum]
  simp only [eval_sub, eval_one, eval_X]
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  have hk' : k ≤ n := by lia
  rw [show n + 1 - 1 - k = n - k by lia]
  simp only [bb, eval_mul, eval_C, eval_pow, eval_X, eval_sub, eval_one, eval_comp]
  rw [Nat.choose_symm hk', show n - (n - k) = k by lia, Nat.cast_sub hk']
  have : 1 - ((n : ℝ) - k) / n = k / n := by field_simp; ring
  rw [this]
  ring

/-- **Reciprocity of the eigenpolynomials**: `G_m(1 - y) = (-1)^m G_m(y)`. -/
lemma eigPoly_reflect (n m : ℕ) (hm : 2 ≤ m) (hmn : m ≤ n) :
    (eigPoly n m).comp (1 - X) = C ((-1 : ℝ) ^ m) * eigPoly n m := by
  have hn : n ≠ 0 := by lia
  obtain ⟨hmon, hdeg, heig⟩ := eigPoly_spec n m hm hmn
  set G := eigPoly n m with hG
  have hdc : (G.comp (1 - X)).natDegree = m := by
    rw [natDegree_comp, natDegree_one_sub_X, hdeg, mul_one]
  have hlc : (G.comp (1 - X)).coeff m = (-1) ^ m := by
    have := leadingCoeff_comp (p := G) (q := 1 - X) (by rw [natDegree_one_sub_X]; norm_num)
    rw [leadingCoeff, hdc, hmon.leadingCoeff, leadingCoeff_one_sub_X, hdeg, one_mul] at this
    exact this
  have heig' : bernOp n (G.comp (1 - X)) = mu n m • G.comp (1 - X) := by
    rw [bernOp_comp_reflect n hn, heig]
    simp [smul_eq_C_mul, mul_comp]
  obtain ⟨c, hc⟩ := eigen_unique n m hm hmn G (G.comp (1 - X)) hmon.ne_zero (by lia)
    (by lia) heig heig'
  have : c = (-1) ^ m := by
    have h2 := congrArg (fun P => P.coeff m) hc
    simp only [coeff_smul, smul_eq_mul] at h2
    have hcm : G.coeff m = 1 := by rw [← hdeg]; exact hmon.leadingCoeff
    rw [hlc, hcm, mul_one] at h2
    exact h2.symm
  rw [hc, this, smul_eq_C_mul]

/-- Linear independence of the polynomials `X^k (1-X)^(n-k)`, `k = 0..n`. -/
lemma bbsum_eq_zero : ∀ (n : ℕ) (c : ℕ → ℝ),
    ∑ k ∈ Finset.range (n + 1), C (c k) * bb n k = 0 → ∀ k ≤ n, c k = 0 := by
  intro n
  induction n with
  | zero =>
    intro c h k hk
    obtain rfl : k = 0 := by lia
    simpa [bb] using h
  | succ n ih =>
    intro c h
    have h0 : c 0 = 0 := by
      have := congrArg (eval 0) h
      rw [eval_finsetSum, Finset.sum_eq_single 0] at this
      · simpa [bb] using this
      · intro k _ hk
        rw [eval_mul, bb_eval_zero, ite_eq_right hk, mul_zero]
      · intro h; simp at h
    rw [Finset.sum_range_succ', h0, map_zero, zero_mul, add_zero] at h
    have h' : X * ∑ k ∈ Finset.range (n + 1), C (c (k + 1)) * bb n k = 0 := by
      rw [← h, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [bb, bb, show n + 1 - (k + 1) = n - k by lia, pow_succ]
      ring
    have h'' := (mul_eq_zero.mp h').resolve_left X_ne_zero
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact h0
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by lia⟩
      exact ih (fun k => c (k + 1)) h'' k' (by lia)

/-- `Ψ_n T = ∑_k T_k X^k (1-X)^(n-k)`, i.e. `(1-y)^n T(y/(1-y))`. -/
def Psi (n : ℕ) (T : ℝ[X]) : ℝ[X] := ∑ k ∈ Finset.range (n + 1), C (T.coeff k) * bb n k

lemma Psi_eval (n : ℕ) (T : ℝ[X]) (hT : T.natDegree ≤ n) (y : ℝ) (hy : y ≠ 1) :
    (Psi n T).eval y = (1 - y) ^ n * T.eval (y / (1 - y)) := by
  rw [Psi, sum_bb_eval n _ y hy, eval_eq_sum_range' (n := n + 1) (by lia)]

/-- `Φ_d H = ∑_i H_i X^i (X+1)^(d-i)`, i.e. `(1+x)^d H(x/(1+x))`. -/
def Phi (d : ℕ) (H : ℝ[X]) : ℝ[X] :=
  ∑ i ∈ Finset.range (d + 1), C (H.coeff i) * (X ^ i * (X + 1) ^ (d - i))

lemma Phi_eval (d : ℕ) (H : ℝ[X]) (hH : H.natDegree ≤ d) (x : ℝ) (hx : x ≠ -1) :
    (Phi d H).eval x = (1 + x) ^ d * H.eval (x / (1 + x)) := by
  have hx' : 1 + x ≠ 0 := by
    intro h; apply hx; linarith
  rw [Phi, eval_finsetSum, eval_eq_sum_range' (n := d + 1) (by lia), Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  simp only [eval_mul, eval_C, eval_pow, eval_X, eval_add, eval_one]
  rw [show (1 + x) ^ d = (1 + x) ^ (d - k) * (1 + x) ^ k by
    rw [← pow_add, Nat.sub_add_cancel (by lia)], div_pow]
  field_simp
  ring

lemma monic_X_pow_mul_X_add_one_pow (i d : ℕ) (hi : i ≤ d) :
    (X ^ i * (X + 1) ^ (d - i) : ℝ[X]).Monic ∧
      (X ^ i * (X + 1) ^ (d - i) : ℝ[X]).natDegree = d := by
  have h1 : (X + 1 : ℝ[X]).Monic := by simpa using monic_X_add_C (1 : ℝ)
  refine ⟨(monic_X_pow i).mul (h1.pow _), ?_⟩
  rw [(monic_X_pow i).natDegree_mul (h1.pow _), natDegree_X_pow, h1.natDegree_pow,
    show (X + 1 : ℝ[X]) = X + C 1 by simp, natDegree_X_add_C]
  lia

lemma Phi_natDegree_le (d : ℕ) (H : ℝ[X]) : (Phi d H).natDegree ≤ d := by
  refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
  rw [Finset.mem_range] at hi
  exact (natDegree_C_mul_le _ _).trans (monic_X_pow_mul_X_add_one_pow i d (by lia)).2.le

lemma Phi_coeff_top (d : ℕ) (H : ℝ[X]) (hH : H.natDegree ≤ d) :
    (Phi d H).coeff d = H.eval 1 := by
  rw [Phi, finsetSum_coeff, eval_eq_sum_range' (n := d + 1) (by lia)]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  obtain ⟨hm, hd⟩ := monic_X_pow_mul_X_add_one_pow i d (by lia)
  have hc := hm.coeff_natDegree
  rw [hd] at hc
  rw [coeff_C_mul, hc]
  simp

lemma eval_reflect_eq (f : ℝ[X]) (N : ℕ) (hf : f.natDegree ≤ N) (w : ℝ) (hw : w ≠ 0) :
    (reflect N f).eval w = w ^ N * f.eval (1 / w) := by
  let : Invertible (1 / w) := invertibleOfNonzero (one_div_ne_zero hw)
  have := eval₂_reflect_mul_pow (RingHom.id ℝ) (1 / w) N f hf
  rw [invOf_eq_inv, one_div, inv_inv] at this
  change (reflect N f).eval w * (w⁻¹) ^ N = f.eval w⁻¹ at this
  rw [one_div, ← this, inv_pow]
  field_simp

/-- Two polynomials agreeing off a finite set are equal. -/
lemma eq_of_eval_eq_off (p q : ℝ[X]) (S : Finset ℝ) (h : ∀ x ∉ S, p.eval x = q.eval x) :
    p = q :=
  eq_of_infinite_eval_eq p q (Set.Infinite.mono (fun x hx => h x hx)
    (S.finite_toSet.infinite_compl))

end Kostov
end RealRooted
