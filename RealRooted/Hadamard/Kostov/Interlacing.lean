import RealRooted.Hadamard.Kostov.RootReal

open Polynomial

noncomputable section

namespace RealRooted
namespace Kostov

/-- `F` has `k` strict sign changes at increasing points of `(0,1)`. -/
def Alt (F : ℝ[X]) (k : ℕ) : Prop :=
  ∃ p : ℕ → ℝ, 0 < p 0 ∧ p k < 1 ∧ (∀ i < k, p i < p (i + 1)) ∧
    ∀ i < k, F.eval (p i) * F.eval (p (i + 1)) < 0

lemma chain_le {α : Type*} [Preorder α] {p : ℕ → α} {k : ℕ}
    (h : ∀ i < k, p i < p (i + 1)) :
    ∀ i j, i ≤ j → j ≤ k → p i ≤ p j := by
  intro i j hij hjk
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact (ih (by lia)).trans (h j (by lia)).le

lemma chain_lt {α : Type*} [Preorder α] {p : ℕ → α} {k : ℕ}
    (h : ∀ i < k, p i < p (i + 1)) :
    ∀ i j, i < j → j ≤ k → p i < p j := by
  intro i j hij hjk
  exact lt_of_lt_of_le (h i (by lia)) (chain_le h (i + 1) j hij hjk)

lemma Alt.mono {F : ℝ[X]} {k k' : ℕ} (h : Alt F k) (hk : k' ≤ k) : Alt F k' := by
  obtain ⟨p, h0, h1, hinc, halt⟩ := h
  exact ⟨p, h0, lt_of_le_of_lt (chain_le hinc k' k hk le_rfl) h1, fun i hi => hinc i (by lia),
    fun i hi => halt i (by lia)⟩

lemma exists_root_of_mul_neg (R : ℝ[X]) {a b : ℝ} (hab : a < b)
    (h : R.eval a * R.eval b < 0) : ∃ r, a < r ∧ r < b ∧ R.eval r = 0 := by
  rcases mul_neg_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨z, ⟨hz1, hz2⟩, hz3⟩ :=
      intermediate_value_Ioo' hab.le (Polynomial.continuous R).continuousOn ⟨h2, h1⟩
    exact ⟨z, hz1, hz2, hz3⟩
  · obtain ⟨z, ⟨hz1, hz2⟩, hz3⟩ :=
      intermediate_value_Ioo hab.le (Polynomial.continuous R).continuousOn ⟨h1, h2⟩
    exact ⟨z, hz1, hz2, hz3⟩

/-- A nonzero polynomial with `k` strict sign changes has degree at least `k`. -/
lemma le_natDegree_of_alt (R : ℝ[X]) (hR : R ≠ 0) (p : ℕ → ℝ) (k : ℕ)
    (hinc : ∀ i < k, p i < p (i + 1)) (halt : ∀ i < k, R.eval (p i) * R.eval (p (i + 1)) < 0) :
    k ≤ R.natDegree := by
  have hr : ∀ i, ∃ r : ℝ, i < k → p i < r ∧ r < p (i + 1) ∧ R.eval r = 0 := by
    intro i
    by_cases hi : i < k
    · obtain ⟨r, h1, h2, h3⟩ := exists_root_of_mul_neg R (hinc i hi) (halt i hi)
      exact ⟨r, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose r hr using hr
  have hinj : Set.InjOn r (Finset.range k) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := (hr a ha).2.1
      have := (hr b hb).1
      have := chain_le hinc (a + 1) b h hb.le
      linarith
    · have := (hr b hb).2.1
      have := (hr a ha).1
      have := chain_le hinc (b + 1) a h ha.le
      linarith
  have hsub : (Finset.range k).image r ⊆ R.roots.toFinset := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    rw [Finset.mem_range] at hi
    exact Multiset.mem_toFinset.mpr ((mem_roots hR).mpr (hr i hi).2.2)
  calc k = ((Finset.range k).image r).card := by
        rw [Finset.card_image_of_injOn hinj, Finset.card_range]
    _ ≤ R.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ R.roots.card := Multiset.toFinset_card_le _
    _ ≤ R.natDegree := card_roots' R

lemma mul_neg_of_sign_eq_neg {a b : ℝ} (ha : a ≠ 0)
    (h : SignType.sign a = -SignType.sign b) : a * b < 0 := by
  rcases opp_sign_cases h ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact mul_neg_of_neg_of_pos h1 h2
  · exact mul_neg_of_pos_of_neg h1 h2

lemma mul_pos_of_not_sign_eq_neg {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ¬ SignType.sign a = -SignType.sign b) : 0 < a * b := by
  rcases lt_or_gt_of_ne ha with ha | ha <;> rcases lt_or_gt_of_ne hb with hb | hb
  · exact mul_pos_of_neg_of_neg ha hb
  · exfalso; apply h; rw [sign_neg ha, sign_pos hb]
  · exfalso; apply h; rw [sign_neg hb, sign_pos ha]; rfl
  · exact mul_pos ha hb

/-- The sign variations of the coefficients are realised by an increasing chain of
indices with strictly alternating coefficients, ending at the leading coefficient. -/
lemma signVariations_alt_idx : ∀ (N : ℕ) (P : ℝ[X]), P.support.card = N → P ≠ 0 →
    ∃ idx : ℕ → ℕ, (∀ i < P.signVariations, idx i < idx (i + 1)) ∧
      idx P.signVariations = P.natDegree ∧
      (∀ i ≤ P.signVariations, P.coeff (idx i) ≠ 0) ∧
      (∀ i < P.signVariations, P.coeff (idx i) * P.coeff (idx (i + 1)) < 0) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro P hN hP0
  have hsv := signVariations_eq_eraseLead_add_ite hP0
  have hld : P.coeff P.natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hP0
  by_cases hE : P.eraseLead = 0
  · have h0 : P.signVariations = 0 := by
      rw [hsv, hE, ite_eq_right]
      · simp
      · simp only [leadingCoeff_zero, sign_zero, neg_zero]
        exact sign_ne_zero.mpr (leadingCoeff_ne_zero.mpr hP0)
    refine ⟨fun _ => P.natDegree, ?_, by simp, ?_, ?_⟩
    · intro i hi; rw [h0] at hi; exact absurd hi (Nat.not_lt_zero _)
    · intro i _; exact hld
    · intro i hi; rw [h0] at hi; exact absurd hi (Nat.not_lt_zero _)
  set E := P.eraseLead with hE_def
  have hEd : E.natDegree < P.natDegree := by
    rcases eraseLead_natDegree_lt_or_eraseLead_eq_zero P with h | h
    · exact h
    · exact absurd h hE
  have hNpos : 0 < N := by
    rw [← hN]; exact Finset.card_pos.mpr (support_nonempty.mpr hP0)
  obtain ⟨idE, hinc, hlast, hnz, halt⟩ := ih (N - 1) (by lia) E
    (by rw [hE_def, card_support_eraseLead, hN]) hE
  have hcoeff : ∀ i ≤ E.signVariations, P.coeff (idE i) = E.coeff (idE i) := by
    intro i hi
    have : idE i ≤ E.natDegree := hlast ▸ chain_le hinc i _ hi le_rfl
    rw [hE_def, eraseLead_coeff_of_ne _ (by lia)]
  have hidx_lt : ∀ i ≤ E.signVariations, idE i < P.natDegree := by
    intro i hi
    exact lt_of_le_of_lt (hlast ▸ chain_le hinc i _ hi le_rfl) hEd
  have hEl : E.coeff E.natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hE
  set s := E.signVariations with hs
  by_cases hcond : SignType.sign P.leadingCoeff = -SignType.sign E.leadingCoeff
  · have hsvP : P.signVariations = s + 1 := by rw [hsv, ite_eq_left hcond]
    refine ⟨fun i => if i ≤ s then idE i else P.natDegree, ?_, ?_, ?_, ?_⟩
    · intro i hi
      rw [hsvP] at hi
      by_cases his : i + 1 ≤ s
      · simp only [ite_eq_left his, ite_eq_left (show i ≤ s by lia)]; exact hinc i (by lia)
      · simp only [ite_eq_right his, ite_eq_left (show i ≤ s by lia)]; exact hidx_lt i (by lia)
    · simp [hsvP]
    · intro i hi
      by_cases his : i ≤ s
      · simp only [ite_eq_left his]; rw [hcoeff i his]; exact hnz i his
      · simp only [ite_eq_right his]; exact hld
    · intro i hi
      rw [hsvP] at hi
      by_cases his : i + 1 ≤ s
      · simp only [ite_eq_left his, ite_eq_left (show i ≤ s by lia)]
        rw [hcoeff i (by lia), hcoeff (i + 1) his]; exact halt i (by lia)
      · obtain rfl : i = s := by lia
        simp only [ite_eq_right his, le_refl, ite_true]
        rw [hcoeff s le_rfl, hlast, mul_comm]
        exact mul_neg_of_sign_eq_neg hld hcond
  · have hsvP : P.signVariations = s := by rw [hsv, ite_eq_right hcond]; simp
    refine ⟨fun i => if i < s then idE i else P.natDegree, ?_, ?_, ?_, ?_⟩
    · intro i hi
      rw [hsvP] at hi
      by_cases his : i + 1 < s
      · simp only [ite_eq_left his, ite_eq_left (show i < s by lia)]; exact hinc i (by lia)
      · simp only [ite_eq_right his, ite_eq_left hi]; exact hidx_lt i (by lia)
    · simp [hsvP]
    · intro i hi
      by_cases his : i < s
      · simp only [ite_eq_left his]; rw [hcoeff i his.le]; exact hnz i his.le
      · simp only [ite_eq_right his]; exact hld
    · intro i hi
      rw [hsvP] at hi
      by_cases his : i + 1 < s
      · simp only [ite_eq_left his, ite_eq_left (show i < s by lia)]
        rw [hcoeff i (by lia), hcoeff (i + 1) his.le]; exact halt i (by lia)
      · have hs1 : i + 1 = s := by lia
        simp only [ite_eq_right his, ite_eq_left hi]
        have h1 := halt i hi
        rw [hcoeff i hi.le]
        rw [hs1, hlast] at h1
        have hpos := mul_pos_of_not_sign_eq_neg hld hEl hcond
        have hEi := hnz i hi.le
        -- `a * E < 0`, `P * E > 0` ⇒ `a * P < 0`
        have : (E.coeff (idE i) * P.coeff P.natDegree) *
            (P.coeff P.natDegree * E.coeff E.natDegree) =
            (E.coeff (idE i) * E.coeff E.natDegree) * (P.coeff P.natDegree) ^ 2 := by ring
        have hsq : 0 < (P.coeff P.natDegree) ^ 2 := by positivity
        by_contra hge
        push Not at hge
        have := mul_nonneg hge hpos.le
        nlinarith

/-- Roots produced by strict sign changes. -/
lemma exists_roots_of_alt (R : ℝ[X]) (p : ℕ → ℝ) (k : ℕ)
    (hinc : ∀ i < k, p i < p (i + 1)) (halt : ∀ i < k, R.eval (p i) * R.eval (p (i + 1)) < 0) :
    ∃ s : Finset ℝ, s.card = k ∧ ∀ r ∈ s, R.eval r = 0 ∧ p 0 < r ∧ r < p k := by
  have hr : ∀ i, ∃ r : ℝ, i < k → p i < r ∧ r < p (i + 1) ∧ R.eval r = 0 := by
    intro i
    by_cases hi : i < k
    · obtain ⟨r, h1, h2, h3⟩ := exists_root_of_mul_neg R (hinc i hi) (halt i hi)
      exact ⟨r, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose r hr using hr
  have hinj : Set.InjOn r (Finset.range k) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := (hr a ha).2.1
      have := (hr b hb).1
      have := chain_le hinc (a + 1) b h hb.le
      linarith
    · have := (hr b hb).2.1
      have := (hr a ha).1
      have := chain_le hinc (b + 1) a h ha.le
      linarith
  refine ⟨(Finset.range k).image r, by rw [Finset.card_image_of_injOn hinj, Finset.card_range],
    fun x hx => ?_⟩
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  rw [Finset.mem_range] at hi
  obtain ⟨h1, h2, h3⟩ := hr i hi
  exact ⟨h3, lt_of_le_of_lt (chain_le hinc 0 i (Nat.zero_le _) hi.le) h1,
    lt_of_lt_of_le h2 (chain_le hinc (i + 1) k hi le_rfl)⟩

/-- **Variation diminishing for sign changes.**  If `B_n F` has `k` strict sign changes in
`(0,1)`, so does `F` (for `F` vanishing at `0` and `1`). -/
lemma Alt.of_bernOp {n : ℕ} (hn : 2 ≤ n) {F : ℝ[X]} (h0 : F.eval 0 = 0) (h1 : F.eval 1 = 0)
    {k : ℕ} (h : Alt (bernOp n F) k) : Alt F k := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by lia)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨fun _ => 1 / 2, by norm_num, by norm_num, fun i hi => absurd hi (Nat.not_lt_zero _),
      fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  obtain ⟨a, ha0, ha1, hinc, halt⟩ := h
  set p := coeffPoly n F with hp
  have hlt1 : ∀ i ≤ k, a i < 1 := fun i hi => lt_of_le_of_lt (chain_le hinc i k hi le_rfl) ha1
  have hpos : ∀ i ≤ k, 0 < a i := fun i hi =>
    lt_of_lt_of_le ha0 (chain_le hinc 0 i (Nat.zero_le _) hi)
  set t : ℕ → ℝ := fun i => a i / (1 - a i) with ht
  have hBt : ∀ i ≤ k, (bernOp n F).eval (a i) = (1 - a i) ^ n * p.eval (t i) := fun i hi =>
    bernOp_eval_eq n F (a i) (hlt1 i hi).ne
  have htinc : ∀ i < k, t i < t (i + 1) := by
    intro i hi
    have h1 := hlt1 i hi.le
    have h2 := hlt1 (i + 1) hi
    have := hinc i hi
    simp only [ht]
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hpalt : ∀ i < k, p.eval (t i) * p.eval (t (i + 1)) < 0 := by
    intro i hi
    have := halt i hi
    rw [hBt i hi.le, hBt (i + 1) hi] at this
    have h1 := hlt1 i hi.le
    have h2 := hlt1 (i + 1) hi
    have hc : 0 < (1 - a i) ^ n * (1 - a (i + 1)) ^ n := by
      have : 0 < 1 - a i := by linarith
      have : 0 < 1 - a (i + 1) := by linarith
      positivity
    have e : (1 - a i) ^ n * p.eval (t i) * ((1 - a (i + 1)) ^ n * p.eval (t (i + 1))) =
        ((1 - a i) ^ n * (1 - a (i + 1)) ^ n) * (p.eval (t i) * p.eval (t (i + 1))) := by ring
    rw [e] at this
    exact neg_of_mul_neg_right this hc.le
  have hp0 : p ≠ 0 := by
    intro h
    have := hpalt 0 hk
    rw [h] at this
    simp at this
  obtain ⟨s, hs, hs'⟩ := exists_roots_of_alt p t k htinc hpalt
  have hcount := card_le_countP_roots p hp0 s fun r hr => by
    obtain ⟨e1, e2, -⟩ := hs' r hr
    exact ⟨e1, lt_trans (div_pos (hpos 0 (Nat.zero_le _)) (by linarith [hlt1 0 (Nat.zero_le _)]))
      e2⟩
  have hsv : k ≤ p.signVariations := by
    have := roots_countP_pos_le_signVariations p
    lia
  obtain ⟨idx, hiinc, -, hnz, halt'⟩ := signVariations_alt_idx _ p rfl hp0
  have hrange : ∀ i ≤ k, 1 ≤ idx i ∧ idx i ≤ n - 1 := by
    intro i hi
    have hne := hnz i (hi.trans hsv)
    rw [hp, coeffPoly_coeff] at hne
    by_cases hin : idx i ≤ n
    · rw [ite_eq_left hin] at hne
      have hk0 : idx i ≠ 0 := by
        intro h; rw [h] at hne; simp [h0] at hne
      have hkn : idx i ≠ n := by
        intro h; rw [h] at hne; simp [div_self hn0.ne', h1] at hne
      lia
    · rw [ite_eq_right hin] at hne; exact absurd rfl hne
  have hcoeff : ∀ i ≤ k, p.coeff (idx i) = F.eval ((idx i : ℝ) / n) * n.choose (idx i) := by
    intro i hi
    rw [hp, coeffPoly_coeff, ite_eq_left (by have := hrange i hi; lia)]
  refine ⟨fun i => (idx i : ℝ) / n, ?_, ?_, ?_, ?_⟩
  · have := (hrange 0 (Nat.zero_le _)).1
    exact div_pos (by exact_mod_cast (show 0 < idx 0 by lia)) hn0
  · have := (hrange k le_rfl).2
    rw [div_lt_one hn0]
    exact_mod_cast (show idx k < n by lia)
  · intro i hi
    exact div_lt_div_of_pos_right (by exact_mod_cast hiinc i (by lia)) hn0
  · intro i hi
    have := halt' i (by lia)
    rw [hcoeff i hi.le, hcoeff (i + 1) hi] at this
    have hc : (0 : ℝ) < (n.choose (idx i) : ℝ) * n.choose (idx (i + 1)) := by
      have := hrange i hi.le
      have := hrange (i + 1) hi
      have a1 : 0 < n.choose (idx i) := Nat.choose_pos (by lia)
      have a2 : 0 < n.choose (idx (i + 1)) := Nat.choose_pos (by lia)
      positivity
    have e : F.eval ((idx i : ℝ) / n) * n.choose (idx i) *
        (F.eval ((idx (i + 1) : ℝ) / n) * n.choose (idx (i + 1))) =
        ((n.choose (idx i) : ℝ) * n.choose (idx (i + 1))) *
          (F.eval ((idx i : ℝ) / n) * F.eval ((idx (i + 1) : ℝ) / n)) := by ring
    rw [e] at this
    exact neg_of_mul_neg_right this hc.le

lemma Alt.of_bernOp_pow {n : ℕ} (hn : 2 ≤ n) : ∀ (r : ℕ) (F : ℝ[X]), F.eval 0 = 0 →
    F.eval 1 = 0 → ∀ k, Alt (((bernOp n) ^ r) F) k → Alt F k := by
  intro r
  induction r with
  | zero => intro F _ _ k h; simpa using h
  | succ r ih =>
    intro F h0 h1 k h
    rw [pow_succ, Module.End.mul_apply] at h
    exact Alt.of_bernOp hn h0 h1 (ih (bernOp n F) (by rw [bernOp_eval_zero, h0])
      (by rw [bernOp_eval_one n (by lia), h1]) k h)

/-- Sorted version of `eigPoly_eq_prod`. -/
lemma eigPoly_eq_prod_sorted (n m : ℕ) (hm : 2 ≤ m) (hmn : m ≤ n) :
    ∃ z : Fin (m - 2) → ℝ, StrictMono z ∧ (∀ i, 0 < z i ∧ z i < 1) ∧
      eigPoly n m = X * (X - C 1) * ∏ i, (X - C (z i)) := by
  obtain ⟨z₀, hinj, hz01, hG⟩ := eigPoly_eq_prod n m hm hmn
  set s := Finset.univ.image z₀ with hs
  have hsc : s.card = m - 2 := by
    rw [hs, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  set e := s.orderIsoOfFin hsc
  refine ⟨fun i => (e i : ℝ), fun a b hab => e.strictMono hab, fun i => ?_, ?_⟩
  · obtain ⟨l, -, hl⟩ := Finset.mem_image.mp (e i).2
    change 0 < (e i : ℝ) ∧ (e i : ℝ) < 1
    rw [← hl]; exact hz01 l
  · rw [hG]
    congr 1
    change _ = ∏ i, (X - C ((e i : ℝ)))
    rw [← Finset.prod_image (f := fun a => X - C a) (s := Finset.univ) (g := z₀)
      (fun a _ b _ h => hinj h), ← hs, ← Finset.prod_coe_sort s]
    exact (Fintype.prod_equiv e.toEquiv _ _ (fun _ => rfl)).symm

/-- `X (X - 1) ∏ (X - z_i)` with increasing `z_i ∈ (0,1)` has `k` strict sign changes in
`(0,1)`. -/
lemma alt_of_prod {k : ℕ} (z : Fin k → ℝ) (hz : StrictMono z)
    (hz01 : ∀ i, 0 < z i ∧ z i < 1) :
    Alt (X * (X - C 1) * ∏ i, (X - C (z i))) k := by
  set e : ℕ → ℝ := fun i => if i = 0 then 0 else if h : i - 1 < k then z ⟨i - 1, h⟩ else 1
    with he
  have he0 : e 0 = 0 := by simp [he]
  have hek : e (k + 1) = 1 := by simp [he]
  have he_z : ∀ l : Fin k, e (l + 1) = z l := by
    intro l; simp [he, l.2]
  have he_inc : ∀ i < k + 1, e i < e (i + 1) := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [he0]
      by_cases hk : 0 < k
      · have := he_z ⟨0, hk⟩
        simp only [zero_add] at this
        rw [this]; exact (hz01 _).1
      · have : k = 0 := by lia
        subst this; rw [hek]; norm_num
    · by_cases hik : i < k
      · have h1 := he_z ⟨i - 1, by lia⟩
        have h2 := he_z ⟨i, hik⟩
        simp only [show i - 1 + 1 = i by lia] at h1
        rw [h1, h2]; exact hz (Fin.mk_lt_mk.mpr (by lia))
      · have : i = k := by lia
        subst this
        have h1 := he_z ⟨i - 1, by lia⟩
        simp only [show i - 1 + 1 = i by lia] at h1
        rw [h1, hek]; exact (hz01 _).2
  have he_mono := chain_le he_inc
  set q : ℕ → ℝ := fun i => (e i + e (i + 1)) / 2 with hq
  have hq1 : ∀ i ≤ k, e i < q i := fun i hi => by
    have := he_inc i (by lia); simp only [hq]; linarith
  have hq2 : ∀ i ≤ k, q i < e (i + 1) := fun i hi => by
    have := he_inc i (by lia); simp only [hq]; linarith
  have hq0 : ∀ i ≤ k, 0 < q i := fun i hi => by
    have := he_mono 0 i (Nat.zero_le _) (by lia); have := hq1 i hi; linarith
  have hqlt : ∀ i ≤ k, q i < 1 := fun i hi => by
    have := he_mono (i + 1) (k + 1) (by lia) le_rfl; have := hq2 i hi; linarith
  have heval : ∀ y : ℝ, (X * (X - C 1) * ∏ i, (X - C (z i))).eval y =
      y * (y - 1) * ∏ i, (y - z i) := by
    intro y; simp [eval_prod]
  refine ⟨q, hq0 0 (Nat.zero_le _), hqlt k le_rfl, fun i hi => ?_, fun i hi => ?_⟩
  · have := hq2 i hi.le; have := hq1 (i + 1) hi; linarith
  rw [heval, heval]
  have hfac : ∀ l : Fin k, l ≠ ⟨i, hi⟩ → 0 < (q i - z l) * (q (i + 1) - z l) := by
    intro l hl
    have hl' : l.1 ≠ i := fun h => hl (Fin.ext h)
    rcases lt_or_gt_of_ne hl' with h | h
    · have a1 := he_mono (l + 1) i (by lia) (by lia)
      rw [he_z] at a1
      have a2 := hq1 i hi.le
      have a3 := hq1 (i + 1) hi
      have a4 := he_mono i (i + 1) (by lia) (by lia)
      apply mul_pos <;> linarith
    · have a1 := he_mono (i + 2) (l + 1) (by lia) (by lia)
      rw [he_z] at a1
      have a2 := hq2 (i + 1) hi
      have a3 := hq2 i hi.le
      have a4 := he_mono (i + 1) (i + 2) (by lia) (by lia)
      apply mul_pos_of_neg_of_neg <;> linarith
  have hmid : (q i - z ⟨i, hi⟩) * (q (i + 1) - z ⟨i, hi⟩) < 0 := by
    have a1 := he_z ⟨i, hi⟩
    simp only at a1
    have a2 := hq2 i hi.le
    have a3 := hq1 (i + 1) hi
    rw [a1] at a2 a3
    exact mul_neg_of_neg_of_pos (by linarith) (by linarith)
  have hprod : ∏ l, ((q i - z l) * (q (i + 1) - z l)) < 0 := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ ⟨i, hi⟩)]
    refine mul_neg_of_neg_of_pos hmid (Finset.prod_pos fun l hl => hfac l ?_)
    exact (Finset.mem_erase.mp hl).1
  have hpre : 0 < q i * (q i - 1) * (q (i + 1) * (q (i + 1) - 1)) := by
    have b1 := hq0 i hi.le
    have b2 := hqlt i hi.le
    have b3 := hq0 (i + 1) hi
    have b4 := hqlt (i + 1) hi
    have c1 : q i * (q i - 1) < 0 := mul_neg_of_pos_of_neg b1 (by linarith)
    have c2 : q (i + 1) * (q (i + 1) - 1) < 0 := mul_neg_of_pos_of_neg b3 (by linarith)
    exact mul_pos_of_neg_of_neg c1 c2
  calc (q i * (q i - 1) * ∏ l, (q i - z l)) *
        (q (i + 1) * (q (i + 1) - 1) * ∏ l, (q (i + 1) - z l))
      = (q i * (q i - 1) * (q (i + 1) * (q (i + 1) - 1))) *
        ∏ l, ((q i - z l) * (q (i + 1) - z l)) := by rw [Finset.prod_mul_distrib]; ring
    _ < 0 := mul_neg_of_pos_of_neg hpre hprod

lemma alt_zero (F : ℝ[X]) : Alt F 0 :=
  ⟨fun _ => 1 / 2, by norm_num, by norm_num, fun i hi => absurd hi (Nat.not_lt_zero _),
    fun i hi => absurd hi (Nat.not_lt_zero _)⟩

lemma eigPoly_alt (n m : ℕ) (hm : 2 ≤ m) (hmn : m ≤ n) : Alt (eigPoly n m) (m - 2) := by
  obtain ⟨z, hz, hz01, hG⟩ := eigPoly_eq_prod_sorted n m hm hmn
  rw [hG]; exact alt_of_prod z hz hz01

/-- Every combination `G_{m+1} - c G_m` has at least `m - 2` strict sign changes in `(0,1)`
(forward iteration of the Bernstein operator, where `G_m` dominates, plus variation
diminishing). -/
lemma alt_comb (n m : ℕ) (hm : 2 ≤ m) (hmn : m + 1 ≤ n) (c : ℝ) :
    Alt (eigPoly n (m + 1) - c • eigPoly n m) (m - 2) := by
  have hn : 2 ≤ n := by lia
  by_cases hc : c = 0
  · rw [hc, zero_smul, sub_zero]
    exact (eigPoly_alt n (m + 1) (by lia) hmn).mono (by lia)
  rcases Nat.eq_zero_or_pos (m - 2) with hk | hk
  · rw [hk]; exact alt_zero _
  set k := m - 2 with hkdef
  set f := eigPoly n m with hf
  set g := eigPoly n (m + 1) with hg
  set H := g - c • f with hH
  have hH0 : H.eval 0 = 0 := by
    simp [hH, hf, hg, eigPoly_eval_zero n m hm (by lia), eigPoly_eval_zero n (m + 1) (by lia) hmn]
  have hH1 : H.eval 1 = 0 := by
    simp [hH, hf, hg, eigPoly_eval_one n m hm (by lia), eigPoly_eval_one n (m + 1) (by lia) hmn]
  obtain ⟨q, hq0, hq1, hqinc, hqalt⟩ := eigPoly_alt n m hm (by lia)
  have hfq : ∀ i ≤ k, f.eval (q i) ≠ 0 := by
    intro i hi
    rcases lt_or_eq_of_le hi with h | h
    · exact left_ne_zero_of_mul (hqalt i h).ne
    · have := hqalt (k - 1) (by lia)
      rw [show k - 1 + 1 = k by lia] at this
      rw [h]; exact right_ne_zero_of_mul this.ne
  have hμ : 0 < mu n m := mu_pos n m (by lia)
  have hμ1 : 0 ≤ mu n (m + 1) := (mu_pos n (m + 1) hmn).le
  have hratio0 : 0 ≤ mu n (m + 1) / mu n m := div_nonneg hμ1 hμ.le
  have hratio1 : mu n (m + 1) / mu n m < 1 := by
    rw [div_lt_one hμ]; exact mu_succ_lt n m (by lia) (by lia)
  have hBr : ∀ r : ℕ, ((bernOp n) ^ r) H =
      (mu n (m + 1)) ^ r • g - (c * (mu n m) ^ r) • f := by
    intro r
    rw [hH, map_sub, map_smul, hg, hf, bernOp_pow_eigPoly n m hm (by lia),
      bernOp_pow_eigPoly n (m + 1) (by lia) hmn, smul_smul]
  set D : ℕ → ℝ := fun r => -(c * (mu n m) ^ r) with hD
  have hD0 : ∀ r, D r ≠ 0 := fun r => neg_ne_zero.mpr (mul_ne_zero hc (pow_ne_zero _ hμ.ne'))
  have hS : ∀ (r : ℕ) (y : ℝ), (((bernOp n) ^ r) H).eval y / D r =
      f.eval y - (mu n (m + 1) / mu n m) ^ r * (g.eval y / c) := by
    intro r y
    rw [hBr]
    simp only [eval_sub, eval_smul, smul_eq_mul, hD, div_pow]
    field_simp
    ring
  have hT : ∀ y : ℝ, Filter.Tendsto (fun r : ℕ => (((bernOp n) ^ r) H).eval y / D r)
      Filter.atTop (nhds (f.eval y)) := by
    intro y
    simp_rw [hS]
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hratio0 hratio1).mul_const
      (g.eval y / c)).const_sub (f.eval y)
    simpa using this
  have hev : ∀ i ∈ Finset.range (k + 1), ∀ᶠ r in Filter.atTop,
      0 < (((bernOp n) ^ r) H).eval (q i) / D r * f.eval (q i) := by
    intro i hi
    rw [Finset.mem_range] at hi
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
      have := mul_pos e1 e2
      calc (0 : ℝ) < _ := this
        _ = _ := by ring
    exact neg_of_mul_pos_left this e3.le
  have : a * b = (a / D r * (b / D r)) * (D r) ^ 2 := by field_simp [hD0 r]
  rw [this]
  exact mul_neg_of_neg_of_pos hab (by have := hD0 r; positivity)

/-- A polynomial vanishing at `0`, `1` and doubly at an interior point `t`, with `k` strict sign
changes in `(0,1)`, has degree at least `k + 4`. -/
lemma double_root_degree (F : ℝ[X]) (hF : F ≠ 0) (h0 : F.eval 0 = 0) (h1 : F.eval 1 = 0)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hFt : F.eval t = 0)
    (hF't : (derivative F).eval t = 0) (k : ℕ) (halt : Alt F k) : k + 4 ≤ F.natDegree := by
  obtain ⟨F1, hF1⟩ : X ∣ F := X_dvd_iff.mpr (by rw [coeff_zero_eq_eval_zero, h0])
  have hF1r : F1.IsRoot 1 := by
    have := h1; rw [hF1, eval_mul, eval_X, one_mul] at this; exact this
  obtain ⟨F2, hF2⟩ := dvd_iff_isRoot.mpr hF1r
  have ht1' : t - 1 ≠ 0 := sub_ne_zero.mpr ht1.ne
  have hF2r : F2.IsRoot t := by
    have := hFt
    rw [hF1, hF2] at this
    simp only [eval_mul, eval_X, eval_sub, eval_C] at this
    exact (mul_eq_zero.mp ((mul_eq_zero.mp this).resolve_left ht0.ne')).resolve_left ht1'
  obtain ⟨F3, hF3⟩ := dvd_iff_isRoot.mpr hF2r
  have hFeq : F = (X - C t) * (X * (X - C 1) * F3) := by rw [hF1, hF2, hF3]; ring
  have hF3r : F3.IsRoot t := by
    have := hF't
    rw [hFeq, derivative_mul] at this
    simp only [derivative_sub, derivative_X, derivative_C, sub_zero, one_mul, eval_add,
      eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero] at this
    exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero ht0.ne' ht1')
  obtain ⟨F4, hF4⟩ := dvd_iff_isRoot.mpr hF3r
  have hFeq' : F = (X * (X - C 1) * (X - C t) ^ 2) * F4 := by rw [hFeq, hF4]; ring
  have hF4ne : F4 ≠ 0 := by
    rintro rfl; rw [mul_zero] at hFeq'; exact hF hFeq'
  have hmon : (X * (X - C 1) * (X - C t) ^ 2 : ℝ[X]).Monic :=
    (monic_X.mul (monic_X_sub_C 1)).mul ((monic_X_sub_C t).pow 2)
  have hdeg4 : (X * (X - C 1) * (X - C t) ^ 2 : ℝ[X]).natDegree = 4 := by
    rw [(monic_X.mul (monic_X_sub_C 1)).natDegree_mul ((monic_X_sub_C t).pow 2),
      monic_X.natDegree_mul (monic_X_sub_C 1), (monic_X_sub_C t).natDegree_pow, natDegree_X,
      natDegree_X_sub_C, natDegree_X_sub_C]
  have hdeg : F.natDegree = 4 + F4.natDegree := by
    rw [hFeq', hmon.natDegree_mul' hF4ne, hdeg4]
  obtain ⟨p, hp0, hp1, hinc, halt⟩ := halt
  have hpin : ∀ i ≤ k, 0 < p i ∧ p i < 1 := fun i hi =>
    ⟨lt_of_lt_of_le hp0 (chain_le hinc 0 i (Nat.zero_le _) hi),
      lt_of_le_of_lt (chain_le hinc i k hi le_rfl) hp1⟩
  have hw : ∀ i ≤ k, p i * (p i - 1) * (p i - t) ^ 2 ≤ 0 := by
    intro i hi
    obtain ⟨a1, a2⟩ := hpin i hi
    have : p i * (p i - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos a1.le (by linarith)
    exact mul_nonpos_of_nonpos_of_nonneg this (sq_nonneg _)
  have hk := le_natDegree_of_alt F4 hF4ne p k hinc (fun i hi => by
    have := halt i hi
    rw [hFeq'] at this
    simp only [eval_mul, eval_X, eval_sub, eval_C, eval_pow] at this
    have w1 := hw i hi.le
    have w2 := hw (i + 1) hi
    by_contra hge
    push Not at hge
    have : 0 ≤ (p i * (p i - 1) * (p i - t) ^ 2) * (p (i + 1) * (p (i + 1) - 1) *
        (p (i + 1) - t) ^ 2) * (F4.eval (p i) * F4.eval (p (i + 1))) :=
      mul_nonneg (mul_nonneg_of_nonpos_of_nonpos w1 w2) hge
    linarith)
  lia

/-- The Wronskian `G_m G_{m+1}' - G_m' G_{m+1}` has no zero in `(0,1)`: otherwise a suitable
combination `G_{m+1} - c G_m` would have a double zero there, which is incompatible with its
`m - 2` sign changes and its degree. -/
lemma wronskian_ne_zero (n m : ℕ) (hm : 2 ≤ m) (hmn : m + 1 ≤ n) (t : ℝ) (ht0 : 0 < t)
    (ht1 : t < 1) :
    (eigPoly n m * derivative (eigPoly n (m + 1)) -
      derivative (eigPoly n m) * eigPoly n (m + 1)).eval t ≠ 0 := by
  set f := eigPoly n m with hf
  set g := eigPoly n (m + 1) with hg
  obtain ⟨hfmon, hfdeg, -⟩ := eigPoly_spec n m hm (by lia)
  obtain ⟨hgmon, hgdeg, -⟩ := eigPoly_spec n (m + 1) (by lia) hmn
  have hf0 := eigPoly_eval_zero n m hm (by lia)
  have hf1 := eigPoly_eval_one n m hm (by lia)
  have hg0 := eigPoly_eval_zero n (m + 1) (by lia) hmn
  have hg1 := eigPoly_eval_one n (m + 1) (by lia) hmn
  have hsimple : f.eval t = 0 → (derivative f).eval t ≠ 0 := by
    intro h h'
    have := double_root_degree f hfmon.ne_zero hf0 hf1 t ht0 ht1 h h' (m - 2)
      (eigPoly_alt n m hm (by lia))
    lia
  have hH : ∀ c : ℝ, (g - c • f).eval t = 0 →
      (derivative (g - c • f)).eval t = 0 → False := by
    intro c h h'
    have hdeg : (g - c • f).natDegree ≤ m + 1 :=
      (natDegree_sub_le _ _).trans (max_le hgdeg.le ((natDegree_smul_le _ _).trans (by lia)))
    have hne : g - c • f ≠ 0 := by
      intro h0
      have := congrArg (fun P => P.coeff (m + 1)) h0
      simp only [coeff_sub, coeff_smul, smul_eq_mul, coeff_zero] at this
      rw [coeff_eq_zero_of_natDegree_lt (by lia : f.natDegree < m + 1), ← hgdeg,
        hgmon.coeff_natDegree] at this
      norm_num at this
    have := double_root_degree (g - c • f) hne (by simp [hf, hg, hg0, hf0])
      (by simp [hf, hg, hg1, hf1]) t ht0
      ht1 h h' (m - 2) (alt_comb n m hm hmn c)
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
      field_simp
      ring
  · apply hH (g.eval t / f.eval t)
    · simp only [eval_sub, eval_smul, smul_eq_mul]
      field_simp
      ring
    · simp only [derivative_sub, derivative_smul, eval_sub, eval_smul, smul_eq_mul]
      field_simp
      linear_combination hW

/-- Between two zeros of `G_{m+1}` in `(0,1)` there is a zero of `G_m` (Rolle). -/
lemma zero_between (n m : ℕ) (hm : 2 ≤ m) (hmn : m + 1 ≤ n) (a b : ℝ) (ha0 : 0 < a)
    (hab : a < b) (hb1 : b < 1) (hga : (eigPoly n (m + 1)).eval a = 0)
    (hgb : (eigPoly n (m + 1)).eval b = 0) :
    ∃ t, a < t ∧ t < b ∧ (eigPoly n m).eval t = 0 := by
  set f := eigPoly n m with hf
  set g := eigPoly n (m + 1) with hg
  have hW := wronskian_ne_zero n m hm hmn
  by_contra hno
  push Not at hno
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
  have := (div_eq_zero_iff.mp hc).resolve_right (pow_ne_zero 2 hfc)
  linear_combination this

lemma interlace_of_between {k : ℕ} (z : Fin k → ℝ) (u : Fin (k + 1) → ℝ)
    (hz : StrictMono z)
    (hu : StrictMono u) (hbet : ∀ i : Fin k, ∃ l, u i.castSucc < z l ∧ z l < u i.succ) :
    ∀ i, u i.castSucc < z i ∧ z i < u i.succ := by
  choose σ hσ using hbet
  have hσm : StrictMono σ := by
    intro i i' hii'
    have h1 := (hσ i).2
    have h2 := (hσ i').1
    have h3 : u i.succ ≤ u i'.castSucc := hu.monotone (Fin.succ_le_castSucc_iff.mpr hii')
    exact hz.lt_iff_lt.mp (by linarith)
  have hid : σ = id := by
    have hs : Function.Surjective σ := Finite.surjective_of_injective hσm.injective
    have := Subsingleton.elim (StrictMono.orderIsoOfSurjective σ hσm hs) (OrderIso.refl _)
    funext i
    exact congrArg (fun e : Fin k ≃o Fin k => e i) this
  intro i
  have := hσ i
  rw [hid] at this
  exact this

lemma moebius_lt {a b : ℝ} (hab : a < b) (hb : b < 1) : a / (1 - a) < b / (1 - b) := by
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith


end Kostov
end RealRooted
