module

import RealRooted.Derivative.LinearCombination
public import RealRooted.Mesh.Basic

/-!
# Mesh and derivatives

Riesz's mesh theorem, as stated in Brändén--Krasikov--Shapiro, *Elements of
Pólya--Schur theory in finite difference setting*, Proc. AMS 144 (2016),
Theorem 1: subtracting a constant multiple of the derivative does not decrease
the mesh of a real-rooted polynomial. The proof was found by Aristotle
(Harmonic).
-/

public section

noncomputable section

namespace Polynomial

private lemma one_div_lt_of_mul_pos {a b : ℝ} (hab : 0 < a * b) (h : b < a) :
    1 / a < 1 / b := by
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hab
  have hb : b ≠ 0 := by
    rintro rfl
    simp at hab
  have heq : 1 / b - 1 / a = (a - b) / (a * b) := by
    field_simp
  have hpos : 0 < (a - b) / (a * b) := div_pos (by linarith) hab
  linarith

private lemma key {n : ℕ} (x : Fin n → ℝ) (hx : StrictMono x) (δ : ℝ)
    (hgap : ∀ i j, i < j → x i + δ ≤ x j) (y y' : ℝ) (hyy : y < y')
    (hlt : y' < y + δ) (hy : ∀ i, x i ≠ y) (hy' : ∀ i, x i ≠ y')
    (hn : n ≠ 0) :
    ∑ i, 1 / (y - x i) ≠ ∑ i, 1 / (y' - x i) := by
  by_cases h : ∃ j, y < x j ∧ x j < y'
  · obtain ⟨j, hj1, hj2⟩ := h
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    apply ne_of_lt
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ]
    have hterm : ∀ i : Fin m,
        1 / (y - x i.castSucc) ≤ 1 / (y' - x i.succ) := by
      intro i
      have hcs := hgap _ _ (Fin.castSucc_lt_succ (i := i))
      apply le_of_lt
      apply one_div_lt_of_mul_pos
      · rcases lt_or_ge i.castSucc j with hij | hij
        · have h1 := hgap _ _ hij
          have h2 : i.succ ≤ j := Fin.castSucc_lt_iff_succ_le.mp hij
          have h3 := hx.monotone h2
          apply mul_pos <;> linarith
        · have h1 := hx.monotone hij
          have h2 : j < i.succ := lt_of_le_of_lt hij Fin.castSucc_lt_succ
          have h3 := hgap _ _ h2
          apply mul_pos_of_neg_of_neg <;> linarith
      · linarith
    have hsum := Finset.sum_le_sum
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => hterm i)
    have hl : 1 / (y - x (Fin.last m)) < 0 := by
      have hlast := hx.monotone (Fin.le_last j)
      apply div_neg_of_pos_of_neg one_pos
      linarith
    have hr : 0 < 1 / (y' - x 0) := by
      have hfirst := hx.monotone (Fin.zero_le j)
      apply div_pos one_pos
      linarith
    linarith
  · push Not at h
    apply ne_of_gt
    apply Finset.sum_lt_sum_of_nonempty
    · exact Finset.univ_nonempty_iff.mpr ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
    · intro i _
      apply one_div_lt_of_mul_pos
      · rcases lt_or_gt_of_ne (hy i) with h1 | h1
        · apply mul_pos <;> linarith
        · have h2 := h i h1
          have h3 := lt_of_le_of_ne h2 (Ne.symm (hy' i))
          apply mul_pos_of_neg_of_neg <;> linarith
      · linarith

private lemma sign_near_simple_root (p : ℝ[X]) (s t : ℝ) (hs : p.IsRoot s)
    (hd : eval s (derivative p) ≠ 0) (hts : t ≠ s)
    (hno : ∀ u ∈ Set.uIcc s t, u ≠ s → ¬p.IsRoot u) :
    0 < (t - s) * (eval t p * eval s (derivative p)) := by
  set r := p /ₘ (X - C s) with hr
  have hpr : (X - C s) * r = p := mul_divByMonic_eq_iff_isRoot.mpr hs
  have hrs : eval s r = eval s (derivative p) := by
    rw [← hpr, derivative_mul]
    simp
  have hpt : ∀ u, eval u p = (u - s) * eval u r := by
    intro u
    rw [← hpr]
    simp
  have hrne : ∀ u ∈ Set.uIcc s t, eval u r ≠ 0 := by
    intro u hu
    by_cases hus : u = s
    · subst hus
      rw [hrs]
      exact hd
    · intro h0
      apply hno u hu hus
      rw [IsRoot, hpt, h0, mul_zero]
  have hpos : 0 < eval t r * eval s r := by
    by_contra hcon
    push Not at hcon
    have hcont : ContinuousOn (fun u => eval u r) (Set.uIcc s t) :=
      r.continuous.continuousOn
    have h0 : (0 : ℝ) ∈ Set.uIcc (eval s r) (eval t r) := by
      rw [Set.mem_uIcc]
      rcases lt_or_gt_of_ne (hrne s Set.left_mem_uIcc) with h | h
      · left
        constructor
        · exact h.le
        · by_contra h'
          push Not at h'
          nlinarith
      · right
        constructor
        · by_contra h'
          push Not at h'
          nlinarith
        · exact h.le
    obtain ⟨u, hu, hu0⟩ := intermediate_value_uIcc hcont h0
    exact hrne u hu hu0
  rw [hpt, ← hrs]
  have hsq : 0 < (t - s) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hts)
  nlinarith

private lemma exists_root_between_of_eval_mul_neg (f : ℝ[X]) (a b : ℝ)
    (hab : a < b) (h : eval a f * eval b f < 0) :
    ∃ y, a < y ∧ y < b ∧ f.IsRoot y := by
  have hcont : ContinuousOn (fun u => eval u f) (Set.Icc a b) :=
    f.continuous.continuousOn
  have ha0 : eval a f ≠ 0 := by
    rintro h0
    rw [h0, zero_mul] at h
    exact lt_irrefl _ h
  rcases lt_or_gt_of_ne ha0 with ha | ha
  · have hb : 0 < eval b f := by nlinarith
    obtain ⟨y, ⟨hy1, hy2⟩, hy⟩ :=
      intermediate_value_Ioo hab.le hcont ⟨ha, hb⟩
    exact ⟨y, hy1, hy2, hy⟩
  · have hb : eval b f < 0 := by nlinarith
    obtain ⟨y, ⟨hy1, hy2⟩, hy⟩ :=
      intermediate_value_Ioo' hab.le hcont ⟨hb, ha⟩
    exact ⟨y, hy1, hy2, hy⟩

private lemma gap_root (p : ℝ[X]) (c : ℝ) (s t : ℝ) (hst : s < t)
    (hs : p.IsRoot s) (ht : p.IsRoot t)
    (hds : eval s (derivative p) ≠ 0) (hdt : eval t (derivative p) ≠ 0)
    (hc : c ≠ 0) (hno : ∀ u, s < u → u < t → ¬p.IsRoot u) :
    ∃ y, s < y ∧ y < t ∧ (p - C c * derivative p).IsRoot y := by
  set m := (s + t) / 2 with hm
  have hsm : s < m := by rw [hm]; linarith
  have hmt : m < t := by rw [hm]; linarith
  have h1 := sign_near_simple_root p s m hs hds hsm.ne' (by
    intro u hu hus
    rw [Set.uIcc_of_le hsm.le] at hu
    exact hno u (lt_of_le_of_ne hu.1 (Ne.symm hus)) (lt_of_le_of_lt hu.2 hmt))
  have h2 := sign_near_simple_root p t m ht hdt hmt.ne (by
    intro u hu hus
    rw [Set.uIcc_of_ge hmt.le] at hu
    exact hno u (lt_of_lt_of_le hsm hu.1) (lt_of_le_of_ne hu.2 hus))
  have e1 : 0 < eval m p * eval s (derivative p) :=
    (mul_pos_iff_of_pos_left (sub_pos.mpr hsm)).mp h1
  have e2 : eval m p * eval t (derivative p) < 0 := by
    rcases mul_pos_iff.mp h2 with h | h
    · linarith [h.1]
    · exact h.2
  have hprod : eval s (derivative p) * eval t (derivative p) < 0 := by
    by_contra h
    push Not at h
    nlinarith [mul_pos_of_neg_of_neg (neg_neg_of_pos e1) e2, sq_nonneg (eval m p)]
  apply exists_root_between_of_eval_mul_neg _ s t hst
  have hs0 : eval s p = 0 := hs
  have ht0 : eval t p = 0 := ht
  simp only [eval_sub, eval_mul, eval_C, hs0, ht0]
  have hcsq : 0 < c ^ 2 := by positivity
  nlinarith

private lemma end_root (p : ℝ[X]) (S : Finset ℝ)
    (hS : ∀ u, p.IsRoot u → u ∈ S)
    (hF : ∀ t, ¬p.IsRoot t →
      eval t (derivative p) = eval t p * ∑ s' ∈ S, 1 / (t - s'))
    (c : ℝ) (hc : c ≠ 0) (s : ℝ) (hs : p.IsRoot s)
    (hds : eval s (derivative p) ≠ 0)
    (hext : ∀ s' ∈ S, 0 ≤ (s - s') * c) :
    ∃ y, 0 < (y - s) * c ∧ (p - C c * derivative p).IsRoot y := by
  set N : ℕ := S.card with hN
  set T := s + c * (N + 1) with hTdef
  have hc2 : 0 < c ^ 2 := by positivity
  have hN1 : (0 : ℝ) < N + 1 := by positivity
  have hT : ∀ s' ∈ S, c ^ 2 * (N + 1) ≤ (T - s') * c := by
    intro s' hs'
    have hext' := hext s' hs'
    rw [hTdef]
    nlinarith
  have hTroot : ¬p.IsRoot T := by
    intro hT'
    have hbound := hT T (hS T hT')
    simp at hbound
    nlinarith
  have hbound : c * ∑ s' ∈ S, 1 / (T - s') ≤ N / (N + 1) := by
    rw [Finset.mul_sum]
    have hterm : ∀ s' ∈ S, c * (1 / (T - s')) ≤ 1 / (N + 1) := by
      intro s' hs'
      have h1 := hT s' hs'
      have hd : T - s' ≠ 0 := by
        intro h0
        rw [h0] at h1
        simp at h1
        nlinarith
      have hpos : 0 < (T - s') * c := by nlinarith
      have heq : c * (1 / (T - s')) = (c * c) / ((T - s') * c) := by
        field_simp
      rw [heq, div_le_div_iff₀ hpos hN1]
      nlinarith
    calc
      ∑ s' ∈ S, c * (1 / (T - s')) ≤ ∑ _s' ∈ S, 1 / ((N : ℝ) + 1) :=
        Finset.sum_le_sum hterm
      _ = N / (N + 1) := by
        rw [Finset.sum_const, nsmul_eq_mul, ← hN]
        ring
  have hlt1 : c * ∑ s' ∈ S, 1 / (T - s') < 1 := by
    refine lt_of_le_of_lt hbound ?_
    rw [div_lt_one hN1]
    linarith
  have hTs : T - s = c * (N + 1) := by
    rw [hTdef]
    ring
  have hsign := sign_near_simple_root p s T hs hds (by
      intro h0
      have hzero : c * (N + 1) = 0 := by rw [← hTs, h0, sub_self]
      rcases mul_eq_zero.mp hzero with h | h
      · exact hc h
      · linarith) (by
    intro u hu hus hu'
    have h1 := hext u (hS u hu')
    rcases lt_or_gt_of_ne hc with hc' | hc'
    · have hTs' : T ≤ s := by nlinarith
      rw [Set.uIcc_of_ge hTs'] at hu
      have hlt : u < s := lt_of_le_of_ne hu.2 hus
      nlinarith
    · have hTs' : s ≤ T := by nlinarith
      rw [Set.uIcc_of_le hTs'] at hu
      have hlt : s < u := lt_of_le_of_ne hu.1 (Ne.symm hus)
      nlinarith)
  rw [hTs] at hsign
  have hkey : 0 < c * (eval T p * eval s (derivative p)) := by
    by_contra h
    push Not at h
    nlinarith
  have hs0 : eval s p = 0 := hs
  have hqT : eval T (p - C c * derivative p) =
      eval T p * (1 - c * ∑ s' ∈ S, 1 / (T - s')) := by
    simp only [eval_sub, eval_mul, eval_C]
    rw [hF T hTroot]
    ring
  have hqs : eval s (p - C c * derivative p) =
      -c * eval s (derivative p) := by
    simp only [eval_sub, eval_mul, eval_C, hs0]
    ring
  have hprod :
      eval s (p - C c * derivative p) * eval T (p - C c * derivative p) < 0 := by
    rw [hqT, hqs]
    have hpos : 0 < 1 - c * ∑ s' ∈ S, 1 / (T - s') := by linarith
    nlinarith
  rcases lt_or_gt_of_ne hc with hc' | hc'
  · have hTs' : T < s := by nlinarith
    rw [mul_comm] at hprod
    obtain ⟨y, hy1, hy2, hy⟩ :=
      exists_root_between_of_eval_mul_neg _ T s hTs' hprod
    exact ⟨y, by nlinarith, hy⟩
  · have hTs' : s < T := by nlinarith
    obtain ⟨y, hy1, hy2, hy⟩ :=
      exists_root_between_of_eval_mul_neg _ s T hTs' hprod
    exact ⟨y, by nlinarith, hy⟩

private lemma sum_orderEmbOfFin (S : Finset ℝ) {k : ℕ} (h : S.card = k)
    (f : ℝ → ℝ) :
    ∑ i, f (S.orderEmbOfFin h i) = ∑ s ∈ S, f s := by
  rw [← Finset.sum_coe_sort S]
  exact Fintype.sum_equiv (S.orderIsoOfFin h).toEquiv _ _
    (fun i => by simp [Finset.coe_orderIsoOfFin_apply])

/-- Subtracting a nonzero multiple of the derivative produces at least as many
distinct roots as the original polynomial. -/
private lemma card_roots_toFinset_sub_C_mul_derivative_ge (p q : ℝ[X])
    (S : Finset ℝ) (hmemS : ∀ u, u ∈ S ↔ p.IsRoot u)
    (hsimple : ∀ s, p.IsRoot s → eval s (derivative p) ≠ 0)
    (hF : ∀ t, ¬p.IsRoot t →
      eval t (derivative p) = eval t p * ∑ s ∈ S, 1 / (t - s))
    (c : ℝ)
    (hq : q = p - C c * derivative p)
    (hqeval : ∀ u, eval u q = eval u p - c * eval u (derivative p))
    (hc : c ≠ 0) :
    S.card ≤ q.roots.toFinset.card := by
  rcases Nat.eq_zero_or_eq_succ_pred S.card with h0 | hm
  · rw [h0]
    exact Nat.zero_le _
  set m := S.card.pred
  set x := S.orderEmbOfFin hm with hxdef
  have hxroot : ∀ i, p.IsRoot (x i) :=
    fun i => (hmemS _).mp (S.orderEmbOfFin_mem hm i)
  have hxsurj : ∀ u, p.IsRoot u → ∃ i, x i = u := by
    intro u hu
    have hrange : u ∈ Set.range x := by
      rw [hxdef, Finset.range_orderEmbOfFin]
      exact (hmemS u).mpr hu
    exact hrange
  have hx : StrictMono x := (S.orderEmbOfFin hm).strictMono
  have hgaproot : ∀ i : Fin m,
      ∃ y, x i.castSucc < y ∧ y < x i.succ ∧ q.IsRoot y := by
    intro i
    rw [hq]
    apply gap_root p c _ _ (hx Fin.castSucc_lt_succ) (hxroot _) (hxroot _)
      (hsimple _ (hxroot _)) (hsimple _ (hxroot _)) hc
    intro u hu1 hu2 hu
    obtain ⟨k, rfl⟩ := hxsurj u hu
    have h1 := hx.lt_iff_lt.mp hu1
    have h2 := hx.lt_iff_lt.mp hu2
    rw [Fin.castSucc_lt_iff_succ_le] at h1
    exact absurd h2 (not_lt.mpr h1)
  choose g hg1 hg2 hg3 using hgaproot
  have hg : StrictMono g := by
    intro i j hij
    have hmono := hx.monotone (Fin.succ_le_castSucc_iff.mpr hij)
    linarith [hg2 i, hg1 j]
  obtain ⟨s0, hs0, hext⟩ :
      ∃ s0, p.IsRoot s0 ∧ ∀ s' ∈ S, 0 ≤ (s0 - s') * c := by
    rcases lt_or_gt_of_ne hc with hc' | hc'
    · refine ⟨x 0, hxroot 0, fun s' hs' => ?_⟩
      obtain ⟨k, rfl⟩ := hxsurj s' ((hmemS s').mp hs')
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hx.monotone (Fin.zero_le k))) hc'.le
    · refine ⟨x (Fin.last m), hxroot _, fun s' hs' => ?_⟩
      obtain ⟨k, rfl⟩ := hxsurj s' ((hmemS s').mp hs')
      exact mul_nonneg (sub_nonneg.mpr (hx.monotone (Fin.le_last k))) hc'.le
  obtain ⟨e, he, heq⟩ := end_root p S (fun u hu => (hmemS u).mpr hu)
    hF c hc s0 hs0 (hsimple s0 hs0) hext
  have hene : e ∉ Finset.univ.image g := by
    intro hmem
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hmem
    have h1 := hext _ ((hmemS _).mpr (hxroot i.castSucc))
    have h2 := hext _ ((hmemS _).mpr (hxroot i.succ))
    have a1 := hg1 i
    have a2 := hg2 i
    have b1 : 0 < (g i - x i.castSucc) * c := by nlinarith
    have b2 : 0 < (g i - x i.succ) * c := by nlinarith
    rcases lt_or_gt_of_ne hc <;> nlinarith
  have hq0 : q ≠ 0 := by
    intro h
    have heval := hqeval (x 0)
    rw [h, (hxroot 0).eq_zero] at heval
    have hmul : c * eval (x 0) (derivative p) = 0 := by
      simpa only [eval_zero, zero_sub, neg_eq_zero] using heval.symm
    exact hsimple _ (hxroot 0) ((mul_eq_zero.mp hmul).resolve_left hc)
  have hsub : insert e (Finset.univ.image g) ⊆ q.roots.toFinset := by
    intro y hy
    rw [Multiset.mem_toFinset, mem_roots hq0]
    rcases Finset.mem_insert.mp hy with rfl | hy
    · rw [hq]
      exact heq
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      exact hg3 i
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hene,
    Finset.card_image_of_injective _ hg.injective, Finset.card_univ,
    Fintype.card_fin] at hcard
  lia

/-- Equal reciprocal-root sums at two roots force those roots to be separated
by the original root gap. -/
private lemma roots_pairwise_gap_of_reciprocal_sum (p q : ℝ[X]) (hp0 : p ≠ 0)
    (S : Finset ℝ) (hmemS : ∀ u, u ∈ S ↔ p.IsRoot u) (δ : ℝ)
    (hgap : ∀ r ∈ p.roots, ∀ s ∈ p.roots, r ≠ s → δ ≤ |r - s|)
    (c : ℝ) (hc : c ≠ 0)
    (hqF : ∀ y, q.IsRoot y → c * ∑ s ∈ S, 1 / (y - s) = 1)
    (hq0 : ∀ y, q.IsRoot y → ¬p.IsRoot y) :
    ∀ r ∈ q.roots, ∀ s ∈ q.roots, r ≠ s → δ ≤ |r - s| := by
  have hmesh : ∀ y y', y < y' → q.IsRoot y → q.IsRoot y' → δ ≤ y' - y := by
    intro y y' hyy hy hy'
    by_contra hlt
    push Not at hlt
    have hFy := hqF y hy
    have hFy' := hqF y' hy'
    have hSne : S.card ≠ 0 := by
      intro h0
      simp [Finset.card_eq_zero.mp h0] at hFy
    have heq : ∑ s ∈ S, 1 / (y - s) = ∑ s ∈ S, 1 / (y' - s) := by
      have hzero :
          c * (∑ s ∈ S, 1 / (y - s) - ∑ s ∈ S, 1 / (y' - s)) = 0 := by
        rw [mul_sub]
        linarith
      have := (mul_eq_zero.mp hzero).resolve_left hc
      linarith
    set x := S.orderEmbOfFin rfl with hxdef
    have hxroot : ∀ i, p.IsRoot (x i) :=
      fun i => (hmemS _).mp (S.orderEmbOfFin_mem rfl i)
    have hx : StrictMono x := (S.orderEmbOfFin rfl).strictMono
    rw [← sum_orderEmbOfFin S rfl (fun s => 1 / (y - s)),
      ← sum_orderEmbOfFin S rfl (fun s => 1 / (y' - s))] at heq
    refine key x hx δ ?_ y y' hyy (by linarith) ?_ ?_ hSne heq
    · intro i j hij
      have hlt' := hx hij
      have hr := hgap (x i) ((mem_roots hp0).mpr (hxroot i)) (x j)
        ((mem_roots hp0).mpr (hxroot j)) hlt'.ne
      rw [abs_sub_comm, abs_of_pos (by linarith)] at hr
      linarith
    · intro i h
      exact hq0 y hy (h ▸ hxroot i)
    · intro i h
      exact hq0 y' hy' (h ▸ hxroot i)
  intro r hr s hs hrs
  have hqne : q ≠ 0 := ne_zero_of_mem_roots hr
  have hr' := (mem_roots hqne).mp hr
  have hs' := (mem_roots hqne).mp hs
  rcases lt_or_gt_of_ne hrs with h | h
  · rw [abs_sub_comm, abs_of_pos (by linarith)]
    exact hmesh r s h hr' hs'
  · rw [abs_of_pos (by linarith)]
    exact hmesh s r h hs' hr'

private theorem sub_C_mul_derivative_of_pos (p : ℝ[X]) (hp : p.Splits)
    (hnd : p.roots.Nodup) (δ : ℝ)
    (hgap : ∀ r ∈ p.roots, ∀ s ∈ p.roots, r ≠ s → δ ≤ |r - s|)
    (c : ℝ) :
    (p - C c * derivative p).Splits ∧
      (p - C c * derivative p).roots.Nodup ∧
        ∀ r ∈ (p - C c * derivative p).roots,
          ∀ s ∈ (p - C c * derivative p).roots, r ≠ s → δ ≤ |r - s| := by
  by_cases hp0 : p = 0
  · subst hp0
    simp
  by_cases hc : c = 0
  · subst hc
    simp only [map_zero, zero_mul, sub_zero]
    exact ⟨hp, hnd, hgap⟩
  set q := p - C c * derivative p with hq
  set S := p.roots.toFinset with hSdef
  have hmemS : ∀ u, u ∈ S ↔ p.IsRoot u := by
    intro u
    simp [S, mem_roots hp0]
  have hsimple : ∀ s, p.IsRoot s → eval s (derivative p) ≠ 0 := by
    intro s hs
    have hsep := (nodup_roots_iff_of_splits hp0 hp).mp hnd
    simpa using hsep.aeval_derivative_ne_zero (x := s) (by simpa using hs)
  have hF : ∀ t, ¬p.IsRoot t →
      eval t (derivative p) = eval t p * ∑ s ∈ S, 1 / (t - s) := by
    intro t ht
    rw [hp.eval_derivative_eq_eval_mul_sum ht]
    congr 1
    rw [Finset.sum_eq_multiset_sum, hSdef, Multiset.toFinset_val,
      Multiset.dedup_eq_self.mpr hnd]
  have hqeval : ∀ u, eval u q = eval u p - c * eval u (derivative p) := by
    intro u
    simp [q]
  have hq0 : ∀ y, q.IsRoot y → ¬p.IsRoot y := by
    intro y hy hpy
    apply hsimple y hpy
    have h1 := hy.eq_zero
    rw [hqeval, hpy.eq_zero] at h1
    have h3 : c * eval y (derivative p) = 0 := by linarith
    exact (mul_eq_zero.mp h3).resolve_left hc
  have hqF : ∀ y, q.IsRoot y → c * ∑ s ∈ S, 1 / (y - s) = 1 := by
    intro y hy
    have hpy := hq0 y hy
    have h1 : eval y q = 0 := hy
    rw [hqeval, hF y hpy] at h1
    have h2 : eval y p * (1 - c * ∑ s ∈ S, 1 / (y - s)) = 0 := by
      linarith
    have := (mul_eq_zero.mp h2).resolve_left hpy
    linarith
  have hdeg : q.natDegree ≤ S.card := by
    rw [hSdef, Multiset.toFinset_card_of_nodup hnd, splits_iff_card_roots.mp hp]
    refine (natDegree_sub_le _ _).trans (max_le le_rfl ?_)
    exact ((natDegree_C_mul_le _ _).trans (natDegree_derivative_le p)).trans
      (Nat.sub_le _ _)
  have hcount : S.card ≤ q.roots.toFinset.card := by
    exact card_roots_toFinset_sub_C_mul_derivative_ge
      p q S hmemS hsimple hF c hq hqeval hc
  have h1 := Multiset.toFinset_card_le q.roots
  have h2 := card_roots' q
  have hsplit : q.Splits := splits_iff_card_roots.mpr (by lia)
  have hnodup : q.roots.Nodup :=
    Multiset.toFinset_card_eq_card_iff_nodup.mp (by lia)
  exact ⟨hsplit, hnodup,
    roots_pairwise_gap_of_reciprocal_sum
      p q hp0 S hmemS δ hgap c hc hqF hq0⟩

namespace MeshGE

/-- Riesz's mesh theorem: subtracting a constant multiple of the derivative
does not decrease the mesh of a real-rooted polynomial. -/
theorem sub_C_mul_derivative {p : ℝ[X]} {α : ℝ} (h : p.MeshGE α) (c : ℝ) :
    (p - C c * derivative p).MeshGE α := by
  rcases h.2.1.eq_or_lt with hα | hα
  · subst α
    apply zero
    simpa [sub_eq_add_neg] using
      RealRooted.splits_add_C_mul_derivative_all h.1 (-c)
  · exact (iff_roots_nodup_pairwise_gap hα).2
      (sub_C_mul_derivative_of_pos p h.1 (h.roots_nodup hα) α
        ((iff_roots_nodup_pairwise_gap hα).1 h).2.2 c)

end MeshGE

end Polynomial
