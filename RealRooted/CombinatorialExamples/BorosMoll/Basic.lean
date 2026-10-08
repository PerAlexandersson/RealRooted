import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Polynomial

/-!
# Boros–Moll log-concavity transform: definitions and small cases

Let `d_i(n)` be the Boros–Moll coefficients (`bmCoeff`),
`L(d(n))_i = d_i(n)^2 - d_{i-1}(n) d_{i+1}(n)` their log-concavity transform (`bmL`),
`M_n(x) = ∑ L(d(n))_i x^i` (`bmM`), and `N_n` the Narayana polynomial (`narayanaN`).
Xie and Zhang (arXiv:2609.20653, Theorem 1.1) prove that `M_n` has `n` simple negative zeros
which strictly interlace the zeros of `N_n`
(`RealRooted.BorosMoll.bmM_roots`, `RealRooted.BorosMoll.bmM_strictInterlaces_narayanaN`).

This file contains the definitions, the generic facts on signs and sorted roots, the reduction
of interlacing to sign alternation at explicit points (`BMInterlace`), and the exact computation
for `1 ≤ n ≤ 35`, certified by kernel-checked tables of dyadic sample points.  The estimates
for `n ≥ 36` are in `RealRooted.CombinatorialExamples.BorosMoll.Estimates`, and the final
theorems in `RealRooted.CombinatorialExamples.BorosMoll`.
-/

namespace RealRooted.BorosMoll

section Basic

open Polynomial Filter

/-- Boros–Moll coefficients `d_i(n) = 2^{-2n} ∑_{k=i}^n 2^k C(2n-2k, n-k) C(n+k, n) C(k, i)`
(`d_i(n) = 0` for `i > n`). -/
noncomputable def bmCoeff (n i : ℕ) : ℝ :=
  (1 / 4 : ℝ) ^ n *
    ∑ k ∈ Finset.Icc i n, (2 : ℝ) ^ k * ((2 * n - 2 * k).choose (n - k) : ℝ) *
      ((n + k).choose n : ℝ) * (k.choose i : ℝ)

/-- The log-concavity transform `L(d(n))_i = d_i(n)^2 - d_{i-1}(n) d_{i+1}(n)` with `d_{-1} = 0`. -/
noncomputable def bmL (n i : ℕ) : ℝ :=
  bmCoeff n i ^ 2 - (if i = 0 then 0 else bmCoeff n (i - 1)) * bmCoeff n (i + 1)

/-- `M_n(x) = ∑_{i=0}^n L(d(n))_i x^i`. -/
noncomputable def bmM (n : ℕ) : ℝ[X] :=
  ∑ i ∈ Finset.range (n + 1), C (bmL n i) * X ^ i

/-- The Narayana polynomial `N_n(x) = ∑_{i=0}^n (1/(i+1)) C(n,i) C(n+1,i) x^i`. -/
noncomputable def narayanaN (n : ℕ) : ℝ[X] :=
  ∑ i ∈ Finset.range (n + 1),
    C ((1 / ((i : ℝ) + 1)) * (n.choose i : ℝ) * ((n + 1).choose i : ℝ)) * X ^ i

/-- The real roots of `p`, listed in increasing order (with multiplicity). -/
noncomputable def sortedRoots (p : ℝ[X]) : List ℝ :=
  p.roots.sort (· ≤ ·)

/-- Strict interlacing of two polynomials of the same degree `n`, both with `n` real roots:
if `a_0 ≤ … ≤ a_{n-1}` are the roots of `p` and `b_0 ≤ … ≤ b_{n-1}` those of `q`, then
`a_0 < b_0 < a_1 < b_1 < ⋯ < a_{n-1} < b_{n-1}`. -/
def StrictInterlacesSameDegree (p q : ℝ[X]) (n : ℕ) : Prop :=
  (sortedRoots p).length = n ∧ (sortedRoots q).length = n ∧
    (∀ i < n, (sortedRoots p).getD i 0 < (sortedRoots q).getD i 0) ∧
    (∀ i, i + 1 < n → (sortedRoots q).getD i 0 < (sortedRoots p).getD (i + 1) 0)

/-! ## Generic facts about real polynomials, sign alternation and sorted roots -/

private lemma sign_mul_neg {a : ℕ} {u v : ℝ} (hu : 0 < (-1 : ℝ) ^ a * u)
    (hv : 0 < (-1 : ℝ) ^ (a + 1) * v) :
    u * v < 0 := by
  rcases neg_one_pow_eq_or ℝ a with h | h <;> simp [h, pow_succ] at hu hv <;> nlinarith

private lemma exists_root_between {p : ℝ[X]} {a b : ℝ} (hab : a < b) (h : p.eval a * p.eval b < 0) :
    ∃ s ∈ Set.Ioo a b, p.eval s = 0 := by
  have hc : ContinuousOn (fun x => p.eval x) (Set.Icc a b) := p.continuous.continuousOn
  rcases lt_or_gt_of_ne (show p.eval a ≠ 0 by intro h0; simp [h0] at h) with ha | ha
  · have hb : 0 < p.eval b := by nlinarith
    obtain ⟨s, hs, hs0⟩ := intermediate_value_Ioo hab.le hc ⟨ha, hb⟩
    exact ⟨s, hs, hs0⟩
  · have hb : p.eval b < 0 := by nlinarith
    obtain ⟨s, hs, hs0⟩ := intermediate_value_Ioo' hab.le hc ⟨hb, ha⟩
    exact ⟨s, hs, hs0⟩

private lemma lt_of_succ_lt {s : ℕ → ℝ} {n : ℕ} (h : ∀ j, j + 1 < n → s j < s (j + 1)) :
    ∀ i j, i < j → j < n → s i < s j := by
  intro i j hij hjn
  induction j with
  | zero => lia
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hij with h1 | h1
    · exact (ih h1 (by lia)).trans (h k hjn)
    · subst h1; exact h i hjn

/-- If a polynomial of degree `n` alternates in sign along `t 0 < t 1 < ⋯ < t n`, then its
roots are exactly `n` reals `s 0 < ⋯ < s (n-1)` with `t j < s j < t (j+1)`. -/
private lemma roots_of_alternation (p : ℝ[X]) (n : ℕ) (hn : 1 ≤ n) (hdeg : p.natDegree = n)
    (t : ℕ → ℝ) (ht : ∀ j < n, t j < t (j + 1))
    (hsign : ∀ j < n, p.eval (t j) * p.eval (t (j + 1)) < 0) :
    ∃ s : ℕ → ℝ, (∀ j < n, t j < s j ∧ s j < t (j + 1)) ∧ p ≠ 0 ∧
      p.roots = ((List.range n).map s : Multiset ℝ) := by
  have : ∀ j, ∃ x, j < n → (t j < x ∧ x < t (j+1) ∧ p.eval x = 0) := by
    intro j
    by_cases hj : j < n
    · obtain ⟨x, hx, hx0⟩ := exists_root_between (ht j hj) (hsign j hj)
      exact ⟨x, fun _ => ⟨hx.1, hx.2, hx0⟩⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose s hs using this
  have hp0 : p ≠ 0 := by
    intro h; have := hsign 0 hn; simp [h] at this
  have hmono : ∀ i j, i < j → j < n → s i < s j :=
    lt_of_succ_lt (fun j hj => ((hs j (by lia)).2.1).trans (hs (j+1) hj).1)
  have hnd : ((List.range n).map s).Nodup := by
    apply List.Nodup.map_on _ (List.nodup_range)
    intro i hi j hj hij
    simp only [List.mem_range] at hi hj
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact (hmono i j h hj).ne hij
    · exact (hmono j i h hi).ne hij.symm
  have hle : ((List.range n).map s : Multiset ℝ) ≤ p.roots := by
    rw [Multiset.le_iff_subset (by simpa using hnd)]
    intro x hx
    simp only [Multiset.mem_coe, List.mem_map, List.mem_range] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    exact (mem_roots hp0).2 (hs j hj).2.2
  refine ⟨s, fun j hj => ⟨(hs j hj).1, (hs j hj).2.1⟩, hp0,
    (Multiset.eq_of_le_of_card_le hle ?_).symm⟩
  simpa [hdeg] using card_roots' p

private lemma mono_of_interleave {s t : ℕ → ℝ} {n : ℕ} (h : ∀ j < n, t j < s j ∧ s j < t (j + 1)) :
    ∀ i j, i < j → j < n → s i < s j :=
  lt_of_succ_lt (fun j hj => ((h j (by lia)).2).trans (h (j+1) hj).1)

/-- A strictly increasing sequence `s 0 < ⋯ < s (n-1)` gives a duplicate-free multiset. -/
lemma nodup_map_range {s : ℕ → ℝ} {n : ℕ} (hmono : ∀ i j, i < j → j < n → s i < s j) :
    (((List.range n).map s : List ℝ) : Multiset ℝ).Nodup := by
  rw [Multiset.coe_nodup]
  apply List.Nodup.map_on _ (List.nodup_range)
  intro i hi j hj hij
  simp only [List.mem_range] at hi hj
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact (hmono i j h hj).ne hij
  · exact (hmono j i h hi).ne hij.symm

private lemma sortedRoots_eq {p : ℝ[X]} {n : ℕ} {s : ℕ → ℝ}
    (hmono : ∀ i j, i < j → j < n → s i < s j)
    (h : p.roots = ((List.range n).map s : Multiset ℝ)) :
    sortedRoots p = (List.range n).map s := by
  unfold sortedRoots
  rw [h, Multiset.coe_sort, List.mergeSort_eq_self]
  rw [List.pairwise_map]
  refine List.pairwise_lt_range.imp_of_mem ?_
  intro a b _ hb hab
  simp only [List.mem_range] at hb
  exact (hmono a b hab hb).le

private lemma getD_map_range {s : ℕ → ℝ} {n j : ℕ} (hj : j < n) :
    ((List.range n).map s).getD j 0 = s j := by
  simp [List.getD_eq_getElem?_getD, hj]

private lemma prod_sign (x : ℝ) (S : Multiset ℝ) (hS : x ∉ S) :
    0 < (-1 : ℝ) ^ ((S.filter (x < ·)).card) * (S.map (fun s => x - s)).prod := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    have hxa : x ≠ a := fun h => hS (h ▸ Multiset.mem_cons_self _ _)
    have ih' := ih (fun h => hS (Multiset.mem_cons_of_mem h))
    rcases lt_or_gt_of_ne hxa with h | h
    · rw [Multiset.filter_cons_of_pos _ h]
      simp only [Multiset.card_cons, pow_succ, Multiset.map_cons, Multiset.prod_cons]
      nlinarith
    · rw [Multiset.filter_cons_of_neg _ (not_lt.2 h.le)]
      simp only [Multiset.map_cons, Multiset.prod_cons]
      nlinarith

/-- The sign of a real-rooted polynomial with positive leading coefficient at a non-root `x`
is `(-1)^(number of roots greater than x)`. -/
private lemma sign_eval_of_card_roots {p : ℝ[X]} (hp : p ≠ 0) (hc : p.roots.card = p.natDegree)
    (hlc : 0 < p.leadingCoeff) {x : ℝ} (hx : ¬ p.IsRoot x) :
    0 < (-1 : ℝ) ^ ((p.roots.filter (x < ·)).card) * p.eval x := by
  have hfac := C_leadingCoeff_mul_prod_multiset_X_sub_C hc
  have hxS : x ∉ p.roots := fun h => hx ((mem_roots hp).1 h)
  have key : p.eval x = p.leadingCoeff * (p.roots.map (fun s => x - s)).prod := by
    conv_lhs => rw [← hfac]
    simp [eval_multiset_prod, Multiset.map_map]
  rw [key]
  have := prod_sign x p.roots hxS
  nlinarith

/-- The sign of the derivative at a simple root `r` of a real-rooted polynomial with positive
leading coefficient is `(-1)^(number of roots greater than r)`. -/
private lemma sign_deriv_at_root {p : ℝ[X]} (hp : p ≠ 0) (hc : p.roots.card = p.natDegree)
    (hlc : 0 < p.leadingCoeff) (hnd : p.roots.Nodup) {r : ℝ} (hr : p.IsRoot r) :
    0 < (-1 : ℝ) ^ ((p.roots.filter (r < ·)).card) * (derivative p).eval r := by
  set q := p /ₘ (X - C r)
  have hpq : (X - C r) * q = p := mul_divByMonic_eq_iff_isRoot.2 hr
  have hq0 : q ≠ 0 := by rintro h; rw [h, mul_zero] at hpq; exact hp hpq.symm
  have hroots : p.roots = r ::ₘ q.roots := by
    rw [← hpq, roots_mul (by rw [hpq]; exact hp), roots_X_sub_C]; rfl
  have hqdeg : q.natDegree + 1 = p.natDegree := by
    rw [← hpq, natDegree_mul (X_sub_C_ne_zero r) hq0, natDegree_X_sub_C]; ring
  have hqc : q.roots.card = q.natDegree := by
    have := congrArg Multiset.card hroots; simp at this; lia
  have hqlc : q.leadingCoeff = p.leadingCoeff := by
    rw [← hpq, leadingCoeff_mul, leadingCoeff_X_sub_C, one_mul]
  have hqr : ¬ q.IsRoot r := by
    intro h; rw [hroots] at hnd; exact (Multiset.nodup_cons.1 hnd).1 ((mem_roots hq0).2 h)
  have hder : (derivative p).eval r = q.eval r := by rw [← hpq]; simp [derivative_mul]
  have hfilt : p.roots.filter (r < ·) = q.roots.filter (r < ·) := by
    rw [hroots, Multiset.filter_cons_of_neg _ (lt_irrefl r)]
  rw [hder, hfilt]
  exact sign_eval_of_card_roots hq0 hqc (hqlc ▸ hlc) hqr

/-- Far to the left, a polynomial with positive leading coefficient has sign `(-1)^deg`. -/
private lemma exists_far_left (p : ℝ[X]) (hdeg : 1 ≤ p.natDegree) (hlc : 0 < p.leadingCoeff) (B : ℝ)
    :
    ∃ T < B, 0 < (-1 : ℝ) ^ p.natDegree * p.eval T := by
  set q := C ((-1:ℝ)^p.natDegree) * p.comp (-X)
  have hnd : (-X : ℝ[X]).natDegree = 1 := by simp
  have hqd : q.natDegree = p.natDegree := by
    rw [natDegree_C_mul (by simp), natDegree_comp, hnd, mul_one]
  have hql : q.leadingCoeff = p.leadingCoeff := by
    rw [leadingCoeff_C_mul_of_isUnit (by simp), leadingCoeff_comp (by rw [hnd]; norm_num)]
    simp only [leadingCoeff_neg, leadingCoeff_X]
    rw [mul_left_comm, ← mul_pow]; simp
  have hq : Tendsto (fun x => q.eval x) atTop atTop := by
    apply tendsto_atTop_of_leadingCoeff_nonneg
    · rw [degree_eq_natDegree (by intro h; rw [h] at hql; simp at hql; linarith), hqd]
      exact_mod_cast hdeg
    · rw [hql]; exact hlc.le
  obtain ⟨x, hx1, hx2⟩ :=
    ((hq.eventually (eventually_gt_atTop 0)).and (eventually_gt_atTop (-B))).exists
  refine ⟨-x, by linarith, ?_⟩
  simpa [q] using hx1

private lemma card_filter_range {ρ : ℕ → ℝ} {n j : ℕ} (hmono : ∀ i j, i < j → j < n → ρ i < ρ j)
    (hj : j < n) :
    ((((List.range n).map ρ : Multiset ℝ)).filter (ρ j < ·)).card = n - 1 - j := by
  rw [← Multiset.map_coe, Multiset.coe_range, Multiset.filter_map, Multiset.card_map]
  have : Multiset.filter ((fun x => ρ j < x) ∘ ρ) (Multiset.range n) = (Finset.Ioo j n).val := by
    rw [← Finset.range_val, ← Finset.filter_val]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Function.comp, Finset.mem_Ioo]
    constructor
    · rintro ⟨hi, h⟩
      refine ⟨?_, hi⟩
      by_contra hc
      rcases Nat.lt_or_eq_of_le (not_lt.1 hc) with hc | hc
      · exact absurd (hmono i j hc hj) (not_lt.2 h.le)
      · subst hc; exact lt_irrefl _ h
    · rintro ⟨h1, h2⟩; exact ⟨h2, hmono j i h1 h2⟩
  rw [this, Finset.card_val, Nat.card_Ioo]; lia

/-- Sign of the derivative at the `j`-th smallest root of a polynomial with `n` simple real roots.
-/
lemma sign_deriv_at_sorted_root {p : ℝ[X]} {n : ℕ} {ρ : ℕ → ℝ}
    (hmono : ∀ i j, i < j → j < n → ρ i < ρ j) (hdeg : p.natDegree = n)
    (hroots : p.roots = ((List.range n).map ρ : Multiset ℝ)) (hp : p ≠ 0)
    (hlc : 0 < p.leadingCoeff) {j : ℕ} (hj : j < n) :
    0 < (-1 : ℝ) ^ (n - 1 - j) * (derivative p).eval (ρ j) := by
  have hc : p.roots.card = p.natDegree := by rw [hroots, hdeg]; simp
  have hnd : p.roots.Nodup := by rw [hroots]; exact nodup_map_range hmono
  have hr : p.IsRoot (ρ j) := by
    rw [← mem_roots hp, hroots]; simp only [Multiset.mem_coe, List.mem_map, List.mem_range]; exact
        ⟨j, hj, rfl⟩
  have := sign_deriv_at_root hp hc hlc hnd hr
  rwa [hroots, card_filter_range hmono hj] at this

/-! ## The Narayana polynomials -/

/-- Coefficients of the Narayana polynomial. -/
noncomputable def narC (n i : ℕ) : ℝ :=
  (1 / ((i : ℝ) + 1)) * (n.choose i : ℝ) * ((n + 1).choose i : ℝ)

/-- The coefficient of `x ^ i` in the Narayana polynomial `N_n` is `narC n i`. -/
lemma coeff_narayanaN (n i : ℕ) : (narayanaN n).coeff i = narC n i := by
  unfold narayanaN
  simp only [finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · simp at h
    simp [narC, Nat.choose_eq_zero_of_lt (show n < i by lia)]

/-- The leading Narayana coefficient `narC n n` equals `1`. -/
lemma narC_self (n : ℕ) : narC n n = 1 := by
  unfold narC
  rw [Nat.choose_self, Nat.choose_succ_self_right]
  push_cast
  field_simp

/-- The Narayana polynomial `N_n` has degree `n`. -/
lemma narayanaN_natDegree (n : ℕ) : (narayanaN n).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro i hi
    rw [coeff_narayanaN]
    simp [narC, Nat.choose_eq_zero_of_lt (show n < i by exact_mod_cast hi)]
  · rw [coeff_narayanaN, narC_self]; norm_num

/-- The Narayana polynomial `N_n` is monic. -/
lemma narayanaN_leadingCoeff (n : ℕ) : (narayanaN n).leadingCoeff = 1 := by
  rw [leadingCoeff, narayanaN_natDegree, coeff_narayanaN, narC_self]

/-- The Narayana polynomial `N_n` is nonzero. -/
lemma narayanaN_ne_zero (n : ℕ) : narayanaN n ≠ 0 := by
  intro h; have := narayanaN_leadingCoeff n; rw [h] at this; simp at this

private lemma narayanaN_eval_zero (n : ℕ) : (narayanaN n).eval 0 = 1 := by
  rw [← coeff_zero_eq_eval_zero, coeff_narayanaN]; simp [narC]

private lemma narC_rec (n k : ℕ) : ((n : ℝ) + 3) * narC (n + 1) (k + 1) =
    ((n : ℝ) + 3 + 2 * ((k : ℝ) + 1)) * narC n (k + 1) + (3 * ((n : ℝ) + 1) - 2 * k) * narC n
        k := by
  rcases le_or_gt k n with hk | hk
  · have h1 := Nat.choose_succ_right_eq n k
    have h2 := Nat.choose_succ_right_eq (n+1) k
    have h3 := Nat.add_one_mul_choose_eq n k
    have h4 := Nat.add_one_mul_choose_eq (n+1) k
    have c1 : ((n.choose (k+1) : ℕ) : ℝ) = (n.choose k) * ((n:ℝ) - k) / ((k:ℝ)+1) := by
      rw [eq_div_iff (by positivity)]
      have := congrArg (fun m : ℕ => (m : ℝ)) h1
      push_cast [Nat.cast_sub hk] at this
      linarith
    have c2 : (((n+1).choose (k+1) : ℕ) : ℝ) =
        ((n+1).choose k) * ((n:ℝ) + 1 - k) / ((k:ℝ)+1) := by
      rw [eq_div_iff (by positivity)]
      have := congrArg (fun m : ℕ => (m : ℝ)) h2
      push_cast [Nat.cast_sub (show k ≤ n + 1 by lia)] at this
      linarith
    have c3 : (((n+1).choose (k+1) : ℕ) : ℝ) = ((n:ℝ) + 1) * (n.choose k) / ((k:ℝ)+1) := by
      rw [eq_div_iff (by positivity)]
      have := congrArg (fun m : ℕ => (m : ℝ)) h3
      push_cast at this
      linarith
    have c4 : (((n+1+1).choose (k+1) : ℕ) : ℝ) =
        ((n:ℝ) + 2) * ((n+1).choose k) / ((k:ℝ)+1) := by
      rw [eq_div_iff (by positivity)]
      have := congrArg (fun m : ℕ => (m : ℝ)) h4
      push_cast at this
      linarith
    unfold narC
    push_cast
    rw [c1, c4]
    nth_rewrite 2 [c2]
    rw [c3]
    field_simp
    ring
  · unfold narC
    rw [Nat.choose_eq_zero_of_lt hk, Nat.choose_eq_zero_of_lt (show n < k + 1 by lia),
      Nat.choose_eq_zero_of_lt (show n + 1 < k + 1 by lia)]
    simp

/-- A differential recurrence for the Narayana polynomials:
`(n+3) N_{n+1} = (n+3 + 3(n+1)x) N_n + 2x(1-x) N_n'`. -/
private lemma narayanaN_rec (n : ℕ) : C ((n : ℝ) + 3) * narayanaN (n + 1) =
    (C ((n : ℝ) + 3) + C (3 * ((n : ℝ) + 1)) * X) * narayanaN n
      + C 2 * X * (1 - X) * derivative (narayanaN n) := by
  have e : (C ((n:ℝ)+3) + C (3*((n:ℝ)+1)) * X) * narayanaN n
      + C 2 * X * (1 - X) * derivative (narayanaN n) =
      C ((n:ℝ)+3) * narayanaN n + C (3*((n:ℝ)+1)) * (X * narayanaN n)
      + C 2 * (X * derivative (narayanaN n)) - C 2 * (X ^ 2 * derivative (narayanaN n)) := by
    ring
  rw [e]
  ext i
  rcases i with _ | k
  · simp [coeff_narayanaN, narC]
  · rw [coeff_sub, coeff_add, coeff_add, coeff_C_mul, coeff_C_mul, coeff_C_mul, coeff_C_mul,
      coeff_C_mul, coeff_X_mul, coeff_X_mul, coeff_X_pow_mul', coeff_derivative]
    rcases k with _ | k
    · simp [coeff_narayanaN, narC]
      ring
    · simp only [show 2 ≤ k + 1 + 1 by lia, ite_true, show k + 1 + 1 - 2 = k by lia,
        coeff_derivative, coeff_narayanaN]
      have := narC_rec n (k+1)
      push_cast at this ⊢
      linarith

/-- `N_n` has `n` simple negative roots `ρ 0 < ⋯ < ρ (n-1)`. -/
lemma narayanaN_roots (n : ℕ) : ∃ ρ : ℕ → ℝ, (∀ i j, i < j → j < n → ρ i < ρ j) ∧
    (∀ j < n, ρ j < 0) ∧ (narayanaN n).roots = ((List.range n).map ρ : Multiset ℝ) := by
  induction n with
  | zero =>
    refine ⟨fun _ => 0, fun i j h hj => absurd hj (by lia), fun j hj => absurd hj (by lia), ?_⟩
    have : narayanaN 0 = C 1 := by
      ext i; rw [coeff_narayanaN, coeff_C]; rcases i with _ | i <;> simp [narC]
    simp [this]
  | succ m ih =>
    obtain ⟨ρ, hmono, hneg, hroots⟩ := ih
    -- sign of `N_{m+1}` at the roots of `N_m`
    have hsignρ : ∀ j < m, 0 < (-1:ℝ)^(m - j) * (narayanaN (m+1)).eval (ρ j) := by
      intro j hj
      have hd := sign_deriv_at_sorted_root hmono (narayanaN_natDegree m) hroots
        (narayanaN_ne_zero m) (by rw [narayanaN_leadingCoeff]; norm_num) hj
      have hr : (narayanaN m).eval (ρ j) = 0 := by
        have : ρ j ∈ (narayanaN m).roots := by rw [hroots]; simp only
            [Multiset.mem_coe, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩
        exact ((mem_roots (narayanaN_ne_zero m)).1 this)
      have hrec := congrArg (eval (ρ j)) (narayanaN_rec m)
      simp only [eval_mul, eval_add, eval_C, eval_X, eval_sub, eval_one, hr, mul_zero,
        zero_add] at hrec
      have hm3 : (0:ℝ) < (m:ℝ) + 3 := by positivity
      have hρ := hneg j hj
      have hval : (narayanaN (m+1)).eval (ρ j) =
          2 * ρ j * (1 - ρ j) / ((m:ℝ)+3) * (derivative (narayanaN m)).eval (ρ j) := by
        field_simp; linarith
      rw [hval, show m - j = (m - 1 - j) + 1 by lia, pow_succ]
      have hc : 2 * ρ j * (1 - ρ j) / ((m:ℝ)+3) < 0 := by
        apply div_neg_of_neg_of_pos _ hm3; nlinarith
      nlinarith
    have hlc1 : 0 < (narayanaN (m+1)).leadingCoeff := by rw [narayanaN_leadingCoeff]; norm_num
    obtain ⟨T, hTB, hT⟩ := exists_far_left (narayanaN (m+1))
      (by rw [narayanaN_natDegree]; lia) hlc1 (if m = 0 then 0 else ρ 0)
    rw [narayanaN_natDegree] at hT
    set t : ℕ → ℝ := fun j => if j = 0 then T else if j ≤ m then ρ (j-1) else 0 with ht_def
    have htt : ∀ j < m + 1, t j < t (j+1) := by
      intro j hj
      simp only [ht_def]
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · simp only [ite_true, show (0+1 ≠ 0) from by lia, ite_false]
        by_cases hm : m = 0
        · simp only [hm, ite_true] at hTB
          rw [ite_eq_right (by lia)]; exact hTB
        · simp only [hm, ite_false] at hTB
          rw [ite_eq_left (by lia)]; simpa using hTB
      · simp only [show j ≠ 0 by lia, show j+1 ≠ 0 by lia, ite_false]
        by_cases h2 : j + 1 ≤ m
        · rw [ite_eq_left (by lia), ite_eq_left h2]
          exact hmono (j-1) (j+1-1) (by lia) (by lia)
        · rw [ite_eq_left (by lia), ite_eq_right h2]
          exact hneg (j-1) (by lia)
    have hsg : ∀ j < m + 1,
        (narayanaN (m+1)).eval (t j) * (narayanaN (m+1)).eval (t (j+1)) < 0 := by
      intro j hj
      simp only [ht_def]
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · simp only [ite_true, show (0 + 1 ≠ 0) from by lia, ite_false]
        split_ifs with h1
        · -- `m ≥ 1`: compare with the first root of `N_m`
          have := hsignρ 0 (by lia)
          rw [show m + 1 = (m - 0) + 1 by lia] at hT
          simp only [Nat.sub_self, zero_add] at this ⊢
          have hT' : 0 < (-1:ℝ)^((m - 0) + 1) * (narayanaN (m+1)).eval T := hT
          nlinarith [sign_mul_neg this hT']
        · have hm : m = 0 := by lia
          subst hm
          have h0 := narayanaN_eval_zero 1
          simp only [zero_add, pow_one, neg_mul, one_mul, Left.neg_pos_iff, gt_iff_lt] at hT ⊢
          rw [h0]; linarith
      · simp only [show j ≠ 0 by lia, ite_false, show j + 1 ≠ 0 by lia]
        split_ifs with h1 h2
        · -- two consecutive roots of `N_m`
          have a1 := hsignρ (j-1) (by lia)
          have a2 := hsignρ j (by lia)
          rw [show m - (j-1) = (m - j) + 1 by lia] at a1
          rw [show j + 1 - 1 = j by lia]
          nlinarith [sign_mul_neg a2 a1]
        · -- last root of `N_m` and `0`
          have hj' : j = m := by lia
          subst hj'
          have a1 := hsignρ (j-1) (by lia)
          rw [show j - (j-1) = 0 + 1 by lia] at a1
          rw [narayanaN_eval_zero]
          have : 0 < (-1:ℝ)^0 * (1:ℝ) := by norm_num
          linarith [sign_mul_neg this a1]
        · lia
        · lia
    obtain ⟨s, hs, _, hsroots⟩ := roots_of_alternation (narayanaN (m+1)) (m+1) (by lia)
      (narayanaN_natDegree _) t htt hsg
    refine ⟨s, mono_of_interleave hs, fun j hj => ?_, hsroots⟩
    have h1 := (hs j hj).2
    have : t (j+1) ≤ 0 := by
      simp only [ht_def, show j + 1 ≠ 0 by lia, ite_false, Nat.add_sub_cancel]
      split_ifs with h3
      · exact (hneg j (by lia)).le
      · exact le_rfl
    linarith

/-! ## The polynomials `M_n` -/

/-- `d_{n+1}(n) = 0`. -/
lemma bmCoeff_succ_self (n : ℕ) : bmCoeff n (n + 1) = 0 := by
  simp [bmCoeff]

/-- The top Boros–Moll coefficient `d_n(n)` is positive. -/
lemma bmCoeff_self_pos (n : ℕ) : 0 < bmCoeff n n := by
  simp only [bmCoeff, one_div, inv_pow, Finset.Icc_self, Finset.sum_singleton, tsub_self,
      Nat.choose_self, Nat.cast_one, mul_one, inv_pos, Nat.ofNat_pos, pow_pos,
      mul_pos_iff_of_pos_left, Nat.cast_pos]; exact Nat.choose_pos (by lia)

private lemma coeff_bmM (n i : ℕ) : (bmM n).coeff i = if i < n + 1 then bmL n i else 0 := by
  unfold bmM
  simp only [finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp

private lemma bmL_self (n : ℕ) : bmL n n = bmCoeff n n ^ 2 := by
  simp [bmL, bmCoeff_succ_self]

private lemma bmM_natDegree (n : ℕ) : (bmM n).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro i hi
    rw [coeff_bmM, ite_eq_right]
    have : n < i := by exact_mod_cast hi
    lia
  · rw [coeff_bmM, ite_eq_left (by lia), bmL_self]
    exact (pow_pos (bmCoeff_self_pos n) 2).ne'

private lemma bmM_leadingCoeff_pos (n : ℕ) : 0 < (bmM n).leadingCoeff := by
  rw [leadingCoeff, bmM_natDegree, coeff_bmM, ite_eq_left (by lia), bmL_self]
  exact pow_pos (bmCoeff_self_pos n) 2

/-- The full interlacing statement for a given `n`: `N_n` has `n` simple negative roots
`ρ 0 < ⋯ < ρ (n-1)`, `M_n` has `n` simple roots `μ 0 < ⋯ < μ (n-1)`, and
`μ 0 < ρ 0 < μ 1 < ρ 1 < ⋯ < μ (n-1) < ρ (n-1)`. -/
def BMInterlace (n : ℕ) : Prop :=
  ∃ ρ μ : ℕ → ℝ, (∀ i j, i < j → j < n → ρ i < ρ j) ∧ (∀ j < n, ρ j < 0) ∧
      (narayanaN n).roots = ((List.range n).map ρ : Multiset ℝ) ∧
      (∀ i j, i < j → j < n → μ i < μ j) ∧ (∀ j < n, μ j < ρ j) ∧
      (∀ j, j + 1 < n → ρ j < μ (j+1)) ∧ bmM n ≠ 0 ∧
      (bmM n).roots = ((List.range n).map μ : Multiset ℝ)

/-- The interlacing, assuming the sign condition `M_n(ρ) N_n'(ρ) > 0` at every root `ρ`
of `N_n`. -/
lemma bmInterlace_of_sign (n : ℕ) (hn : 1 ≤ n)
    (hS : ∀ r : ℝ, (narayanaN n).IsRoot r →
      0 < (bmM n).eval r * (derivative (narayanaN n)).eval r) :
    BMInterlace n := by
  obtain ⟨ρ, hmono, hneg, hroots⟩ := narayanaN_roots n
  -- sign of `M_n` at the roots of `N_n`
  have hsignρ : ∀ j < n, 0 < (-1:ℝ)^(n - 1 - j) * (bmM n).eval (ρ j) := by
    intro j hj
    have hd := sign_deriv_at_sorted_root hmono (narayanaN_natDegree n) hroots
      (narayanaN_ne_zero n) (by rw [narayanaN_leadingCoeff]; norm_num) hj
    have hr : (narayanaN n).IsRoot (ρ j) := by
      have : ρ j ∈ (narayanaN n).roots := by rw [hroots]; simp only
          [Multiset.mem_coe, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩
      exact ((mem_roots (narayanaN_ne_zero n)).1 this)
    have hw := hS (ρ j) hr
    have hsq : ((-1:ℝ)^(n - 1 - j))^2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
    by_contra hcon
    push Not at hcon
    have : ((-1:ℝ)^(n - 1 - j) * (bmM n).eval (ρ j)) *
        ((-1:ℝ)^(n - 1 - j) * (derivative (narayanaN n)).eval (ρ j)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hcon hd.le
    nlinarith
  obtain ⟨T, hTB, hT⟩ := exists_far_left (bmM n) (by rw [bmM_natDegree]; lia)
    (bmM_leadingCoeff_pos n) (ρ 0)
  rw [bmM_natDegree] at hT
  set t : ℕ → ℝ := fun j => if j = 0 then T else ρ (j-1) with ht_def
  have htt : ∀ j < n, t j < t (j+1) := by
    intro j hj
    simp only [ht_def]
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simpa using hTB
    · simp only [show j ≠ 0 by lia, show j + 1 ≠ 0 by lia, ite_false]
      exact hmono _ _ (by lia) (by lia)
  have hsg : ∀ j < n, (bmM n).eval (t j) * (bmM n).eval (t (j+1)) < 0 := by
    intro j hj
    simp only [ht_def]
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp only [ite_true, show (0 + 1 ≠ 0) from by lia, ite_false, Nat.add_sub_cancel]
      have a1 := hsignρ 0 (by lia)
      have hT' : 0 < (-1:ℝ)^((n - 1 - 0) + 1) * (bmM n).eval T := by
        rw [show (n - 1 - 0) + 1 = n by lia]; exact hT
      nlinarith [sign_mul_neg a1 hT']
    · simp only [show j ≠ 0 by lia, show j + 1 ≠ 0 by lia, ite_false]
      have a1 := hsignρ (j-1) (by lia)
      have a2 := hsignρ j (by lia)
      rw [show n - 1 - (j-1) = (n - 1 - j) + 1 by lia] at a1
      rw [show j + 1 - 1 = j by lia]
      nlinarith [sign_mul_neg a2 a1]
  obtain ⟨μ, hμ, hM0, hμroots⟩ := roots_of_alternation (bmM n) n hn (bmM_natDegree n) t htt hsg
  refine ⟨ρ, μ, hmono, hneg, hroots, mono_of_interleave hμ, fun j hj => ?_, fun j hj => ?_,
    hM0, hμroots⟩
  · have := (hμ j hj).2; simpa [ht_def] using this
  · have := (hμ (j+1) hj).1; simpa [ht_def] using this

/-- Theorem 1.1 (first part), from the interlacing data. -/
lemma bmM_roots_of_interlace (n : ℕ) (h : BMInterlace n) :
    bmM n ≠ 0 ∧ (bmM n).natDegree = n ∧ (bmM n).Splits ∧ (bmM n).roots.Nodup ∧
      ∀ r ∈ (bmM n).roots, r < 0 := by
  obtain ⟨ρ, μ, hmono, hneg, -, hμmono, hμρ, -, hM0, hμroots⟩ := h
  refine ⟨hM0, bmM_natDegree n, ?_, ?_, ?_⟩
  · rw [splits_iff_card_roots, hμroots, bmM_natDegree]; simp
  · rw [hμroots]; exact nodup_map_range hμmono
  · intro r hr
    rw [hμroots] at hr
    simp only [Multiset.mem_coe, List.mem_map, List.mem_range] at hr
    obtain ⟨j, hj, rfl⟩ := hr
    exact (hμρ j hj).trans (hneg j hj)

/-- Theorem 1.1 (second part), from the interlacing data. -/
lemma bmM_strictInterlaces_of_interlace (n : ℕ) (h : BMInterlace n) :
    StrictInterlacesSameDegree (bmM n) (narayanaN n) n := by
  obtain ⟨ρ, μ, hmono, -, hroots, hμmono, hμρ, hρμ, -, hμroots⟩ := h
  rw [StrictInterlacesSameDegree, sortedRoots_eq hmono hroots, sortedRoots_eq hμmono hμroots]
  refine ⟨by simp, by simp, fun i hi => ?_, fun i hi => ?_⟩
  · rw [getD_map_range hi, getD_map_range hi]; exact hμρ i hi
  · rw [getD_map_range (by lia), getD_map_range hi]; exact hρμ i hi

end Basic

section SmallCasesCore

/-! ## Small degrees: exact computation

For `1 ≤ n ≤ 35` we certify the interlacing of the zeros of `M_n` and `N_n` by exhibiting
explicit dyadic rationals `t 0 < t 1 < ⋯ < t (2n) ≤ 0` such that `M_n` changes sign on each
`[t (2j), t (2j+1)]` and `N_n` changes sign on each `[t (2j+1), t (2j+2)]`.  The sign checks
are done with exact integer arithmetic, verified by the kernel.
-/

open Polynomial

/-- Roots in prescribed disjoint intervals: a degree `n` polynomial changing sign on `n`
disjoint intervals `(a j, b j)` has exactly one simple root in each, and no others. -/
private lemma roots_of_intervals (p : ℝ[X]) (n : ℕ) (hn : 1 ≤ n) (hdeg : p.natDegree = n)
    (a b : ℕ → ℝ) (hab : ∀ j < n, a j < b j) (hba : ∀ j, j + 1 < n → b j ≤ a (j + 1))
    (hsign : ∀ j < n, p.eval (a j) * p.eval (b j) < 0) :
    ∃ s : ℕ → ℝ, (∀ j < n, a j < s j ∧ s j < b j) ∧ p ≠ 0 ∧
      p.roots = ((List.range n).map s : Multiset ℝ) := by
  have : ∀ j, ∃ x, j < n → (a j < x ∧ x < b j ∧ p.eval x = 0) := by
    intro j
    by_cases hj : j < n
    · obtain ⟨x, hx, hx0⟩ := exists_root_between (hab j hj) (hsign j hj)
      exact ⟨x, fun _ => ⟨hx.1, hx.2, hx0⟩⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose s hs using this
  have hp0 : p ≠ 0 := by
    intro h; have := hsign 0 hn; simp [h] at this
  have hmono : ∀ i j, i < j → j < n → s i < s j :=
    lt_of_succ_lt (fun j hj => (((hs j (by lia)).2.1).trans_le (hba j hj)).trans
      (hs (j+1) hj).1)
  have hle : ((List.range n).map s : Multiset ℝ) ≤ p.roots := by
    rw [Multiset.le_iff_subset (nodup_map_range hmono)]
    intro x hx
    simp only [Multiset.mem_coe, List.mem_map, List.mem_range] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    exact (mem_roots hp0).2 (hs j hj).2.2
  refine ⟨s, fun j hj => ⟨(hs j hj).1, (hs j hj).2.1⟩, hp0,
    (Multiset.eq_of_le_of_card_le hle ?_).symm⟩
  simpa [hdeg] using card_roots' p

private lemma mono_of_succ {t : ℕ → ℝ} {m : ℕ} (ht : ∀ i < m, t i < t (i + 1)) :
    ∀ i j, i ≤ j → j ≤ m → t i ≤ t j := by
  intro i j hij hjm
  induction j with
  | zero => have : i = 0 := by lia
            subst this; exact le_rfl
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hij) with h | h
    · exact (ih (by lia) (by lia)).trans (ht k (by lia)).le
    · rw [h]

/-- Interlacing from explicit sign changes at increasing points. -/
private lemma bmInterlace_of_points (n : ℕ) (hn : 1 ≤ n) (t : ℕ → ℝ)
    (ht : ∀ i < 2 * n, t i < t (i + 1)) (h0 : t (2 * n) ≤ 0)
    (hM : ∀ j < n, (bmM n).eval (t (2 * j)) * (bmM n).eval (t (2 * j + 1)) < 0)
    (hN : ∀ j < n, (narayanaN n).eval (t (2 * j + 1)) * (narayanaN n).eval (t (2 * j + 2)) < 0) :
    BMInterlace n := by
  have hmo := mono_of_succ ht
  obtain ⟨μ, hμ, hM0, hμroots⟩ := roots_of_intervals (bmM n) n hn (bmM_natDegree n)
    (fun j => t (2*j)) (fun j => t (2*j+1)) (fun j hj => ht _ (by lia))
    (fun j hj => hmo _ _ (by lia) (by lia)) hM
  obtain ⟨ρ, hρ, -, hρroots⟩ := roots_of_intervals (narayanaN n) n hn (narayanaN_natDegree n)
    (fun j => t (2*j+1)) (fun j => t (2*j+2)) (fun j hj => ht _ (by lia))
    (fun j hj => hmo _ _ (by lia) (by lia)) hN
  refine ⟨ρ, μ, ?_, ?_, hρroots, ?_, ?_, ?_, hM0, hμroots⟩
  · exact lt_of_succ_lt (fun j hj => ((hρ j (by lia)).2.trans_le
      (hmo _ _ (by lia) (by lia))).trans (hρ (j+1) hj).1)
  · intro j hj
    exact (hρ j hj).2.trans_le ((hmo _ _ (by lia) (by lia)).trans h0)
  · exact lt_of_succ_lt (fun j hj => ((hμ j (by lia)).2.trans_le
      (hmo _ _ (by lia) (by lia))).trans (hμ (j+1) hj).1)
  · intro j hj; exact (hμ j hj).2.trans (hρ j hj).1
  · intro j hj
    have := (hμ (j+1) hj).1
    rw [show 2 * (j+1) = 2*j+2 by ring] at this
    exact (hρ j (by lia)).2.trans this

/-! ### Integer versions of the coefficients -/

/-- A kernel-friendly binomial coefficient. -/
private def chooseF (n k : ℕ) : ℕ := n.descFactorial k / k.factorial

private lemma chooseF_eq (n k : ℕ) : chooseF n k = n.choose k :=
  (Nat.choose_eq_descFactorial_div_factorial n k).symm

/-- `4^n d_i(n)`, an integer. -/
private def bmDF (n i : ℕ) : ℕ :=
  ((List.range (n + 1 - i)).map (fun r =>
    2 ^ (i + r) * chooseF (2 * n - 2 * (i + r)) (n - (i + r)) * chooseF (n + (i + r)) n *
      chooseF (i + r) i)).sum

/-- `16^n L(d(n))_i`, an integer. -/
private def LintF (n i : ℕ) : ℤ :=
  (bmDF n i : ℤ) ^ 2 - (if i = 0 then 0 else (bmDF n (i - 1) : ℤ)) * (bmDF n (i + 1) : ℤ)

/-- The Narayana number, written as `C(n,i)^2 - C(n,i-1) C(n,i+1)`. -/
private def NintF (n i : ℕ) : ℤ :=
  (chooseF n i : ℤ) ^ 2 - (if i = 0 then 0 else (chooseF n (i - 1) : ℤ)) * (chooseF n (i + 1) : ℤ)

/-- Homogenized evaluation at `a / 1024`, multiplied by `1024 ^ n`. -/
private def hornerAt (cs : List ℤ) (n : ℕ) (a : ℤ) : ℤ :=
  ((List.range (n + 1)).map (fun i => cs.getD i 0 * a ^ i * 1024 ^ (n - i))).sum

private lemma bmCoeff_eq_bmDF (n i : ℕ) : bmCoeff n i = (bmDF n i : ℝ) / 4 ^ n := by
  unfold bmCoeff bmDF
  have : ∀ m (f : ℕ → ℕ), ((((List.range m).map f).sum : ℕ) : ℝ) =
      ∑ r ∈ Finset.range m, (f r : ℝ) := by
    intro m f
    simp [Finset.sum_eq_multiset_sum, Finset.range_val, Multiset.range, Function.comp_def]
  rw [this, show Finset.Icc i n = Finset.Ico i (n + 1) from rfl, Finset.sum_Ico_eq_sum_range]
  simp only [chooseF_eq]
  push_cast
  rw [eq_div_iff (by positivity), mul_comm, ← mul_assoc, ← mul_pow]
  norm_num

private lemma bmL_eq_LintF (n i : ℕ) : bmL n i = (LintF n i : ℝ) / 16 ^ n := by
  unfold bmL LintF
  rw [bmCoeff_eq_bmDF, bmCoeff_eq_bmDF]
  have h16 : (16:ℝ)^n = 4^n * 4^n := by rw [← mul_pow]; norm_num
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp only [↓reduceIte, zero_add, zero_mul, sub_zero, Int.cast_pow, Int.cast_natCast]; rw [h16];
        field_simp
  · simp only [show i ≠ 0 by lia, ite_false]
    rw [bmCoeff_eq_bmDF]
    push_cast
    rw [h16]; field_simp

private lemma narC_eq_NintF (n i : ℕ) : narC n i = (NintF n i : ℝ) := by
  unfold narC NintF
  simp only [chooseF_eq]
  rcases le_or_gt i n with hin | hin
  · rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by lia⟩
      simp only [show j + 1 ≠ 0 by lia, ite_false, Nat.add_sub_cancel]
      have h1 := Nat.choose_succ_right_eq n j
      have h2 := Nat.choose_succ_right_eq n (j+1)
      have h3 := Nat.add_one_mul_choose_eq n j
      have c1 : ((n.choose (j+1) : ℕ) : ℝ) * ((j:ℝ)+1) = (n.choose j) * ((n:ℝ) - j) := by
        have := congrArg (fun m : ℕ => (m:ℝ)) h1
        push_cast [Nat.cast_sub (show j ≤ n by lia)] at this; linarith
      have c2 : (((n+1).choose (j+1) : ℕ) : ℝ) * ((j:ℝ)+1) = ((n:ℝ)+1) * (n.choose j) := by
        have := congrArg (fun m : ℕ => (m:ℝ)) h3
        push_cast at this; linarith
      have h4 : ((n + 1).choose (j + 1) : ℝ) * ((n:ℝ) - j) = ((n:ℝ) + 1) * (n.choose (j+1)) := by
        have hj : (0:ℝ) < (j:ℝ) + 1 := by positivity
        have : (((n+1).choose (j+1) : ℕ) : ℝ) * ((n:ℝ) - j) * ((j:ℝ)+1) =
            ((n:ℝ) + 1) * (n.choose (j+1)) * ((j:ℝ)+1) := by
          linear_combination ((n:ℝ)-j) * c2 - ((n:ℝ)+1) * c1
        exact mul_right_cancel₀ hj.ne' this
      have c1 : ((n.choose (j+1) : ℕ) : ℝ) * ((j:ℝ)+1) = (n.choose j) * ((n:ℝ) - j) := by
        have := congrArg (fun m : ℕ => (m:ℝ)) h1
        push_cast [Nat.cast_sub (show j ≤ n by lia)] at this; linarith
      have c3 : ((n.choose (j+2) : ℕ) : ℝ) * ((j:ℝ)+2) = (n.choose (j+1)) * ((n:ℝ) - j - 1) := by
        have := congrArg (fun m : ℕ => (m:ℝ)) h2
        push_cast [Nat.cast_sub (show j + 1 ≤ n by lia)] at this; linarith
      have hnj : (0:ℝ) < (n:ℝ) - j := by
        have : (j:ℝ) + 1 ≤ n := by exact_mod_cast hin
        linarith
      push_cast
      have e1 : ((n+1).choose (j+1) : ℝ) = ((n:ℝ) + 1) * (n.choose (j+1)) / ((n:ℝ) - j) := by
        rw [eq_div_iff hnj.ne']; exact h4
      have e2 : (n.choose j : ℝ) = (n.choose (j+1)) * ((j:ℝ)+1) / ((n:ℝ) - j) := by
        rw [eq_div_iff hnj.ne']; linarith
      have e3 : (n.choose (j+2) : ℝ) = (n.choose (j+1)) * ((n:ℝ) - j - 1) / ((j:ℝ)+2) := by
        rw [eq_div_iff (by positivity)]; linarith
      rw [e1, e2, e3]
      field_simp
      ring
  · rw [Nat.choose_eq_zero_of_lt hin, Nat.choose_eq_zero_of_lt (show n < i + 1 by lia)]
    simp

private lemma list_sum_cast (m : ℕ) (f : ℕ → ℤ) :
    ((((List.range m).map f).sum : ℤ) : ℝ) = ∑ r ∈ Finset.range m, (f r : ℝ) := by
  simp [Finset.sum_eq_multiset_sum, Finset.range_val, Multiset.range, Function.comp_def]

private lemma hornerAt_cast (cs : List ℤ) (n : ℕ) (a : ℤ) (c : ℕ → ℝ)
    (hc : ∀ i < n + 1, (cs.getD i 0 : ℝ) = c i) :
    (hornerAt cs n a : ℝ) =
      1024 ^ n * ∑ i ∈ Finset.range (n + 1), c i * ((a : ℝ) / 1024) ^ i := by
  unfold hornerAt
  rw [list_sum_cast, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n := by simp at hi; lia
  push_cast
  rw [hc i (by lia), div_pow, show (1024:ℝ)^n = 1024^(n-i) * 1024^i by
    rw [← pow_add, Nat.sub_add_cancel hi']]
  field_simp

private lemma eval_bmM_dyadic (n : ℕ) (cs : List ℤ) (hcs : (List.range (n + 1)).map (LintF n) = cs)
    (a : ℤ) : (bmM n).eval ((a : ℝ) / 1024) = (hornerAt cs n a : ℝ) / (16 ^ n * 1024 ^ n) := by
  rw [hornerAt_cast cs n a (fun i => (LintF n i : ℝ))]
  · unfold bmM
    rw [eval_finsetSum]
    simp only [eval_mul, eval_C, eval_pow, eval_X]
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [bmL_eq_LintF]
    field_simp
  · intro i hi
    rw [← hcs]; simp [List.getD_eq_getElem?_getD, hi]

private lemma eval_narayanaN_dyadic (n : ℕ) (cs : List ℤ)
    (hcs : (List.range (n + 1)).map (NintF n) = cs)
    (a : ℤ) : (narayanaN n).eval ((a : ℝ) / 1024) = (hornerAt cs n a : ℝ) / 1024 ^ n := by
  rw [hornerAt_cast cs n a (fun i => (NintF n i : ℝ))]
  · unfold narayanaN
    rw [eval_finsetSum]
    simp only [eval_mul, eval_C, eval_pow, eval_X]
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← narC, narC_eq_NintF]
    field_simp
  · intro i hi
    rw [← hcs]; simp [List.getD_eq_getElem?_getD, hi]

/-- The Boolean certificate check. -/
private def checkN (n : ℕ) (cm cn l : List ℤ) : Bool :=
  l.length == 2 * n + 1 &&
  (List.range (2 * n)).all (fun i => decide (l.getD i 0 < l.getD (i + 1) 0)) &&
  decide (l.getD (2 * n) 0 ≤ 0) &&
  (List.range n).all (fun j =>
    decide (hornerAt cm n (l.getD (2 * j) 0) * hornerAt cm n (l.getD (2 * j + 1) 0) < 0) &&
    decide (hornerAt cn n (l.getD (2 * j + 1) 0) * hornerAt cn n (l.getD (2 * j + 2) 0) < 0))

private lemma bmInterlace_of_check (n : ℕ) (hn : 1 ≤ n) (cm cn l : List ℤ)
    (hcm : (List.range (n + 1)).map (LintF n) = cm) (hcn : (List.range (n + 1)).map (NintF n) = cn)
    (h : checkN n cm cn l = true) : BMInterlace n := by
  simp only [checkN, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    beq_iff_eq] at h
  obtain ⟨⟨⟨-, h1⟩, h2⟩, h3⟩ := h
  have hpos16 : (0:ℝ) < 16 ^ n * 1024 ^ n := by positivity
  have hpos : (0:ℝ) < 1024 ^ n := by positivity
  refine bmInterlace_of_points n hn (fun i => ((l.getD i 0 : ℤ) : ℝ) / 1024) ?_ ?_ ?_ ?_
  · intro i hi
    have := h1 i hi
    have : ((l.getD i 0 : ℤ) : ℝ) < ((l.getD (i+1) 0 : ℤ) : ℝ) := by exact_mod_cast this
    linarith
  · have : ((l.getD (2*n) 0 : ℤ) : ℝ) ≤ 0 := by exact_mod_cast h2
    linarith
  · intro j hj
    rw [eval_bmM_dyadic n cm hcm, eval_bmM_dyadic n cm hcm, div_mul_div_comm]
    apply div_neg_of_neg_of_pos
    · exact_mod_cast (h3 j hj).1
    · positivity
  · intro j hj
    rw [eval_narayanaN_dyadic n cn hcn, eval_narayanaN_dyadic n cn hcn, div_mul_div_comm]
    apply div_neg_of_neg_of_pos
    · exact_mod_cast (h3 j hj).2
    · positivity

end SmallCasesCore

section SmallCases

/-! Certificates for `1 ≤ n ≤ 35` (generated tables, checked by the kernel). -/

/-- `16^n L(d(1))_i`. -/
private def cmT1 : List ℤ := [36, 16]
private def cnT1 : List ℤ := [1, 1]
private def ptT1 : List ℤ := [-4096, -2048, 0]

private theorem bmInterlace_1 : BMInterlace 1 :=
  bmInterlace_of_check 1 (by norm_num) cmT1 cnT1 ptT1 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `16^n L(d(2))_i`. -/
private def cmT2 : List ℤ := [1764, 2592, 576]
private def cnT2 : List ℤ := [1, 3, 1]
private def ptT2 : List ℤ := [-6144, -3072, -2048, -512, 0]

private theorem bmInterlace_2 : BMInterlace 2 :=
  bmInterlace_of_check 2 (by norm_num) cmT2 cnT2 ptT2 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `16^n L(d(3))_i`. -/
private def cmT3 : List ℤ := [94864, 300864, 203520, 25600]
private def cnT3 : List ℤ := [1, 6, 6, 1]
private def ptT3 : List ℤ := [-10240, -5120, -3072, -1280, -512, -256, 0]

private theorem bmInterlace_3 : BMInterlace 3 :=
  bmInterlace_of_check 3 (by norm_num) cmT3 cnT3 ptT3 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `16^n L(d(4))_i`. -/
private def cmT4 : List ℤ := [5336100, 29890800, 41054400, 15590400, 1254400]
private def cnT4 : List ℤ := [1, 10, 20, 10, 1]
private def ptT4 : List ℤ := [-14336, -8192, -5120, -2048, -1024, -768, -512, -256, 0]

private theorem bmInterlace_4 : BMInterlace 4 :=
  bmInterlace_of_check 4 (by norm_num) cmT4 cnT4 ptT4 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `16^n L(d(5))_i`. -/
private def cmT5 : List ℤ := [308213136, 2709842688, 6293839104, 4809821184, 1165086720, 65028096]
private def cnT5 : List ℤ := [1, 15, 50, 50, 15, 1]
private def ptT5 : List ℤ := [-19456, -12288, -7168, -3072, -2048, -1280, -768, -512, -256, -128, 0]

private theorem bmInterlace_5 : BMInterlace 5 :=
  bmInterlace_of_check 5 (by norm_num) cmT5 cnT5 ptT5 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `16^n L(d(6))_i`. -/
private def cmT6 : List ℤ := [18116083216, 231270438336, 816643502080, 1046448076800, 508673249280,
    85360214016, 3497066496]
private def cnT6 : List ℤ := [1, 21, 105, 175, 105, 21, 1]
private def ptT6 : List ℤ := [-26624, -16384, -10240, -4096, -3072, -1792, -1024, -768, -512, -320,
    -256, -128, 0]

private theorem bmInterlace_6 : BMInterlace 6 :=
  bmInterlace_of_check 6 (by norm_num) cmT6 cnT6 ptT6 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `16^n L(d(7))_i`. -/
private def cmT7 : List ℤ := [1078091809344, 18910627333632, 94646238621696, 182983593369600,
    148729938001920, 50020968628224, 6156835356672, 192980975616]
private def cnT7 : List ℤ := [1, 28, 196, 490, 490, 196, 28, 1]
private def ptT7 : List ℤ := [-33792, -20480, -12288, -5632, -4096, -2304, -2048, -1152, -768, -512,
    -384, -256, -128, -64, 0]

private theorem bmInterlace_7 : BMInterlace 7 :=
  bmInterlace_of_check 7 (by norm_num) cmT7 cnT7 ptT7 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `16^n L(d(8))_i`. -/
private def cmT8 : List ℤ := [64752889298724, 1497755160072864, 10107936521337600,
    27511992362764800, 33649107835622400, 18899553401524224, 4659016065859584, 438549267087360,
    10855179878400]
private def cnT8 : List ℤ := [1, 36, 336, 1176, 1764, 1176, 336, 36, 1]
private def ptT8 : List ℤ := [-40960, -25600, -16384, -7168, -5120, -3072, -2048, -1536, -1024,
    -768, -512, -384, -256, -192, -128, -64, 0]

private theorem bmInterlace_8 : BMInterlace 8 :=
  bmInterlace_of_check 8 (by norm_num) cmT8 cnT8 ptT8 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `16^n L(d(9))_i`. -/
private def cmT9 : List ℤ := [3917150093379600, 115735238749240000, 1014584615693158400,
    3701614722993510400, 6357719445901824000, 5366857770808934400, 2207993474188902400,
    416082931161497600, 30920376818073600, 619683355033600]
private def cnT9 : List ℤ := [1, 45, 540, 2520, 5292, 5292, 2520, 540, 45, 1]
private def ptT9 : List ℤ := [-50176, -31744, -19456, -9216, -6144, -4096, -3072, -2048, -1536,
    -1152, -768, -640, -512, -320, -256, -128, -64, -48, 0]

private theorem bmInterlace_9 : BMInterlace 9 :=
  bmInterlace_of_check 9 (by norm_num) cmT9 cnT9 ptT9 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `16^n L(d(10))_i`. -/
private def cmT10 : List ℤ := [238319411681214864, 8769352111513776640, 97000615233878543616,
    457306464969386013696, 1050369090784383225856, 1243696126812987015168, 768515214810904264704,
    241600273923208904704, 35934006289848336384, 2161703415699210240, 35792910586740736]
private def cnT10 : List ℤ := [1, 55, 825, 4950, 13860, 19404, 13860, 4950, 825, 55, 1]
private def ptT10 : List ℤ := [-59392, -37888, -23552, -11264, -7168, -4608, -4096, -2560, -2048,
    -1408, -1024, -896, -768, -512, -384, -256, -192, -128, -64, -32, 0]

private theorem bmInterlace_10 : BMInterlace 10 :=
  bmInterlace_of_check 10 (by norm_num) cmT10 cnT10 ptT10 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `16^n L(d(11))_i`. -/
private def cmT11 : List ℤ := [14567027841274918464, 653927673297021537024, 8917096769669512719360,
    52800210228804575846400, 156370484702282980147200, 247325235321876126105600,
    214234243805701944115200, 101117838699127111680000, 25083538916974578892800,
    3019574242713293291520, 150056896783466889216, 2087229562810269696]
private def cnT11 : List ℤ := [1, 66, 1210, 9075, 32670, 60984, 60984, 32670, 9075, 1210, 66, 1]
private def ptT11 : List ℤ := [-69632, -45056, -27648, -13312, -9216, -5632, -4096, -3072, -2048,
    -1792, -1536, -1152, -768, -640, -512, -384, -256, -192, -128, -96, -64, -32, 0]

private theorem bmInterlace_11 : BMInterlace 11 :=
  bmInterlace_of_check 11 (by norm_num) cmT11 cnT11 ptT11 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `16^n L(d(12))_i`. -/
private def cmT12 : List ℤ := [893849013927119302416, 48120977670361108688448,
    793685230986782853298944, 5769912357418030425676800, 21418688317611124979712000,
    43634596111074950588006400, 50458059905429867043225600, 33372612712157841535795200,
    12426212696148889593446400, 2494448467235733388656640, 248026228175881176612864,
    10353354374726541115392, 122682715414070296576]
private def cnT12 : List ℤ := [1, 78, 1716, 15730, 70785, 169884, 226512, 169884, 70785, 15730,
    1716, 78, 1]
private def ptT12 : List ℤ := [-81920, -52224, -32768, -15360, -11264, -6656, -5120, -3584, -3072,
    -2176, -2048, -1408, -1024, -896, -768, -512, -384, -320, -256, -192, -128, -96, -64, -32, 0]

private theorem bmInterlace_12 : BMInterlace 12 :=
  bmInterlace_of_check 12 (by norm_num) cmT12 cnT12 ptT12 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `16^n L(d(13))_i`. -/
private def cmT13 : List ℤ := [55027249354424551611456, 3501767840430639530128896,
    68758738310762815698109440, 602399190663056541197721600, 2740361936644788305220403200,
    6990588649293136452904550400, 10406029278642248649749299200, 9184746335070062327522918400,
    4791078269622419604583219200, 1443394265247576075251220480, 239295872712267790773387264,
    19984485135629348014915584, 710616036206114871705600, 7259332273021911040000]
private def cnT13 : List ℤ := [1, 91, 2366, 26026, 143143, 429429, 736164, 736164, 429429, 143143,
    26026, 2366, 91, 1]
private def ptT13 : List ℤ := [-93184, -60416, -37888, -17408, -12288, -8192, -6144, -4352, -3072,
    -2560, -2048, -1664, -1536, -1088, -768, -704, -512, -448, -384, -256, -192, -160, -128, -64,
    -32, -24, 0]

private theorem bmInterlace_13 : BMInterlace 13 :=
  bmInterlace_of_check 13 (by norm_num) cmT13 cnT13 ptT13 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `16^n L(d(14))_i`. -/
private def cmT14 : List ℤ := [3397090393819066706625600, 252404615358230695506720000,
    5821408193288088804188774400, 60519051532159021911586406400, 331209721697763813066901094400,
    1034415257120784360151135027200, 1927040237249883828430543257600,
    2188732578684183850354842009600, 1523284058685689838209964441600,
    642806980517884603819622400000, 159917747019452217723086438400, 22266108250672300151537664000,
    1583916264231910149980160000, 48552488336905690152960000, 432004345063916175360000]
private def cnT14 : List ℤ := [1, 105, 3185, 41405, 273273, 1002001, 2147145, 2760615, 2147145,
    1002001, 273273, 41405, 3185, 105, 1]
private def ptT14 : List ℤ := [-106496, -68608, -43008, -19456, -14336, -9216, -7168, -5120, -4096,
    -3072, -2560, -2048, -1536, -1280, -1024, -896, -768, -576, -512, -384, -320, -256, -192, -128,
    -96, -64, -32, -16, 0]

private theorem bmInterlace_14 : BMInterlace 14 :=
  bmInterlace_of_check 14 (by norm_num) cmT14 cnT14 ptT14 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `16^n L(d(15))_i`. -/
private def cmT15 : List ℤ := [210227051749051932546910464, 18043853486756556744688988160,
    483219897425958962352350232576, 5883313128033564436080089235456,
    38145892279120072152478993612800, 143197453559956506356714969235456,
    326425121482781993044201445523456, 463834303296243873700912199368704,
    415310798575562144085963643551744, 233790733809540014947851393040384,
    81459661273662004808020698071040, 17018446156003140517035507712000,
    2018227626579615056447039078400, 123758164429365922639537766400, 3304084432207514620133376000,
    25835779854133582469529600]
private def cnT15 : List ℤ := [1, 120, 4200, 63700, 496860, 2186184, 5725720, 9202050, 9202050,
    5725720, 2186184, 496860, 63700, 4200, 120, 1]
private def ptT15 : List ℤ := [-120832, -77824, -49152, -22528, -16384, -10240, -8192, -5632, -5120,
    -3584, -3072, -2304, -2048, -1536, -1280, -1088, -896, -768, -640, -512, -384, -320, -256, -192,
    -160, -128, -96, -64, -32, -16, 0]

private theorem bmInterlace_15 : BMInterlace 15 :=
  bmInterlace_of_check 15 (by norm_num) cmT15 cnT15 ptT15 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `16^n L(d(16))_i`. -/
private def cmT16 : List ℤ := [13037362006124798754354494244, 1280680681949152712014517688384,
    39427660967904535560140888755200, 555914871942455301473910514636800,
    4215070483012254238938022600396800, 18729948080766559291508891751727104,
    51292791850311193576935897117425664, 89154960713277417298258939708047360,
    99847743837797900970434365548134400, 72301696058961460121096553549004800,
    33602426612497546742358982891929600, 9831321695556980823964744522137600,
    1749302746785355514873018056704000, 178817576283119323186578063360000,
    9549826147560301417753214976000, 224054341840009960571378073600, 1551761527488898297076121600]
private def cnT16 : List ℤ := [1, 136, 5440, 95200, 866320, 4504864, 14158144, 27810640, 34763300,
    27810640, 14158144, 4504864, 866320, 95200, 5440, 136, 1]
private def ptT16 : List ℤ := [-135168, -87040, -55296, -25600, -18432, -11776, -9216, -6656, -5120,
    -4096, -3072, -2688, -2048, -1792, -1536, -1280, -1024, -896, -768, -640, -512, -448, -384,
    -288, -256, -192, -128, -96, -64, -48, -32, -16, 0]

private theorem bmInterlace_16 : BMInterlace 16 :=
  bmInterlace_of_check 16 (by norm_num) cmT16 cnT16 ptT16 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `16^n L(d(17))_i`. -/
private def cmT17 : List ℤ := [810030699591615523990274389776, 90324911009427343240363457617728,
    3168934252142836473815928177936384, 51240895993094306572391840053862400,
    449310645303364648677228342107258880, 2332912742048017445281644811870273536,
    7558706309463442174556062100005060608, 15778663396729550212243853673220276224,
    21611277230345552844292977610850304000, 19570803720053160909085537344159744000,
    11698779679782153297886482702689894400, 4565141478125942134650409449632563200,
    1137483471853104979500443914312089600, 174450749427563858197973764669440000,
    15530433586134304626465451278336000, 728847414157382704747898103398400,
    15145557628651056532003435315200, 93556722681545203903994265600]
private def cnT17 : List ℤ := [1, 153, 6936, 138720, 1456560, 8836464, 32821152, 77364144,
    118195220, 118195220, 77364144, 32821152, 8836464, 1456560, 138720, 6936, 153, 1]
private def ptT17 : List ℤ := [-150528, -97280, -62464, -28672, -20480, -13312, -10240, -7424,
    -6144, -4608, -4096, -3072, -2560, -2176, -2048, -1536, -1280, -1088, -896, -768, -640, -512,
    -448, -384, -320, -256, -192, -160, -128, -96, -64, -48, -32, -16, 0]

private theorem bmInterlace_17 : BMInterlace 17 :=
  bmInterlace_of_check 17 (by norm_num) cmT17 cnT17 ptT17 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `16^n L(d(18))_i`. -/
private def cmT18 : List ℤ := [50411910575818936499197199985936, 6334923023871467248576646055312256,
    251327104206694211632877844729217280, 4620962790937425881799598410287564800,
    46409126958906299615809264170487726080, 278456087675857171973316244044997656576,
    1053706438305147069422376092480995065856, 2601586027419608284832422537564966092800,
    4278505578281338384266263531257200640000, 4737780997844353625352630154146349056000,
    3541436973437387187766069439498708582400, 1777334880334656413978876890541614694400,
    590618343431037175066807653120344064000, 126838939794535018502414014233968640000,
    16940654957691117319561922199158784000, 1325244982624480587631549636568678400,
    55084546923236360018483160180326400, 1020911748283839386156808536064000,
    5659604211599648137402122240000]
private def cnT18 : List ℤ := [1, 171, 8721, 197676, 2372112, 16604784, 71954064, 200443464,
    367479684, 449141836, 367479684, 200443464, 71954064, 16604784, 2372112, 197676, 8721, 171, 1]
private def ptT18 : List ℤ := [-166912, -108544, -68608, -31744, -23552, -14848, -11264, -8192,
    -7168, -5120, -4096, -3584, -3072, -2432, -2048, -1728, -1536, -1280, -1024, -896, -768, -640,
    -512, -448, -384, -320, -256, -224, -192, -144, -128, -80, -64, -40, -32, -12, 0]

private theorem bmInterlace_18 : BMInterlace 18 :=
  bmInterlace_of_check 18 (by norm_num) cmT18 cnT18 ptT18 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `16^n L(d(19))_i`. -/
private def cmT19 : List ℤ := [3142016587135529283190961217960000,
    442083421987000122354645467589280000, 19697590446111460182154529394572160000,
    408717982363506019455200082891394560000, 4661939206520974408551495261220003840000,
    32014485506344700892242010422182871040000, 139930830720782214763106255223639244800000,
    403382394771371601215653678701559152640000, 784475287982863841317316003159031152640000,
    1042904444025735586510389658336509296640000, 953145810543881342238435450460003368960000,
    598120595781083971270324799474698813440000, 255609753746054699991555147786816061440000,
    73206638121907897133174912970066493440000, 13690857352253155185275659878232227840000,
    1606760663279451955620163616684113920000, 111323738672318139139917877094645760000,
    4126891034510068592078454584770560000, 68640871373904027273178707394560000,
    343401580750356489755280015360000]
private def cnT19 : List ℤ := [1, 190, 10830, 276165, 3755844, 30046752, 150233760, 488259720,
    1057896060, 1551580888, 1551580888, 1057896060, 488259720, 150233760, 30046752, 3755844, 276165,
    10830, 190, 1]
private def ptT19 : List ℤ := [-184320, -119808, -75776, -34816, -25600, -16384, -12288, -9216,
    -7168, -5888, -5120, -3840, -3072, -2816, -2048, -1920, -1536, -1408, -1280, -1088, -896, -768,
    -640, -576, -512, -416, -384, -288, -256, -192, -160, -128, -96, -80, -64, -32, -16, -12, 0]

private theorem bmInterlace_19 : BMInterlace 19 :=
  bmInterlace_of_check 19 (by norm_num) cmT19 cnT19 ptT19 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `16^n L(d(20))_i`. -/
private def cmT20 : List ℤ := [196093255203128382563947889612883600,
    30712718882661769430125727345013700800, 1527460302971934605406007245399068793600,
    35529412169258916987217522452721024665600, 456840651359061780815476909496948481331200,
    3560563184615311337334526303104986544537600, 17804214241067874976092069694195194475315200,
    59266003387459244720368963408340693837414400, 134545122968961029543604887992895214216806400,
    211486077086511873703088466805576274804736000, 232025425427043329695735126396944261316608000,
    178009419873694921723407425103603417533644800, 95114502228205698498222562550737963214438400,
    35030933513280562593835073895892798301798400, 8736635559617164268376406472677102977024000,
    1435672275340023307785923116065924474470400, 149223327246762754974062824693894112870400,
    9220764199326830996118305802682997145600, 306758691006858260908333296000801177600,
    4604397075016929885936745501949952000, 20892552172851688836711236134502400]
private def cnT20 : List ℤ := [1, 210, 13300, 379050, 5799465, 52581816, 300467520, 1126753200,
    2848181700, 4936848280, 5924217936, 4936848280, 2848181700, 1126753200, 300467520, 52581816,
    5799465, 379050, 13300, 210, 1]
private def ptT20 : List ℤ := [-201728, -131072, -83968, -38912, -27648, -18432, -14336, -10240,
    -8192, -6400, -5120, -4352, -4096, -3072, -2560, -2176, -2048, -1664, -1536, -1216, -1024, -896,
    -768, -704, -640, -512, -448, -384, -320, -256, -224, -192, -128, -112, -96, -64, -48, -32, -16,
    -10, 0]

private theorem bmInterlace_20 : BMInterlace 20 :=
  bmInterlace_of_check 20 (by norm_num) cmT20 cnT20 ptT20 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `16^n L(d(21))_i`. -/
private def cmT21 : List ℤ := [12252938186796838344517342508327937600,
    2125070224157953637146426497171131289600, 117318397982975047534776305413976000640000,
    3040791666688541307989442508753466350080000, 43784277139560365368515105262633643673600000,
    384435457318409939559992410200249362974310400, 2180821032926018856519241735263998295303782400,
    8302704720265900501444989441073958591397888000, 21760987593436513569040031024906796607733760000,
    39923995999337652126624338531246147050143744000,
    51783798036704135177285599133096068299463065600,
    47687946650619901275508065722333314844039577600,
    31150588690920860606428305537075392714637312000,
    14343911689043395280614035157837356686376960000, 4600205922126916871208471173373629470605312000,
    1008065776350086991499032396704379622234521600, 146707136700019069427833498179694740740505600,
    13599357636784797794710557045969093918720000, 754113696984332956442172183199120097280000,
    22640054270129817926610013349121884160000, 308210909187655323564656862358300262400,
    1274208805535190528236248088602214400]
private def cnT21 : List ℤ := [1, 231, 16170, 512050, 8756055, 89311761, 578399976, 2478857040,
    7229999700, 14620666060, 20734762776, 20734762776, 14620666060, 7229999700, 2478857040,
    578399976, 89311761, 8756055, 512050, 16170, 231, 1]
private def ptT21 : List ℤ := [-221184, -143360, -92160, -41984, -30720, -19456, -15360, -11264,
    -9216, -7168, -6144, -4864, -4096, -3456, -3072, -2560, -2048, -1856, -1536, -1408, -1280,
    -1088, -896, -832, -768, -608, -512, -448, -384, -320, -256, -224, -192, -160, -128, -96, -80,
    -64, -48, -32, -16, -8, 0]

private theorem bmInterlace_21 : BMInterlace 21 :=
  bmInterlace_of_check 21 (by norm_num) cmT21 cnT21 ptT21 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `16^n L(d(22))_i`. -/
private def cmT22 : List ℤ := [766466852362522887848361697896976526400,
    146498384332994606150432391106498233619200, 8932926124176157096987695370164306879897600,
    256608569940026148356432097224198546611200000, 4113208250143913464933600079904878600030208000,
    40417783266122825119184963070518627750893977600,
    258194068510181678465784150176939640318020812800,
    1114863876376221435530841820396735388727666278400,
    3341313942288760344236712144305256813625344000000,
    7076399860145904659328914625667493090499231744000,
    10712042236378289873986147196567019482413164134400,
    11661705277731809537193800437706411925163946803200,
    9143307852123392317317506170336057634156288409600,
    5146834234398997095831155940301215233118044160000,
    2063629411669891231057257315448763848071315456000,
    581498830832941262182202018020590519107085926400,
    112850190940885389279933434384278999562138419200,
    14646798040807843533296740983756900749908377600, 1218405049947557385590963298959967167447040000,
    60969896593693402943214381956861496655872000, 1660145857328173866367142886450461776281600,
    20591445971776958061848357520555166924800, 77884696906927844188721412093404774400]
private def cnT22 : List ℤ := [1, 253, 19481, 681835, 12954865, 147685461, 1075994073, 5226256926,
    17420856420, 40648664980, 67255063876, 79483257308, 67255063876, 40648664980, 17420856420,
    5226256926, 1075994073, 147685461, 12954865, 681835, 19481, 253, 1]
private def ptT22 : List ℤ := [-240640, -156672, -100352, -46080, -33792, -21504, -16384, -12288,
    -10240, -7680, -6144, -5376, -4096, -3840, -3072, -2816, -2560, -2048, -1792, -1536, -1280,
    -1216, -1024, -896, -768, -704, -640, -544, -512, -416, -384, -288, -256, -224, -192, -144,
    -128, -96, -64, -56, -32, -24, -16, -8, 0]

private theorem bmInterlace_22 : BMInterlace 22 :=
  bmInterlace_of_check 22 (by norm_num) cmT22 cnT22 ptT22 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `16^n L(d(23))_i`. -/
private def cmT23 : List ℤ := [47993285477610979465196848546577411078400,
    10065579479647243376995324221699059137382400, 674826470002088581984052975627323918252032000,
    21379782123028498593895417132128885381304320000,
    379464375062555520081472709886709693240713216000,
    4148450443025528267555541899007832116865931673600,
    29646891893738577354360978474175450764732766617600,
    144118377566285504259276990396466489693880451072000,
    489793210157084641471888055868667811856730030080000,
    1186010764483861852993351005986364903738335821824000,
    2072275707966635226285130462512558566676491560550400,
    2632733466779369952637686562763641112268181497446400,
    2440057113813312480859749084508549500513583890432000,
    1648551059368566402853178323452074768702310973440000,
    808007048224684762196580803570262929200946085888000,
    284644442847183457499763130739947454348587853414400,
    71031735903520335017603304109278477709620962918400,
    12293521456658975305456543235886157637829525504000,
    1431832605635133150426936615768174364805038080000,
    107483381787734404080816087944885291326636032000,
    4878101329940940659384150277542991093143961600, 121017424766477606223790033708600784427417600,
    1373276521027631214447568759146059661312000, 4770253647985750759384827508178288640000]
private def cnT23 : List ℤ := [1, 276, 23276, 896126, 18818646, 238369516, 1941008916, 10606227291,
    40067969766, 106847919376, 203982391536, 281248448936, 281248448936, 203982391536, 106847919376,
    40067969766, 10606227291, 1941008916, 238369516, 18818646, 896126, 23276, 276, 1]
private def ptT23 : List ℤ := [-261120, -169984, -108544, -50176, -36864, -23552, -18432, -13312,
    -11264, -8704, -7168, -5888, -5120, -4096, -3584, -3072, -2560, -2304, -2048, -1792, -1536,
    -1344, -1280, -1088, -896, -832, -768, -640, -512, -480, -448, -384, -320, -272, -256, -192,
    -160, -128, -112, -96, -64, -48, -32, -24, -16, -8, 0]

private theorem bmInterlace_23 : BMInterlace 23 :=
  bmInterlace_of_check 23 (by norm_num) cmT23 cnT23 ptT23 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `16^n L(d(24))_i`. -/
private def cmT24 : List ℤ := [3007912509968327011620844153700424548490000,
    689469379612310517786280885059264390790320000, 50612389952494550448437530926942727180172160000,
    1760641209374655561839169585879884865514824960000,
    34434771888686863221684941679803219183910535680000,
    416608205175287109992143274883306566143183349760000,
    3311188092160664409713805801055973758442540851200000,
    18002578604772110041144358990567022922195857408000000,
    68867900725733989241720089964636972617368403968000000,
    189075981467110774132666534634832165875616212582400000,
    377690645628670889810099479489484998812085612707840000,
    553815006066502046215050490294715104962806934405120000,
    598969286228724890853153408490847441626403061104640000,
    478344745473028869715750177263270053123164093808640000,
    281387808929343277776597590356061853401375016222720000,
    121172145701809635414634479328611553124064417546240000,
    37801915617134021905186505431485487158875966668800000,
    8412526810745598260175843518248356969285943296000000,
    1306530898608250838722377874293523698545590272000000,
    137318966711016005364906921363151826246959104000000,
    9348909739682949359558563089747265832154562560000,
    386574377314143042077634930394764442840596480000,
    8773976885333053085432303468756078438645760000, 91437016966865534847681604481346133032960000,
    292708064122236761874474554599051100160000]
private def cnT24 : List ℤ := [1, 300, 27600, 1163800, 26883780, 376372920, 3405278800, 20796524100,
    88385227425, 267119798440, 582806832960, 927192688800, 1081724803600, 927192688800,
    582806832960, 267119798440, 88385227425, 20796524100, 3405278800, 376372920, 26883780, 1163800,
    27600, 300, 1]
private def ptT24 : List ℤ := [-282624, -184320, -117760, -54272, -39936, -25600, -20480, -14336,
    -12288, -9216, -8192, -6400, -5120, -4608, -4096, -3328, -3072, -2560, -2048, -1920, -1792,
    -1536, -1280, -1216, -1024, -960, -768, -736, -640, -576, -512, -448, -384, -320, -288, -256,
    -192, -176, -160, -128, -96, -80, -64, -48, -32, -24, -16, -6, 0]

private theorem bmInterlace_24 : BMInterlace 24 :=
  bmInterlace_of_check 24 (by norm_num) cmT24 cnT24 ptT24 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `16^n L(d(25))_i`. -/
private def cmT25 : List ℤ := [188675523265277267461733718722674310398403136,
    47094500297056794776729033747268262429381678848,
    3770917696456001206174737595622475374147592781824,
    143449900823824705071047566650617969888498040889344,
    3078051463457557562635699636629264375310307357048832,
    41014198027302765444711938536293758010784508690694144,
    360621817863484347719135462105406812535260341480980480,
    2180019644719801511496845268208234471031756596130611200,
    9325657100107836245137297786723228998666433064022835200,
    28816065721190519430169947779824951796866528941818511360,
    65258818784689972465310855923675565627271287045646974976,
    109390438018034553943781924254706246250143648047712698368,
    136541882930043506656852282743703648782563785076266500096,
    127242324355730624376058225431568858440118544250276151296,
    88474084158436043121985777969064608684779650309400035328,
    45725033196560294363472390043704733648111268096970326016,
    17436768410472132843693930923185777858031233276890316800,
    4851014366827384383172059021634915791124057375427788800,
    968742710719743923561039974313006788716580655490662400,
    135766136796631790055118354176045001387639340751912960,
    12941343542401333844367289055840408973162904723390464,
    802728644852461990892848301535472123937385854533632,
    30367152837712117854607106123665588496478832164864,
    632965873710089219530591132812592094383957868544,
    6079007908980872628490987465841829096298905600, 17991476786111755910671703183163435301994496]
private def cnT25 : List ℤ := [1, 325, 32500, 1495000, 37823500, 582481900, 5824819000, 39525557500,
    187746398125, 638337753625, 1578435172600, 2869882132000, 3863302870000, 3863302870000,
    2869882132000, 1578435172600, 638337753625, 187746398125, 39525557500, 5824819000, 582481900,
    37823500, 1495000, 32500, 325, 1]
private def ptT25 : List ℤ := [-304128, -198656, -128000, -58368, -43008, -27648, -21504, -15872,
    -13312, -10240, -8192, -6912, -6144, -4992, -4096, -3712, -3072, -2816, -2560, -2176, -2048,
    -1664, -1536, -1344, -1280, -1056, -896, -832, -768, -640, -576, -512, -448, -384, -320, -304,
    -256, -224, -192, -160, -128, -112, -96, -80, -64, -48, -32, -20, -16, -6, 0]

private theorem bmInterlace_25 : BMInterlace 25 :=
  bmInterlace_of_check 25 (by norm_num) cmT25 cnT25 ptT25 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `16^n L(d(26))_i`. -/
private def cmT26 : List ℤ := [11844133883558145150896645100170720467554194496,
    3208487998067074121832216649060521063358593401856,
    279248652916973011526256849987174569491169915950080,
    11573539404589892332712495391634519620828721259212800,
    271360867157210755153571811439530432417782666727997440,
    3964923412676955668996300891557388615331522936743460864,
    38382422267493269848312534014389455860435288503063937024,
    256626062259513345711771203328790090452215024094522900480,
    1220409632660553792596912584238254247088479962550973235200,
    4216441075113397846502012064828235518852645650107528642560,
    10746031493709379816015612473357505097022276260707933618176,
    20420396538290465688807407871914166353730888704229340348416,
    29136696097552466492062443891819235364143206595113233940480,
    31335418332965997002001522643541773308565074555751209369600,
    25423515743634328240938654171254855583695146436183740907520,
    15530407187876813277719789187768300718127346729729713504256,
    7107655515214242979751342634617519394632083996877537673216,
    2417055427830855959528611361996450335242752249432490639360,
    603407038531757841269551269817702495448198983045034803200,
    108735412434211649104367620130540154540016453283406151680,
    13820598058082339991102838592831832045732386793024651264,
    1200245524328458292062951955415616012115692981063778304,
    68111372329365920701384162361671198784596126602362880,
    2366274386605840706747778865063006904131664845209600,
    45453349307054866990994964491799885409088585072640,
    403587575185564464242943133759058051992079302656,
    1107593635992347387542179881169422372082548736]
private def cnT26 : List ℤ := [1, 351, 38025, 1901250, 52474500, 885069900, 9735768900, 73018266750,
    385374185625, 1464421905375, 4073755482225, 8394405236100, 12914469594000, 14901311070000,
    12914469594000, 8394405236100, 4073755482225, 1464421905375, 385374185625, 73018266750,
    9735768900, 885069900, 52474500, 1901250, 38025, 351, 1]
private def ptT26 : List ℤ := [-327680, -214016, -137216, -63488, -46080, -29696, -23552, -16896,
    -14336, -10752, -9216, -7424, -6144, -5376, -5120, -4096, -3584, -3072, -2560, -2432, -2048,
    -1856, -1536, -1472, -1280, -1152, -1024, -960, -896, -768, -640, -576, -512, -480, -384, -352,
    -320, -288, -256, -208, -192, -160, -128, -112, -96, -64, -48, -40, -32, -20, -16, -6, 0]

private theorem bmInterlace_26 : BMInterlace 26 :=
  bmInterlace_of_check 26 (by norm_num) cmT26 cnT26 ptT26 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `16^n L(d(27))_i`. -/
private def cmT27 : List ℤ := [744052064926514149973199943768749402650359247104,
    218067442882246602014704204187798724632324141939712,
    20563224650298316447281833742007002438567724707393536,
    925336847918970627660905209818142592702259511705600000,
    23620397970397499583048331320115399726934417259712020480,
    376938309172736873311516864213129131873210058908427616256,
    3999952859708359092091925626782897316280293120605650157568,
    29437749103538362216555794460097324809893625851371904303104,
    154810248954855425123641376329232967395067003385992445952000,
    594532281756451327564496171760154731674953777826817208483840,
    1694046407812045265445863677445693486326539507138695459241984,
    3622519278700362768518331797364599913791085173922787284221952,
    5859237024086534361751339877268433368389767870754081898233856,
    7202925641501886762283489018258183864498569251925482117529600,
    6744117166404343812962112373417186346317185056924564308623360,
    4807033994089552128969877417722287744344011298136143360425984,
    2600286778500438328598803318493740854286811535762668862308352,
    1061221054359699291132098827700429669898814653459170649440256,
    323830194637141407442675367345943749557435609869843850854400,
    72949256802543153923870955049195933288030948799246206238720,
    11922027793011039021349152903616472016033236260046363426816,
    1380567848538716243889093875620467997174288785556004405248,
    109687746971551134670688533868876461234303100559235743744,
    5716302442450575916219242360165855790773817804062720000,
    183013439415159284550036500781271504543099651725721600,
    3250134222744845433663099742862515832526696133689344,
    26759626333521185823372775881628232572088019320832,
    68284894891687326455001004909847076942219575296]
private def cnT27 : List ℤ := [1, 378, 44226, 2395575, 71867250, 1322357400, 15931258200,
    131432880150, 766691800875, 3237143159250, 10064572367850, 23331508670925, 40680579221100,
    53644719852000, 53644719852000, 40680579221100, 23331508670925, 10064572367850, 3237143159250,
    766691800875, 131432880150, 15931258200, 1322357400, 71867250, 2395575, 44226, 378, 1]
private def ptT27 : List ℤ := [-351232, -229376, -147456, -67584, -50176, -31744, -24576, -18432,
    -15360, -11776, -10240, -8192, -7168, -5888, -5120, -4352, -4096, -3328, -3072, -2560, -2304,
    -2048, -1792, -1664, -1536, -1280, -1152, -1056, -896, -832, -768, -672, -640, -544, -512, -416,
    -384, -320, -288, -256, -224, -192, -160, -144, -128, -96, -80, -64, -48, -40, -32, -16, -8, -6,
    0]

private theorem bmInterlace_27 : BMInterlace 27 :=
  bmInterlace_of_check 27 (by norm_num) cmT27 cnT27 ptT27 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `16^n L(d(28))_i`. -/
private def cmT28 : List ℤ := [46772783122242759397039778097830415255383042263104,
    14788268535744143830844827465023900372338511329942784,
    1506355473574322674971299612625981243864241091326233600,
    73366081994781808545860738893000671452324058309473587200,
    2031970526873396227994498389168819399639641469203251200000,
    35286318701742891686491747389501725569205756081915440398336,
    408836470885118280939524438166054552375368797051124151484416,
    3297547764521175472850494075290230595614705945454985735045120,
    19085332859845168447674017387613846933651095805435148920422400,
    81043167122138977524361748743886590196703315410203932843048960,
    256664020386131627475561155447780057291652224659146805790900224,
    613579012875793102995974207630788209362422833363049689020104704,
    1116731796532950621059764446899079894451861544048013383439482880,
    1556160197736926232407908162608473788947342322931633154844262400,
    1665443574091537877788612445649236495683191654770155716272455680,
    1369895520441228800952335086918216161560904011934099507505004544,
    864624846823362570930153670692636828492193712120532153195823104,
    417066926459855177810911354082462080022635543807698050167603200,
    152733998851312449198835858653058297927479383924542104875827200,
    42055427841229963088158920591444294532170520478638354412339200,
    8591916852452888136934386012294957075700216317281067111284736,
    1279285864700431203622516957419880458698041953865030032162816,
    135528092184439629313143857155851805035656064279805060710400,
    9888596407104704789691993861801753184914892143187722240000,
    474910549298659495158890939279989859086025983586520268800,
    14057082395606524279214952195075123363400784369831378944,
    231482767111630507035888374973565758849332695472799744,
    1772139347214054022921108222421052747529759878021120,
    4215547082599064541354653874536477709188045209600]
private def cnT28 : List ℤ := [1, 406, 51156, 2992626, 97260345, 1945206900, 25565576400,
    231003243900, 1482270815025, 6917263803450, 23896002230100, 61912369414350, 121443493851225,
    181497968832600, 207426250094400, 181497968832600, 121443493851225, 61912369414350,
    23896002230100, 6917263803450, 1482270815025, 231003243900, 25565576400, 1945206900, 97260345,
    2992626, 51156, 406, 1]
private def ptT28 : List ℤ := [-375808, -245760, -157696, -72704, -53248, -34816, -26624, -19456,
    -16384, -12800, -10240, -8704, -7168, -6400, -5120, -4736, -4096, -3584, -3072, -2816, -2560,
    -2240, -2048, -1792, -1536, -1472, -1280, -1152, -1024, -960, -896, -768, -640, -608, -512,
    -480, -448, -384, -352, -320, -256, -240, -192, -176, -160, -128, -112, -96, -80, -64, -48, -32,
    -24, -16, -8, -5, 0]

private theorem bmInterlace_28 : BMInterlace 28 :=
  bmInterlace_of_check 28 (by norm_num) cmT28 cnT28 ptT28 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `16^n L(d(29))_i`. -/
private def cmT29 : List ℤ := [2942069235632154544712728015903958343650134287417600,
    1000801238275530197770418766806349621321519052484044800,
    109814765258012492892007220044875400479338202176889753600,
    5771848861466260052860176787694459041095818493092428185600,
    172907140881016231780901802668191184057176610380659897139200,
    3256454478788296950342488259950634737580268925797394389401600,
    41045212333380764183748079031204292015535422792291318969139200,
    361385244087082156689900023019439966027904777203173602780774400,
    2291948419150191169796369559511351815607308191887750213297766400,
    10709936534839015581474589772705870656544194334254750066802688000,
    37500804192965230196156542261054854752086138094982121069215744000,
    99636309860202555206328379110192970664031118159923653387275468800,
    202719330304420835978558327867805593904694940151360229046904422400,
    317857301742123541264821784218269804847799425203205949916341862400,
    385595832665463001223136859663056128011499138072690057621274624000,
    362525711209785773438594584049561103954157483204678541153560166400,
    264043807179583294419878711387346401952310954671688004397327974400,
    148608355672427355149095390716634200095748084314427072603330969600,
    64322189095642127827884108019999620554274539813308965156657561600,
    21254983645008792821220364297456537977114333512727492191846400000,
    5307713705937099396994936232208830584535940964280236136359526400,
    987916635495305051709758389638483965840538697372571189379072000,
    134570219705145945004818399924280089922233496765302508093440000,
    13092214071947419136639295517032101978323648325384342077440000,
    880311348791089850018995462629045333929713710049196507136000,
    39086531990033713240487146241921140613345101339067783577600,
    1072788232538813934727675146732852246030048001811860684800,
    16426175744267420833259041402355599072192238201497190400,
    117226514727684800430064884550541342685750704367206400,
    260571937624054424634697178375629318947005163110400]
private def cnT29 : List ℤ := [1, 435, 58870, 3708810, 130179231, 2820550005, 40293571500,
    397179490500, 2791289197125, 14328617878575, 54709268263650, 157496378334750, 345280521733875,
    580526591486625, 751920156592200, 751920156592200, 580526591486625, 345280521733875,
    157496378334750, 54709268263650, 14328617878575, 2791289197125, 397179490500, 40293571500,
    2820550005, 130179231, 3708810, 58870, 435, 1]
private def ptT29 : List ℤ := [-401408, -263168, -168960, -77824, -57344, -36864, -28672, -20992,
    -17408, -13824, -11264, -9472, -8192, -6912, -6144, -5120, -4096, -3968, -3584, -3072, -2560,
    -2432, -2048, -1920, -1792, -1600, -1536, -1280, -1152, -1056, -896, -864, -768, -704, -640,
    -576, -512, -448, -384, -352, -320, -288, -256, -224, -192, -160, -144, -128, -96, -80, -64,
    -56, -48, -32, -24, -16, -8, -5, 0]

private theorem bmInterlace_29 : BMInterlace 29 :=
  bmInterlace_of_check 29 (by norm_num) cmT29 cnT29 ptT29 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `16^n L(d(30))_i`. -/
private def cmT30 : List ℤ := [185167299759053068923008628592070907130798007307202816,
    67599482595263126830443155692080677621328437866579166208,
    7969579718776834233324138779547326499942314492135588560896,
    450810202905466449164625542172748868428073735195519980404736,
    14564952634798454824435861213631237901288164129491941640372224,
    296574476524260287547610063749236497060552036471576822340911104,
    4052916036402636396745096181291658238377852634253702946587934720,
    38811498157927576936991796679033242191559403754893271558504054784,
    268656348677520437561112770110758701606906680717578467792633462784,
    1375491580514486935681855355459296403208285585713119799385379569664,
    5299585634683100258429910496811293057112240354862167756190573920256,
    15566729826172358232247421111222606495210548026763137287447572905984,
    35198637722490999233946535857063042473845585244276175379906013691904,
    61694416667102369909583635190821899216654031817598612558304514146304,
    84210211218761220761448451461836773192520321353616590405639700742144,
    89739864826089013666978143261726189153652479766106392315692425674752,
    74707313866991799668217407143111389020852203237934509408454700957696,
    48519950172530739411693202178145874360452684488422933944520698494976,
    24503120221266954470415347681006375674636665386681239970491270168576,
    9569828577907245678759657395475368293760733560280206118606996504576,
    2867876497391785345352737085217994982490230789459280411214353530880,
    652451925361337164228681231722688009310873259092703884702698700800,
    111098837112080107942284727519307136061950675811619697311770214400,
    13897544124403527290916598671881449896038846345245626875668070400,
    1245999561887995096584923073222213700945891454458747425537392640,
    77455608196411375196542611717365221019689535894715056642850816,
    3188934061442357185548851254146322418380028327168833285521408,
    81382296196818303201026533721036860561647640126656058753024,
    1161612589643183355021473255764147287963431353277170581504,
    7746317304612906476130229011707825144232429089634385920,
    16125349597677039149393437829787833942302666182885376]
private def cnT30 : List ℤ := [1, 465, 67425, 4562425, 172459665, 4035556161, 62455035825,
    669161098125, 5130235085625, 28843321703625, 121141951155225, 385451662766625, 938920716995625,
    1764345523145625, 2570903476583625, 2913690606794775, 2570903476583625, 1764345523145625,
    938920716995625, 385451662766625, 121141951155225, 28843321703625, 5130235085625, 669161098125,
    62455035825, 4035556161, 172459665, 4562425, 67425, 465, 1]
private def ptT30 : List ℤ := [-428032, -280576, -180224, -82944, -60416, -38912, -30720, -22528,
    -18432, -14336, -12288, -9984, -8192, -7296, -6144, -5504, -5120, -4224, -4096, -3328, -3072,
    -2688, -2560, -2176, -2048, -1728, -1536, -1408, -1280, -1152, -1024, -960, -896, -768, -704,
    -640, -576, -512, -448, -416, -384, -336, -320, -256, -224, -208, -192, -160, -128, -112, -96,
    -80, -64, -48, -40, -32, -24, -16, -8, -4, 0]

private theorem bmInterlace_30 : BMInterlace 30 :=
  bmInterlace_of_check 30 (by norm_num) cmT30 cnT30 ptT30 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `16^n L(d(31))_i`. -/
private def cmT31 : List ℤ := [11660337473692877751243278010278629569123176077214032896,
    4557838855820120170428899873997513485791776442431743164416,
    575945758044193224569374987998048624369164317387869498900480,
    34973816573825179093332378176630976056507374916256078023884800,
    1215365069436408151917476051193407528280390135112086897169530880,
    26679230829613966608433608754033122023411905043643991187653656576,
    394073811695602256230015090062497636648087510992201468096655917056,
    4090724006433672667548959558283149707665599580994861603469289062400,
    30793519689918817567611098720690637968898142559497490773070315520000,
    172058656575443057477470513392785114517940528696556909393206050816000,
    726281363714058503725789109171258963523160113844595434786618186137600,
    2347277745563377377080982726695240019253972351220475437336957131161600,
    5867472993341587610887683939667685480856811669257733895155290734592000,
    11428944511992433682028131040267950857514248302195330319994092257280000,
    17437945757118689419303276831884315805097989399268249154981174706176000,
    20908579142762731045190878103130402460078817035151523379581022529126400,
    19729136908528580719436422766805926242369049755709453275410219820646400,
    14645324731360328276269757057110120700188369779456255182402198962176000,
    8534623187981575770687060553956024979773589848806903224917169274880000,
    3889070540582234793615369382891791735350657328064311128039884849152000,
    1377466054889072507176321175308696748503513058330977851700871272857600,
    376075588485686262308049828710653262381362261886147409109533170073600,
    78272371426864343805015470372474865102449039575710655064326537216000,
    12239590027689865605280010607993897076330260755309806404470046720000,
    1410941306936757075853235961687326390365768285604824294061663846400,
    116949581754805884263988356638344914946683487546230064785639079936,
    6741147725902803323448451777794742132886445742262061417476653056,
    258061141979956164197235914399215742412393140195584514489057280,
    6139240625887328175106167636403059053457123178139771260108800,
    81882197988156502389647114424678435094467020387320206458880,
    511369167131804933510616235095371117440746318077620125696,
    998999806084599586678759328443546807064444884354072576]
private def cnT31 : List ℤ := [1, 496, 76880, 5573800, 226296280, 5702666256, 95315993136,
    1106346348900, 9219552907500, 56546591166000, 260114319363600, 910400117772600,
    2451077240157000, 5117633798130000, 8334432185526000, 10626401036545650, 10626401036545650,
    8334432185526000, 5117633798130000, 2451077240157000, 910400117772600, 260114319363600,
    56546591166000, 9219552907500, 1106346348900, 95315993136, 5702666256, 226296280, 5573800,
    76880, 496, 1]
private def ptT31 : List ℤ := [-454656, -297984, -191488, -88064, -64512, -41984, -32768, -24064,
    -19456, -15360, -13312, -10752, -9216, -7680, -7168, -5888, -5120, -4608, -4096, -3584, -3072,
    -2816, -2560, -2304, -2048, -1920, -1792, -1536, -1408, -1280, -1152, -1056, -896, -864, -768,
    -704, -640, -576, -512, -480, -448, -384, -352, -320, -288, -256, -224, -192, -160, -144, -128,
    -112, -96, -80, -64, -48, -32, -28, -16, -14, -8, -4, 0]

private theorem bmInterlace_31 : BMInterlace 31 :=
  bmInterlace_of_check 31 (by norm_num) cmT31 cnT31 ptT31 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `16^n L(d(32))_i`. -/
private def cmT32 : List ℤ := [734646809035907911132042308702281313751514480271035689764,
    306792262918442385267777067700261450652185041252874453515392,
    41458807438872465830111955096126328683173424927650842093694976,
    2696209116711974052105406990502449180398680159588320538240409600,
    100525679886580075541197677916471161103627035558754594528490373120,
    2372595828472726412771352020065524533341766781797137324412659236864,
    37770444319573006261718943845277809304948284695448247936606048878592,
    423702738801705453271834593073219963084889903150629242437850616037376,
    3456920995132145838217226922680766851281471933680134515340394233856000,
    21003141607369296935118654655933969054235944761654989119683264774144000,
    96746514823420467488699740588269467518282549647960164698048088663654400,
    342541815786845314001491038077144563804266945547796886255092727231283200,
    942072625291523934817733607905356295735465131132899609429853307771289600,
    2028532066847988974768395060201378145857945920585356901463830005022720000,
    3439486394997224080855333561669596889815701779985447152800550663225344000,
    4609809933421554695234080960043360781548670741190164797598614016334233600,
    4894033218730073930056189538038122053561175713482150008673917542911180800,
    4117721055508830561162432003605436449619165839935664318476176633259622400,
    2742649719682762055140468274038688169700940321210588201677710509998080000,
    1442153239944893549974687279140503161600461195979601951609834352672768000,
    595965647287569535035187436180608493339725254629747696979636755261030400,
    192305139636906221463279049026357813535769525827395198081297129091891200,
    48031651924349592178994676783075854090986648492045409102720457611673600,
    9180276795326983616406433822471865920889509121008060297019129856000000,
    1322895504654100233103923067602183586257189136841644791247408830873600,
    140985890738495679627608929439423037922546752924411015314438067585024,
    10835873950406572075927117282955144661233208581466731290946722332672,
    580756113259684055187641235192053499552267974212083946666711842816,
    20724733110351227720754649378605610098644722173200714205600153600,
    460705443271509977947672411218883963828523802335738141469573120,
    5754508955425534054609673133811052612115173683627290676690944,
    33726358328391842621223249773170195649846542351404034424832,
    61953597349215246242624933978006832456855964781270532096]
private def cnT32 : List ℤ := [1, 528, 87296, 6765440, 294296640, 7965629056, 143381323008,
    1797387299136, 16226413117200, 108176087448000, 542847275193600, 2080914554908800,
    6162708489537600, 14221634975856000, 25734387099168000, 36671501616314400, 41255439318353700,
    36671501616314400, 25734387099168000, 14221634975856000, 6162708489537600, 2080914554908800,
    542847275193600, 108176087448000, 16226413117200, 1797387299136, 143381323008, 7965629056,
    294296640, 6765440, 87296, 528, 1]
private def ptT32 : List ℤ := [-483328, -317440, -203776, -94208, -68608, -44032, -34816, -25600,
    -20480, -16384, -14336, -11520, -10240, -8448, -7168, -6272, -5120, -4864, -4096, -3840, -3584,
    -3072, -2560, -2496, -2304, -2048, -1792, -1664, -1536, -1408, -1280, -1152, -1024, -960, -896,
    -800, -768, -640, -576, -544, -512, -448, -384, -352, -320, -288, -256, -224, -192, -176, -160,
    -128, -112, -96, -80, -72, -64, -48, -32, -24, -16, -12, -8, -4, 0]

private theorem bmInterlace_32 : BMInterlace 32 :=
  bmInterlace_of_check 32 (by norm_num) cmT32 cnT32 ptT32 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `16^n L(d(33))_i`. -/
private def cmT33 : List ℤ := [46307709420992527687555474966537556015756620738039461788944,
    20617920898397013899036160428431542814438056414676525492075584,
    2973361472099792667462390673523803613276291277126998053511065600,
    206632255043282305137336054646807610454110895383590805748702412800,
    8246410251978020649661198406563952684775178939491513592095606374400,
    208742115363781230077074410870525804195929802891896445536568175755264,
    3571946629811121953602745275732416901768067975001119626488263212007424,
    43177440568832997972304224752320591327634847588675858539850640769679360,
    380638300491740504702713414134446584436356808869077283937406067566182400,
    2506296905379076534711597064325340955664116776904932344748043920841113600,
    12552441628728201743332132922321017434770413634140723850717872014124646400,
    48495777907540583442457287520932069364948394629688770946987412563584614400,
    146107932058540341252687347017656569613802329254454147113400732129165312000,
    346130611247168951759507715750507048104236649551714365186803391969361920000,
    648756720866566224483883000985308012313919341754368359809314086855901184000,
    966237444857595993069388736374224797807593041483937995757624839330437529600,
    1146620928532278776811249395305196855288707690443991261077723529797540249600,
    1085434235416292937833962770866952595307420494442268691462528977120264192000,
    819427379064066993922817781755872432807210474248619077305192393086074880000,
    492464530252759111090953769641271129267396332096297611136827856745660416000,
    234833709808842011006825539353234664280139285032664765096182178807965286400,
    88410021536724004722387935978639469212801847026943260629970002387560038400,
    26098208644176771664668861536119129353948946384682364149486410147037184000,
    5986042265910885598923663166983852526457807668499013726627273784688640000,
    1054331770190617862374783862827703511839246077300974144956179304310374400,
    140460188615063015063459521386154469577978103412757586784070488769429504,
    13880346721128857997142522224543271135349900733343112710914207953977344,
    991931923660251064256743838934094693564423211605371989788610422374400,
    49558351857264100826185301735673768830247510374126584489705262284800,
    1652544896425643843180437926902128242722158880895426238311143833600,
    34403036709883657414189554720766389102805002463164142970883538944,
    403270979136703221213678328310551770681290278539546449783291904,
    2222406953638000733245289222560149337144756181477952438927360,
    3845788044818136497705643284585180784282335371178960486400]
private def cnT33 : List ℤ := [1, 561, 98736, 8162176, 379541184, 11006694336, 212796090496,
    2872747221696, 28009285411536, 202289283527760, 1103396091969600, 4614201839145600,
    14966577760305600, 37992082006929600, 75984164013859200, 120308259688610400, 151269944167296900,
    151269944167296900, 120308259688610400, 75984164013859200, 37992082006929600, 14966577760305600,
    4614201839145600, 1103396091969600, 202289283527760, 28009285411536, 2872747221696,
    212796090496, 11006694336, 379541184, 8162176, 98736, 561, 1]
private def ptT33 : List ℤ := [-512000, -335872, -216064, -99328, -72704, -47104, -36864, -27136,
    -22528, -17408, -14336, -12288, -10240, -8960, -8192, -6656, -6144, -5120, -4608, -4096, -3584,
    -3328, -3072, -2688, -2560, -2176, -2048, -1792, -1664, -1536, -1408, -1280, -1152, -1056, -896,
    -864, -768, -736, -640, -608, -576, -512, -448, -416, -384, -336, -320, -272, -256, -208, -192,
    -160, -144, -128, -112, -96, -80, -64, -48, -40, -32, -24, -16, -12, -8, -4, 0]

private theorem bmInterlace_33 : BMInterlace 33 :=
  bmInterlace_of_check 33 (by norm_num) cmT33 cnT33 ptT33 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `16^n L(d(34))_i`. -/
private def cmT34 : List ℤ := [2920269910718300405210029519948605392343129456577056024579600,
    1383571170423553810678554018536144659721862045094659442875792000,
    212506045967525276368731765786435178664552050432825297141773062400,
    15748296773676875022766890636547281392147373735008106868179402854400,
    671263092482814961142491910959824184702244143243885983175031070720000,
    18181362524015311097947638015374865688283538823871593452417871636070400,
    333587690696112224882137417161043873903168283453218848372158150108774400,
    4333608212512489899421287464858125943279931823299493269685843930487193600,
    41161422812027754530762559171317653873333946916232457794107174186752409600,
    292816144929635914949492102743146204279279495090414660536953336004975001600,
    1589218527301517976775867584932872355464463516774766966137318943636848640000,
    6675428926261908714598494050673184419369766602868763793162490719554764800000,
    21944576395487460848854635401364420354536800028775251924216274808209408000000,
    56947842185506252427153386006621439618896027562172860756888788861452288000000,
    117429090624932607995526434144806298156216978700948108819846732935960985600000,
    193329447430507357461179556020191550707361905306474799839326221736597258240000,
    254940339151060744463471840238463882629430258657183362104044903381409464320000,
    269753883193360883527781632675450339967128178387702680899797853676807127040000,
    229119895695198571275655404572415691296801033003625028528630587619687792640000,
    156068843811687221051056402569979955538916074187909180008802634011823308800000,
    85059186484857835977442331869942633864367075293273730102183274953991782400000,
    36951718475257614935531580797512478075214897431364578220048347286082682880000,
    12726600345093665467443521279429813503129227676612422507925953082703216640000,
    3449940640928765386964113763789809413987996365016883827893001575139901440000,
    729202013823026979607429265867510174065649152538888760411662060340903936000,
    118738000910849838063323164523295036138322681559296704672714283621652889600,
    14667667085966926463730755060360683784855874707708132213274755261792256000,
    1347720923331395566131799223710001841389995356564756717059576542160486400,
    89781205195475515704915717546464395851119031142791847371980405106278400,
    4191414224574485007902760313621802885452872499627790781831412973568000,
    130889600375503932122958224053701943690889387926139271281912473190400,
    2557190341366750368205749907259768333308138590959612530453276262400,
    28185640884550158759876982160694372133812923825037927377377689600,
    146324995974892789010174634002871615560466564712660756699545600,
    238944533331330307795164466498309709905099010120724617625600]
private def cnT34 : List ℤ := [1, 595, 111265, 9791320, 485649472, 15055133632, 311856339520,
    4521916923040, 47480127691920, 370344995996976, 2188402249073040, 9947282950332000,
    35198078131944000, 97858393048152000, 215288464705934400, 376754813235385200,
    526348636137670500, 588272005095043500, 526348636137670500, 376754813235385200,
    215288464705934400, 97858393048152000, 35198078131944000, 9947282950332000, 2188402249073040,
    370344995996976, 47480127691920, 4521916923040, 311856339520, 15055133632, 485649472, 9791320,
    111265, 595, 1]
private def ptT34 : List ℤ := [-541696, -355328, -229376, -105472, -77824, -50176, -38912, -28672,
    -23552, -18432, -15360, -12800, -11264, -9472, -8192, -7168, -6144, -5504, -5120, -4352, -4096,
    -3584, -3072, -2880, -2560, -2368, -2048, -1984, -1792, -1600, -1536, -1344, -1280, -1152,
    -1024, -960, -896, -800, -768, -672, -640, -576, -512, -464, -448, -384, -352, -320, -288, -256,
    -224, -208, -192, -160, -128, -120, -96, -88, -80, -64, -48, -40, -32, -24, -16, -12, -8, -3, 0]

private theorem bmInterlace_34 : BMInterlace 34 :=
  bmInterlace_of_check 34 (by norm_num) cmT34 cnT34 ptT34 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- `16^n L(d(35))_i`. -/
private def cmT35 : List ℤ := [184236848799961737564287282791598382972935850548654039023354944,
    92715397629541652789888324509464892799115698711434044000542833920,
    15138262591986229997447047356047338433426547962564793312710028266496,
    1193996337122947809988276768476280720348490042642016817874514546610176,
    54245377596438065813757778376614075469299118754646154492805334757277696,
    1568700284468029209703160064984026994669399718737163284624009151232606208,
    30789748462627125943062954255548708473857926459327131722034371646501945344,
    428803153961268584142702959253341969456426145680220607495241777507702145024,
    4376533738804649598089392015988000025443735753669981353606040381780240891904,
    33541172378435691388496582104655149882107565768435808316868762754844941352960,
    196661696113034906846822270026820015651853983382363435625420288697526864838656,
    895125447651383077880664882706400771561990656791505620012943060808851940966400,
    3199136623626446758713084581367584156910625436979982169937440300411356446720000,
    9058285922531713951077540870166951786599213616823357242427294184841433579520000,
    20460503274617970454126438617868318266399173028803116680852000827751366918144000,
    37058299548905594036103519162821104525314067476658335476302020100039747672473600,
    54017990980229455442089055795089018123535949016135954000344463513134933265612800,
    63513432446991597539996082264932403164993246061816631486792099311663374244249600,
    60297698502833338483485664549865825127033505896413922709315221685488307509657600,
    46210186992118626574324049803748695598893368770308474596179018946000675510681600,
    28544852846971870737284543195991511191588658107326054205892788603187469117030400,
    14172859292881673640300468027172410397674684678462823350330535459846346086809600,
    5632546622968177636624511470782994029082317334360158999059820117035063024025600,
    1781435743463373770513590824531972305985854431719440985977249228878174067097600,
    445014792508762459946610908100604641800157587678019341442397539318780773007360,
    86958737942092766888257482799855701796167893221660456210430153838255547613184,
    13129520742320783611662716180452718337500114408968711169271601116615215677440,
    1508032334814611008920674342306738824822045068023709508945619181428702969856,
    129167205157120791836507726295827120242707136459532553805896123340591988736,
    8040384257061250235111794889547097592748525631744609985639977551906471936,
    351527367565477541750043876954540377916832239646600926264072172405260288,
    10301898038231326468708842332569427806718242109218044255219958828498944,
    189251384171083905858293088274109858174073206630364780661480215281664,
    1965021143490444181461836567063268194798871849967357916757092204544,
    9626624666799301878201048330794358542337760931059195763427901440,
    14858643894732585736003631346918563642229242608127606916120576]
private def cnT35 : List ℤ := [1, 630, 124950, 11682825, 616853160, 20397277824, 451654008960,
    7016767639200, 79133546153200, 664721787686880, 4242133590510816, 20889294195697200,
    80343439214220000, 243679002451920000, 587150358288912000, 1130264439706155600,
    1745261267193328500, 2167317913508055000, 2167317913508055000, 1745261267193328500,
    1130264439706155600, 587150358288912000, 243679002451920000, 80343439214220000,
    20889294195697200, 4242133590510816, 664721787686880, 79133546153200, 7016767639200,
    451654008960, 20397277824, 616853160, 11682825, 124950, 630, 1]
private def ptT35 : List ℤ := [-572416, -375808, -241664, -111616, -81920, -53248, -40960, -30720,
    -24576, -19456, -16384, -13824, -12288, -9984, -9216, -7680, -7168, -5888, -5120, -4608, -4096,
    -3712, -3584, -3072, -2816, -2560, -2304, -2112, -2048, -1728, -1536, -1472, -1280, -1248,
    -1152, -1056, -960, -896, -768, -736, -640, -608, -576, -512, -448, -432, -384, -352, -320,
    -288, -256, -240, -224, -192, -160, -144, -128, -112, -96, -80, -64, -56, -48, -40, -32, -24,
    -16, -12, -8, -3, 0]

private theorem bmInterlace_35 : BMInterlace 35 :=
  bmInterlace_of_check 35 (by norm_num) cmT35 cnT35 ptT35 (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

/-- The interlacing data `BMInterlace n` holds for `1 ≤ n ≤ 35`, by kernel-checked
certificates. -/
theorem bmInterlace_small (n : ℕ) (hn : 1 ≤ n) (h35 : n ≤ 35) : BMInterlace n := by
  interval_cases n
  · exact bmInterlace_1
  · exact bmInterlace_2
  · exact bmInterlace_3
  · exact bmInterlace_4
  · exact bmInterlace_5
  · exact bmInterlace_6
  · exact bmInterlace_7
  · exact bmInterlace_8
  · exact bmInterlace_9
  · exact bmInterlace_10
  · exact bmInterlace_11
  · exact bmInterlace_12
  · exact bmInterlace_13
  · exact bmInterlace_14
  · exact bmInterlace_15
  · exact bmInterlace_16
  · exact bmInterlace_17
  · exact bmInterlace_18
  · exact bmInterlace_19
  · exact bmInterlace_20
  · exact bmInterlace_21
  · exact bmInterlace_22
  · exact bmInterlace_23
  · exact bmInterlace_24
  · exact bmInterlace_25
  · exact bmInterlace_26
  · exact bmInterlace_27
  · exact bmInterlace_28
  · exact bmInterlace_29
  · exact bmInterlace_30
  · exact bmInterlace_31
  · exact bmInterlace_32
  · exact bmInterlace_33
  · exact bmInterlace_34
  · exact bmInterlace_35

end SmallCases

end RealRooted.BorosMoll
