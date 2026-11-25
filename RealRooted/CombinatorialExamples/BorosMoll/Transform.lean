module

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Topology.Algebra.Polynomial
import RealRooted.Mathlib.Algebra.Order.BigOperators.Ring.Multiset
import RealRooted.Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Polynomial.Splits

/-!
# Boros–Moll log-concavity transform: definitions and root arguments

Let `d_i(n)` be the Boros–Moll coefficients (`bmCoeff`),
`L(d(n))_i = d_i(n)^2 - d_{i-1}(n) d_{i+1}(n)` their log-concavity transform (`bmL`),
`M_n(x) = ∑ L(d(n))_i x^i` (`bmM`), and `N_n` the Narayana polynomial (`narayanaN`).
Xie and Zhang (arXiv:2609.20653, Theorem 1.1) prove that `M_n` has `n` simple negative zeros
which strictly interlace the zeros of `N_n`
(`RealRooted.BorosMoll.bmM_roots`, `RealRooted.BorosMoll.bmM_strictInterlaces_narayanaN`).

This file contains the definitions, the generic facts on signs and sorted roots, the reduction
of interlacing to sign alternation at explicit points (`BMInterlace`). The exact computation
for `1 ≤ n ≤ 35` is in `RealRooted.CombinatorialExamples.BorosMoll.SmallCases`. The estimates
for `n ≥ 36` are in `RealRooted.CombinatorialExamples.BorosMoll.Estimates`, and the final
theorems in `RealRooted.CombinatorialExamples.BorosMoll`.
-/

@[expose] public section

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
  | succ k ih => grind

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

/-- If a polynomial of degree `n` alternates in sign along `t 0 < t 1 < ⋯ < t n`, then its
roots are exactly `n` reals `s 0 < ⋯ < s (n-1)` with `t j < s j < t (j+1)`. -/
private lemma roots_of_alternation (p : ℝ[X]) (n : ℕ) (hn : 1 ≤ n) (hdeg : p.natDegree = n)
    (t : ℕ → ℝ) (ht : ∀ j < n, t j < t (j + 1))
    (hsign : ∀ j < n, p.eval (t j) * p.eval (t (j + 1)) < 0) :
    ∃ s : ℕ → ℝ, (∀ j < n, t j < s j ∧ s j < t (j + 1)) ∧ p ≠ 0 ∧
      p.roots = ((List.range n).map s : Multiset ℝ) := by
  exact roots_of_intervals p n hn hdeg t (fun j => t (j + 1)) ht
    (fun _ _ => le_rfl) hsign

private lemma mono_of_interleave {s t : ℕ → ℝ} {n : ℕ} (h : ∀ j < n, t j < s j ∧ s j < t (j + 1)) :
    ∀ i j, i < j → j < n → s i < s j :=
  lt_of_succ_lt (fun j hj => ((h j (by lia)).2).trans (h (j+1) hj).1)

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
  have := Multiset.prod_sub_sign (m := p.roots) (x := x)
    (fun ξ hξ hξeq => hxS (hξeq ▸ hξ))
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

lemma coeff_bmM (n i : ℕ) : (bmM n).coeff i = if i < n + 1 then bmL n i else 0 := by
  simpa only [bmM, C_mul_X_pow_eq_monomial] using
    Polynomial.coeff_sum_range_monomial (bmL n) (n + 1) i

private lemma bmL_self (n : ℕ) : bmL n n = bmCoeff n n ^ 2 := by
  simp [bmL, bmCoeff_succ_self]

lemma bmM_natDegree (n : ℕ) : (bmM n).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro i hi
    rw [coeff_bmM, ite_eq_right]
    have : n < i := by exact_mod_cast hi
    lia
  · rw [coeff_bmM, ite_eq_left (by lia), bmL_self]
    exact (pow_pos (bmCoeff_self_pos n) 2).ne'

lemma bmM_leadingCoeff_pos (n : ℕ) : 0 < (bmM n).leadingCoeff := by
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

/-! ## Interlacing from prescribed root intervals -/

open Polynomial

private lemma mono_of_succ {t : ℕ → ℝ} {m : ℕ} (ht : ∀ i < m, t i < t (i + 1)) :
    ∀ i j, i ≤ j → j ≤ m → t i ≤ t j := by
  intro i j hij hjm
  induction j with
  | zero => grind
  | succ k ih => grind

/-- Construct `BMInterlace n` from alternating sign changes of `bmM n` and `narayanaN n`
at increasing nonpositive sample points. This is the interface used by the exact
finite certificates in `BorosMoll.SmallCases`. -/
lemma bmInterlace_of_points (n : ℕ) (hn : 1 ≤ n) (t : ℕ → ℝ)
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

end SmallCasesCore

end RealRooted.BorosMoll
