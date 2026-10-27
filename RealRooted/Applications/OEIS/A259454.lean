module

import Mathlib.Analysis.Polynomial.Basic
public import RealRooted.Basic
import RealRooted.Recurrence.RowModel
import RealRooted.Recurrence.Uniqueness
public import RealRooted.Basic.ProperPosition

/-!
# Adjacent strict interlacing for OEIS A259454

The polynomial family is defined by Riordan's compact row recurrence. Its first rows are

`1`, `1 + 3 * X`, and `1 + 6 * X + 7 * X ^ 2`.

The generated downstream definition instead uses a lag-three differential recurrence with
rational coefficients. The second half of this file proves that recurrence defines the same
family.

Mathematically, these are rook polynomials of the board with cells
`(i,i)`, `(i,i+1)`, and `(i,i+2)`.  Equivalently they are matching-generating
polynomials of the corresponding banded bipartite graphs.  General matching
polynomial real-rootedness proves splitting, but the missing content here is
the sharper adjacent interlacing as the board grows by one row and one column.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace RealRooted.A259454

/-- Riordan's compact recurrence for the A259454 row polynomials. -/
def row : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + 3 * X
  | 2 => 1 + 6 * X + 7 * X ^ 2
  | n + 3 =>
      (1 + 2 * X) * row (n + 2) + X * row (n + 1) -
        X ^ 3 * row n + X ^ (n + 3)

/-! ## Auxiliary development

We introduce four auxiliary polynomial families `pS, pA, pE, pC` (a transfer-matrix
refinement of the rows; combinatorially they are rook polynomials of the board with
the last one or two columns removed).  `pS n = row n`, and the key identity
`pE n * pA n - pS n * pC n = X ^ 2 * (pA (n-1) ^ 2 + ...)` is a sum of squares. -/

/-- The four-state transfer recursion. -/
private def quad : ℕ → ℝ[X] × ℝ[X] × ℝ[X] × ℝ[X]
  | 0 => (1, 1, 1, 1)
  | n + 1 =>
    let q := quad n
    ((1 + X) * q.1 + X * q.2.1 + X * q.2.2.1, q.1 + X * q.2.1 + X * q.2.2.1,
      (1 + X) * q.2.1 + X * q.2.2.2, q.2.1 + X * q.2.2.2)

private def pS (n : ℕ) : ℝ[X] := (quad n).1
private def pA (n : ℕ) : ℝ[X] := (quad n).2.1
private def pE (n : ℕ) : ℝ[X] := (quad n).2.2.1
private def pC (n : ℕ) : ℝ[X] := (quad n).2.2.2

private lemma pS_zero : pS 0 = 1 := rfl
private lemma pA_zero : pA 0 = 1 := rfl
private lemma pE_zero : pE 0 = 1 := rfl
private lemma pC_zero : pC 0 = 1 := rfl
private lemma pS_succ (n : ℕ) : pS (n + 1) = (1 + X) * pS n + X * pA n + X * pE n := rfl
private lemma pA_succ (n : ℕ) : pA (n + 1) = pS n + X * pA n + X * pE n := rfl
private lemma pE_succ (n : ℕ) : pE (n + 1) = (1 + X) * pA n + X * pC n := rfl
private lemma pC_succ (n : ℕ) : pC (n + 1) = pA n + X * pC n := rfl

private lemma pA_succ' (n : ℕ) : pA (n + 1) = pS (n + 1) - X * pS n := by
  rw [pA_succ, pS_succ]; ring

private lemma pC_succ' (n : ℕ) : pC (n + 1) = pS n + X ^ (n + 1) := by
  induction n with
  | zero => rw [pC_succ, pA_zero, pC_zero, pS_zero]; ring
  | succ n ih => rw [pC_succ, ih, pA_succ']; ring

private lemma pS_rec (n : ℕ) : pS (n + 3) =
    (1 + 2 * X) * pS (n + 2) + X * pS (n + 1) - X ^ 3 * pS n + X ^ (n + 3) := by
  rw [pS_succ (n + 2), pA_succ' (n + 1), pE_succ (n + 1), pA_succ' n, pC_succ' n]
  ring

private lemma pS_eq_row (n : ℕ) : pS n = row n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => rfl
    | 1, _ => rw [pS_succ, pS_zero, pA_zero, pE_zero, row]; ring
    | 2, _ =>
      rw [pS_succ, pS_succ, pA_succ, pE_succ, pS_zero, pA_zero, pE_zero, pC_zero, row]; ring
    | n + 3, ih =>
      rw [pS_rec, ih n (by lia), ih (n + 1) (by lia), ih (n + 2) (by lia), row]

private lemma deg_facts (n : ℕ) :
    (pS n).natDegree ≤ n ∧ (pA n).natDegree ≤ n ∧ (pE n).natDegree ≤ n ∧
      (pC n).natDegree ≤ n ∧ 1 ≤ (pS n).coeff n ∧ 1 ≤ (pA n).coeff n ∧
      1 ≤ (pE n).coeff n ∧ 1 ≤ (pC n).coeff n := by
  induction n with
  | zero => simp [pS_zero, pA_zero, pE_zero, pC_zero]
  | succ n ih =>
    obtain ⟨hS, hA, hE, hC, cS, cA, cE, cC⟩ := ih
    have z : ∀ p : ℝ[X], p.natDegree ≤ n → p.coeff (n + 1) = 0 := fun p hp =>
      coeff_eq_zero_of_natDegree_lt (by lia)
    rw [pS_succ, pA_succ, pE_succ, pC_succ]
    refine ⟨by compute_degree; lia, by compute_degree; lia,
      by compute_degree; lia, by compute_degree; lia,
      ?_, ?_, ?_, ?_⟩ <;>
    simp only [add_mul, one_mul, coeff_add, coeff_X_mul, z _ hS, z _ hA] <;>
    linarith

/-- The sum-of-squares identity. -/
private lemma delta_succ (n : ℕ) : pE (n + 1) * pA (n + 1) - pS (n + 1) * pC (n + 1) =
    X ^ 2 * (pA n ^ 2 + (pE n * pA n - pS n * pC n)) := by
  rw [pE_succ, pA_succ, pS_succ, pC_succ]; ring

private lemma delta_nonneg (n : ℕ) (t : ℝ) :
    0 ≤ (pE n * pA n - pS n * pC n).eval t := by
  induction n with
  | zero => simp [pE_zero, pA_zero, pS_zero, pC_zero]
  | succ n ih =>
    rw [delta_succ]
    simp only [eval_mul, eval_pow, eval_X, eval_add] at ih ⊢
    positivity

private lemma pS_natDegree (n : ℕ) : (pS n).natDegree = n :=
  natDegree_eq_of_le_of_coeff_ne_zero (deg_facts n).1 (by linarith [(deg_facts n).2.2.2.2.1])

private lemma pS_leadingCoeff_pos (n : ℕ) : 0 < (pS n).leadingCoeff := by
  rw [leadingCoeff, pS_natDegree]; linarith [(deg_facts n).2.2.2.2.1]

private lemma pS_ne_zero (n : ℕ) : pS n ≠ 0 :=
  leadingCoeff_ne_zero.mp (pS_leadingCoeff_pos n).ne'

private lemma pS_eval_zero (n : ℕ) : (pS n).eval 0 = 1 := by
  induction n with
  | zero => simp [pS_zero]
  | succ n ih => simp [pS_succ, ih]

private lemma ivt_root (p : ℝ[X]) {a b : ℝ} (hab : a < b) (h : p.eval a * p.eval b < 0) :
    ∃ c, a < c ∧ c < b ∧ p.eval c = 0 := by
  have hc : ContinuousOn (fun x => p.eval x) (Set.Icc a b) := p.continuous.continuousOn
  rcases lt_or_gt_of_ne (show p.eval a ≠ 0 by intro h0; rw [h0] at h; simp at h) with ha | ha
  · have hb : 0 < p.eval b := by nlinarith
    obtain ⟨c, ⟨h1, h2⟩, h3⟩ := intermediate_value_Ioo hab.le hc ⟨ha, hb⟩
    exact ⟨c, h1, h2, h3⟩
  · have hb : p.eval b < 0 := by nlinarith
    obtain ⟨c, ⟨h1, h2⟩, h3⟩ := intermediate_value_Ioo' hab.le hc ⟨hb, ha⟩
    exact ⟨c, h1, h2, h3⟩

private lemma neg_infty (p : ℝ[X]) (m : ℕ) (hm : p.natDegree = m) (hpos : 0 < p.leadingCoeff)
    (h1 : 1 ≤ m) (a : ℝ) : ∃ M < a, 0 < (-1) ^ m * p.eval M := by
  set q : ℝ[X] := C ((-1) ^ m) * p.comp (-X) with hq
  have hX : (-X : ℝ[X]).natDegree = 1 := by simp
  have hc : ((-1 : ℝ) ^ m) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hdeg : q.natDegree = m := by
    rw [hq, natDegree_C_mul hc, natDegree_comp, hX, hm, mul_one]
  have hlc : q.leadingCoeff = p.leadingCoeff := by
    rw [hq, leadingCoeff_C_mul_of_isUnit (isUnit_iff_ne_zero.mpr hc),
      leadingCoeff_comp (by rw [hX]; norm_num), hm]
    simp only [leadingCoeff_neg, leadingCoeff_X]
    rw [← mul_assoc, mul_comm ((-1 : ℝ) ^ m), mul_assoc, ← mul_pow]; norm_num
  have ht := tendsto_atTop_of_leadingCoeff_nonneg q
    (by rw [degree_eq_natDegree (fun h => by rw [h] at hdeg; simp at hdeg; lia), hdeg];
        exact_mod_cast h1) (by rw [hlc]; exact hpos.le)
  obtain ⟨x, hx1, hx2⟩ :=
    ((ht.eventually_gt_atTop 0).and (Filter.eventually_gt_atTop (-a))).exists
  refine ⟨-x, by linarith, ?_⟩
  simpa [hq, eval_comp] using hx1

private lemma dec_chain (v : ℕ → ℝ) (n : ℕ) (h : ∀ i, i + 1 < n → v (i + 1) < v i) :
    ∀ j k, j < k → k < n → v k < v j := by
  intro j k hjk hk
  induction k with
  | zero => lia
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hjk with h' | h'
    · exact (h k hk).trans (ih h' (by lia))
    · subst h'; exact h j hk

private lemma roots_eq (p : ℝ[X]) (m : ℕ) (v : ℕ → ℝ) (hp : p ≠ 0)
    (hdeg : p.natDegree = m)
    (hroot : ∀ j < m, p.eval (v j) = 0) (hdec : ∀ i, i + 1 < m → v (i + 1) < v i) :
    p.roots = (Finset.range m).val.map v := by
  have hinj := dec_chain v m hdec
  have hnd : ((Finset.range m).val.map v).Nodup := by
    refine (Finset.range m).nodup.map_on ?_
    intro j hj k hk hjk
    simp only [Finset.mem_val, Finset.mem_range] at hj hk
    rcases lt_trichotomy j k with h | h | h
    · exact absurd hjk (hinj j k h hk).ne'
    · exact h
    · exact absurd hjk (hinj k j h hj).ne
  symm
  apply Multiset.eq_of_le_of_card_le
  · rw [Multiset.le_iff_subset hnd]
    intro x hx
    simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_range] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    exact (mem_roots hp).mpr (hroot j hj)
  · simpa [hdeg] using card_roots' p

private lemma prod_sign (m i : ℕ) (hi : i ≤ m) (v : ℕ → ℝ) (y : ℝ)
    (hy1 : ∀ j < i, y < v j)
    (hy2 : ∀ j, i ≤ j → j < m → v j < y) :
    0 < (-1) ^ i * ∏ j ∈ Finset.range m, (y - v j) := by
  rw [← Finset.prod_range_mul_prod_Ico _ hi, ← mul_assoc]
  have : (-1 : ℝ) ^ i * ∏ j ∈ Finset.range i, (y - v j) =
      ∏ j ∈ Finset.range i, (v j - y) := by
    rw [← Finset.card_range i, ← Finset.prod_const, Finset.card_range,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => by ring
  rw [this]
  apply mul_pos
  · exact Finset.prod_pos fun j hj => by
      have := hy1 j (Finset.mem_range.mp hj); linarith
  · exact Finset.prod_pos fun j hj => by
      obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hj
      have := hy2 j h1 h2; linarith

private lemma sign_eval (p : ℝ[X]) (m : ℕ) (v : ℕ → ℝ) (hdeg : p.natDegree = m)
    (hlc : 0 < p.leadingCoeff) (hroot : ∀ j < m, p.eval (v j) = 0)
    (hdec : ∀ i, i + 1 < m → v (i + 1) < v i) (i : ℕ) (hi : i ≤ m) (y : ℝ)
    (hy1 : ∀ j < i, y < v j) (hy2 : ∀ j, i ≤ j → j < m → v j < y) :
    0 < (-1) ^ i * p.eval y := by
  have hp : p ≠ 0 := leadingCoeff_ne_zero.mp hlc.ne'
  have hr := roots_eq p m v hp hdeg hroot hdec
  have hcard : p.roots.card = p.natDegree := by rw [hr, hdeg]; simp
  have hfac := C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  rw [← hfac, hr, eval_mul, eval_C, eval_multiset_prod, Multiset.map_map, Multiset.map_map]
  have : (Multiset.map ((eval y ∘ fun a => X - C a) ∘ v) (Finset.range m).val).prod
      = ∏ j ∈ Finset.range m, (y - v j) := by
    rw [Finset.prod_eq_multiset_prod]; congr 1; apply Multiset.map_congr rfl; intro j _; simp
  rw [this, mul_left_comm]
  exact mul_pos hlc (prod_sign m i hi v y hy1 hy2)

private lemma key_sign (n i : ℕ) (t : ℝ) (ht : t < 0) (hS : (pS (n + 1)).eval t = 0)
    (hs : 0 < (-1) ^ i * (pS n).eval t) : (-1) ^ i * (pS (n + 2)).eval t < 0 := by
  have hD := delta_nonneg (n + 1) t
  have hA : (pA (n + 1)).eval t = - t * (pS n).eval t := by
    rw [pA_succ']; simp [hS]
  have h2 : (pS (n + 2)).eval t = t * (pA (n + 1)).eval t + t * (pE (n + 1)).eval t := by
    rw [pS_succ (n + 1)]; simp [hS]
  simp only [eval_sub, eval_mul, hS, zero_mul, sub_zero] at hD
  rw [h2]
  set a := (pA (n + 1)).eval t
  set e := (pE (n + 1)).eval t
  set s := (pS n).eval t
  have hsq : ((-1 : ℝ) ^ i) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hsa : 0 < (-1) ^ i * a := by rw [hA]; nlinarith
  have ha2 : 0 < a ^ 2 := by nlinarith
  have hX : a * (t * a + t * e) < 0 := by nlinarith
  nlinarith

/-- Inductive data: the `n+1` roots of `pS (n+1)` (decreasing order), together with the
signs of `pS n` at them. -/
private def Claim (n : ℕ) (v : ℕ → ℝ) : Prop :=
  (∀ i ≤ n, (pS (n + 1)).eval (v i) = 0) ∧ v 0 < 0 ∧ (∀ i < n, v (i + 1) < v i) ∧
    (∀ i ≤ n, 0 < (-1) ^ i * (pS n).eval (v i))

private lemma claim_zero : Claim 0 (fun _ => -1 / 3) := by
  refine ⟨fun i _ => ?_, by norm_num, by simp, fun i hi => ?_⟩
  · simp [pS_succ, pS_zero, pA_zero, pE_zero]; norm_num
  · obtain rfl : i = 0 := by lia
    simp [pS_zero]

private lemma chain_le (v : ℕ → ℝ) (n : ℕ) (h : ∀ i < n, v (i + 1) < v i) :
    ∀ j k, j ≤ k → k ≤ n → v k ≤ v j := by
  intro j k hjk hk
  rcases eq_or_lt_of_le hjk with h' | h'
  · rw [h']
  · exact (dec_chain v (n + 1) (fun i hi => h i (by lia)) j k h' (by lia)).le

private lemma claim_step (n : ℕ) (v : ℕ → ℝ) (hv : Claim n v) :
    ∃ w, Claim (n + 1) w ∧ ∀ i ≤ n, w (i + 1) < v i ∧ v i < w i := by
  obtain ⟨hroot, hv0, hdec, hsign⟩ := hv
  have hle := chain_le v n hdec
  have hneg : ∀ i ≤ n, v i < 0 := fun i hi => (hle 0 i (by lia) hi).trans_lt hv0
  have key : ∀ i ≤ n, (-1) ^ i * (pS (n + 2)).eval (v i) < 0 := fun i hi =>
    key_sign n i (v i) (hneg i hi) (hroot i hi) (hsign i hi)
  obtain ⟨M, hM, hMs⟩ := neg_infty (pS (n + 2)) (n + 2) (pS_natDegree _)
    (pS_leadingCoeff_pos _) (by lia) (v n)
  have hex : ∀ k, ∃ w, k ≤ n + 1 → (pS (n + 2)).eval w = 0 ∧
      (k = 0 → v 0 < w ∧ w < 0) ∧
      (∀ j, k = j + 1 → j < n → v (j + 1) < w ∧ w < v j) ∧
      (k = n + 1 → M < w ∧ w < v n) := by
    intro k
    by_cases hk : k ≤ n + 1
    · rcases Nat.eq_zero_or_pos k with rfl | hk0
      · obtain ⟨c, h1, h2, h3⟩ := ivt_root (pS (n + 2)) hv0 (by
          have := key 0 (by lia); rw [pS_eval_zero]; simpa using this)
        exact ⟨c, fun _ => ⟨h3, fun _ => ⟨h1, h2⟩, fun j hj => by lia, fun h => by lia⟩⟩
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by lia⟩
        rcases lt_or_eq_of_le (show j ≤ n by lia) with hj | rfl
        · have k1 := key j (by lia)
          have k2 := key (j + 1) (by lia)
          have hsq : ((-1 : ℝ) ^ j) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
          rw [pow_succ] at k2
          obtain ⟨c, h1, h2, h3⟩ := ivt_root (pS (n + 2)) (hdec j hj) (by nlinarith)
          exact ⟨c, fun _ => ⟨h3, fun h => by lia, fun j' hj' _ => by
            obtain rfl : j' = j := by lia
            exact ⟨h1, h2⟩, fun h => by lia⟩⟩
        · have k1 := key j le_rfl
          have hsq : ((-1 : ℝ) ^ j) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
          rw [pow_add] at hMs
          obtain ⟨c, h1, h2, h3⟩ := ivt_root (pS (j + 2)) hM (by norm_num at hMs; nlinarith)
          exact ⟨c, fun _ => ⟨h3, fun h => by lia, fun j' hj' hj'' => by lia,
            fun _ => ⟨h1, h2⟩⟩⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose w hw using hex
  have hint : ∀ i ≤ n, w (i + 1) < v i ∧ v i < w i := by
    intro i hi
    constructor
    · rcases lt_or_eq_of_le hi with h | rfl
      · exact ((hw (i + 1) (by lia)).2.2.1 i rfl h).2
      · exact ((hw (i + 1) le_rfl).2.2.2 rfl).2
    · rcases Nat.eq_zero_or_pos i with rfl | h
      · exact ((hw 0 (by lia)).2.1 rfl).1
      · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by lia⟩
        exact ((hw (j + 1) (by lia)).2.2.1 j rfl (by lia)).1
  refine ⟨w, ⟨fun i hi => (hw i hi).1, ((hw 0 (by lia)).2.1 rfl).2,
    fun i hi => (hint i (by lia)).1.trans (hint i (by lia)).2, fun i hi => ?_⟩, hint⟩
  apply sign_eval (pS (n + 1)) (n + 1) v (pS_natDegree _) (pS_leadingCoeff_pos _)
    (fun j hj => hroot j (by lia)) (fun j hj => hdec j (by lia)) i hi
  · intro j hj
    rcases Nat.eq_zero_or_pos i with rfl | h
    · lia
    · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by lia⟩
      exact (hint k (by lia)).1.trans_le (hle j k (by lia) (by lia))
  · intro j hj1 hj2
    exact (hle i j hj1 (by lia)).trans_lt (hint i (by lia)).2

/-- Reversed list `[v (n-1), ..., v 0]`. -/
private def revList (v : ℕ → ℝ) (n : ℕ) : List ℝ := ((List.range n).map v).reverse

private lemma revList_succ (v : ℕ → ℝ) (n : ℕ) :
    revList v (n + 1) = v n :: revList v n := by
  simp [revList, List.range_succ]

private lemma revList_length (v : ℕ → ℝ) (n : ℕ) : (revList v n).length = n := by
  simp [revList]

private lemma revList_coe (v : ℕ → ℝ) (n : ℕ) :
    (↑(revList v n) : Multiset ℝ) = (Finset.range n).val.map v := by
  simp [revList, Multiset.range]

private lemma revList_pairwise (v : ℕ → ℝ) (n : ℕ)
    (h : ∀ i, i + 1 < n → v (i + 1) < v i) :
    (revList v n).Pairwise (· ≤ ·) := by
  induction n with
  | zero => simp [revList]
  | succ n ih =>
    rw [revList_succ, List.pairwise_cons]
    refine ⟨fun x hx => ?_, ih fun i hi => h i (by lia)⟩
    simp only [revList, List.mem_reverse, List.mem_map, List.mem_range] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    exact (dec_chain v (n + 1) h j n hj (by lia)).le

private lemma revList_interlaces (v w : ℕ → ℝ) (n : ℕ)
    (h : ∀ i < n, w (i + 1) ≤ v i ∧ v i ≤ w i) :
    ListInterlaces (revList v n) (revList w (n + 1)) := by
  induction n with
  | zero => simp [revList, ListInterlaces]
  | succ n ih =>
    rw [revList_succ, revList_succ w (n + 1), revList_succ w n, ListInterlaces,
      ← revList_succ w n]
    exact ⟨(h n (by lia)).1, (h n (by lia)).2, ih fun i hi => h i (by lia)⟩

private lemma claim_exists (n : ℕ) : ∃ v, Claim n v := by
  induction n with
  | zero => exact ⟨_, claim_zero⟩
  | succ n ih =>
    obtain ⟨v, hv⟩ := ih
    obtain ⟨w, hw, -⟩ := claim_step n v hv
    exact ⟨w, hw⟩

private lemma final (n : ℕ) (v w : ℕ → ℝ) (hv : ∀ i < n, (pS n).eval (v i) = 0)
    (hvd : ∀ i, i + 1 < n → v (i + 1) < v i) (hw : ∀ i < n + 1, (pS (n + 1)).eval (w i) = 0)
    (hwd : ∀ i, i + 1 < n + 1 → w (i + 1) < w i)
    (hint : ∀ i < n, w (i + 1) ≤ v i ∧ v i ≤ w i) :
    StrictInterl (pS n) (pS (n + 1)) := by
  have r1 := roots_eq (pS n) n v (pS_ne_zero n) (pS_natDegree n) hv hvd
  have r2 := roots_eq (pS (n + 1)) (n + 1) w (pS_ne_zero _) (pS_natDegree _) hw hwd
  refine ⟨⟨pS_ne_zero n, splits_iff_card_roots.mpr (by rw [r1, pS_natDegree]; simp)⟩,
    ⟨pS_ne_zero _, splits_iff_card_roots.mpr (by rw [r2, pS_natDegree]; simp)⟩,
    revList v n, revList w (n + 1), revList_pairwise v n hvd, revList_pairwise w (n + 1) hwd,
    by rw [revList_coe, r1], by rw [revList_coe, r2],
    Or.inl ⟨?_, revList_interlaces v w n hint⟩⟩
  simp [revList_length]

/-- Consecutive A259454 rows are in strict proper position.

The proof was found by Aristotle (Harmonic). -/
theorem row_strictInterl_succ (n : ℕ) : StrictInterl (row n) (row (n + 1)) := by
  rw [← pS_eq_row, ← pS_eq_row]
  cases n with
  | zero =>
    obtain ⟨h1, -, -, -⟩ := claim_zero
    exact final 0 (fun _ => 0) _ (fun i hi => by lia) (fun i hi => by lia)
      (fun i hi => h1 i (by lia)) (fun i hi => by lia) (fun i hi => by lia)
  | succ m =>
    obtain ⟨v, hv⟩ := claim_exists m
    obtain ⟨w, hw, hint⟩ := claim_step m v hv
    exact final (m + 1) v w (fun i hi => hv.1 i (by lia)) (fun i hi => hv.2.2.1 i (by lia))
      (fun i hi => hw.1 i (by lia)) (fun i hi => hw.2.2.1 i (by lia))
      (fun i hi => ⟨(hint i (by lia)).1.le, (hint i (by lia)).2.le⟩)

/-- The A259454 row indexed by `n` has degree `n`. -/
theorem row_natDegree (n : ℕ) : (row n).natDegree = n := by
  simpa only [← pS_eq_row] using pS_natDegree n

/-- Consecutive A259454 rows interlace. -/
theorem row_interlaces_succ (n : ℕ) : Interlaces (row n) (row (n + 1)) :=
  (row_strictInterl_succ n).toInterlaces (by simp only [row_natDegree])

/-! ## Bridge from the generated differential recurrence -/

/-- The lag-three differential update in the generated A259454 presentation. -/
def nextRow (n : ℕ) (p₂ p₁ p₀ : ℝ[X]) : ℝ[X] :=
  (C ((10 / 7) * (1 / (-3 + -1 * (n : ℝ)))) * X +
      C ((26 / 7) * (1 / (-3 + -1 * (n : ℝ)))) * X ^ 2) * p₂.derivative +
    (C ((-3 / 7) * (1 / (-3 + -1 * (n : ℝ)))) * X +
      C ((-10 / 7) * (1 / (-3 + -1 * (n : ℝ)))) * X ^ 2 +
      C ((-33 / 7) * (1 / (-3 + -1 * (n : ℝ)))) * X ^ 3) * p₁.derivative +
    (C ((1 / (-3 + -1 * (n : ℝ))) * (-27 / 7 + (-10 / 7) * (n : ℝ))) +
      C ((1 / (-3 + -1 * (n : ℝ))) * (-101 / 7 + (-40 / 7) * (n : ℝ))) * X) * p₂ +
    (C ((1 / (-3 + -1 * (n : ℝ))) * (6 / 7 + (3 / 7) * (n : ℝ))) +
      C ((1 / (-3 + -1 * (n : ℝ))) * (5 / 7 + (n : ℝ))) * X +
      C ((1 / (-3 + -1 * (n : ℝ))) * (40 / 7 + (33 / 7) * (n : ℝ))) * X ^ 2) * p₁ +
    (C ((3 / 7) * (1 / (-3 + -1 * (n : ℝ))) * (4 + (n : ℝ))) * X ^ 2 +
      C ((1 / (-3 + -1 * (n : ℝ))) * (4 + (n : ℝ))) * X ^ 3) * p₀

private def literalRows : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + 3 * X
  | 2 => 1 + 6 * X + 7 * X ^ 2
  | n + 3 => nextRow n (literalRows (n + 2)) (literalRows (n + 1)) (literalRows n)

private def compactRHS (n : ℕ) : ℝ[X] :=
  (1 + 2 * X) * literalRows (n + 2) + X * literalRows (n + 1) -
    X ^ 3 * literalRows n + X ^ (n + 3)

private def clearedRHS (n : ℕ) : ℝ[X] :=
  (C (-10) * X + C (-26) * X ^ 2) * (literalRows (n + 2)).derivative +
    (C 3 * X + C 10 * X ^ 2 + C 33 * X ^ 3) *
      (literalRows (n + 1)).derivative +
    (C (10 * (n : ℝ) + 27) + C (40 * (n : ℝ) + 101) * X) *
      literalRows (n + 2) -
    (C (3 * (n : ℝ) + 6) + C (7 * (n : ℝ) + 5) * X +
      C (33 * (n : ℝ) + 40) * X ^ 2) * literalRows (n + 1) -
    (C (3 * ((n : ℝ) + 4)) * X ^ 2 + C (7 * ((n : ℝ) + 4)) * X ^ 3) * literalRows n

private lemma clearedRHS_eq_scale_nextRow (n : ℕ) :
    clearedRHS n = C (7 * ((n : ℝ) + 3)) *
      nextRow n (literalRows (n + 2)) (literalRows (n + 1)) (literalRows n) := by
  have : (-3 : ℝ) - (n : ℝ) ≠ 0 := by grind
  unfold nextRow clearedRHS
  apply Polynomial.funext
  intro x
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_pow]
  grind

private lemma literalRows_step (n : ℕ) :
    literalRows (n + 3) =
      nextRow n (literalRows (n + 2)) (literalRows (n + 1)) (literalRows n) := by
  rw [literalRows]

private lemma literalRows_compact_recurrence (n : ℕ) :
    literalRows (n + 3) =
      (1 + 2 * X) * literalRows (n + 2) + X * literalRows (n + 1) -
        X ^ 3 * literalRows n + X ^ (n + 3) := by
  have hraw : nextRow n (literalRows (n + 2)) (literalRows (n + 1))
      (literalRows n) = compactRHS n := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      match n with
      | 0 =>
        apply Polynomial.funext
        intro x
        simp [nextRow, compactRHS, literalRows]
        ring
      | 1 | 2 =>
        apply Polynomial.funext
        intro x
        simp [nextRow, compactRHS, literalRows]
        grind
      | k + 3 =>
        have hcc := ih (k + 2) (by lia)
        have hc := ih (k + 1) (by lia)
        have hp := ih k (by lia)
        have scaled (i : ℕ)
            (hi : nextRow i (literalRows (i + 2)) (literalRows (i + 1))
              (literalRows i) = compactRHS i) :
            clearedRHS i = C (7 * ((i : ℝ) + 3)) * compactRHS i := by
          rw [clearedRHS_eq_scale_nextRow, hi]
        have hccN := scaled (k + 2) hcc
        have hcN := scaled (k + 1) hc
        have hpN := scaled k hp
        have hrr := (literalRows_step (k + 2)).trans hcc
        have hr := (literalRows_step (k + 1)).trans hc
        have hrp := (literalRows_step k).trans hp
        unfold compactRHS at hrr hr hrp
        have hscale : C (7 * (((k + 3 : ℕ) : ℝ) + 3)) ≠ (0 : ℝ[X]) := by
          rw [C_ne_zero]
          positivity
        apply mul_left_cancel₀ hscale
        rw [← clearedRHS_eq_scale_nextRow (k + 3)]
        unfold clearedRHS compactRHS at hccN hcN hpN ⊢
        norm_num [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at hrr hr hrp hccN hcN hpN ⊢
        rw [hr, hrp] at hccN
        rw [hrp] at hcN
        rw [hrr, hr, hrp]
        simp only [derivative_add, derivative_sub, derivative_mul,
          derivative_pow, derivative_X, derivative_one, derivative_ofNat,
          zero_mul, zero_add, Nat.cast_add] at hccN hcN hpN ⊢
        apply Polynomial.funext
        intro x
        have hccx := congrArg (Polynomial.eval x) hccN
        have hcx := congrArg (Polynomial.eval x) hcN
        have hpx := congrArg (Polynomial.eval x) hpN
        simp only [eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_pow,
          eval_one, eval_ofNat] at hccx hcx hpx ⊢
        norm_num [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at hccx hcx hpx ⊢
        linear_combination (-x ^ 3) * hpx + x * hcx + (1 + 2 * x) * hccx
  simpa [compactRHS] using (literalRows_step n).trans hraw

private lemma literalRows_eq_row : ∀ n : ℕ, literalRows n = row n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 | 1 | 2 => rfl
    | k + 3 =>
      rw [literalRows_compact_recurrence, row,
        ih k (by lia), ih (k + 1) (by lia), ih (k + 2) (by lia)]

/-- Every sequence with the generated A259454 initial rows and differential recurrence equals
Riordan's compact row family. -/
theorem eq_row_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hone : P 1 = 1 + 3 * X)
    (htwo : P 2 = 1 + 6 * X + 7 * X ^ 2)
    (hrec : ∀ n : ℕ, P (n + 3) = nextRow n (P (n + 2)) (P (n + 1)) (P n))
    (n : ℕ) : P n = row n := by
  rw [← literalRows_eq_row]
  exact sequence_eq_of_same_lag_three_recurrence nextRow
    (by simpa only [literalRows] using hzero)
    (by simpa only [literalRows] using hone)
    (by simpa only [literalRows] using htwo)
    hrec literalRows_step n

/-- Every sequence with the generated A259454 recurrence has interlacing consecutive rows. -/
@[rr_row_model]
theorem interlaces_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hone : P 1 = 1 + 3 * X)
    (htwo : P 2 = 1 + 6 * X + 7 * X ^ 2)
    (hrec : ∀ n : ℕ, P (n + 3) = nextRow n (P (n + 2)) (P (n + 1)) (P n))
    (n : ℕ) : Interlaces (P n) (P (n + 1)) := by
  rw [eq_row_of_recurrence hzero hone htwo hrec,
    eq_row_of_recurrence hzero hone htwo hrec]
  exact row_interlaces_succ n

end RealRooted.A259454
