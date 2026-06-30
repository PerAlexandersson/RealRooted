import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Tactic

/-!
# Newton's inequalities for elementary symmetric functions

This auxiliary file isolates the core analytic content of Newton's inequalities
for elementary symmetric functions of a finite multiset of real numbers.
-/

open Polynomial

namespace NewtonAux

set_option linter.style.induction false in
set_option linter.flexible false in
lemma iterate_derivative_rr {p : ℝ[X]} (hp : Multiset.card p.roots = p.natDegree)
    (k : ℕ) :
    Multiset.card (derivative^[k] p).roots = (derivative^[k] p).natDegree ∧
      (derivative^[k] p).natDegree = p.natDegree - k := by
  induction' k with k ih
  · aesop
  · by_cases h : (derivative^[k] p).natDegree = 0 <;>
      simp_all +decide [Function.iterate_succ_apply']
    · rw [Polynomial.eq_C_of_natDegree_eq_zero
        (show (derivative^[k] p).natDegree = 0 from by lia)]
      norm_num
      lia
    · have h_roots :
          Multiset.card (Polynomial.roots (Polynomial.derivative (derivative^[k] p))) ≥
            (derivative^[k] p).natDegree - 1 := by
        have := Polynomial.card_roots_le_derivative (derivative^[k] p)
        aesop
      have h_deg :
          (Polynomial.derivative (derivative^[k] p)).natDegree ≤
            (derivative^[k] p).natDegree - 1 := by
        exact Polynomial.natDegree_derivative_le _
      have h_card :
          Multiset.card (Polynomial.roots (Polynomial.derivative (derivative^[k] p))) ≤
            (Polynomial.derivative (derivative^[k] p)).natDegree := by
        exact Polynomial.card_roots' _
      lia

set_option linter.style.induction false in
set_option linter.flexible false in
set_option linter.unusedSimpArgs false in
lemma reverse_rr {p : ℝ[X]} (hp : Multiset.card p.roots = p.natDegree)
    (h0 : p.coeff 0 ≠ 0) :
    Multiset.card p.reverse.roots = p.reverse.natDegree := by
  obtain ⟨rs, hrs⟩ :
      ∃ rs : Multiset ℝ,
        p = Polynomial.C p.leadingCoeff *
          Multiset.prod (Multiset.map (fun r => Polynomial.X - Polynomial.C r) rs) := by
    exact ⟨p.roots,
      Polynomial.Splits.eq_prod_roots <| Polynomial.splits_iff_card_roots.mpr hp⟩
  have h_reverse :
      p.reverse =
        Polynomial.C p.leadingCoeff *
          Multiset.prod
            (Multiset.map (fun r => Polynomial.C (-r) * (Polynomial.X - Polynomial.C (1 / r)))
              rs) := by
    have h_reverse :
        p.reverse =
          Polynomial.C p.leadingCoeff *
            Multiset.prod (Multiset.map (fun r =>
              Polynomial.reverse (Polynomial.X - Polynomial.C r)) rs) := by
      conv_lhs => rw [hrs]
      induction' rs using Multiset.induction with r rs ih
      · simp +decide [Polynomial.reverse]
      · induction' (r ::ₘ rs) using Multiset.induction <;> norm_num at *
        tauto
    refine h_reverse.trans (congr_arg _ (congr_arg _ (Multiset.map_congr rfl fun x hx => ?_)))
    rcases eq_or_ne x 0 with rfl | hx' <;>
      simp +decide [Polynomial.reverse, Polynomial.coeff_zero_eq_eval_zero] at *
    · exact h0 <| by
        rw [hrs]
        simp +decide [hx, Polynomial.eval_multiset_prod]
    · exact Polynomial.funext fun y => by
        simp +decide [hx', mul_sub, sub_mul, mul_assoc, mul_left_comm]
  rw [h_reverse, Polynomial.roots_C_mul, Polynomial.natDegree_C_mul] <;> norm_num
  · rw [Polynomial.roots_multiset_prod] <;> norm_num [Polynomial.natDegree_multiset_prod]
    · rw [Polynomial.natDegree_multiset_prod] <;> norm_num [Polynomial.natDegree_mul']
      · rw [Multiset.map_congr rfl]
        intro x hx
        by_cases hx' : x = 0 <;> simp +decide [hx', Polynomial.natDegree_mul']
      · intro x hx
        refine ⟨?_, Polynomial.X_sub_C_ne_zero _⟩
        contrapose! h0
        replace hrs := congr_arg (fun q => Polynomial.coeff q 0) hrs
        simp_all +singlePass
        exact Or.inr (by
          rw [Polynomial.coeff_zero_eq_eval_zero]
          rw [Polynomial.eval_multiset_prod]
          aesop)
    · intro x hx
      refine ⟨?_, Polynomial.X_sub_C_ne_zero _⟩
      contrapose! h0
      replace hrs := congr_arg (fun q => Polynomial.coeff q 0) hrs
      simp_all +singlePass
      exact Or.inr (by
        rw [Polynomial.coeff_zero_eq_eval_zero]
        rw [Polynomial.eval_multiset_prod]
        aesop)
  · rintro rfl
    contradiction
  · rintro rfl
    contradiction

set_option linter.unusedSimpArgs false in
lemma quad_discrim {q : ℝ[X]} (hd : q.natDegree = 2)
    (hq : Multiset.card q.roots = q.natDegree) :
    4 * q.coeff 0 * q.coeff 2 ≤ q.coeff 1 ^ 2 := by
  obtain ⟨x0, hx⟩ : ∃ x0, x0 ∈ q.roots := by
    exact Multiset.card_pos_iff_exists_mem.mp (by linarith)
  simp_all +decide [Polynomial.eval_eq_sum_range, Finset.sum_range_succ',
    Polynomial.natDegree_eq_of_degree_eq_some]
  cases le_or_gt 0 (q.coeff 2) <;>
    nlinarith [sq_nonneg (q.coeff 1 + 2 * x0 * q.coeff 2)]

set_option linter.flexible false in
set_option linter.unusedSimpArgs false in
lemma newton_poly {g : ℝ[X]} (hg : Multiset.card g.roots = g.natDegree)
    {j : ℕ} (hj0 : 0 < j) (hj : j < g.natDegree) :
    g.coeff (j - 1) * g.coeff (j + 1) *
        ((j + 1 : ℝ) * ((g.natDegree - j + 1 : ℕ) : ℝ)) ≤
      g.coeff j ^ 2 * ((j : ℝ) * ((g.natDegree - j : ℕ) : ℝ)) := by
  revert j
  intro j hj0 hj
  by_contra h_neg
  have h_pos : 0 < g.coeff (j - 1) * g.coeff (j + 1) := by
    exact not_le.mp fun h =>
      h_neg <| by
        exact le_trans (mul_nonpos_of_nonpos_of_nonneg h <| by positivity) <| by
          exact mul_nonneg (sq_nonneg _) <| by positivity
  set q1 := derivative^[j - 1] g
  set q2 := q1.reverse
  set q := derivative^[g.natDegree - j - 1] q2
  have hq_deg : q.natDegree = 2 := by
    have hq_deg : q2.natDegree = g.natDegree - (j - 1) := by
      have hq1_deg : q1.natDegree = g.natDegree - (j - 1) := by
        have := iterate_derivative_rr hg (j - 1)
        aesop
      have hq1_coeff0 : q1.coeff 0 ≠ 0 := by
        simp +zetaDelta at *
        simp_all +decide [Polynomial.coeff_iterate_derivative]
        aesop_cat
      have hq2_deg : q2.natDegree = q1.natDegree := by
        rw [Polynomial.reverse_natDegree]
        rw [Polynomial.natTrailingDegree_eq_zero.mpr]
        · aesop
        · exact Or.inr hq1_coeff0
      rw [hq2_deg, hq1_deg]
    convert iterate_derivative_rr
      (show Multiset.card q2.roots = q2.natDegree from ?_) (g.natDegree - j - 1) |>.2
      using 1
    · lia
    · apply reverse_rr
      · convert iterate_derivative_rr hg (j - 1) |>.1 using 1
      · simp +zetaDelta at *
        simp_all +decide [Polynomial.coeff_iterate_derivative]
        aesop
  have hq_coeff0 :
      q.coeff 0 =
        ((g.natDegree - j - 1).descFactorial (g.natDegree - j - 1)) *
          ((j + 1).descFactorial (j - 1)) * g.coeff (j + 1) := by
    have hq_coeff0 :
        q.coeff 0 =
          ((g.natDegree - j - 1).descFactorial (g.natDegree - j - 1)) *
            q2.coeff (g.natDegree - j - 1) := by
      rw [Polynomial.coeff_iterate_derivative]
      aesop
    have hq_coeff0 : q2.coeff (g.natDegree - j - 1) = q1.coeff 2 := by
      rw [Polynomial.coeff_reverse]
      rw [show q1.natDegree = g.natDegree - (j - 1) from ?_, revAt]
      · simp +zetaDelta at *
        rw [if_pos (by lia)]
        rw [show g.natDegree - (j - 1) - (g.natDegree - j - 1) = 2 by lia]
      · have := iterate_derivative_rr hg (j - 1)
        aesop
    have hq_coeff0 : q1.coeff 2 = ((j + 1).descFactorial (j - 1)) * g.coeff (j + 1) := by
      rw [Polynomial.coeff_iterate_derivative]
      rw [show 2 + (j - 1) = j + 1 from by lia, nsmul_eq_mul]
    grind
  have hq_coeff1 :
      q.coeff 1 =
        ((g.natDegree - j - 1 + 1).descFactorial (g.natDegree - j - 1)) *
          (j.descFactorial (j - 1)) * g.coeff j := by
    rw [Polynomial.coeff_iterate_derivative]
    rw [Polynomial.coeff_reverse]
    rw [Polynomial.coeff_iterate_derivative]
    rw [show q1.natDegree = g.natDegree - (j - 1) from ?_]
    · rcases j with _ | j <;> simp_all +decide [Nat.sub_sub, add_comm]
      rw [show g.natDegree - j = (g.natDegree - (1 + (j + 1))) + 2 by lia]
      simp +decide [revAt]
      ring_nf
      grind
    · have := iterate_derivative_rr hg (j - 1)
      aesop
  have hq_coeff2 :
      q.coeff 2 =
        ((g.natDegree - j - 1 + 2).descFactorial (g.natDegree - j - 1)) *
          ((j - 1).descFactorial (j - 1)) * g.coeff (j - 1) := by
    have hq_coeff2 :
        q.coeff 2 =
          ((g.natDegree - j - 1 + 2).descFactorial (g.natDegree - j - 1)) *
            q2.coeff (g.natDegree - j - 1 + 2) := by
      rw [Polynomial.coeff_iterate_derivative]
      norm_num [add_comm, add_left_comm, add_assoc]
    have hq_coeff2 : q2.coeff (g.natDegree - j - 1 + 2) = q1.coeff 0 := by
      have hq_coeff2 :
          q2.coeff (g.natDegree - j - 1 + 2) =
            q1.coeff (q1.natDegree - (g.natDegree - j - 1 + 2)) := by
        convert Polynomial.coeff_reverse _ _ using 2
        rw [Polynomial.revAt_le]
        rw [iterate_derivative_rr hg (j - 1) |>.2]
        lia
      have hq_coeff2 : q1.natDegree = g.natDegree - (j - 1) := by
        have := iterate_derivative_rr hg (j - 1)
        aesop
      change q1.reverse.coeff (g.natDegree - j - 1 + 2) = q1.coeff 0
      rw [Polynomial.coeff_reverse, hq_coeff2,
        Polynomial.revAt_le
          (by lia : g.natDegree - j - 1 + 2 ≤ g.natDegree - (j - 1)),
        show g.natDegree - (j - 1) - (g.natDegree - j - 1 + 2) = 0 from by lia]
    simp_all +decide [mul_assoc, Polynomial.coeff_iterate_derivative]
    rw [Polynomial.coeff_iterate_derivative]
    aesop
  have h_discriminant : 4 * q.coeff 0 * q.coeff 2 ≤ q.coeff 1 ^ 2 := by
    apply quad_discrim
    · exact hq_deg
    · apply (iterate_derivative_rr _ _).left
      apply reverse_rr
      · exact iterate_derivative_rr hg _ |>.1
      · rw [Polynomial.coeff_iterate_derivative]
        aesop
  simp_all +decide [Nat.descFactorial_eq_factorial_mul_choose]
  rcases j with _ | j <;> simp_all +decide [Nat.choose_succ_succ, Nat.factorial_succ]
  rw [Nat.cast_choose, Nat.cast_choose] at * <;> try linarith
  norm_num [Nat.succ_sub, Nat.factorial_succ] at *
  field_simp at *
  rw [Nat.sub_sub, Nat.cast_sub (by linarith)] at *
  rw [Nat.cast_sub (by linarith)] at *
  push_cast at *
  nlinarith [(by norm_cast : (j : ℝ) + 1 < g.natDegree)]

theorem newton_esymm_ineq (t : Multiset ℝ) {n m : ℕ} (hn : Multiset.card t = n)
    (hm0 : 0 < m) (hmn : m < n) :
    t.esymm (m - 1) * t.esymm (m + 1) * ((m + 1 : ℝ) * ((n - m + 1 : ℕ) : ℝ)) ≤
      t.esymm m ^ 2 * ((m : ℝ) * ((n - m : ℕ) : ℝ)) := by
  set g : Polynomial ℝ := (t.map (fun a => Polynomial.X + Polynomial.C a)).prod with hg_def
  have hg_natDegree : g.natDegree = n := by
    rw [Polynomial.natDegree_multiset_prod]
    · aesop
    · norm_num [Polynomial.X_add_C_ne_zero]
  have hg_card_roots : Multiset.card g.roots = n := by
    rw [Polynomial.roots_multiset_prod] at *
    · aesop
    · norm_num [Polynomial.X_add_C_ne_zero]
  have hg_coeff : ∀ k ≤ n, g.coeff k = t.esymm (n - k) := by
    intro k hk
    rw [← hn]
    rw [Multiset.prod_X_add_C_coeff]
    aesop
  convert newton_poly
      (show Multiset.card g.roots = g.natDegree from ?_) (show 0 < n - m from ?_)
      (show n - m < g.natDegree from ?_) using 1 <;>
    norm_num [hg_natDegree, hg_card_roots]
  · rw [hg_coeff, hg_coeff] <;> try lia
    rw [show n - (n - m - 1) = m + 1 by lia,
      show n - (n - m + 1) = m - 1 by lia]
    push_cast [Nat.cast_sub hmn.le]
    ring
  · rw [hg_coeff _ (Nat.sub_le _ _), Nat.cast_sub hmn.le]
    ring_nf
    rw [Nat.sub_sub_self hmn.le]
    ring
  · grind
  · exact ⟨pos_of_gt hmn, hm0⟩

end NewtonAux
