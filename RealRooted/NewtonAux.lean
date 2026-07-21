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

lemma iterate_derivative_rr {p : ℝ[X]} (hp : Multiset.card p.roots = p.natDegree)
    (k : ℕ) :
    Multiset.card (derivative^[k] p).roots = (derivative^[k] p).natDegree ∧
      (derivative^[k] p).natDegree = p.natDegree - k := by
  induction k with
  | zero => aesop
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    by_cases h : (derivative^[k] p).natDegree = 0
    · rw [Polynomial.eq_C_of_natDegree_eq_zero h]
      simp
      lia
    · have h_roots :
          Multiset.card (Polynomial.roots (Polynomial.derivative (derivative^[k] p))) ≥
            (derivative^[k] p).natDegree - 1 := by
        have := Polynomial.card_roots_le_derivative (derivative^[k] p)
        rw [ih.1] at this
        lia
      have h_deg :
          (Polynomial.derivative (derivative^[k] p)).natDegree ≤
            (derivative^[k] p).natDegree - 1 :=
        Polynomial.natDegree_derivative_le _
      have h_card :
          Multiset.card (Polynomial.roots (Polynomial.derivative (derivative^[k] p))) ≤
            (Polynomial.derivative (derivative^[k] p)).natDegree :=
        Polynomial.card_roots' _
      constructor
      · lia
      · rw [(derivative^[k] p).natDegree_derivative]
        rw [ih.2]
        lia

lemma reverse_rr {p : ℝ[X]} (hp : Multiset.card p.roots = p.natDegree)
    (h0 : p.coeff 0 ≠ 0) :
    Multiset.card p.reverse.roots = p.reverse.natDegree := by
  obtain ⟨rs, hrs⟩ :
      ∃ rs : Multiset ℝ,
        p = Polynomial.C p.leadingCoeff *
          Multiset.prod (Multiset.map (fun r => Polynomial.X - Polynomial.C r) rs) :=
    ⟨p.roots, Polynomial.Splits.eq_prod_roots <| Polynomial.splits_iff_card_roots.mpr hp⟩
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
      induction rs using Multiset.induction with
      | empty =>
          simp [Polynomial.reverse]
      | cons r rs ih =>
          induction (r ::ₘ rs) using Multiset.induction <;> norm_num at *
          tauto
    refine h_reverse.trans (congr_arg _ (congr_arg _ (Multiset.map_congr rfl fun x hx => ?_)))
    rcases eq_or_ne x 0 with rfl | hx'
    · exfalso
      rw [Polynomial.coeff_zero_eq_eval_zero] at h0
      exact h0 <| by
        rw [hrs]
        simp [hx, Polynomial.eval_multiset_prod]
    · exact Polynomial.funext fun y => by
        simp [hx', mul_sub, Polynomial.reverse]
        ring
  have h_factor_nonzero : ∀ x ∈ rs,
      ¬ x = 0 ∧ ¬ (Polynomial.X - Polynomial.C x⁻¹ : ℝ[X]) = 0 := by
    intro x hx
    refine ⟨?_, Polynomial.X_sub_C_ne_zero _⟩
    intro hx_zero
    rw [Polynomial.coeff_zero_eq_eval_zero] at h0
    apply h0
    rw [hrs]
    rw [hx_zero] at hx
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_multiset_prod,
      Multiset.map_map, Function.comp_apply, Polynomial.eval_sub, Polynomial.eval_X,
      mul_eq_zero]
    right
    exact Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨0, hx, by simp⟩)
  rw [h_reverse, Polynomial.roots_C_mul, Polynomial.natDegree_C_mul] <;> norm_num
  · rw [Polynomial.roots_multiset_prod] <;> norm_num [Polynomial.natDegree_multiset_prod]
    · rw [Polynomial.natDegree_multiset_prod] <;> norm_num [Polynomial.natDegree_mul']
      · rw [Multiset.map_congr rfl]
        intro x hx
        by_cases hx' : x = 0 <;> simp [hx', Polynomial.natDegree_mul']
      · intro x hx
        exact h_factor_nonzero x hx
    · intro x hx
      exact h_factor_nonzero x hx
  · rintro rfl
    contradiction
  · rintro rfl
    contradiction

lemma quad_discrim {q : ℝ[X]} (hd : q.natDegree = 2)
    (hq : Multiset.card q.roots = q.natDegree) :
    4 * q.coeff 0 * q.coeff 2 ≤ q.coeff 1 ^ 2 := by
  obtain ⟨x0, hx⟩ : ∃ x0, x0 ∈ q.roots :=
    Multiset.card_pos_iff_exists_mem.mp (by linarith)
  simp_all [Polynomial.eval_eq_sum_range, Finset.sum_range_succ']
  cases le_or_gt 0 (q.coeff 2) <;>
    nlinarith [sq_nonneg (q.coeff 1 + 2 * x0 * q.coeff 2)]

lemma newton_poly {g : ℝ[X]} (hg : Multiset.card g.roots = g.natDegree)
    {j : ℕ} (hj0 : 0 < j) (hj : j < g.natDegree) :
    g.coeff (j - 1) * g.coeff (j + 1) *
        ((j + 1 : ℝ) * ((g.natDegree - j + 1 : ℕ) : ℝ)) ≤
      g.coeff j ^ 2 * ((j : ℝ) * ((g.natDegree - j : ℕ) : ℝ)) := by
  revert j
  intro j hj0 hj
  by_contra h_neg
  have h_pos : 0 < g.coeff (j - 1) * g.coeff (j + 1) :=
    not_le.mp fun h =>
      h_neg <| by
        exact le_trans (mul_nonpos_of_nonpos_of_nonneg h <| by positivity) <|
          mul_nonneg (sq_nonneg _) <| by positivity
  set q1 := derivative^[j - 1] g
  set q2 := q1.reverse
  set q := derivative^[g.natDegree - j - 1] q2
  have hq_deg : q.natDegree = 2 := by
    have hq_deg : q2.natDegree = g.natDegree - (j - 1) := by
      have hq1_deg : q1.natDegree = g.natDegree - (j - 1) := by
        have := iterate_derivative_rr hg (j - 1)
        aesop
      have hq1_coeff0 : q1.coeff 0 ≠ 0 := by
        dsimp only [q1]
        rw [Polynomial.coeff_iterate_derivative, zero_add, nsmul_eq_mul,
          Nat.descFactorial_self, mul_ne_zero_iff]
        refine ⟨Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _), ?_⟩
        exact mul_ne_zero_iff.mp (ne_of_gt h_pos) |>.1
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
      · dsimp only [q1]
        rw [Polynomial.coeff_iterate_derivative, zero_add, nsmul_eq_mul,
          Nat.descFactorial_self, mul_ne_zero_iff]
        refine ⟨Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _), ?_⟩
        exact mul_ne_zero_iff.mp (ne_of_gt h_pos) |>.1
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
      · simp +zetaDelta only [Function.Embedding.coeFn_mk, tsub_le_iff_right] at *
        rw [if_pos (by lia)]
        rw [show g.natDegree - (j - 1) - (g.natDegree - j - 1) = 2 by lia]
      · have := iterate_derivative_rr hg (j - 1)
        aesop
    have hq_coeff0 :
        q1.coeff 2 = ((j + 1).descFactorial (j - 1)) * g.coeff (j + 1) := by
      rw [Polynomial.coeff_iterate_derivative]
      rw [show 2 + (j - 1) = j + 1 by lia, nsmul_eq_mul]
    grind
  have hq_coeff1 :
      q.coeff 1 =
        ((g.natDegree - j - 1 + 1).descFactorial (g.natDegree - j - 1)) *
          (j.descFactorial (j - 1)) * g.coeff j := by
    rw [Polynomial.coeff_iterate_derivative]
    rw [Polynomial.coeff_reverse]
    rw [Polynomial.coeff_iterate_derivative]
    rw [show q1.natDegree = g.natDegree - (j - 1) from ?_]
    · rcases j with _ | j
      · contradiction
      · have h_deg : g.natDegree - (j + 1 - 1) = (g.natDegree - (1 + (j + 1))) + 2 := by lia
        rw [h_deg]
        simp_all [add_comm]
        simp [revAt]
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
    have hq_coeff2' : q2.coeff (g.natDegree - j - 1 + 2) = q1.coeff 0 := by
      have hq_coeff2_1 :
          q2.coeff (g.natDegree - j - 1 + 2) =
            q1.coeff (q1.natDegree - (g.natDegree - j - 1 + 2)) := by
        convert Polynomial.coeff_reverse _ _ using 2
        rw [Polynomial.revAt_le]
        rw [iterate_derivative_rr hg (j - 1) |>.2]
        lia
      have hq_coeff2_2 : q1.natDegree = g.natDegree - (j - 1) := by
        have := iterate_derivative_rr hg (j - 1)
        aesop
      change q1.reverse.coeff (g.natDegree - j - 1 + 2) = q1.coeff 0
      rw [Polynomial.coeff_reverse, hq_coeff2_2,
        Polynomial.revAt_le
          (by lia : g.natDegree - j - 1 + 2 ≤ g.natDegree - (j - 1)),
        show g.natDegree - (j - 1) - (g.natDegree - j - 1 + 2) = 0 by lia]
    rw [hq_coeff2, hq_coeff2', Polynomial.coeff_iterate_derivative, nsmul_eq_mul]
    simp only [zero_add, mul_assoc]
  have h_discriminant : 4 * q.coeff 0 * q.coeff 2 ≤ q.coeff 1 ^ 2 := by
    apply quad_discrim
    · exact hq_deg
    · apply (iterate_derivative_rr _ _).left
      apply reverse_rr
      · exact iterate_derivative_rr hg _ |>.1
      · rw [Polynomial.coeff_iterate_derivative]
        aesop
  simp only [Nat.descFactorial_eq_factorial_mul_choose] at *
  rcases j with _ | j
  · contradiction
  · have hq0 : q.coeff 0 =
        ((g.natDegree - (j + 1) - 1).factorial : ℝ) * j.factorial *
          ((j + 2).choose j : ℝ) * g.coeff (j + 2) := by
      rw [hq_coeff0]
      simp only [Nat.choose_self, mul_one, add_tsub_cancel_right, Nat.cast_mul,
        mul_eq_mul_right_iff]
      left
      ring
    have hq1 : q.coeff 1 =
        ((g.natDegree - (j + 1) - 1).factorial : ℝ) *
          ((g.natDegree - (j + 1) - 1 + 1).choose (g.natDegree - (j + 1) - 1) : ℝ) *
          j.factorial * ((j + 1).choose j : ℝ) * g.coeff (j + 1) := by
      rw [hq_coeff1]
      simp only [Nat.choose_succ_self_right, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        add_tsub_cancel_right, mul_eq_mul_right_iff]
      left
      ring
    have hq2 : q.coeff 2 =
        ((g.natDegree - (j + 1) - 1).factorial : ℝ) *
          ((g.natDegree - (j + 1) - 1 + 2).choose (g.natDegree - (j + 1) - 1) : ℝ) *
          j.factorial * (j.choose j : ℝ) * g.coeff j := by
      rw [hq_coeff2]
      simp
    rw [hq0, hq1, hq2] at h_discriminant
    rw [Nat.cast_choose, Nat.cast_choose] at h_discriminant
    · norm_num [Nat.succ_sub, Nat.factorial_succ] at h_discriminant
      field_simp at h_discriminant
      rw [Nat.sub_sub] at h_discriminant
      rw [Nat.cast_sub (by linarith)] at h_discriminant
      push_cast at h_neg
      rw [Nat.cast_sub (by linarith)] at h_neg
      push_cast at h_neg h_discriminant
      nlinarith [(by norm_cast : (j : ℝ) + 1 < g.natDegree)]
    · linarith
    · linarith

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
  · rw [hg_coeff, hg_coeff]
    · rw [show n - (n - m - 1) = m + 1 by lia,
        show n - (n - m + 1) = m - 1 by lia]
      push_cast [Nat.cast_sub hmn.le]
      ring
    · lia
    · lia
  · rw [hg_coeff _ (Nat.sub_le _ _), Nat.cast_sub hmn.le]
    ring_nf
    rw [Nat.sub_sub_self hmn.le]
    ring
  · grind
  · exact ⟨pos_of_gt hmn, hm0⟩

end NewtonAux
