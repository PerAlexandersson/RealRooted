import RealRooted.Bezoutian

/-!
# Successor-degree Wronskian root gaps

The sign of the reversed Wronskian at the roots of a degree-`n + 1` polynomial
forces a root of its lower-degree companion in every consecutive root gap.
-/

open Polynomial

namespace RealRooted

/-- A positive reversed Wronskian at the roots of `q` places a root of `p` in
every consecutive root gap of `q`. -/
lemma has_gap_root_of_wronskian_pos_succ_atRoots {n : ℕ}
    {p q : ℝ[X]} (_hp_ne : p ≠ 0) (hq_pos : HasPosLeadingCoeff q)
    (hq_deg : q.natDegree = n + 1)
    (r : Fin (n + 1) → ℝ) (hr_mono : StrictMono r)
    (hr_roots : ∀ k, q.IsRoot (r k))
    (hW : ∀ k : Fin (n + 1), 0 < q.derivative.eval (r k) * p.eval (r k) -
      q.eval (r k) * p.derivative.eval (r k)) :
    ∀ k : Fin n, ∃ x, p.IsRoot x ∧ r k.castSucc < x ∧ x < r k.succ := by
  have h_sign_change_prod : ∀ k : Fin (n + 1),
      0 < p.eval (r k) * ∏ j ∈ Finset.erase Finset.univ k, (r k - r j) := by
    intro k
    have h_eval_deriv :
        q.derivative.eval (r k) =
          q.leadingCoeff * ∏ j ∈ Finset.erase Finset.univ k, (r k - r j) := by
      have h_eval_deriv : q = Polynomial.C q.leadingCoeff * ∏ j : Fin (n + 1),
        (Polynomial.X - Polynomial.C (r j)) := by
        convert Polynomial.splits_eq_C_mul_prod _ _ _ _ _
        · exact leadingCoeff_ne_zero.mp hq_pos.ne'
        · simp_all
        · simp_all
        · exact hr_mono.injective
      conv_lhs => rw [h_eval_deriv]
      exact Polynomial.eval_derivative_C_mul_prod_X_sub_C_univ_at_root
        q.leadingCoeff r k
    have hWk := hW k
    have hq_eval : q.eval (r k) = 0 := hr_roots k
    rw [hq_eval, zero_mul, sub_zero, h_eval_deriv, mul_assoc] at hWk
    have h_prod := pos_of_mul_pos_right hWk hq_pos.le
    grind
  have h_sign_change_pow : ∀ k : Fin (n + 1),
      0 < p.eval (r k) * (-1) ^ (n - k.val) := by
    intro k
    have h_prod_sign : ∏ j ∈ Finset.erase (Finset.univ : Finset (Fin (n + 1))) k,
      (r k - r j) = (-1) ^ (n - k.val) *
        (∏ j ∈ Finset.erase (Finset.univ : Finset (Fin (n + 1))) k,
          |r k - r j|) := by
      have h_prod_sign_abs : ∏ j ∈ Finset.erase (Finset.univ : Finset (Fin (n + 1))) k,
        (r k - r j) = ∏ j ∈ Finset.erase (Finset.univ : Finset (Fin (n + 1))) k,
          (-1) ^ (if k < j then 1 else 0) * |r k - r j| := by
        refine Finset.prod_congr rfl fun j hj ↦ ?_
        split_ifs with hjk
        · simp_all only [pow_one, neg_mul, one_mul]
          rw [abs_of_neg] <;> linarith [hr_mono hjk]
        · simp_all only [pow_zero, one_mul]
          rw [abs_of_nonneg (sub_nonneg.mpr (hr_mono.monotone (not_lt.mp hjk)))]
      rw [h_prod_sign_abs, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      simp only [Finset.sum_boole, Nat.cast_id, mul_eq_mul_right_iff]
      have hfilter : (Finset.univ.erase k).filter (fun x ↦ k < x) = Finset.Ioi k := by
        grind
      simp_all
    specialize h_sign_change_prod k
    rw [h_prod_sign] at h_sign_change_prod
    nlinarith [show 0 < ∏ j ∈ Finset.univ.erase k, |r k - r j| from
      Finset.prod_pos fun j hj ↦ abs_pos.mpr <| sub_ne_zero.mpr <|
        hr_mono.injective.ne (Finset.ne_of_mem_erase hj).symm]
  have h_sign_change_mul : ∀ k : Fin n,
      p.eval (r (Fin.castSucc k)) * p.eval (r (Fin.succ k)) < 0 := by
    intro k
    have h_sign_change_k :
        0 < p.eval (r (Fin.castSucc k)) * (-1) ^ (n - k.val) := by
      grind
    have h_sign_change_k_succ :
        0 < p.eval (r (Fin.succ k)) * (-1) ^ (n - (k.val + 1)) := by
      grind
    rw [show n - k = n - (k + 1) + 1 by lia] at h_sign_change_k
    let m := n - (k.val + 1)
    change 0 < p.eval (r (Fin.castSucc k)) * (-1) ^ (m + 1) at h_sign_change_k
    change 0 < p.eval (r (Fin.succ k)) * (-1) ^ m at h_sign_change_k_succ
    rcases Nat.even_or_odd m with hm | hm
    · have hm_pow : (-1 : ℝ) ^ m = 1 := hm.neg_one_pow
      have hm_succ_pow : (-1 : ℝ) ^ (m + 1) = -1 := by simp_all
      rw [hm_pow] at h_sign_change_k_succ
      rw [hm_succ_pow] at h_sign_change_k
      nlinarith
    · have hm_pow : (-1 : ℝ) ^ m = -1 := hm.neg_one_pow
      have hm_succ_pow : (-1 : ℝ) ^ (m + 1) = 1 := by simp_all
      rw [hm_pow] at h_sign_change_k_succ
      rw [hm_succ_pow] at h_sign_change_k
      nlinarith
  intro k
  have h_ivt : ∃ x ∈ Set.Ioo (r (Fin.castSucc k)) (r (Fin.succ k)), p.eval x = 0 := by
    have h_cont :
        ContinuousOn (fun x ↦ p.eval x)
          (Set.Icc (r (Fin.castSucc k)) (r (Fin.succ k))) :=
      p.continuous.continuousOn
    have hsign := h_sign_change_mul k
    rw [mul_neg_iff] at hsign
    have hle : r (Fin.castSucc k) ≤ r (Fin.succ k) :=
      hr_mono.monotone (Nat.le_succ _)
    rcases hsign with h | h
    · exact intermediate_value_Ioo' (by simp_all) h_cont (by simp_all)
    · exact intermediate_value_Ioo (by simp_all) h_cont (by simp_all)
  rcases h_ivt with ⟨c, hc_in, hc_root⟩
  exact ⟨c, hc_root, hc_in⟩

/-- The global reversed-Wronskian condition implies the root-local gap
condition. -/
lemma has_gap_root_of_wronskian_pos_succ {n : ℕ}
    {p q : ℝ[X]} (hp_ne : p ≠ 0) (hq_pos : HasPosLeadingCoeff q)
    (hq_deg : q.natDegree = n + 1)
    (hW : ∀ t : ℝ, 0 < q.derivative.eval t * p.eval t -
      q.eval t * p.derivative.eval t)
    (r : Fin (n + 1) → ℝ) (hr_mono : StrictMono r)
    (hr_roots : ∀ k, q.IsRoot (r k)) :
    ∀ k : Fin n, ∃ x, p.IsRoot x ∧ r k.castSucc < x ∧ x < r k.succ :=
  has_gap_root_of_wronskian_pos_succ_atRoots hp_ne hq_pos hq_deg r hr_mono hr_roots
    fun k ↦ hW (r k)

end RealRooted
