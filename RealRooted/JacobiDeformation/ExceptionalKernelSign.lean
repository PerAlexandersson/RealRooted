import RealRooted.JacobiDeformation.QuasiKernelSign

/-!
# The exceptional previous-Jacobi-root kernel sign

The quasi-Jacobi kernel sign is applied one dimension below the fixed Newton
weight degree.  The two omitted summands are handled directly.
-/

open Finset Polynomial
open scoped BigOperators

noncomputable section

namespace RealRooted.JacobiDeformation

/-- Two distinct roots of `p_(m-1)` cannot occur in the rank-two exceptional
case, since then that polynomial is the monic linear Jacobi polynomial. -/
theorem shiftedJacobiMonic_prev_two_roots_force_three
    {m : ℕ} (hm : 2 ≤ m) {α β r z : ℝ}
    (hα : -1 < α) (hβ : -1 < β)
    (hr : (shiftedJacobiMonic (m - 1) α β).IsRoot r)
    (hz : (shiftedJacobiMonic (m - 1) α β).IsRoot z) (hrz : r ≠ z) :
    3 ≤ m := by
  by_contra h
  have hm2 : m = 2 := by lia
  subst m
  have hsum : α + β + 2 ≠ 0 := by linarith
  rw [shiftedJacobiMonic_one α β hsum, Polynomial.IsRoot.def] at hr hz
  simp only [eval_sub, eval_X, eval_C] at hr hz
  apply hrz
  linarith

/-- At a root of `p_(n+2)`, the Favard recurrence gives the next Jacobi
evaluation in terms of `p_(n+1)`. -/
private theorem shiftedJacobiMonic_eval_succ_of_root
    (n : ℕ) {α β x : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (hx : (shiftedJacobiMonic (n + 2) α β).IsRoot x) :
    (shiftedJacobiMonic (n + 3) α β).eval x =
      -shiftedJacobiSubdiag (n + 2) α β *
        (shiftedJacobiMonic (n + 1) α β).eval x := by
  have hrec := congrArg (fun p : ℝ[X] => p.eval x)
    (shiftedJacobiMonic_recurrence (n + 2) α β (by lia) hα hβ)
  rw [Polynomial.IsRoot.def] at hx
  simp only [eval_sub, eval_mul, eval_C, eval_X] at hrec
  rw [hx, mul_zero, zero_sub] at hrec
  exact hrec

private theorem shiftedJacobiMonic_eval_prev_ne_zero_of_next_root
    (n : ℕ) {α β x : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (hx : (shiftedJacobiMonic (n + 2) α β).IsRoot x) :
    (shiftedJacobiMonic (n + 1) α β).eval x ≠ 0 := by
  intro hzero
  let hrec := shiftedJacobiMonic_satisfiesFavardRecurrence α β hα hβ
  have hsub : ∀ k : ℕ, 0 < shiftedJacobiSubdiag (k + 1) α β := by
    intro k
    exact shiftedJacobiSubdiag_pos (k + 1) (by lia) hα hβ
  have hcommon := noCommonRoot_succ_of_favard hrec hsub (n + 1) x
  apply hcommon
  · simpa only [Polynomial.IsRoot.def] using hzero
  · exact hx

/-- The fixed degree-`m` kernel has positive normalized value at roots of
`p_(m-1)`.  The `p_(m-1)` summand vanishes and the top summand is positive. -/
theorem exceptional_prev_root_kernel_sign
    {m : ℕ} (hm : 3 ≤ m) {α β δ r z : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : (shiftedJacobiMonic (m - 1) α β).IsRoot r)
    (hz : (shiftedJacobiMonic (m - 1) α β).IsRoot z) :
    (shiftedJacobiMonic m α β).eval r ≠ 0 ∧
      (shiftedJacobiMonic m α β).eval z ≠ 0 ∧
      0 <
        (∑ l : Fin (m + 1),
            kernelWeight m δ (α + β + 2) l *
              (shiftedJacobiMonic l α β).eval r *
              (shiftedJacobiMonic l α β).eval z /
                shiftedJacobiMonicNorm l α β) /
          ((shiftedJacobiMonic m α β).eval r *
            (shiftedJacobiMonic m α β).eval z) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 3 :=
    ⟨m - 3, (Nat.sub_add_cancel hm).symm⟩
  have hsub : 0 < shiftedJacobiSubdiag (n + 2) α β :=
    shiftedJacobiSubdiag_pos (n + 2) (by lia) hα hβ
  have hprev_r : (shiftedJacobiMonic (n + 1) α β).eval r ≠ 0 :=
    shiftedJacobiMonic_eval_prev_ne_zero_of_next_root n hα hβ (by simpa using hr)
  have hprev_z : (shiftedJacobiMonic (n + 1) α β).eval z ≠ 0 :=
    shiftedJacobiMonic_eval_prev_ne_zero_of_next_root n hα hβ (by simpa using hz)
  have hnext_r := shiftedJacobiMonic_eval_succ_of_root n hα hβ (by simpa using hr)
  have hnext_z := shiftedJacobiMonic_eval_succ_of_root n hα hβ (by simpa using hz)
  have hnext_r_ne : (shiftedJacobiMonic (n + 3) α β).eval r ≠ 0 := by
    rw [hnext_r]
    exact mul_ne_zero (neg_ne_zero.mpr hsub.ne') hprev_r
  have hnext_z_ne : (shiftedJacobiMonic (n + 3) α β).eval z ≠ 0 := by
    rw [hnext_z]
    exact mul_ne_zero (neg_ne_zero.mpr hsub.ne') hprev_z
  refine ⟨hnext_r_ne, hnext_z_ne, ?_⟩
  have hsmall := quasiJacobi_kernelWeight_sum_div_eval_prev_pos
    (q := n + 2) (m := n + 3) (by lia) (by lia) hα hβ hδ hδ1
    (τ := 0) (r := r) (z := z) (by simpa [quasiJacobiPolynomial] using hr)
    (by simpa [quasiJacobiPolynomial] using hz)
  let term : Fin (n + 4) → ℝ := fun l =>
    kernelWeight (n + 3) δ (α + β + 2) l *
      (shiftedJacobiMonic l α β).eval r *
      (shiftedJacobiMonic l α β).eval z /
        shiftedJacobiMonicNorm l α β
  have hsmall' : 0 <
      (∑ l : Fin (n + 2), term l.castSucc.castSucc) /
        ((shiftedJacobiMonic (n + 1) α β).eval r *
          (shiftedJacobiMonic (n + 1) α β).eval z) := by
    simpa [term] using hsmall
  have hsplit : (∑ l : Fin (n + 4), term l) =
      (∑ l : Fin (n + 2), term l.castSucc.castSucc) +
        term (Fin.last (n + 2)).castSucc + term (Fin.last (n + 3)) := by
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have hmiddle : term (Fin.last (n + 2)).castSucc = 0 := by
    simp [term, Fin.val_last, Fin.val_castSucc, Polynomial.IsRoot.def] at hr hz
    simp [term, Fin.val_last, Fin.val_castSucc, hr, hz]
  have htop : 0 < kernelWeight (n + 3) δ (α + β + 2) (n + 3) /
      shiftedJacobiMonicNorm (n + 3) α β := by
    apply div_pos
    · exact kernelWeight_pos (j := n + 3) (by rfl) hδ (by linarith)
    · exact shiftedJacobiMonicNorm_pos hα hβ (n + 3)
  have hprod :
      (shiftedJacobiMonic (n + 3) α β).eval r *
        (shiftedJacobiMonic (n + 3) α β).eval z =
      shiftedJacobiSubdiag (n + 2) α β ^ 2 *
        ((shiftedJacobiMonic (n + 1) α β).eval r *
          (shiftedJacobiMonic (n + 1) α β).eval z) := by
    rw [hnext_r, hnext_z]
    ring
  have hbase : 0 <
      (∑ l : Fin (n + 2), term l.castSucc.castSucc) /
        ((shiftedJacobiMonic (n + 3) α β).eval r *
          (shiftedJacobiMonic (n + 3) α β).eval z) := by
    rw [hprod]
    have hsq : 0 < shiftedJacobiSubdiag (n + 2) α β ^ 2 := sq_pos_of_pos hsub
    rw [show
      (∑ l : Fin (n + 2), term l.castSucc.castSucc) /
          (shiftedJacobiSubdiag (n + 2) α β ^ 2 *
            ((shiftedJacobiMonic (n + 1) α β).eval r *
              (shiftedJacobiMonic (n + 1) α β).eval z)) =
        ((∑ l : Fin (n + 2), term l.castSucc.castSucc) /
          ((shiftedJacobiMonic (n + 1) α β).eval r *
            (shiftedJacobiMonic (n + 1) α β).eval z)) /
          shiftedJacobiSubdiag (n + 2) α β ^ 2 by
      field_simp [hprev_r, hprev_z, hsub.ne']
      ring]
    exact div_pos hsmall' hsq
  have htopterm :
      term (Fin.last (n + 3)) /
          ((shiftedJacobiMonic (n + 3) α β).eval r *
            (shiftedJacobiMonic (n + 3) α β).eval z) =
        kernelWeight (n + 3) δ (α + β + 2) (n + 3) /
          shiftedJacobiMonicNorm (n + 3) α β := by
    simp [term, Fin.val_last]
    field_simp [hnext_r_ne, hnext_z_ne]
  have htotal :
      (∑ l : Fin (n + 4), term l) /
          ((shiftedJacobiMonic (n + 3) α β).eval r *
            (shiftedJacobiMonic (n + 3) α β).eval z) =
        (∑ l : Fin (n + 2), term l.castSucc.castSucc) /
          ((shiftedJacobiMonic (n + 3) α β).eval r *
            (shiftedJacobiMonic (n + 3) α β).eval z) +
          kernelWeight (n + 3) δ (α + β + 2) (n + 3) /
            shiftedJacobiMonicNorm (n + 3) α β := by
    rw [hsplit, hmiddle]
    rw [zero_add, add_div, htopterm]
  change 0 < (∑ l : Fin (n + 4), term l) /
    ((shiftedJacobiMonic (n + 3) α β).eval r *
      (shiftedJacobiMonic (n + 3) α β).eval z)
  rw [htotal]
  exact add_pos hbase htop

end RealRooted.JacobiDeformation
