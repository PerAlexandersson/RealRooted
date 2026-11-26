module

import RealRooted.JacobiDeformation.QuasiNodes
public import RealRooted.JacobiDeformation.SpectralKernel
import RealRooted.Favard

/-!
# Kernel signs at the critical coordinates

At a critical point `ξ` of `F_0 = J_{m,0}`, the two coordinates `r, z` of the
image value `ξ` have one of three shapes, and each needs its own sign of the
weighted kernel `∑_{j ≤ m} w_j p_j(r) p_j(z) / h_j`:

* ordinary: `p_{m-1}(r) / p_m(r) = p_{m-1}(z) / p_m(z) ≠ 0`, so `r, z` are
  roots of one quasi-Jacobi polynomial `p_m - τ p_{m-1}` with `τ ≠ 0`;
* exceptional: `p_{m-1}(r) = p_{m-1}(z) = 0`, where the sign is taken one
  dimension lower and the two omitted summands are handled directly;
* root: `r, z` are roots of `p_m`, where the top summand vanishes.

In each case the kernel has, strictly, the sign of the corresponding pair of
preceding Jacobi evaluations.  The first section extends the weighted
spectral sign of `RealRooted.JacobiDeformation.SpectralKernel` from indexed
node families to arbitrary pairs of quasi-Jacobi roots.
-/

public section

open Finset Polynomial

noncomputable section

namespace RealRooted.JacobiDeformation

/-! ## Kernel signs at arbitrary quasi-Jacobi roots

The ordered enumeration of all quasi-Jacobi roots removes the indexed-node
interface from the weighted spectral kernel sign.
-/

/-- The weighted Jacobi spectral kernel has positive normalized value at any
two roots of the quasi-Jacobi polynomial. -/
theorem quasiJacobi_kernelWeight_sum_div_eval_prev_pos
    {q m : ℕ} (hq : 2 ≤ q) (hm : q ≤ m) {α β τ δ r z : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : (quasiJacobiPolynomial q α β τ).IsRoot r)
    (hz : (quasiJacobiPolynomial q α β τ).IsRoot z) :
    0 <
      (∑ l : Fin q,
          kernelWeight m δ (α + β + 2) l *
            (shiftedJacobiMonic l α β).eval r *
            (shiftedJacobiMonic l α β).eval z /
              shiftedJacobiMonicNorm l α β) /
        ((shiftedJacobiMonic (q - 1) α β).eval r *
          (shiftedJacobiMonic (q - 1) α β).eval z) := by
  cases q with
  | zero => simp at hq
  | succ N =>
      have hN : 1 ≤ N := by lia
      obtain ⟨x, _, hx, hroots, hcomplete⟩ :=
        exists_quasiJacobiPolynomial_orderedRoots (q := N + 1) (by lia) hα hβ
      obtain ⟨i, hi⟩ := hcomplete r hr
      obtain ⟨j, hj⟩ := hcomplete z hz
      subst r
      subst z
      simpa using kernelWeight_quasiJacobi_sum_div_eval_prev_pos
        hN hm hα hβ hδ hδ1 x hx hroots i j

/-! ## Ordinary critical-kernel sign

This is the scalar nonroot case of the finite Jacobi kernel.  Equal nonzero
adjacent-Jacobi ratios turn the two points into roots of one quasi-Jacobi
polynomial; the quasi-root kernel sign then controls all
but the positive top summand.
-/

/-- At two points with one common nonzero adjacent-Jacobi ratio, the degree
`m` weighted kernel is positive after division by the two degree-`m` Jacobi
evaluations.  The weight degree remains `m` when the quasi-Jacobi sign theorem
is applied to its degree-`m` lower part. -/
theorem ordinaryJacobi_kernelWeight_sum_div_eval_top_pos
    {m : ℕ} (hm : 2 ≤ m) {α β δ r z : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hpr : (shiftedJacobiMonic m α β).eval r ≠ 0)
    (hpz : (shiftedJacobiMonic m α β).eval z ≠ 0)
    (hratio :
      (shiftedJacobiMonic (m - 1) α β).eval r /
          (shiftedJacobiMonic m α β).eval r =
        (shiftedJacobiMonic (m - 1) α β).eval z /
          (shiftedJacobiMonic m α β).eval z)
    (hratio_ne :
      (shiftedJacobiMonic (m - 1) α β).eval r /
          (shiftedJacobiMonic m α β).eval r ≠ 0) :
    0 <
      (∑ l : Fin (m + 1),
          kernelWeight m δ (α + β + 2) l *
              (shiftedJacobiMonic l α β).eval r *
                (shiftedJacobiMonic l α β).eval z /
            shiftedJacobiMonicNorm l α β) /
        ((shiftedJacobiMonic m α β).eval r *
          (shiftedJacobiMonic m α β).eval z) := by
  let K := (shiftedJacobiMonic (m - 1) α β).eval r /
    (shiftedJacobiMonic m α β).eval r
  have hK : K ≠ 0 := hratio_ne
  have hroot (x : ℝ) (hx : (shiftedJacobiMonic m α β).eval x ≠ 0)
      (hratio_x : (shiftedJacobiMonic (m - 1) α β).eval x /
        (shiftedJacobiMonic m α β).eval x = K) :
      (quasiJacobiPolynomial m α β K⁻¹).IsRoot x := by
    rw [div_eq_iff hx] at hratio_x
    simp only [IsRoot.def, quasiJacobiPolynomial, eval_sub, eval_mul, eval_C, hratio_x]
    field_simp [hK]
    ring
  have hlower := quasiJacobi_kernelWeight_sum_div_eval_prev_pos hm le_rfl
    hα hβ hδ hδ1 (hroot r hpr rfl) (hroot z hpz hratio.symm)
  have hden :
      (shiftedJacobiMonic (m - 1) α β).eval r *
          (shiftedJacobiMonic (m - 1) α β).eval z =
        K ^ 2 * ((shiftedJacobiMonic m α β).eval r *
          (shiftedJacobiMonic m α β).eval z) := by
    have hr := (div_eq_iff hpr).mp (show
      (shiftedJacobiMonic (m - 1) α β).eval r /
        (shiftedJacobiMonic m α β).eval r = K from rfl)
    have hz := (div_eq_iff hpz).mp hratio.symm
    rw [hr, hz]
    ring
  rw [hden, mul_comm (K ^ 2), ← div_div] at hlower
  have hbase := (div_pos_iff_of_pos_right (sq_pos_of_ne_zero hK)).mp hlower
  have htop : 0 < kernelWeight m δ (α + β + 2) m /
      shiftedJacobiMonicNorm m α β :=
    div_pos (kernelWeight_pos (j := m) le_rfl hδ (by linarith))
      (shiftedJacobiMonicNorm_pos hα hβ m)
  rw [Fin.sum_univ_castSucc, add_div]
  simp only [Fin.val_castSucc, Fin.val_last]
  refine add_pos hbase ?_
  convert htop using 1
  field_simp [hpr, hpz]

/-! ## Root critical-kernel sign

At two roots of the top monic Jacobi polynomial, the final summand of the
finite kernel vanishes.  The quasi-Jacobi sign with parameter zero
therefore gives the required preceding-evaluation normalization directly.
-/

/-- At two roots of the degree-`m` monic shifted-Jacobi polynomial, the
degree-`m` weighted kernel is positive after division by the preceding Jacobi
evaluations. -/
theorem rootJacobi_kernelWeight_sum_div_eval_prev_pos
    {m : ℕ} (hm : 2 ≤ m) {α β δ r z : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : (shiftedJacobiMonic m α β).IsRoot r)
    (hz : (shiftedJacobiMonic m α β).IsRoot z) :
    0 <
      (∑ l : Fin (m + 1),
          kernelWeight m δ (α + β + 2) l *
              (shiftedJacobiMonic l α β).eval r *
                (shiftedJacobiMonic l α β).eval z /
            shiftedJacobiMonicNorm l α β) /
        ((shiftedJacobiMonic (m - 1) α β).eval r *
          (shiftedJacobiMonic (m - 1) α β).eval z) := by
  have h := quasiJacobi_kernelWeight_sum_div_eval_prev_pos hm le_rfl
    hα hβ hδ hδ1 (τ := 0) (r := r) (z := z)
    (by simpa only [quasiJacobiPolynomial, C_0, zero_mul, sub_zero] using hr)
    (by simpa only [quasiJacobiPolynomial, C_0, zero_mul, sub_zero] using hz)
  rw [Fin.sum_univ_castSucc]
  simpa only [Fin.val_castSucc, Fin.val_last, hr.eq_zero, mul_zero, zero_mul,
    zero_div, add_zero] using h

/-! ## The exceptional previous-Jacobi-root kernel sign

The quasi-Jacobi kernel sign is applied one dimension below the fixed Newton
weight degree.  The two omitted summands are handled directly.
-/

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
  have hadd : n + 2 + 1 = n + 3 := by lia
  have hsub : n + 2 - 1 = n + 1 := by lia
  rw [hadd, hsub] at hrec
  simpa only [neg_mul] using hrec

private theorem shiftedJacobiMonic_eval_prev_ne_zero_of_next_root
    (n : ℕ) {α β x : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (hx : (shiftedJacobiMonic (n + 2) α β).IsRoot x) :
    (shiftedJacobiMonic (n + 1) α β).eval x ≠ 0 := by
  intro hzero
  let hrec := shiftedJacobiMonic_satisfiesFavardRecurrence α β hα hβ
  have hsub : ∀ k : ℕ, 0 < shiftedJacobiSubdiag (k + 1) α β :=
    fun k => shiftedJacobiSubdiag_pos (k + 1) (by lia) hα hβ
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
    simp only [Polynomial.IsRoot.def] at hr hz
    have hr' : (shiftedJacobiMonic (n + 2) α β).eval r = 0 := by
      simpa using hr
    have hz' : (shiftedJacobiMonic (n + 2) α β).eval z = 0 := by
      simpa using hz
    simp [term, Fin.val_last, Fin.val_castSucc, hr', hz']
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
    rw [hprod, mul_comm (shiftedJacobiSubdiag (n + 2) α β ^ 2), ← div_div]
    exact div_pos hsmall' (sq_pos_of_pos hsub)
  have htopterm :
      term (Fin.last (n + 3)) /
          ((shiftedJacobiMonic (n + 3) α β).eval r *
            (shiftedJacobiMonic (n + 3) α β).eval z) =
        kernelWeight (n + 3) δ (α + β + 2) (n + 3) /
          shiftedJacobiMonicNorm (n + 3) α β := by
    simp [term, Fin.val_last]
    field_simp [hnext_r_ne, hnext_z_ne]
  change 0 < (∑ l : Fin (n + 4), term l) /
    ((shiftedJacobiMonic (n + 3) α β).eval r *
      (shiftedJacobiMonic (n + 3) α β).eval z)
  rw [hsplit, hmiddle, add_zero, add_div, htopterm]
  exact add_pos hbase htop

end RealRooted.JacobiDeformation
