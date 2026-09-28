import RealRooted.JacobiDeformation.QuasiNodes
import RealRooted.JacobiDeformation.SpectralKernel

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
  let K :=
    (shiftedJacobiMonic (m - 1) α β).eval r /
      (shiftedJacobiMonic m α β).eval r
  let τ := K⁻¹
  let L := ∑ l : Fin m,
    kernelWeight m δ (α + β + 2) l *
        (shiftedJacobiMonic l α β).eval r *
          (shiftedJacobiMonic l α β).eval z /
      shiftedJacobiMonicNorm l α β
  have hKne : K ≠ 0 := by
    simpa only [K] using hratio_ne
  have hprev_r :
      (shiftedJacobiMonic (m - 1) α β).eval r =
        K * (shiftedJacobiMonic m α β).eval r := by
    dsimp only [K]
    field_simp [hpr]
  have hprev_z :
      (shiftedJacobiMonic (m - 1) α β).eval z =
        K * (shiftedJacobiMonic m α β).eval z := by
    change (shiftedJacobiMonic (m - 1) α β).eval z =
      ((shiftedJacobiMonic (m - 1) α β).eval r /
          (shiftedJacobiMonic m α β).eval r) *
        (shiftedJacobiMonic m α β).eval z
    rw [hratio]
    field_simp [hpz]
  have hroot_r : (quasiJacobiPolynomial m α β τ).IsRoot r := by
    change (quasiJacobiPolynomial m α β τ).eval r = 0
    rw [quasiJacobiPolynomial, eval_sub, eval_mul, eval_C, hprev_r]
    dsimp only [τ]
    field_simp [hKne]
    ring
  have hroot_z : (quasiJacobiPolynomial m α β τ).IsRoot z := by
    change (quasiJacobiPolynomial m α β τ).eval z = 0
    rw [quasiJacobiPolynomial, eval_sub, eval_mul, eval_C, hprev_z]
    dsimp only [τ]
    field_simp [hKne]
    ring
  have hlower :
      0 < L /
        ((shiftedJacobiMonic (m - 1) α β).eval r *
          (shiftedJacobiMonic (m - 1) α β).eval z) := by
    simpa only [L] using quasiJacobi_kernelWeight_sum_div_eval_prev_pos
      (q := m) (m := m) hm (le_refl m) hα hβ hδ hδ1 hroot_r hroot_z
  have hKsq : 0 < K * K := mul_self_pos.mpr hKne
  have hden :
      (shiftedJacobiMonic (m - 1) α β).eval r *
          (shiftedJacobiMonic (m - 1) α β).eval z =
        (K * K) *
          ((shiftedJacobiMonic m α β).eval r *
            (shiftedJacobiMonic m α β).eval z) := by
    rw [hprev_r, hprev_z]
    ring
  have hlower' :
      0 < L /
        ((shiftedJacobiMonic m α β).eval r *
          (shiftedJacobiMonic m α β).eval z) := by
    rw [hden] at hlower
    have hrewrite :
        L /
            ((shiftedJacobiMonic m α β).eval r *
              (shiftedJacobiMonic m α β).eval z) =
          (L /
              ((K * K) *
                ((shiftedJacobiMonic m α β).eval r *
                  (shiftedJacobiMonic m α β).eval z))) *
            (K * K) := by
      field_simp [hKne, hpr, hpz]
    rw [hrewrite]
    exact mul_pos hlower hKsq
  have hs : 0 < α + β + 2 := by linarith
  have htop :
      0 < kernelWeight m δ (α + β + 2) m /
        shiftedJacobiMonicNorm m α β :=
    div_pos (kernelWeight_pos (by simp) hδ hs)
      (shiftedJacobiMonicNorm_pos hα hβ m)
  have htop_eq :
      (kernelWeight m δ (α + β + 2) m *
          (shiftedJacobiMonic m α β).eval r *
            (shiftedJacobiMonic m α β).eval z /
          shiftedJacobiMonicNorm m α β) /
        ((shiftedJacobiMonic m α β).eval r *
          (shiftedJacobiMonic m α β).eval z) =
        kernelWeight m δ (α + β + 2) m /
          shiftedJacobiMonicNorm m α β := by
    field_simp [hpr, hpz, (shiftedJacobiMonicNorm_pos hα hβ m).ne']
  have hsplit :
      (∑ l : Fin (m + 1),
          kernelWeight m δ (α + β + 2) l *
              (shiftedJacobiMonic l α β).eval r *
                (shiftedJacobiMonic l α β).eval z /
            shiftedJacobiMonicNorm l α β) =
        L +
          kernelWeight m δ (α + β + 2) m *
              (shiftedJacobiMonic m α β).eval r *
                (shiftedJacobiMonic m α β).eval z /
            shiftedJacobiMonicNorm m α β := by
    rw [Fin.sum_univ_castSucc]
    rfl
  rw [hsplit, add_div, htop_eq]
  exact add_pos hlower' htop

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
  have hpmr : (shiftedJacobiMonic m α β).eval r = 0 := by
    simpa only [Polynomial.IsRoot.def] using hr
  have hpmz : (shiftedJacobiMonic m α β).eval z = 0 := by
    simpa only [Polynomial.IsRoot.def] using hz
  have hquasi_r : (quasiJacobiPolynomial m α β 0).IsRoot r := by
    change (quasiJacobiPolynomial m α β 0).eval r = 0
    simp [quasiJacobiPolynomial, hpmr]
  have hquasi_z : (quasiJacobiPolynomial m α β 0).IsRoot z := by
    change (quasiJacobiPolynomial m α β 0).eval z = 0
    simp [quasiJacobiPolynomial, hpmz]
  have hlower :
      0 <
        (∑ l : Fin m,
            kernelWeight m δ (α + β + 2) l *
                (shiftedJacobiMonic l α β).eval r *
                  (shiftedJacobiMonic l α β).eval z /
              shiftedJacobiMonicNorm l α β) /
          ((shiftedJacobiMonic (m - 1) α β).eval r *
            (shiftedJacobiMonic (m - 1) α β).eval z) :=
    quasiJacobi_kernelWeight_sum_div_eval_prev_pos
      (q := m) (m := m) hm (le_refl m) hα hβ hδ hδ1 hquasi_r hquasi_z
  have htop_zero :
      kernelWeight m δ (α + β + 2) m *
          (shiftedJacobiMonic m α β).eval r *
            (shiftedJacobiMonic m α β).eval z /
          shiftedJacobiMonicNorm m α β = 0 := by
    simp [hpmr]
  have hsplit :
      (∑ l : Fin (m + 1),
          kernelWeight m δ (α + β + 2) l *
              (shiftedJacobiMonic l α β).eval r *
                (shiftedJacobiMonic l α β).eval z /
            shiftedJacobiMonicNorm l α β) =
        (∑ l : Fin m,
            kernelWeight m δ (α + β + 2) l *
                (shiftedJacobiMonic l α β).eval r *
                  (shiftedJacobiMonic l α β).eval z /
              shiftedJacobiMonicNorm l α β) +
          kernelWeight m δ (α + β + 2) m *
              (shiftedJacobiMonic m α β).eval r *
                (shiftedJacobiMonic m α β).eval z /
              shiftedJacobiMonicNorm m α β := by
    rw [Fin.sum_univ_castSucc]
    rfl
  rw [hsplit, htop_zero, add_zero]
  exact hlower

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
      ]
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
    rw [add_zero, add_div, htopterm]
  change 0 < (∑ l : Fin (n + 4), term l) /
    ((shiftedJacobiMonic (n + 3) α β).eval r *
      (shiftedJacobiMonic (n + 3) α β).eval z)
  rw [htotal]
  exact add_pos hbase htop

end RealRooted.JacobiDeformation
