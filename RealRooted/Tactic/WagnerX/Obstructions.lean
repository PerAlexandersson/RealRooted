import RealRooted.Tactic.WagnerX.Core

/-!
# Wagner `X`-shift obstructions
-/

open Polynomial

namespace RealRooted

/-!
### The `X^2 * P'` derivative-lag obstruction

A natural attempt to extend the derivative-lag bridge to a cross-row lag is to
place the degree-matched tail `X^2 * f'`, where `f = P_{n-1}` and
`g = P_n` with `deg g = deg f + 1`, into proper position with the current row
`g`.  This fails in the generic OEIS case where `g.coeff 0 ≠ 0`: `X^2 * f'`
has `0` as a root, while a real-rooted nonnegative-coefficient `g` with
nonzero constant term has all roots strictly negative.
-/

/-- A nonnegative-coefficient real-rooted polynomial with nonzero constant term
has a strictly negative upper bound on its roots. -/
theorem exists_neg_root_upper_bound_of_nonneg_of_coeff_zero_ne {g : ℝ[X]}
    (hg0 : g ≠ 0)
    (hg : g.Splits)
    (hgnn : HasNonnegCoeffs g)
    (hdeg : 1 ≤ g.natDegree)
    (hgc0 : g.coeff 0 ≠ 0) :
    ∃ c : ℝ, c < 0 ∧ ∀ r ∈ g.roots, r ≤ c := by
  obtain ⟨r0, hr0_root, hr0_max⟩ :=
    exists_rightmost_root_of_isRealRooted hg0 hg hdeg
  have hr0_mem : r0 ∈ g.roots := (mem_roots hg0).mpr hr0_root
  have hr0_le : r0 ≤ 0 := roots_nonpos_of_nonneg_coeffs hg hgnn r0 hr0_mem
  have hr0_ne : r0 ≠ 0 := by
    intro h0
    apply hgc0
    have : g.eval 0 = 0 := by simpa [h0, IsRoot] using hr0_root
    rwa [coeff_zero_eq_eval_zero]
  exact ⟨r0, lt_of_le_of_ne hr0_le hr0_ne, hr0_max⟩

/-- Obstruction in the orientation `X^2 * f' ≪ g`. -/
theorem not_prec_X_sq_mul_derivative_left {f g : ℝ[X]}
    (hgnn : HasNonnegCoeffs g)
    (hgc0 : g.coeff 0 ≠ 0) :
    ¬ Prec (X ^ 2 * f.derivative) g := by
  intro h
  have hg0 : g ≠ 0 := right_ne_zero_of_prec h
  have hgs : g.Splits := right_splits_of_prec h
  have hXf_ne : X ^ 2 * f.derivative ≠ 0 := left_ne_zero_of_prec h
  have hfd : f.derivative ≠ 0 := by rr_nonzero
  have hXdeg : 2 ≤ (X ^ 2 * f.derivative).natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 X_ne_zero) hfd, natDegree_pow, natDegree_X]
    lia
  have hb1 := h.natDegree_le
  have hgdeg : 1 ≤ g.natDegree := by lia
  obtain ⟨c, hc_neg, hc_max⟩ :=
    exists_neg_root_upper_bound_of_nonneg_of_coeff_zero_ne hg0 hgs hgnn hgdeg hgc0
  have hall : ∀ r ∈ (X ^ 2 * f.derivative).roots, r ≤ c :=
    roots_le_of_prec_right h hc_max
  have hzero_root : (X ^ 2 * f.derivative).IsRoot 0 := by simp [IsRoot]
  have hzero_mem : (0 : ℝ) ∈ (X ^ 2 * f.derivative).roots :=
    (mem_roots hXf_ne).mpr hzero_root
  have hzc : (0 : ℝ) ≤ c := hall 0 hzero_mem
  linarith

/-- Obstruction in the orientation `g ≪ X^2 * f'` for the degree-matched
cross-row derivative tail. -/
theorem not_prec_X_sq_mul_derivative_right {f g : ℝ[X]}
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hdeg : f.natDegree + 1 = g.natDegree)
    (hf2 : 2 ≤ f.natDegree)
    (hgc0 : g.coeff 0 ≠ 0) :
    ¬ Prec g (X ^ 2 * f.derivative) := by
  intro h
  have hg0 : g ≠ 0 := left_ne_zero_of_prec h
  have hgs : g.Splits := left_splits_of_prec h
  have hXf_ne : X ^ 2 * f.derivative ≠ 0 := right_ne_zero_of_prec h
  have hfd : f.derivative ≠ 0 := by rr_nonzero
  have hXf_deg : (X ^ 2 * f.derivative).natDegree = g.natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 X_ne_zero) hfd, natDegree_pow, natDegree_X,
      f.natDegree_derivative]
    lia
  have hdeg_eq : g.natDegree = (X ^ 2 * f.derivative).natDegree := hXf_deg.symm
  have hdeg_pos : 1 ≤ (X ^ 2 * f.derivative).natDegree := by
    rw [hXf_deg]
    lia
  obtain ⟨uR, q, hq_eq, huR_root, huR_max, hint⟩ :=
    exists_rightmost_factor_interlaces_of_prec_sameDegree h hdeg_eq hdeg_pos
  have hXf_nn : HasNonnegCoeffs (X ^ 2 * f.derivative) := by
    have hrw : X ^ 2 * f.derivative = X * (X * f.derivative) := by ring
    rw [hrw]
    rr_nonneg_coeffs using hfnn.derivative
  have hXf_splits : (X ^ 2 * f.derivative).Splits := right_splits_of_prec h
  have huR_mem : uR ∈ (X ^ 2 * f.derivative).roots :=
    (mem_roots hXf_ne).mpr huR_root
  have huR_le : uR ≤ 0 :=
    roots_nonpos_of_nonneg_coeffs hXf_splits hXf_nn uR huR_mem
  have hzero_root : (X ^ 2 * f.derivative).IsRoot 0 := by simp [IsRoot]
  have hzero_mem : (0 : ℝ) ∈ (X ^ 2 * f.derivative).roots :=
    (mem_roots hXf_ne).mpr hzero_root
  have hzero_le : (0 : ℝ) ≤ uR := huR_max 0 hzero_mem
  have huR0 : uR = 0 := le_antisymm huR_le hzero_le
  have hq_eq' : X ^ 2 * f.derivative = X * q := by
    rw [hq_eq, huR0]
    simp
  have hq_alt : X * (X * f.derivative) = X * q := by
    rw [← hq_eq']
    ring
  have hq : q = X * f.derivative :=
    (mul_left_cancel₀ X_ne_zero hq_alt).symm
  have hq_ne : q ≠ 0 := by
    rw [hq]
    rr_nonzero
  have hq_zero_root : q.IsRoot 0 := by
    rw [hq]
    simp [IsRoot]
  have hq_zero_mem : (0 : ℝ) ∈ q.roots := (mem_roots hq_ne).mpr hq_zero_root
  have hgdeg : 1 ≤ g.natDegree := by lia
  obtain ⟨c, hc_neg, hc_max⟩ :=
    exists_neg_root_upper_bound_of_nonneg_of_coeff_zero_ne hg0 hgs hgnn hgdeg hgc0
  have hall : ∀ r ∈ q.roots, r ≤ c := roots_le_of_prec_right hint.toPrec hc_max
  have hzc : (0 : ℝ) ≤ c := hall 0 hq_zero_mem
  linarith


end RealRooted
