import RealRooted.PosCombo
import RealRooted.AffineFamily
import RealRooted.Tactic.Finish

/-!
# Wagner `X`-shift tactics

Small wrappers for the Wagner `X`-multiplication bridge used in plateau
positive-`t` lag recurrences.
-/

open Polynomial

namespace RealRooted

/-- Nonzero scalar form of the Wagner `X`-shift bridge.

From `f ≪ g` and nonnegative coefficients, Wagner (3) gives
`g ≪ X * f`.  This wrapper includes the nonzero scalar normalization used by
positive `c * X` lag terms. -/
theorem prec_C_mul_X_of_prec_of_nonneg {f g : ℝ[X]} {c : ℝ}
    (h : Prec f g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hc : c ≠ 0) :
    Prec g ((C c * X) * f) := by
  simpa [mul_assoc] using
    (prec_C_mul_right (prec_mul_X_of_prec_of_nonneg h hfnn hgnn) hc)

/-- Nonnegative-coefficient form of the common-factor Wagner `X` bridge.

This packages the standard root-nonpositive side conditions for applications
where both polynomials are multiplied by the same factor `X`. -/
theorem prec_mul_X_both_of_prec_of_nonneg {f g : ℝ[X]}
    (h : Prec f g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g) :
    Prec (X * f) (X * g) := by
  exact
    prec_mul_X_both_of_roots_nonpos h
      (roots_nonpos_of_nonneg_coeffs (left_splits_of_prec h) hfnn)
      (roots_nonpos_of_nonneg_coeffs (right_splits_of_prec h) hgnn)

/-- Derivative-lag bridge for later mixed lag recurrences.

If `f` is real-rooted with nonnegative coefficients, then `X * f'` is in
proper position with `X * f`.  This packages derivative interlacing together
with the Wagner common-`X` multiplication bridge. -/
theorem prec_X_mul_derivative_X_mul_self_of_splits_nonneg {f : ℝ[X]}
    (hf : f.Splits)
    (hdeg : 2 ≤ f.natDegree)
    (hfnn : HasNonnegCoeffs f) :
    Prec (X * f.derivative) (X * f) := by
  exact
    prec_mul_X_both_of_prec_of_nonneg
      (derivative_interlaces hf hdeg).toPrec hfnn.derivative hfnn

/-- Wagner derivative-gap-lag step.

If `f ≪ g`, then the derivative of `g` also precedes `g`, and Wagner's
positive-cone theorem puts `c g' + a f` before `g`.  Multiplication by `X`
then gives the active-row step behind recurrences
`P_{n+2} = X * (c_n P'_{n+1} + a_n P_n)`. -/
theorem prec_wagner_derivative_gap_lag_step {f g : ℝ[X]} {a c : ℝ}
    (h : Prec f g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hdeg : 2 ≤ g.natDegree)
    (ha : 0 < a)
    (hc : 0 < c) :
    Prec g (X * (C c * g.derivative + C a * f)) := by
  have hg_pos : HasPosLeadingCoeff g := hgnn.pos_leadingCoeff (right_ne_zero_of_prec h)
  have hf_pos : HasPosLeadingCoeff f := hfnn.pos_leadingCoeff (left_ne_zero_of_prec h)
  have hg_der_pos : HasPosLeadingCoeff g.derivative := hg_pos.derivative (by lia)
  have hder : Prec g.derivative g := (derivative_interlaces (right_splits_of_prec h) hdeg).toPrec
  have hnonneg : ∀ ap ∈ [(c, g.derivative), (a, f)], 0 ≤ ap.1 := by
    intro ap hap
    rcases List.mem_cons.mp hap with rfl | hap
    · exact hc.le
    rcases List.mem_cons.mp hap with rfl | hap
    · exact ha.le
    · cases hap
  have hprec : ∀ ap ∈ [(c, g.derivative), (a, f)], Prec ap.2 g := by
    intro ap hap
    rcases List.mem_cons.mp hap with rfl | hap
    · exact hder
    rcases List.mem_cons.mp hap with rfl | hap
    · exact h
    · cases hap
  have hpoly_pos :
      ∀ ap ∈ [(c, g.derivative), (a, f)], HasPosLeadingCoeff ap.2 := by
    intro ap hap
    rcases List.mem_cons.mp hap with rfl | hap
    · exact hg_der_pos
    rcases List.mem_cons.mp hap with rfl | hap
    · exact hf_pos
    · cases hap
  have hex : ∃ ap ∈ [(c, g.derivative), (a, f)], 0 < ap.1 :=
    ⟨(c, g.derivative), by simp, hc⟩
  have hsum_prec : Prec (weightedSum [(c, g.derivative), (a, f)]) g :=
    prec_weightedSum_right [(c, g.derivative), (a, f)] g
      hnonneg hprec hpoly_pos hex
  have hsum_nonneg : HasNonnegCoeffs (C c * g.derivative + C a * f) :=
    (nonnegCoeffs_C_mul hc.le hgnn.derivative).add (nonnegCoeffs_C_mul ha.le hfnn)
  have hsum_nonneg_weighted :
      HasNonnegCoeffs (weightedSum [(c, g.derivative), (a, f)]) := by
    simpa [weightedSum, add_assoc] using hsum_nonneg
  simpa [weightedSum, add_assoc] using
    (prec_mul_X_of_prec_of_nonneg hsum_prec hsum_nonneg_weighted hgnn)

/-- Scalar-left Wagner derivative-gap-lag step.

This is the same bridge as `prec_wagner_derivative_gap_lag_step`, but the
recurrence may be supplied in the unnormalized form
`d * p = X * (c * g' + a * f)`. -/
theorem prec_wagner_derivative_gap_lag_step_den {f g p : ℝ[X]} {a c d : ℝ}
    (h : Prec f g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hdeg : 2 ≤ g.natDegree)
    (ha : 0 < a)
    (hc : 0 < c)
    (hd : 0 < d)
    (hrec : C d * p = X * (C c * g.derivative + C a * f)) :
    Prec g p := by
  have hstep : Prec g (X * (C c * g.derivative + C a * f)) :=
    prec_wagner_derivative_gap_lag_step h hfnn hgnn hdeg ha hc
  have hscaled : Prec g (C d * p) := by
    simpa [hrec] using hstep
  have hscaled' : Prec g (C d⁻¹ * (C d * p)) :=
    prec_C_mul_right hscaled (inv_ne_zero hd.ne')
  have hnormalize : C d⁻¹ * (C d * p) = p := by
    rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hd.ne']
    simp
  simpa [hnormalize] using hscaled'

/-- Sequence induction for active Wagner derivative-gap-lag recurrences.

Use this after any exceptional startup rows have been absorbed into the base
case, so that the derivative and lag coefficients are both positive on the
indexed range. -/
theorem prec_wagner_derivative_gap_lag_sequence {P : Nat → ℝ[X]} {a c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (ha : ∀ n : Nat, 0 < a n)
    (hc : ∀ n : Nat, 0 < c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = X * (C (c n) * (P (n + 1)).derivative + C (a n) * P n)) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  intro n
  induction n with
  | zero =>
      exact hbase
  | succ n ih =>
      have hstep :
          Prec (P (n + 1))
            (X * (C (c n) * (P (n + 1)).derivative + C (a n) * P n)) :=
        prec_wagner_derivative_gap_lag_step
          ih (hnonneg n) (hnonneg (n + 1)) (hdeg n) (ha n) (hc n)
      simpa [← hrec n] using hstep

/-- Real-rootedness corollary for active Wagner derivative-gap-lag recurrences. -/
theorem isRealRooted_of_prec_wagner_derivative_gap_lag_sequence
    {P : Nat → ℝ[X]} {a c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (ha : ∀ n : Nat, 0 < a n)
    (hc : ∀ n : Nat, 0 < c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = X * (C (c n) * (P (n + 1)).derivative + C (a n) * P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  have hprec : ∀ n : Nat, Prec (P n) (P (n + 1)) :=
    prec_wagner_derivative_gap_lag_sequence hbase hnonneg hdeg ha hc hrec
  intro n
  cases n with
  | zero =>
      exact hbase.1
  | succ n =>
      exact (hprec n).2.1

/-- Sequence induction for scalar-left active Wagner derivative-gap-lag recurrences. -/
theorem prec_wagner_derivative_gap_lag_sequence_den
    {P : Nat → ℝ[X]} {a c d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (ha : ∀ n : Nat, 0 < a n)
    (hc : ∀ n : Nat, 0 < c n)
    (hd : ∀ n : Nat, 0 < d n)
    (hrec : ∀ n : Nat,
      C (d n) * P (n + 2) =
        X * (C (c n) * (P (n + 1)).derivative + C (a n) * P n)) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  intro n
  induction n with
  | zero =>
      exact hbase
  | succ n ih =>
      exact
        prec_wagner_derivative_gap_lag_step_den
          ih (hnonneg n) (hnonneg (n + 1)) (hdeg n) (ha n) (hc n) (hd n)
          (hrec n)

/-- Real-rootedness corollary for scalar-left active Wagner gap-lag recurrences. -/
theorem isRealRooted_of_prec_wagner_derivative_gap_lag_sequence_den
    {P : Nat → ℝ[X]} {a c d : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (hdeg : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (ha : ∀ n : Nat, 0 < a n)
    (hc : ∀ n : Nat, 0 < c n)
    (hd : ∀ n : Nat, 0 < d n)
    (hrec : ∀ n : Nat,
      C (d n) * P (n + 2) =
        X * (C (c n) * (P (n + 1)).derivative + C (a n) * P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  have hprec : ∀ n : Nat, Prec (P n) (P (n + 1)) :=
    prec_wagner_derivative_gap_lag_sequence_den hbase hnonneg hdeg ha hc hd hrec
  intro n
  cases n with
  | zero =>
      exact hbase.1
  | succ n =>
      exact (hprec n).2.1

/-!
### The `X^2 * P'` derivative-lag obstruction

A natural attempt to extend the derivative-lag bridge to a cross-row lag is to
try to place the degree-matched tail `X^2 * f'`, where `f = P_{n-1}` and
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
    have : g.eval 0 = 0 := by
      simpa [h0, IsRoot] using hr0_root
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
  have hfd : f.derivative ≠ 0 := by
    intro hz
    simp [hz] at hXf_ne
  have hXdeg : 2 ≤ (X ^ 2 * f.derivative).natDegree := by
    rw [natDegree_mul (pow_ne_zero 2 X_ne_zero) hfd, natDegree_pow, natDegree_X]
    lia
  obtain ⟨hb1, _⟩ := natDegree_bounds_of_prec h
  have hgdeg : 1 ≤ g.natDegree := by
    lia
  obtain ⟨c, hc_neg, hc_max⟩ :=
    exists_neg_root_upper_bound_of_nonneg_of_coeff_zero_ne hg0 hgs hgnn hgdeg hgc0
  have hall : ∀ r ∈ (X ^ 2 * f.derivative).roots, r ≤ c :=
    roots_le_of_prec_right h hc_max
  have hzero_root : (X ^ 2 * f.derivative).IsRoot 0 := by
    simp [IsRoot]
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
  have hfd : f.derivative ≠ 0 := by
    intro hz
    simp [hz] at hXf_ne
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
    have hrw : X ^ 2 * f.derivative = X * (X * f.derivative) := by
      ring
    rw [hrw]
    exact hfnn.derivative.X_mul.X_mul
  have hXf_splits : (X ^ 2 * f.derivative).Splits := right_splits_of_prec h
  have huR_mem : uR ∈ (X ^ 2 * f.derivative).roots :=
    (mem_roots hXf_ne).mpr huR_root
  have huR_le : uR ≤ 0 :=
    roots_nonpos_of_nonneg_coeffs hXf_splits hXf_nn uR huR_mem
  have hzero_root : (X ^ 2 * f.derivative).IsRoot 0 := by
    simp [IsRoot]
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
    exact mul_ne_zero X_ne_zero hfd
  have hq_zero_root : q.IsRoot 0 := by
    rw [hq]
    simp [IsRoot]
  have hq_zero_mem : (0 : ℝ) ∈ q.roots := (mem_roots hq_ne).mpr hq_zero_root
  have hgdeg : 1 ≤ g.natDegree := by
    lia
  obtain ⟨c, hc_neg, hc_max⟩ :=
    exists_neg_root_upper_bound_of_nonneg_of_coeff_zero_ne hg0 hgs hgnn hgdeg hgc0
  have hall : ∀ r ∈ q.roots, r ≤ c := roots_le_of_prec_right hint.toPrec hc_max
  have hzc : (0 : ℝ) ≤ c := hall 0 hq_zero_mem
  linarith

/-- Positive scalar-current plus nonnegative `X`-lag plateau step.

This is the abstract step behind recurrences such as
`P_n = P_{n-1} + t P_{n-2}` and `P_n = 2 P_{n-1} + t P_{n-2}`. -/
theorem prec_pos_X_lag_combo_of_prec_nonneg {f g : ℝ[X]} {a c : ℝ}
    (h : Prec f g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (ha : 0 < a)
    (hc : 0 ≤ c) :
    Prec g (C a * g + (C c * X) * f) := by
  have hg_pos : HasPosLeadingCoeff g := hgnn.pos_leadingCoeff (right_ne_zero_of_prec h)
  have hXf_pos : HasPosLeadingCoeff (X * f) :=
    (hfnn.pos_leadingCoeff (left_ne_zero_of_prec h)).X_mul
  have hX : Prec g (X * f) := prec_mul_X_of_prec_of_nonneg h hfnn hgnn
  have hself : Prec g g := prec_refl (right_ne_zero_of_prec h) (right_splits_of_prec h)
  have hnonneg : ∀ ap ∈ [(a, g), (c, X * f)], 0 ≤ ap.1 := by
    intro ap hap
    rcases List.mem_cons.mp hap with rfl | hap
    · exact ha.le
    rcases List.mem_cons.mp hap with rfl | hap
    · exact hc
    · cases hap
  have hprec : ∀ ap ∈ [(a, g), (c, X * f)], Prec g ap.2 := by
    intro ap hap
    rcases List.mem_cons.mp hap with rfl | hap
    · exact hself
    rcases List.mem_cons.mp hap with rfl | hap
    · exact hX
    · cases hap
  have hpoly_pos :
      ∀ ap ∈ [(a, g), (c, X * f)], HasPosLeadingCoeff ap.2 := by
    intro ap hap
    rcases List.mem_cons.mp hap with rfl | hap
    · exact hg_pos
    rcases List.mem_cons.mp hap with rfl | hap
    · exact hXf_pos
    · cases hap
  have hex : ∃ ap ∈ [(a, g), (c, X * f)], 0 < ap.1 := by
    exact ⟨(a, g), by simp, ha⟩
  have hsum : Prec g (weightedSum [(a, g), (c, X * f)]) :=
    prec_weightedSum_left_of_common_left
      [(a, g), (c, X * f)] g hnonneg hprec hg_pos hpoly_pos hex
  simpa [weightedSum, mul_assoc, add_assoc] using hsum

/-- Sequence induction for scalar positive-current plus nonnegative `X`-lag
recurrences.  This is plateau-safe: it never converts the previous `Prec`
certificate to a differ-by-one `Interlaces` certificate. -/
theorem prec_pos_X_lag_combo_sequence {P : Nat → ℝ[X]} {a c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (ha : ∀ n : Nat, 0 < a n)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = C (a n) * P (n + 1) + (C (c n) * X) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  intro n
  induction n with
  | zero =>
      exact hbase
  | succ n ih =>
      have hstep :
          Prec (P (n + 1)) (C (a n) * P (n + 1) + (C (c n) * X) * P n) :=
        prec_pos_X_lag_combo_of_prec_nonneg
          ih (hnonneg n) (hnonneg (n + 1)) (ha n) (hc n)
      simpa [← hrec n] using hstep

/-- Real-rootedness corollary of scalar positive-current plus nonnegative
`X`-lag sequence induction. -/
theorem isRealRooted_of_prec_pos_X_lag_combo_sequence {P : Nat → ℝ[X]}
    {a c : Nat → ℝ}
    (hbase : Prec (P 0) (P 1))
    (hnonneg : ∀ n : Nat, HasNonnegCoeffs (P n))
    (ha : ∀ n : Nat, 0 < a n)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = C (a n) * P (n + 1) + (C (c n) * X) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  have hprec : ∀ n : Nat, Prec (P n) (P (n + 1)) :=
    prec_pos_X_lag_combo_sequence hbase hnonneg ha hc hrec
  intro n
  cases n with
  | zero =>
      exact hbase.1
  | succ n =>
      exact (hprec n).2.1

namespace Tactic

syntax (name := rr_prec_mul_X)
  "rr_prec_mul_X" " using "
    "proper" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term :
  tactic

syntax (name := rr_prec_mul_X_both)
  "rr_prec_mul_X_both" " using "
    "proper" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term :
  tactic

syntax (name := rr_prec_C_mul_X)
  "rr_prec_C_mul_X" " using "
    "proper" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "coeff_ne" ":=" term :
  tactic

syntax (name := rr_prec_C_mul_X_pos)
  "rr_prec_C_mul_X" " using "
    "proper" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "coeff_pos" ":=" term :
  tactic

syntax (name := rr_prec_X_derivative_X_self)
  "rr_prec_X_derivative_X_self" " using "
    "splits" ":=" term ","
    "degree_two" ":=" term ","
    "nonneg_coeffs" ":=" term :
  tactic

syntax (name := rr_prec_wagner_derivative_gap_lag)
  "rr_prec_wagner_derivative_gap_lag" " using "
    "proper" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "degree_two" ":=" term ","
    "lag_coeff_pos" ":=" term ","
    "derivative_coeff_pos" ":=" term :
  tactic

syntax (name := rr_prec_wagner_derivative_gap_lag_den)
  "rr_prec_wagner_derivative_gap_lag_den" " using "
    "proper" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "degree_two" ":=" term ","
    "lag_coeff_pos" ":=" term ","
    "derivative_coeff_pos" ":=" term ","
    "denom_pos" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_prec_wagner_derivative_gap_lag_sequence)
  "rr_prec_wagner_derivative_gap_lag_sequence" " using "
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "lag_coeff_pos" ":=" term ","
    "derivative_coeff_pos" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_prec_wagner_derivative_gap_lag_sequence_realrooted)
  "rr_prec_wagner_derivative_gap_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "lag_coeff_pos" ":=" term ","
    "derivative_coeff_pos" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_prec_wagner_derivative_gap_lag_sequence_den)
  "rr_prec_wagner_derivative_gap_lag_sequence_den" " using "
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "lag_coeff_pos" ":=" term ","
    "derivative_coeff_pos" ":=" term ","
    "denom_pos" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_prec_wagner_derivative_gap_lag_sequence_den_realrooted)
  "rr_prec_wagner_derivative_gap_lag_sequence_den_realrooted" " using "
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "degree_two" ":=" term ","
    "lag_coeff_pos" ":=" term ","
    "derivative_coeff_pos" ":=" term ","
    "denom_pos" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_prec_pos_X_lag_combo)
  "rr_prec_pos_X_lag_combo" " using "
    "proper" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "current_coeff_pos" ":=" term ","
    "lag_coeff_nonneg" ":=" term :
  tactic

syntax (name := rr_prec_pos_X_lag_combo_lag_pos)
  "rr_prec_pos_X_lag_combo" " using "
    "proper" ":=" term ","
    "left_nonneg" ":=" term ","
    "right_nonneg" ":=" term ","
    "current_coeff_pos" ":=" term ","
    "lag_coeff_pos" ":=" term :
  tactic

syntax (name := rr_prec_pos_X_lag_sequence)
  "rr_prec_pos_X_lag_sequence" " using "
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "current_coeff_pos" ":=" term ","
    "lag_coeff_nonneg" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_prec_pos_X_lag_sequence_auto)
  "rr_prec_pos_X_lag_sequence_auto" " using "
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_prec_pos_X_lag_sequence_realrooted)
  "rr_prec_pos_X_lag_sequence_realrooted" " using "
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "current_coeff_pos" ":=" term ","
    "lag_coeff_nonneg" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_prec_pos_X_lag_sequence_realrooted_auto)
  "rr_prec_pos_X_lag_sequence_realrooted_auto" " using "
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_prec_pos_X_unit_lag_sequence_auto)
  "rr_prec_pos_X_unit_lag_sequence_auto" " using "
    "current_coeff" ":=" term ","
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_prec_pos_X_unit_lag_sequence_realrooted_auto)
  "rr_prec_pos_X_unit_lag_sequence_realrooted_auto" " using "
    "current_coeff" ":=" term ","
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_prec_pos_X_same_coeff_sequence_auto)
  "rr_prec_pos_X_same_coeff_sequence_auto" " using "
    "shared_coeff" ":=" term ","
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_prec_pos_X_same_coeff_sequence_realrooted_auto)
  "rr_prec_pos_X_same_coeff_sequence_realrooted_auto" " using "
    "shared_coeff" ":=" term ","
    "base" ":=" term ","
    "nonneg_coeffs" ":=" term ","
    "recurrence" ":=" term :
  tactic

syntax (name := rr_wagner_pos) "rr_wagner_pos" : tactic

syntax (name := rr_wagner_pos_seq) "rr_wagner_pos_seq" : term

syntax (name := rr_wagner_recurrence_seq) "rr_wagner_recurrence_seq " term : term

macro_rules
  | `(tactic| rr_wagner_pos) =>
      `(tactic| rr_side_pos)
  | `(rr_wagner_pos_seq) =>
      `(fun n => by rr_wagner_pos)
  | `(rr_wagner_recurrence_seq $hrec:term) =>
      `(fun n => by simpa using $hrec n)

macro_rules
  | `(tactic|
      rr_prec_mul_X using
        proper := $hprec:term,
        left_nonneg := $hfnn:term,
        right_nonneg := $hgnn:term) =>
      `(tactic|
        exact RealRooted.prec_mul_X_of_prec_of_nonneg $hprec $hfnn $hgnn)
  | `(tactic|
      rr_prec_mul_X_both using
        proper := $hprec:term,
        left_nonneg := $hfnn:term,
        right_nonneg := $hgnn:term) =>
      `(tactic|
        exact RealRooted.prec_mul_X_both_of_prec_of_nonneg $hprec $hfnn $hgnn)
  | `(tactic|
      rr_prec_C_mul_X using
        proper := $hprec:term,
        left_nonneg := $hfnn:term,
        right_nonneg := $hgnn:term,
        coeff_ne := $hc:term) =>
      `(tactic|
        exact RealRooted.prec_C_mul_X_of_prec_of_nonneg $hprec $hfnn $hgnn $hc)
  | `(tactic|
      rr_prec_C_mul_X using
        proper := $hprec:term,
        left_nonneg := $hfnn:term,
        right_nonneg := $hgnn:term,
        coeff_pos := $hc:term) =>
      `(tactic|
        exact RealRooted.prec_C_mul_X_of_prec_of_nonneg
          $hprec $hfnn $hgnn ($hc).ne')
  | `(tactic|
      rr_prec_X_derivative_X_self using
        splits := $hf:term,
        degree_two := $hdeg:term,
        nonneg_coeffs := $hfnn:term) =>
      `(tactic|
        exact RealRooted.prec_X_mul_derivative_X_mul_self_of_splits_nonneg
          $hf $hdeg $hfnn)
  | `(tactic|
      rr_prec_wagner_derivative_gap_lag using
        proper := $hprec:term,
        left_nonneg := $hfnn:term,
        right_nonneg := $hgnn:term,
        degree_two := $hdeg:term,
        lag_coeff_pos := $ha:term,
        derivative_coeff_pos := $hc:term) =>
      `(tactic|
        exact RealRooted.prec_wagner_derivative_gap_lag_step
          $hprec $hfnn $hgnn $hdeg $ha $hc)
  | `(tactic|
      rr_prec_wagner_derivative_gap_lag_den using
        proper := $hprec:term,
        left_nonneg := $hfnn:term,
        right_nonneg := $hgnn:term,
        degree_two := $hdeg:term,
        lag_coeff_pos := $ha:term,
        derivative_coeff_pos := $hc:term,
        denom_pos := $hd:term,
        recurrence := $hrec:term) =>
      `(tactic|
        exact RealRooted.prec_wagner_derivative_gap_lag_step_den
          $hprec $hfnn $hgnn $hdeg $ha $hc $hd $hrec)
  | `(tactic|
      rr_prec_wagner_derivative_gap_lag_sequence using
        base := $hbase:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg:term,
        lag_coeff_pos := $ha:term,
        derivative_coeff_pos := $hc:term,
        recurrence := $hrec:term) =>
      `(tactic|
        exact RealRooted.prec_wagner_derivative_gap_lag_sequence
          $hbase $hnonneg $hdeg $ha $hc $hrec)
  | `(tactic|
      rr_prec_wagner_derivative_gap_lag_sequence_realrooted using
        base := $hbase:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg:term,
        lag_coeff_pos := $ha:term,
        derivative_coeff_pos := $hc:term,
        recurrence := $hrec:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_prec_wagner_derivative_gap_lag_sequence
            $hbase $hnonneg $hdeg $ha $hc $hrec))
  | `(tactic|
      rr_prec_wagner_derivative_gap_lag_sequence_den using
        base := $hbase:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg:term,
        lag_coeff_pos := $ha:term,
        derivative_coeff_pos := $hc:term,
        denom_pos := $hd:term,
        recurrence := $hrec:term) =>
      `(tactic|
        exact RealRooted.prec_wagner_derivative_gap_lag_sequence_den
          $hbase $hnonneg $hdeg $ha $hc $hd $hrec)
  | `(tactic|
      rr_prec_wagner_derivative_gap_lag_sequence_den_realrooted using
        base := $hbase:term,
        nonneg_coeffs := $hnonneg:term,
        degree_two := $hdeg:term,
        lag_coeff_pos := $ha:term,
        derivative_coeff_pos := $hc:term,
        denom_pos := $hd:term,
        recurrence := $hrec:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_prec_wagner_derivative_gap_lag_sequence_den
            $hbase $hnonneg $hdeg $ha $hc $hd $hrec))
  | `(tactic|
      rr_prec_pos_X_lag_combo using
        proper := $hprec:term,
        left_nonneg := $hfnn:term,
        right_nonneg := $hgnn:term,
        current_coeff_pos := $ha:term,
        lag_coeff_nonneg := $hc:term) =>
      `(tactic|
        rr_first_exact_or_simpa_mul_add_assoc
          (RealRooted.prec_pos_X_lag_combo_of_prec_nonneg
            $hprec $hfnn $hgnn $ha $hc),
          (RealRooted.prec_pos_X_lag_combo_of_prec_nonneg
            $hprec $hfnn $hgnn $ha $hc))
  | `(tactic|
      rr_prec_pos_X_lag_combo using
        proper := $hprec:term,
        left_nonneg := $hfnn:term,
        right_nonneg := $hgnn:term,
        current_coeff_pos := $ha:term,
        lag_coeff_pos := $hc:term) =>
      `(tactic|
        rr_first_exact_or_simpa_mul_add_assoc
          (RealRooted.prec_pos_X_lag_combo_of_prec_nonneg
            $hprec $hfnn $hgnn $ha ($hc).le),
          (RealRooted.prec_pos_X_lag_combo_of_prec_nonneg
            $hprec $hfnn $hgnn $ha ($hc).le))
  | `(tactic|
      rr_prec_pos_X_lag_sequence using
        base := $hbase:term,
        nonneg_coeffs := $hnonneg:term,
        current_coeff_pos := $ha:term,
        lag_coeff_nonneg := $hc:term,
        recurrence := $hrec:term) =>
      `(tactic|
        exact RealRooted.prec_pos_X_lag_combo_sequence
          $hbase $hnonneg $ha $hc $hrec)
  | `(tactic|
      rr_prec_pos_X_lag_sequence_auto using
        base := $hbase:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term) =>
      `(tactic|
        rr_first_exact
          (RealRooted.prec_pos_X_lag_combo_sequence
            $hbase $hnonneg rr_wagner_pos_seq rr_wagner_pos_seq $hrec),
          (RealRooted.prec_pos_X_lag_combo_sequence
              (a := fun _ => (1 : ℝ)) (c := fun _ => (1 : ℝ))
              $hbase $hnonneg rr_wagner_pos_seq rr_wagner_pos_seq
              (rr_wagner_recurrence_seq $hrec)))
  | `(tactic|
      rr_prec_pos_X_lag_sequence_realrooted using
        base := $hbase:term,
        nonneg_coeffs := $hnonneg:term,
        current_coeff_pos := $ha:term,
        lag_coeff_nonneg := $hc:term,
        recurrence := $hrec:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_prec_pos_X_lag_combo_sequence
            $hbase $hnonneg $ha $hc $hrec))
  | `(tactic|
      rr_prec_pos_X_lag_sequence_realrooted_auto using
        base := $hbase:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term) =>
      `(tactic|
        rr_first_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_prec_pos_X_lag_combo_sequence
            $hbase $hnonneg rr_wagner_pos_seq rr_wagner_pos_seq $hrec),
          (RealRooted.isRealRooted_of_prec_pos_X_lag_combo_sequence
            (a := fun _ => (1 : ℝ)) (c := fun _ => (1 : ℝ))
            $hbase $hnonneg rr_wagner_pos_seq rr_wagner_pos_seq
            (rr_wagner_recurrence_seq $hrec)))
  | `(tactic|
      rr_prec_pos_X_unit_lag_sequence_auto using
        current_coeff := $a:term,
        base := $hbase:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term) =>
      `(tactic|
        exact RealRooted.prec_pos_X_lag_combo_sequence
          (a := $a) (c := fun _ => (1 : ℝ))
          $hbase $hnonneg rr_wagner_pos_seq rr_wagner_pos_seq
          (rr_wagner_recurrence_seq $hrec))
  | `(tactic|
      rr_prec_pos_X_unit_lag_sequence_realrooted_auto using
        current_coeff := $a:term,
        base := $hbase:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_prec_pos_X_lag_combo_sequence
            (a := $a) (c := fun _ => (1 : ℝ))
            $hbase $hnonneg rr_wagner_pos_seq rr_wagner_pos_seq
            (rr_wagner_recurrence_seq $hrec)))
  | `(tactic|
      rr_prec_pos_X_same_coeff_sequence_auto using
        shared_coeff := $c:term,
        base := $hbase:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term) =>
      `(tactic|
        exact RealRooted.prec_pos_X_lag_combo_sequence
          (a := $c) (c := $c)
          $hbase $hnonneg rr_wagner_pos_seq rr_wagner_pos_seq
          (rr_wagner_recurrence_seq $hrec))
  | `(tactic|
      rr_prec_pos_X_same_coeff_sequence_realrooted_auto using
        shared_coeff := $c:term,
        base := $hbase:term,
        nonneg_coeffs := $hnonneg:term,
        recurrence := $hrec:term) =>
      `(tactic|
        rr_exact_realrooted_sequence_or_projection
          (RealRooted.isRealRooted_of_prec_pos_X_lag_combo_sequence
            (a := $c) (c := $c)
            $hbase $hnonneg rr_wagner_pos_seq rr_wagner_pos_seq
            (rr_wagner_recurrence_seq $hrec)))

end Tactic
end RealRooted
