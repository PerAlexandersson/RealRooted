import RealRooted.IteratedDerivativeShift
import RealRooted.PosCombo
import RealRooted.Tactic.MaWang

/-!
# Second-derivative tactic shells

This file contains small tactic-facing wrappers for second-derivative
recurrences that factor as a Ma--Wang step followed by `a + D`.
-/

open Polynomial

namespace RealRooted

/-- Positive plus-derivative preservation in the form needed by Laguerre/Rolle
style outer steps. -/
theorem splits_add_C_mul_derivative {p : ℝ[X]} (hp : p.Splits) {eps : ℝ}
    (heps : 0 < eps) :
    (p + C eps * p.derivative).Splits := by
  have hT : (TDeriv eps (p.comp (-X))).Splits :=
    splits_tderiv heps hp.comp_neg_X
  have hcomp : ((TDeriv eps (p.comp (-X))).comp (-X)).Splits :=
    hT.comp_neg_X
  convert hcomp using 1
  simp [TDeriv, Polynomial.derivative_comp, comp_assoc]

/-- Negative plus-derivative preservation, directly from the existing
`TDeriv` theorem. -/
theorem splits_add_C_mul_derivative_of_neg {p : ℝ[X]} (hp : p.Splits) {eps : ℝ}
    (heps : eps < 0) :
    (p + C eps * p.derivative).Splits := by
  have hT : (TDeriv (-eps) p).Splits :=
    splits_tderiv (neg_pos.mpr heps) hp
  convert hT using 1
  simp [TDeriv]

/-- Plus-derivative preservation for every real coefficient. -/
theorem splits_add_C_mul_derivative_all {p : ℝ[X]} (hp : p.Splits) (eps : ℝ) :
    (p + C eps * p.derivative).Splits := by
  rcases lt_trichotomy eps 0 with heps | heps | heps
  · exact splits_add_C_mul_derivative_of_neg hp heps
  · subst eps
    simpa using hp
  · exact splits_add_C_mul_derivative hp heps

/-- The scaled outer form `(a + D) p = a p + p'`, for every nonzero `a`. -/
theorem splits_C_mul_add_derivative {p : ℝ[X]} (hp : p.Splits) {a : ℝ}
    (ha : a ≠ 0) :
    (C a * p + p.derivative).Splits := by
  have hscaled : (p + C a⁻¹ * p.derivative).Splits :=
    splits_add_C_mul_derivative_all hp a⁻¹
  have hmul : (C a * (p + C a⁻¹ * p.derivative)).Splits := by
    exact (Polynomial.Splits.C (R := ℝ) a).mul hscaled
  have hEq : C a * (p + C a⁻¹ * p.derivative) = C a * p + p.derivative := by
    rw [mul_add]
    have hterm : C a * (C a⁻¹ * p.derivative) = p.derivative := by
      rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ ha, C_1, one_mul]
    rw [hterm]
  simpa [hEq] using hmul

/-- Splits-only Ma--Wang wrapper for the usual sign orientation. -/
theorem splits_mw_derivative_of_nonpos {f u v : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hdeg_lo : f.natDegree ≤ (u * f + v * f.derivative).natDegree)
    (hdeg_hi : (u * f + v * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_pos : HasPosLeadingCoeff (u * f + v * f.derivative))
    (hf_pos : HasPosLeadingCoeff f)
    (hv_nonpos : ∀ r, f.IsRoot r → v.eval r ≤ 0) :
    (u * f + v * f.derivative).Splits :=
  (prec_mw_derivative_of_nonpos
    hf hdegf hdeg_lo hdeg_hi hF_pos hf_pos hv_nonpos).2.1.2

/-- Splits-only Ma--Wang wrapper for the sign-flipped inner transform.  This
is useful when `u f + v f'` has negative leading coefficient and `v` is
nonnegative at roots of `f`. -/
theorem splits_mw_derivative_of_nonneg_neg_inner {f u v : ℝ[X]}
    (hf : f.Splits)
    (hdegf : 2 ≤ f.natDegree)
    (hdeg_lo : f.natDegree ≤ (u * f + v * f.derivative).natDegree)
    (hdeg_hi : (u * f + v * f.derivative).natDegree ≤ f.natDegree + 1)
    (hF_neg_pos : HasPosLeadingCoeff (-(u * f + v * f.derivative)))
    (hf_pos : HasPosLeadingCoeff f)
    (hv_nonneg : ∀ r, f.IsRoot r → 0 ≤ v.eval r) :
    (u * f + v * f.derivative).Splits := by
  have hneg_eq : (-u) * f + (-v) * f.derivative = -(u * f + v * f.derivative) := by
    ring
  have hdeg_lo_neg : f.natDegree ≤ ((-u) * f + (-v) * f.derivative).natDegree := by
    rw [hneg_eq, natDegree_neg]
    exact hdeg_lo
  have hdeg_hi_neg : ((-u) * f + (-v) * f.derivative).natDegree ≤ f.natDegree + 1 := by
    rw [hneg_eq, natDegree_neg]
    exact hdeg_hi
  have hF_neg_pos' : HasPosLeadingCoeff ((-u) * f + (-v) * f.derivative) := by
    rw [hneg_eq]
    exact hF_neg_pos
  have hneg_splits :
      ((-u) * f + (-v) * f.derivative).Splits := by
    refine
      splits_mw_derivative_of_nonpos
        hf hdegf ?_ ?_ ?_ hf_pos ?_
    · exact hdeg_lo_neg
    · exact hdeg_hi_neg
    · exact hF_neg_pos'
    · intro r hr
      simpa using neg_nonpos.mpr (hv_nonneg r hr)
  have hscaled : (C (-1 : ℝ) * ((-u) * f + (-v) * f.derivative)).Splits :=
    (Polynomial.Splits.C (R := ℝ) (-1)).mul hneg_splits
  have hscale_eq : C (-1 : ℝ) * ((-u) * f + (-v) * f.derivative) =
      u * f + v * f.derivative := by
    rw [hneg_eq]
    simp
  simpa [hscale_eq, add_comm, add_left_comm, add_assoc] using hscaled

/-- Sequence-level LS4 shell: first prove the inner Ma--Wang transform
`U_n P_{n+1}+V_n P'_{n+1}` is in proper position with `P_{n+1}`, then apply
the outer operator `a_n + D`.  The recurrence is supplied in the factored
form; examples can derive it from the expanded OEIS recurrence by `ring`. -/
theorem isRealRooted_of_mw_then_const_add_derivative_sequence
    {P : Nat → ℝ[X]} {U V : Nat → ℝ[X]} (a : Nat → ℝ)
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (ha : ∀ n : Nat, a n ≠ 0)
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hinner_pos : ∀ n : Nat,
      HasPosLeadingCoeff (U n * P (n + 1) + V n * (P (n + 1)).derivative))
    (hV_nonpos : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (V n).eval r ≤ 0)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        C (a n) * (U n * P (n + 1) + V n * (P (n + 1)).derivative) +
          (U n * P (n + 1) + V n * (P (n + 1)).derivative).derivative)
    (hinner_deg_lo : ∀ n : Nat,
      (P (n + 1)).natDegree ≤
        (U n * P (n + 1) + V n * (P (n + 1)).derivative).natDegree)
    (hinner_deg_hi : ∀ n : Nat,
      (U n * P (n + 1) + V n * (P (n + 1)).derivative).natDegree ≤
        (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  have htail : ∀ n : Nat, P (n + 1) ≠ 0 ∧ (P (n + 1)).Splits := by
    intro n
    induction n with
    | zero =>
        simpa using hbase_one
    | succ n ih =>
        let G : ℝ[X] := U n * P (n + 1) + V n * (P (n + 1)).derivative
        have hinner_splits : G.Splits :=
          splits_mw_derivative_of_nonpos
            ih.2 (hdeg_two n) (by simpa [G] using hinner_deg_lo n)
            (by simpa [G] using hinner_deg_hi n)
            (by simpa [G] using hinner_pos n)
            (hpos (n + 1)) (by simpa [G] using hV_nonpos n)
        have houter : (C (a n) * G + G.derivative).Splits :=
          splits_C_mul_add_derivative hinner_splits (ha n)
        exact
          ⟨(hpos (n + 2)).ne_zero, by
            simpa [G, hrec n] using houter⟩
  intro n
  cases n with
  | zero =>
      exact hbase_zero
  | succ n =>
      exact htail n

/-- Compatibility wrapper for the positive-outer branch. -/
theorem isRealRooted_of_mw_then_pos_const_add_derivative_sequence
    {P : Nat → ℝ[X]} {U V : Nat → ℝ[X]} (a : Nat → ℝ)
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (ha : ∀ n : Nat, 0 < a n)
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hinner_pos : ∀ n : Nat,
      HasPosLeadingCoeff (U n * P (n + 1) + V n * (P (n + 1)).derivative))
    (hV_nonpos : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → (V n).eval r ≤ 0)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        C (a n) * (U n * P (n + 1) + V n * (P (n + 1)).derivative) +
          (U n * P (n + 1) + V n * (P (n + 1)).derivative).derivative)
    (hinner_deg_lo : ∀ n : Nat,
      (P (n + 1)).natDegree ≤
        (U n * P (n + 1) + V n * (P (n + 1)).derivative).natDegree)
    (hinner_deg_hi : ∀ n : Nat,
      (U n * P (n + 1) + V n * (P (n + 1)).derivative).natDegree ≤
        (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_mw_then_const_add_derivative_sequence
    a hbase_zero hbase_one hpos (fun n => ne_of_gt (ha n)) hdeg_two hinner_pos
    hV_nonpos hrec hinner_deg_lo hinner_deg_hi

/-- Sequence-level LS4 shell for the sign-flipped inner Ma--Wang transform.
Here `U_n P_{n+1}+V_n P'_{n+1}` has negative leading coefficient, while
`V_n` is nonnegative at the old roots. -/
theorem isRealRooted_of_neg_mw_then_const_add_derivative_sequence
    {P : Nat → ℝ[X]} {U V : Nat → ℝ[X]} (a : Nat → ℝ)
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hpos : ∀ n : Nat, HasPosLeadingCoeff (P n))
    (ha : ∀ n : Nat, a n ≠ 0)
    (hdeg_two : ∀ n : Nat, 2 ≤ (P (n + 1)).natDegree)
    (hinner_neg_pos : ∀ n : Nat,
      HasPosLeadingCoeff (-(U n * P (n + 1) + V n * (P (n + 1)).derivative)))
    (hV_nonneg : ∀ n : Nat, ∀ r, (P (n + 1)).IsRoot r → 0 ≤ (V n).eval r)
    (hrec : ∀ n : Nat,
      P (n + 2) =
        C (a n) * (U n * P (n + 1) + V n * (P (n + 1)).derivative) +
          (U n * P (n + 1) + V n * (P (n + 1)).derivative).derivative)
    (hinner_deg_lo : ∀ n : Nat,
      (P (n + 1)).natDegree ≤
        (U n * P (n + 1) + V n * (P (n + 1)).derivative).natDegree)
    (hinner_deg_hi : ∀ n : Nat,
      (U n * P (n + 1) + V n * (P (n + 1)).derivative).natDegree ≤
        (P (n + 1)).natDegree + 1) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  have htail : ∀ n : Nat, P (n + 1) ≠ 0 ∧ (P (n + 1)).Splits := by
    intro n
    induction n with
    | zero =>
        simpa using hbase_one
    | succ n ih =>
        let G : ℝ[X] := U n * P (n + 1) + V n * (P (n + 1)).derivative
        have hinner_splits : G.Splits :=
          splits_mw_derivative_of_nonneg_neg_inner
            ih.2 (hdeg_two n) (by simpa [G] using hinner_deg_lo n)
            (by simpa [G] using hinner_deg_hi n)
            (by simpa [G] using hinner_neg_pos n)
            (hpos (n + 1)) (by simpa [G] using hV_nonneg n)
        have houter : (C (a n) * G + G.derivative).Splits :=
          splits_C_mul_add_derivative hinner_splits (ha n)
        exact
          ⟨(hpos (n + 2)).ne_zero, by
            simpa [G, hrec n] using houter⟩
  intro n
  cases n with
  | zero =>
      exact hbase_zero
  | succ n =>
      exact htail n

/-- Sequence-level wrapper for an LS4 output plus a nonnegative multiple of
the current row.

This is the next shell after the pure LS4 recurrence: the factored LS4 output
`H_n = a_n G_n + G'_n` is allowed to be combined with `b_n P_{n+1}`.  The
proper-position bridge `P_{n+1} ≪ H_n` is supplied as a side condition; the
wrapper hides the positive-combination step and the expanded-recurrence
normalization. -/
theorem isRealRooted_of_mw_then_const_add_derivative_plus_current_sequence
    {P : Nat → ℝ[X]} {U V : Nat → ℝ[X]} (a b : Nat → ℝ)
    (hbase_zero : P 0 ≠ 0 ∧ (P 0).Splits)
    (hbase_one : P 1 ≠ 0 ∧ (P 1).Splits)
    (hcurrent_pos : ∀ n : Nat, HasPosLeadingCoeff (P (n + 1)))
    (hb : ∀ n : Nat, 0 ≤ b n)
    (houter_pos : ∀ n : Nat,
      HasPosLeadingCoeff
        (C (a n) * (U n * P (n + 1) + V n * (P (n + 1)).derivative) +
          (U n * P (n + 1) + V n * (P (n + 1)).derivative).derivative))
    (houter_prec : ∀ n : Nat,
      Prec (P (n + 1))
        (C (a n) * (U n * P (n + 1) + V n * (P (n + 1)).derivative) +
          (U n * P (n + 1) + V n * (P (n + 1)).derivative).derivative))
    (hrec : ∀ n : Nat,
      P (n + 2) =
        C (b n) * P (n + 1) +
          (C (a n) * (U n * P (n + 1) + V n * (P (n + 1)).derivative) +
            (U n * P (n + 1) + V n * (P (n + 1)).derivative).derivative)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  intro n
  cases n with
  | zero =>
      exact hbase_zero
  | succ n =>
      cases n with
      | zero =>
          exact hbase_one
      | succ n =>
          let H : ℝ[X] :=
            C (a n) * (U n * P (n + 1) + V n * (P (n + 1)).derivative) +
              (U n * P (n + 1) + V n * (P (n + 1)).derivative).derivative
          have hcombo :
              (C (b n) * P (n + 1) + C (1 : ℝ) * H) ≠ 0 ∧
                (C (b n) * P (n + 1) + C (1 : ℝ) * H).Splits :=
            isRealRooted_nonneg_combo_of_prec
              (by simpa [H] using houter_prec n)
              (hcurrent_pos n) (by simpa [H] using houter_pos n)
              (hb n) (by norm_num : 0 ≤ (1 : ℝ)) (Or.inr (by norm_num))
          simpa [H, hrec n] using hcombo

/-- Algebraic expansion of the LS4 operator `(a + D) (U f + V f')`.

The tactic-facing examples use this to convert OEIS recurrences written as an
expanded combination of `f`, `f'`, and `f''` into the factored Ma--Wang plus
outer-derivative form required by the sequence shell. -/
theorem ls4_factor_expansion (a : ℝ) (U V f : ℝ[X]) :
    C a * (U * f + V * f.derivative) + (U * f + V * f.derivative).derivative =
      (C a * U + U.derivative) * f +
        (C a * V + U + V.derivative) * f.derivative +
          V * f.derivative.derivative := by
  simp [Polynomial.derivative_add, Polynomial.derivative_mul]
  ring

theorem ls4_C_two_real : (C (2 : ℝ) : ℝ[X]) = 2 := by
  exact Polynomial.C_eq_natCast 2

theorem ls4_C_four_real : (C (4 : ℝ) : ℝ[X]) = 4 := by
  exact Polynomial.C_eq_natCast 4

theorem ls4_C_eight_real : (C (8 : ℝ) : ℝ[X]) = 8 := by
  exact Polynomial.C_eq_natCast 8

theorem ls4_C_sixteen_real : (C (16 : ℝ) : ℝ[X]) = 16 := by
  exact Polynomial.C_eq_natCast 16

theorem ls4_C_neg_one_real : (C (-1 : ℝ) : ℝ[X]) = -1 := by
  norm_num

theorem ls4_C_ofNat_real (m : Nat) [m.AtLeastTwo] :
    (C (OfNat.ofNat m : ℝ) : ℝ[X]) = (OfNat.ofNat m : ℝ[X]) := by
  change (C (m : ℝ) : ℝ[X]) = (m : ℝ[X])
  exact Polynomial.C_eq_natCast m

theorem ls4_C_mul_ofNat_mul (a : ℝ) (m : Nat) [m.AtLeastTwo] (p : ℝ[X]) :
    C a * ((OfNat.ofNat m : ℝ[X]) * p) =
      C (a * (OfNat.ofNat m : ℝ)) * p := by
  change C a * ((m : ℝ[X]) * p) = C (a * (m : ℝ)) * p
  rw [show (m : ℝ[X]) = C (m : ℝ) by
    exact (Polynomial.C_eq_natCast m).symm]
  rw [← mul_assoc, ← C_mul]

theorem ls4_C_mul_neg_ofNat_mul (a : ℝ) (m : Nat) [m.AtLeastTwo] (p : ℝ[X]) :
    C a * (-((OfNat.ofNat m : ℝ[X]) * p)) =
      C (-(a * (OfNat.ofNat m : ℝ))) * p := by
  change C a * (-((m : ℝ[X]) * p)) = C (-(a * (m : ℝ))) * p
  rw [show -((m : ℝ[X]) * p) = (-(m : ℝ[X])) * p by ring]
  rw [← mul_assoc]
  rw [show C a * -(m : ℝ[X]) = C (-(a * (m : ℝ))) by
    rw [show (m : ℝ[X]) = C (m : ℝ) by
      exact (Polynomial.C_eq_natCast m).symm]
    rw [← C_neg, ← C_mul]
    congr
    ring]

theorem ls4_mul_C_ofNat_right (a : ℝ) (m : Nat) [m.AtLeastTwo] (p : ℝ[X]) :
    p * C a * (OfNat.ofNat m : ℝ[X]) =
      p * C (a * (OfNat.ofNat m : ℝ)) := by
  change p * C a * (m : ℝ[X]) = p * C (a * (m : ℝ))
  rw [show (m : ℝ[X]) = C (m : ℝ) by
    exact (Polynomial.C_eq_natCast m).symm]
  rw [mul_assoc, ← C_mul]

namespace Tactic

syntax (name := rr_ls4_factorize) "rr_ls4_factorize" : tactic

syntax (name := rr_mw_plus_derivative_sequence_named)
  "rr_mw_plus_derivative_sequence" " using "
    "outer" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "pos_lc" ":=" term ","
    "outer_nonzero" ":=" term ","
    "degree_two" ":=" term ","
    "inner_pos_lc" ":=" term ","
    "coeff_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "inner_degree_lower" ":=" term ","
    "inner_degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_plus_derivative_sequence_expanded_named)
  "rr_mw_plus_derivative_sequence_expanded" " using "
    "outer" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "pos_lc" ":=" term ","
    "outer_nonzero" ":=" term ","
    "degree_two" ":=" term ","
    "inner_pos_lc" ":=" term ","
    "coeff_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "inner_degree_lower" ":=" term ","
    "inner_degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_plus_derivative_sequence_pos_named)
  "rr_mw_plus_derivative_sequence" " using "
    "outer" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "pos_lc" ":=" term ","
    "outer_pos" ":=" term ","
    "degree_two" ":=" term ","
    "inner_pos_lc" ":=" term ","
    "coeff_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "inner_degree_lower" ":=" term ","
    "inner_degree_upper" ":=" term :
  tactic

syntax (name := rr_mw_plus_derivative_sequence_expanded_pos_named)
  "rr_mw_plus_derivative_sequence_expanded" " using "
    "outer" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "pos_lc" ":=" term ","
    "outer_pos" ":=" term ","
    "degree_two" ":=" term ","
    "inner_pos_lc" ":=" term ","
    "coeff_nonpos" ":=" term ","
    "recurrence" ":=" term ","
    "inner_degree_lower" ":=" term ","
    "inner_degree_upper" ":=" term :
  tactic

syntax (name := rr_neg_mw_plus_derivative_sequence_named)
  "rr_neg_mw_plus_derivative_sequence" " using "
    "outer" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "pos_lc" ":=" term ","
    "outer_nonzero" ":=" term ","
    "degree_two" ":=" term ","
    "inner_neg_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "inner_degree_lower" ":=" term ","
    "inner_degree_upper" ":=" term :
  tactic

syntax (name := rr_neg_mw_plus_derivative_sequence_expanded_named)
  "rr_neg_mw_plus_derivative_sequence_expanded" " using "
    "outer" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "pos_lc" ":=" term ","
    "outer_nonzero" ":=" term ","
    "degree_two" ":=" term ","
    "inner_neg_lc" ":=" term ","
    "coeff_nonneg" ":=" term ","
    "recurrence" ":=" term ","
    "inner_degree_lower" ":=" term ","
    "inner_degree_upper" ":=" term :
  tactic

syntax (name := rr_ls4_plus_current_sequence_expanded_named)
  "rr_ls4_plus_current_sequence_expanded" " using "
    "outer" ":=" term ","
    "tail" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "pos_lc" ":=" term ","
    "tail_nonneg" ":=" term ","
    "outer_pos_lc" ":=" term ","
    "outer_prec" ":=" term ","
    "recurrence" ":=" term :
  tactic

macro_rules
  | `(tactic| rr_ls4_factorize) =>
      `(tactic|
        first
          | rw [RealRooted.ls4_factor_expansion]
            simp [Polynomial.derivative_add, Polynomial.derivative_sub,
              Polynomial.derivative_mul, Polynomial.derivative_C,
              Polynomial.derivative_X, Polynomial.derivative_one,
              Polynomial.derivative_zero, Polynomial.derivative_natCast,
              Polynomial.derivative_ofNat, Polynomial.derivative_neg,
              RealRooted.ls4_C_two_real, RealRooted.ls4_C_four_real,
              RealRooted.ls4_C_eight_real, RealRooted.ls4_C_sixteen_real,
              RealRooted.ls4_C_neg_one_real,
              Polynomial.C_1, one_mul]
            repeat rw [RealRooted.ls4_C_ofNat_real]
            repeat rw [RealRooted.ls4_C_mul_neg_ofNat_mul]
            repeat rw [RealRooted.ls4_C_mul_ofNat_mul]
            repeat rw [RealRooted.ls4_mul_C_ofNat_right]
            try norm_num1
            repeat rw [RealRooted.ls4_C_ofNat_real]
            try
              simp [RealRooted.ls4_C_two_real, RealRooted.ls4_C_four_real,
                RealRooted.ls4_C_eight_real, RealRooted.ls4_C_sixteen_real,
                RealRooted.ls4_C_neg_one_real, Polynomial.C_add, Polynomial.C_1,
                Polynomial.C_neg, one_mul, mul_one]
            repeat rw [RealRooted.ls4_C_ofNat_real]
            ring_nf
          | simp [Polynomial.derivative_add, Polynomial.derivative_sub,
              Polynomial.derivative_mul, Polynomial.derivative_C,
              Polynomial.derivative_X, Polynomial.derivative_one,
              Polynomial.derivative_zero, Polynomial.derivative_natCast,
              Polynomial.derivative_ofNat, Polynomial.derivative_neg,
              RealRooted.ls4_C_two_real, RealRooted.ls4_C_four_real,
              RealRooted.ls4_C_eight_real, RealRooted.ls4_C_sixteen_real,
              RealRooted.ls4_C_neg_one_real,
              Polynomial.C_1, one_mul]
            repeat rw [RealRooted.ls4_C_ofNat_real]
            repeat rw [RealRooted.ls4_C_mul_neg_ofNat_mul]
            repeat rw [RealRooted.ls4_C_mul_ofNat_mul]
            repeat rw [RealRooted.ls4_mul_C_ofNat_right]
            try norm_num1
            repeat rw [RealRooted.ls4_C_ofNat_real]
            try
              simp [RealRooted.ls4_C_two_real, RealRooted.ls4_C_four_real,
                RealRooted.ls4_C_eight_real, RealRooted.ls4_C_sixteen_real,
                RealRooted.ls4_C_neg_one_real, Polynomial.C_add, Polynomial.C_1,
                Polynomial.C_neg, one_mul, mul_one]
            repeat rw [RealRooted.ls4_C_ofNat_real]
            ring_nf)
  | `(tactic|
      rr_mw_plus_derivative_sequence_expanded using
        outer := $a:term,
        base_zero := $hbase_zero:term,
        base_one := $hbase_one:term,
        pos_lc := $hpos:term,
        outer_nonzero := $ha:term,
        degree_two := $hdeg_two:term,
        inner_pos_lc := $hinner_pos:term,
        coeff_nonpos := $hV:term,
        recurrence := $hrec:term,
        inner_degree_lower := $hinner_deg_lo:term,
        inner_degree_upper := $hinner_deg_hi:term) =>
      `(tactic|
        refine
          RealRooted.isRealRooted_of_mw_then_const_add_derivative_sequence
            $a $hbase_zero $hbase_one $hpos $ha $hdeg_two $hinner_pos $hV ?_
            $hinner_deg_lo $hinner_deg_hi <;>
          (intro n
           rw [$hrec n]
           rr_ls4_factorize))
  | `(tactic|
      rr_mw_plus_derivative_sequence_expanded using
        outer := $a:term,
        base_zero := $hbase_zero:term,
        base_one := $hbase_one:term,
        pos_lc := $hpos:term,
        outer_pos := $ha:term,
        degree_two := $hdeg_two:term,
        inner_pos_lc := $hinner_pos:term,
        coeff_nonpos := $hV:term,
        recurrence := $hrec:term,
        inner_degree_lower := $hinner_deg_lo:term,
        inner_degree_upper := $hinner_deg_hi:term) =>
      `(tactic|
        refine
          RealRooted.isRealRooted_of_mw_then_pos_const_add_derivative_sequence
            $a $hbase_zero $hbase_one $hpos $ha $hdeg_two $hinner_pos $hV ?_
            $hinner_deg_lo $hinner_deg_hi <;>
          (intro n
           rw [$hrec n]
           rr_ls4_factorize))
  | `(tactic|
      rr_neg_mw_plus_derivative_sequence_expanded using
        outer := $a:term,
        base_zero := $hbase_zero:term,
        base_one := $hbase_one:term,
        pos_lc := $hpos:term,
        outer_nonzero := $ha:term,
        degree_two := $hdeg_two:term,
        inner_neg_lc := $hinner_neg:term,
        coeff_nonneg := $hV:term,
        recurrence := $hrec:term,
        inner_degree_lower := $hinner_deg_lo:term,
        inner_degree_upper := $hinner_deg_hi:term) =>
      `(tactic|
        refine
          RealRooted.isRealRooted_of_neg_mw_then_const_add_derivative_sequence
            $a $hbase_zero $hbase_one $hpos $ha $hdeg_two $hinner_neg $hV ?_
            $hinner_deg_lo $hinner_deg_hi <;>
          (intro n
           rw [$hrec n]
           rr_ls4_factorize))
  | `(tactic|
      rr_ls4_plus_current_sequence_expanded using
        outer := $a:term,
        tail := $b:term,
        base_zero := $hbase_zero:term,
        base_one := $hbase_one:term,
        pos_lc := $hpos:term,
        tail_nonneg := $hb:term,
        outer_pos_lc := $houter_pos:term,
        outer_prec := $houter_prec:term,
        recurrence := $hrec:term) =>
      `(tactic|
        refine
          RealRooted.isRealRooted_of_mw_then_const_add_derivative_plus_current_sequence
            $a $b $hbase_zero $hbase_one (fun n => $hpos (n + 1)) $hb
            $houter_pos $houter_prec ?_ <;>
          (intro n
           rw [$hrec n]
           rr_ls4_factorize))
  | `(tactic|
      rr_mw_plus_derivative_sequence using
        outer := $a:term,
        base_zero := $hbase_zero:term,
        base_one := $hbase_one:term,
        pos_lc := $hpos:term,
        outer_nonzero := $ha:term,
        degree_two := $hdeg_two:term,
        inner_pos_lc := $hinner_pos:term,
        coeff_nonpos := $hV:term,
        recurrence := $hrec:term,
        inner_degree_lower := $hinner_deg_lo:term,
        inner_degree_upper := $hinner_deg_hi:term) =>
      `(tactic|
        exact
          RealRooted.isRealRooted_of_mw_then_const_add_derivative_sequence
            $a $hbase_zero $hbase_one $hpos $ha $hdeg_two $hinner_pos $hV $hrec
            $hinner_deg_lo $hinner_deg_hi)
  | `(tactic|
      rr_mw_plus_derivative_sequence using
        outer := $a:term,
        base_zero := $hbase_zero:term,
        base_one := $hbase_one:term,
        pos_lc := $hpos:term,
        outer_pos := $ha:term,
        degree_two := $hdeg_two:term,
        inner_pos_lc := $hinner_pos:term,
        coeff_nonpos := $hV:term,
        recurrence := $hrec:term,
        inner_degree_lower := $hinner_deg_lo:term,
        inner_degree_upper := $hinner_deg_hi:term) =>
      `(tactic|
        exact
          RealRooted.isRealRooted_of_mw_then_pos_const_add_derivative_sequence
            $a $hbase_zero $hbase_one $hpos $ha $hdeg_two $hinner_pos $hV $hrec
            $hinner_deg_lo $hinner_deg_hi)
  | `(tactic|
      rr_neg_mw_plus_derivative_sequence using
        outer := $a:term,
        base_zero := $hbase_zero:term,
        base_one := $hbase_one:term,
        pos_lc := $hpos:term,
        outer_nonzero := $ha:term,
        degree_two := $hdeg_two:term,
        inner_neg_lc := $hinner_neg:term,
        coeff_nonneg := $hV:term,
        recurrence := $hrec:term,
        inner_degree_lower := $hinner_deg_lo:term,
        inner_degree_upper := $hinner_deg_hi:term) =>
      `(tactic|
        exact
          RealRooted.isRealRooted_of_neg_mw_then_const_add_derivative_sequence
            $a $hbase_zero $hbase_one $hpos $ha $hdeg_two $hinner_neg $hV $hrec
            $hinner_deg_lo $hinner_deg_hi)

end Tactic
end RealRooted
