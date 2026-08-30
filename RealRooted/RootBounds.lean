import RealRooted.SignEvaluation
import RealRooted.Derivative
import RealRooted.WagnerX

/-!
# Root bounds from coefficient positivity

Reusable root-bound consequences of splitness and nonnegative coefficients.
-/

open Polynomial

namespace RealRooted

lemma root_nonpos_of_ne_zero_of_splits_of_nonneg_coeffs {p : ℝ[X]}
    (hp_ne : p ≠ 0) (hp_splits : p.Splits) (hpnn : HasNonnegCoeffs p)
    {r : ℝ} (hr : p.IsRoot r) :
    r ≤ 0 :=
  roots_nonpos_of_nonneg_coeffs hp_splits hpnn r ((mem_roots hp_ne).mpr hr)

lemma root_nonpos_of_realrooted_of_nonneg_coeffs {p : ℝ[X]}
    (hrr : p ≠ 0 ∧ p.Splits) (hpnn : HasNonnegCoeffs p)
    {r : ℝ} (hr : p.IsRoot r) :
    r ≤ 0 :=
  root_nonpos_of_ne_zero_of_splits_of_nonneg_coeffs hrr.1 hrr.2 hpnn hr

lemma roots_nonpos_of_realrooted_of_nonneg_coeffs {p : ℝ[X]}
    (hrr : p ≠ 0 ∧ p.Splits) (hpnn : HasNonnegCoeffs p) :
    ∀ r, p.IsRoot r → r ≤ 0 := fun _ hr =>
  root_nonpos_of_realrooted_of_nonneg_coeffs hrr hpnn hr

lemma roots_nonpos_of_interlaces_of_nonneg_coeffs {f g : ℝ[X]}
    (hgf : Interlaces g f) (hfnn : HasNonnegCoeffs f) :
    ∀ r, f.IsRoot r → r ≤ 0 :=
  roots_nonpos_of_realrooted_of_nonneg_coeffs hgf.1 hfnn

/-- Shifted nonnegative coefficients give a left root bound in the original
variable.  If `p(t-a)` has nonnegative coefficients, then every real root of
`p(t)` is at most `-a`. -/
lemma root_le_neg_of_realrooted_of_shift_nonneg_coeffs {p : ℝ[X]} {a r : ℝ}
    (hrr : p ≠ 0 ∧ p.Splits) (hshift_nonneg : HasNonnegCoeffs (p.comp (X - C a)))
    (hr : p.IsRoot r) :
    r ≤ -a := by
  have hshift_rr : p.comp (X - C a) ≠ 0 ∧ (p.comp (X - C a)).Splits := by
    simpa [sub_eq_add_neg] using isRealRooted_comp_X_add_C hrr.1 hrr.2 (-a)
  have hshift_root : (p.comp (X - C a)).IsRoot (r + a) := by
    rw [Polynomial.IsRoot.def] at hr ⊢
    simpa [Polynomial.eval_comp, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hr
  have hnonpos :
      r + a ≤ 0 :=
    root_nonpos_of_realrooted_of_nonneg_coeffs hshift_rr hshift_nonneg hshift_root
  linarith

lemma roots_nonpos_derivative_of_splits_of_nonneg_coeffs {p : ℝ[X]}
    (hp_splits : p.Splits) (hpnn : HasNonnegCoeffs p) :
    ∀ r ∈ p.derivative.roots, r ≤ 0 :=
  roots_nonpos_derivative_of_roots_nonpos hp_splits
    (roots_nonpos_of_nonneg_coeffs hp_splits hpnn)

lemma derivative_root_nonpos_of_splits_of_nonneg_coeffs {p : ℝ[X]}
    (hp_splits : p.Splits) (hpnn : HasNonnegCoeffs p)
    (hp_der_ne : p.derivative ≠ 0) {r : ℝ}
    (hr : p.derivative.IsRoot r) :
    r ≤ 0 :=
  roots_nonpos_derivative_of_splits_of_nonneg_coeffs hp_splits hpnn r
    ((mem_roots hp_der_ne).mpr hr)

lemma derivative_root_nonpos_of_realrooted_of_nonneg_coeffs {p : ℝ[X]}
    (hrr : p ≠ 0 ∧ p.Splits) (hpnn : HasNonnegCoeffs p)
    (hp_der_ne : p.derivative ≠ 0) {r : ℝ}
    (hr : p.derivative.IsRoot r) :
    r ≤ 0 :=
  derivative_root_nonpos_of_splits_of_nonneg_coeffs hrr.2 hpnn hp_der_ne hr

lemma roots_nonpos_sequence_of_realrooted_of_nonneg_coeffs
    {P : Nat → ℝ[X]}
    (hrr : ∀ i : Nat, P i ≠ 0 ∧ (P i).Splits)
    (hnn : ∀ i : Nat, HasNonnegCoeffs (P i)) :
    ∀ i : Nat, ∀ r, (P i).IsRoot r → r ≤ 0 := fun i _ hr =>
  root_nonpos_of_realrooted_of_nonneg_coeffs (hrr i) (hnn i) hr

lemma roots_le_neg_sequence_of_realrooted_of_shift_nonneg_coeffs
    {P : Nat → ℝ[X]} {a : Nat → ℝ}
    (hrr : ∀ i : Nat, P i ≠ 0 ∧ (P i).Splits)
    (hshift_nonneg : ∀ i : Nat, HasNonnegCoeffs ((P i).comp (X - C (a i)))) :
    ∀ i : Nat, ∀ r, (P i).IsRoot r → r ≤ -(a i) := fun i _ hr =>
  root_le_neg_of_realrooted_of_shift_nonneg_coeffs
    (hrr i) (hshift_nonneg i) hr

lemma derivative_roots_nonpos_sequence_of_realrooted_of_nonneg_coeffs
    {P : Nat → ℝ[X]}
    (hrr : ∀ i : Nat, P i ≠ 0 ∧ (P i).Splits)
    (hnn : ∀ i : Nat, HasNonnegCoeffs (P i))
    (hder_ne : ∀ i : Nat, (P i).derivative ≠ 0) :
    ∀ i : Nat, ∀ r, (P i).derivative.IsRoot r → r ≤ 0 := fun i _ hr =>
  derivative_root_nonpos_of_realrooted_of_nonneg_coeffs
    (hrr i) (hnn i) (hder_ne i) hr

end RealRooted
