import RealRooted.Tactic.WagnerX.PositiveLag

/-!
# Translated Wagner `X`-lag recurrences
-/

open Polynomial

namespace RealRooted

/-! ### Plateau-safe translated affine lags -/

/-- Translating a fixed `X - r` lag by `X ↦ X + r` produces a pure `X` lag. -/
private lemma comp_pos_X_sub_C_lag_recurrence
    {P : Nat → ℝ[X]} {a c : Nat → ℝ} {r : ℝ}
    (hrec : ∀ n : Nat,
      P (n + 2) = C (a n) * P (n + 1) + (C (c n) * (X - C r)) * P n) :
    ∀ n : Nat,
      (P (n + 2)).comp (X + C r) =
        C (a n) * (P (n + 1)).comp (X + C r) +
          (C (c n) * X) * (P n).comp (X + C r) := by
  intro n
  have h := congrArg (fun p : ℝ[X] => p.comp (X + C r)) (hrec n)
  simpa [add_comp, mul_comp, sub_comp, X_comp, C_comp, sub_eq_add_neg,
    add_assoc] using h

/-- Positive leading coefficient can be transported back across a translation. -/
private lemma hasPosLeadingCoeff_of_comp_X_add_C {p : ℝ[X]} {r : ℝ}
    (h : HasPosLeadingCoeff (p.comp (X + C r))) :
    HasPosLeadingCoeff p := by
  have hback := h.comp_X_add_C (-r)
  simpa [comp_assoc, add_assoc, add_left_comm, add_comm] using hback

/-- Plateau-safe sequence induction for a fixed translated affine lag.

The change of variables `Q_n(X) = P_n(X + r)` turns the lag `X - r` into
`X`, so `prec_pos_X_lag_combo_sequence` applies even when consecutive degrees
are equal. -/
theorem prec_pos_X_sub_C_lag_combo_sequence
    {P : Nat → ℝ[X]} {a c : Nat → ℝ} {r : ℝ}
    (hbase : Prec (P 0) (P 1))
    (hshift_nonneg : ∀ n : Nat, HasNonnegCoeffs ((P n).comp (X + C r)))
    (ha : ∀ n : Nat, 0 < a n)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = C (a n) * P (n + 1) + (C (c n) * (X - C r)) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  let Q : Nat → ℝ[X] := fun n => (P n).comp (X + C r)
  have hQbase : Prec (Q 0) (Q 1) := by
    simpa [Q] using
      (prec_comp_X_add_C_iff (f := P 0) (g := P 1) r).2 hbase
  have hQrec : ∀ n : Nat,
      Q (n + 2) = C (a n) * Q (n + 1) + (C (c n) * X) * Q n := by
    simpa [Q] using comp_pos_X_sub_C_lag_recurrence hrec
  have hQprec : ∀ n : Nat, Prec (Q n) (Q (n + 1)) :=
    prec_pos_X_lag_combo_sequence hQbase
      (by simpa [Q] using hshift_nonneg) ha hc hQrec
  intro n
  exact
    (prec_comp_X_add_C_iff (f := P n) (g := P (n + 1)) r).1
      (hQprec n)

/-- Equal-base degree profile for a fixed translated affine lag. -/
theorem natDegree_pos_X_sub_C_lag_combo_sequence
    {P : Nat → ℝ[X]} {a c : Nat → ℝ} {r : ℝ} {d : Nat}
    (hzero : (P 0).natDegree = d ∧ HasPosLeadingCoeff (P 0))
    (hone : (P 1).natDegree = d ∧ HasPosLeadingCoeff (P 1))
    (ha : ∀ n : Nat, 0 < a n)
    (hc : ∀ n : Nat, 0 < c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = C (a n) * P (n + 1) + (C (c n) * (X - C r)) * P n) :
    ∀ n : Nat, (P n).natDegree = d + n / 2 ∧ HasPosLeadingCoeff (P n) := by
  let Q : Nat → ℝ[X] := fun n => (P n).comp (X + C r)
  have hQzero : (Q 0).natDegree = d ∧ HasPosLeadingCoeff (Q 0) := by
    constructor
    · simpa [Q, natDegree_comp, natDegree_X_add_C] using hzero.1
    · simpa [Q] using hzero.2.comp_X_add_C r
  have hQone : (Q 1).natDegree = d ∧ HasPosLeadingCoeff (Q 1) := by
    constructor
    · simpa [Q, natDegree_comp, natDegree_X_add_C] using hone.1
    · simpa [Q] using hone.2.comp_X_add_C r
  have hQrec : ∀ n : Nat,
      Q (n + 2) = C (a n) * Q (n + 1) + (C (c n) * X) * Q n := by
    simpa [Q] using comp_pos_X_sub_C_lag_recurrence hrec
  have hQ := natDegree_pos_X_lag_combo_sequence hQzero hQone ha hc hQrec
  intro n
  constructor
  · simpa [Q, natDegree_comp, natDegree_X_add_C] using (hQ n).1
  · exact hasPosLeadingCoeff_of_comp_X_add_C (hQ n).2

/-- Shifted-base degree profile for a fixed translated affine lag. -/
theorem natDegree_pos_X_sub_C_lag_combo_sequence_shifted
    {P : Nat → ℝ[X]} {a c : Nat → ℝ} {r : ℝ} {d : Nat}
    (hzero : (P 0).natDegree = d ∧ HasPosLeadingCoeff (P 0))
    (hone : (P 1).natDegree = d + 1 ∧ HasPosLeadingCoeff (P 1))
    (ha : ∀ n : Nat, 0 < a n)
    (hc : ∀ n : Nat, 0 < c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = C (a n) * P (n + 1) + (C (c n) * (X - C r)) * P n) :
    ∀ n : Nat, (P n).natDegree = d + (n + 1) / 2 ∧
      HasPosLeadingCoeff (P n) := by
  let Q : Nat → ℝ[X] := fun n => (P n).comp (X + C r)
  have hQzero : (Q 0).natDegree = d ∧ HasPosLeadingCoeff (Q 0) := by
    constructor
    · simpa [Q, natDegree_comp, natDegree_X_add_C] using hzero.1
    · simpa [Q] using hzero.2.comp_X_add_C r
  have hQone : (Q 1).natDegree = d + 1 ∧ HasPosLeadingCoeff (Q 1) := by
    constructor
    · simpa [Q, natDegree_comp, natDegree_X_add_C] using hone.1
    · simpa [Q] using hone.2.comp_X_add_C r
  have hQrec : ∀ n : Nat,
      Q (n + 2) = C (a n) * Q (n + 1) + (C (c n) * X) * Q n := by
    simpa [Q] using comp_pos_X_sub_C_lag_recurrence hrec
  have hQ :=
    natDegree_pos_X_lag_combo_sequence_shifted hQzero hQone ha hc hQrec
  intro n
  constructor
  · simpa [Q, natDegree_comp, natDegree_X_add_C] using (hQ n).1
  · exact hasPosLeadingCoeff_of_comp_X_add_C (hQ n).2

/-- Real-rootedness corollary for a plateau-safe translated affine lag. -/
theorem isRealRooted_of_prec_pos_X_sub_C_lag_combo_sequence
    {P : Nat → ℝ[X]} {a c : Nat → ℝ} {r : ℝ}
    (hbase : Prec (P 0) (P 1))
    (hshift_nonneg : ∀ n : Nat, HasNonnegCoeffs ((P n).comp (X + C r)))
    (ha : ∀ n : Nat, 0 < a n)
    (hc : ∀ n : Nat, 0 ≤ c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = C (a n) * P (n + 1) + (C (c n) * (X - C r)) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_prec_chain_from_step <|
    prec_pos_X_sub_C_lag_combo_sequence hbase hshift_nonneg ha hc hrec


end RealRooted
