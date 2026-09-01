import RealRooted.Tactic.WagnerX.Core

/-!
# Positive Wagner `X`-lag recurrences
-/

open Polynomial

namespace RealRooted

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
  have hg_pos : HasPosLeadingCoeff g := by rr_pos_lc using nonzero := right_ne_zero_of_prec h
  have hXf_pos : HasPosLeadingCoeff (X * f) := by
    have hf_pos : HasPosLeadingCoeff f := by rr_pos_lc using nonzero := left_ne_zero_of_prec h
    rr_pos_lc
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
  have hex : ∃ ap ∈ [(a, g), (c, X * f)], 0 < ap.1 := ⟨(a, g), by simp, ha⟩
  have hsum : Prec g (weightedSum [(a, g), (c, X * f)]) :=
    prec_weightedSum_left_of_common_left
      [(a, g), (c, X * f)] g hnonneg hprec hg_pos hpoly_pos hex
  simpa [weightedSum, mul_assoc, add_assoc] using hsum

/-- The previous polynomial also precedes a positive-current, nonnegative
`X`-lag step.  Together with `prec_pos_X_lag_combo_of_prec_nonneg`, this says
that both inputs lie on the left of the new polynomial. -/
theorem prec_left_pos_X_lag_combo_of_prec_nonneg {f g : ℝ[X]} {a c : ℝ}
    (h : Prec f g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (ha : 0 < a)
    (hc : 0 ≤ c) :
    Prec f (C a * g + (C c * X) * f) := by
  have hf_pos : HasPosLeadingCoeff f :=
    hfnn.pos_leadingCoeff (left_ne_zero_of_prec h)
  have hg_pos : HasPosLeadingCoeff g :=
    hgnn.pos_leadingCoeff (right_ne_zero_of_prec h)
  have hXf : Prec f (X * f) :=
    prec_self_mul_X_of_nonneg (left_ne_zero_of_prec h) (left_splits_of_prec h) hfnn
  have hXf_pos : HasPosLeadingCoeff (X * f) := hf_pos.X_mul
  have hnonneg : ∀ ap ∈ [(a, g), (c, X * f)], 0 ≤ ap.1 := by
    intro ap hap
    rcases List.mem_cons.mp hap with rfl | hap
    · exact ha.le
    rcases List.mem_cons.mp hap with rfl | hap
    · exact hc
    · cases hap
  have hprec : ∀ ap ∈ [(a, g), (c, X * f)], Prec f ap.2 := by
    intro ap hap
    rcases List.mem_cons.mp hap with rfl | hap
    · exact h
    rcases List.mem_cons.mp hap with rfl | hap
    · exact hXf
    · cases hap
  have hpoly_pos :
      ∀ ap ∈ [(a, g), (c, X * f)], HasPosLeadingCoeff ap.2 := by
    intro ap hap
    rcases List.mem_cons.mp hap with rfl | hap
    · exact hg_pos
    rcases List.mem_cons.mp hap with rfl | hap
    · exact hXf_pos
    · cases hap
  have hex : ∃ ap ∈ [(a, g), (c, X * f)], 0 < ap.1 :=
    ⟨(a, g), by simp, ha⟩
  have hsum : Prec f (weightedSum [(a, g), (c, X * f)]) :=
    prec_weightedSum_left_of_common_left
      [(a, g), (c, X * f)] f hnonneg hprec hf_pos hpoly_pos hex
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
  refine prec_sequence_of_base_and_step hbase ?_
  intro n hprev
  have hstep :
      Prec (P (n + 1)) (C (a n) * P (n + 1) + (C (c n) * X) * P n) :=
    prec_pos_X_lag_combo_of_prec_nonneg
      hprev (hnonneg n) (hnonneg (n + 1)) (ha n) (hc n)
  simpa [← hrec n] using hstep

/-- Degree profile for a positive scalar-current, positive `X`-lag plateau
sequence whose first two rows have the same degree.

The current and lag summands have respective degrees
`d + (n+1)/2` and `d + n/2 + 1`. They alternate between strict inequality and
equality, while positivity of both leading coefficients prevents cancellation.
-/
theorem natDegree_pos_X_lag_combo_sequence {P : Nat → ℝ[X]}
    {a c : Nat → ℝ} {d : Nat}
    (hzero : (P 0).natDegree = d ∧ HasPosLeadingCoeff (P 0))
    (hone : (P 1).natDegree = d ∧ HasPosLeadingCoeff (P 1))
    (ha : ∀ n : Nat, 0 < a n)
    (hc : ∀ n : Nat, 0 < c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = C (a n) * P (n + 1) + (C (c n) * X) * P n) :
    ∀ n : Nat, (P n).natDegree = d + n / 2 ∧ HasPosLeadingCoeff (P n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      match n with
      | 0 => simpa using hzero
      | 1 => simpa using hone
      | m + 2 =>
          obtain ⟨hdeg1, hpos1⟩ := ih (m + 1) (by lia)
          obtain ⟨hdeg0, hpos0⟩ := ih m (by lia)
          have hhead_deg :
              (C (a m) * P (m + 1)).natDegree = d + (m + 1) / 2 := by
            rw [natDegree_C_mul (ne_of_gt (ha m)), hdeg1]
          have hhead_pos : HasPosLeadingCoeff (C (a m) * P (m + 1)) :=
            hasPosLeadingCoeff_C_mul (ha m) hpos1
          have hCX_ne : C (c m) * X ≠ 0 :=
            mul_ne_zero (by simpa using ne_of_gt (hc m)) X_ne_zero
          have hCX_deg : (C (c m) * X).natDegree = 1 := by
            rw [natDegree_C_mul (ne_of_gt (hc m)), natDegree_X]
          have hlag_deg :
              ((C (c m) * X) * P m).natDegree = d + m / 2 + 1 := by
            rw [natDegree_mul hCX_ne hpos0.ne_zero, hCX_deg, hdeg0]
            lia
          have hlag_pos : HasPosLeadingCoeff ((C (c m) * X) * P m) := by
            rw [mul_assoc]
            exact hasPosLeadingCoeff_C_mul (hc m) hpos0.X_mul
          rcases (by lia :
              d + (m + 1) / 2 < d + m / 2 + 1 ∨
                d + (m + 1) / 2 = d + m / 2 + 1) with hlt | heq
          · have hdlt :
                (C (a m) * P (m + 1)).natDegree <
                  ((C (c m) * X) * P m).natDegree := by
              rw [hhead_deg, hlag_deg]
              exact hlt
            refine ⟨?_, ?_⟩
            · rw [hrec m,
                natDegree_add_eq_right_of_natDegree_lt_of_posLeadingCoeff
                  hdlt hlag_pos,
                hlag_deg]
              lia
            · rw [hrec m]
              exact hasPosLeadingCoeff_add_of_natDegree_lt_right hdlt hlag_pos
          · have hdeq :
                (C (a m) * P (m + 1)).natDegree =
                  ((C (c m) * X) * P m).natDegree := by
              rw [hhead_deg, hlag_deg]
              exact heq
            refine ⟨?_, ?_⟩
            · rw [hrec m,
                natDegree_add_eq_of_same_natDegree_of_posLeadingCoeff
                  hdeq hhead_pos hlag_pos,
                hhead_deg]
              lia
            · rw [hrec m]
              exact hasPosLeadingCoeff_add_of_same_natDegree
                hdeq hhead_pos hlag_pos

/-- Degree profile for a positive scalar-current, positive `X`-lag sequence
whose second base row has degree one more than its first.

After deriving the row-two certificate, the tail has equal base degrees and is
handled by `natDegree_pos_X_lag_combo_sequence`.
-/
theorem natDegree_pos_X_lag_combo_sequence_shifted {P : Nat → ℝ[X]}
    {a c : Nat → ℝ} {d : Nat}
    (hzero : (P 0).natDegree = d ∧ HasPosLeadingCoeff (P 0))
    (hone : (P 1).natDegree = d + 1 ∧ HasPosLeadingCoeff (P 1))
    (ha : ∀ n : Nat, 0 < a n)
    (hc : ∀ n : Nat, 0 < c n)
    (hrec : ∀ n : Nat,
      P (n + 2) = C (a n) * P (n + 1) + (C (c n) * X) * P n) :
    ∀ n : Nat, (P n).natDegree = d + (n + 1) / 2 ∧
      HasPosLeadingCoeff (P n) := by
  have hhead_deg : (C (a 0) * P 1).natDegree = d + 1 := by
    rw [natDegree_C_mul (ne_of_gt (ha 0)), hone.1]
  have hhead_pos : HasPosLeadingCoeff (C (a 0) * P 1) :=
    hasPosLeadingCoeff_C_mul (ha 0) hone.2
  have hCX_ne : C (c 0) * X ≠ 0 :=
    mul_ne_zero (by simpa using ne_of_gt (hc 0)) X_ne_zero
  have hlag_deg : ((C (c 0) * X) * P 0).natDegree = d + 1 := by
    rw [natDegree_mul hCX_ne hzero.2.ne_zero,
      natDegree_C_mul (ne_of_gt (hc 0)), natDegree_X, hzero.1]
    lia
  have hlag_pos : HasPosLeadingCoeff ((C (c 0) * X) * P 0) := by
    rw [mul_assoc]
    exact hasPosLeadingCoeff_C_mul (hc 0) hzero.2.X_mul
  have htwo : (P 2).natDegree = d + 1 ∧ HasPosLeadingCoeff (P 2) := by
    constructor
    · rw [show (2 : Nat) = 0 + 2 by rfl, hrec,
        natDegree_add_eq_of_same_natDegree_of_posLeadingCoeff
          (hhead_deg.trans hlag_deg.symm) hhead_pos hlag_pos,
        hhead_deg]
    · rw [show (2 : Nat) = 0 + 2 by rfl, hrec]
      exact hasPosLeadingCoeff_add_of_same_natDegree
        (hhead_deg.trans hlag_deg.symm) hhead_pos hlag_pos
  have htail :
      ∀ n : Nat, (P (n + 1)).natDegree = d + 1 + n / 2 ∧
        HasPosLeadingCoeff (P (n + 1)) := by
    apply natDegree_pos_X_lag_combo_sequence
      (P := fun n => P (n + 1))
      (a := fun n => a (n + 1))
      (c := fun n => c (n + 1))
      (d := d + 1) hone htwo
    · exact fun n => ha (n + 1)
    · exact fun n => hc (n + 1)
    · intro n
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrec (n + 1)
  intro n
  cases n with
  | zero => simpa using hzero
  | succ n =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail n

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
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_prec_chain_from_step <|
    prec_pos_X_lag_combo_sequence hbase hnonneg ha hc hrec



end RealRooted
