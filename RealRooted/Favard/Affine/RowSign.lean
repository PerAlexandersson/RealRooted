import RealRooted.Favard.Affine.Basic
import RealRooted.ScalarNormalization

/-!
# Row-sign normalized affine Favard recurrences

This module owns the affine Favard APIs transported through
`Q n = (-1)^n P n`, including their scalar-denominator variants.
-/

open Polynomial

namespace RealRooted

private lemma neg_one_pow_mul_self (n : Nat) :
    ((-1 : ℝ) ^ n) * ((-1 : ℝ) ^ n) = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]
  simp

private lemma neg_one_pow_add_two (n : Nat) :
    ((-1 : ℝ) ^ (n + 2)) = (-1 : ℝ) ^ n := by
  rw [show n + 2 = n + 1 + 1 by rfl, pow_succ, pow_succ]
  ring_nf

private lemma neg_one_pow_succ (n : Nat) :
    ((-1 : ℝ) ^ (n + 1)) = -((-1 : ℝ) ^ n) := by
  rw [pow_succ]
  ring


/-- Positive-slope affine Favard wrapper after row-sign normalization.  This
packages the Chebyshev-like shape
`P_{n+2}=-(sX-α)P_{n+1}-βP_n`, with `s > 0` and `β > 0`, by applying Favard
to `Q_n=(-1)^n P_n`. -/
theorem favardInterlacing_affine_const_coeff_rowSign
    {P : Nat → ℝ[X]} {s α β : ℝ}
    (hs : 0 < s)
    (hβ : 0 < β)
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C s * X - C α))
    (hstep : ∀ n : Nat,
      P (n + 2) = -(C s * X - C α) * P (n + 1) - C β * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  let Q : Nat → ℝ[X] := fun n => C ((-1 : ℝ) ^ n) * P n
  have hQ0 : Q 0 = 1 := by simp [Q, hP0]
  have hQ1 : Q 1 = C s * X - C α := by simp [Q, hP1]
  have hQstep : ∀ n : Nat,
      Q (n + 2) = (C s * X - C α) * Q (n + 1) - C β * Q n := by
    intro n
    dsimp [Q]
    rw [neg_one_pow_add_two n, neg_one_pow_succ n, hstep n, C_neg]
    ring_nf
  have hQprec : ∀ n : Nat, Prec (Q n) (Q (n + 1)) :=
    favardInterlacing_affine_const_coeff hs hβ hQ0 hQ1 hQstep
  intro n
  have hleft_ne : ((-1 : ℝ) ^ n) ≠ 0 := by exact pow_ne_zero _ (by norm_num)
  have hright_ne : ((-1 : ℝ) ^ (n + 1)) ≠ 0 := by exact pow_ne_zero _ (by norm_num)
  have hscaled : Prec (C ((-1 : ℝ) ^ n) * Q n)
      (C ((-1 : ℝ) ^ (n + 1)) * Q (n + 1)) :=
    prec_C_mul_right (prec_C_mul_left (hQprec n) hleft_ne) hright_ne
  have hleft_eq : C ((-1 : ℝ) ^ n) * Q n = P n := by
    dsimp [Q]
    rw [← mul_assoc, ← C_mul, neg_one_pow_mul_self n]
    simp
  have hright_eq : C ((-1 : ℝ) ^ (n + 1)) * Q (n + 1) = P (n + 1) := by
    dsimp [Q]
    rw [← mul_assoc, ← C_mul, neg_one_pow_mul_self (n + 1)]
    simp
  rwa [hleft_eq, hright_eq] at hscaled

/-- Real-rootedness consequence of row-sign normalized affine Favard. -/
theorem isRealRooted_of_favard_affine_const_coeff_rowSign
    {P : Nat → ℝ[X]} {s α β : ℝ}
    (hs : 0 < s)
    (hβ : 0 < β)
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C s * X - C α))
    (hstep : ∀ n : Nat,
      P (n + 2) = -(C s * X - C α) * P (n + 1) - C β * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_prec_chain_from_step <|
    favardInterlacing_affine_const_coeff_rowSign hs hβ hP0 hP1 hstep

/-- Nonzero consequence of row-sign normalized affine Favard. -/
theorem nonzero_of_favard_affine_const_coeff_rowSign
    {P : Nat → ℝ[X]} {s α β : ℝ}
    (hs : 0 < s)
    (hβ : 0 < β)
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C s * X - C α))
    (hstep : ∀ n : Nat,
      P (n + 2) = -(C s * X - C α) * P (n + 1) - C β * P n) :
    ∀ n : Nat, P n ≠ 0 :=
  ne_zero_of_isRealRooted_sequence <|
    isRealRooted_of_favard_affine_const_coeff_rowSign hs hβ hP0 hP1 hstep


/-- Positive-slope parameterized affine Favard wrapper after row-sign
normalization.  This packages
`P_{n+2}=-(s_{n+1}X-α_{n+1})P_{n+1}-β_{n+1}P_n`, with positive slopes and
positive lags, by applying Favard to `Q_n=(-1)^n P_n`. -/
theorem favardInterlacing_affine_param_coeff_rowSign
    {P : Nat → ℝ[X]} {s α β : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (s 0) * X - C (α 0)))
    (hstep : ∀ n : Nat,
      P (n + 2) =
        -(C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1) -
          C (β (n + 1)) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  let Q : Nat → ℝ[X] := fun n => C ((-1 : ℝ) ^ n) * P n
  have hQ0 : Q 0 = 1 := by simp [Q, hP0]
  have hQ1 : Q 1 = C (s 0) * X - C (α 0) := by simp [Q, hP1]
  have hQstep : ∀ n : Nat,
      Q (n + 2) =
        (C (s (n + 1)) * X - C (α (n + 1))) * Q (n + 1) -
          C (β (n + 1)) * Q n := by
    intro n
    dsimp [Q]
    rw [neg_one_pow_add_two n, neg_one_pow_succ n, hstep n, C_neg]
    ring_nf
  have hQprec : ∀ n : Nat, Prec (Q n) (Q (n + 1)) :=
    favardInterlacing_affine_param_coeff hs hβ hQ0 hQ1 hQstep
  intro n
  have hleft_ne : ((-1 : ℝ) ^ n) ≠ 0 := by exact pow_ne_zero _ (by norm_num)
  have hright_ne : ((-1 : ℝ) ^ (n + 1)) ≠ 0 := by exact pow_ne_zero _ (by norm_num)
  have hscaled : Prec (C ((-1 : ℝ) ^ n) * Q n)
      (C ((-1 : ℝ) ^ (n + 1)) * Q (n + 1)) :=
    prec_C_mul_right (prec_C_mul_left (hQprec n) hleft_ne) hright_ne
  have hleft_eq : C ((-1 : ℝ) ^ n) * Q n = P n := by
    dsimp [Q]
    rw [← mul_assoc, ← C_mul, neg_one_pow_mul_self n]
    simp
  have hright_eq : C ((-1 : ℝ) ^ (n + 1)) * Q (n + 1) = P (n + 1) := by
    dsimp [Q]
    rw [← mul_assoc, ← C_mul, neg_one_pow_mul_self (n + 1)]
    simp
  rwa [hleft_eq, hright_eq] at hscaled

/-- Real-rootedness consequence of parameterized row-sign affine Favard. -/
theorem isRealRooted_of_favard_affine_param_coeff_rowSign
    {P : Nat → ℝ[X]} {s α β : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (s 0) * X - C (α 0)))
    (hstep : ∀ n : Nat,
      P (n + 2) =
        -(C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1) -
          C (β (n + 1)) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_prec_chain_from_step <|
    favardInterlacing_affine_param_coeff_rowSign hs hβ hP0 hP1 hstep

/-- Nonzero consequence of parameterized row-sign affine Favard. -/
theorem nonzero_of_favard_affine_param_coeff_rowSign
    {P : Nat → ℝ[X]} {s α β : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (s 0) * X - C (α 0)))
    (hstep : ∀ n : Nat,
      P (n + 2) =
        -(C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1) -
          C (β (n + 1)) * P n) :
    ∀ n : Nat, P n ≠ 0 :=
  ne_zero_of_isRealRooted_sequence <|
    isRealRooted_of_favard_affine_param_coeff_rowSign hs hβ hP0 hP1 hstep

/-- Row-sign parameterized affine Favard wrapper with a scalar left
denominator in the displayed recurrence. -/
theorem favardInterlacing_affine_param_coeff_rowSign_den
    {P : Nat → ℝ[X]} {s α β d : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (s 0) * X - C (α 0)))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) *
          (-(C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1) -
            C (β (n + 1)) * P n)) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  favardInterlacing_affine_param_coeff_rowSign hs hβ hP0 hP1 <|
    fun n => eq_of_C_mul_eq_C_mul (hden n) (hraw n)

/-- Real-rootedness consequence of scalar-denominator row-sign Favard. -/
theorem isRealRooted_of_favard_affine_param_coeff_rowSign_den
    {P : Nat → ℝ[X]} {s α β d : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (s 0) * X - C (α 0)))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) *
          (-(C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1) -
            C (β (n + 1)) * P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_prec_chain_from_step <|
    favardInterlacing_affine_param_coeff_rowSign_den hs hβ hP0 hP1 hden hraw

/-- Nonzero consequence of scalar-denominator row-sign Favard. -/
theorem nonzero_of_favard_affine_param_coeff_rowSign_den
    {P : Nat → ℝ[X]} {s α β d : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (s 0) * X - C (α 0)))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) *
          (-(C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1) -
            C (β (n + 1)) * P n)) :
    ∀ n : Nat, P n ≠ 0 :=
  ne_zero_of_isRealRooted_sequence <|
    isRealRooted_of_favard_affine_param_coeff_rowSign_den hs hβ hP0 hP1 hden hraw

/-- Row-sign parameterized affine Favard wrapper with a scalar denominator
distributed across the two displayed summands. -/
theorem favardInterlacing_affine_param_coeff_rowSign_den_split
    {P : Nat → ℝ[X]} {s α β d : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (s 0) * X - C (α 0)))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (-(C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1)) -
          C (d n * β (n + 1)) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  favardInterlacing_affine_param_coeff_rowSign hs hβ hP0 hP1 fun n =>
    eq_sub_C_mul_of_C_mul_eq_C_mul_sub_C_mul (hden n) (hraw n)

/-- Real-rootedness consequence of distributed scalar-denominator row-sign
Favard. -/
theorem isRealRooted_of_favard_affine_param_coeff_rowSign_den_split
    {P : Nat → ℝ[X]} {s α β d : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (s 0) * X - C (α 0)))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (-(C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1)) -
          C (d n * β (n + 1)) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_prec_chain_from_step <|
    favardInterlacing_affine_param_coeff_rowSign_den_split hs hβ hP0 hP1 hden hraw

/-- Nonzero consequence of distributed scalar-denominator row-sign Favard. -/
theorem nonzero_of_favard_affine_param_coeff_rowSign_den_split
    {P : Nat → ℝ[X]} {s α β d : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (s 0) * X - C (α 0)))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (-(C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1)) -
          C (d n * β (n + 1)) * P n) :
    ∀ n : Nat, P n ≠ 0 :=
  ne_zero_of_isRealRooted_sequence <|
    isRealRooted_of_favard_affine_param_coeff_rowSign_den_split
      hs hβ hP0 hP1 hden hraw

/-- Distributed scalar-denominator row-sign Favard wrapper where the displayed
lag coefficient is written in the reversed scalar order `β_{n+1} d_n`. -/
theorem favardInterlacing_affine_param_coeff_rowSign_den_split_rev
    {P : Nat → ℝ[X]} {s α β d : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (s 0) * X - C (α 0)))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (-(C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1)) -
          C (β (n + 1) * d n) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  favardInterlacing_affine_param_coeff_rowSign_den_split hs hβ hP0 hP1 hden <| by
    intro n
    have hcomm : β (n + 1) * d n = d n * β (n + 1) := by ring
    simpa [hcomm] using hraw n

/-- Real-rootedness consequence of reversed-coefficient distributed
scalar-denominator row-sign Favard. -/
theorem isRealRooted_of_favard_affine_param_coeff_rowSign_den_split_rev
    {P : Nat → ℝ[X]} {s α β d : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (s 0) * X - C (α 0)))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (-(C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1)) -
          C (β (n + 1) * d n) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_prec_chain_from_step <|
    favardInterlacing_affine_param_coeff_rowSign_den_split_rev
      hs hβ hP0 hP1 hden hraw

/-- Nonzero consequence of reversed-coefficient distributed scalar-denominator
row-sign Favard. -/
theorem nonzero_of_favard_affine_param_coeff_rowSign_den_split_rev
    {P : Nat → ℝ[X]} {s α β d : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (s 0) * X - C (α 0)))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * (-(C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1)) -
          C (β (n + 1) * d n) * P n) :
    ∀ n : Nat, P n ≠ 0 :=
  ne_zero_of_isRealRooted_sequence <|
    isRealRooted_of_favard_affine_param_coeff_rowSign_den_split_rev
      hs hβ hP0 hP1 hden hraw

/-- Row-sign parameterized affine Favard wrapper with a scalar left
denominator and raw affine numerator coefficients. -/
theorem favardInterlacing_affine_param_coeff_rowSign_den_raw
    {P : Nat → ℝ[X]} {s α β d araw braw craw : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (s 0) * X - C (α 0)))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hs_coeff : ∀ n : Nat, -((d n)⁻¹ * araw n) = s (n + 1))
    (hα_coeff : ∀ n : Nat, (d n)⁻¹ * braw n = α (n + 1))
    (hβ_coeff : ∀ n : Nat, -((d n)⁻¹ * craw n) = β (n + 1))
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        (C (araw n) * X + C (braw n)) * P (n + 1) + C (craw n) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  favardInterlacing_affine_param_coeff_rowSign hs hβ hP0 hP1 <| by
    intro n
    have hnorm :
        P (n + 2) =
          C (d n)⁻¹ *
            ((C (araw n) * X + C (braw n)) * P (n + 1) + C (craw n) * P n) :=
      eq_C_inv_mul_of_C_mul_eq (hden n) (hraw n)
    calc
      P (n + 2) =
          C (d n)⁻¹ *
            ((C (araw n) * X + C (braw n)) * P (n + 1) + C (craw n) * P n) :=
        hnorm
      _ =
          -(C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1) -
            C (β (n + 1)) * P n := by
        rw [← hs_coeff n, ← hα_coeff n, ← hβ_coeff n]
        simp [C_mul, C_neg, sub_eq_add_neg]
        ring_nf

/-- Real-rootedness consequence of raw-affine scalar-denominator row-sign
Favard. -/
theorem isRealRooted_of_favard_affine_param_coeff_rowSign_den_raw
    {P : Nat → ℝ[X]} {s α β d araw braw craw : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (s 0) * X - C (α 0)))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hs_coeff : ∀ n : Nat, -((d n)⁻¹ * araw n) = s (n + 1))
    (hα_coeff : ∀ n : Nat, (d n)⁻¹ * braw n = α (n + 1))
    (hβ_coeff : ∀ n : Nat, -((d n)⁻¹ * craw n) = β (n + 1))
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        (C (araw n) * X + C (braw n)) * P (n + 1) + C (craw n) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_prec_chain_from_step <|
    favardInterlacing_affine_param_coeff_rowSign_den_raw
      hs hβ hP0 hP1 hden hs_coeff hα_coeff hβ_coeff hraw

/-- Nonzero consequence of raw-affine scalar-denominator row-sign Favard. -/
theorem nonzero_of_favard_affine_param_coeff_rowSign_den_raw
    {P : Nat → ℝ[X]} {s α β d araw braw craw : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (s 0) * X - C (α 0)))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hs_coeff : ∀ n : Nat, -((d n)⁻¹ * araw n) = s (n + 1))
    (hα_coeff : ∀ n : Nat, (d n)⁻¹ * braw n = α (n + 1))
    (hβ_coeff : ∀ n : Nat, -((d n)⁻¹ * craw n) = β (n + 1))
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        (C (araw n) * X + C (braw n)) * P (n + 1) + C (craw n) * P n) :
    ∀ n : Nat, P n ≠ 0 :=
  ne_zero_of_isRealRooted_sequence <|
    isRealRooted_of_favard_affine_param_coeff_rowSign_den_raw
      hs hβ hP0 hP1 hden hs_coeff hα_coeff hβ_coeff hraw

/-- Row-sign raw-affine scalar-denominator Favard where the displayed slope and
lag coefficients are written as products of two constants. -/
theorem favardInterlacing_affine_param_coeff_rowSign_den_raw_prod
    {P : Nat → ℝ[X]} {s α β d aleft aright braw cleft cright : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (s 0) * X - C (α 0)))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hs_coeff : ∀ n : Nat, -((d n)⁻¹ * (aleft n * aright n)) = s (n + 1))
    (hα_coeff : ∀ n : Nat, (d n)⁻¹ * braw n = α (n + 1))
    (hβ_coeff : ∀ n : Nat, -((d n)⁻¹ * (cleft n * cright n)) = β (n + 1))
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        (C (aleft n) * C (aright n) * X + C (braw n)) * P (n + 1) +
          C (cleft n) * C (cright n) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  favardInterlacing_affine_param_coeff_rowSign_den_raw
    (s := s) (α := α) (β := β) (d := d)
    (araw := fun n => aleft n * aright n)
    (braw := braw) (craw := fun n => cleft n * cright n)
    hs hβ hP0 hP1 hden hs_coeff hα_coeff hβ_coeff <| by
      intro n
      simpa [C_mul, mul_assoc] using hraw n

/-- Real-rootedness consequence of product-form raw-affine scalar-denominator
row-sign Favard. -/
theorem isRealRooted_of_favard_affine_param_coeff_rowSign_den_raw_prod
    {P : Nat → ℝ[X]} {s α β d aleft aright braw cleft cright : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (s 0) * X - C (α 0)))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hs_coeff : ∀ n : Nat, -((d n)⁻¹ * (aleft n * aright n)) = s (n + 1))
    (hα_coeff : ∀ n : Nat, (d n)⁻¹ * braw n = α (n + 1))
    (hβ_coeff : ∀ n : Nat, -((d n)⁻¹ * (cleft n * cright n)) = β (n + 1))
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        (C (aleft n) * C (aright n) * X + C (braw n)) * P (n + 1) +
          C (cleft n) * C (cright n) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_prec_chain_from_step <|
    favardInterlacing_affine_param_coeff_rowSign_den_raw_prod
      hs hβ hP0 hP1 hden hs_coeff hα_coeff hβ_coeff hraw

/-- Nonzero consequence of product-form raw-affine scalar-denominator row-sign
Favard. -/
theorem nonzero_of_favard_affine_param_coeff_rowSign_den_raw_prod
    {P : Nat → ℝ[X]} {s α β d aleft aright braw cleft cright : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = -(C (s 0) * X - C (α 0)))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hs_coeff : ∀ n : Nat, -((d n)⁻¹ * (aleft n * aright n)) = s (n + 1))
    (hα_coeff : ∀ n : Nat, (d n)⁻¹ * braw n = α (n + 1))
    (hβ_coeff : ∀ n : Nat, -((d n)⁻¹ * (cleft n * cright n)) = β (n + 1))
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        (C (aleft n) * C (aright n) * X + C (braw n)) * P (n + 1) +
          C (cleft n) * C (cright n) * P n) :
    ∀ n : Nat, P n ≠ 0 :=
  ne_zero_of_isRealRooted_sequence <|
    isRealRooted_of_favard_affine_param_coeff_rowSign_den_raw_prod
      hs hβ hP0 hP1 hden hs_coeff hα_coeff hβ_coeff hraw

end RealRooted
