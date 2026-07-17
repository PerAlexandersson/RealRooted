import RealRooted.Favard
import RealRooted.Tactic.Finish
import RealRooted.Tactic.ScalarDen
import RealRooted.Tactic.SideGoals

open Polynomial

/-!
# Favard tactic

The tactic

```lean
rr_favard using hrec, hbeta
```

applies the already-formalized Favard interface to goals that match
`favardInterlacing`,
`isRealRooted_of_favard`, or
`isGeneralizedSturmSeq_reverse_range_map_of_favard`.

First intended regression examples:

- Chebyshev-like examples;
- OEIS Family F examples after small wrapper definitions exist.
-/

namespace RealRooted

private lemma C_mul_X_sub_C_eq_C_mul_X_sub_C_div {s t : ℝ} (hs : s ≠ 0) :
    (C s * X - C t : ℝ[X]) = C s * (X - C (t / s)) := by
  ring_nf
  rw [← C_mul]
  congr 1
  field_simp [hs]

private lemma natDegree_C_mul_X_sub_C {s t : ℝ} (hs : s ≠ 0) :
    (C s * X - C t : ℝ[X]).natDegree = 1 := by
  rw [C_mul_X_sub_C_eq_C_mul_X_sub_C_div hs]
  rw [Polynomial.natDegree_C_mul hs, natDegree_X_sub_C]

private lemma hasPosLeadingCoeff_C_mul_X_sub_C {s t : ℝ} (hs : 0 < s) :
    HasPosLeadingCoeff (C s * X - C t : ℝ[X]) := by
  rw [C_mul_X_sub_C_eq_C_mul_X_sub_C_div hs.ne']
  unfold HasPosLeadingCoeff
  rw [Polynomial.leadingCoeff_mul, leadingCoeff_C, leadingCoeff_X_sub_C]
  simpa using hs

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

/-- Constant-coefficient Favard wrapper.  This packages the recurring
Chebyshev-style shape
`P_{n+2} = (X - α) P_{n+1} - β P_n`, with `β > 0`. -/
theorem favardInterlacing_const_coeff {P : Nat → ℝ[X]} {α β : ℝ}
    (hβ : 0 < β)
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X - C α)
    (hstep : ∀ n : Nat, P (n + 2) = (X - C α) * P (n + 1) - C β * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  have hrec : SatisfiesFavardRecurrence P (fun _ => α) (fun _ => β) :=
    ⟨hP0, hP1, by
      intro n
      simpa using hstep n⟩
  exact favardInterlacing hrec (by intro n; simpa using hβ)

/-- Real-rootedness consequence of the constant-coefficient Favard wrapper. -/
theorem isRealRooted_of_favard_const_coeff {P : Nat → ℝ[X]} {α β : ℝ}
    (hβ : 0 < β)
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X - C α)
    (hstep : ∀ n : Nat, P (n + 2) = (X - C α) * P (n + 1) - C β * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  have hrec : SatisfiesFavardRecurrence P (fun _ => α) (fun _ => β) :=
    ⟨hP0, hP1, by
      intro n
      simpa using hstep n⟩
  exact isRealRooted_of_favard hrec (by intro n; simpa using hβ)

/-- Nonzero consequence of the constant-coefficient Favard wrapper. -/
theorem nonzero_of_favard_const_coeff {P : Nat → ℝ[X]} {α β : ℝ}
    (hβ : 0 < β)
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X - C α)
    (hstep : ∀ n : Nat, P (n + 2) = (X - C α) * P (n + 1) - C β * P n) :
    ∀ n : Nat, P n ≠ 0 :=
  fun n => (isRealRooted_of_favard_const_coeff hβ hP0 hP1 hstep n).1

/-- Parameterized Favard wrapper.  This packages the monic shape
`P_{n+2} = (X - α_{n+1}) P_{n+1} - β_{n+1} P_n`, with `β_{n+1} > 0`. -/
theorem favardInterlacing_param_coeff {P : Nat → ℝ[X]} {α β : Nat → ℝ}
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X - C (α 0))
    (hstep : ∀ n : Nat,
      P (n + 2) = (X - C (α (n + 1))) * P (n + 1) - C (β (n + 1)) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  exact favardInterlacing ⟨hP0, hP1, hstep⟩ hβ

/-- Real-rootedness consequence of the parameterized Favard wrapper. -/
theorem isRealRooted_of_favard_param_coeff {P : Nat → ℝ[X]} {α β : Nat → ℝ}
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X - C (α 0))
    (hstep : ∀ n : Nat,
      P (n + 2) = (X - C (α (n + 1))) * P (n + 1) - C (β (n + 1)) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits := by
  exact isRealRooted_of_favard ⟨hP0, hP1, hstep⟩ hβ

/-- Nonzero consequence of the parameterized Favard wrapper. -/
theorem nonzero_of_favard_param_coeff {P : Nat → ℝ[X]} {α β : Nat → ℝ}
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X - C (α 0))
    (hstep : ∀ n : Nat,
      P (n + 2) = (X - C (α (n + 1))) * P (n + 1) - C (β (n + 1)) * P n) :
    ∀ n : Nat, P n ≠ 0 :=
  fun n => (isRealRooted_of_favard_param_coeff hβ hP0 hP1 hstep n).1

/-- Positive-slope affine Favard wrapper.  This packages the recurring
nonmonic Chebyshev-style shape
`P_{n+2} = (sX - α) P_{n+1} - β P_n`, with `s > 0` and `β > 0`. -/
theorem favardInterlacing_affine_const_coeff {P : Nat → ℝ[X]} {s α β : ℝ}
    (hs : 0 < s)
    (hβ : 0 < β)
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C s * X - C α)
    (hstep : ∀ n : Nat, P (n + 2) = (C s * X - C α) * P (n + 1) - C β * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  let aPoly : ℝ[X] := C s * X - C α
  let bPoly : ℝ[X] := C (-β)
  have hA_deg : aPoly.natDegree = 1 := by
    simpa [aPoly] using natDegree_C_mul_X_sub_C (s := s) (t := α) hs.ne'
  have hA_ne : aPoly ≠ 0 := by
    intro h
    simp [h] at hA_deg
  have hA_pos : HasPosLeadingCoeff aPoly := by
    simpa [aPoly] using hasPosLeadingCoeff_C_mul_X_sub_C (s := s) (t := α) hs
  let Q : Nat → Prop := fun n =>
    Interlaces (P n) (P (n + 1)) ∧
      HasPosLeadingCoeff (P n) ∧
      HasPosLeadingCoeff (P (n + 1))
  have hQ : ∀ n : Nat, Q n := by
    intro n
    induction n with
    | zero =>
        refine ⟨?_, ?_, ?_⟩
        · rw [hP0, hP1]
          exact interlaces_one_linear (by simpa [aPoly] using hA_deg)
        · rw [hP0]
          unfold HasPosLeadingCoeff
          simp
        · rw [hP1]
          simpa [aPoly] using hA_pos
    | succ n ih =>
        rcases ih with ⟨hInter, hPos_n, hPos_n1⟩
        let f : ℝ[X] := P (n + 1)
        let g : ℝ[X] := P n
        have hdeg_gf : g.natDegree + 1 = f.natDegree := by
          simpa [f, g] using natDegree_succ_of_interlaces hInter
        have hf_ne : f ≠ 0 := by
          simpa [f] using right_ne_zero_of_interlaces hInter
        have hAf_deg : (aPoly * f).natDegree = f.natDegree + 1 := by
          rw [natDegree_mul hA_ne hf_ne, hA_deg]
          lia
        have hAf_pos : HasPosLeadingCoeff (aPoly * f) := by
          unfold HasPosLeadingCoeff at hA_pos hPos_n1 ⊢
          simpa [Polynomial.leadingCoeff_mul] using mul_pos hA_pos hPos_n1
        have hBg_lt_Af : (bPoly * g).natDegree < (aPoly * f).natDegree := by
          have hBg_le : (bPoly * g).natDegree ≤ g.natDegree := by
            dsimp [bPoly]
            exact Polynomial.natDegree_C_mul_le _ _
          lia
        have hF_pos_aux : HasPosLeadingCoeff (bPoly * g + aPoly * f) :=
          hasPosLeadingCoeff_add_of_natDegree_lt_right hBg_lt_Af hAf_pos
        have hF_pos : HasPosLeadingCoeff (aPoly * f + bPoly * g) := by grind
        have hF_deg :
            (aPoly * f + bPoly * g).natDegree = f.natDegree + 1 := by
          have hdeg_aux :
              (bPoly * g + aPoly * f).natDegree = (aPoly * f).natDegree :=
            natDegree_add_eq_right_of_natDegree_lt_of_posLeadingCoeff hBg_lt_Af hAf_pos
          grind
        have hdeg_lo : f.natDegree ≤ (aPoly * f + bPoly * g).natDegree := by lia
        have hdeg_hi : (aPoly * f + bPoly * g).natDegree ≤ f.natDegree + 1 := by lia
        have hb_nonpos : ∀ r, f.IsRoot r → bPoly.eval r ≤ 0 := by
          intros
          have hb_le : 0 ≤ β := hβ.le
          simpa [bPoly] using (neg_nonpos.mpr hb_le)
        have hPrec_step : Prec f (aPoly * f + bPoly * g) :=
          prec_of_interlaces_evalCoeff_nonpos
            (f := f) (g := g) (a := aPoly) (b := bPoly)
            hInter hPos_n hF_pos hdeg_lo hdeg_hi hb_nonpos
        have hInter_step : Interlaces f (aPoly * f + bPoly * g) :=
          hPrec_step.toInterlaces (by lia)
        grind
  exact fun n => (hQ n).1.toPrec

/-- Real-rootedness consequence of the positive-slope affine Favard wrapper. -/
theorem isRealRooted_of_favard_affine_const_coeff {P : Nat → ℝ[X]} {s α β : ℝ}
    (hs : 0 < s)
    (hβ : 0 < β)
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C s * X - C α)
    (hstep : ∀ n : Nat, P (n + 2) = (C s * X - C α) * P (n + 1) - C β * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  fun n => (favardInterlacing_affine_const_coeff hs hβ hP0 hP1 hstep n).1

/-- Nonzero consequence of the positive-slope affine Favard wrapper. -/
theorem nonzero_of_favard_affine_const_coeff {P : Nat → ℝ[X]} {s α β : ℝ}
    (hs : 0 < s)
    (hβ : 0 < β)
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C s * X - C α)
    (hstep : ∀ n : Nat, P (n + 2) = (C s * X - C α) * P (n + 1) - C β * P n) :
    ∀ n : Nat, P n ≠ 0 :=
  fun n => (isRealRooted_of_favard_affine_const_coeff hs hβ hP0 hP1 hstep n).1

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
  have hQ0 : Q 0 = 1 := by
    simp [Q, hP0]
  have hQ1 : Q 1 = C s * X - C α := by
    simp [Q, hP1]
  have hQstep : ∀ n : Nat,
      Q (n + 2) = (C s * X - C α) * Q (n + 1) - C β * Q n := by
    intro n
    dsimp [Q]
    rw [neg_one_pow_add_two n, neg_one_pow_succ n, hstep n, C_neg]
    ring_nf
  have hQprec : ∀ n : Nat, Prec (Q n) (Q (n + 1)) :=
    favardInterlacing_affine_const_coeff hs hβ hQ0 hQ1 hQstep
  intro n
  have hleft_ne : ((-1 : ℝ) ^ n) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hright_ne : ((-1 : ℝ) ^ (n + 1)) ≠ 0 := pow_ne_zero _ (by norm_num)
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
  fun n => (favardInterlacing_affine_const_coeff_rowSign hs hβ hP0 hP1 hstep n).1

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
  fun n =>
    (isRealRooted_of_favard_affine_const_coeff_rowSign hs hβ hP0 hP1 hstep n).1

/-- Positive-slope parameterized affine Favard wrapper.  This packages
`P_{n+2} = (s_{n+1} X - α_{n+1}) P_{n+1} - β_{n+1} P_n`, with positive
slopes and positive lags. -/
theorem favardInterlacing_affine_param_coeff
    {P : Nat → ℝ[X]} {s α β : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (s 0) * X - C (α 0))
    (hstep : ∀ n : Nat,
      P (n + 2) =
        (C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1) -
          C (β (n + 1)) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) := by
  let Q : Nat → Prop := fun n =>
    Interlaces (P n) (P (n + 1)) ∧
      HasPosLeadingCoeff (P n) ∧
      HasPosLeadingCoeff (P (n + 1))
  have hQ : ∀ n : Nat, Q n := by
    intro n
    induction n with
    | zero =>
        let aPoly : ℝ[X] := C (s 0) * X - C (α 0)
        have hA_deg : aPoly.natDegree = 1 := by
          simpa [aPoly] using natDegree_C_mul_X_sub_C (s := s 0) (t := α 0) (hs 0).ne'
        have hA_pos : HasPosLeadingCoeff aPoly := by
          simpa [aPoly] using hasPosLeadingCoeff_C_mul_X_sub_C (s := s 0) (t := α 0)
            (hs 0)
        refine ⟨?_, ?_, ?_⟩
        · rw [hP0, hP1]
          exact interlaces_one_linear (by simpa [aPoly] using hA_deg)
        · rw [hP0]
          unfold HasPosLeadingCoeff
          simp
        · rw [hP1]
          simpa [aPoly] using hA_pos
    | succ n ih =>
        rcases ih with ⟨hInter, hPos_n, hPos_n1⟩
        let f : ℝ[X] := P (n + 1)
        let g : ℝ[X] := P n
        let aPoly : ℝ[X] := C (s (n + 1)) * X - C (α (n + 1))
        let bPoly : ℝ[X] := C (-β (n + 1))
        have hA_deg : aPoly.natDegree = 1 := by
          simpa [aPoly] using
            natDegree_C_mul_X_sub_C (s := s (n + 1)) (t := α (n + 1))
              (hs (n + 1)).ne'
        have hA_ne : aPoly ≠ 0 := by
          intro h
          simp [h] at hA_deg
        have hA_pos : HasPosLeadingCoeff aPoly := by
          simpa [aPoly] using
            hasPosLeadingCoeff_C_mul_X_sub_C (s := s (n + 1)) (t := α (n + 1))
              (hs (n + 1))
        have hdeg_gf : g.natDegree + 1 = f.natDegree := by
          simpa [f, g] using natDegree_succ_of_interlaces hInter
        have hf_ne : f ≠ 0 := by
          simpa [f] using right_ne_zero_of_interlaces hInter
        have hAf_deg : (aPoly * f).natDegree = f.natDegree + 1 := by
          rw [natDegree_mul hA_ne hf_ne, hA_deg]
          lia
        have hAf_pos : HasPosLeadingCoeff (aPoly * f) := by
          unfold HasPosLeadingCoeff at hA_pos hPos_n1 ⊢
          simpa [Polynomial.leadingCoeff_mul] using mul_pos hA_pos hPos_n1
        have hBg_lt_Af : (bPoly * g).natDegree < (aPoly * f).natDegree := by
          have hBg_le : (bPoly * g).natDegree ≤ g.natDegree := by
            dsimp [bPoly]
            exact Polynomial.natDegree_C_mul_le _ _
          lia
        have hF_pos_aux : HasPosLeadingCoeff (bPoly * g + aPoly * f) :=
          hasPosLeadingCoeff_add_of_natDegree_lt_right hBg_lt_Af hAf_pos
        have hF_pos : HasPosLeadingCoeff (aPoly * f + bPoly * g) := by grind
        have hF_deg :
            (aPoly * f + bPoly * g).natDegree = f.natDegree + 1 := by
          have hdeg_aux :
              (bPoly * g + aPoly * f).natDegree = (aPoly * f).natDegree :=
            natDegree_add_eq_right_of_natDegree_lt_of_posLeadingCoeff hBg_lt_Af hAf_pos
          grind
        have hdeg_lo : f.natDegree ≤ (aPoly * f + bPoly * g).natDegree := by lia
        have hdeg_hi : (aPoly * f + bPoly * g).natDegree ≤ f.natDegree + 1 := by lia
        have hb_nonpos : ∀ r, f.IsRoot r → bPoly.eval r ≤ 0 := by
          intros
          have hb_le : 0 ≤ β (n + 1) := (hβ n).le
          simpa [bPoly] using (neg_nonpos.mpr hb_le)
        have hPrec_step : Prec f (aPoly * f + bPoly * g) :=
          prec_of_interlaces_evalCoeff_nonpos
            (f := f) (g := g) (a := aPoly) (b := bPoly)
            hInter hPos_n hF_pos hdeg_lo hdeg_hi hb_nonpos
        have hInter_step : Interlaces f (aPoly * f + bPoly * g) :=
          hPrec_step.toInterlaces (by lia)
        grind
  exact fun n => (hQ n).1.toPrec

/-- Real-rootedness consequence of the positive-slope parameterized affine
Favard wrapper. -/
theorem isRealRooted_of_favard_affine_param_coeff
    {P : Nat → ℝ[X]} {s α β : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (s 0) * X - C (α 0))
    (hstep : ∀ n : Nat,
      P (n + 2) =
        (C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1) -
          C (β (n + 1)) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  fun n => (favardInterlacing_affine_param_coeff hs hβ hP0 hP1 hstep n).1

/-- Nonzero consequence of the positive-slope parameterized affine Favard
wrapper. -/
theorem nonzero_of_favard_affine_param_coeff
    {P : Nat → ℝ[X]} {s α β : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (s 0) * X - C (α 0))
    (hstep : ∀ n : Nat,
      P (n + 2) =
        (C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1) -
          C (β (n + 1)) * P n) :
    ∀ n : Nat, P n ≠ 0 :=
  fun n => (isRealRooted_of_favard_affine_param_coeff hs hβ hP0 hP1 hstep n).1

/-- Positive-slope parameterized affine Favard wrapper with a scalar left
denominator in the displayed recurrence. -/
theorem favardInterlacing_affine_param_coeff_den
    {P : Nat → ℝ[X]} {s α β d : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (s 0) * X - C (α 0))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) *
          ((C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1) -
            C (β (n + 1)) * P n)) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  favardInterlacing_affine_param_coeff hs hβ hP0 hP1 <|
    fun n => eq_of_C_mul_eq_C_mul (hden n) (hraw n)

/-- Real-rootedness consequence of the scalar-denominator parameterized affine
Favard wrapper. -/
theorem isRealRooted_of_favard_affine_param_coeff_den
    {P : Nat → ℝ[X]} {s α β d : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (s 0) * X - C (α 0))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) *
          ((C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1) -
            C (β (n + 1)) * P n)) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  fun n => (favardInterlacing_affine_param_coeff_den hs hβ hP0 hP1 hden hraw n).1

/-- Nonzero consequence of the scalar-denominator parameterized affine Favard
wrapper. -/
theorem nonzero_of_favard_affine_param_coeff_den
    {P : Nat → ℝ[X]} {s α β d : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (s 0) * X - C (α 0))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) *
          ((C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1) -
            C (β (n + 1)) * P n)) :
    ∀ n : Nat, P n ≠ 0 :=
  fun n => (isRealRooted_of_favard_affine_param_coeff_den hs hβ hP0 hP1 hden hraw n).1

/-- Positive-slope parameterized affine Favard wrapper with a scalar left
denominator distributed across the two displayed summands. -/
theorem favardInterlacing_affine_param_coeff_den_split
    {P : Nat → ℝ[X]} {s α β d : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (s 0) * X - C (α 0))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * ((C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1)) -
          C (d n * β (n + 1)) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  favardInterlacing_affine_param_coeff hs hβ hP0 hP1 <| by
    intro n
    let A : ℝ[X] := (C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1)
    have hcoeff : (d n)⁻¹ * (-(d n * β (n + 1))) = -(β (n + 1)) := by
      field_simp [hden n]
    have hsplit :
        C (d n) * P (n + 2) =
          C (d n) * A + C (-(d n * β (n + 1))) * P n := by
      simpa [A, sub_eq_add_neg, C_neg, add_comm, add_left_comm, add_assoc,
        mul_assoc] using hraw n
    have hnorm :
        P (n + 2) = A + C (-(β (n + 1))) * P n :=
      eq_add_C_mul_of_C_mul_eq_C_mul_add_C_mul (hden n) hcoeff hsplit
    calc
      P (n + 2) = A + C (-(β (n + 1))) * P n := hnorm
      _ =
          (C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1) -
            C (β (n + 1)) * P n := by
        simp [A, sub_eq_add_neg]

/-- Real-rootedness consequence of the distributed scalar-denominator affine
Favard wrapper. -/
theorem isRealRooted_of_favard_affine_param_coeff_den_split
    {P : Nat → ℝ[X]} {s α β d : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (s 0) * X - C (α 0))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * ((C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1)) -
          C (d n * β (n + 1)) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  fun n =>
    (favardInterlacing_affine_param_coeff_den_split hs hβ hP0 hP1 hden hraw n).1

/-- Nonzero consequence of the distributed scalar-denominator affine Favard
wrapper. -/
theorem nonzero_of_favard_affine_param_coeff_den_split
    {P : Nat → ℝ[X]} {s α β d : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (s 0) * X - C (α 0))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * ((C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1)) -
          C (d n * β (n + 1)) * P n) :
    ∀ n : Nat, P n ≠ 0 :=
  fun n =>
    (isRealRooted_of_favard_affine_param_coeff_den_split hs hβ hP0 hP1 hden hraw n).1

/-- Distributed scalar-denominator affine Favard wrapper where the displayed
lag coefficient is written in the reversed scalar order `β_{n+1} d_n`. -/
theorem favardInterlacing_affine_param_coeff_den_split_rev
    {P : Nat → ℝ[X]} {s α β d : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (s 0) * X - C (α 0))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * ((C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1)) -
          C (β (n + 1) * d n) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  favardInterlacing_affine_param_coeff_den_split hs hβ hP0 hP1 hden <| by
    intro n
    have hcomm : β (n + 1) * d n = d n * β (n + 1) := by ring
    simpa [hcomm] using hraw n

/-- Real-rootedness consequence of reversed-coefficient distributed
scalar-denominator affine Favard. -/
theorem isRealRooted_of_favard_affine_param_coeff_den_split_rev
    {P : Nat → ℝ[X]} {s α β d : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (s 0) * X - C (α 0))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * ((C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1)) -
          C (β (n + 1) * d n) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  fun n =>
    (favardInterlacing_affine_param_coeff_den_split_rev hs hβ hP0 hP1 hden hraw n).1

/-- Nonzero consequence of reversed-coefficient distributed
scalar-denominator affine Favard. -/
theorem nonzero_of_favard_affine_param_coeff_den_split_rev
    {P : Nat → ℝ[X]} {s α β d : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (s 0) * X - C (α 0))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        C (d n) * ((C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1)) -
          C (β (n + 1) * d n) * P n) :
    ∀ n : Nat, P n ≠ 0 :=
  fun n =>
    (isRealRooted_of_favard_affine_param_coeff_den_split_rev
      hs hβ hP0 hP1 hden hraw n).1

/-- Positive-slope parameterized affine Favard wrapper with a scalar left
denominator and raw affine numerator coefficients.

This accepts OEIS-style recurrences where the numerator has not been factored
as `d_n` times the normalized Favard step.  The side equalities identify the
normalized slope, shift, and lag after division by `d_n`. -/
theorem favardInterlacing_affine_param_coeff_den_raw
    {P : Nat → ℝ[X]} {s α β d araw braw craw : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (s 0) * X - C (α 0))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hs_coeff : ∀ n : Nat, (d n)⁻¹ * araw n = s (n + 1))
    (hα_coeff : ∀ n : Nat, -((d n)⁻¹ * braw n) = α (n + 1))
    (hβ_coeff : ∀ n : Nat, -((d n)⁻¹ * craw n) = β (n + 1))
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        (C (araw n) * X + C (braw n)) * P (n + 1) + C (craw n) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  favardInterlacing_affine_param_coeff hs hβ hP0 hP1 <| by
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
          (C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1) -
            C (β (n + 1)) * P n := by
        rw [← hs_coeff n, ← hα_coeff n, ← hβ_coeff n]
        simp [C_mul, C_neg, sub_eq_add_neg]
        ring_nf

/-- Real-rootedness consequence of raw-affine scalar-denominator Favard. -/
theorem isRealRooted_of_favard_affine_param_coeff_den_raw
    {P : Nat → ℝ[X]} {s α β d araw braw craw : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (s 0) * X - C (α 0))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hs_coeff : ∀ n : Nat, (d n)⁻¹ * araw n = s (n + 1))
    (hα_coeff : ∀ n : Nat, -((d n)⁻¹ * braw n) = α (n + 1))
    (hβ_coeff : ∀ n : Nat, -((d n)⁻¹ * craw n) = β (n + 1))
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        (C (araw n) * X + C (braw n)) * P (n + 1) + C (craw n) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  fun n =>
    (favardInterlacing_affine_param_coeff_den_raw
      hs hβ hP0 hP1 hden hs_coeff hα_coeff hβ_coeff hraw n).1

/-- Nonzero consequence of raw-affine scalar-denominator Favard. -/
theorem nonzero_of_favard_affine_param_coeff_den_raw
    {P : Nat → ℝ[X]} {s α β d araw braw craw : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (s 0) * X - C (α 0))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hs_coeff : ∀ n : Nat, (d n)⁻¹ * araw n = s (n + 1))
    (hα_coeff : ∀ n : Nat, -((d n)⁻¹ * braw n) = α (n + 1))
    (hβ_coeff : ∀ n : Nat, -((d n)⁻¹ * craw n) = β (n + 1))
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        (C (araw n) * X + C (braw n)) * P (n + 1) + C (craw n) * P n) :
    ∀ n : Nat, P n ≠ 0 :=
  fun n =>
    (isRealRooted_of_favard_affine_param_coeff_den_raw
      hs hβ hP0 hP1 hden hs_coeff hα_coeff hβ_coeff hraw n).1

/-- Raw-affine scalar-denominator Favard where the displayed slope and lag
coefficients are written as products of two constants. -/
theorem favardInterlacing_affine_param_coeff_den_raw_prod
    {P : Nat → ℝ[X]} {s α β d aleft aright braw cleft cright : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (s 0) * X - C (α 0))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hs_coeff : ∀ n : Nat, (d n)⁻¹ * (aleft n * aright n) = s (n + 1))
    (hα_coeff : ∀ n : Nat, -((d n)⁻¹ * braw n) = α (n + 1))
    (hβ_coeff : ∀ n : Nat, -((d n)⁻¹ * (cleft n * cright n)) = β (n + 1))
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        (C (aleft n) * C (aright n) * X + C (braw n)) * P (n + 1) +
          C (cleft n) * C (cright n) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  favardInterlacing_affine_param_coeff_den_raw
    (s := s) (α := α) (β := β) (d := d)
    (araw := fun n => aleft n * aright n)
    (braw := braw) (craw := fun n => cleft n * cright n)
    hs hβ hP0 hP1 hden hs_coeff hα_coeff hβ_coeff <| by
      intro n
      simpa [C_mul, mul_assoc] using hraw n

/-- Real-rootedness consequence of product-form raw-affine scalar-denominator
Favard. -/
theorem isRealRooted_of_favard_affine_param_coeff_den_raw_prod
    {P : Nat → ℝ[X]} {s α β d aleft aright braw cleft cright : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (s 0) * X - C (α 0))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hs_coeff : ∀ n : Nat, (d n)⁻¹ * (aleft n * aright n) = s (n + 1))
    (hα_coeff : ∀ n : Nat, -((d n)⁻¹ * braw n) = α (n + 1))
    (hβ_coeff : ∀ n : Nat, -((d n)⁻¹ * (cleft n * cright n)) = β (n + 1))
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        (C (aleft n) * C (aright n) * X + C (braw n)) * P (n + 1) +
          C (cleft n) * C (cright n) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  fun n =>
    (favardInterlacing_affine_param_coeff_den_raw_prod
      hs hβ hP0 hP1 hden hs_coeff hα_coeff hβ_coeff hraw n).1

/-- Nonzero consequence of product-form raw-affine scalar-denominator Favard. -/
theorem nonzero_of_favard_affine_param_coeff_den_raw_prod
    {P : Nat → ℝ[X]} {s α β d aleft aright braw cleft cright : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (s 0) * X - C (α 0))
    (hden : ∀ n : Nat, d n ≠ 0)
    (hs_coeff : ∀ n : Nat, (d n)⁻¹ * (aleft n * aright n) = s (n + 1))
    (hα_coeff : ∀ n : Nat, -((d n)⁻¹ * braw n) = α (n + 1))
    (hβ_coeff : ∀ n : Nat, -((d n)⁻¹ * (cleft n * cright n)) = β (n + 1))
    (hraw : ∀ n : Nat,
      C (d n) * P (n + 2) =
        (C (aleft n) * C (aright n) * X + C (braw n)) * P (n + 1) +
          C (cleft n) * C (cright n) * P n) :
    ∀ n : Nat, P n ≠ 0 :=
  fun n =>
    (isRealRooted_of_favard_affine_param_coeff_den_raw_prod
      hs hβ hP0 hP1 hden hs_coeff hα_coeff hβ_coeff hraw n).1

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
  have hQ0 : Q 0 = 1 := by
    simp [Q, hP0]
  have hQ1 : Q 1 = C (s 0) * X - C (α 0) := by
    simp [Q, hP1]
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
  have hleft_ne : ((-1 : ℝ) ^ n) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hright_ne : ((-1 : ℝ) ^ (n + 1)) ≠ 0 := pow_ne_zero _ (by norm_num)
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
  fun n => (favardInterlacing_affine_param_coeff_rowSign hs hβ hP0 hP1 hstep n).1

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
  fun n =>
    (isRealRooted_of_favard_affine_param_coeff_rowSign hs hβ hP0 hP1 hstep n).1

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
  fun n =>
    (favardInterlacing_affine_param_coeff_rowSign_den hs hβ hP0 hP1 hden hraw n).1

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
  fun n =>
    (isRealRooted_of_favard_affine_param_coeff_rowSign_den hs hβ hP0 hP1 hden hraw n).1

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
  favardInterlacing_affine_param_coeff_rowSign hs hβ hP0 hP1 <| by
    intro n
    let A : ℝ[X] := -(C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1)
    have hcoeff : (d n)⁻¹ * (-(d n * β (n + 1))) = -(β (n + 1)) := by
      field_simp [hden n]
    have hsplit :
        C (d n) * P (n + 2) =
          C (d n) * A + C (-(d n * β (n + 1))) * P n := by
      rw [hraw n]
      simp [A, sub_eq_add_neg, C_neg, C_mul]
      ring
    have hnorm :
        P (n + 2) = A + C (-(β (n + 1))) * P n :=
      eq_add_C_mul_of_C_mul_eq_C_mul_add_C_mul (hden n) hcoeff hsplit
    calc
      P (n + 2) = A + C (-(β (n + 1))) * P n := hnorm
      _ =
          -(C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1) -
            C (β (n + 1)) * P n := by
        simp [A, sub_eq_add_neg]
        ring

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
  fun n =>
    (favardInterlacing_affine_param_coeff_rowSign_den_split hs hβ hP0 hP1 hden hraw n).1

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
  fun n =>
    (isRealRooted_of_favard_affine_param_coeff_rowSign_den_split
      hs hβ hP0 hP1 hden hraw n).1

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
  fun n =>
    (favardInterlacing_affine_param_coeff_rowSign_den_split_rev
      hs hβ hP0 hP1 hden hraw n).1

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
  fun n =>
    (isRealRooted_of_favard_affine_param_coeff_rowSign_den_split_rev
      hs hβ hP0 hP1 hden hraw n).1

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
  fun n =>
    (favardInterlacing_affine_param_coeff_rowSign_den_raw
      hs hβ hP0 hP1 hden hs_coeff hα_coeff hβ_coeff hraw n).1

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
  fun n =>
    (isRealRooted_of_favard_affine_param_coeff_rowSign_den_raw
      hs hβ hP0 hP1 hden hs_coeff hα_coeff hβ_coeff hraw n).1

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
  fun n =>
    (favardInterlacing_affine_param_coeff_rowSign_den_raw_prod
      hs hβ hP0 hP1 hden hs_coeff hα_coeff hβ_coeff hraw n).1

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
  fun n =>
    (isRealRooted_of_favard_affine_param_coeff_rowSign_den_raw_prod
      hs hβ hP0 hP1 hden hs_coeff hα_coeff hβ_coeff hraw n).1

namespace Tactic

syntax (name := rr_favard) "rr_favard" " using " term ", " term : tactic

syntax (name := rr_favard_named)
  "rr_favard" " using "
    "recurrence" ":=" term ","
    "beta_pos" ":=" term :
  tactic

syntax (name := rr_favard_auto_named)
  "rr_favard_auto" " using "
    "recurrence" ":=" term :
  tactic

syntax (name := rr_favard_const)
  "rr_favard_const" " using " term ", " term ", " term ", " term ", " term ", " term :
  tactic

syntax (name := rr_favard_const_named)
  "rr_favard_const" " using "
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "beta_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_const_auto_named)
  "rr_favard_const_auto" " using "
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_const_unit_named)
  "rr_favard_const_unit" " using "
    "alpha" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_param)
  "rr_favard_param" " using " term ", " term ", " term ", " term ", " term ", " term :
  tactic

syntax (name := rr_favard_param_named)
  "rr_favard_param" " using "
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "beta_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_param_auto_named)
  "rr_favard_param_auto" " using "
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_param_unit_named)
  "rr_favard_param_unit" " using "
    "alpha" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_affine_const)
  "rr_favard_affine_const" " using " term ", " term ", " term ", " term ", "
    term ", " term ", " term ", " term :
  tactic

syntax (name := rr_favard_affine_const_named)
  "rr_favard_affine_const" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "slope_pos" ":=" term ","
    "beta_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_affine_const_auto_named)
  "rr_favard_affine_const_auto" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_affine_const_unit_named)
  "rr_favard_affine_const_unit" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_affine_const_row_sign_named)
  "rr_favard_affine_const_row_sign" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "slope_pos" ":=" term ","
    "beta_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_affine_const_row_sign_auto_named)
  "rr_favard_affine_const_row_sign_auto" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_const_row_sign_unit_named)
  "rr_favard_const_row_sign_unit" " using "
    "alpha" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_affine_param)
  "rr_favard_affine_param" " using " term ", " term ", " term ", " term ", "
    term ", " term ", " term ", " term :
  tactic

syntax (name := rr_favard_affine_param_named)
  "rr_favard_affine_param" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "slope_pos" ":=" term ","
    "beta_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_affine_param_auto_named)
  "rr_favard_affine_param_auto" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_affine_param_den_named)
  "rr_favard_affine_param_den" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "slope_pos" ":=" term ","
    "beta_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

syntax (name := rr_favard_affine_param_den_auto_named)
  "rr_favard_affine_param_den_auto" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

syntax (name := rr_favard_affine_param_den_raw_named)
  "rr_favard_affine_param_den_raw" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "raw_slope" ":=" term ","
    "raw_const" ":=" term ","
    "raw_lag" ":=" term ","
    "slope_pos" ":=" term ","
    "beta_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "slope_coeff_eq" ":=" term ","
    "alpha_coeff_eq" ":=" term ","
    "beta_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

syntax (name := rr_favard_affine_param_den_raw_auto_named)
  "rr_favard_affine_param_den_raw_auto" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "raw_slope" ":=" term ","
    "raw_const" ":=" term ","
    "raw_lag" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "slope_coeff_eq" ":=" term ","
    "alpha_coeff_eq" ":=" term ","
    "beta_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

syntax (name := rr_favard_affine_param_den_raw_prod_named)
  "rr_favard_affine_param_den_raw_prod" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "raw_slope_left" ":=" term ","
    "raw_slope_right" ":=" term ","
    "raw_const" ":=" term ","
    "raw_lag_left" ":=" term ","
    "raw_lag_right" ":=" term ","
    "slope_pos" ":=" term ","
    "beta_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "slope_coeff_eq" ":=" term ","
    "alpha_coeff_eq" ":=" term ","
    "beta_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

syntax (name := rr_favard_affine_param_den_raw_prod_auto_named)
  "rr_favard_affine_param_den_raw_prod_auto" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "raw_slope_left" ":=" term ","
    "raw_slope_right" ":=" term ","
    "raw_const" ":=" term ","
    "raw_lag_left" ":=" term ","
    "raw_lag_right" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "slope_coeff_eq" ":=" term ","
    "alpha_coeff_eq" ":=" term ","
    "beta_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

syntax (name := rr_favard_affine_param_den_raw_unit_explicit_named)
  "rr_favard_affine_param_den_raw_unit" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "raw_slope" ":=" term ","
    "raw_const" ":=" term ","
    "raw_lag" ":=" term ","
    "slope_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "slope_coeff_eq" ":=" term ","
    "alpha_coeff_eq" ":=" term ","
    "beta_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

syntax (name := rr_favard_affine_param_den_raw_unit_named)
  "rr_favard_affine_param_den_raw_unit" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "raw_slope" ":=" term ","
    "raw_const" ":=" term ","
    "raw_lag" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "slope_coeff_eq" ":=" term ","
    "alpha_coeff_eq" ":=" term ","
    "beta_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

syntax (name := rr_favard_param_den_raw_named)
  "rr_favard_param_den_raw" " using "
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "raw_slope" ":=" term ","
    "raw_const" ":=" term ","
    "raw_lag" ":=" term ","
    "beta_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "slope_coeff_eq" ":=" term ","
    "alpha_coeff_eq" ":=" term ","
    "beta_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

syntax (name := rr_favard_param_den_raw_auto_named)
  "rr_favard_param_den_raw_auto" " using "
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "raw_slope" ":=" term ","
    "raw_const" ":=" term ","
    "raw_lag" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "slope_coeff_eq" ":=" term ","
    "alpha_coeff_eq" ":=" term ","
    "beta_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

syntax (name := rr_favard_param_den_raw_unit_named)
  "rr_favard_param_den_raw_unit" " using "
    "alpha" ":=" term ","
    "raw_slope" ":=" term ","
    "raw_const" ":=" term ","
    "raw_lag" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "slope_coeff_eq" ":=" term ","
    "alpha_coeff_eq" ":=" term ","
    "beta_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

syntax (name := rr_favard_affine_param_den_unit_explicit_named)
  "rr_favard_affine_param_den_unit" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "slope_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

syntax (name := rr_favard_affine_param_den_unit_named)
  "rr_favard_affine_param_den_unit" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

syntax (name := rr_favard_param_den_named)
  "rr_favard_param_den" " using "
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "beta_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

syntax (name := rr_favard_param_den_auto_named)
  "rr_favard_param_den_auto" " using "
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

syntax (name := rr_favard_param_den_unit_named)
  "rr_favard_param_den_unit" " using "
    "alpha" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

syntax (name := rr_favard_affine_param_unit_explicit_named)
  "rr_favard_affine_param_unit" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "slope_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_affine_param_unit_named)
  "rr_favard_affine_param_unit" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_affine_param_row_sign_named)
  "rr_favard_affine_param_row_sign" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "slope_pos" ":=" term ","
    "beta_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_affine_param_row_sign_auto_named)
  "rr_favard_affine_param_row_sign_auto" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_affine_param_row_sign_den_named)
  "rr_favard_affine_param_row_sign_den" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "slope_pos" ":=" term ","
    "beta_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

syntax (name := rr_favard_affine_param_row_sign_den_auto_named)
  "rr_favard_affine_param_row_sign_den_auto" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

syntax (name := rr_favard_affine_param_row_sign_den_raw_named)
  "rr_favard_affine_param_row_sign_den_raw" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "raw_slope" ":=" term ","
    "raw_const" ":=" term ","
    "raw_lag" ":=" term ","
    "slope_pos" ":=" term ","
    "beta_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "slope_coeff_eq" ":=" term ","
    "alpha_coeff_eq" ":=" term ","
    "beta_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

syntax (name := rr_favard_affine_param_row_sign_den_raw_auto_named)
  "rr_favard_affine_param_row_sign_den_raw_auto" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "raw_slope" ":=" term ","
    "raw_const" ":=" term ","
    "raw_lag" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "slope_coeff_eq" ":=" term ","
    "alpha_coeff_eq" ":=" term ","
    "beta_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

syntax (name := rr_favard_affine_param_row_sign_den_raw_prod_named)
  "rr_favard_affine_param_row_sign_den_raw_prod" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "raw_slope_left" ":=" term ","
    "raw_slope_right" ":=" term ","
    "raw_const" ":=" term ","
    "raw_lag_left" ":=" term ","
    "raw_lag_right" ":=" term ","
    "slope_pos" ":=" term ","
    "beta_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "slope_coeff_eq" ":=" term ","
    "alpha_coeff_eq" ":=" term ","
    "beta_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

syntax (name := rr_favard_affine_param_row_sign_den_raw_prod_auto_named)
  "rr_favard_affine_param_row_sign_den_raw_prod_auto" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "raw_slope_left" ":=" term ","
    "raw_slope_right" ":=" term ","
    "raw_const" ":=" term ","
    "raw_lag_left" ":=" term ","
    "raw_lag_right" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "slope_coeff_eq" ":=" term ","
    "alpha_coeff_eq" ":=" term ","
    "beta_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

syntax (name := rr_favard_affine_param_row_sign_den_raw_unit_explicit_named)
  "rr_favard_affine_param_row_sign_den_raw_unit" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "raw_slope" ":=" term ","
    "raw_const" ":=" term ","
    "raw_lag" ":=" term ","
    "slope_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "slope_coeff_eq" ":=" term ","
    "alpha_coeff_eq" ":=" term ","
    "beta_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

syntax (name := rr_favard_affine_param_row_sign_den_raw_unit_named)
  "rr_favard_affine_param_row_sign_den_raw_unit" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "raw_slope" ":=" term ","
    "raw_const" ":=" term ","
    "raw_lag" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "slope_coeff_eq" ":=" term ","
    "alpha_coeff_eq" ":=" term ","
    "beta_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

syntax (name := rr_favard_param_row_sign_den_raw_named)
  "rr_favard_param_row_sign_den_raw" " using "
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "raw_slope" ":=" term ","
    "raw_const" ":=" term ","
    "raw_lag" ":=" term ","
    "beta_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "slope_coeff_eq" ":=" term ","
    "alpha_coeff_eq" ":=" term ","
    "beta_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

syntax (name := rr_favard_param_row_sign_den_raw_auto_named)
  "rr_favard_param_row_sign_den_raw_auto" " using "
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "raw_slope" ":=" term ","
    "raw_const" ":=" term ","
    "raw_lag" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "slope_coeff_eq" ":=" term ","
    "alpha_coeff_eq" ":=" term ","
    "beta_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

syntax (name := rr_favard_param_row_sign_den_raw_unit_named)
  "rr_favard_param_row_sign_den_raw_unit" " using "
    "alpha" ":=" term ","
    "raw_slope" ":=" term ","
    "raw_const" ":=" term ","
    "raw_lag" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "slope_coeff_eq" ":=" term ","
    "alpha_coeff_eq" ":=" term ","
    "beta_coeff_eq" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

syntax (name := rr_favard_affine_param_row_sign_den_unit_explicit_named)
  "rr_favard_affine_param_row_sign_den_unit" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "slope_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

syntax (name := rr_favard_affine_param_row_sign_den_unit_named)
  "rr_favard_affine_param_row_sign_den_unit" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

syntax (name := rr_favard_param_row_sign_den_named)
  "rr_favard_param_row_sign_den" " using "
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "beta_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

syntax (name := rr_favard_param_row_sign_den_auto_named)
  "rr_favard_param_row_sign_den_auto" " using "
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

syntax (name := rr_favard_param_row_sign_den_unit_named)
  "rr_favard_param_row_sign_den_unit" " using "
    "alpha" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
    "den_nonzero" ":=" term ","
    "raw_recurrence" ":=" term :
  tactic

syntax (name := rr_favard_affine_param_row_sign_unit_explicit_named)
  "rr_favard_affine_param_row_sign_unit" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "slope_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_affine_param_row_sign_unit_named)
  "rr_favard_affine_param_row_sign_unit" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_param_row_sign_unit_named)
  "rr_favard_param_row_sign_unit" " using "
    "alpha" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_param_row_sign_named)
  "rr_favard_param_row_sign" " using "
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "beta_pos" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_param_row_sign_auto_named)
  "rr_favard_param_row_sign_auto" " using "
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "step" ":=" term :
  tactic

syntax (name := rr_favard_den_raw) "rr_favard_den_raw" " using " term : tactic

macro_rules
  | `(tactic| rr_favard_den_raw using $hraw:term) =>
      `(tactic|
        first
          | intro n
            simpa [Nat.succ_eq_add_one] using $hraw n
          | intro n
            simpa [Nat.succ_eq_add_one, sub_eq_add_neg, add_comm, add_left_comm,
              add_assoc, C_mul, mul_assoc]
              using $hraw n
          | intro n
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, C_mul,
              mul_assoc] using $hraw n)
  | `(tactic| rr_favard using $hrec:term, $hbeta:term) =>
      `(tactic|
        first
          | exact RealRooted.favardInterlacing $hrec $hbeta
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_favard $hrec $hbeta)
          | exact RealRooted.nonzero_of_favard $hrec $hbeta
          | exact RealRooted.isGeneralizedSturmSeq_reverse_range_map_of_favard
              $hrec $hbeta
          | exact RealRooted.favardInterlacing $hrec $hbeta _
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_favard $hrec $hbeta _)
          | exact RealRooted.nonzero_of_favard $hrec $hbeta _
          | exact RealRooted.isGeneralizedSturmSeq_reverse_range_map_of_favard
              $hrec $hbeta _)
  | `(tactic|
      rr_favard using
        recurrence := $hrec:term,
        beta_pos := $hbeta:term) =>
      `(tactic|
        rr_favard using $hrec, $hbeta)
  | `(tactic|
      rr_favard_auto using
        recurrence := $hrec:term) =>
      `(tactic|
        first
          | refine RealRooted.favardInterlacing $hrec ?_ <;>
              intro n <;>
              positivity
          | rr_exact_realrooted_sequence_or_projection
              (by
                refine RealRooted.isRealRooted_of_favard $hrec ?_ <;>
                intro n <;>
                positivity)
          | refine RealRooted.nonzero_of_favard $hrec ?_ <;>
              intro n <;>
              positivity
          | refine RealRooted.isGeneralizedSturmSeq_reverse_range_map_of_favard
              $hrec ?_ <;>
              intro n <;>
              positivity
          | refine RealRooted.favardInterlacing $hrec ?_ _ <;>
              intro n <;>
              positivity
          | rr_exact_realrooted_sequence_or_projection
              (by
                refine RealRooted.isRealRooted_of_favard $hrec ?_ _ <;>
                intro n <;>
                positivity)
          | refine RealRooted.nonzero_of_favard $hrec ?_ _ <;>
              intro n <;>
              positivity
          | refine RealRooted.isGeneralizedSturmSeq_reverse_range_map_of_favard
              $hrec ?_ _ <;>
              intro n <;>
              positivity)
  | `(tactic|
      rr_favard_const using
        $α:term, $β:term, $hβ:term, $hP0:term, $hP1:term, $hstep:term) =>
      `(tactic|
        first
          | exact RealRooted.favardInterlacing_const_coeff
              (α := $α) (β := $β) $hβ $hP0 $hP1 $hstep
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_favard_const_coeff
                (α := $α) (β := $β) $hβ $hP0 $hP1 $hstep)
          | exact RealRooted.nonzero_of_favard_const_coeff
              (α := $α) (β := $β) $hβ $hP0 $hP1 $hstep
          | exact RealRooted.favardInterlacing_const_coeff
              (α := $α) (β := $β) $hβ $hP0 $hP1 $hstep _
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_favard_const_coeff
                (α := $α) (β := $β) $hβ $hP0 $hP1 $hstep _)
          | exact RealRooted.nonzero_of_favard_const_coeff
              (α := $α) (β := $β) $hβ $hP0 $hP1 $hstep _)
  | `(tactic|
      rr_favard_const using
        alpha := $α:term,
        beta := $β:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_const using $α, $β, $hβ, $hP0, $hP1, $hstep)
  | `(tactic|
      rr_favard_const_auto using
        alpha := $α:term,
        beta := $β:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_const using
          alpha := $α,
          beta := $β,
          beta_pos := by positivity,
          base_zero := $hP0,
          base_one := $hP1,
          step := $hstep)
  | `(tactic|
      rr_favard_const_unit using
        alpha := $α:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_const_auto using
          alpha := $α,
          beta := 1,
          base_zero := $hP0,
          base_one := by simpa using $hP1,
          step := by
            intro n
            simpa using $hstep n)
  | `(tactic|
      rr_favard_param using
        $α:term, $β:term, $hβ:term, $hP0:term, $hP1:term, $hstep:term) =>
      `(tactic|
        first
          | exact RealRooted.favardInterlacing_param_coeff
              (α := $α) (β := $β) $hβ $hP0 $hP1 $hstep
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_favard_param_coeff
                (α := $α) (β := $β) $hβ $hP0 $hP1 $hstep)
          | exact RealRooted.nonzero_of_favard_param_coeff
              (α := $α) (β := $β) $hβ $hP0 $hP1 $hstep
          | exact RealRooted.favardInterlacing_param_coeff
              (α := $α) (β := $β) $hβ $hP0 $hP1 $hstep _
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_favard_param_coeff
                (α := $α) (β := $β) $hβ $hP0 $hP1 $hstep _)
          | exact RealRooted.nonzero_of_favard_param_coeff
              (α := $α) (β := $β) $hβ $hP0 $hP1 $hstep _)
  | `(tactic|
      rr_favard_param using
        alpha := $α:term,
        beta := $β:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_param using $α, $β, $hβ, $hP0, $hP1, $hstep)
  | `(tactic|
      rr_favard_param_auto using
        alpha := $α:term,
        beta := $β:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_param using
          alpha := $α,
          beta := $β,
          beta_pos := by
            intro n
            positivity,
          base_zero := $hP0,
          base_one := $hP1,
          step := $hstep)
  | `(tactic|
      rr_favard_param_unit using
        alpha := $α:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_param_auto using
          alpha := $α,
          beta := fun _ => (1 : ℝ),
          base_zero := $hP0,
          base_one := by
            try dsimp
            simpa using $hP1,
          step := by
            intro n
            try dsimp
            simpa using $hstep n)
  | `(tactic|
      rr_favard_affine_const using
        $s:term, $α:term, $β:term, $hs:term, $hβ:term, $hP0:term, $hP1:term,
        $hstep:term) =>
      `(tactic|
        first
          | exact RealRooted.favardInterlacing_affine_const_coeff
              (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_favard_affine_const_coeff
                (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep)
          | exact RealRooted.nonzero_of_favard_affine_const_coeff
              (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep
          | exact RealRooted.favardInterlacing_affine_const_coeff
              (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep _
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_favard_affine_const_coeff
                (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep _)
          | exact RealRooted.nonzero_of_favard_affine_const_coeff
              (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep _)
  | `(tactic|
      rr_favard_affine_const using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        slope_pos := $hs:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_affine_const using
          $s, $α, $β, $hs, $hβ, $hP0, $hP1, $hstep)
  | `(tactic|
      rr_favard_affine_const_auto using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_affine_const using
          slope := $s,
          alpha := $α,
          beta := $β,
          slope_pos := by positivity,
          beta_pos := by positivity,
          base_zero := $hP0,
          base_one := $hP1,
          step := $hstep)
  | `(tactic|
      rr_favard_affine_const_unit using
        slope := $s:term,
        alpha := $α:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_affine_const_auto using
          slope := $s,
          alpha := $α,
          beta := 1,
          base_zero := $hP0,
          base_one := by simpa using $hP1,
          step := by
            intro n
            simpa using $hstep n)
  | `(tactic|
      rr_favard_affine_const_row_sign using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        slope_pos := $hs:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        first
          | exact RealRooted.favardInterlacing_affine_const_coeff_rowSign
              (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_favard_affine_const_coeff_rowSign
                (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep)
          | exact RealRooted.nonzero_of_favard_affine_const_coeff_rowSign
              (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep
          | exact RealRooted.favardInterlacing_affine_const_coeff_rowSign
              (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep _
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_favard_affine_const_coeff_rowSign
                (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep _)
          | exact RealRooted.nonzero_of_favard_affine_const_coeff_rowSign
              (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep _)
  | `(tactic|
      rr_favard_affine_const_row_sign_auto using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_affine_const_row_sign using
          slope := $s,
          alpha := $α,
          beta := $β,
          slope_pos := by positivity,
          beta_pos := by positivity,
          base_zero := $hP0,
          base_one := $hP1,
          step := $hstep)
  | `(tactic|
      rr_favard_const_row_sign_unit using
        alpha := $α:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_affine_const_row_sign_auto using
          slope := 1,
          alpha := $α,
          beta := 1,
          base_zero := $hP0,
          base_one := by simpa using $hP1,
          step := by
            intro n
            simpa using $hstep n)
  | `(tactic|
      rr_favard_affine_param using
        $s:term, $α:term, $β:term, $hs:term, $hβ:term, $hP0:term, $hP1:term,
        $hstep:term) =>
      `(tactic|
        first
          | exact RealRooted.favardInterlacing_affine_param_coeff
              (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_favard_affine_param_coeff
                (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep)
          | exact RealRooted.nonzero_of_favard_affine_param_coeff
              (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep
          | exact RealRooted.favardInterlacing_affine_param_coeff
              (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep _
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_favard_affine_param_coeff
                (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep _)
          | exact RealRooted.nonzero_of_favard_affine_param_coeff
              (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep _)
  | `(tactic|
      rr_favard_affine_param using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        slope_pos := $hs:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_affine_param using $s, $α, $β, $hs, $hβ, $hP0, $hP1, $hstep)
  | `(tactic|
      rr_favard_affine_param_auto using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_affine_param using
          slope := $s,
          alpha := $α,
          beta := $β,
          slope_pos := by
            intro n
            positivity,
          beta_pos := by
            intro n
            positivity,
          base_zero := $hP0,
          base_one := $hP1,
          step := $hstep)
  | `(tactic|
      rr_favard_affine_param_den using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        slope_pos := $hs:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        first
          | exact
              RealRooted.favardInterlacing_affine_param_coeff_den
                (s := $s) (α := $α) (β := $β) (d := $d)
                $hs $hβ $hP0 $hP1 $hden
                (by
                  intro n
                  first
                    | simpa [Nat.succ_eq_add_one] using $hraw n
                    | simpa [Nat.succ_eq_add_one, sub_eq_add_neg, add_comm,
                        add_left_comm, add_assoc, C_mul, mul_assoc]
                        using $hraw n
                    | simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
                        C_mul, mul_assoc]
                        using $hraw n
                  all_goals done)
          | exact
              RealRooted.favardInterlacing_affine_param_coeff_den_split
                (s := $s) (α := $α) (β := $β) (d := $d)
                $hs $hβ $hP0 $hP1 $hden
                (by
                  intro n
                  first
                    | simpa [Nat.succ_eq_add_one] using $hraw n
                    | simpa [Nat.succ_eq_add_one, sub_eq_add_neg, add_comm,
                        add_left_comm, add_assoc, C_mul, mul_assoc]
                        using $hraw n
                    | simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
                        C_mul, mul_assoc]
                        using $hraw n
                  all_goals done)
          | exact
              RealRooted.favardInterlacing_affine_param_coeff_den_split_rev
                (s := $s) (α := $α) (β := $β) (d := $d)
                $hs $hβ $hP0 $hP1 $hden
                (by rr_favard_den_raw using $hraw)
          | exact
              RealRooted.isRealRooted_of_favard_affine_param_coeff_den
                (s := $s) (α := $α) (β := $β) (d := $d)
                $hs $hβ $hP0 $hP1 $hden
                (by
                  intro n
                  first
                    | simpa [Nat.succ_eq_add_one] using $hraw n
                    | simpa [Nat.succ_eq_add_one, sub_eq_add_neg, add_comm,
                        add_left_comm, add_assoc, C_mul, mul_assoc]
                        using $hraw n
                    | simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
                        C_mul, mul_assoc]
                        using $hraw n
                  all_goals done)
          | exact
              RealRooted.isRealRooted_of_favard_affine_param_coeff_den_split
                (s := $s) (α := $α) (β := $β) (d := $d)
                $hs $hβ $hP0 $hP1 $hden
                (by
                  intro n
                  first
                    | simpa [Nat.succ_eq_add_one] using $hraw n
                    | simpa [Nat.succ_eq_add_one, sub_eq_add_neg, add_comm,
                        add_left_comm, add_assoc, C_mul, mul_assoc]
                        using $hraw n
                    | simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
                        C_mul, mul_assoc]
                        using $hraw n
                  all_goals done)
          | exact
              RealRooted.isRealRooted_of_favard_affine_param_coeff_den_split_rev
                (s := $s) (α := $α) (β := $β) (d := $d)
                $hs $hβ $hP0 $hP1 $hden
                (by rr_favard_den_raw using $hraw)
          | exact
              RealRooted.nonzero_of_favard_affine_param_coeff_den
                (s := $s) (α := $α) (β := $β) (d := $d)
                $hs $hβ $hP0 $hP1 $hden
                (by
                  intro n
                  first
                    | simpa [Nat.succ_eq_add_one] using $hraw n
                    | simpa [Nat.succ_eq_add_one, sub_eq_add_neg, add_comm,
                        add_left_comm, add_assoc, C_mul, mul_assoc]
                        using $hraw n
                    | simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
                        C_mul, mul_assoc]
                        using $hraw n
                  all_goals done)
          | exact
              RealRooted.nonzero_of_favard_affine_param_coeff_den_split
                (s := $s) (α := $α) (β := $β) (d := $d)
                $hs $hβ $hP0 $hP1 $hden
                (by
                  intro n
                  first
                    | simpa [Nat.succ_eq_add_one] using $hraw n
                    | simpa [Nat.succ_eq_add_one, sub_eq_add_neg, add_comm,
                        add_left_comm, add_assoc, C_mul, mul_assoc]
                        using $hraw n
                    | simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
                        C_mul, mul_assoc]
                        using $hraw n
                  all_goals done)
          | exact
              RealRooted.nonzero_of_favard_affine_param_coeff_den_split_rev
                (s := $s) (α := $α) (β := $β) (d := $d)
                $hs $hβ $hP0 $hP1 $hden
                (by rr_favard_den_raw using $hraw)
          | exact
              RealRooted.favardInterlacing_affine_param_coeff_den
                (s := $s) (α := $α) (β := $β) (d := $d)
                $hs $hβ $hP0 $hP1 $hden
                (by
                  intro n
                  first
                    | simpa [Nat.succ_eq_add_one] using $hraw n
                    | simpa [Nat.succ_eq_add_one, sub_eq_add_neg, add_comm,
                        add_left_comm, add_assoc, C_mul, mul_assoc]
                        using $hraw n
                    | simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
                        C_mul, mul_assoc]
                        using $hraw n
                  all_goals done) _
          | exact
              RealRooted.favardInterlacing_affine_param_coeff_den_split
                (s := $s) (α := $α) (β := $β) (d := $d)
                $hs $hβ $hP0 $hP1 $hden
                (by
                  intro n
                  first
                    | simpa [Nat.succ_eq_add_one] using $hraw n
                    | simpa [Nat.succ_eq_add_one, sub_eq_add_neg, add_comm,
                        add_left_comm, add_assoc, C_mul, mul_assoc]
                        using $hraw n
                    | simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
                        C_mul, mul_assoc]
                        using $hraw n
                  all_goals done) _
          | exact
              RealRooted.favardInterlacing_affine_param_coeff_den_split_rev
                (s := $s) (α := $α) (β := $β) (d := $d)
                $hs $hβ $hP0 $hP1 $hden
                (by rr_favard_den_raw using $hraw) _
          | exact
              RealRooted.isRealRooted_of_favard_affine_param_coeff_den
                (s := $s) (α := $α) (β := $β) (d := $d)
                $hs $hβ $hP0 $hP1 $hden
                (by
                  intro n
                  first
                    | simpa [Nat.succ_eq_add_one] using $hraw n
                    | simpa [Nat.succ_eq_add_one, sub_eq_add_neg, add_comm,
                        add_left_comm, add_assoc, C_mul, mul_assoc]
                        using $hraw n
                    | simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
                        C_mul, mul_assoc]
                        using $hraw n
                  all_goals done) _
          | exact
              RealRooted.isRealRooted_of_favard_affine_param_coeff_den_split
                (s := $s) (α := $α) (β := $β) (d := $d)
                $hs $hβ $hP0 $hP1 $hden
                (by
                  intro n
                  first
                    | simpa [Nat.succ_eq_add_one] using $hraw n
                    | simpa [Nat.succ_eq_add_one, sub_eq_add_neg, add_comm,
                        add_left_comm, add_assoc, C_mul, mul_assoc]
                        using $hraw n
                    | simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
                        C_mul, mul_assoc]
                        using $hraw n
                  all_goals done) _
          | exact
              RealRooted.isRealRooted_of_favard_affine_param_coeff_den_split_rev
                (s := $s) (α := $α) (β := $β) (d := $d)
                $hs $hβ $hP0 $hP1 $hden
                (by rr_favard_den_raw using $hraw) _
          | exact
              RealRooted.nonzero_of_favard_affine_param_coeff_den
                (s := $s) (α := $α) (β := $β) (d := $d)
                $hs $hβ $hP0 $hP1 $hden
                (by
                  intro n
                  first
                    | simpa [Nat.succ_eq_add_one] using $hraw n
                    | simpa [Nat.succ_eq_add_one, sub_eq_add_neg, add_comm,
                        add_left_comm, add_assoc, C_mul, mul_assoc]
                        using $hraw n
                    | simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
                        C_mul, mul_assoc]
                        using $hraw n
                  all_goals done) _
          | exact
              RealRooted.nonzero_of_favard_affine_param_coeff_den_split
                (s := $s) (α := $α) (β := $β) (d := $d)
                $hs $hβ $hP0 $hP1 $hden
                (by
                  intro n
                  first
                    | simpa [Nat.succ_eq_add_one] using $hraw n
                    | simpa [Nat.succ_eq_add_one, sub_eq_add_neg, add_comm,
                        add_left_comm, add_assoc, C_mul, mul_assoc]
                        using $hraw n
                    | simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
                        C_mul, mul_assoc]
                        using $hraw n
                  all_goals done) _
          | exact
              RealRooted.nonzero_of_favard_affine_param_coeff_den_split_rev
                (s := $s) (α := $α) (β := $β) (d := $d)
                $hs $hβ $hP0 $hP1 $hden
                (by rr_favard_den_raw using $hraw) _)
  | `(tactic|
      rr_favard_affine_param_den_auto using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_den using
          slope := $s,
          alpha := $α,
          beta := $β,
          slope_pos := by
            intro n
            positivity,
          beta_pos := by
            intro n
            positivity,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := $hden,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_den_raw using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        slope_pos := $hs:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        slope_coeff_eq := $hs_coeff:term,
        alpha_coeff_eq := $hα_coeff:term,
        beta_coeff_eq := $hβ_coeff:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        first
          | exact
              RealRooted.favardInterlacing_affine_param_coeff_den_raw
                (s := $s) (α := $α) (β := $β) (d := $d)
                (araw := $araw) (braw := $braw) (craw := $craw)
                $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw
          | exact
              RealRooted.isRealRooted_of_favard_affine_param_coeff_den_raw
                (s := $s) (α := $α) (β := $β) (d := $d)
                (araw := $araw) (braw := $braw) (craw := $craw)
                $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw
          | exact
              RealRooted.nonzero_of_favard_affine_param_coeff_den_raw
                (s := $s) (α := $α) (β := $β) (d := $d)
                (araw := $araw) (braw := $braw) (craw := $craw)
                $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw
          | exact
              RealRooted.favardInterlacing_affine_param_coeff_den_raw
                (s := $s) (α := $α) (β := $β) (d := $d)
                (araw := $araw) (braw := $braw) (craw := $craw)
                $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw _
          | exact
              RealRooted.isRealRooted_of_favard_affine_param_coeff_den_raw
                (s := $s) (α := $α) (β := $β) (d := $d)
                (araw := $araw) (braw := $braw) (craw := $craw)
                $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw _
          | exact
              RealRooted.nonzero_of_favard_affine_param_coeff_den_raw
                (s := $s) (α := $α) (β := $β) (d := $d)
                (araw := $araw) (braw := $braw) (craw := $craw)
                $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw _)
  | `(tactic|
      rr_favard_affine_param_den_raw_auto using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        slope_coeff_eq := $hs_coeff:term,
        alpha_coeff_eq := $hα_coeff:term,
        beta_coeff_eq := $hβ_coeff:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_den_raw using
          slope := $s,
          alpha := $α,
          beta := $β,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          slope_pos := by
            intro n
            positivity,
          beta_pos := by
            intro n
            positivity,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := $hden,
          slope_coeff_eq := $hs_coeff,
          alpha_coeff_eq := $hα_coeff,
          beta_coeff_eq := $hβ_coeff,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_den_raw_prod using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        raw_slope_left := $aleft:term,
        raw_slope_right := $aright:term,
        raw_const := $braw:term,
        raw_lag_left := $cleft:term,
        raw_lag_right := $cright:term,
        slope_pos := $hs:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        slope_coeff_eq := $hs_coeff:term,
        alpha_coeff_eq := $hα_coeff:term,
        beta_coeff_eq := $hβ_coeff:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        first
          | exact
              RealRooted.favardInterlacing_affine_param_coeff_den_raw_prod
                (s := $s) (α := $α) (β := $β) (d := $d)
                (aleft := $aleft) (aright := $aright) (braw := $braw)
                (cleft := $cleft) (cright := $cright)
                $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw
          | exact
              RealRooted.isRealRooted_of_favard_affine_param_coeff_den_raw_prod
                (s := $s) (α := $α) (β := $β) (d := $d)
                (aleft := $aleft) (aright := $aright) (braw := $braw)
                (cleft := $cleft) (cright := $cright)
                $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw
          | exact
              RealRooted.nonzero_of_favard_affine_param_coeff_den_raw_prod
                (s := $s) (α := $α) (β := $β) (d := $d)
                (aleft := $aleft) (aright := $aright) (braw := $braw)
                (cleft := $cleft) (cright := $cright)
                $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw
          | exact
              RealRooted.favardInterlacing_affine_param_coeff_den_raw_prod
                (s := $s) (α := $α) (β := $β) (d := $d)
                (aleft := $aleft) (aright := $aright) (braw := $braw)
                (cleft := $cleft) (cright := $cright)
                $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw _
          | exact
              RealRooted.isRealRooted_of_favard_affine_param_coeff_den_raw_prod
                (s := $s) (α := $α) (β := $β) (d := $d)
                (aleft := $aleft) (aright := $aright) (braw := $braw)
                (cleft := $cleft) (cright := $cright)
                $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw _
          | exact
              RealRooted.nonzero_of_favard_affine_param_coeff_den_raw_prod
                (s := $s) (α := $α) (β := $β) (d := $d)
                (aleft := $aleft) (aright := $aright) (braw := $braw)
                (cleft := $cleft) (cright := $cright)
                $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw _)
  | `(tactic|
      rr_favard_affine_param_den_raw_prod_auto using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        raw_slope_left := $aleft:term,
        raw_slope_right := $aright:term,
        raw_const := $braw:term,
        raw_lag_left := $cleft:term,
        raw_lag_right := $cright:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        slope_coeff_eq := $hs_coeff:term,
        alpha_coeff_eq := $hα_coeff:term,
        beta_coeff_eq := $hβ_coeff:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_den_raw_prod using
          slope := $s,
          alpha := $α,
          beta := $β,
          raw_slope_left := $aleft,
          raw_slope_right := $aright,
          raw_const := $braw,
          raw_lag_left := $cleft,
          raw_lag_right := $cright,
          slope_pos := by
            intro n
            positivity,
          beta_pos := by
            intro n
            positivity,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := $hden,
          slope_coeff_eq := $hs_coeff,
          alpha_coeff_eq := $hα_coeff,
          beta_coeff_eq := $hβ_coeff,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_den_raw_unit using
        slope := $s:term,
        alpha := $α:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        slope_pos := $hs:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        slope_coeff_eq := $hs_coeff:term,
        alpha_coeff_eq := $hα_coeff:term,
        beta_coeff_eq := $hβ_coeff:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_den_raw using
          slope := $s,
          alpha := $α,
          beta := fun _ => (1 : ℝ),
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          slope_pos := $hs,
          beta_pos := by
            intro n
            positivity,
          base_zero := $hP0,
          base_one := by
            try dsimp
            simpa using $hP1,
          den := $d,
          den_nonzero := $hden,
          slope_coeff_eq := $hs_coeff,
          alpha_coeff_eq := $hα_coeff,
          beta_coeff_eq := $hβ_coeff,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_den_raw_unit using
        slope := $s:term,
        alpha := $α:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        slope_coeff_eq := $hs_coeff:term,
        alpha_coeff_eq := $hα_coeff:term,
        beta_coeff_eq := $hβ_coeff:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_den_raw_auto using
          slope := $s,
          alpha := $α,
          beta := fun _ => (1 : ℝ),
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          base_zero := $hP0,
          base_one := by
            try dsimp
            simpa using $hP1,
          den := $d,
          den_nonzero := $hden,
          slope_coeff_eq := $hs_coeff,
          alpha_coeff_eq := $hα_coeff,
          beta_coeff_eq := $hβ_coeff,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_param_den_raw using
        alpha := $α:term,
        beta := $β:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        slope_coeff_eq := $hs_coeff:term,
        alpha_coeff_eq := $hα_coeff:term,
        beta_coeff_eq := $hβ_coeff:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_den_raw using
          slope := fun _ => (1 : ℝ),
          alpha := $α,
          beta := $β,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          slope_pos := by
            intro n
            positivity,
          beta_pos := $hβ,
          base_zero := $hP0,
          base_one := by
            try dsimp
            simpa using $hP1,
          den := $d,
          den_nonzero := $hden,
          slope_coeff_eq := $hs_coeff,
          alpha_coeff_eq := $hα_coeff,
          beta_coeff_eq := $hβ_coeff,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_param_den_raw_auto using
        alpha := $α:term,
        beta := $β:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        slope_coeff_eq := $hs_coeff:term,
        alpha_coeff_eq := $hα_coeff:term,
        beta_coeff_eq := $hβ_coeff:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_param_den_raw using
          alpha := $α,
          beta := $β,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          beta_pos := by
            intro n
            positivity,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := $hden,
          slope_coeff_eq := $hs_coeff,
          alpha_coeff_eq := $hα_coeff,
          beta_coeff_eq := $hβ_coeff,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_param_den_raw_unit using
        alpha := $α:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        slope_coeff_eq := $hs_coeff:term,
        alpha_coeff_eq := $hα_coeff:term,
        beta_coeff_eq := $hβ_coeff:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_den_raw_unit using
          slope := fun _ => (1 : ℝ),
          alpha := $α,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := $hden,
          slope_coeff_eq := $hs_coeff,
          alpha_coeff_eq := $hα_coeff,
          beta_coeff_eq := $hβ_coeff,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_den_unit using
        slope := $s:term,
        alpha := $α:term,
        slope_pos := $hs:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_den using
          slope := $s,
          alpha := $α,
          beta := fun _ => (1 : ℝ),
          slope_pos := $hs,
          beta_pos := by
            intro n
            positivity,
          base_zero := $hP0,
          base_one := by
            try dsimp
            simpa using $hP1,
          den := $d,
          den_nonzero := $hden,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_den_unit using
        slope := $s:term,
        alpha := $α:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_den_auto using
          slope := $s,
          alpha := $α,
          beta := fun _ => (1 : ℝ),
          base_zero := $hP0,
          base_one := by
            try dsimp
            simpa using $hP1,
          den := $d,
          den_nonzero := $hden,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_param_den using
        alpha := $α:term,
        beta := $β:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_den using
          slope := fun _ => (1 : ℝ),
          alpha := $α,
          beta := $β,
          slope_pos := by
            intro n
            positivity,
          beta_pos := $hβ,
          base_zero := $hP0,
          base_one := by
            try dsimp
            simpa using $hP1,
          den := $d,
          den_nonzero := $hden,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_param_den_auto using
        alpha := $α:term,
        beta := $β:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_param_den using
          alpha := $α,
          beta := $β,
          beta_pos := by
            intro n
            positivity,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := $hden,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_param_den_unit using
        alpha := $α:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_den_unit using
          slope := fun _ => (1 : ℝ),
          alpha := $α,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := $hden,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_unit using
        slope := $s:term,
        alpha := $α:term,
        slope_pos := $hs:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_affine_param using
          slope := $s,
          alpha := $α,
          beta := fun _ => (1 : ℝ),
          slope_pos := $hs,
          beta_pos := by
            intro n
            positivity,
          base_zero := $hP0,
          base_one := by
            try dsimp
            simpa using $hP1,
          step := by
            intro n
            try dsimp
            simpa using $hstep n)
  | `(tactic|
      rr_favard_affine_param_unit using
        slope := $s:term,
        alpha := $α:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_affine_param_auto using
          slope := $s,
          alpha := $α,
          beta := fun _ => (1 : ℝ),
          base_zero := $hP0,
          base_one := by
            try dsimp
            simpa using $hP1,
          step := by
            intro n
            try dsimp
            simpa using $hstep n)
  | `(tactic|
      rr_favard_affine_param_row_sign using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        slope_pos := $hs:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        first
          | exact RealRooted.favardInterlacing_affine_param_coeff_rowSign
              (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_favard_affine_param_coeff_rowSign
                (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep)
          | exact RealRooted.nonzero_of_favard_affine_param_coeff_rowSign
              (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep
          | exact RealRooted.favardInterlacing_affine_param_coeff_rowSign
              (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep _
          | rr_exact_realrooted_sequence_or_projection
              (RealRooted.isRealRooted_of_favard_affine_param_coeff_rowSign
                (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep _)
          | exact RealRooted.nonzero_of_favard_affine_param_coeff_rowSign
              (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep _)
  | `(tactic|
      rr_favard_affine_param_row_sign_auto using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign using
          slope := $s,
          alpha := $α,
          beta := $β,
          slope_pos := by
            intro n
            positivity,
          beta_pos := by
            intro n
            positivity,
          base_zero := $hP0,
          base_one := $hP1,
          step := $hstep)
  | `(tactic|
      rr_favard_affine_param_row_sign_den using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        slope_pos := $hs:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        first
          | exact
              RealRooted.favardInterlacing_affine_param_coeff_rowSign_den
                (s := $s) (α := $α) (β := $β) (d := $d)
                $hs $hβ $hP0 $hP1 $hden
                (by
                  intro n
                  first
                    | simpa [Nat.succ_eq_add_one] using $hraw n
                    | simpa [Nat.succ_eq_add_one, sub_eq_add_neg, add_comm,
                        add_left_comm, add_assoc, C_mul, mul_assoc]
                        using $hraw n
                    | simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
                        C_mul, mul_assoc]
                        using $hraw n
                  all_goals done)
          | exact
              RealRooted.favardInterlacing_affine_param_coeff_rowSign_den_split
                (s := $s) (α := $α) (β := $β) (d := $d)
                $hs $hβ $hP0 $hP1 $hden
                (by
                  intro n
                  first
                    | simpa [Nat.succ_eq_add_one] using $hraw n
                    | simpa [Nat.succ_eq_add_one, sub_eq_add_neg, add_comm,
                        add_left_comm, add_assoc, C_mul, mul_assoc]
                        using $hraw n
                    | simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
                        C_mul, mul_assoc]
                        using $hraw n
                  all_goals done)
          | exact
              RealRooted.favardInterlacing_affine_param_coeff_rowSign_den_split_rev
                (s := $s) (α := $α) (β := $β) (d := $d)
                $hs $hβ $hP0 $hP1 $hden
                (by rr_favard_den_raw using $hraw)
          | exact
              RealRooted.isRealRooted_of_favard_affine_param_coeff_rowSign_den
                (s := $s) (α := $α) (β := $β) (d := $d)
                $hs $hβ $hP0 $hP1 $hden
                (by
                  intro n
                  first
                    | simpa [Nat.succ_eq_add_one] using $hraw n
                    | simpa [Nat.succ_eq_add_one, sub_eq_add_neg, add_comm,
                        add_left_comm, add_assoc, C_mul, mul_assoc]
                        using $hraw n
                    | simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
                        C_mul, mul_assoc]
                        using $hraw n
                  all_goals done)
          | exact
              RealRooted.isRealRooted_of_favard_affine_param_coeff_rowSign_den_split
                (s := $s) (α := $α) (β := $β) (d := $d)
                $hs $hβ $hP0 $hP1 $hden
                (by
                  intro n
                  first
                    | simpa [Nat.succ_eq_add_one] using $hraw n
                    | simpa [Nat.succ_eq_add_one, sub_eq_add_neg, add_comm,
                        add_left_comm, add_assoc, C_mul, mul_assoc]
                        using $hraw n
                    | simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
                        C_mul, mul_assoc]
                        using $hraw n
                  all_goals done)
          | exact
              RealRooted.isRealRooted_of_favard_affine_param_coeff_rowSign_den_split_rev
                (s := $s) (α := $α) (β := $β) (d := $d)
                $hs $hβ $hP0 $hP1 $hden
                (by rr_favard_den_raw using $hraw)
          | exact
              RealRooted.nonzero_of_favard_affine_param_coeff_rowSign_den
                (s := $s) (α := $α) (β := $β) (d := $d)
                $hs $hβ $hP0 $hP1 $hden
                (by
                  intro n
                  first
                    | simpa [Nat.succ_eq_add_one] using $hraw n
                    | simpa [Nat.succ_eq_add_one, sub_eq_add_neg, add_comm,
                        add_left_comm, add_assoc, C_mul, mul_assoc]
                        using $hraw n
                    | simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
                        C_mul, mul_assoc]
                        using $hraw n
                  all_goals done)
          | exact
              RealRooted.nonzero_of_favard_affine_param_coeff_rowSign_den_split
                (s := $s) (α := $α) (β := $β) (d := $d)
                $hs $hβ $hP0 $hP1 $hden
                (by
                  intro n
                  first
                    | simpa [Nat.succ_eq_add_one] using $hraw n
                    | simpa [Nat.succ_eq_add_one, sub_eq_add_neg, add_comm,
                        add_left_comm, add_assoc, C_mul, mul_assoc]
                        using $hraw n
                    | simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
                        C_mul, mul_assoc]
                        using $hraw n
                  all_goals done)
          | exact
              RealRooted.nonzero_of_favard_affine_param_coeff_rowSign_den_split_rev
                (s := $s) (α := $α) (β := $β) (d := $d)
                $hs $hβ $hP0 $hP1 $hden
                (by rr_favard_den_raw using $hraw)
          | exact
              RealRooted.favardInterlacing_affine_param_coeff_rowSign_den
                (s := $s) (α := $α) (β := $β) (d := $d)
                $hs $hβ $hP0 $hP1 $hden
                (by
                  intro n
                  first
                    | simpa [Nat.succ_eq_add_one] using $hraw n
                    | simpa [Nat.succ_eq_add_one, sub_eq_add_neg, add_comm,
                        add_left_comm, add_assoc, C_mul, mul_assoc]
                        using $hraw n
                    | simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
                        C_mul, mul_assoc]
                        using $hraw n
                  all_goals done) _
          | exact
              RealRooted.favardInterlacing_affine_param_coeff_rowSign_den_split
                (s := $s) (α := $α) (β := $β) (d := $d)
                $hs $hβ $hP0 $hP1 $hden
                (by
                  intro n
                  first
                    | simpa [Nat.succ_eq_add_one] using $hraw n
                    | simpa [Nat.succ_eq_add_one, sub_eq_add_neg, add_comm,
                        add_left_comm, add_assoc, C_mul, mul_assoc]
                        using $hraw n
                    | simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
                        C_mul, mul_assoc]
                        using $hraw n
                  all_goals done) _
          | exact
              RealRooted.favardInterlacing_affine_param_coeff_rowSign_den_split_rev
                (s := $s) (α := $α) (β := $β) (d := $d)
                $hs $hβ $hP0 $hP1 $hden
                (by rr_favard_den_raw using $hraw) _
          | exact
              RealRooted.isRealRooted_of_favard_affine_param_coeff_rowSign_den
                (s := $s) (α := $α) (β := $β) (d := $d)
                $hs $hβ $hP0 $hP1 $hden
                (by
                  intro n
                  first
                    | simpa [Nat.succ_eq_add_one] using $hraw n
                    | simpa [Nat.succ_eq_add_one, sub_eq_add_neg, add_comm,
                        add_left_comm, add_assoc, C_mul, mul_assoc]
                        using $hraw n
                    | simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
                        C_mul, mul_assoc]
                        using $hraw n
                  all_goals done) _
          | exact
              RealRooted.isRealRooted_of_favard_affine_param_coeff_rowSign_den_split
                (s := $s) (α := $α) (β := $β) (d := $d)
                $hs $hβ $hP0 $hP1 $hden
                (by
                  intro n
                  first
                    | simpa [Nat.succ_eq_add_one] using $hraw n
                    | simpa [Nat.succ_eq_add_one, sub_eq_add_neg, add_comm,
                        add_left_comm, add_assoc, C_mul, mul_assoc]
                        using $hraw n
                    | simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
                        C_mul, mul_assoc]
                        using $hraw n
                  all_goals done) _
          | exact
              RealRooted.isRealRooted_of_favard_affine_param_coeff_rowSign_den_split_rev
                (s := $s) (α := $α) (β := $β) (d := $d)
                $hs $hβ $hP0 $hP1 $hden
                (by rr_favard_den_raw using $hraw) _
          | exact
              RealRooted.nonzero_of_favard_affine_param_coeff_rowSign_den
                (s := $s) (α := $α) (β := $β) (d := $d)
                $hs $hβ $hP0 $hP1 $hden
                (by
                  intro n
                  first
                    | simpa [Nat.succ_eq_add_one] using $hraw n
                    | simpa [Nat.succ_eq_add_one, sub_eq_add_neg, add_comm,
                        add_left_comm, add_assoc, C_mul, mul_assoc]
                        using $hraw n
                    | simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
                        C_mul, mul_assoc]
                        using $hraw n
                  all_goals done) _
          | exact
              RealRooted.nonzero_of_favard_affine_param_coeff_rowSign_den_split
                (s := $s) (α := $α) (β := $β) (d := $d)
                $hs $hβ $hP0 $hP1 $hden
                (by
                  intro n
                  first
                    | simpa [Nat.succ_eq_add_one] using $hraw n
                    | simpa [Nat.succ_eq_add_one, sub_eq_add_neg, add_comm,
                        add_left_comm, add_assoc, C_mul, mul_assoc]
                        using $hraw n
                    | simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
                        C_mul, mul_assoc]
                        using $hraw n
                  all_goals done) _
          | exact
              RealRooted.nonzero_of_favard_affine_param_coeff_rowSign_den_split_rev
                (s := $s) (α := $α) (β := $β) (d := $d)
                $hs $hβ $hP0 $hP1 $hden
                (by rr_favard_den_raw using $hraw) _)
  | `(tactic|
      rr_favard_affine_param_row_sign_den_auto using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den using
          slope := $s,
          alpha := $α,
          beta := $β,
          slope_pos := by
            intro n
            positivity,
          beta_pos := by
            intro n
            positivity,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := $hden,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_row_sign_den_raw using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        slope_pos := $hs:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        slope_coeff_eq := $hs_coeff:term,
        alpha_coeff_eq := $hα_coeff:term,
        beta_coeff_eq := $hβ_coeff:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        first
          | exact
              RealRooted.favardInterlacing_affine_param_coeff_rowSign_den_raw
                (s := $s) (α := $α) (β := $β) (d := $d)
                (araw := $araw) (braw := $braw) (craw := $craw)
                $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw
          | exact
              RealRooted.isRealRooted_of_favard_affine_param_coeff_rowSign_den_raw
                (s := $s) (α := $α) (β := $β) (d := $d)
                (araw := $araw) (braw := $braw) (craw := $craw)
                $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw
          | exact
              RealRooted.nonzero_of_favard_affine_param_coeff_rowSign_den_raw
                (s := $s) (α := $α) (β := $β) (d := $d)
                (araw := $araw) (braw := $braw) (craw := $craw)
                $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw
          | exact
              RealRooted.favardInterlacing_affine_param_coeff_rowSign_den_raw
                (s := $s) (α := $α) (β := $β) (d := $d)
                (araw := $araw) (braw := $braw) (craw := $craw)
                $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw _
          | exact
              RealRooted.isRealRooted_of_favard_affine_param_coeff_rowSign_den_raw
                (s := $s) (α := $α) (β := $β) (d := $d)
                (araw := $araw) (braw := $braw) (craw := $craw)
                $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw _
          | exact
              RealRooted.nonzero_of_favard_affine_param_coeff_rowSign_den_raw
                (s := $s) (α := $α) (β := $β) (d := $d)
                (araw := $araw) (braw := $braw) (craw := $craw)
                $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw _)
  | `(tactic|
      rr_favard_affine_param_row_sign_den_raw_auto using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        slope_coeff_eq := $hs_coeff:term,
        alpha_coeff_eq := $hα_coeff:term,
        beta_coeff_eq := $hβ_coeff:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den_raw using
          slope := $s,
          alpha := $α,
          beta := $β,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          slope_pos := by
            intro n
            positivity,
          beta_pos := by
            intro n
            positivity,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := $hden,
          slope_coeff_eq := $hs_coeff,
          alpha_coeff_eq := $hα_coeff,
          beta_coeff_eq := $hβ_coeff,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_row_sign_den_raw_prod using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        raw_slope_left := $aleft:term,
        raw_slope_right := $aright:term,
        raw_const := $braw:term,
        raw_lag_left := $cleft:term,
        raw_lag_right := $cright:term,
        slope_pos := $hs:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        slope_coeff_eq := $hs_coeff:term,
        alpha_coeff_eq := $hα_coeff:term,
        beta_coeff_eq := $hβ_coeff:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        first
          | exact
              RealRooted.favardInterlacing_affine_param_coeff_rowSign_den_raw_prod
                (s := $s) (α := $α) (β := $β) (d := $d)
                (aleft := $aleft) (aright := $aright) (braw := $braw)
                (cleft := $cleft) (cright := $cright)
                $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw
          | exact
              RealRooted.isRealRooted_of_favard_affine_param_coeff_rowSign_den_raw_prod
                (s := $s) (α := $α) (β := $β) (d := $d)
                (aleft := $aleft) (aright := $aright) (braw := $braw)
                (cleft := $cleft) (cright := $cright)
                $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw
          | exact
              RealRooted.nonzero_of_favard_affine_param_coeff_rowSign_den_raw_prod
                (s := $s) (α := $α) (β := $β) (d := $d)
                (aleft := $aleft) (aright := $aright) (braw := $braw)
                (cleft := $cleft) (cright := $cright)
                $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw
          | exact
              RealRooted.favardInterlacing_affine_param_coeff_rowSign_den_raw_prod
                (s := $s) (α := $α) (β := $β) (d := $d)
                (aleft := $aleft) (aright := $aright) (braw := $braw)
                (cleft := $cleft) (cright := $cright)
                $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw _
          | exact
              RealRooted.isRealRooted_of_favard_affine_param_coeff_rowSign_den_raw_prod
                (s := $s) (α := $α) (β := $β) (d := $d)
                (aleft := $aleft) (aright := $aright) (braw := $braw)
                (cleft := $cleft) (cright := $cright)
                $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw _
          | exact
              RealRooted.nonzero_of_favard_affine_param_coeff_rowSign_den_raw_prod
                (s := $s) (α := $α) (β := $β) (d := $d)
                (aleft := $aleft) (aright := $aright) (braw := $braw)
                (cleft := $cleft) (cright := $cright)
                $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw _)
  | `(tactic|
      rr_favard_affine_param_row_sign_den_raw_prod_auto using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        raw_slope_left := $aleft:term,
        raw_slope_right := $aright:term,
        raw_const := $braw:term,
        raw_lag_left := $cleft:term,
        raw_lag_right := $cright:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        slope_coeff_eq := $hs_coeff:term,
        alpha_coeff_eq := $hα_coeff:term,
        beta_coeff_eq := $hβ_coeff:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den_raw_prod using
          slope := $s,
          alpha := $α,
          beta := $β,
          raw_slope_left := $aleft,
          raw_slope_right := $aright,
          raw_const := $braw,
          raw_lag_left := $cleft,
          raw_lag_right := $cright,
          slope_pos := by
            intro n
            positivity,
          beta_pos := by
            intro n
            positivity,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := $hden,
          slope_coeff_eq := $hs_coeff,
          alpha_coeff_eq := $hα_coeff,
          beta_coeff_eq := $hβ_coeff,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_row_sign_den_raw_unit using
        slope := $s:term,
        alpha := $α:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        slope_pos := $hs:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        slope_coeff_eq := $hs_coeff:term,
        alpha_coeff_eq := $hα_coeff:term,
        beta_coeff_eq := $hβ_coeff:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den_raw using
          slope := $s,
          alpha := $α,
          beta := fun _ => (1 : ℝ),
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          slope_pos := $hs,
          beta_pos := by
            intro n
            positivity,
          base_zero := $hP0,
          base_one := by
            try dsimp
            simpa using $hP1,
          den := $d,
          den_nonzero := $hden,
          slope_coeff_eq := $hs_coeff,
          alpha_coeff_eq := $hα_coeff,
          beta_coeff_eq := $hβ_coeff,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_row_sign_den_raw_unit using
        slope := $s:term,
        alpha := $α:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        slope_coeff_eq := $hs_coeff:term,
        alpha_coeff_eq := $hα_coeff:term,
        beta_coeff_eq := $hβ_coeff:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den_raw_auto using
          slope := $s,
          alpha := $α,
          beta := fun _ => (1 : ℝ),
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          base_zero := $hP0,
          base_one := by
            try dsimp
            simpa using $hP1,
          den := $d,
          den_nonzero := $hden,
          slope_coeff_eq := $hs_coeff,
          alpha_coeff_eq := $hα_coeff,
          beta_coeff_eq := $hβ_coeff,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_param_row_sign_den_raw using
        alpha := $α:term,
        beta := $β:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        slope_coeff_eq := $hs_coeff:term,
        alpha_coeff_eq := $hα_coeff:term,
        beta_coeff_eq := $hβ_coeff:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den_raw using
          slope := fun _ => (1 : ℝ),
          alpha := $α,
          beta := $β,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          slope_pos := by
            intro n
            positivity,
          beta_pos := $hβ,
          base_zero := $hP0,
          base_one := by
            try dsimp
            simpa using $hP1,
          den := $d,
          den_nonzero := $hden,
          slope_coeff_eq := $hs_coeff,
          alpha_coeff_eq := $hα_coeff,
          beta_coeff_eq := $hβ_coeff,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_param_row_sign_den_raw_auto using
        alpha := $α:term,
        beta := $β:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        slope_coeff_eq := $hs_coeff:term,
        alpha_coeff_eq := $hα_coeff:term,
        beta_coeff_eq := $hβ_coeff:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_param_row_sign_den_raw using
          alpha := $α,
          beta := $β,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          beta_pos := by
            intro n
            positivity,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := $hden,
          slope_coeff_eq := $hs_coeff,
          alpha_coeff_eq := $hα_coeff,
          beta_coeff_eq := $hβ_coeff,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_param_row_sign_den_raw_unit using
        alpha := $α:term,
        raw_slope := $araw:term,
        raw_const := $braw:term,
        raw_lag := $craw:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        slope_coeff_eq := $hs_coeff:term,
        alpha_coeff_eq := $hα_coeff:term,
        beta_coeff_eq := $hβ_coeff:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den_raw_unit using
          slope := fun _ => (1 : ℝ),
          alpha := $α,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := $hden,
          slope_coeff_eq := $hs_coeff,
          alpha_coeff_eq := $hα_coeff,
          beta_coeff_eq := $hβ_coeff,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_row_sign_den_unit using
        slope := $s:term,
        alpha := $α:term,
        slope_pos := $hs:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den using
          slope := $s,
          alpha := $α,
          beta := fun _ => (1 : ℝ),
          slope_pos := $hs,
          beta_pos := by
            intro n
            positivity,
          base_zero := $hP0,
          base_one := by
            try dsimp
            simpa using $hP1,
          den := $d,
          den_nonzero := $hden,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_row_sign_den_unit using
        slope := $s:term,
        alpha := $α:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den_auto using
          slope := $s,
          alpha := $α,
          beta := fun _ => (1 : ℝ),
          base_zero := $hP0,
          base_one := by
            try dsimp
            simpa using $hP1,
          den := $d,
          den_nonzero := $hden,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_param_row_sign_den using
        alpha := $α:term,
        beta := $β:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den using
          slope := fun _ => (1 : ℝ),
          alpha := $α,
          beta := $β,
          slope_pos := by
            intro n
            positivity,
          beta_pos := $hβ,
          base_zero := $hP0,
          base_one := by
            try dsimp
            simpa using $hP1,
          den := $d,
          den_nonzero := $hden,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_param_row_sign_den_auto using
        alpha := $α:term,
        beta := $β:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_param_row_sign_den using
          alpha := $α,
          beta := $β,
          beta_pos := by
            intro n
            positivity,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := $hden,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_param_row_sign_den_unit using
        alpha := $α:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        den_nonzero := $hden:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den_unit using
          slope := fun _ => (1 : ℝ),
          alpha := $α,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := $hden,
          raw_recurrence := $hraw)
  | `(tactic|
      rr_favard_affine_param_row_sign_unit using
        slope := $s:term,
        alpha := $α:term,
        slope_pos := $hs:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign using
          slope := $s,
          alpha := $α,
          beta := fun _ => (1 : ℝ),
          slope_pos := $hs,
          beta_pos := by
            intro n
            positivity,
          base_zero := $hP0,
          base_one := by
            try dsimp
            simpa using $hP1,
          step := by
            intro n
            try dsimp
            simpa using $hstep n)
  | `(tactic|
      rr_favard_affine_param_row_sign_unit using
        slope := $s:term,
        alpha := $α:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_auto using
          slope := $s,
          alpha := $α,
          beta := fun _ => (1 : ℝ),
          base_zero := $hP0,
          base_one := by
            try dsimp
            simpa using $hP1,
          step := by
            intro n
            try dsimp
            simpa using $hstep n)
  | `(tactic|
      rr_favard_param_row_sign_unit using
        alpha := $α:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_unit using
          slope := fun _ => (1 : ℝ),
          alpha := $α,
          base_zero := $hP0,
          base_one := $hP1,
          step := $hstep)
  | `(tactic|
      rr_favard_param_row_sign using
        alpha := $α:term,
        beta := $β:term,
        beta_pos := $hβ:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign using
          slope := fun _ => (1 : ℝ),
          alpha := $α,
          beta := $β,
          slope_pos := by
            intro n
            positivity,
          beta_pos := $hβ,
          base_zero := $hP0,
          base_one := by
            try dsimp
            simpa using $hP1,
          step := by
            intro n
            try dsimp
            simpa using $hstep n)
  | `(tactic|
      rr_favard_param_row_sign_auto using
        alpha := $α:term,
        beta := $β:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        step := $hstep:term) =>
      `(tactic|
        rr_favard_param_row_sign using
          alpha := $α,
          beta := $β,
          beta_pos := by
            intro n
            positivity,
          base_zero := $hP0,
          base_one := $hP1,
          step := $hstep)

end Tactic
end RealRooted
