import RealRooted.Favard
import RealRooted.Tactic.Finish
import RealRooted.Tactic.ScalarDen
import RealRooted.Tactic.SideGoals

open Polynomial

/-!
# Favard tactic

The tactic

```lean
rr_favard
rr_favard using hrec, hbeta
rr_favard_auto
```

applies the already-formalized Favard interface to goals that match
`favardInterlacing`,
`isRealRooted_of_favard`, or
`isGeneralizedSturmSeq_reverse_range_map_of_favard`.
The bare forms infer exact local recurrence and positivity hypotheses. Use an
explicit `using` form when more than one Favard certificate packet is in scope.
`rr_favard_affine_param_infer` keeps the coefficient families and recurrence
explicit while inferring positivity, base certificates, and the standard or
row-sign orientation.

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
  rr_pos_lc

private theorem prec_affine_favard_step {f g aPoly bPoly : ℝ[X]}
    (hInter : Interlaces g f)
    (hg_pos : HasPosLeadingCoeff g)
    (hf_pos : HasPosLeadingCoeff f)
    (hA_deg : aPoly.natDegree = 1)
    (hA_pos : HasPosLeadingCoeff aPoly)
    (hA_ne : aPoly ≠ 0)
    (hBg_le : (bPoly * g).natDegree ≤ g.natDegree)
    (hb_nonpos : ∀ r, f.IsRoot r → bPoly.eval r ≤ 0) :
    Prec f (aPoly * f + bPoly * g) ∧
      Interlaces f (aPoly * f + bPoly * g) ∧
      HasPosLeadingCoeff (aPoly * f + bPoly * g) := by
  have hdeg_gf : g.natDegree + 1 = f.natDegree := by
    simpa using natDegree_succ_of_interlaces hInter
  have hf_ne : f ≠ 0 := by
    simpa using right_ne_zero_of_interlaces hInter
  have hAf_deg : (aPoly * f).natDegree = f.natDegree + 1 := by
    rw [natDegree_mul hA_ne hf_ne, hA_deg]
    lia
  have hAf_pos : HasPosLeadingCoeff (aPoly * f) := by
    rr_pos_lc
  have hBg_lt_Af : (bPoly * g).natDegree < (aPoly * f).natDegree := by
    lia
  have hF_pos : HasPosLeadingCoeff (aPoly * f + bPoly * g) := by
    simpa [add_comm] using
      hasPosLeadingCoeff_add_of_natDegree_lt_right hBg_lt_Af hAf_pos
  have hF_deg : (aPoly * f + bPoly * g).natDegree = f.natDegree + 1 := by
    simpa [add_comm, hAf_deg] using
      natDegree_add_eq_right_of_natDegree_lt_of_posLeadingCoeff hBg_lt_Af hAf_pos
  have hPrec_step : Prec f (aPoly * f + bPoly * g) :=
    prec_of_interlaces_evalCoeff_nonpos
      (f := f) (g := g) (a := aPoly) (b := bPoly)
      hInter hg_pos hF_pos (by lia) (by lia) hb_nonpos
  exact ⟨hPrec_step, hPrec_step.toInterlaces (by lia), hF_pos⟩

private def affineFavardChainPackage (P : Nat → ℝ[X]) (n : Nat) : Prop :=
  Interlaces (P n) (P (n + 1)) ∧
    HasPosLeadingCoeff (P n) ∧
    HasPosLeadingCoeff (P (n + 1))

private theorem prec_sequence_of_affineFavardChainPackage {P : Nat → ℝ[X]}
    (hQ : ∀ n : Nat, affineFavardChainPackage P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  fun n => (hQ n).1.toPrec

private theorem affineFavardChainPackage_of_param_coeff
    {P : Nat → ℝ[X]} {s α β : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (s 0) * X - C (α 0))
    (hstep : ∀ n : Nat,
      P (n + 2) =
        (C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1) -
          C (β (n + 1)) * P n) :
    ∀ n : Nat, affineFavardChainPackage P n := by
  refine sequence_of_base_and_step ?_ ?_
  · let aPoly : ℝ[X] := C (s 0) * X - C (α 0)
    have hA_deg : aPoly.natDegree = 1 := by
      simpa [aPoly] using natDegree_C_mul_X_sub_C
        (s := s 0) (t := α 0) (hs 0).ne'
    have hA_pos : HasPosLeadingCoeff aPoly := by
      simpa [aPoly] using hasPosLeadingCoeff_C_mul_X_sub_C
        (s := s 0) (t := α 0) (hs 0)
    refine ⟨?_, ?_, ?_⟩
    · rw [hP0, hP1]
      exact interlaces_one_linear (by simpa [aPoly] using hA_deg)
    · rw [hP0]
      rr_pos_lc
    · rw [hP1]
      simpa [aPoly] using hA_pos
  · intro n hP
    rcases hP with ⟨hInter, hPos_n, hPos_n1⟩
    let f : ℝ[X] := P (n + 1)
    let g : ℝ[X] := P n
    let aPoly : ℝ[X] := C (s (n + 1)) * X - C (α (n + 1))
    let bPoly : ℝ[X] := C (-β (n + 1))
    have hA_deg : aPoly.natDegree = 1 := by
      simpa [aPoly] using natDegree_C_mul_X_sub_C
        (s := s (n + 1)) (t := α (n + 1)) (hs (n + 1)).ne'
    have hA_pos : HasPosLeadingCoeff aPoly := by
      simpa [aPoly] using hasPosLeadingCoeff_C_mul_X_sub_C
        (s := s (n + 1)) (t := α (n + 1)) (hs (n + 1))
    have hA_ne : aPoly ≠ 0 := by
      rr_nonzero
    have hBg_le : (bPoly * g).natDegree ≤ g.natDegree := by
      dsimp [bPoly]
      exact Polynomial.natDegree_C_mul_le _ _
    have hb_nonpos : ∀ r, f.IsRoot r → bPoly.eval r ≤ 0 := by
      intros
      have hb_le : 0 ≤ β (n + 1) := (hβ n).le
      simpa [bPoly] using (neg_nonpos.mpr hb_le)
    have hFavardStep :=
      prec_affine_favard_step hInter hPos_n hPos_n1 hA_deg hA_pos hA_ne
        hBg_le hb_nonpos
    have hInter_step : Interlaces f (aPoly * f + bPoly * g) := hFavardStep.2.1
    have hF_pos : HasPosLeadingCoeff (aPoly * f + bPoly * g) := hFavardStep.2.2
    dsimp [affineFavardChainPackage]
    grind

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

private theorem eq_sub_C_mul_of_C_mul_eq_C_mul_sub_C_mul {d b : ℝ} (hd : d ≠ 0)
    {F A Q : ℝ[X]} (h : C d * F = C d * A - C (d * b) * Q) :
    F = A - C b * Q :=
  eq_of_C_mul_eq_C_mul hd <| by rw [h, C_mul]; ring

private theorem satisfiesFavardRecurrence_const_coeff {P : Nat → ℝ[X]} {α β : ℝ}
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X - C α)
    (hstep : ∀ n : Nat, P (n + 2) = (X - C α) * P (n + 1) - C β * P n) :
    SatisfiesFavardRecurrence P (fun _ => α) (fun _ => β) :=
  ⟨hP0, hP1, fun n => by simpa using hstep n⟩

/-- Constant-coefficient Favard wrapper.  This packages the recurring
Chebyshev-style shape
`P_{n+2} = (X - α) P_{n+1} - β P_n`, with `β > 0`. -/
theorem favardInterlacing_const_coeff {P : Nat → ℝ[X]} {α β : ℝ}
    (hβ : 0 < β)
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X - C α)
    (hstep : ∀ n : Nat, P (n + 2) = (X - C α) * P (n + 1) - C β * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  favardInterlacing
    (P := P) (α := fun _ => α) (β := fun _ => β)
    (satisfiesFavardRecurrence_const_coeff hP0 hP1 hstep)
    (fun _ => hβ)

/-- Real-rootedness consequence of the constant-coefficient Favard wrapper. -/
theorem isRealRooted_of_favard_const_coeff {P : Nat → ℝ[X]} {α β : ℝ}
    (hβ : 0 < β)
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X - C α)
    (hstep : ∀ n : Nat, P (n + 2) = (X - C α) * P (n + 1) - C β * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_favard
    (P := P) (α := fun _ => α) (β := fun _ => β)
    (satisfiesFavardRecurrence_const_coeff hP0 hP1 hstep)
    (fun _ => hβ)

/-- Nonzero consequence of the constant-coefficient Favard wrapper. -/
theorem nonzero_of_favard_const_coeff {P : Nat → ℝ[X]} {α β : ℝ}
    (hβ : 0 < β)
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X - C α)
    (hstep : ∀ n : Nat, P (n + 2) = (X - C α) * P (n + 1) - C β * P n) :
    ∀ n : Nat, P n ≠ 0 :=
  ne_zero_of_isRealRooted_sequence <|
    isRealRooted_of_favard_const_coeff hβ hP0 hP1 hstep

/-- Parameterized Favard wrapper.  This packages the monic shape
`P_{n+2} = (X - α_{n+1}) P_{n+1} - β_{n+1} P_n`, with `β_{n+1} > 0`. -/
theorem favardInterlacing_param_coeff {P : Nat → ℝ[X]} {α β : Nat → ℝ}
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X - C (α 0))
    (hstep : ∀ n : Nat,
      P (n + 2) = (X - C (α (n + 1))) * P (n + 1) - C (β (n + 1)) * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  favardInterlacing ⟨hP0, hP1, hstep⟩ hβ

/-- Real-rootedness consequence of the parameterized Favard wrapper. -/
theorem isRealRooted_of_favard_param_coeff {P : Nat → ℝ[X]} {α β : Nat → ℝ}
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X - C (α 0))
    (hstep : ∀ n : Nat,
      P (n + 2) = (X - C (α (n + 1))) * P (n + 1) - C (β (n + 1)) * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_favard ⟨hP0, hP1, hstep⟩ hβ

/-- Nonzero consequence of the parameterized Favard wrapper. -/
theorem nonzero_of_favard_param_coeff {P : Nat → ℝ[X]} {α β : Nat → ℝ}
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = X - C (α 0))
    (hstep : ∀ n : Nat,
      P (n + 2) = (X - C (α (n + 1))) * P (n + 1) - C (β (n + 1)) * P n) :
    ∀ n : Nat, P n ≠ 0 :=
  ne_zero_of_isRealRooted_sequence <|
    isRealRooted_of_favard_param_coeff hβ hP0 hP1 hstep

/-- Positive-slope affine Favard wrapper.  This packages the recurring
nonmonic Chebyshev-style shape
`P_{n+2} = (sX - α) P_{n+1} - β P_n`, with `s > 0` and `β > 0`. -/
theorem favardInterlacing_affine_const_coeff {P : Nat → ℝ[X]} {s α β : ℝ}
    (hs : 0 < s)
    (hβ : 0 < β)
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C s * X - C α)
    (hstep : ∀ n : Nat, P (n + 2) = (C s * X - C α) * P (n + 1) - C β * P n) :
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  prec_sequence_of_affineFavardChainPackage <|
    affineFavardChainPackage_of_param_coeff
      (P := P) (s := fun _ => s) (α := fun _ => α) (β := fun _ => β)
      (fun _ => hs) (fun _ => hβ) hP0 (by simpa using hP1)
      (fun n => by simpa using hstep n)

/-- Real-rootedness consequence of the positive-slope affine Favard wrapper. -/
theorem isRealRooted_of_favard_affine_const_coeff {P : Nat → ℝ[X]} {s α β : ℝ}
    (hs : 0 < s)
    (hβ : 0 < β)
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C s * X - C α)
    (hstep : ∀ n : Nat, P (n + 2) = (C s * X - C α) * P (n + 1) - C β * P n) :
    ∀ n : Nat, P n ≠ 0 ∧ (P n).Splits :=
  isRealRooted_of_prec_chain_from_step <|
    favardInterlacing_affine_const_coeff hs hβ hP0 hP1 hstep

/-- Nonzero consequence of the positive-slope affine Favard wrapper. -/
theorem nonzero_of_favard_affine_const_coeff {P : Nat → ℝ[X]} {s α β : ℝ}
    (hs : 0 < s)
    (hβ : 0 < β)
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C s * X - C α)
    (hstep : ∀ n : Nat, P (n + 2) = (C s * X - C α) * P (n + 1) - C β * P n) :
    ∀ n : Nat, P n ≠ 0 :=
  ne_zero_of_isRealRooted_sequence <|
    isRealRooted_of_favard_affine_const_coeff hs hβ hP0 hP1 hstep

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
  have hleft_ne : ((-1 : ℝ) ^ n) ≠ 0 := by rr_side_ne
  have hright_ne : ((-1 : ℝ) ^ (n + 1)) ≠ 0 := by rr_side_ne
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
    ∀ n : Nat, Prec (P n) (P (n + 1)) :=
  prec_sequence_of_affineFavardChainPackage <|
    affineFavardChainPackage_of_param_coeff hs hβ hP0 hP1 hstep

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
  isRealRooted_of_prec_chain_from_step <|
    favardInterlacing_affine_param_coeff hs hβ hP0 hP1 hstep

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
  ne_zero_of_isRealRooted_sequence <|
    isRealRooted_of_favard_affine_param_coeff hs hβ hP0 hP1 hstep

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
  isRealRooted_of_prec_chain_from_step <|
    favardInterlacing_affine_param_coeff_den hs hβ hP0 hP1 hden hraw

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
  ne_zero_of_isRealRooted_sequence <|
    isRealRooted_of_favard_affine_param_coeff_den hs hβ hP0 hP1 hden hraw

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
  favardInterlacing_affine_param_coeff hs hβ hP0 hP1 fun n =>
    eq_sub_C_mul_of_C_mul_eq_C_mul_sub_C_mul (hden n) (hraw n)

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
  isRealRooted_of_prec_chain_from_step <|
    favardInterlacing_affine_param_coeff_den_split hs hβ hP0 hP1 hden hraw

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
  ne_zero_of_isRealRooted_sequence <|
    isRealRooted_of_favard_affine_param_coeff_den_split hs hβ hP0 hP1 hden hraw

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
  isRealRooted_of_prec_chain_from_step <|
    favardInterlacing_affine_param_coeff_den_split_rev hs hβ hP0 hP1 hden hraw

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
  ne_zero_of_isRealRooted_sequence <|
    isRealRooted_of_favard_affine_param_coeff_den_split_rev
      hs hβ hP0 hP1 hden hraw

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
  isRealRooted_of_prec_chain_from_step <|
    favardInterlacing_affine_param_coeff_den_raw
      hs hβ hP0 hP1 hden hs_coeff hα_coeff hβ_coeff hraw

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
  ne_zero_of_isRealRooted_sequence <|
    isRealRooted_of_favard_affine_param_coeff_den_raw
      hs hβ hP0 hP1 hden hs_coeff hα_coeff hβ_coeff hraw

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
  isRealRooted_of_prec_chain_from_step <|
    favardInterlacing_affine_param_coeff_den_raw_prod
      hs hβ hP0 hP1 hden hs_coeff hα_coeff hβ_coeff hraw

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
  ne_zero_of_isRealRooted_sequence <|
    isRealRooted_of_favard_affine_param_coeff_den_raw_prod
      hs hβ hP0 hP1 hden hs_coeff hα_coeff hβ_coeff hraw

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
  have hleft_ne : ((-1 : ℝ) ^ n) ≠ 0 := by rr_side_ne
  have hright_ne : ((-1 : ℝ) ^ (n + 1)) ≠ 0 := by rr_side_ne
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

namespace Tactic

syntax (name := rr_favard_step_seq) "rr_favard_step_seq " term : term

syntax (name := rr_favard_step_dsimp_seq) "rr_favard_step_dsimp_seq " term : term

syntax (name := rr_favard_base_one) "rr_favard_base_one " term : term

syntax (name := rr_favard_base_one_dsimp) "rr_favard_base_one_dsimp " term : term

syntax (name := rr_favard_base_lookup_term) "rr_favard_base_lookup_term" : term

syntax (name := rr_favard_positive_lookup_term) "rr_favard_positive_lookup_term" : term

macro_rules
  | `(rr_favard_step_seq $hstep:term) =>
      `(fun n => by simpa using $hstep n)
  | `(rr_favard_step_dsimp_seq $hstep:term) =>
      `(by
        intro n
        first | dsimp | skip
        first
        | simpa using $hstep n
        | (convert ($hstep n) <;>
            first
              | (dsimp; simp; ring_nf)
              | (dsimp; simp)
              | (simp; ring_nf)
              | simp))
  | `(rr_favard_base_one $hP1:term) =>
      `(by simpa using $hP1)
  | `(rr_favard_base_one_dsimp $hP1:term) =>
      `(by
        first | dsimp | skip
        first
        | simpa using $hP1
        | (convert ($hP1) <;>
            first
              | (dsimp; simp; ring_nf)
              | (dsimp; simp)
              | (simp; ring_nf)
              | simp))
  | `(rr_favard_base_lookup_term) =>
      `(by
        first
          | rr_lookup
          | ((first | dsimp | skip); (first | simp | skip); rr_lookup))
  | `(rr_favard_positive_lookup_term) =>
      `(by
        first
          | rr_lookup
          | rr_positivity_seq)
syntax (name := rr_favard) "rr_favard" " using " term ", " term : tactic

syntax (name := rr_favard_inferred) "rr_favard" : tactic

syntax (name := rr_favard_named)
  "rr_favard" " using "
    "recurrence" ":=" term ","
    "beta_pos" ":=" term :
  tactic

syntax (name := rr_favard_auto_named)
  "rr_favard_auto" " using "
    "recurrence" ":=" term :
  tactic

syntax (name := rr_favard_auto_inferred) "rr_favard_auto" : tactic

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

syntax (name := rr_favard_const_unit)
  "rr_favard_const_unit" " using " term ", " term ", " term ", " term :
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

syntax (name := rr_favard_param_unit)
  "rr_favard_param_unit" " using " term ", " term ", " term ", " term :
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

syntax (name := rr_favard_affine_const_unit)
  "rr_favard_affine_const_unit" " using " term ", " term ", " term ", "
    term ", " term :
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

syntax (name := rr_favard_const_row_sign_unit)
  "rr_favard_const_row_sign_unit" " using " term ", " term ", " term ", " term :
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

syntax (name := rr_favard_affine_param_infer_named)
  "rr_favard_affine_param_infer" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
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

syntax (name := rr_favard_affine_param_den_auto_active_named)
  "rr_favard_affine_param_den_auto" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
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

syntax (name := rr_favard_affine_param_den_raw_active_named)
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

syntax (name := rr_favard_affine_param_den_raw_auto_active_named)
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

syntax (name := rr_favard_affine_param_den_raw_prod_active_named)
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

syntax (name := rr_favard_affine_param_den_raw_prod_auto_active_named)
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

syntax (name := rr_favard_affine_param_den_raw_unit_active_named)
  "rr_favard_affine_param_den_raw_unit" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "raw_slope" ":=" term ","
    "raw_const" ":=" term ","
    "raw_lag" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
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

syntax (name := rr_favard_param_den_raw_active_named)
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

syntax (name := rr_favard_param_den_raw_auto_active_named)
  "rr_favard_param_den_raw_auto" " using "
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "raw_slope" ":=" term ","
    "raw_const" ":=" term ","
    "raw_lag" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
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

syntax (name := rr_favard_param_den_raw_unit_active_named)
  "rr_favard_param_den_raw_unit" " using "
    "alpha" ":=" term ","
    "raw_slope" ":=" term ","
    "raw_const" ":=" term ","
    "raw_lag" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
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

syntax (name := rr_favard_affine_param_row_sign_den_raw_active_named)
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

syntax (name := rr_favard_affine_param_row_sign_den_raw_auto_active_named)
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

syntax (name := rr_favard_affine_param_row_sign_den_raw_prod_active_named)
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

syntax (name := rr_favard_affine_param_row_sign_den_raw_prod_auto_active_named)
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

syntax (name := rr_favard_affine_param_row_sign_den_raw_unit_active_named)
  "rr_favard_affine_param_row_sign_den_raw_unit" " using "
    "slope" ":=" term ","
    "alpha" ":=" term ","
    "raw_slope" ":=" term ","
    "raw_const" ":=" term ","
    "raw_lag" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
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

syntax (name := rr_favard_param_row_sign_den_raw_active_named)
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

syntax (name := rr_favard_param_row_sign_den_raw_auto_active_named)
  "rr_favard_param_row_sign_den_raw_auto" " using "
    "alpha" ":=" term ","
    "beta" ":=" term ","
    "raw_slope" ":=" term ","
    "raw_const" ":=" term ","
    "raw_lag" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
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

syntax (name := rr_favard_param_row_sign_den_raw_unit_active_named)
  "rr_favard_param_row_sign_den_raw_unit" " using "
    "alpha" ":=" term ","
    "raw_slope" ":=" term ","
    "raw_const" ":=" term ","
    "raw_lag" ":=" term ","
    "base_zero" ":=" term ","
    "base_one" ":=" term ","
    "den" ":=" term ","
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

syntax (name := rr_favard_den_raw_term) "rr_favard_den_raw_term " term : term

macro "rr_favard_active_den_all" : tactic =>
  `(tactic| rr_scalar_active_den_all)

macro "rr_favard_coeff_at " n:term : tactic =>
  `(tactic| rr_scalar_coeff_at $n)

macro "rr_favard_coeff_all" : tactic =>
  `(tactic| rr_scalar_coeff_all)

syntax (name := rr_favard_active_den_all_term)
  "rr_favard_active_den_all_term" : term

syntax (name := rr_favard_coeff_at_term)
  "rr_favard_coeff_at_term " term : term

syntax (name := rr_favard_coeff_all_term)
  "rr_favard_coeff_all_term" : term

syntax (name := rr_favard_goal_variants)
  "rr_favard_goal_variants"
    term ", " term ", " term ", " term ", " term ", " term :
  tactic

syntax (name := rr_favard_goal_variants_seq)
  "rr_favard_goal_variants" term ", " term ", " term :
  tactic

syntax (name := rr_favard_goal_variant_alternatives3)
  "rr_favard_goal_variant_alternatives3"
    term ", " term ", " term "; "
    term ", " term ", " term "; "
    term ", " term ", " term :
  tactic

syntax (name := rr_favard_refine_positivity_seq)
  "rr_favard_refine_positivity_seq " term :
  tactic

syntax (name := rr_favard_exact_realrooted_positivity_seq)
  "rr_favard_exact_realrooted_positivity_seq " term :
  tactic

macro_rules
  | `(tactic| rr_favard) =>
      `(tactic|
        rr_favard using
          recurrence := (by assumption),
          beta_pos := (by assumption))
  | `(tactic| rr_favard_auto) =>
      `(tactic|
        rr_favard_auto using
          recurrence := (by assumption))
  | `(tactic| rr_favard_refine_positivity_seq $h:term) =>
      `(tactic| rr_refine_then $h with rr_positivity_seq)
  | `(tactic| rr_favard_exact_realrooted_positivity_seq $h:term) =>
      `(tactic| rr_exact_realrooted_refine_then $h with rr_positivity_seq)
  | `(tactic|
      rr_favard_goal_variants
        $hinterlace:term, $hrealrooted:term, $hnonzero:term,
        $hinterlace_proj:term, $hrealrooted_proj:term, $hnonzero_proj:term) =>
      `(tactic|
        first
          | exact $hinterlace
          | rr_exact_realrooted_sequence_or_projection $hrealrooted
          | exact $hnonzero
          | exact $hinterlace_proj
          | rr_exact_realrooted_sequence_or_projection $hrealrooted_proj
          | exact $hnonzero_proj)
  | `(tactic|
      rr_favard_goal_variants
        $hinterlace:term, $hrealrooted:term, $hnonzero:term) =>
      `(tactic|
        rr_favard_goal_variants
          $hinterlace, $hrealrooted, $hnonzero,
          ($hinterlace _), ($hrealrooted _), ($hnonzero _))
  | `(tactic|
      rr_favard_goal_variant_alternatives3
        $hinterlace1:term, $hrealrooted1:term, $hnonzero1:term;
        $hinterlace2:term, $hrealrooted2:term, $hnonzero2:term;
        $hinterlace3:term, $hrealrooted3:term, $hnonzero3:term) =>
      `(tactic|
        first
          | rr_first_exact $hinterlace1, $hinterlace2, $hinterlace3
          | rr_first_exact $hrealrooted1, $hrealrooted2, $hrealrooted3
          | rr_first_exact $hnonzero1, $hnonzero2, $hnonzero3
          | rr_first_exact ($hinterlace1 _), ($hinterlace2 _), ($hinterlace3 _)
          | rr_first_exact ($hrealrooted1 _), ($hrealrooted2 _), ($hrealrooted3 _)
          | rr_first_exact ($hnonzero1 _), ($hnonzero2 _), ($hnonzero3 _))
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
  | `(rr_favard_den_raw_term $hraw:term) =>
      `(by rr_favard_den_raw using $hraw)
  | `(rr_favard_active_den_all_term) =>
      `(by rr_favard_active_den_all)
  | `(rr_favard_coeff_at_term $n:term) =>
      `(by rr_favard_coeff_at $n)
  | `(rr_favard_coeff_all_term) =>
      `(by rr_favard_coeff_all)
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
          | rr_favard_refine_positivity_seq
              (RealRooted.favardInterlacing $hrec ?_)
          | rr_favard_exact_realrooted_positivity_seq
              (RealRooted.isRealRooted_of_favard $hrec ?_)
          | rr_favard_refine_positivity_seq
              (RealRooted.nonzero_of_favard $hrec ?_)
          | rr_favard_refine_positivity_seq
              (RealRooted.isGeneralizedSturmSeq_reverse_range_map_of_favard
                $hrec ?_)
          | rr_favard_refine_positivity_seq
              (RealRooted.favardInterlacing $hrec ?_ _)
          | rr_favard_exact_realrooted_positivity_seq
              (RealRooted.isRealRooted_of_favard $hrec ?_ _)
          | rr_favard_refine_positivity_seq
              (RealRooted.nonzero_of_favard $hrec ?_ _)
          | rr_favard_refine_positivity_seq
              (RealRooted.isGeneralizedSturmSeq_reverse_range_map_of_favard
                $hrec ?_ _))
  | `(tactic|
      rr_favard_const using
        $α:term, $β:term, $hβ:term, $hP0:term, $hP1:term, $hstep:term) =>
      `(tactic|
        rr_favard_goal_variants
          (RealRooted.favardInterlacing_const_coeff
            (α := $α) (β := $β) $hβ $hP0 $hP1 $hstep),
          (RealRooted.isRealRooted_of_favard_const_coeff
            (α := $α) (β := $β) $hβ $hP0 $hP1 $hstep),
          (RealRooted.nonzero_of_favard_const_coeff
            (α := $α) (β := $β) $hβ $hP0 $hP1 $hstep))
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
          beta_pos := rr_positivity_term,
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
          base_one := rr_favard_base_one $hP1,
          step := rr_favard_step_seq $hstep)
  | `(tactic|
      rr_favard_const_unit using
        $α:term, $hP0:term, $hP1:term, $hstep:term) =>
      `(tactic|
        rr_favard_const_unit using
          alpha := $α,
          base_zero := $hP0,
          base_one := $hP1,
          step := $hstep)
  | `(tactic|
      rr_favard_param using
        $α:term, $β:term, $hβ:term, $hP0:term, $hP1:term, $hstep:term) =>
      `(tactic|
        rr_favard_goal_variants
          (RealRooted.favardInterlacing_param_coeff
            (α := $α) (β := $β) $hβ $hP0 $hP1 $hstep),
          (RealRooted.isRealRooted_of_favard_param_coeff
            (α := $α) (β := $β) $hβ $hP0 $hP1 $hstep),
          (RealRooted.nonzero_of_favard_param_coeff
            (α := $α) (β := $β) $hβ $hP0 $hP1 $hstep))
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
          beta_pos := rr_positivity_seq_term,
          base_zero := $hP0,
          base_one := rr_favard_base_one_dsimp $hP1,
          step := rr_favard_step_dsimp_seq $hstep)
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
          base_one := $hP1,
          step := $hstep)
  | `(tactic|
      rr_favard_param_unit using
        $α:term, $hP0:term, $hP1:term, $hstep:term) =>
      `(tactic|
        rr_favard_param_unit using
          alpha := $α,
          base_zero := $hP0,
          base_one := $hP1,
          step := $hstep)
  | `(tactic|
      rr_favard_affine_const using
        $s:term, $α:term, $β:term, $hs:term, $hβ:term, $hP0:term, $hP1:term,
        $hstep:term) =>
      `(tactic|
        rr_favard_goal_variants
          (RealRooted.favardInterlacing_affine_const_coeff
            (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep),
          (RealRooted.isRealRooted_of_favard_affine_const_coeff
            (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep),
          (RealRooted.nonzero_of_favard_affine_const_coeff
            (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep))
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
          slope_pos := rr_positivity_term,
          beta_pos := rr_positivity_term,
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
          base_one := rr_favard_base_one $hP1,
          step := rr_favard_step_seq $hstep)
  | `(tactic|
      rr_favard_affine_const_unit using
        $s:term, $α:term, $hP0:term, $hP1:term, $hstep:term) =>
      `(tactic|
        rr_favard_affine_const_unit using
          slope := $s,
          alpha := $α,
          base_zero := $hP0,
          base_one := $hP1,
          step := $hstep)
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
        rr_favard_goal_variants
          (RealRooted.favardInterlacing_affine_const_coeff_rowSign
            (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep),
          (RealRooted.isRealRooted_of_favard_affine_const_coeff_rowSign
            (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep),
          (RealRooted.nonzero_of_favard_affine_const_coeff_rowSign
            (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep))
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
          slope_pos := rr_positivity_term,
          beta_pos := rr_positivity_term,
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
          base_one := rr_favard_base_one $hP1,
          step := rr_favard_step_seq $hstep)
  | `(tactic|
      rr_favard_const_row_sign_unit using
        $α:term, $hP0:term, $hP1:term, $hstep:term) =>
      `(tactic|
        rr_favard_const_row_sign_unit using
          alpha := $α,
          base_zero := $hP0,
          base_one := $hP1,
          step := $hstep)
  | `(tactic|
      rr_favard_affine_param_infer using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        step := $hstep:term) =>
      `(tactic|
        first
          | rr_favard_affine_param using
              slope := $s,
              alpha := $α,
              beta := $β,
              slope_pos := rr_favard_positive_lookup_term,
              beta_pos := rr_favard_positive_lookup_term,
              base_zero := rr_favard_base_lookup_term,
              base_one := rr_favard_base_lookup_term,
              step := rr_favard_step_dsimp_seq $hstep
          | rr_favard_affine_param_row_sign using
              slope := $s,
              alpha := $α,
              beta := $β,
              slope_pos := rr_favard_positive_lookup_term,
              beta_pos := rr_favard_positive_lookup_term,
              base_zero := rr_favard_base_lookup_term,
              base_one := rr_favard_base_lookup_term,
              step := rr_favard_step_dsimp_seq $hstep)
  | `(tactic|
      rr_favard_affine_param using
        $s:term, $α:term, $β:term, $hs:term, $hβ:term, $hP0:term, $hP1:term,
        $hstep:term) =>
      `(tactic|
        rr_favard_goal_variants
          (RealRooted.favardInterlacing_affine_param_coeff
            (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep),
          (RealRooted.isRealRooted_of_favard_affine_param_coeff
            (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep),
          (RealRooted.nonzero_of_favard_affine_param_coeff
            (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep))
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
          slope_pos := rr_positivity_seq_term,
          beta_pos := rr_positivity_seq_term,
          base_zero := $hP0,
          base_one := rr_favard_base_one_dsimp $hP1,
          step := rr_favard_step_dsimp_seq $hstep)
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
        rr_favard_goal_variant_alternatives3
          (RealRooted.favardInterlacing_affine_param_coeff_den
            (s := $s) (α := $α) (β := $β) (d := $d)
            $hs $hβ $hP0 $hP1 $hden (rr_favard_den_raw_term $hraw)),
          (RealRooted.isRealRooted_of_favard_affine_param_coeff_den
            (s := $s) (α := $α) (β := $β) (d := $d)
            $hs $hβ $hP0 $hP1 $hden (rr_favard_den_raw_term $hraw)),
          (RealRooted.nonzero_of_favard_affine_param_coeff_den
            (s := $s) (α := $α) (β := $β) (d := $d)
            $hs $hβ $hP0 $hP1 $hden (rr_favard_den_raw_term $hraw));
          (RealRooted.favardInterlacing_affine_param_coeff_den_split
            (s := $s) (α := $α) (β := $β) (d := $d)
            $hs $hβ $hP0 $hP1 $hden (rr_favard_den_raw_term $hraw)),
          (RealRooted.isRealRooted_of_favard_affine_param_coeff_den_split
            (s := $s) (α := $α) (β := $β) (d := $d)
            $hs $hβ $hP0 $hP1 $hden (rr_favard_den_raw_term $hraw)),
          (RealRooted.nonzero_of_favard_affine_param_coeff_den_split
            (s := $s) (α := $α) (β := $β) (d := $d)
            $hs $hβ $hP0 $hP1 $hden (rr_favard_den_raw_term $hraw));
          (RealRooted.favardInterlacing_affine_param_coeff_den_split_rev
            (s := $s) (α := $α) (β := $β) (d := $d)
            $hs $hβ $hP0 $hP1 $hden (rr_favard_den_raw_term $hraw)),
          (RealRooted.isRealRooted_of_favard_affine_param_coeff_den_split_rev
            (s := $s) (α := $α) (β := $β) (d := $d)
            $hs $hβ $hP0 $hP1 $hden (rr_favard_den_raw_term $hraw)),
          (RealRooted.nonzero_of_favard_affine_param_coeff_den_split_rev
            (s := $s) (α := $α) (β := $β) (d := $d)
            $hs $hβ $hP0 $hP1 $hden (rr_favard_den_raw_term $hraw)))
  | `(tactic|
      rr_favard_affine_param_den_auto using
        slope := $s:term,
        alpha := $α:term,
        beta := $β:term,
        base_zero := $hP0:term,
        base_one := $hP1:term,
        den := $d:term,
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_den_auto using
          slope := $s,
          alpha := $α,
          beta := $β,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := rr_favard_active_den_all_term,
          raw_recurrence := $hraw)
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
          slope_pos := rr_positivity_seq_term,
          beta_pos := rr_positivity_seq_term,
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
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_den_raw using
          slope := $s,
          alpha := $α,
          beta := $β,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          slope_pos := $hs,
          beta_pos := $hβ,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := rr_favard_active_den_all_term,
          slope_coeff_eq := rr_favard_coeff_all_term,
          alpha_coeff_eq := rr_favard_coeff_all_term,
          beta_coeff_eq := rr_favard_coeff_all_term,
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
        rr_favard_goal_variants
          (RealRooted.favardInterlacing_affine_param_coeff_den_raw
            (s := $s) (α := $α) (β := $β) (d := $d)
            (araw := $araw) (braw := $braw) (craw := $craw)
            $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw),
          (RealRooted.isRealRooted_of_favard_affine_param_coeff_den_raw
            (s := $s) (α := $α) (β := $β) (d := $d)
            (araw := $araw) (braw := $braw) (craw := $craw)
            $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw),
          (RealRooted.nonzero_of_favard_affine_param_coeff_den_raw
            (s := $s) (α := $α) (β := $β) (d := $d)
            (araw := $araw) (braw := $braw) (craw := $craw)
            $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw))
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
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_den_raw_auto using
          slope := $s,
          alpha := $α,
          beta := $β,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := rr_favard_active_den_all_term,
          slope_coeff_eq := rr_favard_coeff_all_term,
          alpha_coeff_eq := rr_favard_coeff_all_term,
          beta_coeff_eq := rr_favard_coeff_all_term,
          raw_recurrence := $hraw)
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
          slope_pos := rr_positivity_seq_term,
          beta_pos := rr_positivity_seq_term,
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
          slope_pos := $hs,
          beta_pos := $hβ,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := rr_favard_active_den_all_term,
          slope_coeff_eq := rr_favard_coeff_all_term,
          alpha_coeff_eq := rr_favard_coeff_all_term,
          beta_coeff_eq := rr_favard_coeff_all_term,
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
        rr_favard_goal_variants
          (RealRooted.favardInterlacing_affine_param_coeff_den_raw_prod
            (s := $s) (α := $α) (β := $β) (d := $d)
            (aleft := $aleft) (aright := $aright) (braw := $braw)
            (cleft := $cleft) (cright := $cright)
            $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw),
          (RealRooted.isRealRooted_of_favard_affine_param_coeff_den_raw_prod
            (s := $s) (α := $α) (β := $β) (d := $d)
            (aleft := $aleft) (aright := $aright) (braw := $braw)
            (cleft := $cleft) (cright := $cright)
            $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw),
          (RealRooted.nonzero_of_favard_affine_param_coeff_den_raw_prod
            (s := $s) (α := $α) (β := $β) (d := $d)
            (aleft := $aleft) (aright := $aright) (braw := $braw)
            (cleft := $cleft) (cright := $cright)
            $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw))
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
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_den_raw_prod_auto using
          slope := $s,
          alpha := $α,
          beta := $β,
          raw_slope_left := $aleft,
          raw_slope_right := $aright,
          raw_const := $braw,
          raw_lag_left := $cleft,
          raw_lag_right := $cright,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := rr_favard_active_den_all_term,
          slope_coeff_eq := rr_favard_coeff_all_term,
          alpha_coeff_eq := rr_favard_coeff_all_term,
          beta_coeff_eq := rr_favard_coeff_all_term,
          raw_recurrence := $hraw)
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
          slope_pos := rr_positivity_seq_term,
          beta_pos := rr_positivity_seq_term,
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
          beta_pos := rr_positivity_seq_term,
          base_zero := $hP0,
          base_one := rr_favard_base_one_dsimp $hP1,
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
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_den_raw_unit using
          slope := $s,
          alpha := $α,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := rr_favard_active_den_all_term,
          slope_coeff_eq := rr_favard_coeff_all_term,
          alpha_coeff_eq := rr_favard_coeff_all_term,
          beta_coeff_eq := rr_favard_coeff_all_term,
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
          base_one := rr_favard_base_one_dsimp $hP1,
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
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_param_den_raw using
          alpha := $α,
          beta := $β,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          beta_pos := $hβ,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := rr_favard_active_den_all_term,
          slope_coeff_eq := rr_favard_coeff_all_term,
          alpha_coeff_eq := rr_favard_coeff_all_term,
          beta_coeff_eq := rr_favard_coeff_all_term,
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
          slope_pos := rr_positivity_seq_term,
          beta_pos := $hβ,
          base_zero := $hP0,
          base_one := rr_favard_base_one_dsimp $hP1,
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
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_param_den_raw_auto using
          alpha := $α,
          beta := $β,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := rr_favard_active_den_all_term,
          slope_coeff_eq := rr_favard_coeff_all_term,
          alpha_coeff_eq := rr_favard_coeff_all_term,
          beta_coeff_eq := rr_favard_coeff_all_term,
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
          beta_pos := rr_positivity_seq_term,
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
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_param_den_raw_unit using
          alpha := $α,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := rr_favard_active_den_all_term,
          slope_coeff_eq := rr_favard_coeff_all_term,
          alpha_coeff_eq := rr_favard_coeff_all_term,
          beta_coeff_eq := rr_favard_coeff_all_term,
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
          beta_pos := rr_positivity_seq_term,
          base_zero := $hP0,
          base_one := rr_favard_base_one_dsimp $hP1,
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
          base_one := rr_favard_base_one_dsimp $hP1,
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
          slope_pos := rr_positivity_seq_term,
          beta_pos := $hβ,
          base_zero := $hP0,
          base_one := rr_favard_base_one_dsimp $hP1,
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
          beta_pos := rr_positivity_seq_term,
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
          beta_pos := rr_positivity_seq_term,
          base_zero := $hP0,
          base_one := rr_favard_base_one_dsimp $hP1,
          step := rr_favard_step_dsimp_seq $hstep)
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
          base_one := $hP1,
          step := $hstep)
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
        rr_favard_goal_variants
          (RealRooted.favardInterlacing_affine_param_coeff_rowSign
            (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep),
          (RealRooted.isRealRooted_of_favard_affine_param_coeff_rowSign
            (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep),
          (RealRooted.nonzero_of_favard_affine_param_coeff_rowSign
            (s := $s) (α := $α) (β := $β) $hs $hβ $hP0 $hP1 $hstep))
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
          slope_pos := rr_positivity_seq_term,
          beta_pos := rr_positivity_seq_term,
          base_zero := $hP0,
          base_one := rr_favard_base_one_dsimp $hP1,
          step := rr_favard_step_dsimp_seq $hstep)
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
        rr_favard_goal_variant_alternatives3
          (RealRooted.favardInterlacing_affine_param_coeff_rowSign_den
            (s := $s) (α := $α) (β := $β) (d := $d)
            $hs $hβ $hP0 $hP1 $hden (rr_favard_den_raw_term $hraw)),
          (RealRooted.isRealRooted_of_favard_affine_param_coeff_rowSign_den
            (s := $s) (α := $α) (β := $β) (d := $d)
            $hs $hβ $hP0 $hP1 $hden (rr_favard_den_raw_term $hraw)),
          (RealRooted.nonzero_of_favard_affine_param_coeff_rowSign_den
            (s := $s) (α := $α) (β := $β) (d := $d)
            $hs $hβ $hP0 $hP1 $hden (rr_favard_den_raw_term $hraw));
          (RealRooted.favardInterlacing_affine_param_coeff_rowSign_den_split
            (s := $s) (α := $α) (β := $β) (d := $d)
            $hs $hβ $hP0 $hP1 $hden (rr_favard_den_raw_term $hraw)),
          (RealRooted.isRealRooted_of_favard_affine_param_coeff_rowSign_den_split
            (s := $s) (α := $α) (β := $β) (d := $d)
            $hs $hβ $hP0 $hP1 $hden (rr_favard_den_raw_term $hraw)),
          (RealRooted.nonzero_of_favard_affine_param_coeff_rowSign_den_split
            (s := $s) (α := $α) (β := $β) (d := $d)
            $hs $hβ $hP0 $hP1 $hden (rr_favard_den_raw_term $hraw));
          (RealRooted.favardInterlacing_affine_param_coeff_rowSign_den_split_rev
            (s := $s) (α := $α) (β := $β) (d := $d)
            $hs $hβ $hP0 $hP1 $hden (rr_favard_den_raw_term $hraw)),
          (RealRooted.isRealRooted_of_favard_affine_param_coeff_rowSign_den_split_rev
            (s := $s) (α := $α) (β := $β) (d := $d)
            $hs $hβ $hP0 $hP1 $hden (rr_favard_den_raw_term $hraw)),
          (RealRooted.nonzero_of_favard_affine_param_coeff_rowSign_den_split_rev
            (s := $s) (α := $α) (β := $β) (d := $d)
            $hs $hβ $hP0 $hP1 $hden (rr_favard_den_raw_term $hraw)))
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
          slope_pos := rr_positivity_seq_term,
          beta_pos := rr_positivity_seq_term,
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
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den_raw using
          slope := $s,
          alpha := $α,
          beta := $β,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          slope_pos := $hs,
          beta_pos := $hβ,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := rr_favard_active_den_all_term,
          slope_coeff_eq := rr_favard_coeff_all_term,
          alpha_coeff_eq := rr_favard_coeff_all_term,
          beta_coeff_eq := rr_favard_coeff_all_term,
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
        rr_favard_goal_variants
          (RealRooted.favardInterlacing_affine_param_coeff_rowSign_den_raw
            (s := $s) (α := $α) (β := $β) (d := $d)
            (araw := $araw) (braw := $braw) (craw := $craw)
            $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw),
          (RealRooted.isRealRooted_of_favard_affine_param_coeff_rowSign_den_raw
            (s := $s) (α := $α) (β := $β) (d := $d)
            (araw := $araw) (braw := $braw) (craw := $craw)
            $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw),
          (RealRooted.nonzero_of_favard_affine_param_coeff_rowSign_den_raw
            (s := $s) (α := $α) (β := $β) (d := $d)
            (araw := $araw) (braw := $braw) (craw := $craw)
            $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw))
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
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den_raw_auto using
          slope := $s,
          alpha := $α,
          beta := $β,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := rr_favard_active_den_all_term,
          slope_coeff_eq := rr_favard_coeff_all_term,
          alpha_coeff_eq := rr_favard_coeff_all_term,
          beta_coeff_eq := rr_favard_coeff_all_term,
          raw_recurrence := $hraw)
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
          slope_pos := rr_positivity_seq_term,
          beta_pos := rr_positivity_seq_term,
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
          slope_pos := $hs,
          beta_pos := $hβ,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := rr_favard_active_den_all_term,
          slope_coeff_eq := rr_favard_coeff_all_term,
          alpha_coeff_eq := rr_favard_coeff_all_term,
          beta_coeff_eq := rr_favard_coeff_all_term,
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
        rr_favard_goal_variants
          (RealRooted.favardInterlacing_affine_param_coeff_rowSign_den_raw_prod
            (s := $s) (α := $α) (β := $β) (d := $d)
            (aleft := $aleft) (aright := $aright) (braw := $braw)
            (cleft := $cleft) (cright := $cright)
            $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw),
          (RealRooted.isRealRooted_of_favard_affine_param_coeff_rowSign_den_raw_prod
            (s := $s) (α := $α) (β := $β) (d := $d)
            (aleft := $aleft) (aright := $aright) (braw := $braw)
            (cleft := $cleft) (cright := $cright)
            $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw),
          (RealRooted.nonzero_of_favard_affine_param_coeff_rowSign_den_raw_prod
            (s := $s) (α := $α) (β := $β) (d := $d)
            (aleft := $aleft) (aright := $aright) (braw := $braw)
            (cleft := $cleft) (cright := $cright)
            $hs $hβ $hP0 $hP1 $hden $hs_coeff $hα_coeff $hβ_coeff $hraw))
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
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den_raw_prod_auto using
          slope := $s,
          alpha := $α,
          beta := $β,
          raw_slope_left := $aleft,
          raw_slope_right := $aright,
          raw_const := $braw,
          raw_lag_left := $cleft,
          raw_lag_right := $cright,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := rr_favard_active_den_all_term,
          slope_coeff_eq := rr_favard_coeff_all_term,
          alpha_coeff_eq := rr_favard_coeff_all_term,
          beta_coeff_eq := rr_favard_coeff_all_term,
          raw_recurrence := $hraw)
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
          slope_pos := rr_positivity_seq_term,
          beta_pos := rr_positivity_seq_term,
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
          beta_pos := rr_positivity_seq_term,
          base_zero := $hP0,
          base_one := rr_favard_base_one_dsimp $hP1,
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
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_affine_param_row_sign_den_raw_unit using
          slope := $s,
          alpha := $α,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := rr_favard_active_den_all_term,
          slope_coeff_eq := rr_favard_coeff_all_term,
          alpha_coeff_eq := rr_favard_coeff_all_term,
          beta_coeff_eq := rr_favard_coeff_all_term,
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
          base_one := rr_favard_base_one_dsimp $hP1,
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
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_param_row_sign_den_raw using
          alpha := $α,
          beta := $β,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          beta_pos := $hβ,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := rr_favard_active_den_all_term,
          slope_coeff_eq := rr_favard_coeff_all_term,
          alpha_coeff_eq := rr_favard_coeff_all_term,
          beta_coeff_eq := rr_favard_coeff_all_term,
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
          slope_pos := rr_positivity_seq_term,
          beta_pos := $hβ,
          base_zero := $hP0,
          base_one := rr_favard_base_one_dsimp $hP1,
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
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_param_row_sign_den_raw_auto using
          alpha := $α,
          beta := $β,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := rr_favard_active_den_all_term,
          slope_coeff_eq := rr_favard_coeff_all_term,
          alpha_coeff_eq := rr_favard_coeff_all_term,
          beta_coeff_eq := rr_favard_coeff_all_term,
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
          beta_pos := rr_positivity_seq_term,
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
        raw_recurrence := $hraw:term) =>
      `(tactic|
        rr_favard_param_row_sign_den_raw_unit using
          alpha := $α,
          raw_slope := $araw,
          raw_const := $braw,
          raw_lag := $craw,
          base_zero := $hP0,
          base_one := $hP1,
          den := $d,
          den_nonzero := rr_favard_active_den_all_term,
          slope_coeff_eq := rr_favard_coeff_all_term,
          alpha_coeff_eq := rr_favard_coeff_all_term,
          beta_coeff_eq := rr_favard_coeff_all_term,
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
          beta_pos := rr_positivity_seq_term,
          base_zero := $hP0,
          base_one := rr_favard_base_one_dsimp $hP1,
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
          base_one := rr_favard_base_one_dsimp $hP1,
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
          slope_pos := rr_positivity_seq_term,
          beta_pos := $hβ,
          base_zero := $hP0,
          base_one := rr_favard_base_one_dsimp $hP1,
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
          beta_pos := rr_positivity_seq_term,
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
          beta_pos := rr_positivity_seq_term,
          base_zero := $hP0,
          base_one := rr_favard_base_one_dsimp $hP1,
          step := rr_favard_step_dsimp_seq $hstep)
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
          base_one := $hP1,
          step := $hstep)
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
          slope_pos := rr_positivity_seq_term,
          beta_pos := $hβ,
          base_zero := $hP0,
          base_one := rr_favard_base_one_dsimp $hP1,
          step := rr_favard_step_dsimp_seq $hstep)
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
          beta_pos := rr_positivity_seq_term,
          base_zero := $hP0,
          base_one := $hP1,
          step := $hstep)

end Tactic
end RealRooted
