import RealRooted.Favard
import RealRooted.SequenceClosure
import Mathlib.Tactic

/-!
# Direct affine Favard recurrences

This module owns theorem APIs for monic and positive-slope affine three-term
recurrences presented directly, without scalar denominators or row-sign
normalization.
-/

open Polynomial

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
  exact hasPosLeadingCoeff_C_mul hs (hasPosLeadingCoeff_X_sub_C _)

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
  have hdeg_gf : g.natDegree + 1 = f.natDegree := by simpa using natDegree_succ_of_interlaces hInter
  have hf_ne : f ≠ 0 := by simpa using right_ne_zero_of_interlaces hInter
  have hAf_deg : (aPoly * f).natDegree = f.natDegree + 1 := by
    rw [natDegree_mul hA_ne hf_ne, hA_deg]
    lia
  have hAf_pos : HasPosLeadingCoeff (aPoly * f) := hA_pos.mul hf_pos
  have hBg_lt_Af : (bPoly * g).natDegree < (aPoly * f).natDegree := by lia
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
      exact hasPosLeadingCoeff_one
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
    have hA_ne : aPoly ≠ 0 := hA_pos.ne_zero
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


/-- Consecutive interlacing for the positive-slope parameterized affine Favard
wrapper. -/
theorem interlaces_of_favard_affine_param_coeff
    {P : Nat → ℝ[X]} {s α β : Nat → ℝ}
    (hs : ∀ n : Nat, 0 < s n)
    (hβ : ∀ n : Nat, 0 < β (n + 1))
    (hP0 : P 0 = 1)
    (hP1 : P 1 = C (s 0) * X - C (α 0))
    (hstep : ∀ n : Nat,
      P (n + 2) =
        (C (s (n + 1)) * X - C (α (n + 1))) * P (n + 1) -
          C (β (n + 1)) * P n) :
    ∀ n : Nat, Interlaces (P n) (P (n + 1)) := fun n =>
  (affineFavardChainPackage_of_param_coeff hs hβ hP0 hP1 hstep n).1

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
    ∀ n : Nat, Prec (P n) (P (n + 1)) := fun n =>
  (interlaces_of_favard_affine_param_coeff hs hβ hP0 hP1 hstep n).toPrec

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


end RealRooted
