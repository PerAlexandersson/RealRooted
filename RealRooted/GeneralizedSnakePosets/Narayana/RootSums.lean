import RealRooted.GeneralizedSnakePosets.Narayana.Recurrence

/-!
# Modified-Narayana root-sum orientation

This module derives the Vieta/root-sum comparison used in Braun--Jal Claim 7,
packages the corresponding induction routes, and records the obstruction to
the older uniformly strict root-bound interface.
-/

open Polynomial Filter

noncomputable section

namespace RealRooted
namespace GeneralizedSnakePosets

/-- Concrete modified-Narayana/auxiliary-`G` route for Braun--Jal Theorem 4.1.

This discharges the standard modified-Narayana facts and the elementary
auxiliary-`G` facts from the generic Section 3 route.  The remaining hypotheses
are the all-`n` equation `(2)`, Claim `(7)` side conditions, adjacent
interlacing of the auxiliary `G` column, and the word-family side conditions.
-/
theorem theorem41InductionRoute_modified_of_section3_of_constant_matches_succ_length
    {M : SnakeWord → ℝ[X]}
    (hrec2 :
      NarayanaAuxiliaryGRecurrenceStatement
        modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG)
    (hside :
      Theorem41Claim7SideConditions
        modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG)
    (hG : ∀ {m : ℕ}, 2 ≤ m →
      Prec (FiniteSkewBoard.auxiliaryG (m - 1)) (FiniteSkewBoard.auxiliaryG m))
    (hM_nonneg : ∀ w, HasNonnegCoeffs (M w))
    (hdeg :
      ∀ {w : SnakeWord}, 1 ≤ w.length →
        (M w.deleteFinal).natDegree + 1 = (M w).natDegree)
    (hM_const :
      ∀ {w : SnakeWord}, w.IsConstant →
        M w = modifiedNarayanaPolynomial (w.length + 1)) :
    Theorem41InductionRouteStatement
      M modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG :=
  theorem41InductionRoute_of_section3_of_constant_matches_succ_length
    (M := M) (P := modifiedNarayanaPolynomial) (G := FiniteSkewBoard.auxiliaryG)
    hrec2 hside modifiedNarayanaPolynomial_interlaces_succ hG
    modifiedNarayanaPolynomial_one FiniteSkewBoard.auxiliaryG_one
    modifiedNarayanaPolynomial_hasNonnegCoeffs
    FiniteSkewBoard.auxiliaryG_hasNonnegCoeffs hM_nonneg hdeg hM_const

/-- Endpoint-compatible modified-Narayana route for Braun--Jal Theorem 4.1,
using root sums to orient Claim `(7)`. -/
theorem theorem41InductionRoute_modified_of_section3_rootSum_of_constant_matches_succ_length
    {M : SnakeWord → ℝ[X]}
    (hrec2 :
      NarayanaAuxiliaryGRecurrenceStatement
        modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG)
    (hside :
      Theorem41Claim7RootSumSideConditions
        modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG)
    (hG : ∀ {m : ℕ}, 2 ≤ m →
      Prec (FiniteSkewBoard.auxiliaryG (m - 1)) (FiniteSkewBoard.auxiliaryG m))
    (hM_nonneg : ∀ w, HasNonnegCoeffs (M w))
    (hdeg :
      ∀ {w : SnakeWord}, 1 ≤ w.length →
        (M w.deleteFinal).natDegree + 1 = (M w).natDegree)
    (hM_const :
      ∀ {w : SnakeWord}, w.IsConstant →
        M w = modifiedNarayanaPolynomial (w.length + 1)) :
    Theorem41InductionRouteStatement
      M modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG :=
  theorem41InductionRoute_of_section3_rootSum_of_constant_matches_succ_length
    (M := M) (P := modifiedNarayanaPolynomial) (G := FiniteSkewBoard.auxiliaryG)
    hrec2 hside modifiedNarayanaPolynomial_interlaces_succ hG
    modifiedNarayanaPolynomial_one FiniteSkewBoard.auxiliaryG_one
    modifiedNarayanaPolynomial_hasNonnegCoeffs
    FiniteSkewBoard.auxiliaryG_hasNonnegCoeffs hM_nonneg hdeg hM_const

/-- Arithmetic comparison between the Vieta expressions predicted by the
leading and next coefficients of the modified-Narayana `U` window and the
auxiliary-`G` `V` window. -/
theorem theorem41Claim7_modified_rootSum_ratio_le
    (d lam nu : ℝ) (hd : 2 ≤ d) (hlam : 0 ≤ lam) (hnu : -1 ≤ nu) :
    -(d * (d + 1) / 2 + lam * (d - 1) * d / 2 + nu) / (lam + 1) ≤
      -((d + 1) * d * (d - 1) / 3 +
          lam * d * (d - 1) * (d - 2) / 3 + nu * (d - 1)) /
        (d + lam * (d - 1)) := by
  have h2 : (0 : ℝ) ≤ d - 2 := by linarith
  rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < lam + 1)
    (by nlinarith : (0 : ℝ) < d + lam * (d - 1))]
  nlinarith [mul_nonneg h2 (sq_nonneg (d - 2)), mul_nonneg hlam h2,
    sq_nonneg lam]

/-- For `m ≥ 3`, equation `(2)`, the expected window degrees, and splitting
identify the two root sums with the Vieta expressions compared by
`theorem41Claim7_modified_rootSum_ratio_le`. -/
theorem theorem41Claim7_modified_roots_sum_le_of_recurrence_of_three_le
    (hrec2 :
      NarayanaAuxiliaryGRecurrenceStatement
        modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG)
    {m : ℕ} {lam nu : ℝ} (hm : 3 ≤ m) (hlam : 0 ≤ lam) (hnu : -1 ≤ nu)
    (hU_split :
      ((C lam * X + C nu) * modifiedNarayanaPolynomial (m - 1) +
        modifiedNarayanaPolynomial m).Splits)
    (hV_split :
      ((C lam * X + C nu) * FiniteSkewBoard.auxiliaryG (m - 1) +
        FiniteSkewBoard.auxiliaryG m).Splits)
    (hUdeg :
      ((C lam * X + C nu) * modifiedNarayanaPolynomial (m - 1) +
        modifiedNarayanaPolynomial m).natDegree = m)
    (hVdeg :
      ((C lam * X + C nu) * FiniteSkewBoard.auxiliaryG (m - 1) +
        FiniteSkewBoard.auxiliaryG m).natDegree = m - 1) :
    ((C lam * X + C nu) * modifiedNarayanaPolynomial (m - 1) +
        modifiedNarayanaPolynomial m).roots.sum ≤
      ((C lam * X + C nu) * FiniteSkewBoard.auxiliaryG (m - 1) +
        FiniteSkewBoard.auxiliaryG m).roots.sum := by
  let U :=
    (C lam * X + C nu) * modifiedNarayanaPolynomial (m - 1) +
      modifiedNarayanaPolynomial m
  let V :=
    (C lam * X + C nu) * FiniteSkewBoard.auxiliaryG (m - 1) +
      FiniteSkewBoard.auxiliaryG m
  change U.Splits at hU_split
  change V.Splits at hV_split
  change U.natDegree = m at hUdeg
  change V.natDegree = m - 1 at hVdeg
  change U.roots.sum ≤ V.roots.sum
  have hm1 : 1 ≤ m - 1 := by lia
  have hm1two : 2 ≤ m - 1 := by lia
  have hcast1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by lia)]
    norm_num
  have hPprevLead :
      (modifiedNarayanaPolynomial (m - 1)).coeff (m - 1) = 1 := by
    calc
      _ = (modifiedNarayanaPolynomial (m - 1)).coeff
          (modifiedNarayanaPolynomial (m - 1)).natDegree := by
            rw [modifiedNarayanaPolynomial_natDegree]
      _ = (modifiedNarayanaPolynomial (m - 1)).leadingCoeff := coeff_natDegree
      _ = 1 := modifiedNarayanaPolynomial_leadingCoeff (m - 1)
  have hPprevNext :=
    modifiedNarayanaPolynomial_coeff_sub_one (m - 1) hm1
  have hPprevAbove :
      (modifiedNarayanaPolynomial (m - 1)).coeff m = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [modifiedNarayanaPolynomial_natDegree]
    lia
  have hPmLead : (modifiedNarayanaPolynomial m).coeff m = 1 := by
    calc
      _ = (modifiedNarayanaPolynomial m).coeff
          (modifiedNarayanaPolynomial m).natDegree := by rw [modifiedNarayanaPolynomial_natDegree]
      _ = (modifiedNarayanaPolynomial m).leadingCoeff := coeff_natDegree
      _ = 1 := modifiedNarayanaPolynomial_leadingCoeff m
  have hPmNext := modifiedNarayanaPolynomial_coeff_sub_one m (by lia)
  have hGmLead :=
    auxiliaryG_coeff_sub_one_of_narayanaRecurrence hrec2 m (by lia)
  have hGmNext :=
    auxiliaryG_coeff_sub_two_of_narayanaRecurrence hrec2 m (by lia)
  have hGprevLead :=
    auxiliaryG_coeff_sub_one_of_narayanaRecurrence hrec2 (m - 1) hm1
  have hGprevNext :=
    auxiliaryG_coeff_sub_two_of_narayanaRecurrence hrec2 (m - 1) hm1two
  have hGprevAbove :=
    auxiliaryG_coeff_self_of_narayanaRecurrence hrec2 (m - 1)
  rw [show m - 1 - 1 = m - 2 by lia] at hPprevNext hGprevLead
  rw [show m - 1 - 2 = m - 3 by lia] at hGprevNext
  have hXPprevLead :
      (X * modifiedNarayanaPolynomial (m - 1)).coeff m = 1 := by
    calc
      _ = (X * modifiedNarayanaPolynomial (m - 1)).coeff ((m - 1) + 1) :=
        congr_arg
          (fun k => (X * modifiedNarayanaPolynomial (m - 1)).coeff k) (by lia)
      _ = (modifiedNarayanaPolynomial (m - 1)).coeff (m - 1) := by
        exact coeff_X_mul (modifiedNarayanaPolynomial (m - 1)) (m - 1)
      _ = 1 := hPprevLead
  have hXPprevNext :
      (X * modifiedNarayanaPolynomial (m - 1)).coeff (m - 1) =
        (modifiedNarayanaPolynomial (m - 1)).coeff (m - 2) := by
    calc
      _ = (X * modifiedNarayanaPolynomial (m - 1)).coeff ((m - 2) + 1) :=
        congr_arg
          (fun k => (X * modifiedNarayanaPolynomial (m - 1)).coeff k) (by lia)
      _ = _ := coeff_X_mul (modifiedNarayanaPolynomial (m - 1)) (m - 2)
  have hXGprevLead :
      (X * FiniteSkewBoard.auxiliaryG (m - 1)).coeff (m - 1) =
        (FiniteSkewBoard.auxiliaryG (m - 1)).coeff (m - 2) := by
    calc
      _ = (X * FiniteSkewBoard.auxiliaryG (m - 1)).coeff ((m - 2) + 1) :=
        congr_arg
          (fun k => (X * FiniteSkewBoard.auxiliaryG (m - 1)).coeff k) (by lia)
      _ = _ := coeff_X_mul (FiniteSkewBoard.auxiliaryG (m - 1)) (m - 2)
  have hXGprevNext :
      (X * FiniteSkewBoard.auxiliaryG (m - 1)).coeff (m - 2) =
        (FiniteSkewBoard.auxiliaryG (m - 1)).coeff (m - 3) := by
    calc
      _ = (X * FiniteSkewBoard.auxiliaryG (m - 1)).coeff ((m - 3) + 1) :=
        congr_arg
          (fun k => (X * FiniteSkewBoard.auxiliaryG (m - 1)).coeff k) (by lia)
      _ = _ := coeff_X_mul (FiniteSkewBoard.auxiliaryG (m - 1)) (m - 3)
  have hUlc : U.leadingCoeff = lam + 1 := by
    rw [leadingCoeff, hUdeg]
    dsimp [U]
    rw [show
        (C lam * X + C nu) * modifiedNarayanaPolynomial (m - 1) =
          C lam * (X * modifiedNarayanaPolynomial (m - 1)) +
            C nu * modifiedNarayanaPolynomial (m - 1) by ring]
    simp only [coeff_add, coeff_C_mul]
    rw [hXPprevLead, hPprevAbove, hPmLead]
    ring
  have hUnext :
      U.nextCoeff =
        (m : ℝ) * (m + 1) / 2 + lam * (m - 1) * m / 2 + nu := by
    rw [nextCoeff_of_natDegree_pos (by rw [hUdeg]; lia), hUdeg]
    dsimp [U]
    rw [show
        (C lam * X + C nu) * modifiedNarayanaPolynomial (m - 1) =
          C lam * (X * modifiedNarayanaPolynomial (m - 1)) +
            C nu * modifiedNarayanaPolynomial (m - 1) by ring]
    simp only [coeff_add, coeff_C_mul]
    rw [hXPprevNext, hPprevNext, hPprevLead, hPmNext, hcast1]
    ring
  have hVlc : V.leadingCoeff = (m : ℝ) + lam * (m - 1) := by
    rw [leadingCoeff, hVdeg]
    dsimp [V]
    rw [show
        (C lam * X + C nu) * FiniteSkewBoard.auxiliaryG (m - 1) =
          C lam * (X * FiniteSkewBoard.auxiliaryG (m - 1)) +
            C nu * FiniteSkewBoard.auxiliaryG (m - 1) by ring]
    simp only [coeff_add, coeff_C_mul]
    rw [hXGprevLead, hGprevLead, hGprevAbove, hGmLead, hcast1]
    ring
  have hVnext :
      V.nextCoeff =
        (m + 1 : ℝ) * m * (m - 1) / 3 +
          lam * m * (m - 1) * (m - 2) / 3 + nu * (m - 1) := by
    rw [nextCoeff_of_natDegree_pos (by rw [hVdeg]; lia), hVdeg]
    rw [show m - 1 - 1 = m - 2 by lia]
    dsimp [V]
    rw [show
        (C lam * X + C nu) * FiniteSkewBoard.auxiliaryG (m - 1) =
          C lam * (X * FiniteSkewBoard.auxiliaryG (m - 1)) +
            C nu * FiniteSkewBoard.auxiliaryG (m - 1) by ring]
    simp only [coeff_add, coeff_C_mul]
    rw [hXGprevNext, hGprevNext, hGprevLead, hGmNext, hcast1]
    ring
  have hUlc_ne : U.leadingCoeff ≠ 0 := by
    rw [hUlc]
    linarith
  have hVlc_ne : V.leadingCoeff ≠ 0 := by
    rw [hVlc]
    have hm_real : (2 : ℝ) ≤ m := by exact_mod_cast (show 2 ≤ m by lia)
    have hterm : 0 ≤ lam * ((m : ℝ) - 1) :=
      mul_nonneg hlam (by linarith)
    nlinarith
  rw [hU_split.sum_roots_eq_neg_nextCoeff_div_leadingCoeff hUlc_ne,
    hV_split.sum_roots_eq_neg_nextCoeff_div_leadingCoeff hVlc_ne,
    hUnext, hUlc, hVnext, hVlc]
  exact theorem41Claim7_modified_rootSum_ratio_le m lam nu
    (by exact_mod_cast (show 2 ≤ m by lia)) hlam hnu

/-- The endpoint `m = 2` case of the modified-Narayana root-sum comparison. -/
theorem theorem41Claim7_modified_roots_sum_le_two
    {lam nu : ℝ} (hlam : 0 ≤ lam) (hnu : -1 ≤ nu)
    (hU_split :
      ((C lam * X + C nu) * modifiedNarayanaPolynomial (2 - 1) +
        modifiedNarayanaPolynomial 2).Splits)
    (hV_split :
      ((C lam * X + C nu) * FiniteSkewBoard.auxiliaryG (2 - 1) +
        FiniteSkewBoard.auxiliaryG 2).Splits)
    (hUdeg :
      ((C lam * X + C nu) * modifiedNarayanaPolynomial (2 - 1) +
        modifiedNarayanaPolynomial 2).natDegree = 2)
    (hVdeg :
      ((C lam * X + C nu) * FiniteSkewBoard.auxiliaryG (2 - 1) +
        FiniteSkewBoard.auxiliaryG 2).natDegree = 1) :
    ((C lam * X + C nu) * modifiedNarayanaPolynomial (2 - 1) +
        modifiedNarayanaPolynomial 2).roots.sum ≤
      ((C lam * X + C nu) * FiniteSkewBoard.auxiliaryG (2 - 1) +
        FiniteSkewBoard.auxiliaryG 2).roots.sum := by
  let U :=
    (C lam * X + C nu) * modifiedNarayanaPolynomial (2 - 1) +
      modifiedNarayanaPolynomial 2
  let V :=
    (C lam * X + C nu) * FiniteSkewBoard.auxiliaryG (2 - 1) +
      FiniteSkewBoard.auxiliaryG 2
  change U.Splits at hU_split
  change V.Splits at hV_split
  change U.natDegree = 2 at hUdeg
  change V.natDegree = 1 at hVdeg
  change U.roots.sum ≤ V.roots.sum
  have hUeq :
      U = C (nu + 1) + C (lam + nu + 3) * X + C (lam + 1) * X ^ 2 := by
    dsimp [U]
    rw [modifiedNarayanaPolynomial_one, modifiedNarayanaPolynomial_two]
    simp only [map_add, map_ofNat, map_one]
    ring
  have hVeq : V = C (nu + 2) + C (lam + 2) * X := by
    dsimp [V]
    rw [FiniteSkewBoard.auxiliaryG_one, FiniteSkewBoard.auxiliaryG_two]
    simp only [map_add, map_ofNat]
    ring
  have hUlc : U.leadingCoeff = lam + 1 := by
    rw [leadingCoeff, hUdeg, hUeq]
    simp only [coeff_add, coeff_C_mul, coeff_C, coeff_X, coeff_X_pow]
    norm_num
  have hUnext : U.nextCoeff = lam + nu + 3 := by
    rw [nextCoeff_of_natDegree_pos (by rw [hUdeg]; norm_num), hUdeg, hUeq]
    simp only [coeff_add, coeff_C_mul, coeff_C, coeff_X, coeff_X_pow]
    norm_num
  have hVlc : V.leadingCoeff = lam + 2 := by
    rw [leadingCoeff, hVdeg, hVeq]
    simp only [coeff_add, coeff_C_mul, coeff_C, coeff_X]
    norm_num
  have hVnext : V.nextCoeff = nu + 2 := by
    rw [nextCoeff_of_natDegree_pos (by rw [hVdeg]; norm_num), hVdeg, hVeq]
    simp only [coeff_add, coeff_C_mul, coeff_C, coeff_X]
    norm_num
  have hUlc_ne : U.leadingCoeff ≠ 0 := by
    rw [hUlc]
    linarith
  have hVlc_ne : V.leadingCoeff ≠ 0 := by
    rw [hVlc]
    linarith
  rw [hU_split.sum_roots_eq_neg_nextCoeff_div_leadingCoeff hUlc_ne,
    hV_split.sum_roots_eq_neg_nextCoeff_div_leadingCoeff hVlc_ne,
    hUnext, hUlc, hVnext, hVlc]
  convert theorem41Claim7_modified_rootSum_ratio_le 2 lam nu (by norm_num) hlam hnu
      using 1 <;>
    ring

/-- Uniform modified-Narayana root-sum comparison from equation `(2)`, the
expected window degrees, and splitting. -/
theorem theorem41Claim7_modified_roots_sum_le_of_recurrence
    (hrec2 :
      NarayanaAuxiliaryGRecurrenceStatement
        modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG)
    {m : ℕ} {lam nu : ℝ} (hm : 2 ≤ m) (hlam : 0 ≤ lam) (hnu : -1 ≤ nu)
    (hU_split :
      ((C lam * X + C nu) * modifiedNarayanaPolynomial (m - 1) +
        modifiedNarayanaPolynomial m).Splits)
    (hV_split :
      ((C lam * X + C nu) * FiniteSkewBoard.auxiliaryG (m - 1) +
        FiniteSkewBoard.auxiliaryG m).Splits)
    (hUdeg :
      ((C lam * X + C nu) * modifiedNarayanaPolynomial (m - 1) +
        modifiedNarayanaPolynomial m).natDegree = m)
    (hVdeg :
      ((C lam * X + C nu) * FiniteSkewBoard.auxiliaryG (m - 1) +
        FiniteSkewBoard.auxiliaryG m).natDegree = m - 1) :
    ((C lam * X + C nu) * modifiedNarayanaPolynomial (m - 1) +
        modifiedNarayanaPolynomial m).roots.sum ≤
      ((C lam * X + C nu) * FiniteSkewBoard.auxiliaryG (m - 1) +
        FiniteSkewBoard.auxiliaryG m).roots.sum := by
  by_cases hm2 : m = 2
  · subst m
    exact theorem41Claim7_modified_roots_sum_le_two hlam hnu
      hU_split hV_split hUdeg hVdeg
  · exact theorem41Claim7_modified_roots_sum_le_of_recurrence_of_three_le
      hrec2 (by lia) hlam hnu hU_split hV_split hUdeg hVdeg

/-- Section 3 provider for the root-sum field in the corrected Claim `(7)`
bundle. Lemma 3.4 supplies splitting of `U`, while the existing degree-gap
field determines the absolute degree of `V`. -/
theorem modifiedNarayanaPencil_natDegree {m : ℕ} {lam nu : ℝ} (hm : 1 ≤ m)
    (hlam : 0 ≤ lam) :
    ((C lam * X + C nu) * modifiedNarayanaPolynomial (m - 1) +
      modifiedNarayanaPolynomial m).natDegree = m := by
  have hfac : (C lam * X + C nu : ℝ[X]).natDegree ≤ 1 := by
    have hlin : (C lam * X : ℝ[X]).natDegree ≤ 1 := by
      calc
        _ ≤ (C lam : ℝ[X]).natDegree + (X : ℝ[X]).natDegree := natDegree_mul_le
        _ ≤ 1 := by simp
    calc
      _ ≤ max (C lam * X : ℝ[X]).natDegree (C nu : ℝ[X]).natDegree :=
        natDegree_add_le _ _
      _ ≤ 1 := max_le hlin (by simp)
  have hprod :
      ((C lam * X + C nu) * modifiedNarayanaPolynomial (m - 1)).natDegree ≤ m := by
    calc
      _ ≤ (C lam * X + C nu : ℝ[X]).natDegree +
          (modifiedNarayanaPolynomial (m - 1)).natDegree := natDegree_mul_le
      _ ≤ 1 + (m - 1) := by
        exact Nat.add_le_add hfac (by
          rw [modifiedNarayanaPolynomial_natDegree])
      _ = m := by lia
  have hle :
      ((C lam * X + C nu) * modifiedNarayanaPolynomial (m - 1) +
        modifiedNarayanaPolynomial m).natDegree ≤ m := by
    apply (natDegree_add_le _ _).trans
    rw [modifiedNarayanaPolynomial_natDegree]
    exact max_le hprod le_rfl
  apply natDegree_eq_of_le_of_coeff_ne_zero hle
  have hPprevLead : (modifiedNarayanaPolynomial (m - 1)).coeff (m - 1) = 1 := by
    calc
      _ = (modifiedNarayanaPolynomial (m - 1)).coeff
          (modifiedNarayanaPolynomial (m - 1)).natDegree := by
            rw [modifiedNarayanaPolynomial_natDegree]
      _ = (modifiedNarayanaPolynomial (m - 1)).leadingCoeff := coeff_natDegree
      _ = 1 := modifiedNarayanaPolynomial_leadingCoeff (m - 1)
  have hPprevAbove : (modifiedNarayanaPolynomial (m - 1)).coeff m = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [modifiedNarayanaPolynomial_natDegree]
    lia
  have hPmLead : (modifiedNarayanaPolynomial m).coeff m = 1 := by
    calc
      _ = (modifiedNarayanaPolynomial m).coeff (modifiedNarayanaPolynomial m).natDegree := by
        rw [modifiedNarayanaPolynomial_natDegree]
      _ = (modifiedNarayanaPolynomial m).leadingCoeff := coeff_natDegree
      _ = 1 := modifiedNarayanaPolynomial_leadingCoeff m
  have hXPprevLead : (X * modifiedNarayanaPolynomial (m - 1)).coeff m = 1 := by
    rw [show m = (m - 1) + 1 by exact (Nat.sub_add_cancel hm).symm, coeff_X_mul]
    exact hPprevLead
  rw [show (C lam * X + C nu) * modifiedNarayanaPolynomial (m - 1) =
      C lam * (X * modifiedNarayanaPolynomial (m - 1)) +
        C nu * modifiedNarayanaPolynomial (m - 1) by ring]
  simp only [coeff_add, coeff_C_mul]
  rw [hXPprevLead, hPprevAbove, hPmLead]
  linarith

theorem theorem41Claim7_modified_u_v_roots_sum_of_section3
    (hrec2 :
      NarayanaAuxiliaryGRecurrenceStatement
        modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG)
    (h34 : Lemma34ModifiedNarayanaInterlacingStatement
      modifiedNarayanaPolynomial)
    (hV_split :
      ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → 0 ≤ lam → -1 ≤ nu →
        ((C lam * X + C nu) * FiniteSkewBoard.auxiliaryG (m - 1) +
          FiniteSkewBoard.auxiliaryG m).Splits)
    (hUdeg :
      ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → 0 ≤ lam → -1 ≤ nu →
        ((C lam * X + C nu) * modifiedNarayanaPolynomial (m - 1) +
          modifiedNarayanaPolynomial m).natDegree = m)
    (hdeg_VU :
      ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → 0 ≤ lam → -1 ≤ nu →
        ((C lam * X + C nu) * FiniteSkewBoard.auxiliaryG (m - 1) +
          FiniteSkewBoard.auxiliaryG m).natDegree + 1 =
            ((C lam * X + C nu) * modifiedNarayanaPolynomial (m - 1) +
              modifiedNarayanaPolynomial m).natDegree) :
    ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → 0 ≤ lam → -1 ≤ nu →
      ((C lam * X + C nu) * modifiedNarayanaPolynomial (m - 1) +
          modifiedNarayanaPolynomial m).roots.sum ≤
        ((C lam * X + C nu) * FiniteSkewBoard.auxiliaryG (m - 1) +
          FiniteSkewBoard.auxiliaryG m).roots.sum := by
  intro m lam nu hm hlam hnu
  have hU_split :
      ((C lam * X + C nu) * modifiedNarayanaPolynomial (m - 1) +
        modifiedNarayanaPolynomial m).Splits :=
    (h34 (m := m) (lam := lam) (nu := nu) hm hlam hnu).1.2
  have hUdeg' := hUdeg hm hlam hnu
  have hVdeg' :
      ((C lam * X + C nu) * FiniteSkewBoard.auxiliaryG (m - 1) +
        FiniteSkewBoard.auxiliaryG m).natDegree = m - 1 := by
    have hgap := hdeg_VU hm hlam hnu
    lia
  exact theorem41Claim7_modified_roots_sum_le_of_recurrence hrec2
    hm hlam hnu hU_split (hV_split hm hlam hnu) hUdeg' hVdeg'

/-- Boundary polynomial showing that the strict negative `U`-root bound in the
current Claim `(7)` side-condition bundle cannot be discharged uniformly at
`ν = -1`. -/
theorem theorem41Claim7_modified_left_boundary_eq :
    (C (0 : ℝ) * X + C (-1 : ℝ)) * modifiedNarayanaPolynomial (2 - 1) +
        modifiedNarayanaPolynomial 2 =
      -X + C (3 : ℝ) * X + X ^ 2 := by
  norm_num [modifiedNarayanaPolynomial_one, modifiedNarayanaPolynomial_two]
  ring_nf

/-- In the boundary case `m = 2`, `λ = 0`, `ν = -1`, the left polynomial
`U = (λ X + ν) P_{m-1} + P_m` has zero as a root. -/
theorem theorem41Claim7_modified_left_boundary_isRoot_zero :
    ((C (0 : ℝ) * X + C (-1 : ℝ)) * modifiedNarayanaPolynomial (2 - 1) +
        modifiedNarayanaPolynomial 2).IsRoot 0 := by
  rw [theorem41Claim7_modified_left_boundary_eq, Polynomial.IsRoot.def]
  simp

/-- The strict negative upper bound requested by the current Claim `(7)` side
condition fails for the modified Narayana boundary case `λ = 0`, `ν = -1`. -/
theorem theorem41Claim7_modified_left_boundary_not_strictRootBound :
    ¬ ∃ c : ℝ,
      (∀ s ∈ (((C (0 : ℝ) * X + C (-1 : ℝ)) *
        modifiedNarayanaPolynomial (2 - 1) + modifiedNarayanaPolynomial 2).roots),
          s ≤ c) ∧ c < 0 := by
  rintro ⟨c, hle, hc⟩
  have hpoly_ne : -X + C (3 : ℝ) * X + X ^ 2 ≠ 0 := by
    intro h
    have heval := congr_arg (fun p : ℝ[X] => p.eval 1) h
    norm_num at heval
  have hboundary_ne :
      (C (0 : ℝ) * X + C (-1 : ℝ)) *
          modifiedNarayanaPolynomial (2 - 1) + modifiedNarayanaPolynomial 2 ≠
        0 := by
    rw [theorem41Claim7_modified_left_boundary_eq]
    exact hpoly_ne
  have hzero_mem :
      (0 : ℝ) ∈ (((C (0 : ℝ) * X + C (-1 : ℝ)) *
        modifiedNarayanaPolynomial (2 - 1) + modifiedNarayanaPolynomial 2).roots) :=
    (Polynomial.mem_roots hboundary_ne).mpr
      theorem41Claim7_modified_left_boundary_isRoot_zero
  have hzero_le : (0 : ℝ) ≤ c := hle 0 hzero_mem
  linarith

/-- Consequently, the current bundled Claim `(7)` side-condition interface is
not satisfiable by the concrete modified-Narayana / auxiliary-`G` data.  The
endpoint `ν = -1` needs a refined conversion route instead of a uniform strict
negative bound on the roots of `U`. -/
theorem not_theorem41Claim7SideConditions_modified_auxiliaryG :
    ¬ Theorem41Claim7SideConditions
      modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG := by
  intro hside
  exact theorem41Claim7_modified_left_boundary_not_strictRootBound
    (hside.u_bound (m := 2) (lam := 0) (nu := -1)
      (by norm_num) (by norm_num) (by norm_num))

end GeneralizedSnakePosets
end RealRooted
