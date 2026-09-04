import RealRooted.GeneralizedSnakePosets.Narayana.RootSums

/-!
# Endpoint-safe Braun--Jal Claim 7 bridge

This module supplies concrete pencil degrees and leading coefficients, derives
auxiliary-pencil splitness and nonpositive roots, and packages the endpoint-safe
root-sum orientation as Braun--Jal Claim 7.
-/

open Polynomial Filter

noncomputable section

namespace RealRooted
namespace GeneralizedSnakePosets

theorem theorem41Claim7_modified_u_v_roots_sum_of_section3_concrete_u_degree
    (hrec2 : NarayanaAuxiliaryGRecurrenceStatement
      modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG)
    (h34 : Lemma34ModifiedNarayanaInterlacingStatement modifiedNarayanaPolynomial)
    (hV_split : ∀ {m : ℕ} {lam nu : ℝ},
      2 ≤ m → 0 ≤ lam → -1 ≤ nu →
        ((C lam * X + C nu) * FiniteSkewBoard.auxiliaryG (m - 1) +
          FiniteSkewBoard.auxiliaryG m).Splits)
    (hdeg_VU : ∀ {m : ℕ} {lam nu : ℝ},
      2 ≤ m → 0 ≤ lam → -1 ≤ nu →
        ((C lam * X + C nu) * FiniteSkewBoard.auxiliaryG (m - 1) +
            FiniteSkewBoard.auxiliaryG m).natDegree + 1 =
          ((C lam * X + C nu) * modifiedNarayanaPolynomial (m - 1) +
            modifiedNarayanaPolynomial m).natDegree)
    {m : ℕ} {lam nu : ℝ} (hm : 2 ≤ m) (hlam : 0 ≤ lam) (hnu : -1 ≤ nu) :
    ((C lam * X + C nu) * modifiedNarayanaPolynomial (m - 1) +
        modifiedNarayanaPolynomial m).roots.sum ≤
      ((C lam * X + C nu) * FiniteSkewBoard.auxiliaryG (m - 1) +
        FiniteSkewBoard.auxiliaryG m).roots.sum := by
  apply theorem41Claim7_modified_u_v_roots_sum_of_section3 hrec2 h34 hV_split
    (fun hm' hlam' _ => modifiedNarayanaPencil_natDegree (by lia) hlam') hdeg_VU
    hm hlam hnu

theorem theorem41Claim7_modified_u_v_roots_sum_of_section3_concrete_degrees
    (hrec2 : NarayanaAuxiliaryGRecurrenceStatement
      modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG)
    (h34 : Lemma34ModifiedNarayanaInterlacingStatement modifiedNarayanaPolynomial)
    (hV_split : ∀ {m : ℕ} {lam nu : ℝ},
      2 ≤ m → 0 ≤ lam → -1 ≤ nu →
        ((C lam * X + C nu) * FiniteSkewBoard.auxiliaryG (m - 1) +
          FiniteSkewBoard.auxiliaryG m).Splits)
    {m : ℕ} {lam nu : ℝ} (hm : 2 ≤ m) (hlam : 0 ≤ lam) (hnu : -1 ≤ nu) :
    ((C lam * X + C nu) * modifiedNarayanaPolynomial (m - 1) +
        modifiedNarayanaPolynomial m).roots.sum ≤
      ((C lam * X + C nu) * FiniteSkewBoard.auxiliaryG (m - 1) +
        FiniteSkewBoard.auxiliaryG m).roots.sum := by
  apply theorem41Claim7_modified_u_v_roots_sum_of_section3_concrete_u_degree
    hrec2 h34 hV_split
  · intro m' lam' nu' hm' hlam' _
    rw [auxiliaryGPencil_natDegree_of_narayanaRecurrence hrec2 hm' hlam',
      modifiedNarayanaPencil_natDegree (by lia) hlam']
    lia
  · exact hm
  · exact hlam
  · exact hnu

theorem modifiedNarayanaPencil_leadingCoeff {m : ℕ} {lam nu : ℝ}
    (hm : 1 ≤ m) (hlam : 0 ≤ lam) :
    ((C lam * X + C nu) * modifiedNarayanaPolynomial (m - 1) +
      modifiedNarayanaPolynomial m).leadingCoeff = lam + 1 := by
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
      _ = (modifiedNarayanaPolynomial m).coeff
          (modifiedNarayanaPolynomial m).natDegree := by rw [modifiedNarayanaPolynomial_natDegree]
      _ = (modifiedNarayanaPolynomial m).leadingCoeff := coeff_natDegree
      _ = 1 := modifiedNarayanaPolynomial_leadingCoeff m
  have hXPprevLead : (X * modifiedNarayanaPolynomial (m - 1)).coeff m = 1 := by
    have hindex : (m - 1) + 1 = m := Nat.sub_add_cancel hm
    calc
      _ = (modifiedNarayanaPolynomial (m - 1)).coeff (m - 1) := by
        simpa only [hindex] using
          (coeff_X_mul (p := modifiedNarayanaPolynomial (m - 1)) (n := m - 1))
      _ = 1 := hPprevLead
  rw [← coeff_natDegree, modifiedNarayanaPencil_natDegree hm hlam]
  rw [show
      (C lam * X + C nu) * modifiedNarayanaPolynomial (m - 1) =
        C lam * (X * modifiedNarayanaPolynomial (m - 1)) +
          C nu * modifiedNarayanaPolynomial (m - 1) by ring]
  simp only [coeff_add, coeff_C_mul]
  rw [hXPprevLead, hPprevAbove, hPmLead]
  ring

theorem auxiliaryGPencil_leadingCoeff_of_narayanaRecurrence
    (hrec2 : NarayanaAuxiliaryGRecurrenceStatement
      modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG)
    {m : ℕ} {lam nu : ℝ} (hm : 2 ≤ m) (hlam : 0 ≤ lam) :
    ((C lam * X + C nu) * FiniteSkewBoard.auxiliaryG (m - 1) +
      FiniteSkewBoard.auxiliaryG m).leadingCoeff =
        lam * ((m - 1 : ℕ) : ℝ) + (m : ℝ) := by
  have hGprev_top :
      (FiniteSkewBoard.auxiliaryG (m - 1)).coeff (m - 2) =
        ((m - 1 : ℕ) : ℝ) := by
    simpa only [show m - 1 - 1 = m - 2 by lia] using
      auxiliaryG_coeff_sub_one_of_narayanaRecurrence hrec2 (m - 1) (by lia)
  have hXGprev_top :
      (X * FiniteSkewBoard.auxiliaryG (m - 1)).coeff (m - 1) =
        ((m - 1 : ℕ) : ℝ) := by
    have hindex : (m - 2) + 1 = m - 1 := by lia
    calc
      _ = (FiniteSkewBoard.auxiliaryG (m - 1)).coeff (m - 2) := by
        simpa only [hindex] using
          (coeff_X_mul (p := FiniteSkewBoard.auxiliaryG (m - 1)) (n := m - 2))
      _ = ((m - 1 : ℕ) : ℝ) := hGprev_top
  have hGprev_above :
      (FiniteSkewBoard.auxiliaryG (m - 1)).coeff (m - 1) = 0 :=
    auxiliaryG_coeff_self_of_narayanaRecurrence hrec2 (m - 1)
  have hGm_top :
      (FiniteSkewBoard.auxiliaryG m).coeff (m - 1) = m :=
    auxiliaryG_coeff_sub_one_of_narayanaRecurrence hrec2 m (by lia)
  rw [← coeff_natDegree,
    auxiliaryGPencil_natDegree_of_narayanaRecurrence hrec2 hm hlam]
  rw [show
      (C lam * X + C nu) * FiniteSkewBoard.auxiliaryG (m - 1) =
        C lam * (X * FiniteSkewBoard.auxiliaryG (m - 1)) +
          C nu * FiniteSkewBoard.auxiliaryG (m - 1) by ring]
  simp only [coeff_add, coeff_C_mul]
  rw [hXGprev_top, hGprev_above, hGm_top]
  ring

/-- The section 3 recurrence gives the auxiliary Braun--Jal pencil a positive
leading coefficient throughout the parameter range used in section 4. -/
theorem auxiliaryGPencil_hasPosLeadingCoeff_of_narayanaRecurrence
    (hrec2 : NarayanaAuxiliaryGRecurrenceStatement
      modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG)
    {m : ℕ} {lam nu : ℝ} (hm : 2 ≤ m) (hlam : 0 ≤ lam) :
    HasPosLeadingCoeff
      ((C lam * X + C nu) * FiniteSkewBoard.auxiliaryG (m - 1) +
        FiniteSkewBoard.auxiliaryG m) := by
  unfold HasPosLeadingCoeff
  rw [auxiliaryGPencil_leadingCoeff_of_narayanaRecurrence hrec2 hm hlam]
  positivity

/-- The two summands in the middle polynomial of Braun--Jal Claim `(7)` have
the same degree and positive leading coefficient. -/
theorem theorem41Claim7_modified_middle_hasPosLeadingCoeff
    (hrec2 : NarayanaAuxiliaryGRecurrenceStatement
      modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG)
    {m : ℕ} {lam nu : ℝ} (hm : 2 ≤ m) (hlam : 0 ≤ lam)
    (hnu : -1 ≤ nu) :
    HasPosLeadingCoeff
      (((C lam * X + C nu) * modifiedNarayanaPolynomial (m - 1) +
          modifiedNarayanaPolynomial m) +
        X * ((C lam * X + C nu) * FiniteSkewBoard.auxiliaryG (m - 1) +
          FiniteSkewBoard.auxiliaryG m)) := by
  have hV_pos :=
    auxiliaryGPencil_hasPosLeadingCoeff_of_narayanaRecurrence
      (nu := nu) hrec2 hm hlam
  apply hasPosLeadingCoeff_add_of_same_natDegree
  · rw [lemma34ModifiedNarayana_left_natDegree (by lia) hlam hnu,
      Polynomial.natDegree_X_mul hV_pos.ne_zero,
      auxiliaryGPencil_natDegree_of_narayanaRecurrence hrec2 hm hlam]
    lia
  · exact lemma34ModifiedNarayana_left_posLeadingCoeff (by lia) hlam hnu
  · exact hV_pos.X_mul

/-- Equation `(2)` and Lemma 3.4 imply that the auxiliary pencil splits,
before the root-sum comparison used to orient Claim `(7)`.

The parameter `h34` is explicit because this lower-level module cannot import
the later Turan module, where
`lemma34ModifiedNarayanaInterlacing_modified` proves the full parameterized
statement. -/
theorem auxiliaryGPencil_splits_of_section3
    (hrec2 : NarayanaAuxiliaryGRecurrenceStatement
      modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG)
    (h34 : Lemma34ModifiedNarayanaInterlacingStatement
      modifiedNarayanaPolynomial)
    {m : ℕ} {lam nu : ℝ} (hm : 2 ≤ m) (hlam : 0 ≤ lam)
    (hnu : -1 ≤ nu) :
    ((C lam * X + C nu) * FiniteSkewBoard.auxiliaryG (m - 1) +
      FiniteSkewBoard.auxiliaryG m).Splits := by
  let U : ℝ[X] :=
    (C lam * X + C nu) * modifiedNarayanaPolynomial (m - 1) +
      modifiedNarayanaPolynomial m
  let V : ℝ[X] :=
    (C lam * X + C nu) * FiniteSkewBoard.auxiliaryG (m - 1) +
      FiniteSkewBoard.auxiliaryG m
  let W : ℝ[X] :=
    (C lam * X + C nu) * modifiedNarayanaPolynomial m +
      modifiedNarayanaPolynomial (m + 1)
  have hUW : Prec U W := by simpa [U, W] using h34 (m := m) (lam := lam) (nu := nu) hm hlam hnu
  have hW_eq : W = (1 + X) * U + X * V := by
    simpa [U, V, W] using
      theorem41Claim7_next_eq_of_narayanaAuxiliaryGRecurrence
        hrec2 hm lam nu
  have hW_pos : HasPosLeadingCoeff W := by
    simpa [W] using
      lemma34ModifiedNarayana_right_posLeadingCoeff (m := m) hlam hnu
  have hWU_lc : W.leadingCoeff = U.leadingCoeff := by
    calc
      W.leadingCoeff = lam + 1 := by
        simpa [W] using modifiedNarayanaPencil_leadingCoeff
          (m := m + 1) (nu := nu) (by lia) hlam
      _ = U.leadingCoeff := by
        symm
        simpa [U] using modifiedNarayanaPencil_leadingCoeff
          (m := m) (nu := nu) (by lia) hlam
  have hdeg_UW : U.natDegree + 1 = W.natDegree := by
    rw [show U.natDegree = m by
        simpa [U] using modifiedNarayanaPencil_natDegree
          (m := m) (nu := nu) (by lia) hlam,
      show W.natDegree = m + 1 by
        simpa [W] using modifiedNarayanaPencil_natDegree
          (m := m + 1) (nu := nu) (by lia) hlam]
  have hW_nonpos : ∀ r ∈ W.roots, r ≤ 0 := by
    simpa [W] using
      lemma34ModifiedNarayana_right_roots_nonpos (m := m) hlam hnu
  have hU_nonpos : ∀ r ∈ U.roots, r ≤ 0 := by
    simpa [U] using
      lemma34ModifiedNarayana_left_roots_nonpos (m := m) (by lia) hlam hnu
  have hmid_pos : HasPosLeadingCoeff (U + X * V) := by
    simpa [U, V] using
      theorem41Claim7_modified_middle_hasPosLeadingCoeff hrec2 hm hlam hnu
  have hmid_eq : W - X * U = U + X * V := by
    rw [hW_eq]
    ring
  have hpair : Prec U (W - X * U) ∧ Prec (W - X * U) W :=
    prec_sub_X_mul_pair_of_eq_posLeadingCoeff hUW hW_pos hWU_lc hdeg_UW
      hW_nonpos hU_nonpos (by simpa [hmid_eq] using hmid_pos)
  have hU_mid : Prec U (U + X * V) := by simpa [hmid_eq] using hpair.left
  have hall_U_mid := allComboRealRooted_of_prec hU_mid
  have hall_U_XV : AllComboRealRooted U (X * V) := by
    intro alpha beta
    have hsplit := hall_U_mid (alpha - beta) beta
    rw [show
        C alpha * U + C beta * (X * V) =
          C (alpha - beta) * U + C beta * (U + X * V) by
      rw [map_sub]
      ring]
    exact hsplit
  have hXV_split : (X * V).Splits := by simpa using hall_U_XV 0 1
  simpa [V] using Polynomial.splits_X_mul.mp hXV_split

/-- Convert the combinatorial nonnegativity of the auxiliary difference into
nonnegativity of the Braun--Jal pencil.

The hypothesis `hH_nonneg` is intentionally explicit. In Braun--Jal's
Section 4, `H_n = G_n - G_(n-1)` comes from the non-nesting-rook
interpretation used in the matrix recurrence, so its coefficient
nonnegativity is a combinatorial input. The present theorem is scoped to the
analytic consequence of that input and does not formalize the underlying rook
model or claim that input has been proved in Lean. -/
theorem auxiliaryGPencil_hasNonnegCoeffs_of_difference
    (hH_nonneg : ∀ n : ℕ, 1 ≤ n →
      HasNonnegCoeffs
        (FiniteSkewBoard.auxiliaryG n - FiniteSkewBoard.auxiliaryG (n - 1)))
    {m : ℕ} {lam nu : ℝ} (hm : 2 ≤ m) (hlam : 0 ≤ lam) (hnu : -1 ≤ nu) :
    HasNonnegCoeffs
      ((C lam * X + C nu) * FiniteSkewBoard.auxiliaryG (m - 1) +
        FiniteSkewBoard.auxiliaryG m) := by
  have hnu_one : 0 ≤ nu + 1 := by linarith
  have hlam_term :
      HasNonnegCoeffs
        (C lam * (X * FiniteSkewBoard.auxiliaryG (m - 1))) :=
    nonnegCoeffs_C_mul hlam
      (FiniteSkewBoard.auxiliaryG_hasNonnegCoeffs (m - 1)).X_mul
  have hnu_term :
      HasNonnegCoeffs
        (C (nu + 1) * FiniteSkewBoard.auxiliaryG (m - 1)) :=
    nonnegCoeffs_C_mul hnu_one
      (FiniteSkewBoard.auxiliaryG_hasNonnegCoeffs (m - 1))
  rw [show
      (C lam * X + C nu) * FiniteSkewBoard.auxiliaryG (m - 1) +
          FiniteSkewBoard.auxiliaryG m =
        C lam * (X * FiniteSkewBoard.auxiliaryG (m - 1)) +
          C (nu + 1) * FiniteSkewBoard.auxiliaryG (m - 1) +
            (FiniteSkewBoard.auxiliaryG m -
              FiniteSkewBoard.auxiliaryG (m - 1)) by
          simp only [map_add, map_one]
          ring]
  exact (hlam_term.add hnu_term).add (hH_nonneg m (by lia))

/-- The explicit combinatorial difference input rules out positive real roots
of the auxiliary Braun--Jal pencil. -/
theorem auxiliaryGPencil_roots_nonpos_of_difference
    (hH_nonneg : ∀ n : ℕ, 1 ≤ n →
      HasNonnegCoeffs
        (FiniteSkewBoard.auxiliaryG n - FiniteSkewBoard.auxiliaryG (n - 1)))
    {m : ℕ} {lam nu : ℝ} (hm : 2 ≤ m) (hlam : 0 ≤ lam) (hnu : -1 ≤ nu) :
    ∀ r ∈ (((C lam * X + C nu) * FiniteSkewBoard.auxiliaryG (m - 1) +
      FiniteSkewBoard.auxiliaryG m).roots), r ≤ 0 :=
  roots_nonpos_of_hasNonnegCoeffs
    (auxiliaryGPencil_hasNonnegCoeffs_of_difference hH_nonneg hm hlam hnu)

/-- Braun--Jal Claim `(7)` for the concrete modified Narayana family, using
the endpoint-safe root-sum orientation.

The analytic Lemma 3.4 input `h34` is explicit only because this lower-level
module cannot import the later Turan module, where it is proved. The
coefficientwise hypothesis `hH_nonneg` is different: as explained at
`auxiliaryGPencil_hasNonnegCoeffs_of_difference`, it is the permitted
combinatorial input from the non-nesting-rook interpretation, whose full model
is intentionally outside the scope of this formalization. -/
theorem theorem41Claim7_modified_of_section3
    (hrec2 : NarayanaAuxiliaryGRecurrenceStatement
      modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG)
    (h34 : Lemma34ModifiedNarayanaInterlacingStatement
      modifiedNarayanaPolynomial)
    (hH_nonneg : ∀ n : ℕ, 1 ≤ n →
      HasNonnegCoeffs
        (FiniteSkewBoard.auxiliaryG n -
          FiniteSkewBoard.auxiliaryG (n - 1))) :
    Theorem41Claim7Statement
      modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG := by
  have hV_split :
      ∀ {m : ℕ} {lam nu : ℝ}, 2 ≤ m → 0 ≤ lam → -1 ≤ nu →
        ((C lam * X + C nu) * FiniteSkewBoard.auxiliaryG (m - 1) +
          FiniteSkewBoard.auxiliaryG m).Splits := by
    intro m lam nu hm hlam hnu
    exact auxiliaryGPencil_splits_of_section3 hrec2 h34 hm hlam hnu
  apply theorem41Claim7_of_section3_rootSumSideConditions hrec2 h34
  refine {
    w_pos := ?_
    wu_lc := ?_
    deg_uw := ?_
    w_nonpos := ?_
    u_nonpos := ?_
    mid_pos := ?_
    v_pos := ?_
    v_nonpos := ?_
    deg_vu := ?_
    u_v_roots_sum := ?_ }
  · intro m lam nu hm hlam hnu
    exact lemma34ModifiedNarayana_right_posLeadingCoeff hlam hnu
  · intro m lam nu hm hlam hnu
    calc
      ((C lam * X + C nu) * modifiedNarayanaPolynomial m +
          modifiedNarayanaPolynomial (m + 1)).leadingCoeff = lam + 1 := by
        simpa using modifiedNarayanaPencil_leadingCoeff
          (m := m + 1) (nu := nu) (by lia) hlam
      _ = ((C lam * X + C nu) * modifiedNarayanaPolynomial (m - 1) +
          modifiedNarayanaPolynomial m).leadingCoeff := by
        symm
        exact modifiedNarayanaPencil_leadingCoeff
          (m := m) (nu := nu) (by lia) hlam
  · intro m lam nu hm hlam hnu
    have hUdeg := modifiedNarayanaPencil_natDegree
      (m := m) (nu := nu) (by lia) hlam
    have hWdeg :
        ((C lam * X + C nu) * modifiedNarayanaPolynomial m +
          modifiedNarayanaPolynomial (m + 1)).natDegree = m + 1 := by
      simpa using modifiedNarayanaPencil_natDegree
        (m := m + 1) (nu := nu) (by lia) hlam
    rw [hUdeg, hWdeg]
  · intro m lam nu hm hlam hnu
    exact lemma34ModifiedNarayana_right_roots_nonpos hlam hnu
  · intro m lam nu hm hlam hnu
    exact lemma34ModifiedNarayana_left_roots_nonpos (by lia) hlam hnu
  · intro m lam nu hm hlam hnu
    exact theorem41Claim7_modified_middle_hasPosLeadingCoeff
      hrec2 hm hlam hnu
  · intro m lam nu hm hlam hnu
    exact auxiliaryGPencil_hasPosLeadingCoeff_of_narayanaRecurrence
      (nu := nu) hrec2 hm hlam
  · intro m lam nu hm hlam hnu
    exact auxiliaryGPencil_roots_nonpos_of_difference
      hH_nonneg hm hlam hnu
  · intro m lam nu hm hlam hnu
    rw [auxiliaryGPencil_natDegree_of_narayanaRecurrence hrec2 hm hlam,
      modifiedNarayanaPencil_natDegree
        (m := m) (nu := nu) (by lia) hlam]
    lia
  · intro m lam nu hm hlam hnu
    exact theorem41Claim7_modified_u_v_roots_sum_of_section3_concrete_degrees
      hrec2 h34 hV_split hm hlam hnu

end GeneralizedSnakePosets
end RealRooted
