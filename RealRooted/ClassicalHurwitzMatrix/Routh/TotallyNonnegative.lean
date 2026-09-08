import RealRooted.ClassicalHurwitzMatrix.Routh
import RealRooted.Mathlib.LinearAlgebra.Matrix.TotallyNonneg

/-!
# Total nonnegativity under a Routh expansion

This file proves the finite-minor statement behind the row-finite `J(c)`
action used in one algebraic Routh step.
-/

namespace Matrix

private def routhChoiceRow (row : ℕ) (choice : Bool) : ℕ :=
  if row % 2 = 0 ∧ choice = true then row else row + 1

private lemma le_routhChoiceRow (row : ℕ) (choice : Bool) :
    row ≤ routhChoiceRow row choice := by
  unfold routhChoiceRow
  split_ifs <;> lia

private lemma routhChoiceRow_le_add_one (row : ℕ) (choice : Bool) :
    routhChoiceRow row choice ≤ row + 1 := by
  unfold routhChoiceRow
  split_ifs <;> lia

private def routhExtendChoices (k : ℕ) (choices : Fin k → Bool)
    (value : Bool) (i : Fin (k + 1)) : Bool :=
  if h : (i : ℕ) < k then choices ⟨i, h⟩ else value

private def routhHybrid {n : ℕ} (rows cols : Fin n → ℕ)
    (M : Matrix ℕ ℕ ℝ) (c : ℝ) (k : ℕ) (choices : Fin k → Bool) :
    Matrix (Fin n) (Fin n) ℝ :=
  .of fun i j ↦
    if h : (i : ℕ) < k then
      M (routhChoiceRow (rows i) (choices ⟨i, h⟩)) (cols j)
    else
      routhExpand c M (rows i) (cols j)

private lemma routhHybrid_nonneg_aux {n : ℕ} (rows cols : Fin n → ℕ)
    (hrows : StrictMono rows) (hcols : StrictMono cols)
    (M : Matrix ℕ ℕ ℝ) (hM : M.IsTotallyNonneg) (c : ℝ) (hc : 0 ≤ c)
    (d k : ℕ) (hk : k ≤ n) (hd : n - k = d) (choices : Fin k → Bool) :
    0 ≤ (routhHybrid rows cols M c k choices).det := by
  induction d generalizing n k choices with
  | zero =>
      have hkn : k = n := by lia
      subst k
      let rows' : Fin n → ℕ := fun i ↦ routhChoiceRow (rows i) (choices i)
      have h_eq : routhHybrid rows cols M c n choices = M.submatrix rows' cols := by
        ext i j
        simp [routhHybrid, rows']
      rw [h_eq]
      have hmono : Monotone rows' := by
        intro i j hij
        by_cases heq : i = j
        · simp_all
        · have hij' : i < j := lt_of_le_of_ne hij heq
          have hrows_lt := hrows hij'
          exact (routhChoiceRow_le_add_one _ _).trans <|
            (Nat.add_one_le_iff.mpr hrows_lt).trans (le_routhChoiceRow _ _)
      by_cases hinj : Function.Injective rows'
      · have hstrict : StrictMono rows' := hmono.strictMono_of_injective hinj
        exact hM hstrict hcols
      · unfold Function.Injective at hinj
        push Not at hinj
        rcases hinj with ⟨i, j, heq, hne⟩
        have hrow_eq : (M.submatrix rows' cols) i =
            (M.submatrix rows' cols) j := by
          ext q
          simp [heq]
        exact det_zero_of_row_eq hne hrow_eq |>.ge
  | succ d ih =>
      have hk_lt : k < n := by lia
      by_cases heven : rows ⟨k, hk_lt⟩ % 2 = 0
      · let choicesCurrent := routhExtendChoices k choices true
        let choicesNext := routhExtendChoices k choices false
        let B := routhHybrid rows cols M c (k + 1) choicesCurrent
        let C := routhHybrid rows cols M c (k + 1) choicesNext
        have hdk : n - (k + 1) = d := by lia
        have hB_nonneg : 0 ≤ B.det :=
          ih rows cols hrows hcols (k + 1) (by lia) hdk choicesCurrent
        have hC_nonneg : 0 ≤ C.det :=
          ih rows cols hrows hcols (k + 1) (by lia) hdk choicesNext
        have h_update : routhHybrid rows cols M c k choices =
            updateRow C ⟨k, hk_lt⟩
              (c • B ⟨k, hk_lt⟩ + C ⟨k, hk_lt⟩) := by
          ext i j
          by_cases hik : i = ⟨k, hk_lt⟩
          · subst i
            simp [routhHybrid, B, C, choicesCurrent, choicesNext,
              routhExtendChoices, routhChoiceRow, routhExpand, heven]
          · have hik' : (i : ℕ) ≠ k := fun h ↦ hik (Fin.ext h)
            simp only [updateRow_ne hik]
            by_cases hi : (i : ℕ) < k
            · simp [routhHybrid, C, choicesNext, routhExtendChoices, hi]
              grind
            · have hki : k < (i : ℕ) := by lia
              simp [routhHybrid, C, choicesNext, routhExtendChoices, hi]
              grind
        rw [h_update, det_updateRow_add, det_updateRow_smul]
        have hB_eq : updateRow C ⟨k, hk_lt⟩ (B ⟨k, hk_lt⟩) = B := by
          ext i j
          by_cases hik : i = ⟨k, hk_lt⟩
          · simp_all
          · have hik' : (i : ℕ) ≠ k := fun h ↦ hik (Fin.ext h)
            rw [updateRow_ne hik]
            by_cases hi : (i : ℕ) < k
            · simp [B, C, routhHybrid, choicesCurrent, choicesNext,
                routhExtendChoices, hi]
            · have hki : k < (i : ℕ) := by lia
              simp [B, C, routhHybrid, choicesCurrent, choicesNext,
                routhExtendChoices, hi]
              grind
        have hC_eq : updateRow C ⟨k, hk_lt⟩ (C ⟨k, hk_lt⟩) = C :=
          updateRow_eq_self C ⟨k, hk_lt⟩
        simpa [hB_eq, hC_eq] using
          add_nonneg (mul_nonneg hc hB_nonneg) hC_nonneg
      · let choicesNext := routhExtendChoices k choices false
        have hdk : n - (k + 1) = d := by lia
        have hnext := ih rows cols hrows hcols (k + 1) (by lia) hdk choicesNext
        have h_eq : routhHybrid rows cols M c k choices =
            routhHybrid rows cols M c (k + 1) choicesNext := by
          ext i j
          by_cases hik : i = ⟨k, hk_lt⟩
          · subst i
            simp [routhHybrid, choicesNext, routhExtendChoices,
              routhChoiceRow, routhExpand, heven]
          · have hik' : (i : ℕ) ≠ k := fun h ↦ hik (Fin.ext h)
            by_cases hi : (i : ℕ) < k
            · simp [routhHybrid, choicesNext, routhExtendChoices, hi]
              grind
            · have hki : k < (i : ℕ) := by lia
              simp [routhHybrid, choicesNext, routhExtendChoices, hi]
              grind
        rw [h_eq]
        exact hnext

/-- The row-finite Routh expansion preserves total nonnegativity when its
elimination coefficient is nonnegative. -/
protected theorem IsTotallyNonneg.routhExpand (hM : M.IsTotallyNonneg)
    (c : ℝ) (hc : 0 ≤ c) : (routhExpand c M).IsTotallyNonneg := by
  intro n rows cols hrows hcols
  have h_eq : (routhExpand c M).submatrix rows cols =
      routhHybrid rows cols M c 0 Fin.elim0 := by
    ext i j
    simp [routhHybrid]
  rw [h_eq]
  exact routhHybrid_nonneg_aux rows cols hrows hcols M hM c hc n 0
    (Nat.zero_le n) (Nat.sub_zero n) Fin.elim0

open RealRooted
open Polynomial

/-- A nonnegative Routh coefficient and total nonnegativity of the reduced
Hurwitz matrix imply total nonnegativity of the original Hurwitz matrix. -/
theorem IsTotallyNonneg.hurwitz_oddEvenPolynomial_of_routhReduced
    {c : ℝ} {odd even : ℝ[X]} (hM :
      (hurwitz (routhReducedPolynomial c odd even).coeff).IsTotallyNonneg)
    (hc : 0 ≤ c) (h0 : even.coeff 0 = c * odd.coeff 0) :
    (hurwitz (oddEvenPolynomial odd even).coeff).IsTotallyNonneg := by
  rw [hurwitz_oddEvenPolynomial_eq_routhExpand c odd even h0]
  exact hM.routhExpand c hc

/-- Ratio-specialized total-nonnegativity implication for a Routh step. -/
theorem IsTotallyNonneg.hurwitz_oddEvenPolynomial_of_routhReduced_ratio
    {odd even : ℝ[X]} (hM : IsTotallyNonneg
      (hurwitz (routhReducedPolynomial (routhCoefficient odd even) odd even).coeff))
    (hc : 0 ≤ routhCoefficient odd even) (hodd : odd.coeff 0 ≠ 0) :
    (hurwitz (oddEvenPolynomial odd even).coeff).IsTotallyNonneg := by
  rw [hurwitz_oddEvenPolynomial_eq_routhExpand_ratio odd even hodd]
  exact hM.routhExpand _ hc

/-- Positive constant coefficients supply the nonnegative multiplier required
by the ratio-specialized Routh step. -/
theorem IsTotallyNonneg.hurwitz_oddEvenPolynomial_of_routhReduced_of_pos
    {odd even : ℝ[X]} (hM : IsTotallyNonneg
      (hurwitz (routhReducedPolynomial (routhCoefficient odd even) odd even).coeff))
    (hodd : 0 < odd.coeff 0) (heven : 0 < even.coeff 0) :
    (hurwitz (oddEvenPolynomial odd even).coeff).IsTotallyNonneg :=
  hM.hurwitz_oddEvenPolynomial_of_routhReduced_ratio
    (routhCoefficient_pos hodd heven).le hodd.ne'

end Matrix
