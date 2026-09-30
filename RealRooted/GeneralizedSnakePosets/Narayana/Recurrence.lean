import RealRooted.Combinatorics.OrderedSubsetPairsNarayana
import RealRooted.GeneralizedSnakePosets.Narayana.JacobiTransport
import RealRooted.GeneralizedSnakePosets.TruncatedStaircase.FullStaircase

/-!
# Modified-Narayana recurrence and coefficient algebra

This module identifies full truncated-staircase rook polynomials with modified
Narayana polynomials, packages the checked finite recurrence cases, and derives
the auxiliary-polynomial coefficient and degree consequences of the all-rank
recurrence hypothesis.
-/

open Polynomial Filter

noncomputable section

namespace RealRooted
namespace GeneralizedSnakePosets

/-! ## Full truncated-staircase Narayana coefficients -/

/-- Size-`k` non-nesting placements in the full truncated staircase are counted
by the `m = 1` Narayana coefficient. -/
theorem FiniteSkewBoard.card_fullStaircasePlacements_eq_narayanaTransformCoeff_one
    (n k : ℕ) :
    (((FiniteSkewBoard.truncatedStaircase n n).nonNestingPlacements.filter
        fun P => P.card = k).card : ℝ) =
      narayanaTransformCoeff 1 n k := by
  rw [FiniteSkewBoard.card_fullStaircasePlacements_eq_orderedKSubsetPairs]
  exact Finset.card_orderedKSubsetPairs_eq_narayanaTransformCoeff_one n k

/-- The full truncated-staircase rook-polynomial coefficients are the
`m = 1` Narayana coefficients. -/
theorem FiniteSkewBoard.coeff_truncatedStaircaseRookPolynomial_full_eq_narayanaTransformCoeff_one
    (n k : ℕ) :
    (FiniteSkewBoard.truncatedStaircaseRookPolynomial n n).coeff k =
      narayanaTransformCoeff 1 n k := by
  rw [FiniteSkewBoard.truncatedStaircaseRookPolynomial,
    FiniteSkewBoard.rookPolynomial_coeff]
  exact FiniteSkewBoard.card_fullStaircasePlacements_eq_narayanaTransformCoeff_one n k

/-- The full truncated-staircase rook polynomial and the coefficient-side
modified Narayana polynomial have the same coefficients. -/
theorem FiniteSkewBoard.coeff_truncatedStaircaseRookPolynomial_full_eq_modifiedNarayanaCoeff
    (n k : ℕ) :
    (FiniteSkewBoard.truncatedStaircaseRookPolynomial n n).coeff k =
      (modifiedNarayanaCoeffPolynomial n).coeff k := by
  rw [FiniteSkewBoard.coeff_truncatedStaircaseRookPolynomial_full_eq_narayanaTransformCoeff_one,
    modifiedNarayanaCoeffPolynomial]
  by_cases hk : k ≤ n
  · rw [coeff_narayanaPolynomial_of_le (m := 1) hk]
  · have hklt : n < k := Nat.lt_of_not_ge hk
    rw [coeff_narayanaPolynomial_of_lt (m := 1) hklt,
      narayanaTransformCoeff_eq_zero_of_lt (m := 1) hklt]

/-- The full truncated-staircase rook polynomial is the modified Narayana
polynomial. -/
theorem FiniteSkewBoard.truncatedStaircaseRookPolynomial_full_eq_modifiedNarayanaPolynomial
    (n : ℕ) :
    FiniteSkewBoard.truncatedStaircaseRookPolynomial n n =
      modifiedNarayanaPolynomial n := by
  rw [modifiedNarayanaPolynomial_eq_coeffPolynomial]
  ext k
  exact
    FiniteSkewBoard.coeff_truncatedStaircaseRookPolynomial_full_eq_modifiedNarayanaCoeff
      n k

/-- Unconditional consecutive interlacing for the modified Narayana
family. -/
theorem modifiedNarayanaPolynomial_strictInterl_succ (n : ℕ) :
    StrictInterl (modifiedNarayanaPolynomial n) (modifiedNarayanaPolynomial (n + 1)) :=
  modifiedNarayanaPolynomial_strictInterl_succ_of_nonnegCoeffs n
    narayanaQuot_hasNonnegCoeffs

/-- Unconditional consecutive interlacing for the modified Narayana family. -/
theorem modifiedNarayanaPolynomial_interlaces_succ (n : ℕ) :
    Interlaces (modifiedNarayanaPolynomial n)
      (modifiedNarayanaPolynomial (n + 1)) :=
  modifiedNarayanaPolynomial_interlaces_succ_of_nonnegCoeffs n
    narayanaQuot_hasNonnegCoeffs

/-- Equation `(2)` determines the leading candidate coefficient of the
auxiliary polynomial `G_n`. -/
theorem auxiliaryG_coeff_sub_one_of_narayanaRecurrence
    (hrec2 :
      NarayanaAuxiliaryGRecurrenceStatement
        modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG)
    (n : ℕ) (hn : 1 ≤ n) :
    (FiniteSkewBoard.auxiliaryG n).coeff (n - 1) = (n : ℝ) := by
  have hrec := hrec2 (n := n + 1) (by lia)
  simp only [Nat.add_sub_cancel] at hrec
  rw [show
      (1 + X) * modifiedNarayanaPolynomial n =
        modifiedNarayanaPolynomial n + X * modifiedNarayanaPolynomial n by
      ring] at hrec
  have hcoeff := congr_arg (fun p : ℝ[X] => p.coeff ((n - 1) + 1)) hrec
  simp only [coeff_X_mul, coeff_sub, coeff_add] at hcoeff
  rw [Nat.sub_add_cancel hn] at hcoeff
  have hPsucc :
      (modifiedNarayanaPolynomial (n + 1)).coeff n =
        ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) + 1) / 2 := by
    simpa using modifiedNarayanaPolynomial_coeff_sub_one (n + 1) (by lia)
  have hPlead : (modifiedNarayanaPolynomial n).coeff n = 1 := by
    calc
      _ = (modifiedNarayanaPolynomial n).coeff
          (modifiedNarayanaPolynomial n).natDegree := by rw [modifiedNarayanaPolynomial_natDegree]
      _ = (modifiedNarayanaPolynomial n).leadingCoeff := coeff_natDegree
      _ = 1 := modifiedNarayanaPolynomial_leadingCoeff n
  have hPnext := modifiedNarayanaPolynomial_coeff_sub_one n hn
  rw [hPsucc, hPlead, hPnext] at hcoeff
  push_cast at hcoeff
  linarith

/-- Equation `(2)` also determines the coefficient immediately below the
leading candidate coefficient of `G_n`. -/
theorem auxiliaryG_coeff_sub_two_of_narayanaRecurrence
    (hrec2 :
      NarayanaAuxiliaryGRecurrenceStatement
        modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG)
    (n : ℕ) (hn : 2 ≤ n) :
    (FiniteSkewBoard.auxiliaryG n).coeff (n - 2) =
      (n + 1 : ℝ) * n * (n - 1) / 3 := by
  have hrec := hrec2 (n := n + 1) (by lia)
  simp only [Nat.add_sub_cancel] at hrec
  rw [show
      (1 + X) * modifiedNarayanaPolynomial n =
        modifiedNarayanaPolynomial n + X * modifiedNarayanaPolynomial n by
      ring] at hrec
  have hcoeff := congr_arg (fun p : ℝ[X] => p.coeff ((n - 2) + 1)) hrec
  simp only [coeff_X_mul, coeff_sub, coeff_add] at hcoeff
  have hindex : n - 2 + 1 = n - 1 := by lia
  rw [hindex] at hcoeff
  have hPsucc := modifiedNarayanaPolynomial_coeff_sub_two (n + 1) (by lia)
  have hPnext := modifiedNarayanaPolynomial_coeff_sub_one n (by lia)
  have hPsecond := modifiedNarayanaPolynomial_coeff_sub_two n hn
  rw [show n + 1 - 2 = n - 1 by lia] at hPsucc
  rw [hPsucc, hPnext, hPsecond] at hcoeff
  push_cast at hcoeff ⊢
  linarith

/-- Equation `(2)` forces the coefficient one place above the leading
candidate coefficient of `G_n` to vanish. -/
theorem auxiliaryG_coeff_self_of_narayanaRecurrence
    (hrec2 :
      NarayanaAuxiliaryGRecurrenceStatement
        modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG)
    (n : ℕ) :
    (FiniteSkewBoard.auxiliaryG n).coeff n = 0 := by
  have hrec := hrec2 (n := n + 1) (by lia)
  simp only [Nat.add_sub_cancel] at hrec
  rw [show
      (1 + X) * modifiedNarayanaPolynomial n =
        modifiedNarayanaPolynomial n + X * modifiedNarayanaPolynomial n by
      ring] at hrec
  have hcoeff := congr_arg (fun p : ℝ[X] => p.coeff (n + 1)) hrec
  simp only [coeff_X_mul, coeff_sub, coeff_add] at hcoeff
  have hPsucc :
      (modifiedNarayanaPolynomial (n + 1)).coeff (n + 1) = 1 := by
    calc
      _ = (modifiedNarayanaPolynomial (n + 1)).coeff
          (modifiedNarayanaPolynomial (n + 1)).natDegree := by
            rw [modifiedNarayanaPolynomial_natDegree]
      _ = (modifiedNarayanaPolynomial (n + 1)).leadingCoeff := coeff_natDegree
      _ = 1 := modifiedNarayanaPolynomial_leadingCoeff (n + 1)
  have hPabove : (modifiedNarayanaPolynomial n).coeff (n + 1) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    rw [modifiedNarayanaPolynomial_natDegree]
    lia
  have hPlead : (modifiedNarayanaPolynomial n).coeff n = 1 := by
    calc
      _ = (modifiedNarayanaPolynomial n).coeff
          (modifiedNarayanaPolynomial n).natDegree := by rw [modifiedNarayanaPolynomial_natDegree]
      _ = (modifiedNarayanaPolynomial n).leadingCoeff := coeff_natDegree
      _ = 1 := modifiedNarayanaPolynomial_leadingCoeff n
  rw [hPsucc, hPabove, hPlead] at hcoeff
  linarith

/-- Equation `(2)` and its two leading coefficients determine the degree of
the auxiliary polynomial `G_n`. -/
theorem auxiliaryG_natDegree_of_narayanaRecurrence
    (hrec2 :
      NarayanaAuxiliaryGRecurrenceStatement
        modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG)
    (n : ℕ) (hn : 1 ≤ n) :
    (FiniteSkewBoard.auxiliaryG n).natDegree = n - 1 := by
  have hcoeff :=
    auxiliaryG_coeff_sub_one_of_narayanaRecurrence hrec2 n hn
  have hcoeff_ne : (FiniteSkewBoard.auxiliaryG n).coeff (n - 1) ≠ 0 := by
    rw [hcoeff]
    positivity
  have hG_ne : FiniteSkewBoard.auxiliaryG n ≠ 0 := by
    intro hzero
    apply hcoeff_ne
    rw [hzero]
    simp
  have hrec := hrec2 (n := n + 1) (by lia)
  simp only [Nat.add_sub_cancel] at hrec
  have hlin : (1 + X : ℝ[X]).natDegree ≤ 1 :=
    (natDegree_add_le (1 : ℝ[X]) X).trans (by simp)
  have hprod_le :
      ((1 + X) * modifiedNarayanaPolynomial n).natDegree ≤ n + 1 := by
    calc
      _ ≤ (1 + X : ℝ[X]).natDegree +
          (modifiedNarayanaPolynomial n).natDegree := natDegree_mul_le
      _ ≤ 1 + n := by
        apply Nat.add_le_add
        · exact hlin
        · rw [modifiedNarayanaPolynomial_natDegree]
      _ = n + 1 := by lia
  have hXG_le : (X * FiniteSkewBoard.auxiliaryG n).natDegree ≤ n + 1 := by
    rw [hrec]
    exact (natDegree_sub_le _ _).trans
      (max_le (by rw [modifiedNarayanaPolynomial_natDegree]) hprod_le)
  have hG_le_n : (FiniteSkewBoard.auxiliaryG n).natDegree ≤ n := by
    rw [natDegree_X_mul hG_ne] at hXG_le
    lia
  have hG_le : (FiniteSkewBoard.auxiliaryG n).natDegree ≤ n - 1 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    by_cases hNn : N = n
    · subst N
      exact auxiliaryG_coeff_self_of_narayanaRecurrence hrec2 n
    · exact (natDegree_le_iff_coeff_eq_zero.mp hG_le_n) N (by lia)
  exact natDegree_eq_of_le_of_coeff_ne_zero hG_le hcoeff_ne

/-- Equation `(2)` determines the degree of the auxiliary Braun--Jal pencil. -/
theorem auxiliaryGPencil_natDegree_of_narayanaRecurrence
    (hrec2 :
      NarayanaAuxiliaryGRecurrenceStatement
        modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG)
    {m : ℕ} {lam nu : ℝ} (hm : 2 ≤ m) (hlam : 0 ≤ lam) :
    ((C lam * X + C nu) * FiniteSkewBoard.auxiliaryG (m - 1) +
      FiniteSkewBoard.auxiliaryG m).natDegree = m - 1 := by
  have hfac : (C lam * X + C nu : ℝ[X]).natDegree ≤ 1 := by
    have hlin : (C lam * X : ℝ[X]).natDegree ≤ 1 := by
      calc
        _ ≤ (C lam : ℝ[X]).natDegree + (X : ℝ[X]).natDegree := natDegree_mul_le
        _ ≤ 1 := by simp
    exact (natDegree_add_le _ _).trans (max_le hlin (by simp))
  have hGprev_deg :
      (FiniteSkewBoard.auxiliaryG (m - 1)).natDegree = m - 2 := by
    simpa only [show m - 1 - 1 = m - 2 by lia] using
      auxiliaryG_natDegree_of_narayanaRecurrence hrec2 (m - 1) (by lia)
  have hGm_deg : (FiniteSkewBoard.auxiliaryG m).natDegree = m - 1 :=
    auxiliaryG_natDegree_of_narayanaRecurrence hrec2 m (by lia)
  have hprod :
      ((C lam * X + C nu) * FiniteSkewBoard.auxiliaryG (m - 1)).natDegree ≤
        m - 1 := by
    calc
      _ ≤ (C lam * X + C nu : ℝ[X]).natDegree +
          (FiniteSkewBoard.auxiliaryG (m - 1)).natDegree := natDegree_mul_le
      _ ≤ 1 + (m - 2) := Nat.add_le_add hfac (by rw [hGprev_deg])
      _ = m - 1 := by lia
  have hle :
      ((C lam * X + C nu) * FiniteSkewBoard.auxiliaryG (m - 1) +
        FiniteSkewBoard.auxiliaryG m).natDegree ≤ m - 1 :=
    (natDegree_add_le _ _).trans (max_le hprod (by rw [hGm_deg]))
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
  have hcoeff :
      ((C lam * X + C nu) * FiniteSkewBoard.auxiliaryG (m - 1) +
        FiniteSkewBoard.auxiliaryG m).coeff (m - 1) =
          lam * ((m - 1 : ℕ) : ℝ) + (m : ℝ) := by
    rw [show
      (C lam * X + C nu) * FiniteSkewBoard.auxiliaryG (m - 1) =
        C lam * (X * FiniteSkewBoard.auxiliaryG (m - 1)) +
          C nu * FiniteSkewBoard.auxiliaryG (m - 1) by ring]
    simp only [coeff_add, coeff_C_mul]
    rw [hXGprev_top, hGprev_above, hGm_top]
    ring
  apply natDegree_eq_of_le_of_coeff_ne_zero hle
  rw [hcoeff]
  positivity

end GeneralizedSnakePosets
end RealRooted
