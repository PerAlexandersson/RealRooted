import RealRooted.GeneralizedSnakePosets.Narayana.Turan
import RealRooted.GeneralizedSnakePosets.MatrixInduction
import RealRooted.GeneralizedSnakePosetsNarayana

/-!
# Braun--Jal Claim 7 for modified Narayana polynomials

This module combines the analytic Lemma 3.4 proof from the Turan development
with the endpoint-safe Claim 7 conversion.
-/

open Polynomial

noncomputable section

namespace RealRooted
namespace GeneralizedSnakePosets

/-- The recurrence hypothesis is accepted combinatorial input from equation (2)
of the paper.  Formalizing the generalized-snake-poset model that proves this
identity is outside the present scope; from this point onward we derive the
analytic root information in Lean. -/
theorem auxiliaryG_roots_sum_of_narayanaRecurrence
    (hrec2 : NarayanaAuxiliaryGRecurrenceStatement
      modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG)
    {n : ℕ} (hn : 2 ≤ n) :
    (FiniteSkewBoard.auxiliaryG n).roots.sum =
      -(((n : ℝ) + 1) * ((n : ℝ) - 1) / 3) := by
  have hsplit : (FiniteSkewBoard.auxiliaryG n).Splits := by
    simpa using auxiliaryGPencil_splits_of_section3 hrec2
      lemma34ModifiedNarayanaInterlacing_modified (m := n) (lam := 0) (nu := 0)
      hn (by norm_num) (by norm_num)
  have hdeg := auxiliaryG_natDegree_of_narayanaRecurrence hrec2 n (by lia)
  have hdegpos : 0 < (FiniteSkewBoard.auxiliaryG n).natDegree := by
    rw [hdeg]
    lia
  have hlead : (FiniteSkewBoard.auxiliaryG n).leadingCoeff = (n : ℝ) := by
    rw [← Polynomial.coeff_natDegree, hdeg]
    exact auxiliaryG_coeff_sub_one_of_narayanaRecurrence hrec2 n (by lia)
  have hnext :
      (FiniteSkewBoard.auxiliaryG n).nextCoeff =
        ((n : ℝ) + 1) * (n : ℝ) * ((n : ℝ) - 1) / 3 := by
    rw [Polynomial.nextCoeff_of_natDegree_pos hdegpos, hdeg]
    simpa [Nat.sub_sub] using
      auxiliaryG_coeff_sub_two_of_narayanaRecurrence hrec2 n hn
  have hvieta := hsplit.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
  rw [hnext, hlead] at hvieta
  apply mul_left_cancel₀ (show (n : ℝ) ≠ 0 by positivity)
  nlinarith

/-- Braun--Jal Claim `(7)` for the concrete modified Narayana family.

The remaining hypotheses are intentionally explicit combinatorial inputs.
Equation `(2)` is the non-nesting-rook recurrence defining the auxiliary
family, while coefficientwise nonnegativity of `G n - G (n - 1)` comes from
the same board interpretation. We use these facts without formalizing the full
rook model; all analytic real-rootedness and interlacing steps are proved in
Lean. -/
theorem theorem41Claim7_modified
    (hrec2 : NarayanaAuxiliaryGRecurrenceStatement
      modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG)
    (hH_nonneg : ∀ n : ℕ, 1 ≤ n →
      HasNonnegCoeffs
        (FiniteSkewBoard.auxiliaryG n -
          FiniteSkewBoard.auxiliaryG (n - 1))) :
    Theorem41Claim7Statement
      modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG :=
  theorem41Claim7_modified_of_section3 hrec2
    lemma34ModifiedNarayanaInterlacing_modified hH_nonneg

/-- Braun--Jal Lemma 3.3 follows from Claim 7 at `lam = nu = 0`, apart from
the already proved `n = 1` base case.  The recurrence and difference
nonnegativity hypotheses remain the accepted combinatorial inputs documented
above; this deduction from them is entirely analytic. -/
theorem lemma33AuxiliaryGInterlaces_modified
    (hrec2 : NarayanaAuxiliaryGRecurrenceStatement
      modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG)
    (hH_nonneg : ∀ n : ℕ, 1 ≤ n →
      HasNonnegCoeffs
        (FiniteSkewBoard.auxiliaryG n -
          FiniteSkewBoard.auxiliaryG (n - 1))) :
    Lemma33AuxiliaryGInterlacesStatement
      modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG := by
  intro n hn
  rcases eq_or_lt_of_le hn with h | hn
  · subst n
    exact lemma33AuxiliaryGInterlaces_modified_base
  · simpa using
      theorem41Claim7_modified hrec2 hH_nonneg
        (m := n) (lam := 0) (nu := 0) (by lia) (by norm_num) (by norm_num)

/-- Consecutive auxiliary `G` polynomials have real-rooted positive linear
combinations. This is the part of adjacent `G` proper position supplied
directly by equation `(2)` and Lemma 3.4; orienting the pencil remains a
separate analytic step. -/
theorem auxiliaryG_posComboRealRooted_of_narayanaRecurrence
    (hrec2 : NarayanaAuxiliaryGRecurrenceStatement
      modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG)
    {m : ℕ} (hm : 2 ≤ m) :
    PosComboRealRooted (FiniteSkewBoard.auxiliaryG (m - 1))
      (FiniteSkewBoard.auxiliaryG m) := by
  intro lam mu hlam hmu
  have hmu_ne : mu ≠ 0 := ne_of_gt hmu
  have hratio : 0 < lam / mu := div_pos hlam hmu
  let V : ℝ[X] :=
    C (lam / mu) * FiniteSkewBoard.auxiliaryG (m - 1) +
      FiniteSkewBoard.auxiliaryG m
  have hV_split : V.Splits := by
    simpa [V] using auxiliaryGPencil_splits_of_section3 (lam := 0) hrec2
      lemma34ModifiedNarayanaInterlacing_modified hm (by positivity)
      (show -1 ≤ lam / mu by linarith)
  have hV_pos : HasPosLeadingCoeff V := by
    simpa [V] using auxiliaryGPencil_hasPosLeadingCoeff_of_narayanaRecurrence
      (lam := 0) (nu := lam / mu) hrec2 hm (by positivity)
  have hscale :
      C mu * V =
        C lam * FiniteSkewBoard.auxiliaryG (m - 1) +
          C mu * FiniteSkewBoard.auxiliaryG m := by
    dsimp [V]
    rw [mul_add, ← mul_assoc, ← map_mul]
    field_simp
  rw [← hscale]
  exact ⟨mul_ne_zero (by simpa using hmu_ne) hV_pos.ne_zero,
    hV_split.C_mul mu⟩

/-- The Braun--Jal induction route for the concrete modified Narayana data.

The recurrence `hrec2` and difference nonnegativity `hH_nonneg` are the
explicit combinatorial inputs described at `theorem41Claim7_modified`. The
remaining hypotheses are genuine properties of the chosen snake-polynomial
model and the auxiliary family; none assumes the induction-route conclusion. -/
theorem theorem41InductionRoute_modified_of_modelInputs
    {M : SnakeWord → ℝ[X]}
    (hrec2 : NarayanaAuxiliaryGRecurrenceStatement
      modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG)
    (hH_nonneg : ∀ n : ℕ, 1 ≤ n →
      HasNonnegCoeffs
        (FiniteSkewBoard.auxiliaryG n -
          FiniteSkewBoard.auxiliaryG (n - 1)))
    (hG : ∀ {m : ℕ}, 2 ≤ m →
      Prec (FiniteSkewBoard.auxiliaryG (m - 1))
        (FiniteSkewBoard.auxiliaryG m))
    (hM_nonneg : ∀ w : SnakeWord, HasNonnegCoeffs (M w))
    (hdeg : ∀ {w : SnakeWord}, 1 ≤ w.length →
      (M w.deleteFinal).natDegree + 1 = (M w).natDegree)
    (hM_const : ∀ {w : SnakeWord}, w.IsConstant →
      M w = modifiedNarayanaPolynomial (w.length + 1)) :
    Theorem41InductionRouteStatement M modifiedNarayanaPolynomial
      FiniteSkewBoard.auxiliaryG :=
  theorem41InductionRoute_of_claim7_of_constant_matches_succ_length
    (fun _h33 _h34 => theorem41Claim7_modified hrec2 hH_nonneg)
    modifiedNarayanaPolynomial_interlaces_succ hG
    modifiedNarayanaPolynomial_one FiniteSkewBoard.auxiliaryG_one
    modifiedNarayanaPolynomial_hasNonnegCoeffs
    FiniteSkewBoard.auxiliaryG_hasNonnegCoeffs hM_nonneg hdeg hM_const

private theorem prec_narayanaPolynomial_two (n : ℕ) :
    Prec (narayanaPolynomial 2 n) (narayanaPolynomial 2 (n + 1)) := by
  cases n with
  | zero =>
      rw [narayanaPolynomial_one]
      simpa using
        (interlaces_one_linear (Polynomial.natDegree_X_add_C (1 : ℝ))).toPrec
  | succ n =>
      simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
        prec_narayanaPolynomial_succ 2 n

/-- Consecutive auxiliary polynomials are in proper position once the rook
model identifies `G n` with `n` times the parameter-two generalized Narayana
polynomial.  This identity is accepted as combinatorial input: formalizing its
board bijection is outside scope, while the proper-position deduction is
proved here from the generalized Narayana recurrence. -/
theorem auxiliaryG_prec_succ_of_narayanaTwoModel
    (hG_model : ∀ n : ℕ, 1 ≤ n →
      FiniteSkewBoard.auxiliaryG n =
        C (n : ℝ) * narayanaPolynomial 2 (n - 1)) :
    ∀ {m : ℕ}, 2 ≤ m →
      Prec (FiniteSkewBoard.auxiliaryG (m - 1))
        (FiniteSkewBoard.auxiliaryG m) := by
  intro m hm
  rw [hG_model (m - 1) (by lia), hG_model m (by lia)]
  have hprec := prec_narayanaPolynomial_two (m - 2)
  have hm1_ne : ((m - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show m - 1 ≠ 0 by lia)
  have hscaled :=
    (hprec.C_mul_left hm1_ne).C_mul_right
      (show (m : ℝ) ≠ 0 by positivity)
  have hleft : m - 1 - 1 = m - 2 := by lia
  have hright : m - 2 + 1 = m - 1 := by lia
  simpa [hleft, hright] using hscaled

/-- Concrete Theorem 4.1 checkpoint with its proof boundary made explicit.
The recurrence, coefficient nonnegativity, word recurrence, degree, and
constant-word hypotheses are combinatorial model inputs, so accepting them is
consistent with the scope documented above.  In contrast, `hG` is an analytic
premise still to be proved (or removed by a sharper matrix argument); this
theorem isolates that sole remaining analytic boundary rather than claiming
the final result unconditionally. -/
theorem theorem41NonNestingRook_modified_of_modelInputs_of_adjacentG
    {M : SnakeWord → ℝ[X]}
    (hrec2 : NarayanaAuxiliaryGRecurrenceStatement
      modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG)
    (hH_nonneg : ∀ n : ℕ, 1 ≤ n →
      HasNonnegCoeffs
        (FiniteSkewBoard.auxiliaryG n -
          FiniteSkewBoard.auxiliaryG (n - 1)))
    (hG : ∀ {m : ℕ}, 2 ≤ m →
      Prec (FiniteSkewBoard.auxiliaryG (m - 1))
        (FiniteSkewBoard.auxiliaryG m))
    (hrec : Theorem35GeneralizedSnakeRecurrenceStatement M
      modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG)
    (hM_nonneg : ∀ w : SnakeWord, HasNonnegCoeffs (M w))
    (hdeg : ∀ {w : SnakeWord}, 1 ≤ w.length →
      (M w.deleteFinal).natDegree + 1 = (M w).natDegree)
    (hM_const : ∀ {w : SnakeWord}, w.IsConstant →
      M w = modifiedNarayanaPolynomial (w.length + 1)) :
    Theorem41NonNestingRookStatement M := by
  exact
    (theorem41InductionRoute_modified_of_modelInputs hrec2 hH_nonneg hG
      hM_nonneg hdeg hM_const)
      (lemma33AuxiliaryGInterlaces_modified hrec2 hH_nonneg)
      lemma34ModifiedNarayanaInterlacing_modified hrec

/-- Braun--Jal Theorem 4.1 from combinatorial model inputs.  In particular,
`hG_model` is the accepted rook-model identification described above; all
real-rootedness and proper-position consequences are proved from recurrences. -/
/--
The model-input hypotheses below are an intentional trust boundary: they record only the
combinatorial identifications from the paper, whose full rook and order-polytope models are
outside the scope of this project.  They do not assume interlacing or real-rootedness; those
conclusions are derived here from the formalized recurrence and generalized Narayana theory.
-/
theorem theorem41NonNestingRook_modified_of_modelInputs
    {M : SnakeWord → ℝ[X]}
    (hrec2 : NarayanaAuxiliaryGRecurrenceStatement
      modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG)
    (hH_nonneg : ∀ n : ℕ, 1 ≤ n →
      HasNonnegCoeffs
        (FiniteSkewBoard.auxiliaryG n -
          FiniteSkewBoard.auxiliaryG (n - 1)))
    (hG_model : ∀ n : ℕ, 1 ≤ n →
      FiniteSkewBoard.auxiliaryG n =
        C (n : ℝ) * narayanaPolynomial 2 (n - 1))
    (hrec : Theorem35GeneralizedSnakeRecurrenceStatement M
      modifiedNarayanaPolynomial FiniteSkewBoard.auxiliaryG)
    (hM_nonneg : ∀ w : SnakeWord, HasNonnegCoeffs (M w))
    (hdeg : ∀ {w : SnakeWord}, 1 ≤ w.length →
      (M w.deleteFinal).natDegree + 1 = (M w).natDegree)
    (hM_const : ∀ {w : SnakeWord}, w.IsConstant →
      M w = modifiedNarayanaPolynomial (w.length + 1)) :
    Theorem41NonNestingRookStatement M :=
  theorem41NonNestingRook_modified_of_modelInputs_of_adjacentG hrec2 hH_nonneg
    (auxiliaryG_prec_succ_of_narayanaTwoModel hG_model) hrec hM_nonneg hdeg hM_const

end GeneralizedSnakePosets
end RealRooted
