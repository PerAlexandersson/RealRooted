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

end GeneralizedSnakePosets
end RealRooted
