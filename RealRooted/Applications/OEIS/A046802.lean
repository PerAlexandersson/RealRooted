import RealRooted.HermiteBiehler.OrientedPencil
import RealRooted.OEIS.A046802
import RealRooted.Recurrence.RowModel
import RealRooted.Recurrence.Uniqueness
import RealRooted.SymmetricDecomposition.EulerianTransform
import RealRooted.Wronskian.Converse

/-!
# A recurrence bridge for OEIS A046802

The downstream rows use the classical order-two recurrence for the binomial
Eulerian polynomials.  We realize that recurrence through the Eulerian
transform.  The adjacent interlacing needed by the row-model registry follows
from the first two entries of the transform's reflection-interlacing row.
-/

open Polynomial

noncomputable section

namespace RealRooted.Applications.OEIS.A046802

open EulerianTransform

private theorem image_natDegree (n : ℕ) :
    (image n).natDegree = n := by
  cases n with
  | zero => simp [image]
  | succ n =>
      rw [image, natDegree_X_mul (generalizedEulerian_monic 1 n).ne_zero,
        generalizedEulerian_natDegree]

private theorem image_monic (n : ℕ) : (image n).Monic := by
  cases n with
  | zero => simp [image]
  | succ n =>
      rw [image]
      exact monic_X.mul (generalizedEulerian_monic 1 n)

private theorem one_add_X_monic : (1 + X : ℝ[X]).Monic := by
  simpa only [C_1, add_comm] using (monic_X_add_C (R := ℝ) 1)

private theorem binomial_monic (n : ℕ) : (binomial n).Monic := by
  simpa only [binomial, transform, Polynomial.basisTransformₗ_apply] using
    (Polynomial.basisTransform_monic_of_monic
      (B := image) image_natDegree image_monic (one_add_X_monic.pow n))

private theorem binomial_natDegree (n : ℕ) :
    (binomial n).natDegree = n := by
  apply le_antisymm (natDegree_binomial_le_and_reflect n).1.1
  have hinput : ((1 + X : ℝ[X]) ^ n).Monic :=
    one_add_X_monic.pow n
  have hcoeff := Polynomial.coeff_basisTransform_natDegree_eq_one_of_monic
    (B := image) image_natDegree image_monic hinput
  have hinputDegree : ((1 + X : ℝ[X]) ^ n).natDegree = n := by
    rw [one_add_X_monic.natDegree_pow]
    have hlinear : (1 + X : ℝ[X]).natDegree = 1 := by
      simpa only [C_1, add_comm] using (natDegree_X_add_C (R := ℝ) 1)
    rw [hlinear, mul_one]
  change (binomial n).coeff ((1 + X : ℝ[X]) ^ n |>.natDegree) = 1 at hcoeff
  rw [hinputDegree] at hcoeff
  exact le_natDegree_of_ne_zero (by simp [hcoeff])

private theorem basisImage_one_eq_sub (n : ℕ) :
    basisImage (n + 1) 1 = binomial (n + 1) - binomial n := by
  unfold basisImage binomial
  rw [show n + 1 - 1 = n by lia]
  rw [show X ^ 1 * (1 + X) ^ n =
      (1 + X) ^ (n + 1) - (1 + X) ^ n by
        rw [pow_succ]
        ring]
  exact transform.map_sub _ _

/-- Consecutive Eulerian-transform binomial rows strictly interlace. -/
theorem binomial_strictInterl_succ (n : ℕ) :
    StrictInterl (binomial n) (binomial (n + 1)) := by
  let d := n + 1
  let p := binomial d
  let g := binomial n
  let q := basisImage d 1
  have hdirect : IsInterlacingSeq0NonnegRealRooted (row d) :=
    (row_reflectionInterlacing d).closedSequence.sublist (by
      simp [BrandenVecchi.reflectionClosure])
  let first : Fin (row d).length := ⟨0, by simp [row]⟩
  let second : Fin (row d).length := ⟨1, by simp [row, d]⟩
  have hpq : Interl p q := by
    simpa [p, q, first, second, row, basisImage, binomial] using
      hdirect.interlacingSeq0.interl (i := first) (j := second) (by simp [first, second])
  have hp_pos : HasPosLeadingCoeff p :=
    hasPosLeadingCoeff_of_monic (binomial_monic d)
  have hg_pos : HasPosLeadingCoeff g :=
    hasPosLeadingCoeff_of_monic (binomial_monic n)
  have hq_pos : HasPosLeadingCoeff q := by
    have hinput : (X ^ 1 * (1 + X) ^ (d - 1) : ℝ[X]).Monic :=
      (monic_X.pow 1).mul (one_add_X_monic.pow (d - 1))
    exact hasPosLeadingCoeff_of_monic
      (Polynomial.basisTransform_monic_of_monic
        (B := image) image_natDegree image_monic hinput)
  have hp_ne : p ≠ 0 := hp_pos.ne_zero
  have hq_ne : q ≠ 0 := hq_pos.ne_zero
  have hpq_strict : StrictInterl p q := hpq.toStrictInterl_of_ne hp_ne hq_ne
  have hall_pq : AllComboRealRooted p q :=
    allComboRealRooted_of_strictInterl hpq_strict
  have hq_eq : q = p - g := by
    simp only [q, p, g, d]
    exact basisImage_one_eq_sub n
  have hall_pg : AllComboRealRooted p g := by
    apply hall_pq.linear_recombination
        (f := p) (g := q) (a := 1) (b := 0) (c := 1) (d := -1)
    · simp
    · rw [hq_eq]
      norm_num [map_neg, map_one]
  have hW : ∀ t : ℝ, 0 ≤ (wronskian g p).eval t := by
    intro t
    have h := wronskian_eval_nonneg_of_strictInterl hq_pos hp_pos hpq_strict t
    rw [hq_eq] at h
    convert h using 1
    unfold wronskian
    simp only [derivative_sub]
    ring
  have hstrict :=
    strictInterl_of_allComboRealRooted_of_wronskian_nonneg
      hp_pos hg_pos hall_pg hW
  simpa [p, g, d] using hstrict

/-- The order-two update in the downstream A046802 presentation. -/
def nextRow (n : ℕ) (p q : ℝ[X]) : ℝ[X] :=
  (X - X ^ 2) * p.derivative +
    (1 + C ((n : ℝ) + 2) * X) * p +
      C (-1 - (n : ℝ)) * X * q

private theorem binomial_step (n : ℕ) :
    binomial (n + 2) = nextRow n (binomial (n + 1)) (binomial n) := by
  rw [binomial_succ_succ]
  unfold nextRow
  push_cast
  norm_num [map_add, map_mul, map_ofNat]
  ring

/-- Every sequence with the A046802 initial rows and classical terminal
recurrence has strict adjacent interlacing. -/
@[rr_row_model]
theorem interlaces_of_recurrence
    {P : ℕ → ℝ[X]}
    (hzero : P 0 = 1)
    (hone : P 1 = 1 + X)
    (hrec : ∀ n, P (n + 2) = nextRow n (P (n + 1)) (P n))
    (n : ℕ) :
    Interlaces (P n) (P (n + 1)) := by
  have heq := sequence_eq_of_same_lag_two_recurrence nextRow
    (by simpa using hzero) (by simpa using hone) hrec binomial_step
  rw [heq n, heq (n + 1)]
  exact (binomial_strictInterl_succ n).toInterlaces (by
    rw [binomial_natDegree, binomial_natDegree])

end RealRooted.Applications.OEIS.A046802
