import RealRooted.ClassicalHurwitzMatrix.Routh
import RealRooted.Mathlib.LinearAlgebra.Matrix.Hurwitz.Determinant

/-!
# The leading Hurwitz-determinant recurrence

This file extracts the determinant recurrence from one algebraic Routh step.
-/

open Polynomial

namespace Matrix

open RealRooted

noncomputable section

/-- A predecessor-closed row minor of a Hurwitz matrix is unchanged by one
reverse Routh row operation. -/
theorem hurwitz_submatrix_det_eq_routhExpand_of_predecessor_closed
    {R : Type*} [CommRing R] (c : R) (a : ℕ → R) {n : ℕ}
    (rows cols : Fin (n + 1) → ℕ)
    (hfirst : Even (rows 0))
    (hpred : ∀ i : Fin n, Odd (rows i.succ) →
      rows i.succ = rows i.castSucc + 1) :
    ((hurwitz a).submatrix rows cols).det =
      ((routhExpand c (hurwitz a)).submatrix
        (fun i => rows i + 1) (fun j => cols j + 1)).det := by
  let A : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
    (hurwitz a).submatrix (fun i => rows i + 2) (fun j => cols j + 1)
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
    (routhExpand c (hurwitz a)).submatrix
      (fun i => rows i + 1) (fun j => cols j + 1)
  have horiginal : (hurwitz a).submatrix rows cols = A := by
    ext i j
    exact (hurwitz_add_two_add_one a (rows i) (cols j)).symm
  rw [horiginal]
  apply det_eq_of_forall_row_eq_smul_add_pred
    (fun i : Fin n => if Odd (rows i.succ) then -c else 0)
  · intro j
    rcases hfirst with ⟨k, hk⟩
    simp only [A, submatrix_apply]
    rw [hk]
    simpa only [Nat.two_mul] using
      (routhExpand_odd_apply c (hurwitz a) k (cols j + 1)).symm
  · intro i j
    simp only [A, submatrix_apply]
    rcases Nat.even_or_odd (rows i.succ) with ⟨k, hk⟩ | ⟨k, hk⟩
    · have hnot : ¬Odd (rows i.succ) := by
        intro hodd
        rcases hodd with ⟨m, hm⟩
        lia
      rw [if_neg hnot]
      rw [hk, show k + k + 1 = 2 * k + 1 by lia,
        show k + k + 2 = 2 * k + 2 by lia]
      simp
    · have hodd : Odd (rows i.succ) := ⟨k, hk⟩
      rw [if_pos hodd]
      have hp := hpred i hodd
      have hprev : rows i.castSucc = 2 * k := by lia
      rw [show rows i.succ + 2 = 2 * (k + 1) + 1 by lia,
        show rows i.succ + 1 = 2 * (k + 1) by lia, hprev]
      simp only [routhExpand_even_apply]
      ring_nf

private def routhTail (odd even : ℝ[X]) (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (hurwitzLeadingPrincipal (oddEvenPolynomial odd even).coeff (n + 1)).submatrix
    Fin.succ Fin.succ

private theorem routhTail_det (c : ℝ) (odd even : ℝ[X])
    (h0 : even.coeff 0 = c * odd.coeff 0) (n : ℕ) :
    (routhTail odd even n).det =
      (hurwitzLeadingPrincipal (routhReducedPolynomial c odd even).coeff n).det := by
  unfold routhTail hurwitzLeadingPrincipal
  rw [hurwitz_oddEvenPolynomial_eq_routhExpand c odd even h0]
  rcases n with _ | n
  · simp
  apply det_eq_of_forall_row_eq_smul_add_pred
    (fun i : Fin n ↦ if (i : ℕ) % 2 = 0 then c else 0)
  · intro j
    simp only [submatrix_apply]
    simpa [routhExpand] using
      hurwitz_add_two_add_one
        (routhReducedPolynomial c odd even).coeff 0 (j : ℕ)
  · intro i j
    simp only [submatrix_apply]
    change routhExpand c
        (hurwitz (routhReducedPolynomial c odd even).coeff)
          ((i : ℕ) + 2) ((j : ℕ) + 1) =
      hurwitz (routhReducedPolynomial c odd even).coeff
          ((i : ℕ) + 1) (j : ℕ) +
        (if (i : ℕ) % 2 = 0 then c else 0) *
          routhExpand c (hurwitz (routhReducedPolynomial c odd even).coeff)
            ((i : ℕ) + 1) ((j : ℕ) + 1)
    rcases Nat.even_or_odd (i : ℕ) with ⟨k, hk⟩ | ⟨k, hk⟩
    · have hi : (i : ℕ) = 2 * k := by lia
      rw [hi]
      rw [show 2 * k + 2 = 2 * (k + 1) by ring]
      rw [routhExpand_even_apply]
      rw [show 2 * (k + 1) = 2 * k + 2 by ring]
      rw [show 2 * k + 2 + 1 = (2 * k + 1) + 2 by ring]
      rw [hurwitz_add_two_add_one, hurwitz_add_two_add_one]
      have hprev : routhExpand c
          (hurwitz (routhReducedPolynomial c odd even).coeff)
            (2 * k + 1) ((j : ℕ) + 1) =
          hurwitz (routhReducedPolynomial c odd even).coeff (2 * k) (j : ℕ) := by
        rw [routhExpand_odd_apply]
        rw [show 2 * k + 2 = 2 * (k + 1) by ring]
        exact hurwitz_add_two_add_one _ _ _
      rw [hprev]
      simp
      ring
    · have hi : (i : ℕ) = 2 * k + 1 := by lia
      rw [hi]
      rw [show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by ring]
      rw [routhExpand_odd_apply]
      rw [show 2 * (k + 1) + 2 = 2 * (k + 2) by ring]
      rw [show 2 * (k + 2) = (2 * k + 2) + 2 by ring]
      rw [hurwitz_add_two_add_one]
      rw [if_neg (by simp)]
      simp only [zero_mul, add_zero]

/-- One algebraic Routh step removes the first leading Hurwitz factor. -/
theorem hurwitzLeadingPrincipal_oddEvenPolynomial_det_succ
    (c : ℝ) (odd even : ℝ[X]) (h0 : even.coeff 0 = c * odd.coeff 0)
    (n : ℕ) :
    (hurwitzLeadingPrincipal (oddEvenPolynomial odd even).coeff (n + 1)).det =
      even.coeff 0 *
        (hurwitzLeadingPrincipal
          (routhReducedPolynomial c odd even).coeff n).det := by
  let A := hurwitzLeadingPrincipal (oddEvenPolynomial odd even).coeff (n + 1)
  have hzero (i : Fin n) : A i.succ 0 = 0 := by
    simp [A, hurwitzLeadingPrincipal, hurwitz]
  rw [det_succ_column_zero A, Fin.sum_univ_succ]
  simp only [hzero, mul_zero, zero_mul, Finset.sum_const_zero, add_zero,
    Fin.val_zero, pow_zero, one_mul]
  change (oddEvenPolynomial odd even).coeff 0 *
      (routhTail odd even n).det = _
  rw [show (oddEvenPolynomial odd even).coeff 0 = even.coeff 0 by
    simpa using coeff_oddEvenPolynomial_even odd even 0]
  rw [routhTail_det c odd even h0 n]

/-- Ratio-specialized form of the leading Hurwitz-determinant recurrence. -/
theorem hurwitzLeadingPrincipal_oddEvenPolynomial_det_succ_ratio
    (odd even : ℝ[X]) (hodd : odd.coeff 0 ≠ 0) (n : ℕ) :
    (hurwitzLeadingPrincipal (oddEvenPolynomial odd even).coeff (n + 1)).det =
      even.coeff 0 *
        (hurwitzLeadingPrincipal
          (routhReducedPolynomial (routhCoefficient odd even) odd even).coeff n).det :=
  hurwitzLeadingPrincipal_oddEvenPolynomial_det_succ _ _ _
    (routhCoefficient_mul_coeff_zero odd even hodd) n

/-- With a positive first Hurwitz factor, positivity of the next leading
determinant is equivalent to positivity of the reduced leading determinant. -/
theorem hurwitzLeadingPrincipal_oddEvenPolynomial_det_succ_pos_iff
    (c : ℝ) (odd even : ℝ[X]) (h0 : even.coeff 0 = c * odd.coeff 0)
    (heven : 0 < even.coeff 0) (n : ℕ) :
    0 < (hurwitzLeadingPrincipal
        (oddEvenPolynomial odd even).coeff (n + 1)).det ↔
      0 < (hurwitzLeadingPrincipal
        (routhReducedPolynomial c odd even).coeff n).det := by
  rw [hurwitzLeadingPrincipal_oddEvenPolynomial_det_succ c odd even h0 n,
    mul_pos_iff_of_pos_left heven]

end

end Matrix
