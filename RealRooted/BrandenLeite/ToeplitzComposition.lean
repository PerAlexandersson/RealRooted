import RealRooted.BrandenLeite.CompositionRow
import RealRooted.BrandenLeite.ConstantDiagonal

/-!
# Toeplitz chain polynomials and composition rows

The chain-polynomial recurrence of a Toeplitz matrix ignores its diagonal
entry.  This file identifies those chain polynomials with the composition
rows of the series obtained by retaining exactly the positive-order Toeplitz
coefficients.  For a PF sequence with positive zeroth entry, the
constant-diagonal normalization theorem then supplies PF and proper-position
conclusions for these rows.
-/

open Matrix Polynomial BigOperators

noncomputable section

namespace RealRooted.BrandenLeite

/-- The formal power series obtained from a sequence by setting only its
zeroth entry to zero. -/
def positivePartSeries {R : Type*} [Semiring R]
    (a : ℕ → R) : PowerSeries R :=
  PowerSeries.mk fun n => if n = 0 then 0 else a n

@[simp]
theorem coeff_positivePartSeries {R : Type*} [Semiring R]
    (a : ℕ → R) (n : ℕ) :
    PowerSeries.coeff n (positivePartSeries a) =
      if n = 0 then 0 else a n := by
  rw [positivePartSeries, PowerSeries.coeff_mk]

@[simp]
theorem constantCoeff_positivePartSeries
    {R : Type*} [Semiring R] (a : ℕ → R) :
    PowerSeries.constantCoeff (positivePartSeries a) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    coeff_positivePartSeries]
  simp

@[simp]
theorem coeff_positivePartSeries_of_pos
    {R : Type*} [Semiring R] (a : ℕ → R)
    {n : ℕ} (hn : 0 < n) :
    PowerSeries.coeff n (positivePartSeries a) = a n := by
  simp [hn.ne']

/-- Toeplitz chain polynomials are exactly the composition rows of the
positive-order part of their defining sequence. -/
theorem chainPolynomial_toeplitz_eq_compositionRow
    {R : Type*} [CommSemiring R] (a : ℕ → R) (n : ℕ) :
    chainPolynomial (toeplitz a) n =
      compositionRow (positivePartSeries a) n := by
  apply congrFun (eq_compositionRow_of_zero_and_succ
    (constantCoeff_positivePartSeries a) (chainPolynomial (toeplitz a))
    (chainPolynomial_zero (toeplitz a)) ?_) n
  intro m
  rw [chainPolynomial_succ]
  apply congrArg (X * ·)
  rw [← Fin.sum_univ_eq_sum_range]
  symm
  exact Fintype.sum_equiv Fin.revPerm
    (fun j =>
      C (PowerSeries.coeff (j + 1) (positivePartSeries a)) *
        chainPolynomial (toeplitz a) (m - j))
    (fun k =>
      C (toeplitz a (m + 1) k) * chainPolynomial (toeplitz a) k)
    (fun j => by
      simp only [coeff_positivePartSeries_of_pos a (Nat.succ_pos _),
        Fin.revPerm_apply, toeplitz_apply]
      rw [if_pos (by lia)]
      have hsum := j.add_rev_cast
      have harg : m + 1 - (j.rev : ℕ) = (j : ℕ) + 1 := by
        calc
          m + 1 - (j.rev : ℕ) =
              ((j : ℕ) + (j.rev : ℕ)) + 1 - (j.rev : ℕ) := by rw [hsum]
          _ = ((j : ℕ) + 1) + (j.rev : ℕ) - (j.rev : ℕ) := by
            rw [Nat.add_assoc, Nat.add_comm (j.rev : ℕ) 1, ← Nat.add_assoc]
          _ = (j : ℕ) + 1 := Nat.add_sub_cancel_right _ _
      have hindex : m - (j : ℕ) = (j.rev : ℕ) := by
        calc
          m - (j : ℕ) =
              ((j : ℕ) + (j.rev : ℕ)) - (j : ℕ) := by rw [hsum]
          _ = (j.rev : ℕ) := Nat.add_sub_cancel_left _ _
      rw [harg, hindex])

/-- Positive-order composition rows of a PF sequence with positive zeroth
entry are PF polynomials. -/
theorem compositionRow_positivePartSeries_isPFPolynomial
    {a : ℕ → ℝ} (ha : IsPolyaFreqSeq a) (ha0 : 0 < a 0) (n : ℕ) :
    IsPFPolynomial (compositionRow (positivePartSeries a) n) := by
  rw [← chainPolynomial_toeplitz_eq_compositionRow]
  apply chainPolynomial_isPFPolynomial_of_pos_constantDiagonal ha0
  · intro i j hij
    simp [toeplitz_apply, Nat.not_le_of_lt hij]
  · intro i
    simp [toeplitz_apply]
  · exact ha

/-- Consecutive positive-order composition rows of a PF sequence with positive
zeroth entry are in zero-aware proper position. -/
theorem prec0_compositionRow_positivePartSeries_succ
    {a : ℕ → ℝ} (ha : IsPolyaFreqSeq a) (ha0 : 0 < a 0) (n : ℕ) :
    Prec0 (compositionRow (positivePartSeries a) n)
      (compositionRow (positivePartSeries a) (n + 1)) := by
  rw [← chainPolynomial_toeplitz_eq_compositionRow,
    ← chainPolynomial_toeplitz_eq_compositionRow]
  apply prec0_chainPolynomial_succ_of_pos_constantDiagonal ha0
  · intro i j hij
    simp [toeplitz_apply, Nat.not_le_of_lt hij]
  · intro i
    simp [toeplitz_apply]
  · exact ha

end RealRooted.BrandenLeite
