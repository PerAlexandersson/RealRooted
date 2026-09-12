import RealRooted.AissenSchoenbergWhitneyBase
import RealRooted.BrandenVecchi.Chow
import RealRooted.Mathlib.RingTheory.PowerSeries.Regular

/-!
# Chow series of lower Toeplitz matrices

This module proves the formal-power-series identities for the Chow and
Chow-derangement polynomials of a lower Toeplitz matrix.  It is the finite,
coefficientwise algebraic core of Brändén--Vecchi, Theorem 8.1; no positivity
or convergence hypothesis is involved.
-/

open Polynomial BigOperators

namespace RealRooted.BrandenVecchi

noncomputable section

variable {R : Type*} [CommRing R]

/-- A coefficient sequence, embedded as constants in polynomial-valued formal
power series. -/
def toeplitzCoefficientSeries (a : ℕ → R) : PowerSeries R[X] :=
  PowerSeries.mk fun n => C (a n)

/-- The formal series of Chow-derangement polynomials of `toeplitz a`. -/
def toeplitzChowDerangementSeries (a : ℕ → R) : PowerSeries R[X] :=
  PowerSeries.mk fun n => chowDerangement (RealRooted.toeplitz a) n

/-- The formal series of Chow polynomials of `toeplitz a`. -/
def toeplitzChowSeries (a : ℕ → R) : PowerSeries R[X] :=
  PowerSeries.mk fun n => chowPolynomial (RealRooted.toeplitz a) n

@[simp]
theorem coeff_toeplitzCoefficientSeries (a : ℕ → R) (n : ℕ) :
    PowerSeries.coeff n (toeplitzCoefficientSeries a) = C (a n) := by
  simp [toeplitzCoefficientSeries]

@[simp]
theorem coeff_toeplitzChowDerangementSeries (a : ℕ → R) (n : ℕ) :
    PowerSeries.coeff n (toeplitzChowDerangementSeries a) =
      chowDerangement (RealRooted.toeplitz a) n := by
  simp [toeplitzChowDerangementSeries]

@[simp]
theorem coeff_toeplitzChowSeries (a : ℕ → R) (n : ℕ) :
    PowerSeries.coeff n (toeplitzChowSeries a) =
      chowPolynomial (RealRooted.toeplitz a) n := by
  simp [toeplitzChowSeries]

/-- The Chow series is the coefficient series times the Chow-derangement
series.  This is the series form of the defining row expansion. -/
theorem toeplitzChowSeries_eq_mul (a : ℕ → R) :
    toeplitzChowSeries a =
      toeplitzCoefficientSeries a * toeplitzChowDerangementSeries a := by
  apply PowerSeries.ext
  intro n
  rw [PowerSeries.coeff_mul]
  simp only [coeff_toeplitzChowSeries, coeff_toeplitzCoefficientSeries,
    coeff_toeplitzChowDerangementSeries]
  rw [chowPolynomial_eq]
  simp only [RealRooted.toeplitz_apply]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [← Finset.sum_range_reflect
    (fun k => C (a k) * chowDerangement (RealRooted.toeplitz a) (n - k))
    (n + 1)]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  simp [hkn, Nat.sub_sub_self]

/-- Reflection of a Toeplitz Chow row moves the coefficient offset into a
power of the Chow variable. -/
theorem reflect_chowPolynomial_toeplitz (a : ℕ → R) (n : ℕ) :
    (chowPolynomial (RealRooted.toeplitz a) n).reflect n =
      ∑ k ∈ Finset.range (n + 1),
        C (a (n - k)) *
          (chowDerangement (RealRooted.toeplitz a) k * X ^ (n - k)) := by
  rw [chowPolynomial_eq, Polynomial.reflect_finset_sum_C_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  rw [RealRooted.toeplitz_apply, if_pos hkn]
  congr 1
  simpa [Nat.add_sub_of_le hkn] using
    Polynomial.reflect_add_right_of_reflect (n - k)
      (natDegree_chowDerangement_le (RealRooted.toeplitz a) k)
      (reflect_chowDerangement (RealRooted.toeplitz a) k)

/-- The Chow-derangement series of a unit-diagonal Toeplitz matrix satisfies
the first denominator identity of Brändén--Vecchi, Theorem 8.1. -/
theorem toeplitzChowDerangementSeries_mul_rescale
    (a : ℕ → R) (ha0 : a 0 = 1) :
    toeplitzChowDerangementSeries a *
        PowerSeries.rescale X (toeplitzCoefficientSeries a) =
      1 - PowerSeries.C X +
        PowerSeries.C X * toeplitzChowSeries a := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
      rw [PowerSeries.coeff_mul]
      simp [ha0, toeplitzChowDerangementSeries,
        toeplitzCoefficientSeries, toeplitzChowSeries,
        chowPolynomial, RealRooted.toeplitz_apply]
  | succ n =>
      rw [PowerSeries.coeff_mul]
      simp only [coeff_toeplitzChowDerangementSeries,
        PowerSeries.coeff_rescale, coeff_toeplitzCoefficientSeries]
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      have hrhs :
          PowerSeries.coeff (n + 1)
              (1 - PowerSeries.C X +
                PowerSeries.C X * toeplitzChowSeries a) =
            X * chowPolynomial (RealRooted.toeplitz a) (n + 1) := by
        simp
      rw [hrhs]
      have hreflect := reflect_chowPolynomial_succ
        (RealRooted.toeplitz a)
        (fun k => by simp [RealRooted.toeplitz_apply, ha0]) n
      rw [reflect_chowPolynomial_toeplitz] at hreflect
      rw [← hreflect]
      apply Finset.sum_congr rfl
      intro k hk
      ring

/-- The Chow series of a unit-diagonal Toeplitz matrix satisfies the
denominator identity of Brändén--Vecchi, Theorem 8.1. -/
theorem toeplitzChowSeries_mul_denominator
    (a : ℕ → R) (ha0 : a 0 = 1) :
    (PowerSeries.rescale X (toeplitzCoefficientSeries a) -
        PowerSeries.C X * toeplitzCoefficientSeries a) *
        toeplitzChowSeries a =
      (1 - PowerSeries.C X) * toeplitzCoefficientSeries a := by
  have h := toeplitzChowDerangementSeries_mul_rescale a ha0
  rw [toeplitzChowSeries_eq_mul] at h ⊢
  calc
    (PowerSeries.rescale X (toeplitzCoefficientSeries a) -
          PowerSeries.C X * toeplitzCoefficientSeries a) *
          (toeplitzCoefficientSeries a *
            toeplitzChowDerangementSeries a) =
        toeplitzCoefficientSeries a *
          (toeplitzChowDerangementSeries a *
              PowerSeries.rescale X (toeplitzCoefficientSeries a) -
            PowerSeries.C X *
              (toeplitzCoefficientSeries a *
                toeplitzChowDerangementSeries a)) := by
      ring
    _ = toeplitzCoefficientSeries a *
          ((1 - PowerSeries.C X +
              PowerSeries.C X *
                (toeplitzCoefficientSeries a *
                  toeplitzChowDerangementSeries a)) -
            PowerSeries.C X *
              (toeplitzCoefficientSeries a *
                toeplitzChowDerangementSeries a)) := by
      rw [h]
    _ = (1 - PowerSeries.C X) * toeplitzCoefficientSeries a := by
      ring

/-- Equivalent product form of the Toeplitz Chow denominator identity. -/
theorem rescale_mul_toeplitzChowSeries
    (a : ℕ → R) (ha0 : a 0 = 1) :
    PowerSeries.rescale X (toeplitzCoefficientSeries a) *
        toeplitzChowSeries a =
      toeplitzCoefficientSeries a *
        (1 - PowerSeries.C X +
          PowerSeries.C X * toeplitzChowSeries a) := by
  have h := toeplitzChowDerangementSeries_mul_rescale a ha0
  rw [toeplitzChowSeries_eq_mul] at h ⊢
  calc
    PowerSeries.rescale X (toeplitzCoefficientSeries a) *
          (toeplitzCoefficientSeries a *
            toeplitzChowDerangementSeries a) =
        toeplitzCoefficientSeries a *
          (toeplitzChowDerangementSeries a *
            PowerSeries.rescale X (toeplitzCoefficientSeries a)) := by
      ring
    _ = toeplitzCoefficientSeries a *
          (1 - PowerSeries.C X +
            PowerSeries.C X *
              (toeplitzCoefficientSeries a *
                toeplitzChowDerangementSeries a)) := by
      rw [h]

end

end RealRooted.BrandenVecchi
