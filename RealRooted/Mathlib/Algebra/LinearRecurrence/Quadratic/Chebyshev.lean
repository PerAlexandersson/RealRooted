import RealRooted.Mathlib.Algebra.LinearRecurrence.Quadratic
import Mathlib.RingTheory.Polynomial.Chebyshev

/-!
# Chebyshev closed forms for normalized quadratic recurrences

This algebraic child expresses solutions of `quadratic (2 * t) (-1)` through
Mathlib's Chebyshev polynomials. Trigonometric specializations and analytic
estimates belong to separate clients.
-/

namespace LinearRecurrence

open Polynomial

variable {R : Type*} [CommRing R]

/-- The Chebyshev solution with prescribed first two terms. -/
noncomputable def quadraticChebyshevSolution (t e0 e1 : R) : ℕ → R :=
  fun n ↦ e0 * (Chebyshev.T R n).eval t +
    (e1 - e0 * t) * (Chebyshev.U R ((n : ℤ) - 1)).eval t

/-- The Chebyshev expression solves the normalized quadratic recurrence. -/
theorem quadraticChebyshevSolution_isSolution (t e0 e1 : R) :
    (quadratic (2 * t) (-1)).IsSolution (quadraticChebyshevSolution t e0 e1) := by
  rw [quadratic_isSolution_iff]
  intro n
  unfold quadraticChebyshevSolution
  have hT := congrArg (fun f : R[X] ↦ f.eval t) (Chebyshev.T_add_two R (n : ℤ))
  have hU := congrArg (fun f : R[X] ↦ f.eval t)
    (Chebyshev.U_add_two R ((n : ℤ) - 1))
  simp only [eval_sub, eval_mul, eval_ofNat, eval_X] at hT hU
  have hT2 : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := by norm_cast
  have hT1 : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by norm_cast
  have hN2 : (n : ℤ) + 2 - 1 = (n : ℤ) + 1 := by ring
  have hN1 : (n : ℤ) + 1 - 1 = (n : ℤ) := by ring
  have hU2 : (n : ℤ) - 1 + 2 = (n : ℤ) + 1 := by ring
  have hU1 : (n : ℤ) - 1 + 1 = (n : ℤ) := by ring
  rw [hU2, hU1] at hU
  rw [hT2, hT1, hN2, hN1]
  linear_combination e0 * hT + (e1 - e0 * t) * hU

@[simp]
theorem quadraticChebyshevSolution_zero (t e0 e1 : R) :
    quadraticChebyshevSolution t e0 e1 0 = e0 := by
  simp [quadraticChebyshevSolution]

@[simp]
theorem quadraticChebyshevSolution_one (t e0 e1 : R) :
    quadraticChebyshevSolution t e0 e1 1 = e1 := by
  simp [quadraticChebyshevSolution]

/-- Every normalized quadratic recurrence solution has its Chebyshev form. -/
theorem isSolution_eq_quadraticChebyshevSolution {t : R} {S : ℕ → R}
    (hS : (quadratic (2 * t) (-1)).IsSolution S) :
    S = quadraticChebyshevSolution t (S 0) (S 1) := by
  refine (eq_iff_eqOn_range_order (quadratic (2 * t) (-1)) S
    (quadraticChebyshevSolution t (S 0) (S 1)) hS
    (quadraticChebyshevSolution_isSolution t (S 0) (S 1))).mpr ?_
  intro n hn
  have hnn := Finset.mem_range.mp hn
  change n < 2 at hnn
  have hn' : n ≤ 1 := Nat.le_of_lt_succ hnn
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn' with rfl | rfl
  · simp
  · simp

end LinearRecurrence
