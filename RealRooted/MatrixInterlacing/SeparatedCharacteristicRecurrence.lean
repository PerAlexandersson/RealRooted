module

public import RealRooted.MatrixInterlacing.SeparatedCharacteristicRows
public import RealRooted.Mathlib.Algebra.LinearRecurrence.Subsequence

/-!
# Scalar recurrences from separated-characteristic matrix orbits

This module supplies the Cayley--Hamilton and uniqueness interfaces used to
identify a scalar polynomial sequence with a chosen coordinate of a
separated-characteristic matrix orbit.  The uniqueness theorem permits an
explicit starting index, so exceptional prefix rows remain outside the
homogeneous recurrence.
-/

public section

open Polynomial
open scoped Matrix

noncomputable section

namespace RealRooted

/-- A separated-characteristic matrix orbit is matrix exponentiation applied
to its seed. -/
theorem separatedCharacteristicRows_eq_pow_mulVec {h m : ℕ}
    (a : Fin (h + m) → ℝ) (b : Fin m → ℝ)
    (seed : Fin (h + m) → ℝ[X]) (n : ℕ) :
    separatedCharacteristicRows a b seed n =
      (separatedCharacteristicFinMatrix a b) ^ n *ᵥ seed := by
  simpa using LinearRecurrence.state_add_eq_pow_mulVec
    (v := separatedCharacteristicRows a b seed)
    (A := separatedCharacteristicFinMatrix a b)
    (fun _ ↦ rfl) 0 n

/-- Every coordinate of a separated-characteristic matrix orbit satisfies
the recurrence encoded by the matrix characteristic polynomial. -/
theorem separatedCharacteristicRows_coordinate_isSolution {h m : ℕ}
    (a : Fin (h + m) → ℝ) (b : Fin m → ℝ)
    (seed : Fin (h + m) → ℝ[X]) (i : Fin (h + m)) :
    (LinearRecurrence.ofMatrix (separatedCharacteristicFinMatrix a b)).IsSolution
      (fun n ↦ separatedCharacteristicRows a b seed n i) := by
  exact LinearRecurrence.ofMatrix_isSolution
    (separatedCharacteristicFinMatrix a b)
    (separatedCharacteristicRows a b seed) (fun _ ↦ rfl) i

/-- Recurrence uniqueness with an explicit starting index.  A scalar sequence
that satisfies the matrix recurrence from `start` onward and agrees with one
coordinate for the first `h + m` tail rows agrees with that coordinate on the
entire tail. -/
theorem eq_separatedCharacteristicRows_coordinate_from {h m : ℕ}
    (a : Fin (h + m) → ℝ) (b : Fin m → ℝ)
    (seed : Fin (h + m) → ℝ[X]) (i : Fin (h + m))
    (P : ℕ → ℝ[X]) (start : ℕ)
    (hP : (LinearRecurrence.ofMatrix
      (separatedCharacteristicFinMatrix a b)).IsSolution
        (fun n ↦ P (start + n)))
    (hinitial : ∀ r < h + m,
      P (start + r) = separatedCharacteristicRows a b seed r i) :
    ∀ n, P (start + n) = separatedCharacteristicRows a b seed n i := by
  let E := LinearRecurrence.ofMatrix (separatedCharacteristicFinMatrix a b)
  have horbit : E.IsSolution
      (fun n ↦ separatedCharacteristicRows a b seed n i) :=
    separatedCharacteristicRows_coordinate_isSolution a b seed i
  have heq : (fun n ↦ P (start + n)) =
      (fun n ↦ separatedCharacteristicRows a b seed n i) := by
    apply (E.eq_iff_eqOn_range_order _ _ hP horbit).2
    intro r hr
    exact hinitial r (Finset.mem_range.mp hr)
  exact fun n ↦ congrFun heq n

end RealRooted
