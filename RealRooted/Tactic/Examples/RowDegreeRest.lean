module

public import RealRooted.Tactic.RowInterlacing
public import RealRooted.Applications.OEIS.PeriodicTopRows
public import RealRooted.Applications.OEIS.HigherOrderDegreeModels

/-!
# Remaining row-degree regressions for issue 1628

These definitions are local copies of the downstream OEIS recurrences.  They exercise the
cancellation and scalar invariant-cone routes on every row left open by the issue.
-/

@[expose] public section

open Polynomial

namespace RealRooted.Tactic.RowDegreeRest

noncomputable section

/-- The downstream A263789 recurrence used to regress the remaining degree route. -/
def A263789 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1
  | n + 2 => ((C (((1 / (((-1 / 2) + ((-1 / 2) * (n : ℝ))))) * (-2 + (-1 * (n : ℝ))))) * X + C
      (((1 / (((-1 / 2) + ((-1 / 2) * (n : ℝ))))) * (2 + (n : ℝ)))) * X ^ 2)) * (A263789 (n +
      1)).derivative + (C (((1 / (((-1 / 2) + ((-1 / 2) * (n : ℝ))))) * ((7 / 2) + ((-1 / 2) *
      ((3 + (n : ℝ))) ^ (2)) + ((3 / 2) * (n : ℝ))))) * X) * A263789 (n + 1)


/-- The downstream A357613 recurrence used to regress the remaining degree route. -/
def A357613 : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => ((C (((1 / (((-7 / 3) + ((-5 / 3) * (n : ℝ)) + ((2 / 3) * ((2 + (n : ℝ))) ^ (2)))))
      * (-1 + ((-3 / 2) * (n : ℝ))))) * X + C (((1 / (((-7 / 3) + ((-5 / 3) * (n : ℝ)) + ((2 /
      3) * ((2 + (n : ℝ))) ^ (2))))) * ((-7 / 6) + ((-5 / 3) * (n : ℝ))))) * X ^ 2 + C (((1 /
      (((-7 / 3) + ((-5 / 3) * (n : ℝ)) + ((2 / 3) * ((2 + (n : ℝ))) ^ (2))))) * ((-1 / 6) +
      ((-1 / 6) * (n : ℝ))))) * X ^ 3)) * (A357613 n).derivative + ((C (((1 / (((-7 / 3) + ((-5
      / 3) * (n : ℝ)) + ((2 / 3) * ((2 + (n : ℝ))) ^ (2))))) * (-17 + ((-27 / 2) * (n : ℝ)) +
      ((9 / 2) * ((2 + (n : ℝ))) ^ (2))))) + C (((1 / (((-7 / 3) + ((-5 / 3) * (n : ℝ)) + ((2 /
      3) * ((2 + (n : ℝ))) ^ (2))))) * ((-46 / 3) + (4 * ((2 + (n : ℝ))) ^ (2)) + ((-37 / 3) *
      (n : ℝ))))) * X + C (((1 / (((-7 / 3) + ((-5 / 3) * (n : ℝ)) + ((2 / 3) * ((2 +
      (n : ℝ)))
      ^ (2))))) * ((-2 / 3) + ((-1 / 2) * (n : ℝ)) + ((1 / 6) * ((2 + (n : ℝ))) ^ (2))))) * X ^
      2)) * A357613 n


/-- The downstream A110200 recurrence used to regress the remaining degree route. -/
def A110200 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 5 + 9 * X
  | 2 => 21 + 70 * X + 49 * X ^ 2
  | n + 3 => ((7 + (7 * X))) * A110200 (n + 2) + ((-14 + (-28 * X) + (-14 * (X) ^ (2)))) *
      A110200 (n + 1) + ((8 + (8 * (X) ^ (3)) + (24 * X) + (24 * (X) ^ (2)))) * A110200 n


/-- The downstream A259454 recurrence used to regress the remaining degree route. -/
def A259454 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + 3 * X
  | 2 => 1 + 6 * X + 7 * X ^ 2
  | n + 3 => ((C (((10 / 7) * (1 / ((-3 + (-1 * (n : ℝ))))))) * X + C (((26 / 7) * (1 / ((-3 +
      (-1 * (n : ℝ))))))) * X ^ 2)) * (A259454 (n + 2)).derivative + ((C (((-3 / 7) * (1 / ((-3
      + (-1 * (n : ℝ))))))) * X + C (((-10 / 7) * (1 / ((-3 + (-1 * (n : ℝ))))))) * X ^ 2 + C
      (((-33 / 7) * (1 / ((-3 + (-1 * (n : ℝ))))))) * X ^ 3)) * (A259454 (n + 1)).derivative +
      ((C (((1 / ((-3 + (-1 * (n : ℝ))))) * ((-27 / 7) + ((-10 / 7) * (n : ℝ))))) + C (((1 /
      ((-3 + (-1 * (n : ℝ))))) * ((-101 / 7) + ((-40 / 7) * (n : ℝ))))) * X)) * A259454 (n + 2)
      + ((C (((1 / ((-3 + (-1 * (n : ℝ))))) * ((6 / 7) + ((3 / 7) * (n : ℝ))))) + C (((1 / ((-3
      + (-1 * (n : ℝ))))) * ((5 / 7) + (n : ℝ)))) * X + C (((1 / ((-3 +
      (-1 * (n : ℝ))))) * ((40
      / 7) + ((33 / 7) * (n : ℝ))))) * X ^ 2)) * A259454 (n + 1) + ((C (((3 / 7) * (1 / ((-3 +
      (-1 * (n : ℝ))))) * (4 + (n : ℝ)))) * X ^ 2 + C (((1 / ((-3 +
      (-1 * (n : ℝ))))) * (4 + (n
      : ℝ)))) * X ^ 3)) * A259454 n


/-- The downstream A133109 recurrence used to regress the remaining degree route. -/
def A133109 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 3 * X
  | 2 => 4 * X ^ 2
  | n + 3 => (C (((-1 / 2) * (1 / ((-1 + ((-1 / 2) * (n : ℝ))))))) * X) * A133109 (n + 2) + (C
      (((-1 / 2) * (1 / ((-1 + ((-1 / 2) * (n : ℝ))))))) * X ^ 2) * A133109 (n + 1) + (C (((1 /
      ((-1 + ((-1 / 2) * (n : ℝ))))) * ((-3 / 2) + ((-1 / 2) * (n : ℝ))))) * X ^ 3) * A133109 n


/-- The downstream A134434 recurrence used to regress the remaining degree route. -/
def A134434 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1
  | 2 => 1 + X
  | 3 => 4 + 2 * X
  | n + 4 => ((C ((4 + (n : ℝ))) * X + C ((-4 + (-1 * (n : ℝ)))) * X ^ 2)) * (A134434 (n +
      2)).derivative + ((C (((15 / 4) + ((3 / 2) * (n : ℝ)))) * X + C (((-15 / 4) + ((-3 / 2) *
      (n : ℝ)))) * X ^ 2)) * (A134434 (n + 1)).derivative + ((C (((3 / 4) + ((1 / 2) * (n :
      ℝ)))) * X + C (((-3 / 4) + ((-1 / 2) * (n : ℝ)))) * X ^ 2)) * (A134434 n).derivative + (C
      (-2)) * A134434 (n + 3) + ((C ((-1 + ((1 / 4) * ((5 + (n : ℝ))) ^ (2)))) + C (((-43 / 4) +
      ((-5 / 2) * (n : ℝ)) + ((3 / 4) * ((5 + (n : ℝ))) ^ (2)))) * X)) * A134434 (n + 2) + ((C
      (((-27 / 4) + ((1 / 2) * ((5 + (n : ℝ))) ^ (2)) + ((-3 / 2) * (n : ℝ)))) + C ((-22 + ((5 +
      (n : ℝ))) ^ (2) + ((-25 / 4) * (n : ℝ)))) * X)) * A134434 (n + 1) + ((C (((-21 / 4) + ((-3
      / 2) * (n : ℝ)) + ((1 / 4) * ((5 + (n : ℝ))) ^ (2)))) + C (((-13 / 2) + ((-9 / 4) * (n :
      ℝ)) + ((1 / 4) * ((5 + (n : ℝ))) ^ (2)))) * X)) * A134434 n


/-- The downstream A339000 recurrence used to regress the remaining degree route. -/
def A339000 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + 2 * X
  | 2 => 1 + 7 * X + 5 * X ^ 2
  | n + 3 => ((C ((-8 * (1 / ((-3 + (-1 * (n : ℝ))))))) * X + C ((-2 * (1 / ((-3 + (-1 * (n :
      ℝ))))))) * X ^ 2)) * (A339000 (n + 2)).derivative + ((C (((1 / ((-3 + (-1 * (n : ℝ))))) *
      (5 + (3 * (n : ℝ))))) + C (((1 / ((-3 + (-1 * (n : ℝ))))) *
      (-6 + (-2 * (n : ℝ))))) * X))
      * A339000 (n + 2) + ((C (((1 / ((-3 + (-1 * (n : ℝ))))) * (-9 + (-5 * (n : ℝ))))) + C (((1
      / ((-3 + (-1 * (n : ℝ))))) * (3 + (n : ℝ)))) * X + C (((1 /
      ((-3 + (-1 * (n : ℝ))))) * (6
      + (4 * (n : ℝ))))) * X ^ 2)) * A339000 (n + 1) + ((C (((1 / ((-3 + (-1 * (n : ℝ))))) * (1
      + (n : ℝ)))) + C (((1 / ((-3 + (-1 * (n : ℝ))))) *
      (-3 + (-3 * (n : ℝ))))) * X + C (((1 /
      ((-3 + (-1 * (n : ℝ))))) * (3 + (3 * (n : ℝ))))) * X ^ 2 + C (((1 / ((-3 + (-1 * (n :
      ℝ))))) * (-1 + (-1 * (n : ℝ))))) * X ^ 3)) * A339000 n


/-- The downstream A366159 recurrence used to regress the remaining degree route. -/
def A366159 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + 5 * X
  | n + 2 => ((C (1) * X + C (1) * X ^ 2)) * (A366159 (n + 1)).derivative + ((C (((1 / ((-2 +
      (-1 * (n : ℝ))))) * (3 + (n : ℝ)))) * X ^ 2 + C (((1 /
      ((-2 + (-1 * (n : ℝ))))) * (3 + (n
      : ℝ)))) * X ^ 3)) * (A366159 n).derivative + ((C (1) + C (((1 / ((-2 + (-1 * (n : ℝ))))) *
      (-9 + (-4 * (n : ℝ))))) * X)) * A366159 (n + 1) + ((C (((1 / ((-2 + (-1 * (n : ℝ))))) * (3
      + (n : ℝ)))) * X + C ((3 * (1 / ((-2 + (-1 * (n : ℝ))))) * (3 + (n : ℝ)))) * X ^ 2)) *
      A366159 n


/-- The exact degree law for A263789, certified by the row-degree tactic. -/
theorem A263789_natDegree (n : ℕ) : (A263789 n).natDegree = n / 2 := by
  rr_row_natDegree (via := cancel)

/-- The exact degree law for A357613, certified by the row-degree tactic. -/
theorem A357613_natDegree (n : ℕ) : (A357613 n).natDegree = n := by
  rr_row_natDegree (via := cancel)

/-- The exact degree law for A110200, certified by the row-degree tactic. -/
theorem A110200_natDegree (n : ℕ) : (A110200 n).natDegree = n := by
  rr_row_natDegree (via := cone)

/-- The exact degree law for A259454, certified by the row-degree tactic. -/
theorem A259454_natDegree (n : ℕ) : (A259454 n).natDegree = n := by
  rr_row_natDegree (via := cone)

/-- The exact degree law for A133109, certified by the row-degree tactic. -/
theorem A133109_natDegree (n : ℕ) : (A133109 n).natDegree = n := by
  rr_row_natDegree

/-- The exact degree law for A134434, certified by the row-degree tactic. -/
theorem A134434_natDegree (n : ℕ) : (A134434 n).natDegree = n / 2 := by
  rr_row_natDegree

/-- The exact degree law for A339000, certified by the row-degree tactic. -/
theorem A339000_natDegree (n : ℕ) : (A339000 n).natDegree = n := by
  rr_row_natDegree (via := cone)

/-- The exact degree law for A366159, certified by the row-degree tactic. -/
theorem A366159_natDegree (n : ℕ) : (A366159 n).natDegree = n := by
  rr_row_natDegree (via := cone)

/-- The downstream A177040 recurrence, used to regress the degree-model fallback. -/
def A177040 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1
  | 2 => 2 + X
  | 3 => 3 + X
  | n + 4 =>
      let next := RealRooted.Tactic.RowParityDegree.A177040Next
      next n (A177040 (n + 3)) (A177040 (n + 2))
        (A177040 (n + 1)) (A177040 n)

/-- The exact A177040 degree law, certified by the default row-degree tactic. -/
theorem A177040_natDegree (n : ℕ) : (A177040 n).natDegree = n / 2 := by
  rr_row_natDegree

/-- The downstream A110205 recurrence, used to regress the degree-model fallback. -/
def A110205 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 9 + 27 * X
  | 2 => 73 + 368 * X + 343 * X ^ 2
  | n + 3 =>
      RealRooted.Applications.OEIS.HigherOrderDegreeModels.A110205.nextRow n
        (A110205 (n + 2)) (A110205 (n + 1)) (A110205 n)

/-- The exact A110205 degree law, certified by the default row-degree tactic. -/
theorem A110205_natDegree (n : ℕ) : (A110205 n).natDegree = n := by
  rr_row_natDegree


/-- The downstream A367873 recurrence, used to regress the degree-model fallback. -/
def A367873 : ℕ → ℝ[X]
  | 0 => 1
  | 1 => 1 + X
  | 2 => 4 * X
  | n + 3 =>
      RealRooted.Applications.OEIS.HigherOrderDegreeModels.A367873.nextRow n
        (A367873 (n + 2)) (A367873 (n + 1)) (A367873 n)

/-- The exact A367873 degree law, certified by the default row-degree tactic. -/
theorem A367873_natDegree (n : ℕ) : (A367873 n).natDegree = (n + 1) / 2 := by
  rr_row_natDegree

end

end RealRooted.Tactic.RowDegreeRest
