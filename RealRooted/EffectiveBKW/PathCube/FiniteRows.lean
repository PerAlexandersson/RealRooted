module

public import RealRooted.EffectiveBKW.PathCube.Basic
import RealRooted.EffectiveBKW.PathCube.FiniteChecks00
import RealRooted.EffectiveBKW.PathCube.FiniteChecks01
import RealRooted.EffectiveBKW.PathCube.FiniteChecks02
import RealRooted.EffectiveBKW.PathCube.FiniteChecks03
import RealRooted.EffectiveBKW.PathCube.FiniteChecks04
import RealRooted.EffectiveBKW.PathCube.FiniteChecks05
import RealRooted.EffectiveBKW.PathCube.FiniteRecurrence
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-!
# The finite part of the path-cube argument

The checked integer-list recurrence identifies the literal rows with the transfer
orbit. Each rational sign grid is independently checked by the kernel, and the
soundness theorem supplies splitting and simple roots for indices below 59.
-/

public section

namespace RealRooted.EffectiveBKW.PathCube

open Polynomial BigDescents321.SmallCases

private theorem listStep_polynomial (a b c d : IntPoly) :
    (listStep a b c d).polynomial =
      (1 + 3 * X) * a.polynomial + 2 * X * (1 - X) * b.polynomial +
      X * (2 - X - X ^ 2) * c.polynomial + X ^ 2 * (1 - X) ^ 2 * d.polynomial := by
  simp only [listStep, IntPoly.polynomial, ofList_addList, ofList_mulList, ofList_cons,
    ofList_nil, Int.cast_zero, Int.cast_one, Int.cast_ofNat, Int.cast_neg, C_0, C_1,
    C_ofNat, C_neg, mul_zero, add_zero, zero_add]
  ring

private theorem row_eq_rowList {r : ℕ} (hr : r < 59) : row r = (rowList r).polynomial := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    match r with
    | 0 =>
      change row 0 = IntPoly.polynomial [1]
      simp [IntPoly.polynomial, ofList]
    | 1 =>
      change row 1 = IntPoly.polynomial [1, 1]
      simp [IntPoly.polynomial, ofList]
    | 2 =>
      change row 2 = IntPoly.polynomial [1, 4, 1]
      rw [row_two]
      simp only [IntPoly.polynomial, ofList, Int.cast_ofNat, Int.cast_one,
        C_1, C_ofNat, mul_zero, add_zero]
      ring
    | 3 =>
      change row 3 = IntPoly.polynomial [1, 11, 11, 1]
      rw [row_three]
      simp only [IntPoly.polynomial, ofList, Int.cast_ofNat, Int.cast_one,
        C_1, C_ofNat, mul_zero, add_zero]
      ring
    | r + 4 =>
      have hc := IntPoly.eqCheck_sound (rowLists_recurrence ⟨r, by lia⟩)
      rw [row_add_four, ih (r + 3) (by lia) (by lia),
        ih (r + 2) (by lia) (by lia), ih (r + 1) (by lia) (by lia),
        ih r (by lia) (by lia), hc, listStep_polynomial]

/-- All transfer rows below the effective cutoff have their full expected set
of distinct negative roots. The zeroth constant row is included. -/
theorem row_splits_nodup_of_lt {r : ℕ} (hr : r < 59) :
    (row r).natDegree = r ∧ (row r).Splits ∧ (row r).roots.Nodup ∧
      ∀ x ∈ (row r).roots, x < 0 := by
  have hc : (grid r).check = true := by
    interval_cases r
    · exact grid00_check
    · exact grid01_check
    · exact grid02_check
    · exact grid03_check
    · exact grid04_check
    · exact grid05_check
    · exact grid06_check
    · exact grid07_check
    · exact grid08_check
    · exact grid09_check
    · exact grid10_check
    · exact grid11_check
    · exact grid12_check
    · exact grid13_check
    · exact grid14_check
    · exact grid15_check
    · exact grid16_check
    · exact grid17_check
    · exact grid18_check
    · exact grid19_check
    · exact grid20_check
    · exact grid21_check
    · exact grid22_check
    · exact grid23_check
    · exact grid24_check
    · exact grid25_check
    · exact grid26_check
    · exact grid27_check
    · exact grid28_check
    · exact grid29_check
    · exact grid30_check
    · exact grid31_check
    · exact grid32_check
    · exact grid33_check
    · exact grid34_check
    · exact grid35_check
    · exact grid36_check
    · exact grid37_check
    · exact grid38_check
    · exact grid39_check
    · exact grid40_check
    · exact grid41_check
    · exact grid42_check
    · exact grid43_check
    · exact grid44_check
    · exact grid45_check
    · exact grid46_check
    · exact grid47_check
    · exact grid48_check
    · exact grid49_check
    · exact grid50_check
    · exact grid51_check
    · exact grid52_check
    · exact grid53_check
    · exact grid54_check
    · exact grid55_check
    · exact grid56_check
    · exact grid57_check
    · exact grid58_check
  have hs : (rowList r).polynomial.Splits ∧ (rowList r).polynomial.roots.Nodup :=
    ⟨(SignGrid.check_sound hc).2.1, (SignGrid.check_sound hc).2.2.1⟩
  rw [← row_eq_rowList hr] at hs
  exact ⟨row_natDegree r, hs.1, hs.2, row_roots_neg r⟩

end RealRooted.EffectiveBKW.PathCube
