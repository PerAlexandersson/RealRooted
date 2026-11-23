module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic

public import RealRooted.Hermite.FormalDifferential.Basic
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.FieldTheory.Separable
import RealRooted.Hermite.Generalized.ExponentialRoots
import RealRooted.Hermite.FormalDifferential.Structure
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Separability of exponential-stride limits

For a nonzero exponential parameter, the only possible multiple root is at
zero. Its multiplicity is exactly the degree remainder modulo the stride.
-/

public section

open Polynomial Complex

namespace RealRooted.HermitePoulain

/-- A nondegenerate exponential-stride limit is separable exactly when
the degree remainder is zero or one. This includes constant inputs. -/
theorem separable_formal_exp_stride_iff {p : ℕ} (hp : 2 ≤ p)
    (d : ℕ) {β : ℝ} (hβ : β ≠ 0) :
    (formalDifferentialOperator
      (PowerSeries.expand p (by lia) (PowerSeries.rescale β (PowerSeries.exp ℝ)))
      (X ^ d)).Separable ↔ d % p ≤ 1 := by
  classical
  let φ := PowerSeries.expand p (by lia : p ≠ 0)
    (PowerSeries.rescale β (PowerSeries.exp ℝ))
  let H := formalDifferentialOperator φ (X ^ d)
  have h0 : PowerSeries.constantCoeff φ = 1 := by
    dsimp only [φ]
    rw [PowerSeries.constantCoeff_expand, ← PowerSeries.coeff_zero_eq_constantCoeff]
    simp
  have hH : H.Monic := formalDifferentialOperator_monic h0 (monic_X.pow d)
  have hs : d % p < p := Nat.mod_lt d (by lia)
  have hd : d % p + p * (d / p) = d := Nat.mod_add_div d p
  have hzero : (H.map ofRealHom).rootMultiplicity 0 = d % p := by
    simpa only [hd] using rootMultiplicity_zero_formal_exp_stride hp hs (d / p) hβ
  change H.Separable ↔ d % p ≤ 1
  constructor
  · intro h
    rw [← hzero]
    exact rootMultiplicity_le_one_of_separable h.map 0
  · intro hrem
    have hnodup : (H.map ofRealHom).roots.Nodup := by
      classical
      apply Multiset.nodup_iff_count_le_one.mpr
      intro z
      rw [count_roots]
      by_cases hz : z = 0
      · simpa only [hz, hzero] using hrem
      · by_cases hroot : (H.map ofRealHom).IsRoot z
        · have hm : (H.map ofRealHom).rootMultiplicity z = 1 := by
            simpa only [hd] using
              rootMultiplicity_formal_exp_stride_of_ne_zero hp hs (d / p) hβ hz
                (by simpa only [hd] using hroot)
          exact hm.le
        · rw [rootMultiplicity_eq_zero hroot]
          exact Nat.zero_le _
    have hc := (nodup_roots_iff_of_splits (hH.map ofRealHom).ne_zero
      (IsAlgClosed.splits _)).mp hnodup
    exact (separable_map ofRealHom).mp hc

end RealRooted.HermitePoulain
