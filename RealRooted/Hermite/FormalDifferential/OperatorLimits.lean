module

public import RealRooted.Hermite.FormalDifferential.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic.TypeStar

/-!
# Joint coefficient limits for formal symbols and polynomial inputs

A common finite degree bound on the inputs reduces the action to a fixed
finite sum, even when the formal symbols vary and have no analytic sum.
-/

public section

open Polynomial Filter Topology

namespace RealRooted.HermitePoulain

/-- Any upper degree bound may be used for the finite differential sum. -/
theorem formalDifferentialOperator_eq_sum_of_natDegree_le
    (φ : PowerSeries ℝ) {P : ℝ[X]} {N : ℕ} (hP : P.natDegree ≤ N) :
    formalDifferentialOperator φ P = ∑ k ∈ Finset.range (N + 1),
      C (PowerSeries.coeff k φ) * (derivative^[k]) P := by
  rw [formalDifferentialOperator_eq_sum]
  apply Finset.sum_subset (Finset.range_subset_range.mpr (by lia))
  intro k _ hk
  have hPk : P.natDegree < k := by simpa using hk
  rw [iterate_derivative_eq_zero hPk, mul_zero]

/-- The coefficient of a formal differential image is a fixed finite convolution. -/
theorem coeff_formalDifferentialOperator_of_natDegree_le
    (φ : PowerSeries ℝ) {P : ℝ[X]} {N : ℕ} (hP : P.natDegree ≤ N) (j : ℕ) :
    (formalDifferentialOperator φ P).coeff j =
      ∑ k ∈ Finset.range (N + 1), PowerSeries.coeff k φ *
        ((j + k).descFactorial k : ℝ) * P.coeff (j + k) := by
  rw [formalDifferentialOperator_eq_sum_of_natDegree_le φ hP, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_iterate_derivative, nsmul_eq_mul, mul_assoc]

/-- Coefficientwise limits pass through varying formal differential symbols
on a common finite degree range of polynomial inputs. -/
theorem tendsto_coeff_formalDifferentialOperator {ι : Type*} {l : Filter ι}
    {φ : ι → PowerSeries ℝ} {ψ : PowerSeries ℝ} {P : ι → ℝ[X]} {Q : ℝ[X]} {N : ℕ}
    (hP : ∀ i, (P i).natDegree ≤ N) (hQ : Q.natDegree ≤ N)
    (hφ : ∀ k, Tendsto (fun i ↦ PowerSeries.coeff k (φ i)) l (𝓝 (PowerSeries.coeff k ψ)))
    (hcoeff : ∀ k, Tendsto (fun i ↦ (P i).coeff k) l (𝓝 (Q.coeff k))) (j : ℕ) :
    Tendsto (fun i ↦ (formalDifferentialOperator (φ i) (P i)).coeff j) l
      (𝓝 ((formalDifferentialOperator ψ Q).coeff j)) := by
  have hleft : (fun i ↦ (formalDifferentialOperator (φ i) (P i)).coeff j) =
      (fun i ↦ ∑ k ∈ Finset.range (N + 1), PowerSeries.coeff k (φ i) *
        ((j + k).descFactorial k : ℝ) * (P i).coeff (j + k)) :=
    funext fun i ↦ coeff_formalDifferentialOperator_of_natDegree_le (φ i) (hP i) j
  rw [hleft, coeff_formalDifferentialOperator_of_natDegree_le ψ hQ j]
  exact tendsto_finsetSum _ fun k _ ↦ ((hφ k).mul_const _).mul (hcoeff (j + k))

end RealRooted.HermitePoulain
