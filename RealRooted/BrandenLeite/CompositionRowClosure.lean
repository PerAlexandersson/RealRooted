import RealRooted.BrandenLeite.ToeplitzComposition
import RealRooted.Mathlib.RingTheory.PowerSeries.PiTopology

/-!
# Degree bounds and limits of composition rows

Composition rows have a uniform degree bound given by their row index. Their
coefficients depend continuously on the coefficients of the defining power
series. The final theorem specializes this fact to the positive-order series
associated with a convergent family of sequences.
-/

open Filter Polynomial Topology
open scoped PowerSeries.WithPiTopology

noncomputable section

namespace RealRooted.BrandenLeite

/-- The degree of a composition row is at most its row index. -/
theorem natDegree_compositionRow_le
    {R : Type*} [CommSemiring R] (h : PowerSeries R) (n : ℕ) :
    (compositionRow h n).natDegree ≤ n := by
  unfold compositionRow
  apply natDegree_sum_le_of_forall_le
  intro k hk
  exact (natDegree_C_mul_X_pow_le _ k).trans
    (Nat.le_of_lt_succ (Finset.mem_range.mp hk))

/-- Coefficientwise limits of zero-constant power series induce
coefficientwise limits of every fixed composition row. -/
theorem tendsto_coeff_compositionRow
    {R : Type*} [TopologicalSpace R] [CommSemiring R] [IsTopologicalSemiring R]
    {ι : Type*} {l : Filter ι} {h : ι → PowerSeries R} {h₀ : PowerSeries R}
    (hzero : ∀ k, PowerSeries.constantCoeff (h k) = 0)
    (hzero₀ : PowerSeries.constantCoeff h₀ = 0)
    (hcoeff : ∀ i, Tendsto (fun k => PowerSeries.coeff i (h k)) l
      (𝓝 (PowerSeries.coeff i h₀))) (n i : ℕ) :
    Tendsto (fun k => (compositionRow (h k) n).coeff i) l
      (𝓝 ((compositionRow h₀ n).coeff i)) := by
  have hleft : (fun k => (compositionRow (h k) n).coeff i) =
      fun k => PowerSeries.coeff n ((h k) ^ i) := by
    funext k
    exact coeff_compositionRow (hzero k) n i
  rw [hleft, coeff_compositionRow hzero₀]
  exact PowerSeries.WithPiTopology.tendsto_coeff_pow_of_coeff_tendsto
    hcoeff i n

/-- Pointwise limits of sequences induce coefficientwise limits of the
composition rows of their positive-order power series. -/
theorem tendsto_coeff_compositionRow_positivePartSeries
    {R : Type*} [TopologicalSpace R] [CommSemiring R] [IsTopologicalSemiring R]
    {ι : Type*} {l : Filter ι} {a : ι → ℕ → R} {a₀ : ℕ → R}
    (ha : ∀ i, Tendsto (fun k => a k i) l (𝓝 (a₀ i)))
    (n i : ℕ) :
    Tendsto (fun k => (compositionRow (positivePartSeries (a k)) n).coeff i)
      l (𝓝 ((compositionRow (positivePartSeries a₀) n).coeff i)) := by
  apply tendsto_coeff_compositionRow
  · exact fun k => constantCoeff_positivePartSeries (a k)
  · exact constantCoeff_positivePartSeries a₀
  · intro d
    by_cases hd : d = 0
    · subst d
      simpa using (tendsto_const_nhds :
        Tendsto (fun _ : ι => (0 : R)) l (𝓝 0))
    · simpa [coeff_positivePartSeries, hd] using ha d

end RealRooted.BrandenLeite
