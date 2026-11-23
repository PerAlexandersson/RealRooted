module

public import RealRooted.Hermite.FormalDifferential.Basic
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import RealRooted.Hermite.FormalDifferential.RescaledIterates
import RealRooted.Hermite.FormalDifferential.Structure
import RealRooted.Hermite.FormalDifferential.Composition
import RealRooted.Mathlib.Analysis.Polynomial.RootMatchingLimit
import RealRooted.Mathlib.RingTheory.PowerSeries.ExpCoefficient
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic.NormNum

/-!
# Multiplicity-sensitive clustering of centered formal iterates

All roots of the centered and rescaled iterates match the roots of the
limiting exponential differential polynomial, counting multiplicity.
No simplicity or reality assumption on the limiting roots is required.
-/

public section

open Polynomial Filter Topology

namespace RealRooted.HermitePoulain

/-- A constant-one expanded exponential preserves monicity and degree. -/
private theorem exponential_limit_monic_degree (β : ℝ) {p : ℕ} (hp : 0 < p) (d : ℕ) :
    let H := formalDifferentialOperator
      (PowerSeries.expand p hp.ne' (PowerSeries.rescale β (PowerSeries.exp ℝ))) (X ^ d)
    H.Monic ∧ H.natDegree = d := by
  dsimp only
  have h0 : PowerSeries.constantCoeff (PowerSeries.expand p hp.ne'
      (PowerSeries.rescale β (PowerSeries.exp ℝ))) = 1 := by
    rw [PowerSeries.constantCoeff_expand, ← PowerSeries.coeff_zero_eq_constantCoeff]
    simp
  refine ⟨formalDifferentialOperator_monic h0 (monic_X.pow d), ?_⟩
  rw [natDegree_formalDifferentialOperator (by rw [h0]; exact one_ne_zero)
    (pow_ne_zero d X_ne_zero), natDegree_X_pow]

/-- Every complex root of the rescaled iterates is matched with a limiting
root, with multiplicity. This includes repeated roots at zero, degree zero,
and vanishing first discrepancy. -/
theorem eventually_rel_roots_rescaled_iterate
    {φ : PowerSeries ℝ} (a : ℝ) {p : ℕ} (hp : 0 < p)
    (hjet : ∀ k < p, PowerSeries.coeff k φ = a ^ k / (k.factorial : ℝ))
    {P : ℝ[X]} (hP : P.Monic) {ε : ℝ} (hε : 0 < ε) :
    let H := formalDifferentialOperator
      (PowerSeries.expand p hp.ne'
        (PowerSeries.rescale (PowerSeries.coeff p φ - a ^ p / (p.factorial : ℝ))
          (PowerSeries.exp ℝ))) (X ^ P.natDegree)
    ∀ᶠ m : ℕ in atTop,
      (H.map Complex.ofRealHom).roots.Rel (fun z w ↦ ‖z - w‖ < ε)
        (((((formalDifferentialOperator φ)^[m] P).comp (X + C (-(m : ℝ) * a))).scaleRoots
          ((m : ℝ) ^ (-(p : ℝ)⁻¹))).map Complex.ofRealHom).roots := by
  intro H
  let Q : ℕ → ℝ[X] := fun m ↦
    (((formalDifferentialOperator φ)^[m] P).comp (X + C (-(m : ℝ) * a))).scaleRoots
      ((m : ℝ) ^ (-(p : ℝ)⁻¹))
  have h0 : PowerSeries.constantCoeff φ = 1 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff, pow_zero,
      Nat.factorial_zero, Nat.cast_one, div_one] using hjet 0 hp
  obtain ⟨hH, hHd⟩ := exponential_limit_monic_degree
    (PowerSeries.coeff p φ - a ^ p / (p.factorial : ℝ)) hp P.natDegree
  have hQ (m : ℕ) : (Q m).Monic ∧ (Q m).natDegree = H.natDegree := by
    have hφm : PowerSeries.constantCoeff (φ ^ m) = 1 := by simp [h0]
    constructor
    · apply (monic_scaleRoots_iff _).mpr
      rw [← formalDifferentialOperator_pow]
      exact (formalDifferentialOperator_monic hφm hP).comp_X_add_C _
    · dsimp only [Q]
      rw [natDegree_scaleRoots, natDegree_comp, natDegree_X_add_C, mul_one,
        ← formalDifferentialOperator_pow,
        natDegree_formalDifferentialOperator (by rw [hφm]; exact one_ne_zero) hP.ne_zero,
        hHd]
  have hPzero : P.scaleRoots 0 = X ^ P.natDegree := by
    rw [scaleRoots_zero, hP, one_smul]
  have hlim (j : ℕ) : Tendsto (fun m ↦ (Q m).coeff j) atTop (𝓝 (H.coeff j)) := by
    have h := tendsto_coeff_rescaled_iterate_of_exponential_jet a hp hjet P j
    rw [hPzero] at h
    exact h
  apply eventually_rel_roots_of_coeff_tendsto (hH.map Complex.ofRealHom)
  · exact Eventually.of_forall fun m ↦
      ⟨(hQ m).1.map Complex.ofRealHom, by simpa only [natDegree_map] using (hQ m).2⟩
  · intro j _
    simp only [coeff_map, Complex.ofRealHom_eq_coe]
    change Tendsto (fun m ↦ ((Q m).coeff j : ℂ)) atTop (𝓝 (H.coeff j : ℂ))
    exact (Complex.continuous_ofReal.tendsto _).comp (hlim j)
  · exact hε

end RealRooted.HermitePoulain
