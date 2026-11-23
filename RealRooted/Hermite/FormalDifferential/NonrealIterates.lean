module

public import RealRooted.Hermite.FormalDifferential.Basic
import RealRooted.Hermite.FormalDifferential.RootClustering
import RealRooted.Hermite.FormalDifferential.NonrealExponential
import RealRooted.Hermite.FormalDifferential.Structure
import RealRooted.Hermite.FormalDifferential.Composition
import RealRooted.Mathlib.Analysis.Polynomial.NonrealPersistence
import RealRooted.Mathlib.RingTheory.PowerSeries.ExpCoefficient

/-!
# Eventual nonreal roots from the first nonexponential formal term
-/

public section

open Polynomial Filter

namespace RealRooted.HermitePoulain

/-- A nonreal limiting root persists in the original unscaled iterates. -/
private theorem eventually_not_splits_monic_of_exponential_jet
    {φ : PowerSeries ℝ} (a : ℝ) {p : ℕ} (hp : 0 < p)
    (hjet : ∀ k < p, PowerSeries.coeff k φ = a ^ k / (k.factorial : ℝ))
    (hbad : (p = 2 ∧ 0 < PowerSeries.coeff p φ - a ^ p / (p.factorial : ℝ)) ∨
      (3 ≤ p ∧ PowerSeries.coeff p φ - a ^ p / (p.factorial : ℝ) ≠ 0))
    {P : ℝ[X]} (hP : P.Monic) (hpd : p ≤ P.natDegree) :
    ∀ᶠ m : ℕ in atTop, ¬ ((formalDifferentialOperator φ)^[m] P).Splits := by
  let σ := PowerSeries.expand p hp.ne'
    (PowerSeries.rescale (PowerSeries.coeff p φ - a ^ p / (p.factorial : ℝ))
      (PowerSeries.exp ℝ))
  let H := formalDifferentialOperator σ (X ^ P.natDegree)
  have hσ : PowerSeries.constantCoeff σ = 1 := by
    rw [PowerSeries.constantCoeff_expand, ← PowerSeries.coeff_zero_eq_constantCoeff]
    simp
  have hH0 : H ≠ 0 := (formalDifferentialOperator_monic hσ
    (monic_X.pow P.natDegree)).ne_zero
  have hHbad : ¬ H.Splits := not_splits_formalDifferentialOperator_exp_stride hp hpd hbad
  have hev := eventually_not_splits_of_eventually_rel_roots hH0 hHbad
    (fun ε hε ↦ eventually_rel_roots_rescaled_iterate a hp hjet hP hε)
  filter_upwards [hev] with m hm hsplit
  exact hm ((hsplit.comp_X_add_C _).scaleRoots _)

/-- A positive quadratic or nonzero higher first centered term forces
nonreal roots in every sufficiently high iterate of each input of adequate degree. -/
theorem eventually_not_splits_iterate_of_exponential_jet
    {φ : PowerSeries ℝ} (a : ℝ) {p : ℕ} (hp : 0 < p)
    (hjet : ∀ k < p, PowerSeries.coeff k φ = a ^ k / (k.factorial : ℝ))
    (hbad : (p = 2 ∧ 0 < PowerSeries.coeff p φ - a ^ p / (p.factorial : ℝ)) ∨
      (3 ≤ p ∧ PowerSeries.coeff p φ - a ^ p / (p.factorial : ℝ) ≠ 0))
    {P : ℝ[X]} (hP : P ≠ 0) (hpd : p ≤ P.natDegree) :
    ∀ᶠ m : ℕ in atTop, ¬ ((formalDifferentialOperator φ)^[m] P).Splits := by
  have hlc : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP
  let Q := C P.leadingCoeff⁻¹ * P
  have hQ : Q.Monic := monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ hlc)
  have hQd : p ≤ Q.natDegree := by rwa [natDegree_C_mul (inv_ne_zero hlc)]
  filter_upwards [eventually_not_splits_monic_of_exponential_jet a hp hjet hbad hQ hQd]
    with m hm hsplit
  apply hm
  rw [← formalDifferentialOperator_pow, formalDifferentialOperator_mul_input]
  rw [← formalDifferentialOperator_pow] at hsplit
  exact hsplit.C_mul _

end RealRooted.HermitePoulain
