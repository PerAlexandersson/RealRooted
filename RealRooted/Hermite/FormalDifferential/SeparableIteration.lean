module

public import RealRooted.Hermite.FormalDifferential.Basic
public import Mathlib.FieldTheory.Separable
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import RealRooted.Hermite.Generalized.Degree
import RealRooted.Hermite.Generalized.Separability
import RealRooted.Hermite.FormalDifferential.RescaledIterates
import RealRooted.Hermite.FormalDifferential.Structure
import RealRooted.Hermite.FormalDifferential.Composition
import RealRooted.Mathlib.Analysis.Polynomial.SeparableLimit
import RealRooted.Mathlib.RingTheory.Polynomial.ScaleRoots.Separable
import TauCeti.RingTheory.Polynomial.Roots
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Eventual separability of formal differential iterates

If the first departure from an exponential has order p and is nonzero,
the generalized Hermite limit is separable in degrees congruent to zero
or one modulo p. Fixed-degree root continuity transfers this to the actual
iterates. No real-rootedness of the input is assumed. This is the real-symbol
case of the eventual-simplicity conclusion in Kim--Kim (2015), Section 4.
-/

public section

open Polynomial Filter Topology

namespace RealRooted.HermitePoulain

/-- For monic input, coefficient convergence to the separable stride limit
and invertible affine root transformations give eventual separability. -/
private theorem eventually_separable_monic_iterates
    {φ : PowerSeries ℝ} (a : ℝ) {p : ℕ} (hp : 2 ≤ p)
    (hjet : ∀ k < p, PowerSeries.coeff k φ = a ^ k / (k.factorial : ℝ))
    (hβ : PowerSeries.coeff p φ - a ^ p / (p.factorial : ℝ) ≠ 0)
    {P : ℝ[X]} (hP : P.Monic) (hrem : P.natDegree % p ≤ 1) :
    ∀ᶠ m : ℕ in atTop, ((formalDifferentialOperator φ)^[m] P).Separable := by
  have hp0 : 0 < p := by lia
  let H := formalDifferentialOperator
    (PowerSeries.expand p hp0.ne'
      (PowerSeries.rescale (PowerSeries.coeff p φ - a ^ p / (p.factorial : ℝ))
        (PowerSeries.exp ℝ))) (X ^ P.natDegree)
  let Q : ℕ → ℝ[X] := fun m ↦
    (((formalDifferentialOperator φ)^[m] P).comp (X + C (-(m : ℝ) * a))).scaleRoots
      ((m : ℝ) ^ (-(p : ℝ)⁻¹))
  have h0 : PowerSeries.constantCoeff φ = 1 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff, pow_zero,
      Nat.factorial_zero, Nat.cast_one, div_one] using hjet 0 hp0
  have hdata := isMonicOfDegree_formal_exp_stride
    (PowerSeries.coeff p φ - a ^ p / (p.factorial : ℝ)) hp0 P.natDegree
  have hH := hdata.monic
  have hHd := hdata.natDegree_eq
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
    have h := tendsto_coeff_rescaled_iterate_of_exponential_jet a hp0 hjet P j
    rw [hPzero] at h
    exact h
  have hsep : H.Separable :=
    (separable_formal_exp_stride_iff hp P.natDegree hβ).mpr hrem
  have hev : ∀ᶠ m : ℕ in atTop, ((Q m).map Complex.ofRealHom).Separable := by
    apply eventually_separable_of_coeff_tendsto (hH.map Complex.ofRealHom) hsep.map
    · exact Eventually.of_forall fun m ↦
        ⟨(hQ m).1.map Complex.ofRealHom, by simpa only [natDegree_map] using (hQ m).2⟩
    · intro j _
      simp only [coeff_map, Complex.ofRealHom_eq_coe]
      change Tendsto (fun m ↦ ((Q m).coeff j : ℂ)) atTop (𝓝 (H.coeff j : ℂ))
      exact (Complex.continuous_ofReal.tendsto _).comp (hlim j)
  filter_upwards [hev, eventually_gt_atTop 0] with m hm hm0
  have hr : (m : ℝ) ^ (-(p : ℝ)⁻¹) ≠ 0 :=
    (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hm0) _).ne'
  have hreal : (Q m).Separable := (separable_map Complex.ofRealHom).mp hm
  exact separable_comp_X_add_C_iff.mp ((separable_scaleRoots_iff _ hr).mp hreal)

/-- A normalized real formal symbol eventually gives separable iterates of
every nonzero input whose degree remainder is zero or one. The time may
depend on the input, and the roots need not all be real. -/
theorem eventually_separable_iterate_of_exponential_jet
    {φ : PowerSeries ℝ} (a : ℝ) {p : ℕ} (hp : 2 ≤ p)
    (hjet : ∀ k < p, PowerSeries.coeff k φ = a ^ k / (k.factorial : ℝ))
    (hβ : PowerSeries.coeff p φ - a ^ p / (p.factorial : ℝ) ≠ 0)
    {P : ℝ[X]} (hP : P ≠ 0) (hrem : P.natDegree % p ≤ 1) :
    ∀ᶠ m : ℕ in atTop, ((formalDifferentialOperator φ)^[m] P).Separable := by
  have hlc : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP
  have hmonic : (C P.leadingCoeff⁻¹ * P).Monic :=
    monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ hlc)
  have hd : (C P.leadingCoeff⁻¹ * P).natDegree % p ≤ 1 := by
    simpa only [natDegree_C_mul (inv_ne_zero hlc)] using hrem
  filter_upwards [eventually_separable_monic_iterates a hp hjet hβ hmonic hd] with m hm
  rw [← formalDifferentialOperator_pow, formalDifferentialOperator_mul_input,
    formalDifferentialOperator_pow] at hm
  exact hm.of_mul_right

end RealRooted.HermitePoulain
