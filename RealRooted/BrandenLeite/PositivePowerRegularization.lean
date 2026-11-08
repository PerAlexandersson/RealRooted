module

import RealRooted.BrandenLeite.PositivePowerRow
import RealRooted.BrandenLeite.PositiveLinearFactors
import RealRooted.Mathlib.Algebra.Polynomial.LinearFactors
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import RealRooted.PFPolynomial
public import RealRooted.Mathlib.RingTheory.PowerSeries.AffineNegativePower
import RealRooted.BrandenLeite.PositivePowerInterlacing
import RealRooted.BrandenLeite.AffineNegativePowerContinuity
import RealRooted.Mathlib.RingTheory.PowerSeries.NegativePowerDegree
import RealRooted.Mathlib.Topology.Algebra.Polynomial
import RealRooted.PFPolynomial.Closure
import RealRooted.Linear
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! Higher-valuation numerators by positive translation after division by `X`. -/

public section

open Polynomial Filter Topology

namespace RealRooted.BrandenLeite

/-- Translating the quotient by the compulsory factor `X` regularizes a
nonzero PF numerator to one with positive first coefficient while preserving
its zero constant coefficient. -/
theorem exists_pf_coeff_one_pos_approximation
    (B : ℝ[X]) (hBne : B ≠ 0) (hB0 : B.coeff 0 = 0)
    (hBs : B.Splits) (hBnn : HasNonnegCoeffs B) :
    ∃ P : ℕ → ℝ[X],
      (∀ m, IsPFPolynomial (P m)) ∧ (∀ m, (P m).coeff 0 = 0) ∧
      (∀ m, 0 < (P m).coeff 1) ∧
      ∀ j, Tendsto (fun m => (P m).coeff j) atTop (𝓝 (B.coeff j)) := by
  let ε : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
  have hε (m : ℕ) : 0 < ε m := by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hX : X * B.divX = B := by
    simpa only [hB0, map_zero, add_zero] using Polynomial.X_mul_divX_add B
  have hdivne : B.divX ≠ 0 := by
    intro h
    apply hBne
    rw [← hX, h, mul_zero]
  have hdivs : B.divX.Splits := by
    apply Polynomial.Splits.of_X_mul
    rw [hX]
    exact hBs
  have hdivpf := IsPFPolynomial.of_realRooted_nonneg hBnn.divX hdivs
  let P : ℕ → ℝ[X] := fun m => X * B.divX.comp (X + C (ε m))
  have hPpf (m : ℕ) : IsPFPolynomial (P m) := by
    apply IsPFPolynomial.X_mul
    simpa only [map_one, one_mul] using
      hdivpf.comp_C_mul_X_add_C (a := 1) (d := ε m) zero_lt_one (hε m).le
  have hPzero (m : ℕ) : (P m).coeff 0 = 0 := by simp [P]
  have hPone (m : ℕ) : 0 < (P m).coeff 1 := by
    simpa only [P, Polynomial.coeff_X_mul, Polynomial.coeff_zero_eq_eval_zero,
      Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C, zero_add] using
      eval_pos_of_hasNonnegCoeffs hBnn.divX hdivne (hε m)
  refine ⟨P, hPpf, hPzero, hPone, ?_⟩
  intro j
  cases j with
  | zero => simpa only [hPzero, hB0] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  | succ j =>
    have hlim := ((B.divX.continuous_coeff_comp_X_add_C j).continuousAt.tendsto).comp hεlim
    simpa only [Function.comp_def, P, Polynomial.coeff_X_mul, map_zero, add_zero,
      Polynomial.comp_X, Polynomial.coeff_divX] using hlim

/-- A numerator with positive first coefficient gives full-degree canonical
rows, even when its other coefficients vanish. -/
private theorem natDegree_affineNegativePowerCoeff_of_coeff_one_pos
    {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (α : ι → ℝ)
    (hα : ∀ i ∈ s, 0 < α i) {κ : ℝ} (hκ : 0 < κ)
    (B : ℝ[X]) (hB0 : B.coeff 0 = 0) (hB1 : 0 < B.coeff 1)
    (hBnn : HasNonnegCoeffs B) (n : ℕ) :
    (PowerSeries.affineNegativePowerCoeff κ
      ((∏ i ∈ s, (1 - C (α i) * X) : ℝ[X]) : PowerSeries ℝ) B n).natDegree = n := by
  have hzero : ∀ j < 1, PowerSeries.coeff j (B : PowerSeries ℝ) = 0 := by
    intro j hj
    have hj0 : j = 0 := by lia
    subst j
    simpa only [Polynomial.coeff_coe] using hB0
  have hdegree := PowerSeries.affineNegativePowerCoeff_prod_linear_degree_and_pos
    s hs α hα (B : PowerSeries ℝ) 1 zero_lt_one hκ
    (fun j => by simpa only [Polynomial.coeff_coe] using hBnn j) hzero
    (by simpa only [Polynomial.coeff_coe] using hB1) n
  simpa only [Nat.div_one, ← Polynomial.coe_prod_one_sub_C_mul_X] using hdegree.1

/-- Canonical positive-power rows consecutively interlace for every nonzero
split numerator with nonnegative coefficients and zero constant term. No
valuation-one restriction remains. -/
theorem interl_affineNegativePowerCoeff_prod_linear_succ
    {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (α : ι → ℝ)
    (hα : ∀ i ∈ s, 0 < α i) {κ : ℝ} (hκ : 0 < κ)
    (B : ℝ[X]) (hBne : B ≠ 0) (hB0 : B.coeff 0 = 0)
    (hBs : B.Splits) (hBnn : HasNonnegCoeffs B) (n : ℕ) :
    Interl (PowerSeries.affineNegativePowerCoeff κ
      ((∏ i ∈ s, (1 - C (α i) * X) : ℝ[X]) : PowerSeries ℝ) B n)
      (PowerSeries.affineNegativePowerCoeff κ
        ((∏ i ∈ s, (1 - C (α i) * X) : ℝ[X]) : PowerSeries ℝ) B (n + 1)) := by
  obtain ⟨P, hPpf, hP0, hP1, hPlim⟩ :=
    exists_pf_coeff_one_pos_approximation B hBne hB0 hBs hBnn
  let Q : ℝ[X] := ∏ i ∈ s, (1 - C (α i) * X)
  have hQ0 : Q.coeff 0 = 1 := Polynomial.coeff_zero_prod_one_sub_C_mul_X s α
  obtain ⟨hQs, hQnn⟩ :=
    splits_and_hasNonnegCoeffs_prod_one_sub_C_mul_X_comp_neg_X s α fun i hi => (hα i hi).le
  have hPne (m : ℕ) : P m ≠ 0 := by
    intro hz
    have := hP1 m
    simp only [hz, Polynomial.coeff_zero, lt_self_iff_false] at this
  have hPs (m : ℕ) : (P m).Splits := ((hPpf m).ne_zero_and_splits (hPne m)).2
  have hdeg (m j : ℕ) :
      (PowerSeries.affineNegativePowerCoeff κ (Q : PowerSeries ℝ) (P m) j).natDegree = j :=
    natDegree_affineNegativePowerCoeff_of_coeff_one_pos
      s hs α hα hκ (P m) (hP0 m) (hP1 m) (hPpf m).hasNonnegCoeffs j
  have hlim (j i : ℕ) : Tendsto
      (fun m => (PowerSeries.affineNegativePowerCoeff κ
        (Q : PowerSeries ℝ) (P m) j).coeff i) atTop
      (𝓝 ((PowerSeries.affineNegativePowerCoeff κ (Q : PowerSeries ℝ) B j).coeff i)) := by
    apply tendsto_coeff_affineNegativePowerCoeff
      (κ := fun _ : ℕ => κ) (Q := fun _ : ℕ => (Q : PowerSeries ℝ))
      (B := fun m => (P m : PowerSeries ℝ))
      (fun _ => by simpa using hQ0) (fun m => by simpa using hP0 m)
      (by simpa using hQ0) (by simpa using hB0)
      tendsto_const_nhds (fun _ => tendsto_const_nhds)
    intro k
    simpa only [Polynomial.coeff_coe] using hPlim k
  apply interl_of_pf_coeff_tendsto_of_natDegree_le (N := n + 1)
    (fun m => isPFPolynomial_affineNegativePowerCoeff_prod_linear s hs α hα hκ
      (P m) (hP0 m) (hPs m) (hPpf m).hasNonnegCoeffs n)
    (fun m => isPFPolynomial_affineNegativePowerCoeff_prod_linear s hs α hα hκ
      (P m) (hP0 m) (hPs m) (hPpf m).hasNonnegCoeffs (n + 1))
    (fun m => (interlaces_affineNegativePowerCoeff_succ hκ Q (P m)
      hQ0 (hP0 m) (hP1 m) hQs hQnn (hPs m) (hPpf m).hasNonnegCoeffs n).toStrictInterl.toInterl)
    (fun m => by rw [hdeg]; exact Nat.le_succ n)
    (fun m => by rw [hdeg])
    (hlim n) (hlim (n + 1))

end RealRooted.BrandenLeite
