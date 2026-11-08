module

public import RealRooted.PFPolynomial
import RealRooted.BrandenLeite.PositivePowerFactors
public import RealRooted.BrandenLeite.AffineLogarithm
import RealRooted.PFPolynomial.Closure
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! Pólya-frequency logarithmic rows and consecutive oriented interlacing. -/

public section

open Polynomial Filter Topology

namespace RealRooted.BrandenLeite

/-- Positive-exponent PF and interlacing certificates pass to the normalized
zero-exponent limit defining the logarithmic rows. Only a uniform degree
bound is needed; the limit may lose degree. -/
theorem affineLogCoeff_pf_and_interl_of_positive_powers
    (Q B : PowerSeries ℝ) (hQ : PowerSeries.constantCoeff Q = 1)
    (hB : PowerSeries.constantCoeff B = 0)
    (hpf : ∀ a : ℝ, 0 < a → ∀ j,
      IsPFPolynomial (affineNegativePowerCoeff a Q B j))
    (hdeg : ∀ a : ℝ, 0 < a → ∀ j,
      (affineNegativePowerCoeff a Q B j).natDegree ≤ j)
    (hi : ∀ a : ℝ, 0 < a → ∀ j, Interl
      (affineNegativePowerCoeff a Q B j)
      (affineNegativePowerCoeff a Q B (j + 1)))
    (n : ℕ) (hn : n ≠ 0) :
    IsPFPolynomial (affineLogCoeff Q B n) ∧
      Interl (affineLogCoeff Q B n)
        (affineLogCoeff Q B (n + 1)) := by
  let ε : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
  have hε (m : ℕ) : 0 < ε m := by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hεright : Tendsto ε atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hεlim, Filter.Eventually.of_forall hε⟩
  let p : ℕ → ℕ → Polynomial ℝ := fun j m =>
    C ((ε m)⁻¹) * affineNegativePowerCoeff (ε m) Q B j
  have hppf (j m : ℕ) : IsPFPolynomial (p j m) :=
    (hpf (ε m) (hε m) j).const_mul (inv_pos.mpr (hε m))
  have hpdeg (j m : ℕ) : (p j m).natDegree ≤ j :=
    (Polynomial.natDegree_C_mul_le _ _).trans (hdeg (ε m) (hε m) j)
  have hpinterl (j m : ℕ) : Interl (p j m) (p (j + 1) m) :=
    ((hi (ε m) (hε m) j).C_mul_left_of_nonneg (inv_pos.mpr (hε m)).le).C_mul_right_of_nonneg
      (inv_pos.mpr (hε m)).le
  have hplim (j : ℕ) (hj : j ≠ 0) (i : ℕ) :
      Tendsto (fun m => (p j m).coeff i) atTop
        (𝓝 ((affineLogCoeff Q B j).coeff i)) := by
    simp only [p, Polynomial.coeff_C_mul]
    simpa only [Function.comp_def, div_eq_mul_inv, mul_comm] using
      (tendsto_coeff_affineNegativePowerCoeff_div Q B hQ hB hj i).comp hεright
  refine ⟨IsPFPolynomial.of_coeff_tendsto (hppf n) (hplim n hn), ?_⟩
  exact interl_of_pf_coeff_tendsto_of_natDegree_le (N := n + 1)
    (hppf n) (hppf (n + 1)) (hpinterl n)
    (fun m => (hpdeg n m).trans (Nat.le_succ n)) (hpdeg (n + 1))
    (hplim n hn) (hplim (n + 1) (Nat.succ_ne_zero n))

/-- The limit argument for the factored logarithmic rows, with the `let` bindings of
the public statement. -/
private theorem pf_and_interl_aux
    {ι ν : Type*} (s : Finset ι) (hs : s.Nonempty) (α : ι → ℝ)
    (hα : ∀ i ∈ s, 0 < α i) (t : Finset ν) (β : ν → ℝ)
    (hβ : ∀ j ∈ t, 0 ≤ β j) {c : ℝ} (hc : 0 < c)
    (r : ℕ) (hr : r ≠ 0) (n : ℕ) (hn : n ≠ 0) :
    let Q : Polynomial ℝ := ∏ i ∈ s, (1 - C (α i) * X)
    let B : Polynomial ℝ := C c * X ^ r * ∏ j ∈ t, (1 + C (β j) * X)
    let ℓ := fun j => affineLogCoeff (Q : PowerSeries ℝ) (B : PowerSeries ℝ) j
    IsPFPolynomial (ℓ n) ∧ Interl (ℓ n) (ℓ (n + 1)) := by
  let Q : Polynomial ℝ := ∏ i ∈ s, (1 - C (α i) * X)
  let B : Polynomial ℝ := C c * X ^ r * ∏ j ∈ t, (1 + C (β j) * X)
  have hQ0 : PowerSeries.constantCoeff (Q : PowerSeries ℝ) = 1 := by
    simp [Q, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]
  have hB0 : PowerSeries.constantCoeff (B : PowerSeries ℝ) = 0 := by
    simp [B, Polynomial.coeff_zero_eq_eval_zero, hr]
  have hprops (a : ℝ) (ha : 0 < a) (j : ℕ) :
      IsPFPolynomial (affineNegativePowerCoeff a
        (Q : PowerSeries ℝ) (B : PowerSeries ℝ) j) ∧
      (affineNegativePowerCoeff a
        (Q : PowerSeries ℝ) (B : PowerSeries ℝ) j).natDegree ≤ j ∧
      Interl (affineNegativePowerCoeff a
        (Q : PowerSeries ℝ) (B : PowerSeries ℝ) j)
        (affineNegativePowerCoeff a
          (Q : PowerSeries ℝ) (B : PowerSeries ℝ) (j + 1)) := by
    obtain ⟨_, hsplit, _, hdegree, hcoeff, hinterl⟩ :=
      affineNegativePowerCoeff_factor_properties s hs α hα t β hβ hc ha r hr j
    refine ⟨IsPFPolynomial.of_realRooted_nonneg ?_ hsplit,
      hdegree.trans_le (Nat.div_le_self j r), hinterl⟩
    intro k
    by_cases hk : k ≤ j / r
    · exact (hcoeff k hk).le
    · have hlarge :
          (affineNegativePowerCoeff a
            (Q : PowerSeries ℝ) (B : PowerSeries ℝ) j).natDegree < k := by
        rw [hdegree]
        exact Nat.lt_of_not_ge hk
      simpa only [Polynomial.coeff_eq_zero_of_natDegree_lt hlarge] using
        (le_refl (0 : ℝ))
  exact affineLogCoeff_pf_and_interl_of_positive_powers
    (Q : PowerSeries ℝ) (B : PowerSeries ℝ) hQ0 hB0
    (fun a ha j => (hprops a ha j).1)
    (fun a ha j => (hprops a ha j).2.1)
    (fun a ha j => (hprops a ha j).2.2) n hn

section

variable {ι ν : Type*} (s : Finset ι) (hs : s.Nonempty) (α : ι → ℝ)
  (hα : ∀ i ∈ s, 0 < α i) (t : Finset ν) (β : ν → ℝ)
  (hβ : ∀ j ∈ t, 0 ≤ β j) {c : ℝ} (hc : 0 < c)
  (r : ℕ) (hr : r ≠ 0) (n : ℕ) (hn : n ≠ 0)

include hs hα hβ hc hr hn

/-- The logarithmic row of positive index of factored data is a Pólya frequency
polynomial. -/
theorem isPFPolynomial_affineLogCoeff_factor :
    IsPFPolynomial (affineLogCoeff
      ((∏ i ∈ s, (1 - C (α i) * X) : ℝ[X]) : PowerSeries ℝ)
      ((C c * X ^ r * ∏ j ∈ t, (1 + C (β j) * X) : ℝ[X]) : PowerSeries ℝ) n) :=
  (pf_and_interl_aux s hs α hα t β hβ hc r hr n hn).1

/-- Consecutive logarithmic rows of positive index of factored data interlace in the
oriented zero-aware relation. -/
theorem interl_affineLogCoeff_factor :
    Interl (affineLogCoeff
        ((∏ i ∈ s, (1 - C (α i) * X) : ℝ[X]) : PowerSeries ℝ)
        ((C c * X ^ r * ∏ j ∈ t, (1 + C (β j) * X) : ℝ[X]) : PowerSeries ℝ) n)
      (affineLogCoeff
        ((∏ i ∈ s, (1 - C (α i) * X) : ℝ[X]) : PowerSeries ℝ)
        ((C c * X ^ r * ∏ j ∈ t, (1 + C (β j) * X) : ℝ[X]) : PowerSeries ℝ) (n + 1)) :=
  (pf_and_interl_aux s hs α hα t β hβ hc r hr n hn).2

end

/-- For the factorized data in the generalized theorem, the logarithmic
rows of positive index are PF and consecutively interlace in the oriented
zero-aware relation. Degree and strict coefficient positivity are separate
algebraic conclusions, not assumptions in this limit argument. -/
theorem affineLogCoeff_factor_pf_and_interl
    {ι ν : Type*} (s : Finset ι) (hs : s.Nonempty) (α : ι → ℝ)
    (hα : ∀ i ∈ s, 0 < α i) (t : Finset ν) (β : ν → ℝ)
    (hβ : ∀ j ∈ t, 0 ≤ β j) {c : ℝ} (hc : 0 < c)
    (r : ℕ) (hr : r ≠ 0) (n : ℕ) (hn : n ≠ 0) :
    let Q : Polynomial ℝ := ∏ i ∈ s, (1 - C (α i) * X)
    let B : Polynomial ℝ := C c * X ^ r * ∏ j ∈ t, (1 + C (β j) * X)
    let ℓ := fun j => affineLogCoeff (Q : PowerSeries ℝ) (B : PowerSeries ℝ) j
    IsPFPolynomial (ℓ n) ∧ Interl (ℓ n) (ℓ (n + 1)) :=
  ⟨isPFPolynomial_affineLogCoeff_factor s hs α hα t β hβ hc r hr n hn,
    interl_affineLogCoeff_factor s hs α hα t β hβ hc r hr n hn⟩

end RealRooted.BrandenLeite
