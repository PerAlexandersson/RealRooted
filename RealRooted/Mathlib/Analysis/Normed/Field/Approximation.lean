import Mathlib.Analysis.Normed.Field.Approximation
import Mathlib.Analysis.Polynomial.CauchyBound

/-!
# One-sided continuity of polynomial roots

This file adds a coefficient-neighborhood form of root continuity intended
for upstreaming to `Mathlib.Analysis.Normed.Field.Approximation`.
-/

open Polynomial

namespace Polynomial

noncomputable section

/-- Every root of a sufficiently close monic polynomial of the same degree is
close to a root of a fixed positive-degree monic split polynomial. -/
theorem exists_coeff_radius_forall_root_near
    {K : Type*} [NormedField K] {p : K[X]}
    (hp : p.Monic) (hdegree : p.natDegree ≠ 0) (hsplits : p.Splits)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q : K[X], q.Monic →
      q.natDegree = p.natDegree →
      (∀ i : ℕ, ‖q.coeff i - p.coeff i‖ < δ) →
      ∀ z : K, q.IsRoot z →
        ∃ w : K, p.IsRoot w ∧ ‖z - w‖ < η := by
  let B : ℝ := max (p.cauchyBound : ℝ) 1
  let ρ : ℝ := min (1 / 2 : ℝ) (η / (2 * B))
  let δ : ℝ := ρ ^ p.natDegree /
    (2 * ((p.natDegree + 1 : ℕ) : ℝ))
  have hdegree_pos : 0 < p.natDegree := Nat.pos_of_ne_zero hdegree
  have hB : 0 < B := by
    exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hρ : 0 < ρ := by
    apply lt_min
    · norm_num
    · exact div_pos hη (mul_pos (by norm_num) hB)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  refine ⟨δ, hδ, ?_⟩
  intro q hq hqdegree hcoeff z hz
  have hcoeff' : ∀ i : ℕ, ‖p.coeff i - q.coeff i‖ < δ := by
    intro i
    simpa [norm_sub_rev] using hcoeff i
  obtain ⟨w, hwmem, hzw⟩ :=
    Polynomial.exists_roots_norm_sub_lt_of_norm_coeff_sub_lt
      (f := q) (g := p) hδ hz hq hp hqdegree.symm hcoeff' hsplits
  have hp0 : p ≠ 0 := hp.ne_zero
  have hw : p.IsRoot w := (Polynomial.mem_roots hp0).mp hwmem
  refine ⟨w, hw, ?_⟩
  have hfactor :
      (((p.natDegree + 1 : ℕ) : ℝ) * δ) ^
          ((p.natDegree : ℝ)⁻¹) < ρ := by
    rw [Real.rpow_inv_lt_iff_of_pos (by positivity) hρ.le
      (by exact_mod_cast hdegree_pos)]
    rw [Real.rpow_natCast]
    dsimp [δ]
    have hpow : 0 < ρ ^ p.natDegree := pow_pos hρ _
    field_simp
    nlinarith
  have hzw' :
      ‖z - w‖ < ρ * max ‖z‖ 1 := by
    have hmax : 0 < max ‖z‖ 1 :=
      lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    calc
      ‖z - w‖ <
          (((p.natDegree + 1 : ℕ) : ℝ) * δ) ^
              ((p.natDegree : ℝ)⁻¹) * max ‖z‖ 1 := by
        simpa [hqdegree] using hzw
      _ < ρ * max ‖z‖ 1 := mul_lt_mul_of_pos_right hfactor hmax
  have hwbound : ‖w‖ < B := by
    have hwbound' : ‖w‖ < (p.cauchyBound : ℝ) := by
      exact_mod_cast hw.norm_lt_cauchyBound hp0
    exact hwbound'.trans_le (le_max_left _ _)
  have hρhalf : ρ ≤ 1 / 2 := min_le_left _ _
  have hmaxbound : max ‖z‖ 1 < 2 * B := by
    rcases le_total ‖z‖ 1 with hzle | hzone
    · rw [max_eq_right hzle]
      have hBone : 1 ≤ B := le_max_right _ _
      linarith
    · rw [max_eq_left hzone] at hzw' ⊢
      have htriangle : ‖z‖ ≤ ‖z - w‖ + ‖w‖ := by
        calc
          ‖z‖ = ‖(z - w) + w‖ := by rw [sub_add_cancel]
          _ ≤ ‖z - w‖ + ‖w‖ := norm_add_le _ _
      have hρnonneg : 0 ≤ ρ := hρ.le
      have hznonneg : 0 ≤ ‖z‖ := norm_nonneg _
      have hhalf : ρ * ‖z‖ ≤ (1 / 2 : ℝ) * ‖z‖ :=
        mul_le_mul_of_nonneg_right hρhalf hznonneg
      nlinarith
  have hρη : ρ ≤ η / (2 * B) := min_le_right _ _
  calc
    ‖z - w‖ < ρ * max ‖z‖ 1 := hzw'
    _ < ρ * (2 * B) := mul_lt_mul_of_pos_left hmaxbound hρ
    _ ≤ (η / (2 * B)) * (2 * B) := by
      gcongr
    _ = η := by field_simp

end

end Polynomial
