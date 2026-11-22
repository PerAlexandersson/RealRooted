module

public import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya
public import RealRooted.Mathlib.Analysis.Complex.InfiniteDifferential.Basic
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.InfiniteDifferentialOrder
import RealRooted.MultiplierSequence.PolyaSchur.LaguerrePolya.GrowthOrder

/-!
# Infinite differential preservation with one subquadratic input

Every LP function has order at most two. Thus it suffices for either the LP
symbol or the LP target to have order strictly below two; the other input has
no supplied growth hypothesis. Convergence is justified by reciprocal exponents.
-/

public section

namespace RealRooted

/-- A strict order bound below two leaves room for a reciprocal exponent
strictly above two on the other input. -/
private theorem exists_reciprocal_exponents_lt_two {ρ : ℝ} (hρ : ρ < 2) :
    ∃ p q : ℝ, 0 < p ∧ ρ < p ∧ 2 < q ∧ 1 < p⁻¹ + q⁻¹ := by
  let p := (max ρ 0 + 2) / 2
  have hp : 0 < p := by dsimp [p]; linarith [le_max_right ρ 0]
  have hpρ : ρ < p := by dsimp [p]; linarith [le_max_left ρ 0]
  have hp2 : p < 2 := by dsimp [p]; have h := max_lt hρ (by norm_num : (0 : ℝ) < 2); linarith
  have hq : 0 < 4 - p := by linarith
  refine ⟨p, 4 - p, hp, hpρ, by linarith, ?_⟩
  have heq : p⁻¹ + (4 - p)⁻¹ = (p + (4 - p)) / (p * (4 - p)) := by
    field_simp
    ring
  rw [heq, lt_div_iff₀ (mul_pos hp hq)]
  nlinarith [sq_pos_of_pos (sub_pos.mpr hp2)]

/-- Any LP target is preserved by an LP differential symbol of order below
two. No separate growth bound is required for the target. -/
theorem IsLaguerrePolya.infiniteDifferentialApply_of_left_order {φ f : ℂ → ℂ}
    (hφ : IsLaguerrePolya φ) (hf : IsLaguerrePolya f) {ρ : ℝ}
    (horder : TauCeti.OrderLE φ ρ) (hρ : ρ < 2) :
    IsLaguerrePolya (Complex.infiniteDifferentialApply φ f) := by
  obtain ⟨p, q, hp, hρp, hq, hsum⟩ := exists_reciprocal_exponents_lt_two hρ
  exact hφ.infiniteDifferentialApply_of_order hf horder hp hρp hf.orderLE_two
    (lt_trans (by norm_num) hq) hq hsum

/-- Every LP symbol acts on every LP target of order below two by an LP
entire differential sum. No separate growth bound is required for the symbol. -/
theorem IsLaguerrePolya.infiniteDifferentialApply_of_right_order {φ f : ℂ → ℂ}
    (hφ : IsLaguerrePolya φ) (hf : IsLaguerrePolya f) {ρ : ℝ}
    (horder : TauCeti.OrderLE f ρ) (hρ : ρ < 2) :
    IsLaguerrePolya (Complex.infiniteDifferentialApply φ f) := by
  obtain ⟨p, q, hp, hρp, hq, hsum⟩ := exists_reciprocal_exponents_lt_two hρ
  exact hφ.infiniteDifferentialApply_of_order hf hφ.orderLE_two (lt_trans (by norm_num) hq) hq
    horder hp hρp (by simpa only [add_comm] using hsum)

end RealRooted
